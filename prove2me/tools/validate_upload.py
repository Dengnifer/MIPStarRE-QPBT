#!/usr/bin/env python3
"""Compile exact QPBT payload text and compare original and staged node types."""

from __future__ import annotations

import json
import hashlib
import os
import re
import shutil
import subprocess
import sys
import threading
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime, timezone
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[2]
PLAN_PATH = ROOT / "prove2me" / "generated" / "upload_plan.json"
PAYLOADS_PATH = ROOT / "prove2me" / "generated" / "payloads.json"
PLATFORM = ROOT / "prove2me" / "platform"
LIDT_PLATFORM = Path("/home/drx/p2m/MIPStarRE/prove2me/platform")
LIDT_BUILD = LIDT_PLATFORM / ".lake" / "build" / "lib" / "lean"
STAGED_BUILD = PLATFORM / ".lake" / "build" / "lib" / "lean"
LOG = ROOT / "prove2me" / "generated" / "validation.log"
ORIGINAL_AUDIT = ROOT / "prove2me" / "generated" / "type_audit_original.lean"
STAGED_AUDIT = ROOT / "prove2me" / "generated" / "type_audit_staged.lean"
ORIGINAL_TYPES = ROOT / "prove2me" / "generated" / "type_audit_original.jsonl"
STAGED_TYPES = ROOT / "prove2me" / "generated" / "type_audit_staged.jsonl"
TYPE_REPORT = ROOT / "prove2me" / "generated" / "type_audit_report.json"
VALIDATION_RECEIPT = ROOT / "prove2me" / "generated" / "validation_receipt.json"
GENERATED_PROOF_RE = re.compile(
    r"\b(?:[A-Za-z_][A-Za-z0-9_']*\.)+_proof_[0-9]+\b"
)


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def platform_digest() -> str:
    digest = hashlib.sha256()
    for path in sorted(PLATFORM.rglob("*.lean")):
        digest.update(str(path.relative_to(PLATFORM)).encode())
        digest.update(b"\0")
        digest.update(path.read_bytes())
        digest.update(b"\0")
    return digest.hexdigest()


def lake_env_value(name: str) -> str:
    result = subprocess.run(
        ["lake", "env", "printenv", name],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=True,
    )
    return result.stdout.strip()


def lean_binary() -> str:
    result = subprocess.run(
        ["lake", "env", "which", "lean"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=True,
    )
    return result.stdout.strip().splitlines()[-1]


def staged_env() -> dict[str, str]:
    env = os.environ.copy()
    original = lake_env_value("LEAN_PATH").split(os.pathsep)
    excluded = {
        str((ROOT / ".lake" / "build" / "lib" / "lean").resolve()),
        str((ROOT / ".lake" / "packages" / "MIPStarRE" / ".lake" / "build" /
             "lib" / "lean").resolve()),
    }
    retained = [
        entry for entry in original
        if entry and str(Path(entry).resolve()) not in excluded
    ]
    env["LEAN_PATH"] = os.pathsep.join([
        str(STAGED_BUILD),
        *retained,
    ])
    return env


def original_env() -> dict[str, str]:
    env = os.environ.copy()
    env["LEAN_PATH"] = lake_env_value("LEAN_PATH")
    return env


def compile_file(lean: str, env: dict[str, str], path: Path) -> tuple[Path, int, str]:
    output = STAGED_BUILD / path.relative_to(PLATFORM).with_suffix(".olean")
    output.parent.mkdir(parents=True, exist_ok=True)
    result = subprocess.run(
        [lean, "-o", str(output), str(path)],
        cwd=ROOT,
        env=env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    return path, result.returncode, result.stdout


def prepare_staged_build() -> None:
    if not LIDT_BUILD.is_dir():
        raise RuntimeError(f"LIDT build tree is unavailable: {LIDT_BUILD}")
    shutil.rmtree(STAGED_BUILD, ignore_errors=True)
    for source in LIDT_BUILD.rglob("*"):
        if not source.is_file() or source.suffix not in {".olean", ".ilean"}:
            continue
        destination = STAGED_BUILD / source.relative_to(LIDT_BUILD)
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, destination)


def compile_dag(
    lean: str,
    env: dict[str, str],
    paths: dict[str, Path],
    dependencies: dict[str, set[str]],
    log_handle: Any,
    log_lock: threading.Lock,
    *,
    jobs: int,
) -> None:
    pending = set(paths)
    completed: set[str] = set()
    while pending:
        ready = sorted(key for key in pending if dependencies.get(key, set()) <= completed)
        if not ready:
            blocked = {key: sorted(dependencies.get(key, set()) - completed)
                       for key in sorted(pending)}
            raise RuntimeError(f"compile DAG is blocked: {dict(list(blocked.items())[:8])}")
        wave = ready[:jobs]
        with ThreadPoolExecutor(max_workers=jobs) as executor:
            futures = {executor.submit(compile_file, lean, env, paths[key]): key for key in wave}
            for future in as_completed(futures):
                key = futures[future]
                path, returncode, output = future.result()
                with log_lock:
                    log_handle.write(f"===== {path.relative_to(ROOT)} =====\n")
                    log_handle.write(output)
                    log_handle.flush()
                if returncode != 0:
                    raise RuntimeError(f"Lean failed for {path}; see {LOG}")
                print(f"compiled {path.relative_to(ROOT)}", flush=True)
                completed.add(key)
                pending.remove(key)


def code_only(text: str) -> str:
    output: list[str] = []
    index = 0
    block_depth = 0
    in_string = False
    while index < len(text):
        if block_depth:
            if text.startswith("/-", index):
                block_depth += 1
                output.extend("  ")
                index += 2
            elif text.startswith("-/", index):
                block_depth -= 1
                output.extend("  ")
                index += 2
            else:
                output.append("\n" if text[index] == "\n" else " ")
                index += 1
        elif in_string:
            if text[index] == "\\" and index + 1 < len(text):
                output.extend("  ")
                index += 2
            elif text[index] == '"':
                in_string = False
                output.append(" ")
                index += 1
            else:
                output.append("\n" if text[index] == "\n" else " ")
                index += 1
        elif text.startswith("--", index):
            newline = text.find("\n", index)
            if newline == -1:
                output.extend(" " * (len(text) - index))
                break
            output.extend(" " * (newline - index))
            output.append("\n")
            index = newline + 1
        elif text.startswith("/-", index):
            block_depth = 1
            output.extend("  ")
            index += 2
        elif text[index] == '"':
            in_string = True
            output.append(" ")
            index += 1
        else:
            output.append(text[index])
            index += 1
    return "".join(output)


def validate_text(payloads: dict[str, Any]) -> None:
    if payloads["tag"] != "QPBT" or not payloads["private"]:
        raise RuntimeError("payload root must be private and tagged QPBT")
    for definition in payloads["definitions"]:
        text = definition["definition"]
        if re.search(r"\b(?:sorry|admit|axiom)\b", code_only(text)):
            raise RuntimeError(f"proof hole in definition {definition['definition_name']}")
        if not definition["private"] or definition["tags"] != ["QPBT"]:
            raise RuntimeError(f"unsafe definition metadata: {definition['definition_name']}")
    theorem_by_name = {item["theorem_name"]: item for item in payloads["theorems"]}
    if len(theorem_by_name) != len(payloads["theorems"]):
        raise RuntimeError("duplicate theorem names in payloads")
    for theorem in payloads["theorems"]:
        formal = theorem["formal_statement"]
        formal_code = code_only(formal)
        if len(re.findall(r"\bsorry\b", formal_code)) != 1 or not formal_code.rstrip().endswith("by sorry"):
            raise RuntimeError(f"invalid theorem stub for {theorem['theorem_name']}")
        declaration = re.escape(theorem["theorem_name"])
        if not re.search(rf"\btheorem\s+{declaration}(?=\s|$)", formal_code):
            raise RuntimeError(f"invalid theorem declaration head: {theorem['theorem_name']}")
        if not theorem["private"] or theorem["tags"] != ["QPBT"]:
            raise RuntimeError(f"unsafe theorem metadata: {theorem['theorem_name']}")
    for solution in payloads["solutions"]:
        path = ROOT / solution["solution_path"]
        text = path.read_text(encoding="utf-8")
        code = code_only(text)
        if re.search(r"\b(?:sorry|admit|axiom)\b", code):
            raise RuntimeError(f"proof hole in solution {solution['theorem_name']}")
        solution_heads = re.findall(r"\btheorem\s+solution\b", code)
        if len(solution_heads) != 1:
            raise RuntimeError(
                f"expected one theorem solution for {solution['theorem_name']}; "
                f"found {len(solution_heads)}"
            )
        if re.search(r"\b(?:lemma|instance|protected\s+theorem)\s+solution\b", code):
            raise RuntimeError(f"invalid solution declaration head: {solution['theorem_name']}")
        own_import = "Theorems.Thm_" + solution["theorem_name"].replace(".", "_")
        solution_imports = re.findall(r"(?m)^import\s+([^\s]+)\s*$", code)
        if own_import in solution_imports:
            raise RuntimeError(f"solution imports its own target: {solution['theorem_name']}")
        if solution["theorem_name"] not in theorem_by_name:
            raise RuntimeError(f"solution has no theorem payload: {solution['theorem_name']}")


def validate_imports(plan: dict[str, Any]) -> None:
    lidt_imports = {item["import_module"] for item in plan["lidt"]["mapping"].values()}
    qpbt_definitions = {
        "Definitions.Def_" + item["definitionName"]
        for item in plan["definitions"].values()
    }
    qpbt_theorems = {
        "Theorems.Thm_" + item["slug"] for item in plan["nodes"].values()
    }
    allowed_exact = lidt_imports | qpbt_definitions | qpbt_theorems
    problems: list[tuple[str, str]] = []
    for path in PLATFORM.rglob("*.lean"):
        for line in path.read_text(encoding="utf-8").splitlines():
            if not line.startswith("import "):
                continue
            imported = line.removeprefix("import ").strip()
            if imported == "Mathlib" or imported.startswith("Mathlib."):
                continue
            if imported not in allowed_exact:
                problems.append((str(path.relative_to(ROOT)), imported))
    if problems:
        raise RuntimeError(f"generated files contain disallowed imports: {problems[:12]}")


def lean_string(value: str) -> str:
    return json.dumps(value, ensure_ascii=False)


def audit_program(imports: list[str], names: list[str]) -> str:
    entries = ",\n  ".join(lean_string(name) for name in names)
    return "\n".join(imports) + f"""

open Lean Meta

run_meta do
  let names : Array String := #[
  {entries}
  ]
  let env ← getEnv
  for name in names do
    let some info := env.find? name.toName
      | throwError "missing declaration {{name}}"
    let rendered ← withOptions (fun opts =>
      (opts.setBool `pp.fullNames true).setBool `pp.universes true) do
        ppExpr info.type
    IO.println (Json.mkObj [
      ("name", Json.str name),
      ("type", Json.str rendered.pretty)
    ]).compress
"""


def run_lean_capture(lean: str, env: dict[str, str], source: Path, output: Path) -> None:
    result = subprocess.run(
        [lean, str(source)],
        cwd=ROOT,
        env=env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    output.write_text(result.stdout + ("\n" + result.stderr if result.stderr else ""),
                      encoding="utf-8")
    if result.returncode != 0:
        raise RuntimeError(f"type audit failed for {source}; see {output}")


def normalize_type(value: str, replacements: dict[str, str]) -> str:
    result = value
    for source, target in sorted(replacements.items(), key=lambda item: len(item[0]), reverse=True):
        result = result.replace(source, target)
    # Lean may name an elaborated proof in one environment and print the same
    # proof-irrelevant argument as `⋯` in another.
    result = GENERATED_PROOF_RE.sub("⋯", result)
    result = re.sub(r"u_[0-9]+", "u", result)
    return re.sub(r"\s+", " ", result).strip()


def run_type_audit(lean: str, plan: dict[str, Any]) -> None:
    original_names = [plan["nodes"][cid]["originalName"] for cid in plan["nodeOrder"]]
    staged_names = [plan["nodes"][cid]["platformName"] for cid in plan["nodeOrder"]]
    original_imports = [
        "import QPBT.Palomar.PauliCompleteness",
        "import QPBT.Palomar.LowDegreeSoundness",
        "import QPBT.Palomar.PauliSoundness",
    ]
    staged_imports = [
        "import Theorems.Thm_" + plan["nodes"][cid]["slug"]
        for cid in plan["nodeOrder"]
    ]
    ORIGINAL_AUDIT.write_text(audit_program(original_imports, original_names), encoding="utf-8")
    STAGED_AUDIT.write_text(audit_program(staged_imports, staged_names), encoding="utf-8")
    run_lean_capture(lean, original_env(), ORIGINAL_AUDIT, ORIGINAL_TYPES)
    run_lean_capture(lean, staged_env(), STAGED_AUDIT, STAGED_TYPES)
    original_records = [
        json.loads(line) for line in ORIGINAL_TYPES.read_text(encoding="utf-8").splitlines()
        if line.startswith("{")
    ]
    staged_records = [
        json.loads(line) for line in STAGED_TYPES.read_text(encoding="utf-8").splitlines()
        if line.startswith("{")
    ]
    if len(original_records) != len(original_names) or len(staged_records) != len(staged_names):
        raise RuntimeError("type audit did not emit one record per node")
    replacements = {
        node["platformName"]: node["originalName"] for node in plan["nodes"].values()
    }
    replacements.update({
        platform: original for original, platform in plan["externalNameMap"].items()
    })
    replacements.update({
        platform: original for original, platform in plan["projectNameMap"].items()
    })
    if plan["uploadNamespace"]:
        replacements[plan["uploadNamespace"] + "."] = ""
    failures = []
    for original, staged in zip(original_records, staged_records, strict=True):
        left = normalize_type(original["type"], {})
        right = normalize_type(staged["type"], replacements)
        if left != right:
            failures.append({
                "originalName": original["name"],
                "stagedName": staged["name"],
                "originalType": left,
                "stagedType": right,
            })
    report = {"checked": len(original_records), "failures": failures}
    TYPE_REPORT.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    if failures:
        raise RuntimeError(f"{len(failures)} staged theorem types differ; see {TYPE_REPORT}")


def main() -> int:
    plan = json.loads(PLAN_PATH.read_text(encoding="utf-8"))
    payloads = json.loads(PAYLOADS_PATH.read_text(encoding="utf-8"))
    validate_text(payloads)
    validate_imports(plan)
    if not LIDT_PLATFORM.is_dir():
        raise RuntimeError(f"LIDT platform tree is unavailable: {LIDT_PLATFORM}")
    lean = lean_binary()
    prepare_staged_build()
    env = staged_env()
    LOG.parent.mkdir(parents=True, exist_ok=True)
    log_lock = threading.Lock()
    with LOG.open("w", encoding="utf-8") as log_handle:
        definition_paths = {
            bundle_id: PLATFORM / "Definitions" /
                f"Def_{plan['definitions'][bundle_id]['definitionName']}.lean"
            for bundle_id in plan["definitionOrder"]
        }
        definition_deps = {
            bundle_id: set(plan["definitions"][bundle_id]["definitionDependencies"])
            for bundle_id in plan["definitionOrder"]
        }
        compile_dag(
            lean, env, definition_paths, definition_deps, log_handle, log_lock, jobs=8
        )
        theorem_paths = {
            command_id: PLATFORM / "Theorems" /
                f"Thm_{plan['nodes'][command_id]['slug']}.lean"
            for command_id in plan["nodeOrder"]
        }
        theorem_deps = {
            command_id: set(plan["nodes"][command_id]["typeTheoremDependencies"])
            for command_id in plan["nodeOrder"]
        }
        compile_dag(
            lean, env, theorem_paths, theorem_deps, log_handle, log_lock, jobs=8
        )
        solution_paths = {
            command_id: PLATFORM / "Solutions" /
                f"Sol_{plan['nodes'][command_id]['slug']}.lean"
            for command_id in plan["nodeOrder"]
        }
        compile_dag(
            lean, env, solution_paths, {key: set() for key in solution_paths},
            log_handle, log_lock, jobs=8,
        )
        path, returncode, output = compile_file(lean, env, PLATFORM / "All.lean")
        log_handle.write(f"===== {path.relative_to(ROOT)} =====\n{output}")
        if returncode != 0:
            raise RuntimeError(f"Lean failed for {path}; see {LOG}")
    run_type_audit(lean, plan)
    receipt = {
        "validatedAt": datetime.now(timezone.utc).isoformat(),
        "planSha256": sha256(PLAN_PATH),
        "payloadsSha256": sha256(PAYLOADS_PATH),
        "platformSha256": platform_digest(),
        "typeAuditFailures": 0,
        "definitions": len(plan["definitionOrder"]),
        "theorems": len(plan["nodeOrder"]),
        "solutions": len(plan["nodeOrder"]),
    }
    VALIDATION_RECEIPT.write_text(
        json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps({
        "definitions": len(plan["definitionOrder"]),
        "theorems": len(plan["nodeOrder"]),
        "solutions": len(plan["nodeOrder"]),
        "typeAudit": "exact modulo mapped names and universe display labels",
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except Exception as error:
        print(f"validation failed: {error}", file=sys.stderr)
        raise
