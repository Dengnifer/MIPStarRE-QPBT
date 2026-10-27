#!/usr/bin/env python3
"""Plan the private Prove2Me QPBT upload from sanctioned Lean extractors."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import unicodedata
from collections import defaultdict, deque
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parents[2]
EXTRACTED = ROOT / "prove2me" / "extracted"
GENERATED = ROOT / "prove2me" / "generated"
GRAPH = EXTRACTED / "decl_graph.jsonl"
BOUNDARY = EXTRACTED / "lidt_boundary.jsonl"
LIDT_INSTANCES = EXTRACTED / "lidt_instances.txt"
SKETCH_DIR = EXTRACTED / "sketch"
SKETCH_EXTRACTOR = ROOT / "prove2me" / "tools" / "extract_sketch_info.lean"
CONTEXT_DIR = EXTRACTED / "context"
CONTEXT_EXTRACTOR = ROOT / "prove2me" / "tools" / "extract_context_info.lean"
SIMP_DECLS = EXTRACTED / "simp_decls.txt"
PARTICIPATING_MODULES = EXTRACTED / "participating-modules.txt"
HEADER_INFO = EXTRACTED / "header-info.jsonl"
PLAN = GENERATED / "upload_plan.json"
PLAN_TSV = GENERATED / "upload_plan.tsv"
RENAME_TSV = GENERATED / "rename_map.tsv"
LIDT_NEEDS = Path("/home/drx/p2m/status/qpbt-needs-from-lidt.txt")
LIDT_NAMES = Path("/home/drx/p2m/status/lidt-names.tsv")
LIDT_PLAN = Path("/home/drx/p2m/MIPStarRE/prove2me/generated/upload_plan.json")
SOURCE_SHA = "8f4118aeea7be16912adbaee3df6dce1741a2c26"
TARGETS = (
    "MIPStarRE.QPBT.Palomar.exists_spcc_value_one",
    "MIPStarRE.QPBT.Palomar.exists_ld_soundness",
    "MIPStarRE.QPBT.Palomar.pauli_soundness",
    "MIPStarRE.QPBT.Palomar.pauli_soundness_qubit",
)
SPLIT_SENSITIVE_EMBEDDED = (
    # This proof unfolds definitions whose ZMod Fintype parameters contain a
    # generated NeZero proof.  Across an olean boundary that proof is opaque,
    # so the source's `simpa` only elaborates when kept with its source bundle.
    "MIPStarRE.QPBT.honestMeasurement_projective",
    "MIPStarRE.QPBT.honestMeasurement_effect_transpose",
)


def platform_project_name(name: str) -> str:
    if (
        name == "MIPStarRE.LDT"
        or name.startswith("MIPStarRE.LDT.")
        or name == "MIPStarRE.Quantum"
        or name.startswith("MIPStarRE.Quantum.")
    ):
        return "LIDT." + name
    return name


@dataclass(frozen=True)
class Position:
    line: int
    col: int
    offset: int

    @classmethod
    def from_json(cls, value: dict[str, int]) -> "Position":
        return cls(value["line"], value["col"], value["offset"])

    def as_json(self) -> dict[str, int]:
        return {"line": self.line, "col": self.col, "offset": self.offset}


@dataclass
class Command:
    command_id: str
    module: str
    index: int
    name_text: str | None
    start: Position
    end: Position
    val_start: Position | None
    val_kind: str | None
    docstring: dict[str, Any] | None
    private_tok: dict[str, Any] | None
    rows: list[str]
    anchor: str | None = None

    def as_json(self) -> dict[str, Any]:
        return {
            "commandId": self.command_id,
            "module": self.module,
            "index": self.index,
            "nameText": self.name_text,
            "declStart": self.start.as_json(),
            "declEnd": self.end.as_json(),
            "valStart": self.val_start.as_json() if self.val_start else None,
            "valKind": self.val_kind,
            "docstring": self.docstring,
            "privateTok": self.private_tok,
            "rows": self.rows,
            "anchor": self.anchor,
        }


def read_jsonl(path: Path) -> list[dict[str, Any]]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line]


def read_lines(path: Path) -> list[str]:
    return [line.strip() for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def source_path(module: str) -> Path:
    path = ROOT / (module.replace(".", "/") + ".lean")
    if not path.is_file():
        raise FileNotFoundError(f"missing source for {module}: {path}")
    return path


def sketch_path(module: str) -> Path:
    return SKETCH_DIR / (module.replace(".", "/") + ".jsonl")


def context_path(module: str) -> Path:
    return CONTEXT_DIR / (module.replace(".", "/") + ".jsonl")


def read_needs() -> list[str]:
    lines = read_lines(LIDT_NEEDS)
    if not lines or lines[-1] != "END":
        raise RuntimeError(f"incomplete LIDT declaration list: {LIDT_NEEDS}")
    names = lines[:-1]
    if names != sorted(set(names)):
        raise RuntimeError("LIDT declaration list must be sorted and unique")
    return names


def read_lidt_map(required: set[str], require_map: bool) -> dict[str, dict[str, str]]:
    if not LIDT_NAMES.is_file():
        if require_map:
            raise RuntimeError(f"LIDT upload map is not available: {LIDT_NAMES}")
        return {}
    lines = LIDT_NAMES.read_text(encoding="utf-8").splitlines()
    if not lines:
        raise RuntimeError(f"empty LIDT upload map: {LIDT_NAMES}")
    expected = [
        "original_name", "platform_name", "import_module", "entry_kind",
        "theorem_id", "note",
    ]
    if lines[0].split("\t") != expected:
        raise RuntimeError(f"unexpected LIDT upload map header: {lines[0]!r}")
    result: dict[str, dict[str, str]] = {}
    for number, line in enumerate(lines[1:], start=2):
        values = line.split("\t")
        if len(values) != len(expected):
            raise RuntimeError(f"bad LIDT map row {number}: expected 6 tab-separated fields")
        item = dict(zip(expected, values, strict=True))
        name = item["original_name"]
        if name in result:
            raise RuntimeError(f"duplicate LIDT map name: {name}")
        if not item["import_module"]:
            raise RuntimeError(f"LIDT map row has no import module: {name}")
        result[name] = item
    missing = sorted(required - result.keys())
    if missing and require_map:
        raise RuntimeError(f"LIDT upload map is missing {len(missing)} required names: {missing[:8]}")
    if missing:
        if not LIDT_PLAN.is_file():
            raise RuntimeError(f"LIDT upload plan is unavailable for provisional mapping: {LIDT_PLAN}")
        lidt_plan = json.loads(LIDT_PLAN.read_text(encoding="utf-8"))
        lidt_command_bundle = {
            command_id: bundle_id
            for bundle_id, bundle in lidt_plan["definitions"].items()
            for command_id in bundle["commands"]
        }
        for name in missing:
            command_id = lidt_plan["rowToCommand"].get(name)
            if command_id is None:
                raise RuntimeError(f"LIDT upload plan has no command for provisional name: {name}")
            command = lidt_plan["commands"][command_id]
            classification = command["classification"]
            if classification == "node":
                node = lidt_plan["nodes"][command_id]
                result[name] = {
                    "original_name": name,
                    "platform_name": node["platformName"],
                    "import_module": f"Theorems.Thm_{node['slug']}",
                    "entry_kind": "theorem",
                    "theorem_id": "",
                    "note": "provisional from LIDT upload plan",
                }
                continue
            bundle_id = command.get("definitionBundle") or lidt_command_bundle.get(command_id)
            if not bundle_id:
                raise RuntimeError(
                    f"LIDT provisional command is neither node nor definition material: {name}"
                )
            bundle = lidt_plan["definitions"][bundle_id]
            result[name] = {
                "original_name": name,
                "platform_name": "LIDT." + name,
                "import_module": f"Definitions.Def_{bundle['definitionName']}",
                "entry_kind": classification,
                "theorem_id": "",
                "note": "provisional from LIDT upload plan",
            }
    return {name: result[name] for name in sorted(required) if name in result}


def name_matches(name: str, name_text: str) -> bool:
    return name == name_text or name.endswith("." + name_text)


def choose_anchor(command: Command, rows: dict[str, dict[str, Any]]) -> str | None:
    candidates = [rows[name] for name in command.rows]
    if not candidates:
        return None
    if command.name_text is None:
        instances = [row for row in candidates if row["isInstance"]]
        pool = instances or candidates
    else:
        matches = [row for row in candidates if name_matches(row["userName"], command.name_text)]
        pool = matches or candidates
    kind_rank = {
        "theorem": 0, "def": 0, "opaque": 0, "inductive": 0,
        "ctor": 1, "rec": 2,
    }
    pool.sort(key=lambda row: (
        kind_rank.get(row["kind"], 3),
        row["userName"].count("."),
        len(row["userName"]),
        row["name"],
    ))
    return pool[0]["name"]


def topo_sort(items: Iterable[str], dependencies: dict[str, set[str]]) -> list[str]:
    item_set = set(items)
    deps = {item: set(dependencies.get(item, set())) & item_set for item in item_set}
    reverse: dict[str, set[str]] = defaultdict(set)
    indegree = {item: len(reqs) for item, reqs in deps.items()}
    for item, reqs in deps.items():
        for req in reqs:
            reverse[req].add(item)
    ready = sorted(item for item, degree in indegree.items() if degree == 0)
    result: list[str] = []
    while ready:
        item = ready.pop(0)
        result.append(item)
        for consumer in sorted(reverse.get(item, set())):
            indegree[consumer] -= 1
            if indegree[consumer] == 0:
                ready.append(consumer)
                ready.sort()
    if len(result) != len(item_set):
        cycle = sorted(item for item, degree in indegree.items() if degree)
        raise RuntimeError(f"dependency cycle among {len(cycle)} items: {cycle[:12]}")
    return result


GREEK = {
    "α": "alpha", "β": "beta", "γ": "gamma", "δ": "delta", "ε": "eps",
    "ζ": "zeta", "η": "eta", "θ": "theta", "ι": "iota", "κ": "kappa",
    "λ": "lambda", "μ": "mu", "ν": "nu", "ξ": "xi", "π": "pi",
    "ρ": "rho", "σ": "sigma", "τ": "tau", "φ": "phi", "χ": "chi",
    "ψ": "psi", "ω": "omega", "Γ": "Gamma", "Δ": "Delta", "Θ": "Theta",
    "Λ": "Lambda", "Ξ": "Xi", "Π": "Pi", "Σ": "Sigma", "Φ": "Phi",
    "Ψ": "Psi", "Ω": "Omega",
}
SUBSCRIPT = {
    "₀": "0", "₁": "1", "₂": "2", "₃": "3", "₄": "4",
    "₅": "5", "₆": "6", "₇": "7", "₈": "8", "₉": "9",
}


def ascii_segment(segment: str) -> str:
    out: list[str] = []
    for char in segment:
        if char.isascii() and (char.isalnum() or char == "_"):
            out.append(char)
        elif char == "'":
            out.append("_prime")
        elif char in GREEK:
            out.append("_" + GREEK[char])
        elif char in SUBSCRIPT:
            out.append("_" + SUBSCRIPT[char])
        else:
            label = unicodedata.name(char, "").lower().replace(" ", "_").replace("-", "_")
            out.append("_" + (label or f"u{ord(char):04x}"))
    value = re.sub(r"_+", "_", "".join(out)).strip("_")
    if not value:
        value = "decl"
    if value[0].isdigit():
        value = "n_" + value
    return value


def ascii_name(name: str) -> str:
    return ".".join(ascii_segment(segment) for segment in name.split("."))


def command_name(command: Command, rows: dict[str, dict[str, Any]]) -> str:
    if command.anchor is None:
        raise RuntimeError(f"command has no anchor: {command.command_id}")
    return rows[command.anchor]["userName"]


def load_headers(modules: list[str]) -> tuple[dict[str, list[str]], dict[str, dict[str, Any]]]:
    module_by_source = {
        str(source_path(module).relative_to(ROOT)): module for module in modules
    }
    imports: dict[str, list[str]] = {module: [] for module in modules}
    header_meta: dict[str, dict[str, Any]] = {module: {} for module in modules}
    for fact in read_jsonl(HEADER_INFO):
        source = fact["source"]
        if source not in module_by_source:
            raise RuntimeError(f"header fact for non-participating source: {source}")
        module = module_by_source[source]
        if fact["kind"] == "import":
            imports[module].append(fact["module"])
        elif fact["kind"] == "header":
            header_meta[module]["headerEnd"] = fact["end"]
        elif fact["kind"] in {"moduleToken", "preludeToken"}:
            header_meta[module][fact["kind"]] = fact["range"]
    missing = [module for module in modules if "headerEnd" not in header_meta[module]]
    if missing:
        raise RuntimeError(f"missing exact header facts for {len(missing)} modules: {missing[:8]}")
    return imports, header_meta


def split_bundles(
    def_commands: set[str],
    embedded_commands: set[str],
    commands: dict[str, Command],
) -> tuple[dict[str, list[str]], dict[str, str]]:
    by_module: dict[str, list[str]] = defaultdict(list)
    for command_id in def_commands | embedded_commands:
        by_module[commands[command_id].module].append(command_id)
    bundles = {
        module: sorted(command_ids, key=lambda cid: commands[cid].index)
        for module, command_ids in sorted(by_module.items())
    }
    command_bundle = {
        command_id: module
        for module, command_ids in bundles.items()
        for command_id in command_ids
    }
    return bundles, command_bundle


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--wrapper",
        default="",
        help="whole-project namespace wrapper selected only after collision search",
    )
    parser.add_argument(
        "--require-lidt-map",
        action="store_true",
        help="fail unless the completed LIDT upload map covers every requested declaration",
    )
    args = parser.parse_args()
    wrapper = args.wrapper.strip(".")
    if wrapper and ascii_name(wrapper) != wrapper:
        raise RuntimeError(f"wrapper must be a conservative ASCII namespace: {wrapper!r}")

    graph_rows = read_jsonl(GRAPH)
    boundary_rows = read_jsonl(BOUNDARY)
    rows = {row["name"]: row for row in graph_rows}
    boundary = {row["name"]: row for row in boundary_rows}
    if rows.keys() != boundary.keys():
        raise RuntimeError("Stage 1 graph and LIDT boundary declaration sets differ")
    by_user: dict[str, list[str]] = defaultdict(list)
    for row in graph_rows:
        by_user[row["userName"]].append(row["name"])

    modules = read_lines(PARTICIPATING_MODULES)
    if len(modules) != len(set(modules)):
        raise RuntimeError("participating module list contains duplicates")
    module_set = set(modules)
    graph_modules = {row["module"] for row in graph_rows}
    if not graph_modules <= module_set:
        raise RuntimeError(f"graph has modules outside participating closure: {sorted(graph_modules - module_set)}")
    missing_sketch = []
    missing_context = []
    for module in modules:
        path = sketch_path(module)
        source = source_path(module)
        if (
            not path.is_file()
            or path.stat().st_mtime_ns <= source.stat().st_mtime_ns
            or path.stat().st_mtime_ns <= SKETCH_EXTRACTOR.stat().st_mtime_ns
        ):
            missing_sketch.append(module)
        context = context_path(module)
        if (
            not context.is_file()
            or context.stat().st_mtime_ns <= source.stat().st_mtime_ns
            or context.stat().st_mtime_ns <= CONTEXT_EXTRACTOR.stat().st_mtime_ns
        ):
            missing_context.append(module)
    if missing_sketch:
        raise RuntimeError(f"Stage 2 is incomplete; missing {len(missing_sketch)} modules")
    if missing_context:
        raise RuntimeError(
            f"context extraction is incomplete; missing {len(missing_context)} modules"
        )

    commands: dict[str, Command] = {}
    module_commands: dict[str, list[str]] = defaultdict(list)
    row_to_command: dict[str, str] = {}
    context_generated_rows: set[str] = set()
    source_ref_names: dict[str, set[str]] = defaultdict(set)
    context_ref_names: dict[str, list[tuple[int, str]]] = defaultdict(list)
    local_instance_commands: set[str] = set()
    active_local_instances: dict[str, set[str]] = defaultdict(set)
    rows_by_module: dict[str, list[dict[str, Any]]] = defaultdict(list)
    private_ref_rows: dict[tuple[str, str], list[str]] = defaultdict(list)
    for row in graph_rows:
        rows_by_module[row["module"]].append(row)
        private_prefix = f"_private.{row['module']}."
        if row["isPrivate"] and row["name"].startswith(private_prefix):
            stage2_name = "_private." + row["name"][len(private_prefix):]
            private_ref_rows[(row["module"], stage2_name)].append(row["name"])
    for module in modules:
        facts = read_jsonl(sketch_path(module))
        decls = [fact for fact in facts if fact["kind"] == "decl"]
        refs = [fact for fact in facts if fact["kind"] == "ref"]
        for index, fact in enumerate(decls):
            command_id = f"{module}#{index:04d}"
            command = Command(
                command_id=command_id,
                module=module,
                index=index,
                name_text=fact["nameText"],
                start=Position.from_json(fact["declStart"]),
                end=Position.from_json(fact["declEnd"]),
                val_start=Position.from_json(fact["valStart"]) if fact["valStart"] else None,
                val_kind=fact["valKind"],
                docstring=fact["docstring"],
                private_tok=fact["privateTok"],
                rows=[],
            )
            commands[command_id] = command
            module_commands[module].append(command_id)
        for row in (item for item in rows_by_module[module] if item["startLine"] > 0):
            containing = [
                commands[cid] for cid in module_commands[module]
                if commands[cid].start.line <= row["startLine"] <= commands[cid].end.line
            ]
            if not containing:
                context_generated_rows.add(row["name"])
                continue
            if len(containing) != 1:
                raise RuntimeError(
                    f"expected one Stage 2 command for {row['name']} at "
                    f"{module}:{row['startLine']}; found {len(containing)}"
                )
            containing[0].rows.append(row["name"])
            row_to_command[row["name"]] = containing[0].command_id
        for command_id in module_commands[module]:
            commands[command_id].anchor = choose_anchor(commands[command_id], rows)
        commands_by_key = {
            (commands[command_id].start.offset, commands[command_id].end.offset): command_id
            for command_id in module_commands[module]
        }
        context_facts = read_jsonl(context_path(module))
        for fact in context_facts:
            if fact["kind"] != "declHead" or fact["keyword"] != "instance":
                continue
            if not fact.get("isLocal", False):
                continue
            key = (fact["declStart"]["offset"], fact["declEnd"]["offset"])
            command_id = commands_by_key.get(key)
            if command_id is None:
                raise RuntimeError(f"local instance has no Stage 2 command in {module}: {key}")
            local_instance_commands.add(command_id)
        for target_id in module_commands[module]:
            target_start = commands[target_id].start.offset
            frames: list[set[str]] = [set()]
            for fact in context_facts:
                offsets = fact.get("range")
                start = (
                    offsets["start"]["offset"] if offsets is not None
                    else fact.get("declStart", {}).get("offset")
                )
                if start is None or start >= target_start:
                    break
                kind = fact["kind"]
                if kind in {"namespace", "section"}:
                    frames.append(set())
                elif kind == "end":
                    if len(frames) == 1:
                        raise RuntimeError(f"unmatched end before {target_id}")
                    frames.pop()
                elif (
                    kind == "declHead"
                    and fact["keyword"] == "instance"
                    and fact.get("isLocal", False)
                    and fact["declEnd"]["offset"] <= target_start
                ):
                    key = (fact["declStart"]["offset"], fact["declEnd"]["offset"])
                    instance_id = commands_by_key.get(key)
                    if instance_id is None:
                        raise RuntimeError(
                            f"active local instance has no command in {module}: {key}"
                        )
                    frames[-1].add(instance_id)
            active_local_instances[target_id].update(
                instance_id for frame in frames for instance_id in frame
            )
        for ref in refs:
            ref_start = ref["start"]["offset"]
            ref_end = ref["end"]["offset"]
            containing = [
                commands[cid] for cid in module_commands[module]
                if commands[cid].start.offset <= ref_start < ref_end <= commands[cid].end.offset
            ]
            if len(containing) == 1:
                source_ref_names[containing[0].command_id].add(ref["const"])
            elif not containing:
                context_ref_names[module].append((ref_start, ref["const"]))
            else:
                raise RuntimeError(
                    f"reference at {module}:{ref_start} belongs to multiple commands"
                )

    def resolve(name: str) -> str:
        if name in rows:
            return name
        matches = by_user.get(name, [])
        if len(matches) == 1:
            return matches[0]
        raise RuntimeError(f"cannot uniquely resolve declaration {name!r}: {matches}")

    def resolve_reference(module: str, name: str) -> str | None:
        if name in rows:
            return name
        matches = by_user.get(name, [])
        if len(matches) == 1:
            return matches[0]
        private_matches = private_ref_rows.get((module, name), [])
        if len(private_matches) == 1:
            return private_matches[0]
        if len(private_matches) > 1:
            raise RuntimeError(
                f"ambiguous private reference {name!r} in {module}: {private_matches}"
            )
        return None

    if not SIMP_DECLS.is_file():
        raise RuntimeError(f"missing supplemental simp-declaration extraction: {SIMP_DECLS}")
    simp_rows = {
        resolve(line.strip())
        for line in SIMP_DECLS.read_text(encoding="utf-8").splitlines()
        if line.strip()
    }
    source_ref_rows: dict[str, set[str]] = defaultdict(set)
    for command_id, names in source_ref_names.items():
        for name in names:
            resolved = resolve_reference(commands[command_id].module, name)
            if resolved is not None:
                source_ref_rows[command_id].add(resolved)
            elif name.startswith("_private."):
                raise RuntimeError(
                    f"cannot resolve private source reference {name!r} in {command_id}"
                )
    context_ref_rows: dict[str, set[str]] = defaultdict(set)
    for command_id, command in commands.items():
        for offset, name in context_ref_names[command.module]:
            if offset >= command.start.offset:
                continue
            resolved = resolve_reference(command.module, name)
            if resolved is not None:
                context_ref_rows[command_id].add(resolved)
            elif name.startswith("MIPStarRE.QPBT."):
                raise RuntimeError(
                    f"cannot resolve project context reference {name!r} before {command_id}"
                )
            elif name.startswith("_private."):
                raise RuntimeError(
                    f"cannot resolve private context reference {name!r} before {command_id}"
                )

    target_rows = {target: resolve(target) for target in TARGETS}
    root_rows = [
        *target_rows.values(),
        *(row["name"] for row in graph_rows if row["isInstance"]),
        *(row for command_id in local_instance_commands for row in commands[command_id].rows),
        *simp_rows,
    ]
    constructors: dict[str, set[str]] = defaultdict(set)
    for row in graph_rows:
        if row["kind"] != "ctor":
            continue
        for dependency in row["typeDeps"]:
            if dependency in rows and rows[dependency]["kind"] == "inductive":
                constructors[dependency].add(row["name"])

    reachable_rows: set[str] = set()
    work = deque(root_rows)
    while work:
        name = work.popleft()
        if name in reachable_rows:
            continue
        row = rows.get(name)
        if row is None:
            raise RuntimeError(f"project dependency absent from Stage 1 graph: {name}")
        reachable_rows.add(name)
        work.extend(row["typeDeps"])
        work.extend(row["valueDeps"])
        if name in row_to_command:
            work.extend(source_ref_rows[row_to_command[name]])
        if row["kind"] == "inductive":
            work.extend(constructors[name])

    reachable_commands = {
        row_to_command[name] for name in reachable_rows if name in row_to_command
    }
    material_cache: dict[str, set[str]] = {}

    def material_commands(name: str, visiting: set[str] | None = None) -> set[str]:
        if name in material_cache:
            return material_cache[name]
        if name in row_to_command:
            result = {row_to_command[name]}
            material_cache[name] = result
            return result
        row = rows.get(name)
        if row is None:
            return set()
        visiting = set() if visiting is None else set(visiting)
        if name in visiting:
            return set()
        visiting.add(name)
        result: set[str] = set()
        for dependency in [*row["typeDeps"], *row["valueDeps"]]:
            result.update(material_commands(dependency, visiting))
        material_cache[name] = result
        return result

    command_type_deps: dict[str, set[str]] = defaultdict(set)
    command_value_deps: dict[str, set[str]] = defaultdict(set)
    command_lidt_type: dict[str, set[str]] = defaultdict(set)
    command_lidt_value: dict[str, set[str]] = defaultdict(set)
    context_lidt_by_module: dict[str, set[str]] = defaultdict(set)
    for row_name in reachable_rows & context_generated_rows:
        ext = boundary[row_name]
        context_lidt_by_module[rows[row_name]["module"]].update(
            ext["lidtTypeDeps"] + ext["lidtValueDeps"]
        )
    for command_id in reachable_commands:
        command = commands[command_id]
        for row_name in command.rows:
            if row_name not in reachable_rows:
                continue
            row = rows[row_name]
            ext = boundary[row_name]
            for dependency in row["typeDeps"]:
                command_type_deps[command_id].update(material_commands(dependency))
            for dependency in row["valueDeps"]:
                command_value_deps[command_id].update(material_commands(dependency))
            command_lidt_type[command_id].update(ext["lidtTypeDeps"])
            command_lidt_value[command_id].update(ext["lidtValueDeps"])
        for dependency in source_ref_rows[command_id]:
            command_value_deps[command_id].update(material_commands(dependency))
        for dependency in context_ref_rows[command_id]:
            command_type_deps[command_id].update(material_commands(dependency))
        command_type_deps[command_id].update(active_local_instances[command_id])
        command_lidt_type[command_id].update(context_lidt_by_module[command.module])
        command_type_deps[command_id].discard(command_id)
        command_value_deps[command_id].discard(command_id)
        command_type_deps[command_id].intersection_update(reachable_commands)
        command_value_deps[command_id].intersection_update(reachable_commands)

    def is_theorem_command(command_id: str) -> bool:
        if command_id in local_instance_commands:
            return False
        command = commands[command_id]
        if command.val_kind == "alias":
            return False
        if command.anchor is None:
            return False
        if rows[command.anchor]["kind"] == "theorem":
            return True
        source_kinds = {rows[name]["kind"] for name in command.rows if name in reachable_rows}
        return source_kinds == {"theorem"}

    def is_private(command_id: str) -> bool:
        return any(rows[name]["isPrivate"] for name in commands[command_id].rows
                   if name in reachable_rows)

    def_commands = {cid for cid in reachable_commands if not is_theorem_command(cid)}
    simp_commands = {
        row_to_command[name] for name in simp_rows
        if name in row_to_command and row_to_command[name] in reachable_commands
        and is_theorem_command(row_to_command[name])
    }
    split_sensitive_commands = {
        row_to_command[resolve(name)] for name in SPLIT_SENSITIVE_EMBEDDED
    }
    if not split_sensitive_commands <= reachable_commands:
        raise RuntimeError("split-sensitive embedded theorem is not reachable")
    if not all(is_theorem_command(command_id) for command_id in split_sensitive_commands):
        raise RuntimeError("split-sensitive embedded declaration is not a theorem command")
    embedded_commands: set[str] = set(simp_commands | split_sensitive_commands)
    embed_work = deque(sorted(def_commands | embedded_commands))
    seen_embed_sources: set[str] = set()
    while embed_work:
        command_id = embed_work.popleft()
        if command_id in seen_embed_sources:
            continue
        seen_embed_sources.add(command_id)
        for dependency in command_type_deps[command_id] | command_value_deps[command_id]:
            if is_theorem_command(dependency) and dependency not in embedded_commands:
                embedded_commands.add(dependency)
                embed_work.append(dependency)
            elif dependency in def_commands:
                embed_work.append(dependency)

    theorem_candidates = {
        cid for cid in reachable_commands
        if is_theorem_command(cid) and cid not in embedded_commands
    }
    mandatory_commands = {row_to_command[row_name] for row_name in target_rows.values()}
    missing_target_commands = [
        target for target, row_name in target_rows.items()
        if row_name not in row_to_command
    ]
    if missing_target_commands:
        raise RuntimeError(f"targets have no source command: {missing_target_commands}")

    source_text = {module: source_path(module).read_text(encoding="utf-8") for module in modules}
    consumers: dict[str, set[str]] = defaultdict(set)
    for consumer in reachable_commands:
        for dependency in command_type_deps[consumer] | command_value_deps[consumer]:
            consumers[dependency].add(consumer)

    proof_lines: dict[str, int] = {}
    paper_signal: dict[str, bool] = {}
    cross_file_signal: dict[str, bool] = {}
    for command_id in theorem_candidates:
        command = commands[command_id]
        proof_lines[command_id] = (
            max(0, command.end.line - command.val_start.line) if command.val_start else 0
        )
        snippet = source_text[command.module][command.start.offset:command.end.offset].lower()
        paper_signal[command_id] = any(marker in snippet for marker in (
            "paper", "thm:", "lem:", "prop:", "references/qpbt-paper",
        ))
        cross_file_signal[command_id] = any(
            commands[consumer].module != command.module for consumer in consumers[command_id]
        )

    nodes = set(mandatory_commands)
    for command_id in theorem_candidates:
        if is_private(command_id):
            continue
        lines = proof_lines[command_id]
        promoted = (
            commands[command_id].docstring is not None
            or paper_signal[command_id]
            or cross_file_signal[command_id]
        )
        if lines > 40 or (11 <= lines <= 40 and promoted):
            nodes.add(command_id)

    changed = True
    while changed:
        changed = False
        for node in list(nodes):
            for dependency in command_type_deps[node]:
                if dependency in theorem_candidates and dependency not in nodes:
                    nodes.add(dependency)
                    changed = True
        for command_id in theorem_candidates - nodes:
            if is_private(command_id) or not (11 <= proof_lines[command_id] <= 40):
                continue
            node_consumers = {consumer for consumer in consumers[command_id] if consumer in nodes}
            if len(node_consumers) >= 2:
                nodes.add(command_id)
                changed = True

    inline_commands = theorem_candidates - nodes
    classifications: dict[str, str] = {}
    classifications.update({cid: "def-material" for cid in def_commands})
    classifications.update({cid: "def-embedded-theorem" for cid in embedded_commands})
    classifications.update({cid: "node" for cid in nodes})
    classifications.update({cid: "inline-helper" for cid in inline_commands})

    bundles, command_bundle = split_bundles(def_commands, embedded_commands, commands)
    bundle_dependencies: dict[str, set[str]] = defaultdict(set)
    module_bundles: dict[str, list[str]] = defaultdict(list)
    for bundle_id, command_ids in bundles.items():
        module_bundles[commands[command_ids[0]].module].append(bundle_id)
        for command_id in command_ids:
            for dependency in command_type_deps[command_id] | command_value_deps[command_id]:
                if dependency in def_commands or dependency in embedded_commands:
                    dep_bundle = command_bundle[dependency]
                    if dep_bundle != bundle_id:
                        bundle_dependencies[bundle_id].add(dep_bundle)
                elif dependency in nodes or dependency in inline_commands:
                    raise RuntimeError(
                        f"definition bundle {bundle_id} depends on non-embedded theorem "
                        f"{command_name(commands[dependency], rows)}"
                    )
    for module, bundle_ids in module_bundles.items():
        bundle_ids.sort(key=lambda bid: commands[bundles[bid][0]].index)
        for previous, current in zip(bundle_ids, bundle_ids[1:]):
            bundle_dependencies[current].add(previous)

    deprivatized: set[str] = {
        command_id for command_id in nodes if is_private(command_id)
    }
    for command_id in def_commands | embedded_commands:
        if not is_private(command_id):
            continue
        own_bundle = command_bundle[command_id]
        if any(
            consumer not in command_bundle or command_bundle[consumer] != own_bundle
            for consumer in consumers[command_id]
        ):
            deprivatized.add(command_id)
    missing_private_tokens = [
        command_name(commands[cid], rows) for cid in deprivatized
        if commands[cid].private_tok is None
    ]
    if missing_private_tokens:
        raise RuntimeError(
            "cannot deprivatize commands without an exact private token range: "
            + ", ".join(missing_private_tokens[:8])
        )

    definition_order = topo_sort(bundles, bundle_dependencies)
    bundle_name: dict[str, str] = {}
    used_bundle_names: set[str] = set()
    for bundle_id in definition_order:
        base = "QPBT_" + bundle_id.replace("#", "_").replace(".", "_")
        candidate = ascii_segment(base)
        if candidate in used_bundle_names:
            candidate += "_" + hashlib.sha256(bundle_id.encode()).hexdigest()[:10]
        used_bundle_names.add(candidate)
        bundle_name[bundle_id] = candidate

    project_name_map = {
        rows[name]["userName"]: platform_project_name(rows[name]["userName"])
        for name in reachable_rows
        if rows[name]["startLine"] > 0
        and platform_project_name(rows[name]["userName"]) != rows[name]["userName"]
    }
    used_platform_names: dict[str, str] = {}
    platform_name: dict[str, str] = {}
    rename_map: dict[str, str] = dict(project_name_map)
    for command_id in sorted(nodes):
        original = command_name(commands[command_id], rows)
        base = platform_project_name(original)
        wrapped = f"{wrapper}.{base}" if wrapper else base
        candidate = ascii_name(wrapped)
        if candidate in used_platform_names and used_platform_names[candidate] != original:
            candidate += "_" + hashlib.sha256(original.encode()).hexdigest()[:10]
        used_platform_names[candidate] = original
        platform_name[command_id] = candidate
        if candidate != original and (base != original or candidate != wrapped):
            rename_map[original] = candidate

    node_dependencies: dict[str, set[str]] = defaultdict(set)
    node_inline_closure: dict[str, set[str]] = defaultdict(set)
    node_def_bundles: dict[str, set[str]] = defaultdict(set)
    node_type_nodes: dict[str, set[str]] = defaultdict(set)
    node_lidt_type: dict[str, set[str]] = defaultdict(set)
    node_lidt_solution: dict[str, set[str]] = defaultdict(set)
    for node in nodes:
        node_lidt_type[node].update(command_lidt_type[node])
        node_lidt_solution[node].update(command_lidt_type[node] | command_lidt_value[node])
        work_commands = deque(sorted(command_type_deps[node] | command_value_deps[node]))
        seen_commands: set[str] = set()
        while work_commands:
            dependency = work_commands.popleft()
            if dependency == node or dependency in seen_commands:
                continue
            seen_commands.add(dependency)
            if dependency in def_commands or dependency in embedded_commands:
                node_def_bundles[node].add(command_bundle[dependency])
            elif dependency in nodes:
                node_dependencies[node].add(dependency)
            elif dependency in inline_commands:
                node_inline_closure[node].add(dependency)
                node_lidt_solution[node].update(
                    command_lidt_type[dependency] | command_lidt_value[dependency]
                )
                work_commands.extend(command_type_deps[dependency])
                work_commands.extend(command_value_deps[dependency])
        for dependency in command_type_deps[node]:
            if dependency in nodes:
                node_type_nodes[node].add(dependency)
            elif dependency in inline_commands:
                raise RuntimeError(
                    f"node statement for {command_name(commands[node], rows)} depends on "
                    f"inline theorem {command_name(commands[dependency], rows)}"
                )
    node_order = topo_sort(nodes, node_dependencies)

    project_imports, header_meta = load_headers(modules)
    mathlib_cache: dict[str, set[str]] = {}
    lidt_source_cache: dict[str, set[str]] = {}

    def transitive_external(module: str, visiting: set[str] | None = None) -> tuple[set[str], set[str]]:
        if module in mathlib_cache:
            return mathlib_cache[module], lidt_source_cache[module]
        visiting = set() if visiting is None else set(visiting)
        if module in visiting:
            return set(), set()
        visiting.add(module)
        mathlib: set[str] = set()
        lidt_source: set[str] = set()
        for imported in project_imports[module]:
            if imported in module_set:
                child_mathlib, child_lidt = transitive_external(imported, visiting)
                mathlib.update(child_mathlib)
                lidt_source.update(child_lidt)
            elif imported == "Mathlib" or imported.startswith("Mathlib."):
                mathlib.add(imported)
            elif imported.startswith("MIPStarRE."):
                lidt_source.add(imported)
            else:
                raise RuntimeError(
                    f"disallowed external import {imported!r} in {module}; "
                    "QPBT uploads may import only Mathlib and mapped LIDT entries"
                )
        mathlib_cache[module] = mathlib
        lidt_source_cache[module] = lidt_source
        return mathlib, lidt_source

    module_metadata: dict[str, dict[str, Any]] = {}
    for module in modules:
        mathlib, lidt_source = transitive_external(module)
        module_metadata[module] = {
            "source": str(source_path(module).relative_to(ROOT)),
            "projectImports": [name for name in project_imports[module] if name in module_set],
            "sourceLidtImports": sorted(lidt_source),
            "mathlibImports": sorted(mathlib),
            **header_meta[module],
        }

    needs = read_needs()
    required_lidt = set(needs)
    discovered_lidt = set(read_lines(LIDT_INSTANCES))
    for name in reachable_rows:
        discovered_lidt.update(boundary[name]["lidtTypeDeps"])
        discovered_lidt.update(boundary[name]["lidtValueDeps"])
    if discovered_lidt != required_lidt:
        raise RuntimeError(
            "current reachable LIDT boundary differs from the coordinated needs file: "
            f"missing={sorted(discovered_lidt - required_lidt)[:8]}, "
            f"extra={sorted(required_lidt - discovered_lidt)[:8]}"
        )
    lidt_map = read_lidt_map(required_lidt, args.require_lidt_map)
    global_lidt_instances = set(read_lines(LIDT_INSTANCES))

    def mapped_imports(names: set[str]) -> list[str]:
        if not lidt_map:
            return []
        return sorted({
            lidt_map[name]["import_module"] for name in names if name in lidt_map
        })

    bundle_lidt_names: dict[str, set[str]] = defaultdict(set)
    for bundle_id, command_ids in bundles.items():
        bundle_lidt_names[bundle_id].update(global_lidt_instances)
        for command_id in command_ids:
            bundle_lidt_names[bundle_id].update(
                command_lidt_type[command_id] | command_lidt_value[command_id]
            )

    commands_json: dict[str, Any] = {}
    for command_id in sorted(reachable_commands):
        command = commands[command_id]
        entry = command.as_json()
        entry.update({
            "classification": classifications[command_id],
            "proofLines": proof_lines.get(command_id),
            "isPrivate": is_private(command_id),
            "isLocalInstance": command_id in local_instance_commands,
            "deprivatize": command_id in deprivatized,
            "typeCommandDeps": sorted(command_type_deps[command_id]),
            "valueCommandDeps": sorted(command_value_deps[command_id]),
            "lidtTypeDeps": sorted(command_lidt_type[command_id]),
            "lidtValueDeps": sorted(command_lidt_value[command_id]),
            "definitionBundle": command_bundle.get(command_id),
        })
        commands_json[command_id] = entry

    target_set = set(TARGETS)
    node_json: dict[str, Any] = {}
    all_command_deps = {
        command_id: command_type_deps[command_id] | command_value_deps[command_id]
        for command_id in reachable_commands
    }
    for command_id in sorted(nodes):
        command = commands[command_id]
        original = command_name(command, rows)
        theorem_lidt_names = node_lidt_type[command_id] | global_lidt_instances
        solution_lidt_names = node_lidt_solution[command_id] | global_lidt_instances
        node_json[command_id] = {
            "originalName": original,
            "platformName": platform_name[command_id],
            "slug": platform_name[command_id].replace(".", "_"),
            "module": command.module,
            "source": module_metadata[command.module]["source"],
            "sourceLines": [command.start.line, command.end.line],
            "proofLines": proof_lines[command_id],
            "definitionBundles": sorted(node_def_bundles[command_id]),
            "theoremDependencies": sorted(node_dependencies[command_id]),
            "typeTheoremDependencies": sorted(node_type_nodes[command_id]),
            "inlineCommands": topo_sort(
                node_inline_closure[command_id], all_command_deps
            ),
            "deprivatize": command_id in deprivatized,
            "isTarget": original in target_set,
            "lidtTheoremNames": sorted(theorem_lidt_names),
            "lidtTheoremImports": mapped_imports(theorem_lidt_names),
            "lidtSolutionNames": sorted(solution_lidt_names),
            "lidtSolutionImports": mapped_imports(solution_lidt_names),
        }

    definitions_json: dict[str, Any] = {}
    for bundle_id in sorted(bundles):
        command_ids = bundles[bundle_id]
        module = commands[command_ids[0]].module
        definitions_json[bundle_id] = {
            "definitionName": bundle_name[bundle_id],
            "slug": bundle_name[bundle_id],
            "module": module,
            "source": module_metadata[module]["source"],
            "sourceLines": [
                min(commands[cid].start.line for cid in command_ids),
                max(commands[cid].end.line for cid in command_ids),
            ],
            "commands": command_ids,
            "definitionDependencies": sorted(bundle_dependencies[bundle_id]),
            "lidtNames": sorted(bundle_lidt_names[bundle_id]),
            "lidtImports": mapped_imports(bundle_lidt_names[bundle_id]),
            "approxSourceLines": sum(
                max(1, commands[cid].end.line - commands[cid].start.line + 1)
                for cid in command_ids
            ),
        }

    external_rename_map: dict[str, str] = {}
    for name, item in lidt_map.items():
        if item["entry_kind"] == "definition" and item["note"] == "module bundle":
            if not name.startswith("MIPStarRE."):
                raise RuntimeError(f"unexpected LIDT module-bundle declaration: {name}")
            external_rename_map[name] = "LIDT." + name
        elif item["platform_name"]:
            external_rename_map[name] = item["platform_name"]
    plan = {
        "schemaVersion": 2,
        "sourceCommit": SOURCE_SHA,
        "uploadNamespace": wrapper,
        "tag": "QPBT",
        "targets": list(TARGETS),
        "private": True,
        "counts": {
            "graphRows": len(graph_rows),
            "participatingModules": len(modules),
            "rootRows": len(set(root_rows)),
            "simpDeclarations": len(simp_rows),
            "reachableRows": len(reachable_rows),
            "spanlessReachableRows": sum(rows[name]["startLine"] == 0 for name in reachable_rows),
            "reachableCommands": len(reachable_commands),
            "definitionBundles": len(bundles),
            "defMaterialCommands": len(def_commands),
            "defEmbeddedTheoremCommands": len(embedded_commands),
            "theoremNodes": len(nodes),
            "inlineHelpers": len(inline_commands),
            "deprivatizedCommands": len(deprivatized),
            "renamedNodes": len(rename_map),
            "requiredLidtNames": len(required_lidt),
            "resolvedLidtNames": len(lidt_map),
        },
        "roots": sorted(set(root_rows)),
        "reachableRows": sorted(reachable_rows),
        "rowToCommand": row_to_command,
        "contextGeneratedRows": sorted(context_generated_rows & reachable_rows),
        "commands": commands_json,
        "modules": module_metadata,
        "definitions": definitions_json,
        "nodes": node_json,
        "definitionOrder": definition_order,
        "nodeOrder": node_order,
        "renameMap": rename_map,
        "projectNameMap": project_name_map,
        "externalNameMap": external_rename_map,
        "lidt": {
            "needsFile": str(LIDT_NEEDS),
            "namesFile": str(LIDT_NAMES),
            "required": needs,
            "resolved": bool(lidt_map),
            "globalInstances": sorted(global_lidt_instances),
            "mapping": lidt_map,
        },
    }

    GENERATED.mkdir(parents=True, exist_ok=True)
    PLAN.write_text(json.dumps(plan, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    tsv_lines = ["class\toriginal_name\tplatform_name\tmodule\tproof_lines\tflags"]
    for bundle_id in definition_order:
        bundle = definitions_json[bundle_id]
        tsv_lines.append(
            f"definition\t{bundle_id}\t{bundle['definitionName']}\t{bundle['module']}\t\t"
        )
    for command_id in node_order:
        node = node_json[command_id]
        flags = ",".join(flag for flag, enabled in (
            ("target", node["isTarget"]),
            ("deprivatized", node["deprivatize"]),
        ) if enabled)
        tsv_lines.append(
            f"theorem\t{node['originalName']}\t{node['platformName']}\t{node['module']}\t"
            f"{node['proofLines']}\t{flags}"
        )
    PLAN_TSV.write_text("\n".join(tsv_lines) + "\n", encoding="utf-8")
    rename_lines = ["generated_source_name\tplatform_name"]
    rename_lines.extend(f"{source}\t{target}" for source, target in sorted(rename_map.items()))
    RENAME_TSV.write_text("\n".join(rename_lines) + "\n", encoding="utf-8")

    print(json.dumps(plan["counts"], sort_keys=True))
    print(f"wrote {PLAN.relative_to(ROOT)}")
    print(f"wrote {PLAN_TSV.relative_to(ROOT)}")
    print(f"wrote {RENAME_TSV.relative_to(ROOT)}")
    if not lidt_map:
        print(f"LIDT map not yet available; rerun with --require-lidt-map after {LIDT_NAMES} exists")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
