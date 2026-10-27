#!/usr/bin/env python3
"""Extract exact structural command ranges for all participating modules."""

from __future__ import annotations

import argparse
import subprocess
import threading
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
MODULES = ROOT / "prove2me" / "extracted" / "participating-modules.txt"
OUT = ROOT / "prove2me" / "extracted" / "context"
EXTRACTOR = ROOT / "prove2me" / "tools" / "extract_context_info.lean"
PROGRESS = ROOT / "prove2me" / "records" / "context-progress.log"


def paths(module: str) -> tuple[Path, Path]:
    relative = Path(*module.split("."))
    return ROOT / relative.with_suffix(".lean"), OUT / relative.with_suffix(".jsonl")


def current(source: Path, output: Path) -> bool:
    return (
        output.is_file()
        and output.stat().st_mtime_ns > source.stat().st_mtime_ns
        and output.stat().st_mtime_ns > EXTRACTOR.stat().st_mtime_ns
    )


def extract(module: str) -> tuple[str, str]:
    source, output = paths(module)
    if current(source, output):
        return module, "cached"
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_suffix(f".jsonl.tmp.{threading.get_ident()}")
    with temporary.open("w", encoding="utf-8") as handle:
        result = subprocess.run(
            ["lake", "env", "lean", "--run", str(EXTRACTOR), str(source)],
            cwd=ROOT,
            text=True,
            stdout=handle,
            stderr=subprocess.PIPE,
            check=False,
        )
    if result.returncode != 0:
        temporary.unlink(missing_ok=True)
        raise RuntimeError(f"context extraction failed for {module}:\n{result.stderr}")
    temporary.replace(output)
    return module, "extract"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--jobs", type=int, default=8)
    args = parser.parse_args()
    if not 1 <= args.jobs <= 16:
        raise RuntimeError("jobs must be between 1 and 16")
    modules = [line for line in MODULES.read_text(encoding="utf-8").splitlines() if line]
    completed = 0
    with PROGRESS.open("a", encoding="utf-8") as progress:
        with ThreadPoolExecutor(max_workers=args.jobs) as executor:
            futures = {executor.submit(extract, module): module for module in modules}
            for future in as_completed(futures):
                module, action = future.result()
                completed += 1
                line = f"[{completed}/{len(modules)}] {action} {module}"
                print(line, flush=True)
                print(line, file=progress, flush=True)
    print(f"complete modules={len(modules)}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
