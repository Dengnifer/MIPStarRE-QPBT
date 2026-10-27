#!/usr/bin/env python3
"""Compute the Phase 2 reachability roots and the QPBT-to-LIDT boundary."""

from __future__ import annotations

import json
from collections import defaultdict, deque
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
EXTRACTED = ROOT / "prove2me" / "extracted"
STATUS = Path.home() / "p2m" / "status"

TARGETS = (
    "MIPStarRE.QPBT.Palomar.exists_spcc_value_one",
    "MIPStarRE.QPBT.Palomar.exists_ld_soundness",
    "MIPStarRE.QPBT.Palomar.pauli_soundness",
    "MIPStarRE.QPBT.Palomar.pauli_soundness_qubit",
)


def load_jsonl(path: Path) -> list[dict]:
    with path.open(encoding="utf-8") as handle:
        return [json.loads(line) for line in handle if line.strip()]


def main() -> None:
    graph_rows = load_jsonl(EXTRACTED / "decl_graph.jsonl")
    boundary_rows = load_jsonl(EXTRACTED / "lidt_boundary.jsonl")
    graph = {row["name"]: row for row in graph_rows}
    boundary = {row["name"]: row for row in boundary_rows}
    if graph.keys() != boundary.keys():
        raise SystemExit("Stage 1 and boundary extraction declaration sets differ")

    missing_targets = [name for name in TARGETS if name not in graph]
    if missing_targets:
        raise SystemExit(f"missing targets: {missing_targets}")

    constructors: dict[str, set[str]] = defaultdict(set)
    for row in graph_rows:
        if row["kind"] != "ctor":
            continue
        for dep in row["typeDeps"]:
            dep_row = graph.get(dep)
            if dep_row is not None and dep_row["kind"] == "inductive":
                constructors[dep].add(row["name"])

    instance_roots = {row["name"] for row in graph_rows if row["isInstance"]}
    roots = set(TARGETS) | instance_roots
    reachable: set[str] = set()
    queue = deque(sorted(roots))
    missing_project_deps: set[str] = set()
    while queue:
        name = queue.popleft()
        if name in reachable:
            continue
        row = graph.get(name)
        if row is None:
            missing_project_deps.add(name)
            continue
        reachable.add(name)
        deps = set(row["typeDeps"]) | set(row["valueDeps"])
        if row["kind"] == "inductive":
            deps |= constructors.get(name, set())
        for dep in sorted(deps):
            if dep not in reachable:
                queue.append(dep)
    if missing_project_deps:
        raise SystemExit(
            "Stage 1 graph is missing project dependencies: "
            + ", ".join(sorted(missing_project_deps))
        )

    lidt_dependencies: set[str] = set()
    lidt_type_dependencies: set[str] = set()
    lidt_value_dependencies: set[str] = set()
    for name in reachable:
        row = boundary[name]
        lidt_type_dependencies.update(row["lidtTypeDeps"])
        lidt_value_dependencies.update(row["lidtValueDeps"])
    lidt_dependencies |= lidt_type_dependencies
    lidt_dependencies |= lidt_value_dependencies
    with (EXTRACTED / "lidt_instances.txt").open(encoding="utf-8") as handle:
        lidt_instances = {line.strip() for line in handle if line.strip()}
    lidt_dependencies |= lidt_instances

    source_reachable = {
        name for name in reachable if graph[name]["startLine"] != 0
    }
    spanless_reachable = reachable - source_reachable

    (EXTRACTED / "reachable-declarations.txt").write_text(
        "\n".join(sorted(reachable)) + "\n", encoding="utf-8"
    )
    (EXTRACTED / "reachable-source-declarations.txt").write_text(
        "\n".join(sorted(source_reachable)) + "\n", encoding="utf-8"
    )
    (STATUS / "qpbt-needs-from-lidt.txt").write_text(
        "\n".join(sorted(lidt_dependencies)) + "\nEND\n", encoding="utf-8"
    )
    summary = {
        "targets": list(TARGETS),
        "graphDeclarations": len(graph),
        "instanceRoots": len(instance_roots),
        "reachableDeclarations": len(reachable),
        "reachableSourceDeclarations": len(source_reachable),
        "reachableSpanlessDeclarations": len(spanless_reachable),
        "lidtTypeDependencies": len(lidt_type_dependencies),
        "lidtValueDependencies": len(lidt_value_dependencies),
        "lidtInstances": len(lidt_instances),
        "lidtBoundaryUnion": len(lidt_dependencies),
    }
    (EXTRACTED / "reachability-summary.json").write_text(
        json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(json.dumps(summary, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
