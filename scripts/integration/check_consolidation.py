#!/usr/bin/env python3
"""Check canonical-source preservation and the integrated local import graph.

These checks establish source ownership and graph consistency, not Lean proof
correctness. The pinned upstream commit must also be a merge ancestor before
publishing a completed integration.
"""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

from extract_downstream_extensions import lexical_mask


ROOT = Path(__file__).resolve().parents[2]
SOURCE_ROOTS = ("ArkLib", "ArkLibTest", "Research", "ProximityPrize")
IMPORT = re.compile(
    r"(?m)^[ \t]*(?:(?:public|meta)\s+)*import\s+(?:all\s+)?([^\n]+)"
)


def module_name(path: str) -> str:
    return path.removesuffix(".lean").replace("/", ".")


def imports(text: str) -> list[str]:
    masked, _ = lexical_mask(text)
    return [name for match in IMPORT.finditer(masked) for name in match[1].split()]


def pinned_blobs(revision: str) -> dict[str, str]:
    tree = subprocess.check_output(
        ["git", "ls-tree", "-rz", "--full-tree", revision, "ArkLib"], cwd=ROOT
    )
    result = {}
    for entry in tree.split(b"\0"):
        if not entry:
            continue
        metadata, path = entry.split(b"\t", 1)
        result[path.decode()] = metadata.split()[2].decode()
    return result


def check(require_ancestor: bool = False) -> tuple[list[str], dict[str, int]]:
    manifest = json.loads((ROOT / "scripts/arklib-upstream.json").read_text())
    revision = manifest["revision"]
    canonical = set(manifest["files"])
    blobs = pinned_blobs(revision)
    expected = {p for p in blobs if p.endswith(".lean")}
    errors = []
    adaptations = {}
    for entry in manifest.get("downstream_adaptations", []):
        path = entry["path"]
        if path in adaptations or path not in canonical:
            errors.append(f"Invalid or duplicate downstream adaptation path: {path}")
        if entry.get("upstream_blob") != blobs.get(path):
            errors.append(f"Downstream adaptation has a different upstream base: {path}")
        if not entry.get("declarations") or not entry.get("source_revision") or not entry.get("reason"):
            errors.append(f"Downstream adaptation lacks declaration/source provenance: {path}")
        adaptations[path] = entry
    if canonical != expected:
        errors.append("Canonical inventory differs from the pinned upstream Lean tree: "
                      f"missing={sorted(expected - canonical)}, extra={sorted(canonical - expected)}")
    for path in sorted(canonical):
        file = ROOT / path
        if not file.is_file():
            errors.append(f"Missing canonical upstream source: {path}")
            continue
        content = file.read_bytes()
        live = hashlib.sha1(b"blob " + str(len(content)).encode() + b"\0" + content).hexdigest()
        reviewed = adaptations.get(path)
        if reviewed and hashlib.sha256(content).hexdigest() != reviewed.get("sha256"):
            errors.append(f"Downstream adaptation differs from its reviewed source hash: {path}")
        elif not reviewed and live != blobs.get(path):
            errors.append(f"Canonical source differs from upstream {revision[:12]}: {path}")

    sources = {}
    for prefix in SOURCE_ROOTS:
        directory = ROOT / prefix
        if directory.is_dir():
            for path in directory.rglob("*.lean"):
                relative = path.relative_to(ROOT).as_posix()
                sources[module_name(relative)] = relative
    for name in SOURCE_ROOTS:
        if (ROOT / f"{name}.lean").is_file():
            sources[name] = f"{name}.lean"
    graph = {}
    canonical_modules = {module_name(p) for p in canonical} | {"ArkLib"}
    for name, relative in sorted(sources.items()):
        direct = imports((ROOT / relative).read_text())
        local = [target for target in direct if target.split(".")[0] in SOURCE_ROOTS]
        graph[name] = sorted(set(local))
        for target in local:
            if target not in sources:
                errors.append(f"Missing local import: {relative} -> {target}")
            if name in canonical_modules and target not in canonical_modules:
                errors.append(f"Canonical module imports downstream/test source: {relative} -> {target}")

    umbrella = imports((ROOT / "ArkLib.lean").read_text())
    counts = Counter(umbrella)
    if set(umbrella) != canonical_modules - {"ArkLib"} or any(n != 1 for n in counts.values()):
        errors.append("ArkLib.lean must re-export every canonical module exactly once")

    # Iterative DFS avoids Python recursion limits on the research proof graph.
    state: dict[str, int] = {}
    for start in sorted(graph):
        if state.get(start):
            continue
        state[start] = 1
        stack = [(start, iter(graph[start]))]
        active = [start]
        while stack:
            node, edges = stack[-1]
            target = next(edges, None)
            if target is None:
                state[node] = 2
                stack.pop()
                active.pop()
            elif target not in graph:
                continue
            elif state.get(target) == 1:
                beginning = active.index(target)
                errors.append("Import cycle: " + " -> ".join(active[beginning:] + [target]))
            elif not state.get(target):
                state[target] = 1
                stack.append((target, iter(graph[target])))
                active.append(target)

    if require_ancestor:
        result = subprocess.run(
            ["git", "merge-base", "--is-ancestor", revision, "HEAD"], cwd=ROOT
        )
        if result.returncode:
            errors.append("Pinned upstream commit is not an ancestor of HEAD")
    return errors, {"canonical_modules": len(canonical), "downstream_adaptations": len(adaptations),
                    "local_modules": len(sources),
                    "local_import_edges": sum(len(v) for v in graph.values())}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--require-ancestor", action="store_true")
    args = parser.parse_args()
    errors, counts = check(args.require_ancestor)
    print(json.dumps(counts, sort_keys=True))
    if errors:
        for message in errors:
            print(message, file=sys.stderr)
        print(f"Consolidation check failed: {len(errors)} issue(s).", file=sys.stderr)
        return 1
    print("Canonical sources and local import graph are consistent.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
