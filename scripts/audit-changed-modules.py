#!/usr/bin/env python3
"""Recompile the modules changed since a base commit against their current sources.

`scripts/pg-iterate.sh` checks one file against whatever compiled modules the shared cache
holds. When an imported module changed after the cache was built, that check can pass
although the file no longer compiles against the current source of its imports. This tool
closes that gap without a Lake build and without the build lock.

It recompiles, in dependency order,

* every tracked module under the audited trees that changed since BASE,
* every tracked module there that imports one of them, directly or not, and
* any of their dependencies in those trees that has no compiled module in the cache.

Compiled modules go to a private mirror of the cache, so later modules see the fresh
ones. The shared `.lake` is only read.

The tool runs `lean` directly. The build-time plugins and Lake's linter options do not
apply, and module-system sources outside the audited trees are not rebuilt. The project
build remains the authoritative check.

    scripts/audit-changed-modules.py BASE [--lake DIR] [--work DIR] [--jobs N]

Exit status 0 means every selected module compiled; 1 means a failure, a module blocked
by a failed import, or a timeout.
"""
from __future__ import annotations

import argparse
import concurrent.futures as futures
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time

SCRIPTS = Path(__file__).resolve().parent
DEFAULT_TREES = ("ArkLib/Research/", "ArkLib/Tests/ProximityPrize/")
IMPORT = re.compile(r"^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)", re.M)


def research_exclusions() -> set[str]:
    """Sources the research umbrella deliberately leaves out.

    The umbrella itself stays in the audit: it imports every module, so it compiles last
    and checks that all of them are present.
    """
    spec = importlib.util.spec_from_file_location(
        "update_research_lib", SCRIPTS / "update-research-lib.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return set(module.EXCLUDED) - {module.TARGET}


def module_path(name: str) -> str:
    """Source path of a module name, with guillemets removed."""
    return name.replace("«", "").replace("»", "").replace(".", "/") + ".lean"


def parse_imports(text: str) -> list[str]:
    """Source paths of the `ArkLib` modules a file imports."""
    return [module_path(name) for name in IMPORT.findall(text) if name.startswith("ArkLib")]


def select(imports: dict[str, list[str]], changed: set[str], compiled: set[str]) -> set[str]:
    """Modules to rebuild: the changed ones, their importers, and uncompiled dependencies.

    `imports` maps each audited source to the audited or external sources it imports.
    `compiled` holds the sources that already have a compiled module in the cache.
    """
    importers: dict[str, list[str]] = {}
    for source, dependencies in imports.items():
        for dependency in dependencies:
            importers.setdefault(dependency, []).append(source)
    todo = {source for source in changed if source in imports}
    stack = list(todo)
    while stack:
        for importer in importers.get(stack.pop(), []):
            if importer not in todo:
                todo.add(importer)
                stack.append(importer)
    stack = list(todo)
    while stack:
        for dependency in imports.get(stack.pop(), []):
            if dependency in imports and dependency not in todo and dependency not in compiled:
                todo.add(dependency)
                stack.append(dependency)
    return todo


def git(root: Path, *args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=root, text=True)


def mirror_cache(library: Path, mirror: Path) -> None:
    """Symlink the cached `ArkLib` tree, the only package this tool overrides."""
    for directory, _, files in os.walk(library / "ArkLib"):
        relative = Path(directory).relative_to(library)
        (mirror / relative).mkdir(parents=True, exist_ok=True)
        for name in files:
            link = mirror / relative / name
            if not link.is_symlink() and not link.exists():
                link.symlink_to(Path(directory) / name)
    for entry in library.iterdir():
        link = mirror / entry.name
        if entry.is_file() and not link.is_symlink() and not link.exists():
            link.symlink_to(entry)


def compile_module(root: Path, source: str, mirror: Path, logs: Path, env: dict[str, str],
                   timeout: int) -> tuple[str, int, float, list[str]]:
    target = mirror / source[:-5]
    target.parent.mkdir(parents=True, exist_ok=True)
    for suffix in (".olean", ".ilean", ".trace", ".olean.hash", ".ilean.hash"):
        stale = Path(str(target) + suffix)
        if stale.is_symlink() or stale.exists():
            stale.unlink()   # never write through a link into the shared cache
    start = time.time()
    try:
        done = subprocess.run(
            ["lean", "-DautoImplicit=false", "-o", str(target) + ".olean", source],
            cwd=root, env=env, capture_output=True, text=True, timeout=timeout)
        code, output = done.returncode, done.stdout + done.stderr
    except subprocess.TimeoutExpired as expired:
        code, output = 124, (expired.stdout or "") + "\naudit: timed out"
    (logs / (source[:-5].replace("/", ".") + ".log")).write_text(output, encoding="utf-8")
    errors = [line for line in output.splitlines() if ": error" in line or "timed out" in line]
    return source, code, time.time() - start, errors[:3]


def run(root: Path, base: str, lake: Path, work: Path, jobs: int, trees: tuple[str, ...],
        timeout: int) -> int:
    excluded = research_exclusions()
    tracked = [path for path in git(root, "ls-files", "--", *trees).splitlines()
               if path.endswith(".lean") and path not in excluded]
    imports = {path: parse_imports((root / path).read_text(encoding="utf-8"))
               for path in tracked}
    diff = [path for path in git(root, "diff", "--name-only", base, "HEAD", "--",
                                 "*.lean").splitlines() if path]
    changed = {path for path in diff if path in imports}
    outside = [path for path in diff if path not in imports and path not in excluded
               and (root / path).exists()]
    if outside:
        print(f"not audited, outside the selected trees: {len(outside)} changed Lean "
              f"sources, for example {outside[0]}")

    library = lake / "build" / "lib" / "lean"
    mirror, logs = work / "mirror", work / "logs"
    mirror.mkdir(parents=True, exist_ok=True)
    logs.mkdir(parents=True, exist_ok=True)
    mirror_cache(library, mirror)
    compiled = {path for path in tracked if (mirror / (path[:-5] + ".olean")).exists()}
    todo = select(imports, changed, compiled)
    print(f"{len(changed)} changed sources, {len(todo)} modules to compile, "
          f"logs in {logs}", flush=True)

    search = [str(mirror), str(library)] + [
        str(package / ".lake" / "build" / "lib" / "lean")
        for package in sorted((lake / "packages").iterdir())
        if (package / ".lake" / "build" / "lib" / "lean").is_dir()]
    env = dict(os.environ, LEAN_PATH=":".join(search))

    status: dict[str, str] = {}
    report: dict[str, dict] = {}
    waiting = {source: {d for d in imports[source] if d in todo} for source in todo}
    running: dict[futures.Future, str] = {}
    with futures.ThreadPoolExecutor(max_workers=jobs) as pool:
        while waiting or running:
            for source in [s for s, deps in waiting.items()
                           if any(status.get(d) in ("failed", "blocked") for d in deps)]:
                status[source] = "blocked"
                del waiting[source]
            for source in [s for s, deps in waiting.items()
                           if all(status.get(d) == "ok" for d in deps)]:
                running[pool.submit(compile_module, root, source, mirror, logs, env,
                                    timeout)] = source
                del waiting[source]
            if not running:
                if waiting and not any(
                        status.get(d) in ("failed", "blocked")
                        for deps in waiting.values() for d in deps):
                    for source in waiting:
                        status[source] = "blocked"   # an import cycle
                    waiting.clear()
                continue
            finished, _ = futures.wait(running, return_when=futures.FIRST_COMPLETED)
            for future in finished:
                source = running.pop(future)
                _, code, seconds, errors = future.result()
                status[source] = "ok" if code == 0 else "failed"
                report[source] = {"exit": code, "seconds": round(seconds, 1), "errors": errors}
                if code != 0:
                    print(f"FAILED {source}: {errors[:1]}", flush=True)
                built = sum(1 for state in status.values() if state in ("ok", "failed"))
                if built % 50 == 0:
                    print(f"{built}/{len(todo)} compiled", flush=True)
    (work / "summary.json").write_text(
        json.dumps({"base": base, "status": status, "report": report}, indent=1),
        encoding="utf-8")
    counts: dict[str, int] = {}
    for state in status.values():
        counts[state] = counts.get(state, 0) + 1
    print("result:", ", ".join(f"{count} {state}" for state, count in sorted(counts.items()))
          or "nothing to compile")
    return 0 if set(counts) <= {"ok"} else 1


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("base", help="commit whose build is trusted, for example the last "
                                     "commit with a completed CI run")
    parser.add_argument("--lake", help="a .lake directory with compiled modules "
                                       "(default: .lake in this checkout)")
    parser.add_argument("--work", help="directory for the mirror and logs (default: a new "
                                       "temporary directory)")
    parser.add_argument("--jobs", type=int, default=4, help="concurrent compilations")
    parser.add_argument("--timeout", type=int, default=3600, help="seconds per module")
    parser.add_argument("--tree", action="append", help="audited source prefix; repeatable")
    args = parser.parse_args()
    root = Path(git(Path.cwd(), "rev-parse", "--show-toplevel").strip())
    lake = Path(args.lake).resolve() if args.lake else (root / ".lake").resolve()
    if not (lake / "build" / "lib" / "lean" / "ArkLib").is_dir():
        print(f"ERROR: no compiled ArkLib modules under {lake}", file=sys.stderr)
        return 2
    work = Path(args.work).resolve() if args.work else Path(tempfile.mkdtemp(prefix="arklib-audit-"))
    trees = tuple(args.tree) if args.tree else DEFAULT_TREES
    return run(root, args.base, lake, work, args.jobs, trees, args.timeout)


if __name__ == "__main__":
    sys.exit(main())
