#!/usr/bin/env python3
"""Recompile the modules changed since a base commit against their current sources.

`scripts/pg-iterate.sh` checks one file against whatever compiled modules the shared cache
holds. That check can pass although the file does not compile against the current source
of its imports, in two ways: an imported module changed after its importer was checked,
or the cache holds an import compiled from another checkout's version of the source. This
tool closes both gaps without a Lake build and without the build lock.

It selects

* every tracked module under the audited trees that changed since BASE,
* every module there whose cached compiled module was built from a different source text,
  according to the source hash Lake recorded in its trace file,
* any dependency of a selected module, in those trees, that has no compiled module, and
* every tracked module there that imports a selected module, directly or not,

and compiles the selection in dependency order. Compiled modules go to a private mirror
of the cache, so later modules see the fresh ones. The shared `.lake` is only read.

`--work DIR` gives every run a new subdirectory of DIR. `--keep DIR` uses DIR itself and
keeps it for the next run, one run at a time. A later run there skips a changed module it
already compiled from the current source text, compiles again every module that failed,
and finishes an interrupted run.

`--axioms` then runs the repository's axiom sweep, `scripts/AxiomSweep.lean`, on the
covered modules through the same mirror. It fails when a declaration there depends on
`sorryAx` or on any axiom other than `propext`, `Classical.choice` and `Quot.sound`.

The tool runs `lean` directly. The build-time plugins and Lake's linter options do not
apply. Modules outside the audited trees are not rebuilt: a cached module there that does
not match its source is reported, and the result is then not trustworthy for its
importers. The project build remains the authoritative check.

    scripts/audit-changed-modules.py BASE [--lake DIR] [--work DIR | --keep DIR] [--jobs N]
        [--axioms]

Exit status 0 means every selected module compiled; 1 means a failure, a module blocked
by a failed import, a timeout, an import that has no source file, a cache that replaced
a module during the run, or a declaration the axiom sweep rejects; 2 means the tool
could not start.
"""
from __future__ import annotations

import argparse
import concurrent.futures as futures
import fcntl
import glob
import importlib.util
import json
import os
from pathlib import Path
import re
import struct
import subprocess
import sys
import tempfile
import time

import lean_lexer

SCRIPTS = Path(__file__).resolve().parent
DEFAULT_TREES = ("ArkLib/Research/", "ArkLib/Tests/ProximityPrize/")
IMPORT = re.compile(r"^[ \t]*(?:(?:public|meta)[ \t]+)*import[ \t]+(?:all[ \t]+)?([^\n]+)", re.M)
MASK = (1 << 64) - 1
MURMUR = 0xC6A4A7935BD1E995
SIDECAR = ".source-hash"
FAILED = ".audit-failed"
STANDARD_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})


def research_exclusions() -> set[str]:
    """Sources the generated research umbrella leaves out."""
    spec = importlib.util.spec_from_file_location(
        "update_research_lib", SCRIPTS / "update-research-lib.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return set(module.EXCLUDED)


def audited(imports: dict[str, list[str]], excluded: set[str]) -> set[str]:
    """The tracked sources the audit covers.

    A source the umbrella leaves out is covered only when a covered source imports it.
    That keeps the umbrella and the workbench, which the library root reaches, and drops
    the files no build compiles.
    """
    keep = {source for source in imports if source not in excluded}
    stack = list(keep)
    while stack:
        for dependency in imports[stack.pop()]:
            if dependency in imports and dependency not in keep:
                keep.add(dependency)
                stack.append(dependency)
    return keep


def module_path(name: str) -> str:
    """Source path of a module name, with guillemets removed."""
    return name.replace("«", "").replace("»", "").replace(".", "/") + ".lean"


def parse_imports(text: str) -> list[str]:
    """Source paths of the `ArkLib` modules a file imports."""
    live, _ = lean_lexer.live_text(text)
    return [module_path(name) for group in IMPORT.findall(live) for name in group.split()
            if name == "ArkLib" or name.startswith("ArkLib.")]


def lake_text_hash(data: bytes) -> str:
    """Lake's hash of a source file, in the form its trace files record.

    Lake normalizes line endings, applies Lean's `String.hash` (MurmurHash64A with
    seed 11) and mixes the result into its empty hash 1723 with `mixHash`.
    """
    data = data.replace(b"\r\n", b"\n")
    size = len(data)
    whole = size - size % 8
    h = (11 ^ (size * MURMUR)) & MASK
    for (k,) in struct.iter_unpack("<Q", data[:whole]):
        k = (k * MURMUR) & MASK
        k ^= k >> 47
        k = (k * MURMUR) & MASK
        h = ((h ^ k) * MURMUR) & MASK
    if size > whole:
        h = ((h ^ int.from_bytes(data[whole:], "little")) * MURMUR) & MASK
    h ^= h >> 47
    h = (h * MURMUR) & MASK
    h ^= h >> 47
    k = (h * MURMUR) & MASK
    k ^= k >> 47
    k ^= MURMUR
    return f"{((1723 ^ k) * MURMUR) & MASK:016x}"


def recorded_source_hash(trace: Path, source: str) -> str | None:
    """The hash a Lake trace file records for the module's own source, if any."""
    try:
        inputs = json.loads(trace.read_text(encoding="utf-8")).get("inputs")
    except (OSError, ValueError, AttributeError):
        return None
    stack = [inputs]
    while stack:
        node = stack.pop()
        if not isinstance(node, list):
            continue
        if (len(node) == 2 and isinstance(node[0], str) and isinstance(node[1], str)
                and (node[0] == source or node[0].endswith("/" + source))):
            return node[1]
        stack.extend(node)
    return None


def compiled_here(mirror: Path, source: str) -> bool:
    """Whether the mirror holds a module this tool compiled, not a link into the cache."""
    private = mirror / (source[:-5] + ".olean")
    return private.is_file() and not private.is_symlink()


def cached_source_hash(library: Path, mirror: Path, source: str) -> str | None:
    """Hash of the source text the usable compiled module was built from.

    A module this tool compiled earlier into the mirror carries a sidecar file; a module
    of the cache is described by its Lake trace file. `None` means there is no compiled
    module or its origin is unknown.
    """
    stem = source[:-5]
    if compiled_here(mirror, source):
        try:
            return (mirror / (stem + SIDECAR)).read_text(encoding="utf-8").strip() or None
        except OSError:
            return None
    if not (library / (stem + ".olean")).exists():
        return None
    return recorded_source_hash(library / (stem + ".trace"), source)


def select(imports: dict[str, list[str]], changed: set[str], compiled: set[str]) -> set[str]:
    """Modules to rebuild: the changed ones, their importers, and uncompiled dependencies.

    `imports` maps each audited source to the audited or external sources it imports.
    `compiled` holds the sources that already have a usable compiled module. An importer
    of a dependency that is rebuilt for want of a compiled module is rebuilt as well.
    """
    importers: dict[str, list[str]] = {}
    for source, dependencies in imports.items():
        for dependency in dependencies:
            importers.setdefault(dependency, []).append(source)
    todo = {source for source in changed if source in imports}
    stack = list(todo)
    while stack:
        current = stack.pop()
        for importer in importers.get(current, []):
            if importer not in todo:
                todo.add(importer)
                stack.append(importer)
        for dependency in imports.get(current, []):
            if dependency in imports and dependency not in todo and dependency not in compiled:
                todo.add(dependency)
                stack.append(dependency)
    return todo


def outdated(imports: dict[str, list[str]], here: dict[str, float]) -> set[str]:
    """Modules that predate a module this work directory compiled and that they import.

    `here` maps each module compiled in the work directory to the time its compiled module
    was written. A finished run leaves none: it compiles every importer after its imports.
    An interrupted run, or a module that was not covered before, does.
    """
    return {source for source, dependencies in imports.items()
            if any(d in here and (source not in here or here[d] > here[source])
                   for d in dependencies)}


def sweep_roots(imports: dict[str, list[str]]) -> list[str]:
    """Module names to hand to the axiom sweep so that it loads and reports every source.

    The sweep imports its roots and reports the loaded modules whose name starts with a
    root. The sources nothing imports make it load everything; the sources with no
    covered source as a name prefix make every name match.
    """
    names = {source: source[:-5].replace("/", ".") for source in imports}
    imported = {dependency for dependencies in imports.values() for dependency in dependencies}
    roots = {names[source] for source in imports if source not in imported}
    kept: list[str] = []
    for name in sorted(names.values()):
        if not any(name == root or name.startswith(root + ".") for root in kept):
            kept.append(name)
    return sorted(roots.union(kept))


def tainted(report: dict) -> list[dict]:
    """Declarations of a sweep report that depend on an axiom outside the standard three."""
    found = []
    for declaration in report.get("declarations", []):
        extra = sorted(set(declaration.get("axioms", [])) - STANDARD_AXIOMS)
        if extra:
            found.append({"name": declaration.get("name"), "module": declaration.get("module"),
                          "axioms": extra})
    return found


def axiom_sweep(root: Path, env: dict[str, str], modules: list[str],
                out: Path) -> tuple[int, list[dict]] | None:
    """Run the repository's axiom sweep on compiled modules; `None` when it cannot run."""
    command = ["lean", "--run", str(SCRIPTS / "AxiomSweep.lean")]
    for module in modules:
        command += ["--root", module]
    command += ["--out", str(out)]
    if out.exists():
        out.unlink()
    try:
        done = subprocess.run(command, cwd=root, env=env, capture_output=True, text=True)
    except OSError as error:
        print(f"axiom sweep: cannot start: {error}", flush=True)
        return None
    try:
        report = json.loads(out.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        report = None
    if done.returncode != 0 or not isinstance(report, dict):
        print("axiom sweep: did not finish\n" + (done.stdout + done.stderr)[-2000:], flush=True)
        return None
    return int(report.get("declarationCount", 0)), tainted(report)


def git(root: Path, *args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=root, text=True)


def mirror_cache(library: Path, mirror: Path, rebuilding: set[str]) -> None:
    """Symlink the cached `ArkLib` tree, the only package this tool overrides.

    Nothing is linked for a module that is about to be rebuilt or that the mirror already
    holds a private compiled module for, so no file of such a module comes from the cache.
    """
    for directory, _, files in os.walk(library / "ArkLib"):
        relative = Path(directory).relative_to(library)
        (mirror / relative).mkdir(parents=True, exist_ok=True)
        for name in files:
            source = (relative / (name.split(".", 1)[0] + ".lean")).as_posix()
            if source in rebuilding or compiled_here(mirror, source):
                continue
            link = mirror / relative / name
            if not link.is_symlink() and not link.exists():
                link.symlink_to(Path(directory) / name)
    for entry in library.iterdir():
        link = mirror / entry.name
        if entry.name.split(".", 1)[0] + ".lean" in rebuilding:
            continue
        if entry.is_file() and not link.is_symlink() and not link.exists():
            link.symlink_to(entry)


def compile_module(root: Path, source: str, mirror: Path, logs: Path, env: dict[str, str],
                   timeout: int) -> tuple[str, int, float, list[str]]:
    target = mirror / source[:-5]
    target.parent.mkdir(parents=True, exist_ok=True)
    for stale in target.parent.glob(glob.escape(target.name) + ".*"):
        if stale.is_symlink() or stale.is_file():
            stale.unlink()   # a kept mirror: never write through a link into the cache
    try:
        text_hash = lake_text_hash((root / source).read_bytes())
    except OSError:
        text_hash = None
    start = time.time()
    try:
        done = subprocess.run(
            ["lean", "-DautoImplicit=false", "-o", str(target) + ".olean", source],
            cwd=root, env=env, capture_output=True, text=True, timeout=timeout)
        code, output = done.returncode, done.stdout + done.stderr
    except subprocess.TimeoutExpired as expired:
        # TimeoutExpired keeps partial output as bytes even with text=True.
        partial = b"".join(value for value in (expired.stdout, expired.stderr) if value)
        code, output = 124, partial.decode(errors="replace") + "\naudit: timed out"
    if text_hash is not None:
        Path(str(target) + (SIDECAR if code == 0 else FAILED)).write_text(
            text_hash + "\n", encoding="utf-8")
    (logs / (source[:-5].replace("/", ".") + ".log")).write_text(output, encoding="utf-8")
    errors = [line for line in output.splitlines() if ": error" in line or "timed out" in line]
    return source, code, time.time() - start, errors[:3]


def outside_mismatches(root: Path, library: Path, covered: set[str]) -> list[str]:
    """Cached `ArkLib` modules outside the audit that were built from another source text."""
    found = []
    for directory, _, files in os.walk(library / "ArkLib"):
        for name in files:
            if not name.endswith(".olean"):
                continue
            source = (Path(directory) / name).relative_to(library).as_posix()[:-6] + ".lean"
            if source in covered or not (root / source).is_file():
                continue
            recorded = recorded_source_hash(library / (source[:-5] + ".trace"), source)
            if recorded != lake_text_hash((root / source).read_bytes()):
                found.append(source)
    return sorted(found)


def run(root: Path, base: str, lake: Path, work: Path, jobs: int, trees: tuple[str, ...],
        timeout: int, keep: bool = False, axioms: bool = False) -> int:
    excluded = research_exclusions()
    imports = {path: parse_imports((root / path).read_text(encoding="utf-8"))
               for path in git(root, "ls-files", "--", *trees).splitlines()
               if path.endswith(".lean") and (root / path).is_file()}
    covered = audited(imports, excluded)
    imports = {path: imports[path] for path in covered}
    tracked = sorted(covered)
    diff = [path for path in git(root, "diff", "--name-only", base, "--",
                                 "*.lean").splitlines() if path]
    changed = {path for path in diff if path in imports}
    outside = [path for path in diff if path not in imports and path not in excluded
               and (root / path).exists()]
    if outside:
        print(f"not audited, outside the selected trees: {len(outside)} changed Lean "
              f"sources, for example {outside[0]}")

    library = lake / "build" / "lib" / "lean"
    work.mkdir(parents=True, exist_ok=True)
    if keep:
        lock = open(work / ".lock", "w", encoding="utf-8")   # held until the process exits
        try:
            fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except OSError:
            print(f"ERROR: another audit is using {work}", file=sys.stderr)
            return 2
    else:
        # Every run owns its output, including when two audits share --work.
        work = Path(tempfile.mkdtemp(prefix="run-", dir=work))
    mirror, logs = work / "mirror", work / "logs"
    mirror.mkdir(parents=True, exist_ok=True)
    logs.mkdir(parents=True, exist_ok=True)

    current = {path: lake_text_hash((root / path).read_bytes()) for path in tracked}
    origin = {path: cached_source_hash(library, mirror, path) for path in tracked}
    present = {path for path in tracked if compiled_here(mirror, path)
               or (library / (path[:-5] + ".olean")).exists()}
    mismatched = {path for path in present if origin[path] != current[path]}
    compiled = present - mismatched
    here = {path: (mirror / (path[:-5] + ".olean")).stat().st_mtime for path in compiled
            if compiled_here(mirror, path)}
    failed_before = {path for path in tracked if (mirror / (path[:-5] + FAILED)).exists()}
    sourceless = {path: [d for d in imports[path] if not (root / d).is_file()]
                  for path in tracked}
    sourceless = {path: missing for path, missing in sourceless.items() if missing}
    todo = select(imports, (changed - set(here)) | mismatched | failed_before
                  | set(sourceless) | outdated(imports, here), compiled)
    if todo:
        mirror_cache(library, mirror, todo)
    print(f"{len(changed)} sources changed since {base} "
          f"({len((changed & set(here)) - todo)} already compiled in this work directory), "
          f"{len(mismatched)} compiled modules built from another source text, "
          f"{len(failed_before)} failed here before, {len(todo)} modules to compile, "
          f"logs in {logs}", flush=True)
    foreign = outside_mismatches(root, library, covered)
    if foreign:
        print(f"WARNING: {len(foreign)} cached modules outside the selected trees were built "
              f"from another source text, for example {foreign[0]}; their importers are "
              "checked against that other version", flush=True)

    search = [str(mirror), str(library)] + [
        str(package / ".lake" / "build" / "lib" / "lean")
        for package in sorted((lake / "packages").iterdir())
        if (package / ".lake" / "build" / "lib" / "lean").is_dir()]
    env = dict(os.environ, LEAN_PATH=":".join(search))

    status: dict[str, str] = {}
    report: dict[str, dict] = {}
    for source, missing in sorted(sourceless.items()):
        status[source] = "failed"
        report[source] = {"exit": 1, "seconds": 0.0,
                          "errors": [f"imports {missing[0]}, which has no source file"]}
        print(f"FAILED {source}: {report[source]['errors']}", flush=True)
    waiting = {source: {d for d in imports[source] if d in todo}
               for source in todo if source not in status}
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

    moved = sorted(path for path in compiled - todo
                   if cached_source_hash(library, mirror, path) != origin[path])
    if moved:
        print(f"WARNING: the cache replaced {len(moved)} compiled modules during the run, "
              f"for example {moved[0]}; run the audit again", flush=True)
    counts: dict[str, int] = {}
    for state in status.values():
        counts[state] = counts.get(state, 0) + 1
    print("result:", ", ".join(f"{count} {state}" for state, count in sorted(counts.items()))
          or "nothing to compile", flush=True)
    clean = set(counts) <= {"ok"} and not moved
    swept: dict | None = None
    if axioms and not clean:
        print("axiom sweep: skipped, the modules above must compile first", flush=True)
    elif axioms:
        outcome = axiom_sweep(root, env, sweep_roots(imports), work / "axioms.json")
        if outcome is None:
            clean = False
            swept = {"ran": False}
        else:
            total, rejected = outcome
            swept = {"ran": True, "declarations": total, "rejected": rejected}
            print(f"axiom sweep: {total} declarations, {len(rejected)} depend on an axiom "
                  "outside propext, Classical.choice, Quot.sound", flush=True)
            for entry in rejected[:10]:
                print(f"  {entry['name']} ({entry['module']}): {entry['axioms']}", flush=True)
            clean = clean and not rejected
    (work / "summary.json").write_text(
        json.dumps({"base": base, "status": status, "report": report,
                    "mismatched": sorted(mismatched), "outside_mismatched": foreign,
                    "replaced_during_run": moved, "axiom_sweep": swept}, indent=1),
        encoding="utf-8")
    return 0 if clean else 1


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("base", help="commit whose build is trusted, for example the last "
                                     "commit with a completed CI run")
    parser.add_argument("--lake", help="a .lake directory with compiled modules "
                                       "(default: .lake in this checkout)")
    where = parser.add_mutually_exclusive_group()
    where.add_argument("--work", help="parent directory; each run gets a new subdirectory "
                                      "for its mirror, logs and summary (default: a new "
                                      "temporary directory)")
    where.add_argument("--keep", help="directory used in place and kept for the next run, "
                                      "which then compiles only what changed or failed")
    parser.add_argument("--jobs", type=int, default=4, help="concurrent compilations")
    parser.add_argument("--timeout", type=int, default=3600, help="seconds per module")
    parser.add_argument("--tree", action="append", help="audited source prefix; repeatable")
    parser.add_argument("--axioms", action="store_true",
                        help="after a clean compile, run the axiom sweep on the covered "
                             "modules and fail on sorryAx or a non-standard axiom")
    args = parser.parse_args()
    root = Path(git(Path.cwd(), "rev-parse", "--show-toplevel").strip())
    lake = Path(args.lake).resolve() if args.lake else (root / ".lake").resolve()
    if not (lake / "build" / "lib" / "lean" / "ArkLib").is_dir():
        print(f"ERROR: no compiled ArkLib modules under {lake}", file=sys.stderr)
        return 2
    if args.keep:
        work = Path(args.keep).resolve()
    else:
        work = Path(args.work).resolve() if args.work else Path(
            tempfile.mkdtemp(prefix="arklib-audit-"))
    trees = tuple(args.tree) if args.tree else DEFAULT_TREES
    return run(root, args.base, lake, work, args.jobs, trees, args.timeout, bool(args.keep),
               args.axioms)


if __name__ == "__main__":
    sys.exit(main())
