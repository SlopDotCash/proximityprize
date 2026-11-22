#!/usr/bin/env python3
"""Check the affine and quadratic list endpoints against Lewko's pinned external proof."""

import argparse
import os
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[3]
SOURCE = "https://github.com/mrklwk/szemeredi-trotter-lean"
REVISION = "844228bc6c042e59373888d1b69f4e215d1c00e4"
FRONTIER = "ArkLib.Research.ProximityGap.Frontier"


def run(*args, **kwargs):
    return subprocess.run(args, check=True, cwd=ROOT, text=True, **kwargs)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", default=SOURCE, help="upstream URL or local Git clone")
    args = parser.parse_args()
    run("./scripts/lake-locked.sh", "build", f"{FRONTIER}.QuadraticListIncidences",
        f"{FRONTIER}._PrizeShapePrimeP30", f"{FRONTIER}._PrizeShapePrimeP30Second")
    library_path = run("lake", "env", "printenv", "LEAN_PATH", capture_output=True).stdout.strip()
    lean = run("lake", "env", "which", "lean", capture_output=True).stdout.strip()
    with tempfile.TemporaryDirectory(prefix="lewko-affine-lists-") as tmp:
        source = Path(tmp) / "source"
        output = Path(tmp) / "lib"
        output.mkdir()
        run("git", "init", "--quiet", source)
        run("git", "-C", source, "fetch", "--quiet", "--depth=1", args.source, REVISION)
        run("git", "-C", source, "checkout", "--quiet", "--detach", REVISION)
        env = {**os.environ, "LEAN_PATH": os.pathsep.join([str(output), library_path])}
        compiled = set()

        def compile_module(name):
            if name in compiled:
                return
            relative = Path(*name.split("."))
            src = source / relative.with_suffix(".lean")
            for dep in re.findall(r"^(?:public )?import (MathCollab\.[\w.]+)", src.read_text(), re.M):
                compile_module(dep)
            artifact = output / relative.with_suffix(".olean")
            artifact.parent.mkdir(exist_ok=True)
            run(lean, "-R", source, "-o", artifact, src, env=env, stdout=subprocess.DEVNULL)
            compiled.add(name)

        compile_module("MathCollab.IncidenceSharper")
        adapter = Path(__file__).with_name("AffineNamedEndpoints.lean").resolve()
        checked = run(lean, "-R", adapter.parent, adapter, env=env, capture_output=True)
        report = checked.stdout + checked.stderr
        expected = {"propext", "Classical.choice", "Quot.sound"}
        for decl in ("First.affine_list_budget", "Second.affine_list_budget",
                     "quadratic_eight", "quadratic_sixty_four", "near_capacity"):
            name = f"ProximityGap.AffineNamedEndpoints.{decl}"
            match = re.search(rf"'{re.escape(name)}' depends on axioms:\s*\[([^\]]+)\]", report)
            if not match or {item.strip() for item in match[1].split(",")} != expected:
                raise RuntimeError(f"Unexpected axiom report for {name}: {report}")
        print(report, end="")
        print(f"Linked {len(compiled)} external modules at {REVISION}.")


if __name__ == "__main__":
    main()
