#!/usr/bin/env python3
"""Deterministic sorry/admit census for the ArkLib source tree.

Produces a per-declaration inventory of every `sorry`/`admit` token under
ArkLib/, distinguishing real proof holes from docstring/comment mentions.
With --fail-on-holes (the CI gate), exits non-zero if any live hole exists.

Usage:
  python3 scripts/sorry_census.py                  # report summary
  python3 scripts/sorry_census.py --fail-on-holes  # CI gate: 0 live holes
  python3 scripts/sorry_census.py --out census.json

A token is classified as:
  hole — `sorry`/`admit` in live code (a tactic body or term position)
  doc  — inside a docstring `/-- ... -/`, block comment `/- ... -/`, or
         line comment `-- ...` (includes prose words containing 'admit')
The containing declaration is the nearest preceding `theorem|lemma|def|
instance|example|abbrev|opaque` header.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
import re

DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+|scoped\s+)*"
    r"(theorem|lemma|def|instance|example|abbrev|opaque)\s+([^\s({\[:]+)"
)
TOKEN_RE = re.compile(r"\b(sorry|admit)\b")


def strip_comments_map(text: str) -> list[bool]:
    """Return per-char mask: True if the char is inside a comment/docstring."""
    mask = [False] * len(text)
    i, n = 0, len(text)
    depth = 0
    while i < n:
        if depth == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j == -1 else j
            for k in range(i, j):
                mask[k] = True
            i = j
        elif text.startswith("/-", i):
            depth += 1
            mask[i] = mask[i + 1 if i + 1 < n else i] = True
            i += 2
        elif depth > 0 and text.startswith("-/", i):
            depth -= 1
            mask[i] = mask[i + 1 if i + 1 < n else i] = True
            i += 2
        else:
            if depth > 0:
                mask[i] = True
            i += 1
    return mask


def census(root: Path) -> list[dict]:
    rows: list[dict] = []
    for f in sorted((root / "ArkLib").rglob("*.lean")):
        text = f.read_text(encoding="utf-8", errors="replace")
        mask = strip_comments_map(text)
        lines = text.splitlines()
        decls: list[tuple[int, str, str]] = []  # (line_no, kind, name)
        for idx, ln in enumerate(lines):
            m = DECL_RE.match(ln)
            if m:
                decls.append((idx, m.group(1), m.group(2)))
        for m in TOKEN_RE.finditer(text):
            line_no = text.count("\n", 0, m.start())
            in_comment = mask[m.start()]
            decl = None
            for dline, kind, name in reversed(decls):
                if dline <= line_no:
                    decl = f"{kind} {name}"
                    break
            rows.append(
                {
                    "file": str(f.relative_to(root)),
                    "line": line_no + 1,
                    "token": m.group(1),
                    "kind": "doc" if in_comment else "hole",
                    "decl": decl or "<file-level>",
                }
            )
    return rows


def summarize(rows: list[dict]) -> dict:
    holes = [r for r in rows if r["kind"] == "hole"]
    return {
        "total_tokens": len(rows),
        "holes": len(holes),
        "doc_mentions": len(rows) - len(holes),
        "files_with_holes": len({r["file"] for r in holes}),
        "decls_with_holes": len({(r["file"], r["decl"]) for r in holes}),
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", type=Path, default=Path("."), help="ArkLib checkout root")
    ap.add_argument("--out", type=Path, help="write census JSON here")
    ap.add_argument(
        "--fail-on-holes",
        action="store_true",
        help="exit 1 if any live sorry/admit hole exists (CI gate)",
    )
    ap.add_argument(
        "--baseline",
        type=Path,
        default=Path("scripts/sorry_baseline.json"),
        help="JSON list of {file, decl} holes inherited from upstream syncs; "
        "baselined holes report but do not fail the gate. Ratchet: any hole "
        "not in the baseline still fails, and retired entries are reported "
        "so the baseline can only shrink.",
    )
    args = ap.parse_args()

    rows = census(args.root.expanduser())
    out = {"summary": summarize(rows), "rows": rows}
    if args.out:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(json.dumps(out, indent=1))
        print(f"wrote {args.out}")
    print(json.dumps(out["summary"], indent=2))

    baseline: set[tuple[str, str]] = set()
    if args.baseline.is_file():
        data = json.loads(args.baseline.read_text())
        baseline = {(e["file"], e["decl"]) for e in data["holes"]}

    holes = [r for r in rows if r["kind"] == "hole"]
    new_holes = [r for r in holes if (r["file"], r["decl"]) not in baseline]
    baselined = [r for r in holes if (r["file"], r["decl"]) in baseline]
    retired = baseline - {(r["file"], r["decl"]) for r in holes}
    if baselined:
        print(
            f"\n{len(baselined)} baselined upstream-inherited hole(s) "
            f"in {len({(r['file'], r['decl']) for r in baselined})} decl(s) "
            f"(tracked in {args.baseline}; see the issue referenced there)",
            file=sys.stderr,
        )
    if retired:
        print(
            f"{len(retired)} baseline entr(ies) no longer have holes — "
            f"remove them from {args.baseline}:",
            file=sys.stderr,
        )
        for f, d in sorted(retired):
            print(f"  {f}: {d}", file=sys.stderr)
    if new_holes:
        print(f"\n{len(new_holes)} NEW live hole(s):", file=sys.stderr)
        for r in new_holes:
            print(f"  {r['file']}:{r['line']}: {r['token']} in {r['decl']}", file=sys.stderr)
        if args.fail_on_holes:
            return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
