#!/usr/bin/env python3
"""Deterministic sorry/admit census for the library and research source trees.

Produces a per-declaration inventory of every `sorry`/`admit` token under
ArkLib/, Research/, and ProximityPrize/, distinguishing real proof holes from docstring/comment mentions.
With --fail-on-holes (the CI gate), exits non-zero if any live hole exists.

Usage:
  python3 scripts/sorry_census.py                  # report summary
  python3 scripts/sorry_census.py --fail-on-holes  # CI gate: 0 live holes
  python3 scripts/sorry_census.py --out census.json

A token is classified as:
  hole — `sorry`/`admit`/`sorryAx` in live code (a tactic body or term position),
         including code spliced into an interpolated string (`s!"{sorry}"`)
         or inside a `{...}` splice of ANY non-raw `"..."` string (see below),
         or a live use of the core API that builds `sorryAx` (`mkSorry`, ...).
         `sorryAx` is the kernel axiom both `sorry` and `admit` elaborate to
         (Lean `Init/Prelude.lean`); writing it directly is a hole and must not
         slip past the `sorry` word-boundary match.
         The core `stop` tactic (`macro "stop" tacticSeq => repeat sorry`)
         in tactic position is also a hole: it yields `sorryAx` with no token.
  doc  — inside a docstring `/-- ... -/`, block comment `/- ... -/`,
         line comment `-- ...`, raw-string literal, char literal, or the
         literal (non-splice) text of a string (includes prose words
         containing 'admit')

Lexing is shared with scripts/forbidden_tokens.py and
scripts/check-research-boundary.py (scripts/lean_lexer.py): comments (a doc
comment's body starts after `/--`), string/raw-string/char literals,
interpolation holes, quoted identifiers, identifiers and numbers are lexed
together with Lean's identifier characters.

Why every splice counts: many Lean 4.30 built-ins parse a bare string with
`interpolatedStr(term)` and no `!` prefix (`dbg_trace "{x}"`, `throwError`,
`throwErrorAt`, `throwNamedError[At]`, `logNamedError[At]`,
`logNamedWarning[At]`, `trace[cls]`, `trace_goal[cls]`, `Macro.trace[cls]`),
and any project `syntax ... interpolatedStr(term)` can add more. Tracking
consumers is fragile, so a token counts as a hole when it is code in ANY
reading: a literal whose plain and interpolated readings end at the same
offset counts its `{...}` contents as code, and for a literal whose readings
end at different offsets every combination of readings is lexed (the rest of
the file depends on the choice). A plain string like `"{sorry}"` is therefore
a (rare, harmless) false positive. If a file has more combinations than the
lexer's budget, every token in it counts as a hole (fail closed).
The containing declaration is the nearest preceding `theorem|lemma|def|
instance|example|abbrev|opaque` header.

This is a lexical census, not an elaborated audit: the post-build axiom audit
(scripts/axiom_audit.py) is what reports `sorryAx` in a pinned declaration.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
import re

import lean_lexer

DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+|scoped\s+)*"
    r"(theorem|lemma|def|instance|example|abbrev|opaque)\s+([^\s({\[:]+)"
)
TOKEN_RE = re.compile(r"\b(sorry|admit|sorryAx)\b")
# Lean core `stop` is `macro "stop" tacticSeq : tactic => `(tactic| repeat sorry)`:
# it closes every remaining goal with `sorryAx` without a `sorry` token. `stop` is
# also an ordinary identifier, so only match it where a tactic can start and it
# is not followed by an operator, binder colon or closing delimiter.
STOP_RE = re.compile(
    r"(?:^[ \t]*(?:[·.][ \t]*)?|\bby[ \t]+|;[ \t]*|<;>[ \t]*|=>[ \t]*|\([ \t]*)"
    r"(stop)\b(?![ \t]*(?:[≤<≥>=:),\]⟧+*/|-]))",
    re.M,
)
# A metaprogram can close a goal with `sorryAx` through the core API without a
# `sorry` token, e.g. `elab "t" : tactic => do (← getMainGoal).assign (← mkSorry ..)`.
# (`sorryAx` itself is already in TOKEN_RE.)
SORRY_API_RE = re.compile(
    r"\b(mkSorry|mkLabeledSorry|mkSyntheticSorry\w*|admitGoal|elabSorry|evalSorry)\b"
)


_INVERT = bytes.maketrans(b"\x00\x01", b"\x01\x00")


def strip_comments_map(text: str) -> bytes:
    """Per-character mask: 1 if the character is code in NO reading of the file.

    Lean v4.30.0-rc2 has many `interpolatedStr(term)` consumers without a `!`
    prefix (`dbg_trace`, `throwError[At]`, `throwNamedError[At]`,
    `logNamedError[At]`, `logNamedWarning[At]`, `trace[..]`, `trace_goal[..]`,
    `Macro.trace[..]`), and projects can declare more, so a bare `"..."` may or
    may not be interpolated. Rather than guess, `lean_lexer.explore` lexes
    every combination of readings of the file's ambiguous literals, and the
    `{...}` contents of the other literals count as code. A character is masked
    only if it is a comment or literal text in every reading, so a `sorry` live
    under any reading is a hole (checking only the all-plain and the
    all-interpolated readings missed a `sorry` that is live only in a mixed
    one). The cost is a rare false positive such as a plain `"{sorry}"`
    string. Past the exploration budget nothing is masked (fail closed).
    """
    readings, exhausted = lean_lexer.explore(text)
    if exhausted:
        return bytes(len(text))
    return lean_lexer.live_mask(readings).translate(_INVERT)


def census(root: Path) -> list[dict]:
    rows: list[dict] = []
    for f in sorted(f for name in ("ArkLib", "Research", "ProximityPrize") for f in (root / name).rglob("*.lean")):
        text = f.read_text(encoding="utf-8", errors="replace")
        mask = strip_comments_map(text)
        lines = text.splitlines()
        decls: list[tuple[int, str, str]] = []  # (line_no, kind, name)
        for idx, ln in enumerate(lines):
            m = DECL_RE.match(ln)
            if m:
                decls.append((idx, m.group(1), m.group(2)))
        matches = [(m.start(1), m.group(1)) for m in TOKEN_RE.finditer(text)]
        matches += [(m.start(1), m.group(1)) for m in STOP_RE.finditer(text)
                    if not mask[m.start(1)]]
        matches += [(m.start(1), m.group(1)) for m in SORRY_API_RE.finditer(text)
                    if not mask[m.start(1)]]
        for start, token in sorted(matches):
            line_no = text.count("\n", 0, start)
            in_comment = mask[start]
            decl = None
            for dline, kind, name in reversed(decls):
                if dline <= line_no:
                    decl = f"{kind} {name}"
                    break
            rows.append(
                {
                    "file": str(f.relative_to(root)),
                    "line": line_no + 1,
                    "offset": start,
                    "token": token,
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
    entries: list[dict] = []
    provenance = None
    if args.baseline.is_file():
        data = json.loads(args.baseline.read_text())
        # Inherited debt applies only to the exact upstream blob. Adding a hole
        # to an already listed declaration changes its file digest and fails.
        from forbidden_tokens import InheritedSourcePolicy
        provenance = InheritedSourcePolicy(args.root.expanduser())
        entries = data["holes"]
        baseline = {(e["file"], e["decl"]) for e in entries}

    holes = [r for r in rows if r["kind"] == "hole"]
    def inherited(row: dict) -> bool:
        if provenance is None:
            return False
        path = args.root.expanduser() / row["file"]
        return any((entry["file"], entry["decl"]) == (row["file"], row["decl"])
                   and (provenance.matches_upstream_file(
                       path, entry.get("sha256"), data.get("revision"), data.get("repository"))
                        or provenance.matches_adapted_upstream_hole(
                            path, row, entry, data.get("revision"), data.get("repository")))
                   for entry in entries)
    baselined = [row for row in holes if inherited(row)]
    new_holes = [row for row in holes if row not in baselined]
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
