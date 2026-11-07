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
         `exact?` / `apply?` with the library-search `all` option left on
         (`+all`, `(all := true)`, `(config := { all := true })`, and the
         same after a later override) are holes too: on Lean v4.30.0-rc2
         `Lean.Elab.LibrarySearch.exact?` calls `admitGoal` on that path
         even when a complete proof was found, and the declaration still
         elaborates. A computed or inherited value for `all` is treated
         conservatively unless a later item turns it off. Use `-all` or
         `(all := .false)` to explicitly select the non-collecting mode.
         `apply?` in tactic position can also admit an incomplete suggestion
         with `all` disabled. Use an explicit proof or a closing `exact?` in
         place of `apply?`. The source scan recognizes ordinary tactic entry
         forms and is not a parser for user-defined tactic syntax.
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
# `exact?` / `apply?` are tactics, not identifiers, but `?` is an identifier
# character, so the match is bounded the same way Lean lexes a name.
_LIBSEARCH_RE = re.compile(r"exact\?|apply\?")
# Same identifier classes as scripts/forbidden_tokens.py (Lean v4.30 isIdRest).
_LETTER_LIKE = (
    "\u03b1-\u03ba\u03bc-\u03c9"
    "\u0391-\u039f\u03a1\u03a2\u03a4-\u03a9"
    "\u03ca-\u03fb"
    "\u1f00-\u1ffe"
    "\u2100-\u214f"
    "\U0001d49c-\U0001d59f"
    "\u00c0-\u00d6\u00d8-\u00f6\u00f8-\u00ff"
    "\u0100-\u017f"
)
_SUBSCRIPT_ALNUM = "\u2080-\u2089\u2090-\u209c\u1d62-\u1d6a\u2c7c"
_ID_FIRST_RE = re.compile("[" + "A-Za-z_" + _LETTER_LIKE + "]")
_ID_REST_RE = re.compile("[" + "A-Za-z0-9_'!?" + _LETTER_LIKE + _SUBSCRIPT_ALNUM + "]")
_OPEN_BRACKETS = {"(": ")", "{": "}", "[": "]", "⟨": "⟩"}
_CLOSE_BRACKETS = {close: open_ for open_, close in _OPEN_BRACKETS.items()}


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


def _skip_ws(text: str, mask: list[bool], i: int, end: int) -> int:
    # The mask includes strings, which are terms and cannot be skipped as trivia.
    while i < end:
        if text[i].isspace():
            i += 1
        elif mask[i] and text.startswith("--", i):
            newline = text.find("\n", i + 2, end)
            i = end if newline < 0 else newline
        elif mask[i] and text.startswith("/-", i):
            depth = 1
            i += 2
            while i < end and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
        else:
            break
    return i


def _read_ident(text: str, i: int, end: int) -> tuple[str | None, int]:
    if i >= end:
        return None, i
    if text[i] == "«":
        close = text.find("»", i + 1, end)
        return (text[i + 1:close], close + 1) if close >= 0 else (None, i)
    if not _ID_FIRST_RE.fullmatch(text[i]):
        return None, i
    j = i + 1
    while j < end and _ID_REST_RE.fullmatch(text[j]):
        j += 1
    return text[i:j], j


def _quoted_spans(text: str, mask: list[bool]) -> list[tuple[int, int]]:
    """Live `«...»` names. Their interior is not a tactic, and `)` inside one is not syntax."""
    spans: list[tuple[int, int]] = []
    i, n = 0, len(text)
    while i < n:
        if text[i] == "«" and not mask[i]:
            j = text.find("»", i + 1)
            if j < 0:
                break
            spans.append((i, j + 1))
            i = j + 1
        else:
            i += 1
    return spans


def _in_span(i: int, spans: list[tuple[int, int]]) -> bool:
    return any(a <= i < b for a, b in spans)


def _match_bracket(text: str, mask: list[bool], open_i: int, end: int) -> int | None:
    """Index of the bracket closing `text[open_i]`, ignoring comments and `«...»`."""
    close_for = _OPEN_BRACKETS.get(text[open_i])
    if close_for is None:
        return None
    depth = 0
    i = open_i
    while i < end:
        if mask[i]:
            i += 1
            continue
        if text[i] == "«":
            j = text.find("»", i + 1, end)
            if j < 0:
                return None
            i = j + 1
            continue
        ch = text[i]
        if ch in _OPEN_BRACKETS:
            depth += 1
        elif ch in _CLOSE_BRACKETS:
            depth -= 1
            if depth == 0 and ch == close_for:
                return i
            if depth < 0:
                return None
        i += 1
    return None


def _term_end(text: str, mask: list[bool], i: int, end: int) -> int:
    """End of a config term: a top-level comma, or `end`."""
    depth = 0
    while i < end:
        if mask[i]:
            i += 1
            continue
        if text[i] == "«":
            j = text.find("»", i + 1, end)
            if j < 0:
                return end
            i = j + 1
            continue
        ch = text[i]
        if ch in _OPEN_BRACKETS:
            depth += 1
        elif ch in _CLOSE_BRACKETS and depth:
            depth -= 1
        elif ch == "," and depth == 0:
            return i
        i += 1
    return end


_BOOL_ATOMS = tuple(
    prefix + name for prefix in ("", ".", "Bool.", "_root_.Bool.") for name in ("false", "true")
)
_EXPLICIT_FALSE = {".false", "_root_.Bool.false"}


def _paren_contents(
    text: str, mask: list[bool], start: int, end: int
) -> tuple[int, int]:
    i = _skip_ws(text, mask, start, end)
    while i < end and text[i] == "(":
        close = _match_bracket(text, mask, i, end)
        if close is None or _skip_ws(text, mask, close + 1, end) != end:
            break
        end = close
        i = _skip_ws(text, mask, i + 1, end)
    return i, end


def _bool_atom(text: str, mask: list[bool], start: int, end: int) -> str | None:
    i, end = _paren_contents(text, mask, start, end)
    for atom in _BOOL_ATOMS:
        if text.startswith(atom, i, end) and _skip_ws(text, mask, i + len(atom), end) == end:
            return atom
    return None


def _config_has_all_off(text: str, mask: list[bool], start: int, end: int) -> bool:
    """Recognize simple structure literals with a definitely disabled `all`.

    Inherited/computed configurations need an explicit later override. Other
    fields in a recognized literal must have simple values so a newline
    introducing another field cannot be mistaken for part of their value.
    """
    i, end = _paren_contents(text, mask, start, end)
    if i >= end or text[i] != "{":
        return False
    close = _match_bracket(text, mask, i, end)
    if close is None or _skip_ws(text, mask, close + 1, end) != end:
        return False
    i = _skip_ws(text, mask, i + 1, close)
    while i < close:
        name, j = _read_ident(text, i, close)
        j = _skip_ws(text, mask, j, close)
        if name not in {"all", "grind", "star", "try?"} or not text.startswith(":=", j):
            return False
        value_end = _term_end(text, mask, j + 2, close)
        atom = _bool_atom(text, mask, j + 2, value_end)
        if atom is None or (name == "all" and atom not in _EXPLICIT_FALSE):
            return False
        i = _skip_ws(text, mask, value_end + 1, close)
    return True


def _config_may_enable_all(text: str, mask: list[bool], i: int) -> bool:
    """Whether the optConfig may leave `LibrarySearchConfig.all` enabled.

    Apply items left to right. A later `-all` clears a prior flag or unknown
    configuration. Unqualified `false` and `Bool.false` can be shadowed, so
    only an anonymous or root-qualified constructor certifies an off value.
    """
    known_off = True
    end = len(text)
    while True:
        i = _skip_ws(text, mask, i, end)
        if i >= end:
            return not known_off
        if text[i] in "+-":
            # `posConfigItem` / `negConfigItem` require the adjacent identifier.
            ident, j = _read_ident(text, i + 1, end)
            if ident is None or mask[i + 1]:
                return not known_off
            if ident == "all":
                known_off = text[i] == "-"
            i = j
            continue
        if text[i] != "(":
            return not known_off
        name_at = _skip_ws(text, mask, i + 1, end)
        ident, j = _read_ident(text, name_at, end)
        j = _skip_ws(text, mask, j, end)
        if ident is None or not text.startswith(":=", j):
            return not known_off
        close = _match_bracket(text, mask, i, end)
        if close is None:
            return not known_off
        if ident == "all":
            known_off = _bool_atom(text, mask, j + 2, close) in _EXPLICIT_FALSE
        elif ident == "config":
            known_off = _config_has_all_off(text, mask, j + 2, close)
        i = close + 1


# Search tactics share their names with valid term identifiers. Restrict the
# bare apply? policy to tactic starts, not references such as `exact apply?`.
_PROOF_BY_RE = re.compile(r"(?<![\w.'])\bby\b")
_TACTIC_WRAPPER = (
    r"all_goals|any_goals|focus|try|repeat1'|repeat'|repeat|"
    r"with_reducible_and_instances|with_reducible|with_unfolding_all|"
    r"with_unfolding_none|classical|unhygienic|show_term"
)
_TACTIC_LEAD_RE = re.compile(
    rf"(?:[({{·]\s*|\.\s+|(?:{_TACTIC_WRAPPER})\s+)*"
)
_TACTIC_ALT_RE = re.compile(r"(?:first|solve)\b")
_TACTIC_CASE_RE = re.compile(r"(?:case'?|next)\b[^\n]*=>\s*")
_TACTIC_MATCH_RE = re.compile(r"match\b[^\n]*\bwith\b")
_TACTIC_SCOPE_RE = re.compile(r"set_option\s+\S+\s+.+?\s+in\b\s*")
_TACTIC_BODY_RE = re.compile(rf"(?:{_TACTIC_WRAPPER}|first|solve|[{{(·.]|\|)")


def _tactic_prefix(prefix: str) -> bool:
    tail = prefix.lstrip()
    while True:
        lead = _TACTIC_LEAD_RE.match(tail)
        tail = tail[lead.end():]
        scope = _TACTIC_SCOPE_RE.match(tail)
        if not scope:
            break
        tail = tail[scope.end():]
    if not tail or _TACTIC_CASE_RE.fullmatch(tail):
        return True
    if _TACTIC_MATCH_RE.match(tail) and tail.rstrip().endswith("=>"):
        return True
    if _TACTIC_ALT_RE.match(tail) and tail.rstrip().endswith("|"):
        return True
    # A separator inside a term (e.g. `exact (let x := y; apply?)`)
    # is not a tactic separator.
    if not tail.rstrip().endswith((";", "<;>")):
        return False
    if re.search(r"\blet\b", tail) and not tail.startswith("let "):
        return False
    brackets: list[str] = []
    for ch in tail:
        if ch in _OPEN_BRACKETS:
            brackets.append(_OPEN_BRACKETS[ch])
        elif brackets and ch == brackets[-1]:
            brackets.pop()
    return not brackets


def _apply_tactic_position(code: str, start: int) -> bool:
    """Recognize ordinary inline and indented tactic sequence entries."""
    line_start = code.rfind("\n", 0, start) + 1
    prefix = code[line_start:start]
    if any(_tactic_prefix(prefix[m.end():]) for m in _PROOF_BY_RE.finditer(prefix)):
        return True
    indent = len(prefix) - len(prefix.lstrip())
    alternative = prefix.lstrip().startswith("|")
    match_branch = alternative and "=>" in prefix
    if alternative:
        prefix = prefix.lstrip()[1:]
        if match_branch:
            prefix = prefix.rsplit("=>", 1)[1]
    if not _tactic_prefix(prefix):
        return False
    line_end = line_start - 1
    while line_end >= 0:
        line_start = code.rfind("\n", 0, line_end) + 1
        line = code[line_start:line_end]
        line_end = line_start - 1
        body = line.strip()
        if not body:
            continue
        parent_indent = len(line) - len(line.lstrip())
        if parent_indent > indent:
            continue
        opener = _TACTIC_MATCH_RE if match_branch else _TACTIC_ALT_RE
        if opener.match(body):
            alternative = False
        if parent_indent == indent:
            continue
        for match in _PROOF_BY_RE.finditer(line):
            rest = line[match.end():]
            first_tactic = match.end() + len(rest) - len(rest.lstrip())
            if not alternative and (not rest.strip() or first_tactic <= indent
                                    or _TACTIC_BODY_RE.fullmatch(rest.strip())):
                return True
        if body.startswith("|") and body.endswith("=>"):
            alternative = match_branch = True
        elif not (_TACTIC_BODY_RE.fullmatch(body) or _TACTIC_CASE_RE.fullmatch(body)
                  or _TACTIC_SCOPE_RE.fullmatch(body) or _TACTIC_MATCH_RE.fullmatch(body)):
            return False
        indent = parent_indent
    return False


def library_search_admit_tokens(text: str, mask: list[bool]) -> list[tuple[int, str]]:
    """Live collection-mode `exact?` and potentially admitting `apply?` tactics."""
    quoted = _quoted_spans(text, mask)
    code: str | None = None
    hits: list[tuple[int, str]] = []
    for match in _LIBSEARCH_RE.finditer(text):
        start = match.start()
        if mask[start] or _in_span(start, quoted):
            continue
        if start > 0 and (text[start - 1] == "." or text[start - 1] == "«"
                          or _ID_REST_RE.fullmatch(text[start - 1])):
            continue
        end = match.end()
        if end < len(text) and _ID_REST_RE.fullmatch(text[end]):
            continue
        # `exact?%` is a term elaborator. It logs an error instead of admitting silently.
        if match.group(0) == "exact?" and end < len(text) and text[end] == "%":
            continue
        tactic = match.group(0)
        if tactic == "apply?":
            if code is None:
                live = [" " if masked and ch != "\n" else ch for ch, masked in zip(text, mask)]
                for left, right in quoted:
                    live[left:right] = ["\n" if ch == "\n" else " " for ch in live[left:right]]
                code = "".join(live)
            admitting = _apply_tactic_position(code, start)
        else:
            admitting = _config_may_enable_all(text, mask, end)
        if admitting:
            hits.append((start, tactic))
    return hits


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
        matches += library_search_admit_tokens(text, mask)
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
                    "file": f.relative_to(root).as_posix(),
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
