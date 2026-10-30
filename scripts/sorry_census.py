#!/usr/bin/env python3
"""Deterministic sorry/admit census for the library and research source trees.

Produces a per-declaration inventory of every `sorry`/`admit` token under
ArkLib/ and Research/, distinguishing real proof holes from docstring/comment mentions.
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
         elaborates. A bare `exact?` / `apply?` is not flagged.
  doc  — inside a docstring `/-- ... -/`, block comment `/- ... -/`,
         line comment `-- ...`, raw-string literal, or the literal
         (non-splice) text of a string (includes prose words containing 'admit')

Why every splice counts: many Lean 4.30 built-ins parse a bare string with
`interpolatedStr(term)` and no `!` prefix (`dbg_trace "{x}"`, `throwError`,
`throwErrorAt`, `throwNamedError[At]`, `logNamedError[At]`,
`logNamedWarning[At]`, `trace[cls]`, `trace_goal[cls]`, `Macro.trace[cls]`),
and any project `syntax ... interpolatedStr(term)` can add more. Tracking
consumers is fragile, so the file is parsed both ways with the same
recursive scanner and a token live in either parse is a hole. A plain string
like `"{sorry}"` is therefore a (rare, harmless) false positive.
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


_HEX = "0123456789abcdefABCDEF"
_IDENT_EXTRA = "_'"


def _ident_char(ch: str) -> bool:
    return ch.isalnum() or ch in _IDENT_EXTRA


def _escape_end(text: str, i: int, *, interpolant: bool, allow_gap: bool) -> int | None:
    """Index after a Lean 4.30 string escape starting at `text[i]`, if it is valid.

    Handles backslash, quote, apostrophe, `n`/`t`/`r`, `\\xHH`, `\\uHHHH`,
    a string gap (backslash, newline, then trailing whitespace), and `\\{`
    inside interpolated strings.
    """
    n = len(text)
    if i + 1 >= n or text[i] != "\\":
        return None
    nxt = text[i + 1]
    quotable = "\\\"'rnt{" if interpolant else "\\\"'rnt"
    if nxt in quotable:
        return i + 2
    if nxt == "x" and i + 3 < n and text[i + 2] in _HEX and text[i + 3] in _HEX:
        return i + 4
    if nxt == "u" and i + 5 < n and all(c in _HEX for c in text[i + 2 : i + 6]):
        return i + 6
    if allow_gap and nxt == "\n":
        j = i + 2
        while j < n and text[j] != "\n" and text[j].isspace():
            j += 1
        return j
    return None


def _raw_token_start(text: str, i: int) -> bool:
    """True when `r` at `i` begins a token, so `r#*"..."#*` is a raw string.

    An identifier such as `foor"..."` is not a raw string. A numeric token may
    end immediately before `r` (`1r"..."`, `1_0r"..."`, `0x1r#...#`); hex,
    binary, and octal prefixes are recognized, scientific exponents are not.
    """
    if i == 0:
        return True
    prev = text[i - 1]
    if not _ident_char(prev):
        return True
    if not prev.isdigit():
        return False
    k = i - 1
    while k >= 0 and (text[k].isdigit() or text[k] == "_"):
        k -= 1
    if (
        k >= 1
        and text[k] in "xXoObB"
        and text[k - 1] == "0"
        and (k == 1 or not _ident_char(text[k - 2]))
    ):
        return True
    return k < 0 or not _ident_char(text[k])


def _interpolated_quote(text: str, quote: int) -> bool:
    """True when `"` opens `s!"..."`, `m!"..."`, `println! "..."`, and similar."""
    j = quote - 1
    while j >= 0 and text[j] in " \t":
        j -= 1
    if j <= 0 or text[j] != "!":
        return False
    return _ident_char(text[j - 1])


def _scan_mask(text: str, *, all_interpolated: bool) -> list[bool]:
    """One scan pass; see `strip_comments_map` for how two passes combine.

    Comments and docstrings are masked, and so is literal text of `"..."`,
    raw `r#*"..."#*` strings, and the literal chunks of interpolated strings.
    Code inside interpolated `"{...}"` stays live, so `s!"{sorry}"` is a hole.
    With `all_interpolated`, every non-raw string is treated as interpolated.
    Masking literals stops `--` / `/-` inside a string from swallowing a later
    `sorry`, which the comment-only scan reported as a docstring mention.
    Escaped identifiers `«...»` are skipped first, so a `"`, `--`, `/-`, or
    brace inside one is part of the name.
    """
    n = len(text)
    mask = [False] * n

    def mark(start: int, stop: int) -> None:
        for k in range(start, stop):
            mask[k] = True

    def scan_block(i: int) -> int:
        depth = 0
        while i < n:
            if text.startswith("/-", i):
                depth += 1
                mark(i, min(i + 2, n))
                i += 2
                continue
            if depth > 0 and text.startswith("-/", i):
                depth -= 1
                mark(i, min(i + 2, n))
                i += 2
                if depth == 0:
                    return i
                continue
            if depth > 0:
                mask[i] = True
            i += 1
        return i

    def scan_raw(i: int) -> int:
        hashes = 0
        j = i + 1
        while j < n and text[j] == "#":
            hashes += 1
            j += 1
        if j >= n or text[j] != '"':
            return i + 1
        j += 1
        mark(i, j)
        while j < n:
            if text[j] != '"':
                mask[j] = True
                j += 1
                continue
            mask[j] = True
            j += 1
            if hashes == 0:
                return j
            count = 0
            while count < hashes and j < n and text[j] == "#":
                mask[j] = True
                j += 1
                count += 1
            if count == hashes:
                return j
        return j

    def scan_string(i: int) -> int:
        interpolated = all_interpolated or _interpolated_quote(text, i)
        mask[i] = True
        i += 1
        while i < n:
            if text[i] == "\\":
                end = _escape_end(text, i, interpolant=interpolated, allow_gap=True)
                if end is None:
                    mask[i] = True
                    i += 1
                    continue
                mark(i, end)
                i = end
                continue
            if text[i] == '"':
                mask[i] = True
                return i + 1
            if interpolated and text[i] == "{":
                mask[i] = True
                i = scan_code(i + 1, interpolating=True)
                if i < n and text[i] == "}":
                    mask[i] = True
                    i += 1
                    continue
                return i
            mask[i] = True
            i += 1
        return i

    def skip_char_lit(i: int) -> int | None:
        # Primes (`x'`) and `''` are not character literals. `'"'` must not
        # open a string, or the following source is masked through the next `"`.
        if i + 2 >= n or text[i] != "'" or text[i + 1] == "'":
            return None
        if i > 0 and _ident_char(text[i - 1]):
            return None
        if text[i + 1] == "\\":
            end = _escape_end(text, i + 1, interpolant=False, allow_gap=False)
            if end is None:
                return None
            j = end
        elif text[i + 1] == "\n":
            return None
        else:
            j = i + 2
        if j < n and text[j] == "'":
            return j + 1
        return None

    def raw_follows(i: int) -> bool:
        j = i + 1
        while j < n and text[j] == "#":
            j += 1
        return j < n and text[j] == '"'

    def scan_code(i: int, *, interpolating: bool) -> int:
        brace = 0
        while i < n:
            if text[i] == "«":
                # Lean reads everything up to the next `»` as one escaped
                # identifier (`def «"»`, `«--»`, `«}»`), so none of it may open
                # a string, comment, or splice brace. The text stays live.
                # Unterminated `«` is a Lean lex error; scan on normally.
                j = text.find("»", i + 1)
                if j >= 0:
                    i = j + 1
                    continue
            if text.startswith("--", i):
                j = text.find("\n", i)
                mark(i, n if j < 0 else j)
                i = n if j < 0 else j
                continue
            if text.startswith("/-", i):
                i = scan_block(i)
                continue
            ch = text[i]
            if ch == '"':
                i = scan_string(i)
                continue
            if ch == "r" and _raw_token_start(text, i) and raw_follows(i):
                i = scan_raw(i)
                continue
            if ch == "'":
                nxt = skip_char_lit(i)
                if nxt is not None:
                    i = nxt
                    continue
            if interpolating and ch == "{":
                brace += 1
            elif interpolating and ch == "}":
                if brace == 0:
                    return i
                brace -= 1
            i += 1
        return i

    scan_code(0, interpolating=False)
    return mask


def strip_comments_map(text: str) -> list[bool]:
    """Return per-char mask: True if the char is not live code in EITHER reading.

    Lean v4.30.0-rc2 has many `interpolatedStr(term)` consumers without a `!`
    prefix (`dbg_trace`, `throwError[At]`, `throwNamedError[At]`,
    `logNamedError[At]`, `logNamedWarning[At]`, `trace[..]`, `trace_goal[..]`,
    `Macro.trace[..]`), and projects can declare more, so a bare `"..."` may or
    may not be interpolated. Rather than guess, the file is scanned twice with
    the same recursive scanner:
      * plain:        only `prefix! "..."` strings are interpolated;
      * interpolated: every non-raw `"..."` is interpolated, so each `{...}`
                      splice is parsed as code (comments, nested strings, char
                      literals, raw strings, nested interpolation).
    Each pass is a self-consistent parse. A char is masked only if both passes
    mask it, so a `sorry` live under either reading is a hole. The cost is a
    rare false positive such as a plain `"{sorry}"` string.
    """
    plain = _scan_mask(text, all_interpolated=False)
    interp = _scan_mask(text, all_interpolated=True)
    return [x and y for x, y in zip(plain, interp)]


def _skip_ws(text: str, mask: list[bool], i: int, end: int) -> int:
    while i < end and (text[i].isspace() or mask[i]):
        i += 1
    return i


def _read_ident(text: str, i: int, end: int) -> tuple[str | None, int]:
    if i >= end or not _ID_FIRST_RE.fullmatch(text[i]):
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


def _as_bool_literal(text: str, mask: list[bool], start: int, end: int) -> bool | None:
    i = _skip_ws(text, mask, start, end)
    if i < end and text[i] == "(":
        close = _match_bracket(text, mask, i, end)
        if close is None:
            return None
        if _skip_ws(text, mask, close + 1, end) != end:
            return None
        return _as_bool_literal(text, mask, i + 1, close)
    ident, j = _read_ident(text, i, end)
    if _skip_ws(text, mask, j, end) != end:
        return None
    if ident == "true":
        return True
    if ident == "false":
        return False
    return None


def _struct_all(text: str, mask: list[bool], start: int, end: int) -> bool | None:
    """The `all` field of a structure literal, or None if a source hides it.

    `{ all := true }` and `{ cfg with all := true }` are determined. `{ grind := true }`
    uses the default `false`. `{ cfg with grind := true }` and `{ ..cfg }` inherit `all`
    from a value this scan cannot see.
    """
    explicit: bool | None = None
    saw_explicit = False
    saw_inherit = False
    i = start
    depth = 0
    while i < end:
        if mask[i] or text[i].isspace():
            i += 1
            continue
        if text[i] == "«":
            j = text.find("»", i + 1, end)
            i = end if j < 0 else j + 1
            continue
        ch = text[i]
        if ch in _OPEN_BRACKETS:
            depth += 1
            i += 1
            continue
        if ch in _CLOSE_BRACKETS:
            if depth:
                depth -= 1
            i += 1
            continue
        if depth:
            i += 1
            continue
        if text.startswith("..", i):
            saw_inherit = True
            i += 2
            continue
        ident, j = _read_ident(text, i, end)
        if ident is None:
            i += 1
            continue
        if ident == "with":
            saw_inherit = True
            i = j
            continue
        j2 = _skip_ws(text, mask, j, end)
        if text.startswith(":=", j2):
            val_end = _term_end(text, mask, j2 + 2, end)
            if ident == "all":
                explicit = _as_bool_literal(text, mask, j2 + 2, val_end)
                saw_explicit = True
            i = val_end
            continue
        i = j
    if saw_explicit:
        return explicit
    if saw_inherit:
        return None
    return False


def _config_term_all(text: str, mask: list[bool], start: int, end: int) -> bool | None:
    """Whether a `(config := term)` or `(all := term)` value sets `all`."""
    i = _skip_ws(text, mask, start, end)
    if i < end and text[i] == "(":
        close = _match_bracket(text, mask, i, end)
        if close is None or _skip_ws(text, mask, close + 1, end) != end:
            return None
        return _config_term_all(text, mask, i + 1, close)
    if i < end and text[i] == "{":
        close = _match_bracket(text, mask, i, end)
        if close is None or _skip_ws(text, mask, close + 1, end) != end:
            return None
        return _struct_all(text, mask, i + 1, close)
    return _as_bool_literal(text, mask, start, end)


def _config_enables_all(text: str, mask: list[bool], i: int) -> bool:
    """True when the optConfig at `i` leaves `LibrarySearchConfig.all` set.

    Items apply left to right, matching `elabConfig`: `+all` / `-all` and
    `(all := true/false)` update the field, and `(config := ...)` replaces it.
    A later item wins. `+all -all` and `+all (config := { grind := true })`
    finish with `all` false (pinned Lean v4.30.0-rc2).
    """
    enabled = False
    end = len(text)
    while True:
        i = _skip_ws(text, mask, i, end)
        if i >= end:
            return enabled
        if text[i] in "+-":
            # `posConfigItem` / `negConfigItem` are `" +"` / `" -"` then `noWs ident`.
            if i + 1 >= end or text[i + 1].isspace() or mask[i + 1]:
                return enabled
            ident, j = _read_ident(text, i + 1, end)
            if ident is None:
                return enabled
            if ident == "all":
                enabled = text[i] == "+"
            i = j
            continue
        if text[i] != "(":
            return enabled
        name_at = _skip_ws(text, mask, i + 1, end)
        ident, j = _read_ident(text, name_at, end)
        j = _skip_ws(text, mask, j, end)
        if ident is None or not text.startswith(":=", j):
            return enabled
        close = _match_bracket(text, mask, i, end)
        if close is None:
            return enabled
        if ident in {"all", "config"}:
            value = _config_term_all(text, mask, j + 2, close)
            # A named `(config := cfg)` is not inspected: an empty config clears
            # `+all`, and guessing `true` would reject that proof.
            enabled = bool(value)
        i = close + 1


def library_search_admit_tokens(text: str, mask: list[bool]) -> list[tuple[int, str]]:
    """Live `exact?` / `apply?` whose config admits the goal via `sorryAx`."""
    quoted = _quoted_spans(text, mask)
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
        if _config_enables_all(text, mask, end):
            hits.append((start, match.group(0)))
    return hits


def census(root: Path) -> list[dict]:
    rows: list[dict] = []
    for f in sorted(f for name in ("ArkLib", "Research") for f in (root / name).rglob("*.lean")):
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
                    "file": str(f.relative_to(root)),
                    "line": line_no + 1,
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
