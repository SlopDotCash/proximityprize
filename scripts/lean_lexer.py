#!/usr/bin/env python3
"""Shared Lean 4 lexer for the repository's source gates.

`scripts/forbidden_tokens.py` (CI gate 1), `scripts/sorry_census.py` (CI gate 2)
and `scripts/check-research-boundary.py` all decide what is live code with this
module, so a construct cannot be a comment for one gate and code for another.

Modelled on the Lean v4.30.0-rc2 tokenizer (`src/Lean/Parser/Basic.lean`):

* line comments `--` and nested block comments `/- … -/` (including `/--` and
  `/-!` doc comments). Comment text is never lexed further, so a `"` inside a
  real comment does not open a string;
* string literals with their escapes and string gaps, raw strings `r#*"…"#*`,
  character literals, and the `{…}` holes of interpolated strings (holes are
  code, with their own comments and literals);
* identifiers built from Lean's identifier characters (`isIdFirst` /
  `isIdRest`, so `αx`, `x'` and `x!` are names), `«…»` quoted name parts,
  name literals `` `x`` and numeric literals. Identifiers and numbers are read
  as whole tokens, which decides whether a following `r` or `'` starts a
  literal: `x'"'` is the identifier `x'` then a string, `1'"'` is the number
  `1` then the character `'"'`, and `1r"…"` / `1e5r"…"` are a number then a
  raw string (each checked against Lean with a custom `syntax`).

What a lexer cannot know is whether a given `"…"` is a plain string or an
interpolated one: that depends on the parser consuming it (`s!`, `m!`,
`throwError`, `dbg_trace`, `trace[…]`, or any `syntax … interpolatedStr(term)`).
A literal whose plain and interpolated readings end at the same offset is
lexed as interpolated, so its holes count as code. A literal whose two
readings end at different offsets is *ambiguous*: the rest of the file lexes
differently under each reading. `explore` therefore lexes every combination of
readings of the ambiguous literals it meets (up to a budget) and returns all of
them. A character is *possibly live* when it is code in at least one reading;
callers fail closed when the budget runs out.

This is a lexical model of Lean source, not an elaborated declaration or axiom
audit: it cannot see declarations that a macro or elaborator builds without the
corresponding keyword appearing in the source.
"""

from __future__ import annotations

import re

CODE, COMMENT, LITERAL = 0, 1, 2

# --- Lean identifier characters ----------------------------------------------
# Mirrors `isLetterLike`, `isSubScriptAlnum`, `isIdFirst` and `isIdRest` in
# Lean v4.30.0-rc2 (src/lean/Init/Meta/Defs.lean). `Char.isAlpha` and
# `Char.isAlphanum` are ASCII-only there, so e.g. `ébad`, `αbad` and `𝔽bad` are
# identifiers but other Unicode letters are not.
_LETTER_LIKE = (
    "α-κμ-ω"              # lower Greek except λ
    "Α-ΟΡ΢Τ-Ω"  # upper Greek except Π and Σ
    "ϊ-ϻ"                             # Coptic
    "ἀ-῾"                             # polytonic Greek
    "℀-⅏"                             # letterlike symbols
    "\U0001d49c-\U0001d59f"                     # script/double-struck/fraktur
    "À-ÖØ-öø-ÿ"  # Latin-1 letters except × and ÷
    "Ā-ſ"                             # Latin Extended-A
)
_SUBSCRIPT_ALNUM = "₀-₉ₐ-ₜᵢ-ᵪⱼ"
ID_FIRST = "A-Za-z_" + _LETTER_LIKE
ID_REST = "A-Za-z0-9_'!?" + _LETTER_LIKE + _SUBSCRIPT_ALNUM
# One name component: a plain identifier or a guillemet-quoted `«…»` one (which
# may contain any character but `»`, newlines included).
COMP = "(?:[" + ID_FIRST + "][" + ID_REST + "]*|«[^»]*»)"
# A possibly qualified Lean name (`A.B.c`, `A.«b c».d`).
NAME = COMP + r"(?:\." + COMP + r")*"
# Not preceded by an identifier character, a name separator or an opening
# guillemet: the following token starts a new identifier/keyword.
ID_START = "(?<![" + ID_REST + ".«])"
# Not followed by an identifier character: the preceding token ends here.
ID_END = "(?![" + ID_REST + "])"

_IDENT_RE = re.compile(NAME)
_QUOTED_PART_RE = re.compile("«[^»]*»")
# `numberFnAux`: decimal (with `_` separators and an optional fraction and
# exponent) or `0x`/`0b`/`0o` literals. Whatever follows starts a new token.
_NUMBER_RE = re.compile(
    r"0[xX][0-9A-Fa-f_]*|0[bB][01_]*|0[oO][0-7_]*"
    r"|[0-9][0-9_]*(?:\.[0-9][0-9_]*)?(?:[eE][+-]?[0-9][0-9_]*)?"
)
# `charLitFnAux`: any one character (a newline too) or a valid escape.
_CHAR_RE = re.compile(
    r"'(?:\\(?:[\\\"'nrt]|x[0-9A-Fa-f]{2}|u[0-9A-Fa-f]{4})|[^\\])'", re.DOTALL
)
_RAW_OPEN_RE = re.compile(r'r(#*)"')
# A complete plain string literal (unterminated ones are handled separately).
_PLAIN_STRING_RE = re.compile(r'"(?:[^"\\]|\\.)*"', re.DOTALL)
# Characters that cannot begin a comment, a literal, an identifier, a number or
# a hole brace; runs of them are skipped in one step.
_PLAIN_RUN_RE = re.compile("[^-/\"'«{}`0-9" + ID_FIRST + "]+")
_NON_NEWLINE_RE = re.compile(r"[^\n]")
# Syntax whose string argument Lean core parses as `interpolatedStr(term)`:
# `ident!` prefixes (`s!`, `m!`, `f!`, `println!`, …), `dbg_trace`,
# `throwError`, `trace[cls]` / `trace_goal[cls]` / `Macro.trace[cls]`, and the
# `…At`/named variants that take a term or an error name first. Only used to
# choose the reading that diagnostics refer to; `explore` covers both.
_INTERP_BEFORE_RE = re.compile(
    "(?:[" + ID_REST + r"]!|" + ID_START + r"(?:dbg_trace|throwError)" + ID_END
    + r"|\])[ \t]*\Z"
    + r"|" + ID_START
    + r"(?:throwErrorAt|throwNamedErrorAt|throwNamedError|logNamedErrorAt|logNamedError"
    r"|logNamedWarningAt|logNamedWarning)" + ID_END + r"[^\n\"]*\Z"
)
_TO_CODE = bytes.maketrans(bytes([CODE, COMMENT, LITERAL]), b"\x01\x00\x00")
_TO_COMMENT = bytes.maketrans(bytes([CODE, COMMENT, LITERAL]), b"\x00\x01\x00")


def guess_interpolated(text: str, offset: int) -> bool:
    """Syntactic guess: is the string literal opening at `offset` interpolated?"""
    return bool(_INTERP_BEFORE_RE.search(text, max(0, offset - 200), offset))


class Reading:
    """One consistent lexing of a file under one choice of string readings."""

    __slots__ = ("text", "kind", "strings", "quoted", "ambiguous", "flips")

    def __init__(self, text: str, kind: bytearray, strings: list[tuple[int, int]],
                 quoted: list[tuple[int, int]], ambiguous: list[int],
                 flips: frozenset[int]):
        self.text = text
        # Per character: CODE, COMMENT or LITERAL (string/char/raw-string text,
        # delimiters included; hole contents are classified on their own).
        self.kind = kind
        # Literal spans outside any hole, hole contents included: their text is
        # data and can never hold a command such as `axiom`.
        self.strings = strings
        # `«…»` name parts; their text is part of an identifier.
        self.quoted = quoted
        # Ambiguous string openers met in this reading, in source order.
        self.ambiguous = ambiguous
        # Ambiguous openers read against `guess_interpolated` in this reading.
        self.flips = flips

    def comment_mask(self) -> bytes:
        """1 for every character inside a comment or docstring."""
        return bytes(self.kind).translate(_TO_COMMENT)

    def code_mask(self) -> bytes:
        """1 for every character that is code in this reading."""
        return bytes(self.kind).translate(_TO_CODE)

    def code_text(self) -> str:
        """The text with comments and top-level literals blanked (newlines kept).

        Only this text can hold commands: `#eval IO.println "axiom foo"`
        declares nothing. Interpolation holes are blanked with their literal,
        since a hole is a term and cannot contain a command.
        """
        keep = bytearray(self.code_mask())
        for a, b in self.strings:
            keep[a:b] = bytes(b - a)
        return blank(self.text, keep)


class _Lexer:
    def __init__(self, text: str, flips: frozenset[int] = frozenset(), record: bool = True):
        self.text, self.n, self.flips, self.record = text, len(text), flips, record
        self.kind = bytearray(self.n) if record else bytearray()
        self.strings: list[tuple[int, int]] = []
        self.quoted: list[tuple[int, int]] = []
        self.ambiguous: list[int] = []
        self.used: set[int] = set()

    def _mark(self, a: int, b: int, kind: int) -> None:
        if self.record and b > a:
            self.kind[a:b] = bytes((kind,)) * (b - a)

    def _literal(self, a: int, b: int, top: bool) -> None:
        self._mark(a, b, LITERAL)
        if top and self.record:
            self.strings.append((a, b))

    def _identifier(self, m: re.Match) -> int:
        if self.record and "«" in m.group(0):
            base = m.start()
            for q in _QUOTED_PART_RE.finditer(m.group(0)):
                self.quoted.append((base + q.start(), base + q.end()))
        return m.end()

    def code(self, i: int, hole: bool = False) -> int:
        """Lex code from `i`; in a hole, return the offset of its closing `}`."""
        text, n = self.text, self.n
        depth = 0
        while i < n:
            run = _PLAIN_RUN_RE.match(text, i)
            if run:
                i = run.end()
                continue
            c = text[i]
            if c == "-":
                if text.startswith("--", i):
                    j = text.find("\n", i)
                    j = n if j < 0 else j
                    self._mark(i, j, COMMENT)
                    i = j
                else:
                    i += 1
            elif c == "/":
                i = self.block_comment(i) if text.startswith("/-", i) else i + 1
            elif c == '"':
                i = self.string(i, top=not hole)
            elif c == "'":
                if text.startswith("''", i):  # not a character literal (`''` token)
                    i += 2
                    continue
                m = _CHAR_RE.match(text, i)
                if m:
                    self._literal(i, m.end(), top=not hole)
                    i = m.end()
                else:  # Lean rejects the file; scan on
                    i += 1
            elif c == "{":
                if hole:
                    depth += 1
                i += 1
            elif c == "}":
                if hole:
                    if depth == 0:
                        return i
                    depth -= 1
                i += 1
            elif c == "`":
                j = i + 2 if text.startswith("``", i) else i + 1
                m = _IDENT_RE.match(text, j)
                i = self._identifier(m) if m else i + 1
            elif "0" <= c <= "9":
                i = _NUMBER_RE.match(text, i).end()
            else:  # an identifier start: a letter-like character or `«`
                raw = _RAW_OPEN_RE.match(text, i) if c == "r" else None
                if raw:
                    close = '"' + raw.group(1)
                    j = text.find(close, raw.end())
                    j = n if j < 0 else j + len(close)
                    self._literal(i, j, top=not hole)
                    i = j
                    continue
                m = _IDENT_RE.match(text, i)
                i = self._identifier(m) if m else i + 1  # unterminated `«`: scan on
        return n

    def block_comment(self, i: int) -> int:
        """`i` is at `/-`; return the offset after the matching `-/`.

        The body of a doc comment starts after `/--` or `/-!` (Lean lexes those
        as tokens, then `finishCommentBlock`), so `/--/` does not close it.
        Scanning left to right, whichever of `/-` (nest) and `-/` (close)
        starts first wins, so `/-/` nests.
        """
        text, n = self.text, self.n
        depth, j = 1, i + 2
        if j < n and text[j] in "-!":
            j += 1
        while depth and j < n:
            close = text.find("-/", j)
            if close < 0:
                j = n
                break
            nested = text.find("/-", j, close + 1)
            if nested >= 0:
                depth += 1
                j = nested + 2
            else:
                depth -= 1
                j = close + 2
        self._mark(i, j, COMMENT)
        return j

    def plain_end(self, o: int) -> int:
        m = _PLAIN_STRING_RE.match(self.text, o)
        return m.end() if m else self.n

    def string(self, o: int, top: bool) -> int:
        """`o` is at `"`; lex the literal and return the offset after it."""
        end_plain = self.plain_end(o)
        if "{" not in self.text[o:end_plain]:
            interpolated = False  # both readings agree
        elif not self.record:
            interpolated = guess_interpolated(self.text, o)
        else:
            end_interp = _Lexer(self.text, record=False).interpolated(o)
            if end_interp == end_plain:
                interpolated = True  # same extent: holes are possibly-live code
            else:
                self.ambiguous.append(o)
                interpolated = guess_interpolated(self.text, o)
                if o in self.flips:
                    self.used.add(o)
                    interpolated = not interpolated
        if interpolated:
            end = self.interpolated(o)
        else:
            end = end_plain
            self._mark(o, end, LITERAL)
        if top and self.record:
            self.strings.append((o, end))
        return end

    def interpolated(self, o: int) -> int:
        """Lex `"…"` at `o` as an interpolated string; return the offset after it."""
        text, n = self.text, self.n
        chunk, j = o, o + 1
        while j < n:
            c = text[j]
            if c == "\\":
                j += 2
            elif c == '"':
                self._mark(chunk, j + 1, LITERAL)
                return j + 1
            elif c == "{":
                self._mark(chunk, j + 1, LITERAL)
                close = self.code(j + 1, hole=True)
                if close >= n:
                    return n
                chunk, j = close, close + 1
            else:
                j += 1
        self._mark(chunk, n, LITERAL)
        return n


def lex(text: str, flips: frozenset[int] = frozenset()) -> Reading:
    """Lex `text`, reading each ambiguous literal in `flips` against the guess."""
    lexer = _Lexer(text, frozenset(flips))
    lexer.code(0)
    return Reading(text, lexer.kind, lexer.strings, lexer.quoted, lexer.ambiguous,
                   frozenset(lexer.used))


DEFAULT_BUDGET = 64


def explore(text: str, budget: int = DEFAULT_BUDGET) -> tuple[list[Reading], bool]:
    """Every reading of `text` reachable by flipping ambiguous literals.

    Returns `(readings, exhausted)`. `readings[0]` follows the syntactic guess
    for every literal. `exhausted` is true when more than `budget` distinct
    readings exist; callers must then fail closed.
    """
    base = lex(text)
    readings = [base]
    if not base.ambiguous:
        return readings, False
    seen = {base.flips}
    tried: set[frozenset[int]] = set()
    queue = [base]
    while queue:
        reading = queue.pop(0)
        for off in reading.ambiguous:
            if off in reading.flips:
                continue
            want = reading.flips | {off}
            if want in tried:
                continue
            tried.add(want)
            child = lex(text, want)
            if child.flips in seen:
                continue
            if len(readings) >= budget:
                return readings, True
            seen.add(child.flips)
            readings.append(child)
            queue.append(child)
    return readings, False


def live_mask(readings: list[Reading]) -> bytes:
    """1 for every character that is code in at least one reading."""
    first = readings[0].code_mask()
    if len(readings) == 1:
        return first
    acc = int.from_bytes(first, "big")
    for reading in readings[1:]:
        acc |= int.from_bytes(reading.code_mask(), "big")
    return acc.to_bytes(len(first), "big")


def blank(text: str, keep: bytes | bytearray) -> str:
    """`text` with every character whose `keep` byte is 0 replaced by a space.

    Newlines are kept, so offsets and line numbers are unchanged.
    """
    parts: list[str] = []
    last = 0
    for m in re.finditer(rb"\x00+", bytes(keep)):
        a, b = m.span()
        parts.append(text[last:a])
        parts.append(_NON_NEWLINE_RE.sub(" ", text[a:b]))
        last = b
    parts.append(text[last:])
    return "".join(parts)


def live_text(text: str, budget: int = DEFAULT_BUDGET) -> tuple[str, bool]:
    """`text` with every character that is code in no reading blanked.

    Returns `(text, exhausted)`; if `exhausted`, nothing is blanked.
    """
    readings, exhausted = explore(text, budget)
    if exhausted:
        return text, True
    return blank(text, live_mask(readings)), False
