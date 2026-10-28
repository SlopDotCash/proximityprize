#!/usr/bin/env python3
"""Reject axiom-laundering tokens in live library and research source.

By default, scans every .lean file under ArkLib/ and Research/. If one or more paths are
provided, scans only those Lean files/directories. Fails if live
(non-comment) code contains (`axiom` text inside a string literal is data):
  - `native_decide` / `bv_decide` (kernel-bypassing decision procedures), the
    equivalent `decide +native` / `decide (native := true)` forms and `bv_check`, or
  - an `unsafe` declaration modifier, live `unsafeCast`, or `implemented_by`
    attribute (repository policy: block unsafe decls, unsafeCast, and
    evaluator-diverging `implemented_by`; this is a fast precheck, not a claim
    that Lean accepts unsafe theorems as axiom-clean proofs), or
  - a metaprogram that adds kernel declarations (`run_cmd` / `run_elab` /
    `run_meta`, `addDecl`, `addAndCompile`, `axiomDecl`), which can declare an
    axiom without the `axiom` keyword, or
  - a custom `axiom` declaration whose name is not an allowlisted, documented
    residual (see scripts/residual_axioms.txt), with any modifiers (including
    `public`/`meta` in `module` files) and with the name on a later line or
    after a comment, or
  - a second declaration of an allowlisted residual name. The allowlist stores
    simple names, so an entry matches an `axiom` declared inside any namespace;
    without this rule a clone such as
    `namespace Sneaky … axiom foldOracleVerifier_rbrKnowledgeSoundness : False … end`
    inherits a documented entry and launders a new axiom under a trusted name.
    One entry documents exactly one declaration, or
  - a `theorem`/`lemma` whose statement type is `True`, or any bracketing /
    `∧` `∨` `→` `↔` combination built only from `True` (e.g. `(True)`,
    `True ∧ (True)`), which is equally vacuous, unless `True` is rebound by a
    binder, an in-scope `variable`, or a non-`protected` `True` declared in the
    current namespace or a prefix of it (then it is a real proposition, e.g.
    `theorem t (True : Prop) : True → True`); scopes follow
    `namespace`/`section`/`mutual`/`end`, and anything else fails closed (a
    placebo that discharges no real obligation, e.g.
    `theorem foo_residual : True := by trivial`). This is the axiom-laundering
    pattern the #169/#171 audits removed: flipping `axiom … : True` into a
    trivially-proved `theorem … : True` slips past the `axiom` check above
    while proving nothing about the named obligation.
  - any other vacuous declaration named like a residual/keystone/conjecture
    obligation and typed as `True`.
  - a bodyless `opaque`/`constant` declaration (no `:=` body). Such a
    declaration introduces an *unproven inhabitant* of its statement type, so
    it is axiom-equivalent — and `constant` no longer parses in Lean 4. This is
    the laundering pattern the #114 audit removed: `noncomputable constant
    foo_holds : <security Prop>` asserts the obligation with no proof and slips
    past the `axiom` check above. (`opaque foo : T := v`, with a real body, is
    fine and is *not* flagged.)

Comment and docstring occurrences are ignored. Comments, string/raw-string/char
literals and guillemet-quoted identifiers are lexed together (see `lex_lean`),
and identifier boundaries use Lean's own identifier characters (`αbad`, `ébad`,
`𝔽bad` are names). A string literal whose plain and interpolated readings would
disagree about what is a comment fails the check rather than being guessed. `sorry`/`admit` are handled
separately by scripts/sorry_census.py --fail-on-holes; this precheck runs
before any Lean toolchain is set up, so CI fails fast on laundering attempts.

The one-declaration rule needs both declarations in the scanned set, so it is
enforced by the full-tree scan that CI (`.github/workflows/ci.yml`) and
`scripts/validate.sh` run. A file-scoped invocation still enforces every other
check and still rejects two declarations of an allowlisted name inside the file
it was given.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

TOKEN_RE = re.compile(r"\b(native_decide|bv_decide|unsafeCast|implemented_by)\b")
# Meta code can add a kernel declaration without the `axiom` keyword, e.g.
# `run_cmd liftCoreM <| addDecl (.axiomDecl { name := `w, type := mkConst ``False, .. })`.
# ArkLib/Research proofs never need to add declarations from metaprograms.
META_DECL_RE = re.compile(
    r"(?<![\w.'])(run_cmd|run_elab|run_meta)\b"
    r"|\b(add(?:Decl\w*|AndCompile)|axiomDecl)\b"
)
# `native_decide` is a synonym for `decide +native`; both forms, the config form
# `decide (native := true)` / `(config := { native := true })` and `bv_check`
# prove the goal by native evaluation and add a compiler-trust axiom. Matched
# against comment/string-blanked code, so a comment between the parts does not
# hide the form.
NATIVE_FORM_RE = re.compile(
    r"\bdecide(?:\s*(?:[+-]\w+|\([^)]*\)))*?\s*"
    r"(?:\+native\b|\([^)]*\bnative\s*:=\s*true\b[^)]*\))"
    r"|\bbv_check\b"
)
# Lean declaration-modifier `unsafe` (not aesop's `(add unsafe …)` tactic hint).
# Allow the same modifiers before or after `unsafe` (Lean accepts e.g.
# `unsafe nonrec def`), then require a declaration keyword so
# `aesop (add unsafe …)` and `attribute [aesop unsafe 50%]` stay allowed.
UNSAFE_DECL_RE = re.compile(
    r"(?m)^[ \t]*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:public|protected|private|scoped|noncomputable|partial|nonrec|meta|local)\s+)*"
    r"unsafe\s+"
    r"(?:(?:public|protected|private|scoped|noncomputable|partial|nonrec|meta|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev|opaque|constant|axiom|instance|structure|inductive|class|example)\b"
)


# --- Lean identifier characters ---------------------------------------------
# Mirrors `isLetterLike`, `isSubScriptAlnum`, `isIdFirst` and `isIdRest` in
# Lean v4.30.0-rc2 (src/lean/Init/Meta/Defs.lean). `Char.isAlpha` and
# `Char.isAlphanum` are ASCII-only there, so e.g. `ébad`, `αbad` and `𝔽bad` are
# identifiers but other Unicode letters are not.
_LETTER_LIKE = (
    "\u03b1-\u03ba\u03bc-\u03c9"              # lower Greek except λ
    "\u0391-\u039f\u03a1\u03a2\u03a4-\u03a9"  # upper Greek except Π and Σ
    "\u03ca-\u03fb"                             # Coptic
    "\u1f00-\u1ffe"                             # polytonic Greek
    "\u2100-\u214f"                             # letterlike symbols
    "\U0001d49c-\U0001d59f"                     # script/double-struck/fraktur
    "\u00c0-\u00d6\u00d8-\u00f6\u00f8-\u00ff"  # Latin-1 letters except × and ÷
    "\u0100-\u017f"                             # Latin Extended-A
)
_SUBSCRIPT_ALNUM = "\u2080-\u2089\u2090-\u209c\u1d62-\u1d6a\u2c7c"
ID_FIRST = "A-Za-z_" + _LETTER_LIKE
ID_REST = "A-Za-z0-9_'!?" + _LETTER_LIKE + _SUBSCRIPT_ALNUM
_ID_REST_RE = re.compile("[" + ID_REST + "]")
# One name component: a plain identifier or a guillemet-quoted `«…»` one (which
# may contain any character but `»`, newlines included).
_COMP = "(?:[" + ID_FIRST + "][" + ID_REST + "]*|«[^»]*»)"
# Not preceded by an identifier character, a name separator or an opening
# guillemet: the following token starts a new identifier/keyword.
_ID_START = "(?<![" + ID_REST + ".«])"
# Not followed by an identifier character: the preceding token ends here.
_ID_END = "(?![" + ID_REST + "])"
# Capture the declared axiom name so it can be checked against the residual
# allowlist. The name may be namespaced/contain primes; we keep the simple
# token as written at the declaration site.
# Lean declaration names: plain identifiers (possibly namespaced/primed) or
# guillemet-quoted `«…»` components.
_NAME = _COMP + r"(?:\." + _COMP + r")*"
# `axiom` is a reserved keyword in Lean 4, so any live (non-comment) `axiom`
# token starts an axiom declaration, whatever modifiers, attributes or docstring
# precede it. Matching the keyword itself (rather than a line-anchored modifier
# list) means the check does not depend on knowing every modifier: Lean
# v4.30.0-rc2 accepts `public`, `private`, `protected`, `noncomputable`,
# `unsafe`, `partial`, `nonrec` and `meta` (and combinations) before `axiom`, in
# both `module` and ordinary files. The keyword boundary uses Lean's own
# identifier characters, so `αaxiom` or `axiomα` is an identifier, not the
# keyword. The regex runs on the comment-blanked source of the whole file, so
# `\s*` also spans newlines and blanked comments: `axiom\n  foo`,
# `axiom/- c -/foo`, `axiom/- c\n-/foo` and `axiom«foo»` are all seen.
AXIOM_RE = re.compile(_ID_START + r"axiom" + _ID_END + r"\s*(" + _NAME + r")")
# Text inside a guillemet-quoted identifier (`«an axiom counterfeit'»`) is part
# of a name, not a command, so an `axiom` match that starts inside one is not a
# declaration. Quoted-identifier spans come from `lex_lean`, which also lexes
# string, raw-string and char literals, so a `«` inside a literal (`"«"`,
# `'«'`) never opens a span and cannot hide a real `axiom` command.
# Declaration heads, matched like `axiom` above: Lean's command parser does not
# care about line breaks, so `def keep : Nat := 1 theorem t : True := trivial`
# declares `t` mid-line. These are all keywords in Lean 4 (`lemma` with
# Mathlib), so a live keyword token starts a declaration whatever precedes it.
DECL_RE = re.compile(
    _ID_START + r"(axiom|theorem|lemma|def|abbrev|opaque)" + _ID_END + r"\s*(" + _NAME + r")"
)
# `constant` is not a Lean 4 keyword (it is an ordinary identifier), so only a
# line-start head is treated as a declaration.
CONSTANT_DECL_RE = re.compile(
    # Keep leading indentation on one line: masked block comments can contain
    # thousands of whitespace-only lines, making ^\s* retry their whole suffix.
    r"^[ \t]*(?:@\[[^\]]*\]\s*)?"
    r"(?:(?:public|protected|private|scoped|noncomputable|unsafe|partial|nonrec|meta)\s+)*"
    r"(constant)" + _ID_END + r"\s*(" + _NAME + r")",
    re.MULTILINE,
)

# A bodyless `opaque`/`constant` declaration introduces an *unproven inhabitant* of its statement
# type — it is axiom-equivalent (and `constant` no longer even parses in Lean 4). This is the
# laundering vector the #114 audit caught: `noncomputable constant foo_holds : <security Prop>`
# asserts the obligation with no proof and slips past the `axiom` check above. We flag any live
# `opaque`/`constant` head that has no top-level `:=` body.
OPAQUE_KINDS = {"opaque", "constant"}

ALLOWLIST_PATH = Path(__file__).resolve().parent / "residual_axioms.txt"

# Heads of proof-carrying declarations whose statement type must never be the
# vacuous `True`. The live `theorem`/`lemma` keyword starts a declaration
# anywhere on a line; an in-proof `have … : True` has no such keyword.
PLACEBO_DECL_RE = re.compile(
    _ID_START + r"(theorem|lemma)" + _ID_END + r"\s*(" + _NAME + r")"
)

# Brackets that may carry binder/type colons we must skip when locating the
# top-level statement colon.
_BRACKET_OPEN = {"(": ")", "[": "]", "{": "}", "⟨": "⟩"}
_BRACKET_CLOSE = {")", "]", "}", "⟩"}


def load_allowlist(path: Path) -> set[str]:
    """Names of documented residual axioms permitted in live source."""
    if not path.exists():
        return set()
    names: set[str] = set()
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.split("#", 1)[0].strip()
        if line:
            names.add(line.split()[0])
    return names


def scan_plan(args: list[str]) -> tuple[list[Path], bool, list[str]]:
    """Return files to scan, whether this is a full-ArkLib scan, and path errors."""
    if not args:
        return sorted(f for name in ("ArkLib", "Research") for f in Path(name).rglob("*.lean")), True, []

    files: set[Path] = set()
    full_arklib_scan = False
    errors: list[str] = []
    arklib_root = Path("ArkLib").resolve()

    for raw in args:
        path = Path(raw)
        if not path.exists():
            errors.append(f"{path}: path does not exist")
            continue
        if path.is_file():
            if path.suffix == ".lean":
                files.add(path)
            else:
                errors.append(f"{path}: expected a .lean file")
            continue

        nested_arklib = path / "ArkLib"
        if nested_arklib.is_dir():
            files.update(nested_arklib.rglob("*.lean"))
            files.update((path / "Research").rglob("*.lean"))
            full_arklib_scan = True
        else:
            files.update(path.rglob("*.lean"))
            if path.resolve() == arklib_root:
                full_arklib_scan = True

    return sorted(files), full_arklib_scan, errors


# --- Lean lexing ------------------------------------------------------------
# Comments, string literals, raw strings, char literals and quoted identifiers
# must be lexed together: `"/-"` or `'«'` is a literal, not a comment or
# identifier opener, while `«a -- b»` or `«x'»` is one identifier.
_CHAR_LIT_RE = re.compile(r"'(?:\\(?:x[0-9A-Fa-f]{2}|u[0-9A-Fa-f]{4}|.)|[^\\'\n])'", re.DOTALL)
_RAW_OPEN_RE = re.compile(r'r(#*)"')
# Syntax that Lean core parses as `interpolatedStr(term)`, whose `{…}` holes are
# code (with their own comments and strings): `s!`/`m!`/`f!`/`v!`-style `ident!`
# prefixes (also `println!`), `throwError`, `throwErrorAt t` and `trace[…]`.
_INTERP_PREFIX_RE = re.compile(
    r"(?:[" + ID_REST + r"]!|" + _ID_START + r"throwError" + _ID_END + r"|\])[ \t]*\Z")
_INTERP_AT_RE = re.compile(_ID_START + r"throwErrorAt" + _ID_END + r"[^\n\"]*\Z")


class LexResult:
    def __init__(self, n: int):
        self.mask = [False] * n
        self.quoted: list[tuple[int, int]] = []
        # String literals whose plain and interpolated readings end at different
        # offsets: Lean's choice depends on the parser context.
        self.ambiguous: list[int] = []
        # Top-level string/char literal spans (interpolation holes included):
        # their text is data, never a command such as `axiom`.
        self.strings: list[tuple[int, int]] = []


class _Lexer:
    def __init__(self, text: str, flip: frozenset[int] = frozenset(), record: bool = True):
        self.text, self.n, self.flip, self.record = text, len(text), flip, record
        self.res = LexResult(self.n)

    def _token_start(self, i: int) -> bool:
        return i == 0 or not _ID_REST_RE.match(self.text[i - 1])

    def _mark(self, a: int, b: int) -> None:
        if self.record:
            for k in range(a, min(b, self.n)):
                self.res.mask[k] = True

    def block_comment(self, i: int) -> int:
        """`i` is at `/-`; return the offset after the matching `-/`."""
        text, n, depth, j = self.text, self.n, 1, i + 2
        while j < n and depth:
            if text.startswith("/-", j):
                depth += 1
                j += 2
            elif text.startswith("-/", j):
                depth -= 1
                j += 2
            else:
                j += 1
        self._mark(i, j)
        return j

    def guess_interpolated(self, i: int) -> bool:
        before = self.text[max(0, i - 200):i]
        return bool(_INTERP_PREFIX_RE.search(before) or _INTERP_AT_RE.search(before))

    def string(self, i: int, interpolated: bool) -> int:
        """`i` is at `"`; return the offset after the closing `"`."""
        text, n, j = self.text, self.n, i + 1
        while j < n:
            c = text[j]
            if c == "\\":
                j += 2
            elif c == '"':
                return j + 1
            elif c == "{" and interpolated:
                j = self.code(j + 1, nested=True)
                j += 1  # past the closing `}`
            else:
                j += 1
        return n

    def code(self, i: int, nested: bool = False) -> int:
        """Lex code from `i`; if `nested`, stop at the `}` closing a `{…}` hole."""
        text, n, depth = self.text, self.n, 0
        while i < n:
            c = text[i]
            if text.startswith("--", i):
                j = text.find("\n", i)
                j = n if j == -1 else j
                self._mark(i, j)
                i = j
            elif text.startswith("/-", i):
                i = self.block_comment(i)
            elif c == '"':
                guess = self.guess_interpolated(i)
                interp = guess != (i in self.flip)
                if self.record:
                    plain_end = _Lexer(text, record=False).string(i, False)
                    if ("{" in text[i:plain_end]
                            and _Lexer(text, record=False).string(i, True) != plain_end):
                        self.res.ambiguous.append(i)
                j = self.string(i, interp)
                if self.record and not nested:
                    self.res.strings.append((i, j))
                i = j
            elif c == "r" and self._token_start(i) and (m := _RAW_OPEN_RE.match(text, i)):
                close = '"' + m.group(1)
                j = text.find(close, m.end())
                j = n if j == -1 else j + len(close)
                if self.record and not nested:
                    self.res.strings.append((i, j))
                i = j
            elif c == "'" and self._token_start(i) and (m := _CHAR_LIT_RE.match(text, i)):
                if self.record and not nested:
                    self.res.strings.append((i, m.end()))
                i = m.end()
            elif c == "«":
                j = text.find("»", i + 1)
                if j == -1:  # unterminated: Lean rejects the file; exempt nothing
                    i += 1
                else:
                    if self.record:
                        self.res.quoted.append((i, j + 1))
                    i = j + 1
            elif nested and c == "{":
                depth += 1
                i += 1
            elif nested and c == "}":
                if depth == 0:
                    return i
                depth -= 1
                i += 1
            else:
                i += 1
        return n


def lex_lean(text: str, flip: frozenset[int] = frozenset()) -> LexResult:
    """Comment mask and quoted-identifier spans of a Lean source file.

    `flip` lists string-literal offsets whose plain/interpolated reading is
    inverted relative to the syntactic guess (used to test ambiguity).
    """
    lexer = _Lexer(text, flip)
    lexer.code(0)
    return lexer.res


def ambiguous_literals(text: str, res: LexResult) -> list[int]:
    """Ambiguous string literals whose other reading changes comment/identifier structure.

    Whether `"…{…}…"` is a plain or an interpolated string depends on the
    parser (any macro may take `interpolatedStr(term)`). When the two readings
    differ we lex the file both ways; if that changes which characters are
    comments or quoted identifiers, the scan cannot be trusted, so it fails.
    """
    bad = []
    for off in res.ambiguous:
        alt = lex_lean(text, frozenset({off}))
        if (alt.mask != res.mask or alt.quoted != res.quoted
                or command_view(text, alt) != command_view(text, res)):
            bad.append(off)
    return bad


def code_text(text: str, res: LexResult) -> str:
    """`text` with comments and string/char literals blanked (newlines kept).

    Only this text can hold commands: `#eval IO.println "axiom foo"` declares
    nothing, so `axiom` inside a literal is data, not a declaration.
    """
    blank = list(res.mask)
    for a, b in res.strings:
        for k in range(a, min(b, len(blank))):
            blank[k] = True
    return "".join(ch if (ch == "\n" or not blank[i]) else " " for i, ch in enumerate(text))


def outside_quoted(offset: int, quoted: list[tuple[int, int]]) -> bool:
    """Command heads cannot start inside a guillemet identifier."""
    return not any(a <= offset < b for a, b in quoted)


def declaration_heads(code: str, res: LexResult) -> list[re.Match]:
    """Live declaration heads in source order (`DECL_RE` and `CONSTANT_DECL_RE`)."""
    heads = [m for rx in (DECL_RE, CONSTANT_DECL_RE) for m in rx.finditer(code)
             if outside_quoted(m.start(), res.quoted)]
    return sorted(heads, key=lambda m: m.start())


def axiom_hits(code: str, res: LexResult) -> list[tuple[int, str]]:
    """Live `axiom` declarations: offset and declared name."""
    return [(m.start(), m.group(1)) for m in AXIOM_RE.finditer(code)
            if outside_quoted(m.start(), res.quoted)]


def command_view(text: str, res: LexResult) -> tuple:
    """What the checks see under one lexing: axiom, declaration and placebo hits."""
    code = code_text(text, res)
    return (axiom_hits(code, res),
            [(m.start(), m.group(1), m.group(2)) for m in declaration_heads(code, res)],
            find_true_placebos(text, res))


def comment_mask(text: str) -> list[bool]:
    """Return per-char mask: True if the char is inside a comment/docstring."""
    return lex_lean(text).mask


def simple_name(name: str) -> str:
    """Final component of a possibly namespaced Lean declaration name."""
    return name.rsplit(".", 1)[-1]


def is_allowlisted(name: str, allowlist: set[str]) -> bool:
    return name in allowlist or simple_name(name) in allowlist


def is_residual_like(name: str, allowlist: set[str]) -> bool:
    final = simple_name(name)
    low = final.lower()
    return (
        is_allowlisted(name, allowlist)
        # Obligation-like names carry the residual suffix in the library's
        # camelCase convention (`fiatShamir_hvzkTransferResidual`,
        # `claim57Residuals`) as well as snake_case (`foo_residual`); matching
        # only the literal `_residual` spelling missed every residual in ArkLib.
        or low.endswith("residual")
        or low.endswith("residuals")
        or "keystone" in low
        or "conjecture" in low
    )


def strip_outer_parens(text: str) -> str:
    """Strip balanced outer parentheses around a syntactic result type."""
    result = text.strip()
    while result.startswith("(") and result.endswith(")"):
        depth = 0
        balanced_outer = True
        for idx, ch in enumerate(result):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and idx != len(result) - 1:
                    balanced_outer = False
                    break
                if depth < 0:
                    balanced_outer = False
                    break
        if not balanced_outer or depth != 0:
            break
        result = result[1:-1].strip()
    return result


# Connectives allowed in a vacuous `True`-only statement. A formula whose only
# atoms are `True` is a tautology under all of these, so it proves nothing.
_TRUE_ONLY_RE = re.compile(r"(?:\s|[()]|True\b|∧|∨|→|↔|/\\|\\/|->|<->)+")


def is_vacuous_true(stmt: str) -> bool:
    """True if `stmt` is built only from `True`, parentheses and logical connectives."""
    stmt = stmt.strip()
    return "True" in stmt and _TRUE_ONLY_RE.fullmatch(stmt) is not None


def top_level_result_type(header: str) -> str | None:
    """Return the text after the last top-level ':' in a declaration header."""
    colon = top_level_colon(header)
    if colon is None:
        return None
    return strip_outer_parens(header[colon + 1:])


def top_level_colon(header: str) -> int | None:
    """Offset of the last top-level ':' (not ':=') in a declaration header."""
    depth_paren = depth_brace = depth_bracket = 0
    last_colon: int | None = None
    i = 0
    while i < len(header):
        ch = header[i]
        if ch == "(":
            depth_paren += 1
        elif ch == ")" and depth_paren > 0:
            depth_paren -= 1
        elif ch == "{":
            depth_brace += 1
        elif ch == "}" and depth_brace > 0:
            depth_brace -= 1
        elif ch == "[":
            depth_bracket += 1
        elif ch == "]" and depth_bracket > 0:
            depth_bracket -= 1
        elif ch == ":" and depth_paren == 0 and depth_brace == 0 and depth_bracket == 0:
            # Skip ':=' if the terminator survived in a malformed header slice.
            if i + 1 >= len(header) or header[i + 1] != "=":
                last_colon = i
        i += 1
    return last_colon


def declaration_header_end(live_text: str, start: int, next_decl_start: int | None) -> int:
    """Best-effort end offset for a Lean declaration header."""
    limit = next_decl_start if next_decl_start is not None else len(live_text)
    candidates = [pos for token in (":=", " where") if (pos := live_text.find(token, start, limit)) != -1]
    if candidates:
        return min(candidates)
    return limit


# --- `True` shadowing -------------------------------------------------------
# `True` is an ordinary name in Lean, so it can be rebound: a binder
# `(True : Prop)`, a `variable (True : Prop)`, or a declaration whose last name
# component is `True` (e.g. `def F.True` inside `namespace F`). A statement such
# as `True → True` is then a real universally quantified proposition, not a
# vacuous placebo. The vacuity check only fires when `True` provably means the
# built-in constant; when resolution is uncertain it errs toward *not* flagging.
_TRUE_TOKEN_RE = re.compile(_ID_START + r"(?:True|«True»)" + _ID_END)
_BINDER_OPEN = {"(": ")", "{": "}", "[": "]", "⦃": "⦄", "⟨": "⟩"}
_VARIABLE_RE = re.compile(_ID_START + r"variable" + _ID_END)


def binder_names(segment: str) -> set[str]:
    """Names bound by the bracketed binder groups at the top level of `segment`.

    Handles `(a b : T)`, `{a : T}`, `⦃a : T⦄`, `{{a : T}}`, `[a : T]`,
    `(a : T := v)` and untyped `(a)`; nested brackets inside a binder's type are
    skipped. `«True»` is normalised to `True`.
    """
    names: set[str] = set()
    i, n = 0, len(segment)
    while i < n:
        ch = segment[i]
        if ch in _BINDER_OPEN:
            close = _BINDER_OPEN[ch]
            depth = 1
            j = i + 1
            # `{{ … }}` strict-implicit spelling: treat the inner brace as part of the opener.
            if ch == "{" and j < n and segment[j] == "{":
                j += 1
            head_end = None
            k = j
            while k < n and depth:
                c = segment[k]
                if c in _BINDER_OPEN:
                    depth += 1
                elif c in _BINDER_CLOSE_ALL and depth:
                    depth -= 1
                    if depth == 0:
                        break
                elif c == ":" and depth == 1 and head_end is None:
                    head_end = k
                k += 1
            head = segment[j:head_end if head_end is not None else k]
            for tok in _BINDER_TOKEN_RE.findall(head):
                names.add("True" if tok == "«True»" else tok)
            i = k + 1
        else:
            i += 1
    return names


_BINDER_CLOSE_ALL = {")", "}", "]", "⦄", "⟩"}
_BINDER_TOKEN_RE = re.compile(_NAME)


# --- `True` scope model -----------------------------------------------------
# Lean resolves a bare `True` inside `namespace A.B` to `A.B.True`, then
# `A.True`, then the builtin: only a non-`protected` `True` declared in the
# current namespace or one of its prefixes shadows the builtin. A namespace's
# declarations stop applying at its `end`, and a `variable` binder at the end
# of its section/namespace. `open`/`export` of a namespace that declares `True`
# makes a bare `True` ambiguous (Lean rejects it), so it never shadows here.
# Anything the model cannot follow (unbalanced `end`, `True` introduced by
# `renaming`/`notation`/`macro`) fails closed: `True` is taken as the builtin.
_SCOPE_CMD_RE = re.compile(
    r"(?m)^[ \t]*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:public|private|noncomputable|meta)\s+)*"
    r"(namespace|section|mutual|end)" + _ID_END + r"[ \t]*(" + _NAME + r")?"
)
_TRUE_DECL_SCOPED_RE = re.compile(
    r"(?m)^[ \t]*(?:@\[[^\]]*\]\s*)*"
    r"((?:(?:public|private|protected|noncomputable|unsafe|partial|nonrec|meta)\s+)*)"
    r"(?:def|abbrev|theorem|lemma|axiom|opaque|constant|structure|class|inductive|instance)"
    + _ID_END + r"\s*((?:" + _COMP + r"\.)*)(?:True|«True»)(?![" + ID_REST + r".])"
)


def _components(name: str) -> list[str]:
    return [c for c in re.findall(_COMP, name)]


class TrueScopes:
    """Where, in one file, a bare `True` may not mean the builtin constant."""

    def __init__(self, live: str, quoted: list[tuple[int, int]] | None = None):
        quoted = quoted or []
        events: list[tuple[int, str, object]] = []
        for m in _SCOPE_CMD_RE.finditer(live):
            if not outside_quoted(m.start(), quoted):
                continue
            events.append((m.start(), m.group(1), m.group(2) or ""))
        for m in _TRUE_DECL_SCOPED_RE.finditer(live):
            if not outside_quoted(m.start(), quoted):
                continue
            events.append((m.start(), "true-decl", (m.group(1), m.group(2))))
        for m in _VARIABLE_RE.finditer(live):
            if not outside_quoted(m.start(), quoted):
                continue
            end = m.end()
            nxt = re.compile(r"\n(?=\S)|" + _ID_START + r"in" + _ID_END).search(live, end)
            seg = live[end: nxt.start() if nxt else len(live)]
            if "True" in binder_names(seg):
                one_shot = bool(nxt and live.startswith("in", nxt.start()))
                events.append((m.start(), "variable", nxt.end() if one_shot else None))
        events.sort(key=lambda e: e[0])
        self.ok = True
        self._live = live
        # (offset, namespace path, shadowing namespaces, variable scope ids alive)
        self.timeline: list[tuple[int, tuple[str, ...], frozenset, frozenset]] = []
        self.one_shot: list[int] = []  # `variable (True …) in`: next command only
        stack: list[tuple[str, list[str], int]] = []  # (kind, components, id)
        decls: set[tuple[str, ...]] = set()
        var_scopes: set[int] = set()
        next_id = 1

        def path() -> tuple[str, ...]:
            return tuple(c for kind, comps, _ in stack for c in comps)

        def snap(off: int) -> None:
            alive = {sid for _, _, sid in stack} | {0}
            self.timeline.append((off, path(), frozenset(decls),
                                  frozenset(var_scopes & alive)))

        snap(0)
        for off, kind, arg in events:
            if kind in ("namespace", "section", "mutual"):
                comps = _components(arg) if kind == "namespace" else []
                if kind == "namespace" and not comps:
                    self.ok = False
                stack.append((kind, comps, next_id))
                next_id += 1
            elif kind == "end":
                if not stack:
                    self.ok = False
                    continue
                top_kind, comps, sid = stack.pop()
                if top_kind == "namespace" and _components(arg) != comps:
                    self.ok = False
                var_scopes.discard(sid)
            elif kind == "true-decl":
                mods, prefix = arg
                if re.search(r"(?<![" + ID_REST + r"])protected(?![" + ID_REST + r"])", mods):
                    continue
                comps = _components(prefix)
                if comps[:1] == ["_root_"]:
                    full = tuple(comps[1:])
                else:
                    full = path() + tuple(comps)
                if full:  # a root `True` clashes with the builtin: Lean rejects it
                    decls.add(full)
            elif kind == "variable":
                if arg is not None:
                    self.one_shot.append(arg)
                else:
                    var_scopes.add(stack[-1][2] if stack else 0)
            snap(off)

    def shadowed_at(self, off: int) -> bool:
        """Can a bare `True` at command offset `off` resolve to a non-builtin?"""
        if not self.ok:
            return False  # cannot follow the scopes: fail closed (builtin)
        state = None
        for t in self.timeline:
            if t[0] <= off:
                state = t
            else:
                break
        _, cur, decls, vars_alive = state
        if vars_alive:
            return True
        if any(cur[:len(d)] == d for d in decls):
            return True
        # `variable (True : Prop) in` covers only the command right after `in`.
        return any(start <= off and not self._live[start:off].strip()
                   for start in self.one_shot)

def true_is_shadowed(binders: str, decl_start: int, scopes: TrueScopes) -> bool:
    """True if `True` in this declaration's statement is not the builtin."""
    return scopes.shadowed_at(decl_start) or "True" in binder_names(binders)


def find_true_placebos(text: str, res: LexResult) -> list[tuple[int, str]]:
    """Find `theorem`/`lemma` declarations whose statement type is exactly `True`.

    Returns a list of `(line, name)`. Comment/docstring characters are blanked
    first (newlines preserved, so line numbers stay accurate). For each
    declaration head we walk its signature tracking bracket depth, locate the
    top-level statement colon (binder colons live inside brackets) and the
    top-level `:=` that begins the proof, and flag it when the type between them
    is built only from `True` (see `is_vacuous_true`) and `True` is not rebound
    by a binder, `variable` or file-level declaration (see `true_is_shadowed`). Stopping at `:=` keeps in-proof `have … : True := …`
    steps from being mistaken for the declaration's statement.
    """
    live = code_text(text, res)
    scopes = TrueScopes(live, res.quoted)
    decls = [m for m in PLACEBO_DECL_RE.finditer(live)
             if outside_quoted(m.start(), res.quoted)]
    hits: list[tuple[int, str]] = []
    for idx, m in enumerate(decls):
        name = m.group(2)
        scan_end = decls[idx + 1].start() if idx + 1 < len(decls) else len(live)
        depth = 0
        stmt_colon = -1
        i = m.end()
        while i < scan_end:
            ch = live[i]
            if ch in _BRACKET_OPEN:
                depth += 1
            elif ch in _BRACKET_CLOSE:
                if depth:
                    depth -= 1
            elif depth == 0 and ch == ":":
                if i + 1 < scan_end and live[i + 1] == "=":
                    # Top-level `:=` — end of the signature, start of the proof.
                    if (stmt_colon != -1 and is_vacuous_true(live[stmt_colon + 1:i])
                            and not true_is_shadowed(live[m.end():stmt_colon], m.start(),
                                                     scopes)):
                        hits.append((live.count("\n", 0, m.start()) + 1, name))
                    break
                if stmt_colon == -1:
                    stmt_colon = i
            i += 1
    return hits


def main() -> int:
    files, full_arklib_scan, path_errors = scan_plan(sys.argv[1:])
    if path_errors:
        print("\n".join(path_errors), file=sys.stderr)
        return 1

    allowlist = load_allowlist(ALLOWLIST_PATH)
    failures: list[str] = []
    allowed_hits: list[str] = []
    seen_allowed: set[str] = set()
    allow_sites: dict[str, list[str]] = {}
    for path in files:
        text = path.read_text(encoding="utf-8", errors="replace")
        lexed = lex_lean(text)
        mask = lexed.mask
        for off in ambiguous_literals(text, lexed):
            line = text.count("\n", 0, off) + 1
            failures.append(
                f"{path}:{line}: string literal reads differently as a plain and as an "
                f"interpolated string, which changes what is a comment; the scan cannot "
                f"be trusted here, so rewrite the literal (e.g. escape `{{` as `\\{{`)"
            )
        live_text = code_text(text, lexed)
        for m in TOKEN_RE.finditer(text):
            if not mask[m.start()]:
                line = text.count("\n", 0, m.start()) + 1
                failures.append(f"{path}:{line}: forbidden token {m.group(1)}")
        for m in NATIVE_FORM_RE.finditer(live_text):
            if not outside_quoted(m.start(), lexed.quoted):
                continue
            line = text.count("\n", 0, m.start()) + 1
            form = " ".join(m.group(0).split())
            failures.append(f"{path}:{line}: forbidden native evaluation `{form}`")
        for m in META_DECL_RE.finditer(text):
            if not mask[m.start()]:
                line = text.count("\n", 0, m.start()) + 1
                failures.append(
                    f"{path}:{line}: forbidden metaprogram declaration `{m.group(0)}` "
                    f"(adds a kernel declaration, e.g. an axiom, without an `axiom` "
                    f"keyword; state residuals as `def ...Residual : Prop`)"
                )
        scopes = TrueScopes(live_text, lexed.quoted)
        for m in UNSAFE_DECL_RE.finditer(live_text):
            if not outside_quoted(m.start(), lexed.quoted):
                continue
            line = text.count("\n", 0, m.start()) + 1
            failures.append(
                f"{path}:{line}: forbidden unsafe declaration "
                f"(repository policy rejects live `unsafe` decls; prove in safe "
                f"Lean or track a residual — this precheck is not a kernel-escape claim)"
            )
        decls = declaration_heads(live_text, lexed)
        for decl_index, dm in enumerate(decls):
            kind, name = dm.group(1), dm.group(2)
            next_decl_start = decls[decl_index + 1].start() if decl_index + 1 < len(decls) else None
            if kind in OPAQUE_KINDS:
                limit = next_decl_start if next_decl_start is not None else len(live_text)
                if live_text.find(":=", dm.end(), limit) == -1:
                    line = text.count("\n", 0, dm.start()) + 1
                    failures.append(
                        f"{path}:{line}: bodyless {kind} declaration {name} introduces an "
                        f"unproven inhabitant of its statement type (axiom-equivalent "
                        f"laundering); provide a real ':=' proof/definition, or state the "
                        f"obligation as an explicit Prop or a tracked sorry"
                    )
                continue
            if kind in {"theorem", "lemma"}:
                continue
            if not is_residual_like(name, allowlist):
                continue
            end = declaration_header_end(live_text, dm.end(), next_decl_start)
            header = live_text[dm.end():end]
            result_type = top_level_result_type(header)
            if (result_type is not None and is_vacuous_true(result_type)
                    and not true_is_shadowed(header[:top_level_colon(header) or 0], dm.start(),
                                             scopes)):
                line = text.count("\n", 0, dm.start()) + 1
                failures.append(
                    f"{path}:{line}: obligation-like name {name} is declared as "
                    f"a vacuous {kind} of type True; keep real residual debt as an "
                    f"explicit axiom/Prop, or remove the allowlist entry"
                )
        for am_start, name in axiom_hits(live_text, lexed):
            idx = live_text.count("\n", 0, am_start) + 1
            if is_allowlisted(name, allowlist):
                final = simple_name(name)
                seen_allowed.add(final)
                allow_sites.setdefault(final, []).append(f"{path}:{idx}")
                allowed_hits.append(f"{path}:{idx}: allowed documented residual axiom {name}")
            else:
                failures.append(
                    f"{path}:{idx}: forbidden custom axiom declaration {name} "
                    f"(add to scripts/residual_axioms.txt only if it is a documented, "
                    f"tracked residual)"
                )

        for line_no, name in find_true_placebos(text, lexed):
            failures.append(
                f"{path}:{line_no}: forbidden vacuous placebo "
                f"`theorem/lemma {name} : True` proves nothing about the named "
                f"obligation (axiom-laundering pattern, #169/#171). Prove the real "
                f"statement or track it by its GitHub issue, not a `True` theorem."
            )

    for name, sites in sorted(allow_sites.items()):
        unique_sites = sorted(set(sites))
        if len(unique_sites) > 1:
            failures.append(
                f"{name}: allowlisted residual axiom declared {len(unique_sites)} times "
                f"({', '.join(unique_sites)}); one residual_axioms.txt entry documents "
                f"exactly one declaration, so a second declaration of the same simple name "
                f"(for example a clone inside a fresh namespace) re-uses the entry to launder "
                f"a new axiom. Remove the clone, or drop the entry if the documented axiom "
                f"itself is gone"
            )

    stale = sorted(allowlist - seen_allowed)
    if full_arklib_scan and stale:
        print(
            "WARNING: residual_axioms.txt entries match no live axiom (discharged? "
            "remove the line): " + ", ".join(stale),
            file=sys.stderr,
        )

    if failures:
        print("\n".join(failures), file=sys.stderr)
        print(f"\nFORBIDDEN: {len(failures)} laundering token(s) in live source", file=sys.stderr)
        return 1
    if allowed_hits:
        print("\n".join(allowed_hits))
    print(
        "forbidden-token precheck: clean (no native_decide / bv_decide / "
        "unsafe declaration / unsafeCast / implemented_by / "
        "undocumented custom axiom / vacuous `: True` placebo; "
        f"{len(allowed_hits)} allowlisted residual axiom(s))"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
