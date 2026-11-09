#!/usr/bin/env python3
"""Reject axiom-laundering tokens in live library and research source.

By default, scans every .lean file under ArkLib/, Research/, and ProximityPrize/.
Pass paths to scan particular Lean files or directories. Fails if live code
contains any of the following. Interpolation holes can contain live terms.
  - `native_decide` / `bv_decide` (kernel-bypassing decision procedures),
    `bv_check`, and `decide` configurations that enable native evaluation or
    whose native flag cannot be established as disabled. Use `-native` or a
    constructor spelling such as `.false` to disable it explicitly. The scan
    also rejects direct use of `Lean.ofReduceBool`, `Lean.ofReduceNat`,
    `Lean.trustCompiler`, `Lean.reduceBool`, and `Lean.reduceNat`, or
  - an `unsafe` declaration modifier, live `unsafeCast`, or `implemented_by`
    attribute (repository policy: block unsafe decls, unsafeCast, and
    evaluator-diverging `implemented_by`; this is a fast precheck, not a claim
    that Lean accepts unsafe theorems as axiom-clean proofs), or
  - a metaprogram that adds kernel declarations (`run_cmd` / `run_elab` /
    `run_meta`, `addDecl`, `addAndCompile`, `axiomDecl`), which can declare an
    axiom without the `axiom` keyword, or
  - a `#exit` command. Lean stops elaborating the file there, so nothing after
    it is checked or even declared, while text-based gates still read it: the
    residual census counts an unelaborated `theorem foo_holds : FooResidual`
    after `#exit` as a discharge, or
  - a custom `axiom` declaration that is not a reviewed residual pinned in
    scripts/residual_axioms.txt, with any modifiers (including `public`/`meta`
    in `module` files), with the name on a later line or after a comment, and
    with any Lean name form (Unicode, `«quoted»`, qualified, `_root_.`).
    Each manifest entry pins ONE declaration by its fully qualified name, its
    defining file and a digest of its reviewed signature (the text after the
    name, comments dropped, plus the in-scope `variable`/`universe`/`open`/
    `export`/`include`/`omit` commands, which change its elaborated type).
    A copy under another namespace, a move to another file, or any change to
    the statement or that context fails until the manifest entry is updated in
    a reviewed change (`--print-residual-manifest` prints the current pins).
    Pinning a residual records a documented assumption; it proves nothing, or
  - an `axiom` keyword followed by an antiquotation (`axiom $n` in a syntax
    quotation), which lets a macro declare an axiom under any name, or
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
  - a Lean debug option that disables the kernel check or replaces proofs
    with `sorryAx` without any `sorry` token in the source:
    `debug.skipKernelTC` (`set_option debug.skipKernelTC true in theorem t :
    1 = 2 := by <tactic assigning True.intro>` elaborates and `#print axioms t`
    reports *no axioms at all*), `debug.byAsSorry`, `debug.proofAsSorry` and
    `debug.terminalTacticsAsSorry` (the proof becomes `sorryAx` with only a
    warning, so `sorry_census.py` sees no hole). The option names are matched
    as bare identifier components in comment-stripped source, with string and
    char literals kept live because a metaprogram can build the option name
    from `"skipKernelTC"` and set it on the command scope. `«debug».«skipKernelTC»`
    is the same option and is matched too. The full-tree scan also rejects the
    names in `lakefile.toml` (`[leanOptions]` applies them to every `lake
    build`, and the flagship axiom audit reads the resulting oleans). A name
    assembled from string pieces (`"skipKernel" ++ "TC"`) or a `-D` flag passed directly to Lean
    is outside this scan.

Comment and docstring occurrences are ignored. Lexing is shared with
scripts/sorry_census.py and scripts/check-research-boundary.py
(scripts/lean_lexer.py): comments (including doc comments, whose body starts
after `/--`), string/raw-string/char literals, interpolation holes, quoted
identifiers, identifiers and numbers are lexed together with Lean's own
identifier characters (`αbad`, `ébad`, `𝔽bad` are names). Whether a `"…"`
is plain or interpolated depends on its consumer, so every combination of
readings of the ambiguous literals is lexed; if the readings disagree about
comments, quoted identifiers or declarations, the check fails rather than
guessing. `sorry`/`admit` are handled separately by
scripts/sorry_census.py --fail-on-holes; this precheck runs before any Lean
toolchain is set up, so CI fails fast on laundering attempts.

This is a lexical precheck, not an elaborated declaration or axiom audit: a
macro or elaborator that builds a declaration without the `axiom` keyword in
the source is not visible to it. The post-build `scripts/axiom_audit.py`
checks the flagship declarations' axiom dependencies and lists, from Lean's
environment metadata, every axiom of the `ArkLib`/`Research` modules it
imports, each of which must be a pin of this manifest.
"""

from __future__ import annotations

import argparse
import bisect
import hashlib
import re
import json
import re
import subprocess
import sys
import tomllib
from pathlib import Path
from typing import NamedTuple

import lean_lexer
from lean_lexer import COMMENT, CODE, ID_FIRST, ID_REST, Reading

# Native reduction primitives can be called directly without a tactic spelling.
TOKEN_RE = re.compile(
    r"\b(native_decide|bv_decide|unsafeCast|implemented_by"
    r"|ofReduceBool|ofReduceNat|trustCompiler|reduceBool|reduceNat)\b"
)
# Meta code can add a kernel declaration without the `axiom` keyword, e.g.
# `run_cmd liftCoreM <| addDecl (.axiomDecl { name := `w, type := mkConst ``False, .. })`.
# ArkLib/Research proofs never need to add declarations from metaprograms.
# `run_tac` (tactic) and `by_elab` (term) run the same inline metaprograms inside a
# proof and can close a goal with `sorryAx` built from a string name, which no
# `sorry` token reveals.
META_DECL_RE = re.compile(
    r"(?<![\w.'])(run_cmd|run_elab|run_meta|run_tac|by_elab)\b"
    r"|\b(add(?:Decl\w*|AndCompile)|axiomDecl)\b"
)
# `#exit` ends elaboration of the file: later text is never checked or declared,
# but text-based gates (residual_census.py, sorry_census.py) still read it. `#` is
# not an identifier character and Lean's tokenizer takes the longest token with
# no boundary check, so `rfl#exit` and `#exit_foo` also start a real `#exit`;
# match the bare text.
EXIT_RE = re.compile(r"#exit")
# Lean declaration-modifier `unsafe` (not aesop's `(add unsafe …)` tactic hint).
# `unsafe` is matched as a keyword wherever it appears, like the `axiom`
# check below: Lean's command parser does not care about line breaks, so a
# line-anchored match missed `open Foo in unsafe def …`, `set_option … in
# unsafe def …`, `omit […] in unsafe def …`, `mutual unsafe def …` and
# mid-line `… unsafe def …` forms. Allow the same modifiers after `unsafe`
# (Lean accepts e.g. `unsafe nonrec def`), then require a declaration
# keyword so `aesop (add unsafe …)` and `attribute [aesop unsafe 50%]`
# stay allowed.


# --- Lean identifier characters ---------------------------------------------
# Shared with the lexer (scripts/lean_lexer.py), which mirrors Lean's
# `isIdFirst`/`isIdRest`: e.g. `ébad`, `αbad` and `𝔽bad` are identifiers.
# One name component (a plain identifier or a guillemet-quoted `«…»` one), the
# token-start / token-end guards, and a possibly qualified declaration name.
_COMP = lean_lexer.COMP
_ID_START = lean_lexer.ID_START
_ID_END = lean_lexer.ID_END
_NAME = lean_lexer.NAME
UNSAFE_DECL_RE = re.compile(
    _ID_START + r"unsafe" + _ID_END + r"\s+"
    r"(?:(?:public|protected|private|scoped|noncomputable|partial|nonrec|meta|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev|opaque|constant|axiom|instance|structure|inductive|class|example)\b"
)

_ID_FIRST_RE = re.compile("[" + ID_FIRST + "]")
_ID_REST_RE = re.compile("[" + ID_REST + "]")
# `native_decide` is `decide +native` (`Init/Tactics.lean`, `DecideConfig.native`).
# `elabConfig` elaborates each optConfig item and evaluates the term, so
# `(native := (true))` and `(native := flag)` are not the two-character word
# `true`. A `[^)]*` scan also stops at the first nested `)`, which drops a
# later `+native`. Items apply left to right; `(config := {…})` replaces the
# config (a fresh literal's omitted `native` is the default `false`), while
# `{cfg with …}` / `{..cfg}` keep `native` unless this literal sets it.
_DECIDE_RE = re.compile(_ID_START + r"\.?decide" + _ID_END)
_BV_CHECK_RE = re.compile(_ID_START + r"\.?bv_check" + _ID_END)
_CFG_OPEN = {"(": ")", "{": "}", "[": "]", "⟨": "⟩"}
_CFG_CLOSE = {close: open_ for open_, close in _CFG_OPEN.items()}


def _skip_ws(text: str, i: int, end: int) -> int:
    while i < end and text[i].isspace():
        i += 1
    return i


def _read_ident(text: str, i: int, end: int) -> tuple[str | None, int]:
    if i >= end:
        return None, i
    if text[i] == "«":
        j = text.find("»", i + 1, end)
        if j < 0:
            return None, i
        return text[i : j + 1], j + 1
    if _ID_FIRST_RE.fullmatch(text[i]) is None:
        return None, i
    j = i + 1
    while j < end and _ID_REST_RE.fullmatch(text[j]):
        j += 1
    return text[i:j], j


def _bare_name(name: str) -> str:
    if name.startswith("«") and name.endswith("»"):
        return name[1:-1]
    return name


def _match_bracket(text: str, open_i: int, end: int) -> int | None:
    close_for = _CFG_OPEN.get(text[open_i])
    if close_for is None:
        return None
    depth = 0
    i = open_i
    while i < end:
        if text[i] == "«":
            j = text.find("»", i + 1, end)
            if j < 0:
                return None
            i = j + 1
            continue
        ch = text[i]
        if ch in _CFG_OPEN:
            depth += 1
        elif ch in _CFG_CLOSE:
            depth -= 1
            if depth == 0 and ch == close_for:
                return i
            if depth < 0:
                return None
        i += 1
    return None


def _term_end(text: str, i: int, end: int) -> int:
    """End of a config term: a top-level comma or closing bracket, or `end`."""
    depth = 0
    while i < end:
        if text[i] == "«":
            j = text.find("»", i + 1, end)
            if j < 0:
                return end
            i = j + 1
            continue
        ch = text[i]
        if ch in _CFG_OPEN:
            depth += 1
        elif ch in _CFG_CLOSE:
            if depth == 0:
                return i
            depth -= 1
        elif depth == 0 and ch == ",":
            return i
        i += 1
    return end


def _as_bool(text: str, start: int, end: int) -> bool | None:
    """A Bool constructor independent of namespace lookup, with parentheses."""
    i = _skip_ws(text, start, end)
    if i >= end:
        return None
    if text[i] == "(":
        close = _match_bracket(text, i, end)
        if close is None or _skip_ws(text, close + 1, end) != end:
            return None
        return _as_bool(text, i + 1, close)
    # An unqualified name can resolve to a definition in the current
    # namespace. These two constructor spellings do not use that lookup.
    value = text[i:end].rstrip()
    if value in {".false", "_root_.Bool.false"}:
        return False
    if value in {".true", "_root_.Bool.true"}:
        return True
    return None


def _struct_native(text: str, start: int, end: int) -> bool | None:
    """`native` in a structure literal. None means the value is not visible.

    An explicit literal wins over `{cfg with …}` / `{..cfg}`. A missing field on
    a fresh literal is the default `false`.
    """
    explicit: bool | None = None
    saw_explicit = False
    unknown = False
    inherited = False
    i = start
    while True:
        i = _skip_ws(text, i, end)
        if i >= end:
            break
        if text.startswith("..", i):
            inherited = True
            i = _term_end(text, i + 2, end)
            if i < end and text[i] == ",":
                i += 1
            continue
        name, j = _read_ident(text, i, end)
        if name is None:
            return None
        j = _skip_ws(text, j, end)
        if (
            j + 4 <= end
            and text.startswith("with", j)
            and (j + 4 == end or _ID_REST_RE.fullmatch(text[j + 4]) is None)
        ):
            inherited = True
            i = j + 4
            continue
        if text.startswith(":=", j):
            val_end = _term_end(text, j + 2, end)
            if _bare_name(name) == "native":
                saw_explicit = True
                explicit = _as_bool(text, j + 2, val_end)
                unknown = explicit is None
            i = val_end
            if i < end and text[i] == ",":
                i += 1
            continue
        return None
    if unknown:
        return None
    if saw_explicit:
        return explicit
    if inherited:
        return None
    return False


def _config_native(text: str, start: int, end: int) -> bool | None:
    """Native bit of a `(config := term)` value, or None if it is not a literal."""
    i = _skip_ws(text, start, end)
    while i < end and text[i] == "(":
        close = _match_bracket(text, i, end)
        if close is None or _skip_ws(text, close + 1, end) != end:
            return None
        start, end = i + 1, close
        i = _skip_ws(text, start, end)
    if i >= end or text[i] != "{":
        return None
    close = _match_bracket(text, i, end)
    if close is None or _skip_ws(text, close + 1, end) != end:
        return None
    return _struct_native(text, i + 1, close)


def _decide_native(text: str, i: int) -> tuple[bool, int]:
    """Whether the optConfig at `i` leaves `DecideConfig.native` true, and where it ends.

    Unknown values fail closed: `elabConfig` evaluates the term, and only a
    verified false constructor is known to disable native evaluation. `(config := {…})` replaces earlier items.
    """
    enabled = False
    end = len(text)
    while True:
        i = _skip_ws(text, i, end)
        if i >= end:
            return enabled, i
        if (
            text[i] in "+-"
            and i + 1 < end
            and not text[i + 1].isspace()
            and (_ID_FIRST_RE.fullmatch(text[i + 1]) is not None or text[i + 1] == "«")
        ):
            name, j = _read_ident(text, i + 1, end)
            if name is None:
                return enabled, i
            if _bare_name(name) == "native":
                enabled = text[i] == "+"
            i = j
            continue
        if text[i] == "(":
            j = _skip_ws(text, i + 1, end)
            name, k = _read_ident(text, j, end)
            k2 = _skip_ws(text, k, end)
            if name is not None and text.startswith(":=", k2):
                close = _match_bracket(text, i, end)
                if close is None:
                    return enabled, i
                bare = _bare_name(name)
                if bare == "native":
                    flag = _as_bool(text, k2 + 2, close)
                    enabled = True if flag is None else flag
                elif bare == "config":
                    flag = _config_native(text, k2 + 2, close)
                    enabled = True if flag is None else flag
                i = close + 1
                continue
        return enabled, i


def native_eval_hits(live: str, quoted: list[tuple[int, int]]) -> list[tuple[int, str]]:
    """`(offset, form)` for `bv_check` and `decide` configs that enable `native`."""
    hits: list[tuple[int, str]] = []
    for m in _BV_CHECK_RE.finditer(live):
        if outside_quoted(m.start(), quoted):
            hits.append((m.start(), "bv_check"))
    for m in _DECIDE_RE.finditer(live):
        if not outside_quoted(m.start(), quoted):
            continue
        enabled, stop = _decide_native(live, m.end())
        if enabled:
            hits.append((m.start(), " ".join(live[m.start() : stop].split())))
    return hits


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
# A syntax quotation can splice the declared name in with an antiquotation:
# `macro "launder " n:ident : command => `(axiom $n : False)` followed by
# `launder w` declares the axiom `w`, and `$(mkIdent `w)` does the same without
# a macro argument. `AXIOM_RE` needs a literal name after the keyword, so a live
# `axiom` keyword followed by `$` is rejected on its own: the real name is only
# known after elaboration, so it can never be matched against the allowlist.
AXIOM_ANTIQUOT_RE = re.compile(_ID_START + r"axiom" + _ID_END + r"\s*\$")
# Text inside a guillemet-quoted identifier (`«an axiom counterfeit'»`) is part
# of a name, not a command, so an `axiom` match that starts inside one is not a
# declaration. Quoted-identifier spans come from the shared lexer, which also
# lexes string, raw-string and char literals, so a `«` inside a literal (`"«"`,
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
REPO_ROOT = Path(__file__).resolve().parents[1]


class InheritedSourcePolicy:
    """Recognize only explicitly reviewed, byte-identical upstream True stubs.

    This never exempts a file or any native/custom-axiom violation. A changed file,
    copied declaration, changed violation kind, or changed upstream inventory makes
    the original source-policy error live again. The named revision's Git blob is
    checked as well as the current bytes, so editing the JSON digest cannot create
    an exception for a new stub.
    """

    def __init__(self, root: Path = REPO_ROOT):
        self.root = root.resolve()
        baseline = self.root / "scripts/upstream-source-policy.json"
        inventory = self.root / "scripts/arklib-upstream.json"
        self.data = json.loads(baseline.read_text()) if baseline.is_file() else {}
        self.inventory = json.loads(inventory.read_text()) if inventory.is_file() else {}
        self.blob_hashes: dict[str, str | None] = {}
        self.blob_contents: dict[str, bytes | None] = {}

    def allows(self, path: Path, declaration: str, kind: str) -> bool:
        if kind != "vacuous_true_theorem":
            return False
        try:
            relative = path.resolve().relative_to(self.root).as_posix()
        except ValueError:
            return False
        matching = [entry for entry in self.data.get("exceptions", [])
                    if entry.get("file") == relative
                    and entry.get("declaration") == declaration
                    and entry.get("kind") == kind]
        return any(self.matches_upstream_file(path, entry.get("sha256"),
                                             self.data.get("revision"),
                                             self.data.get("repository"))
                   for entry in matching)

    def matches_upstream_file(self, path: Path, digest: str | None,
                              revision: str | None, repository: str | None) -> bool:
        """Check provenance and exact bytes; used by the inherited sorry baseline too."""
        try:
            relative = path.resolve().relative_to(self.root).as_posix()
        except ValueError:
            return False
        if (not revision or revision != self.inventory.get("revision")
                or repository != "https://github.com/Verified-zkEVM/ArkLib"
                or repository != self.inventory.get("repository")
                or relative not in self.inventory.get("files", []) or not path.is_file()):
            return False
        current_hash = hashlib.sha256(path.read_bytes()).hexdigest()
        self._load_upstream_blob(relative, revision)
        return digest == current_hash == self.blob_hashes[relative]

    def _load_upstream_blob(self, relative: str, revision: str) -> bytes | None:
        if relative not in self.blob_contents:
            result = subprocess.run(["git", "show", f"{revision}:{relative}"], cwd=self.root,
                                    capture_output=True)
            self.blob_contents[relative] = result.stdout if result.returncode == 0 else None
            self.blob_hashes[relative] = (hashlib.sha256(result.stdout).hexdigest()
                                          if result.returncode == 0 else None)
        return self.blob_contents[relative]

    def matches_adapted_upstream_hole(self, path: Path, row: dict, entry: dict,
                                     revision: str | None, repository: str | None) -> bool:
        """Accept only an unchanged admitted command inside a reviewed adaptation.

        Whole-file matching remains mandatory for True-stub exceptions. This
        separate path is used only for sorry-census tokens, and checks each token's
        position so a later command cannot reuse its predecessor's census label.
        """
        try:
            relative = path.resolve().relative_to(self.root).as_posix()
        except ValueError:
            return False
        if (not revision or revision != self.inventory.get("revision")
                or repository != "https://github.com/Verified-zkEVM/ArkLib"
                or repository != self.inventory.get("repository")
                or relative not in self.inventory.get("files", [])
                or relative != row.get("file") or relative != entry.get("file")
                or row.get("decl") != entry.get("decl") or row.get("kind") != "hole"
                or not path.is_file()):
            return False
        adaptations = [item for item in self.inventory.get("downstream_adaptations", [])
                       if item.get("path") == relative]
        if len(adaptations) != 1:
            return False
        adapted = adaptations[0]
        current_bytes = path.read_bytes()
        upstream_bytes = self._load_upstream_blob(relative, revision)
        if (upstream_bytes is None or entry.get("sha256") != self.blob_hashes[relative]
                or hashlib.sha256(current_bytes).hexdigest() != adapted.get("sha256")
                or not adapted.get("declarations") or not adapted.get("source_revision")
                or not adapted.get("reason")):
            return False
        upstream_blob = hashlib.sha1(b"blob " + str(len(upstream_bytes)).encode() + b"\0"
                                     + upstream_bytes).hexdigest()
        if upstream_blob != adapted.get("upstream_blob"):
            return False
        # The reviewed declaration identity must be unambiguous in both source
        # versions. The strict parser rejects uncertain command boundaries.
        from integration.extract_downstream_extensions import parse_commands
        try:
            current = current_bytes.decode("utf-8")
            upstream = upstream_bytes.decode("utf-8")
            def matching(text: str):
                return [command for command in parse_commands(text)
                        if command.full_name == entry.get("declaration")
                        and f"{command.kind} {command.name}" == entry.get("decl")]
            old_commands, new_commands = matching(upstream), matching(current)
        except (UnicodeError, ValueError):
            return False
        if len(old_commands) != 1 or len(new_commands) != 1:
            return False
        old, new = old_commands[0], new_commands[0]
        def digest(text: str, command) -> str:
            return hashlib.sha256(text[command.start:command.end].strip().encode()).hexdigest()
        if not entry.get("command_sha256") == digest(upstream, old) == digest(current, new):
            return False
        offset = row.get("offset")
        token = row.get("token")
        return (isinstance(offset, int) and isinstance(token, str)
                and new.start <= offset < new.end
                and current[offset:offset + len(token)] == token)

# Lean debug options that defeat the proof gates without a `sorry`/`axiom` token
# (Lean v4.30.0-rc2): `debug.skipKernelTC` (src/Lean/Environment.lean) adds the
# declaration with `addDeclWithoutChecking`, so an elaborator-level assignment
# such as `mvarId.assign (mkConst ``True.intro)` proves `1 = 2` and `#print
# axioms` reports nothing; `debug.byAsSorry` (src/Lean/Elab/Term/TermElabM.lean),
# `debug.proofAsSorry` (src/Lean/Elab/MutualDef.lean) and
# `debug.terminalTacticsAsSorry` (src/Lean/Meta/Tactic/Util.lean) replace the
# proof, the `by` block or the terminal tactic with `sorryAx`. The final name
# component is distinctive, so it is matched on its own with Lean identifier
# boundaries: that covers `set_option debug.skipKernelTC true [in]`, the
# term-level `set_option … in`, the quoted `«debug».«skipKernelTC»`, a name
# literal `` `debug.skipKernelTC `` and a string component `"skipKernelTC"`
# passed to `Options.setBool`. No live source in this repository mentions any of
# them.
DEBUG_OPTION_NAMES = ("skipKernelTC", "byAsSorry", "proofAsSorry", "terminalTacticsAsSorry")
DEBUG_OPTION_RE = re.compile(
    "(?<![" + ID_REST + "])(" + "|".join(DEBUG_OPTION_NAMES) + ")(?![" + ID_REST + "])"
)
LAKEFILE_NAME = "lakefile.toml"

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


class Pin(NamedTuple):
    """One reviewed residual axiom: exactly one declaration, pinned three ways."""

    fqn: str      # fully qualified name (canonical spelling, see `canonical_name`)
    file: str     # defining file, relative to the repository root (POSIX)
    digest: str   # `sha256:` digest of the reviewed signature (`signature_digest`)
    note: str     # the entry's trailing comment (tracking issue, short note)
    line: int     # line number in the manifest


# `<fully qualified name>  <defining file>  sha256:<64 hex>  # note`
_MANIFEST_RE = re.compile(
    r"[ \t]*(" + _NAME + r")[ \t]+(\S+)[ \t]+(sha256:[0-9a-f]{64})[ \t]*(?:#[ \t]*(.*))?\Z"
)


def canonical_name(name: str) -> str:
    """`name` with redundant guillemets dropped (`«foo».bar` is `foo.bar`)."""
    return ".".join(c[1:-1] if c.startswith("«") and re.fullmatch(
        "[" + ID_FIRST + "][" + ID_REST + "]*", c[1:-1]) else c for c in _components(name))


def load_manifest(path: Path) -> tuple[dict[str, Pin], list[str]]:
    """Reviewed residual-axiom pins by fully qualified name, and format errors."""
    pins: dict[str, Pin] = {}
    errors: list[str] = []
    if not path.exists():
        return pins, errors
    for number, raw in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        stripped = raw.strip()
        if not stripped or stripped.startswith("#"):
            continue
        m = _MANIFEST_RE.match(raw)
        if not m:
            errors.append(
                f"{path}:{number}: malformed residual-axiom entry {stripped!r}; expected "
                f"`<fully qualified name>  <defining file>  sha256:<digest>  # note` "
                f"(python3 scripts/forbidden_tokens.py --print-residual-manifest prints "
                f"the current pins)"
            )
            continue
        fqn = canonical_name(m.group(1))
        if fqn in pins:
            errors.append(f"{path}:{number}: residual axiom {fqn} is pinned twice "
                          f"(also line {pins[fqn].line}); one entry documents one declaration")
            continue
        pins[fqn] = Pin(fqn, m.group(2), m.group(3), (m.group(4) or "").strip(), number)
    return pins, errors


def scan_plan(args: list[str]) -> tuple[list[Path], bool, list[str]]:
    """Return files to scan, whether this is a full-ArkLib scan, and path errors."""
    if not args:
        return sorted(f for name in ("ArkLib", "Research", "ProximityPrize") for f in Path(name).rglob("*.lean")), True, []

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
            elif path.name != LAKEFILE_NAME:  # a lakefile is scanned by `lakefile_paths`
                errors.append(f"{path}: expected a .lean file")
            continue

        nested_arklib = path / "ArkLib"
        if nested_arklib.is_dir():
            files.update(nested_arklib.rglob("*.lean"))
            files.update((path / "Research").rglob("*.lean"))
            files.update((path / "ProximityPrize").rglob("*.lean"))
            full_arklib_scan = True
        else:
            files.update(path.rglob("*.lean"))
            if path.resolve() == arklib_root:
                full_arklib_scan = True

    return sorted(files), full_arklib_scan, errors


def lakefile_paths(args: list[str]) -> list[Path]:
    """Lakefiles to scan for debug options: the checkout root's on a full scan,
    the root of any directory argument that contains `ArkLib/`, and any
    `lakefile.toml` named explicitly."""
    roots = [Path(".")] if not args else []
    for raw in args:
        path = Path(raw)
        if path.is_file() and path.name == LAKEFILE_NAME:
            roots.append(path.parent)
        elif path.is_dir() and (path / "ArkLib").is_dir():
            roots.append(path)
    found = {root / LAKEFILE_NAME for root in roots if (root / LAKEFILE_NAME).is_file()}
    return sorted(found)


def lakefile_debug_option_hits(text: str) -> list[tuple[str, str]]:
    """Find debug option names in decoded TOML keys and string values."""
    hits: list[tuple[str, str]] = []

    def scan_string(value: str, location: str) -> None:
        hits.extend((location, match.group(1)) for match in DEBUG_OPTION_RE.finditer(value))

    def scan(value: object, location: str) -> None:
        if isinstance(value, dict):
            for key, child in value.items():
                child_location = f"{location}.{key}" if location else key
                scan_string(key, child_location)
                scan(child, child_location)
        elif isinstance(value, list):
            for index, child in enumerate(value):
                scan(child, f"{location}[{index}]")
        elif isinstance(value, str):
            scan_string(value, location)

    scan(tomllib.loads(text), "")
    return hits


# --- Lean lexing ------------------------------------------------------------
# Comments, string literals, raw strings, char literals, quoted identifiers,
# identifiers and numbers are lexed together by scripts/lean_lexer.py, shared
# with scripts/sorry_census.py and scripts/check-research-boundary.py: `"/-"`
# or `'«'` is a literal, `«a -- b»` or `«x'»` is one identifier, and `/--/ "`
# is still inside a doc comment. `lean_lexer.explore` returns every reading of
# the file's ambiguous plain/interpolated literals; readings[0] follows the
# syntactic guess. Command checks run on `Reading.code_text()` (comments and
# top-level literals blanked); token checks run on the text that is code in
# some reading, which keeps interpolation holes (`s!"{by decide +native}"`).


def outside_quoted(offset: int, quoted: list[tuple[int, int]]) -> bool:
    """Command heads cannot start inside a guillemet identifier.

    `quoted` is sorted and its spans do not overlap (lexer order).
    """
    i = bisect.bisect_right(quoted, (offset, sys.maxsize)) - 1
    return i < 0 or not quoted[i][0] <= offset < quoted[i][1]


def declaration_heads(code: str, reading: Reading) -> list[re.Match]:
    """Live declaration heads in source order (`DECL_RE` and `CONSTANT_DECL_RE`)."""
    heads = [m for rx in (DECL_RE, CONSTANT_DECL_RE) for m in rx.finditer(code)
             if outside_quoted(m.start(), reading.quoted)]
    return sorted(heads, key=lambda m: m.start())


def axiom_hits(code: str, reading: Reading) -> list[re.Match]:
    """Live `axiom` declarations (`AXIOM_RE` matches; group 1 is the name)."""
    return [m for m in AXIOM_RE.finditer(code) if outside_quoted(m.start(), reading.quoted)]


def antiquoted_axiom_hits(code: str, reading: Reading) -> list[int]:
    """Find syntax quotations whose axiom name comes from an antiquotation."""
    return [m.start() for m in AXIOM_ANTIQUOT_RE.finditer(code)
            if outside_quoted(m.start(), reading.quoted)]


def exit_hits(code: str, reading: Reading) -> list[int]:
    """Offsets of live `#exit` commands."""
    return [m.start() for m in EXIT_RE.finditer(code) if outside_quoted(m.start(), reading.quoted)]


def command_view(reading: Reading, code: str | None = None) -> tuple:
    """What the checks see under one reading: axiom, declaration, placebo and exit hits."""
    code = reading.code_text() if code is None else code
    return ([(m.start(), m.group(1)) for m in axiom_hits(code, reading)],
            [(m.start(), m.group(1), m.group(2)) for m in declaration_heads(code, reading)],
            find_true_placebos(reading, code),
            exit_hits(code, reading),
            antiquoted_axiom_hits(code, reading))


def disagreeing_readings(readings: list[Reading], base_code: str) -> list[Reading]:
    """Readings whose comments, quoted identifiers or commands differ from readings[0].

    Whether `"…{…}…"` is a plain or an interpolated string depends on the
    parser (any macro may take `interpolatedStr(term)`). If another reading of
    the ambiguous literals changes which characters are comments or quoted
    identifiers, or which declarations exist, the scan cannot be trusted.
    """
    base = readings[0]
    view = (base.comment_mask(), base.quoted, command_view(base, base_code))
    return [r for r in readings[1:] if (r.comment_mask(), r.quoted, command_view(r)) != view]


def comment_mask(text: str) -> bytes:
    """Per-character mask: 1 if the character is inside a comment or docstring."""
    return lean_lexer.lex(text).comment_mask()


# --- Residual-axiom pins ------------------------------------------------------
# A residual axiom is pinned by its fully qualified name, its defining file and a
# digest of its reviewed signature. Namespaces follow `namespace`/`section`/
# `mutual`/`end` (keywords, so matched anywhere, not only at a line start).
_SCOPE_RE = re.compile(_ID_START + r"(namespace|section|mutual|end)" + _ID_END)
_LINE_NAME_RE = re.compile(r"[ \t]*(" + _NAME + r")")
_NEXT_NAME_RE = re.compile(r"\s*(" + _NAME + r")")
# Commands that change how an axiom's statement elaborates without changing its
# text: section variables (and which of them are included), universes, and the
# namespaces opened for name resolution.
_CONTEXT_RE = re.compile(_ID_START + r"(variable|universe|open|export|include|omit)" + _ID_END)
# Tokens that only ever start a command (never occur inside a term), so the
# signature of a bodyless `axiom` ends at the first one after its name. `open`
# and `set_option` are left out because `open X in t` and `set_option o v in t`
# are also terms; `unsafe`/`meta` are left out for the same caution (a
# declaration keyword, which is listed, always follows them as modifiers).
_COMMAND_KEYWORDS = (
    "axiom|theorem|lemma|def|abbrev|opaque|instance|example|structure|class|inductive"
    "|coinductive|mutual|namespace|section|end|private|protected|noncomputable|partial"
    "|nonrec|public|variable|universe|attribute|export|include|omit|notation|infix"
    "|infixl|infixr|prefix|postfix|macro|macro_rules|syntax|elab|elab_rules"
    "|declare_syntax_cat|initialize|builtin_initialize|deriving|add_decl_doc"
)
_HASH_COMMAND = r"|@\[|" + _ID_START + r"#[A-Za-z_]"
_DECL_END_RE = re.compile(_ID_START + r"(?:" + _COMMAND_KEYWORDS + r")" + _ID_END + _HASH_COMMAND)
_CONTEXT_END_RE = re.compile(
    _ID_START + r"(?:" + _COMMAND_KEYWORDS + r"|open|set_option)" + _ID_END + _HASH_COMMAND)
_IN_SUFFIX_RE = re.compile(_ID_START + r"in\Z")


class AxiomSite(NamedTuple):
    start: int          # offset of the `axiom` keyword
    name: str           # the declared name as written
    fqn: str | None     # fully qualified name; None if the scopes cannot be followed
    digest: str         # `signature_digest` of the declaration in its context


def normalized_source(reading: Reading, start: int, stop: int) -> str:
    """Source in `[start, stop)` with comments dropped and code whitespace collapsed.

    Literal text (strings, chars) is kept verbatim.
    """
    text, kind = reading.text, reading.kind
    out: list[str] = []
    space = False
    for i in range(start, stop):
        ch, k = text[i], kind[i]
        if k == COMMENT or (k == CODE and ch.isspace()):
            space = True
            continue
        if space and out:
            out.append(" ")
        space = False
        out.append(ch)
    return "".join(out)


def signature_digest(signature: str, context: list[str]) -> str:
    """Digest of an axiom's normalized signature and in-scope context commands."""
    payload = "".join(f"context {c}\n" for c in context) + f"signature {signature}\n"
    return "sha256:" + hashlib.sha256(payload.encode("utf-8")).hexdigest()


def axiom_sites(reading: Reading, code: str) -> list[AxiomSite]:
    """Every live `axiom` with its fully qualified name and signature digest.

    The signature is the text after the declared name up to the next command
    (binders, universe parameters and type). Its context is every in-scope
    `variable`/`universe`/`open`/`export`/`include`/`omit` command, each
    normalized, outermost scope first; a `… in` form counts only for the
    declaration right after it. An unbalanced or mismatched `end` makes every
    later name unknown (`fqn` None), so the pin check fails closed.
    """
    axioms = axiom_hits(code, reading)
    if not axioms:
        return []
    quoted = reading.quoted
    events = [(m.start(), 0, m) for m in _SCOPE_RE.finditer(code)
              if outside_quoted(m.start(), quoted)]
    events += [(m.start(), 1, m) for m in _CONTEXT_RE.finditer(code)
               if outside_quoted(m.start(), quoted)]
    events += [(m.start(), 2, m) for m in axioms]
    events.sort(key=lambda e: e[0])
    heads = [h.start() for h in declaration_heads(code, reading)]
    # Scope stack entries: [kind, name component or None, context commands].
    stack: list[list] = []
    file_context: list[str] = []
    once: list[tuple[int, str]] = []
    ok = True
    sites: list[AxiomSite] = []
    for off, tag, m in events:
        if tag == 0:
            keyword = m.group(1)
            if keyword == "namespace":
                name = _NEXT_NAME_RE.match(code, m.end())
                if not name:
                    ok = False
                    continue
                stack += [["namespace", canonical_name(c), []] for c in _components(name.group(1))]
            elif keyword == "mutual":
                stack.append(["mutual", None, []])
            else:
                name = _LINE_NAME_RE.match(code, m.end())
                comps = ([canonical_name(c) for c in _components(name.group(1))]
                         if name else [None])
                if keyword == "section":
                    stack += [["section", c, []] for c in comps]
                    continue
                for comp in reversed(comps):  # `end A.B` closes `B`, then `A`
                    if not stack or stack[-1][1] != comp:
                        ok = False
                        break
                    stack.pop()
        elif tag == 1:
            stop = _CONTEXT_END_RE.search(code, m.end())
            body = normalized_source(reading, m.start(), stop.start() if stop else len(code))
            if _IN_SUFFIX_RE.search(body):
                once.append((off, body))
            else:
                (stack[-1][2] if stack else file_context).append(body)
        else:
            comps = [canonical_name(c) for c in _components(m.group(1))]
            if comps[0] == "_root_":
                comps = comps[1:]
            else:
                comps = [e[1] for e in stack if e[0] == "namespace"] + comps
            context = file_context + [c for e in stack for c in e[2]]
            context += [body for at, body in once
                        if not any(at < h < off for h in heads)]
            stop = _DECL_END_RE.search(code, m.end())
            signature = normalized_source(reading, m.end(), stop.start() if stop else len(code))
            sites.append(AxiomSite(off, m.group(1), ".".join(comps) if ok else None,
                                   signature_digest(signature, context)))
    return sites


def repo_path(path: Path, root: Path) -> str:
    """`path` relative to `root` (POSIX), or its absolute path outside `root`."""
    resolved = path.resolve()
    try:
        return resolved.relative_to(root.resolve()).as_posix()
    except ValueError:
        return resolved.as_posix()


def simple_name(name: str) -> str:
    """Final component of a possibly qualified Lean name (`«a.b»` is one component)."""
    comps = _components(name)
    return canonical_name(comps[-1]) if comps else name


def is_residual_like(name: str, residual_names: set[str]) -> bool:
    """Is `name` obligation-like (a vacuous `True` under it launders a debt)?

    `residual_names` holds the full and simple names of the pinned residuals.
    This is a naming heuristic only; authorizing an `axiom` needs its exact pin.
    """
    final = simple_name(name)
    low = final.lower()
    return (
        canonical_name(name) in residual_names
        or final in residual_names
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


_OPAQUE_HEADER_TOKEN_RE = re.compile(
    r":=|[(){}\[\]⟨⟩⦃⦄]|#[A-Za-z_]\w*|"
    + _ID_START
    + r"(?:(?P<complex>let\s+rec|by)|"
    + r"(?P<binding>let|letI|let_fun|let_λ|let_delayed|let_tmp|have|haveI)|"
    + r"(?P<command>example|instance|structure|class|inductive|namespace|section|end))"
    + _ID_END
)
_OPAQUE_BRACKETS = {**_BRACKET_OPEN, "⦃": "⦄"}
_OPAQUE_CLOSERS = set(_OPAQUE_BRACKETS.values())


def opaque_has_body(
    live_text: str, start: int, limit: int, quoted: list[tuple[int, int]]
) -> bool:
    """Find a body assignment before the next command, excluding type bindings."""
    brackets: list[str] = []
    bindings = 0
    for match in _OPAQUE_HEADER_TOKEN_RE.finditer(live_text, start, limit):
        if not outside_quoted(match.start(), quoted):
            continue
        token = match.group()
        if token in _OPAQUE_BRACKETS:
            brackets.append(_OPAQUE_BRACKETS[token])
        elif token in _OPAQUE_CLOSERS:
            if not brackets or brackets.pop() != token:
                return False
        elif not brackets:
            if token.startswith("#") or match.lastgroup in {"complex", "command"}:
                return False
            if match.lastgroup == "binding":
                bindings += 1
            elif token == ":=":
                if not bindings:
                    return True
                bindings -= 1
    return False


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


def find_true_placebos(reading: Reading, live: str | None = None) -> list[tuple[int, str]]:
    """Find `theorem`/`lemma` declarations whose statement type is exactly `True`.

    Returns a list of `(line, name)`. Comment/docstring and literal characters
    are blanked first (`live`, defaulting to `reading.code_text()`; newlines
    preserved, so line numbers stay accurate). For each
    declaration head we walk its signature tracking bracket depth, locate the
    top-level statement colon (binder colons live inside brackets) and the
    top-level `:=` that begins the proof, and flag it when the type between them
    is built only from `True` (see `is_vacuous_true`) and `True` is not rebound
    by a binder, `variable` or file-level declaration (see `true_is_shadowed`).
    Stopping at `:=` keeps in-proof `have … : True := …` steps from being
    mistaken for the declaration's statement.
    """
    live = reading.code_text() if live is None else live
    scopes = TrueScopes(live, reading.quoted)
    decls = [m for m in PLACEBO_DECL_RE.finditer(live)
             if outside_quoted(m.start(), reading.quoted)]
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


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Reject axiom-laundering tokens in live Lean source (CI gate 1).")
    parser.add_argument("paths", nargs="*",
                        help="Lean files or directories "
                             "(default: ArkLib/, Research/ and ProximityPrize/)")
    parser.add_argument("--allowlist", type=Path, default=ALLOWLIST_PATH,
                        help="reviewed residual-axiom manifest "
                             "(default: scripts/residual_axioms.txt)")
    parser.add_argument("--root", type=Path, default=REPO_ROOT,
                        help="directory the manifest's file paths are relative to "
                             "(default: the repository root)")
    parser.add_argument("--print-residual-manifest", action="store_true",
                        help="print the pin line of every live axiom in the scanned files "
                             "(for a reviewed manifest update) and exit")
    return parser.parse_args(argv)


def ambiguity_failure(path: Path, text: str, offset: int) -> str:
    line = text.count("\n", 0, offset) + 1
    return (
        f"{path}:{line}: string literal reads differently as a plain and as an "
        f"interpolated string, which changes what is a comment, a quoted identifier or "
        f"a declaration; the scan cannot be trusted here, so rewrite the literal (in a "
        f"plain string write `{{` as `\\x7b`; `\\{{` is only valid in an interpolated one)"
    )


def print_manifest(sites: list[tuple[Path, str, str, AxiomSite]], pins: dict[str, Pin]) -> int:
    """Print a manifest line for every live axiom (`--print-residual-manifest`)."""
    status = 0
    for path, text, rel, site in sites:
        if site.fqn is None:
            line = text.count("\n", 0, site.start) + 1
            print(f"# {path}:{line}: cannot determine the fully qualified name of axiom "
                  f"{site.name}")
            status = 1
            continue
        pin = pins.get(site.fqn)
        note = pin.note if pin and pin.note else "TODO: tracking issue and short note"
        print(f"{site.fqn}  {rel}  {site.digest}  # {note}")
    return status


def check_axiom(path: Path, text: str, rel: str, site: AxiomSite,
                pins: dict[str, Pin]) -> str | None:
    """None if `site` is exactly its reviewed pin, else the failure message."""
    line = text.count("\n", 0, site.start) + 1
    where = f"{path}:{line}"
    if site.fqn is None:
        return (f"{where}: forbidden custom axiom declaration {site.name}: its fully "
                f"qualified name cannot be determined (unbalanced or mismatched "
                f"namespace/section/end), so it cannot match a reviewed pin")
    pin = pins.get(site.fqn)
    suggestion = f"`{site.fqn}  {rel}  {site.digest}`"
    if pin is None:
        same_name = sorted(p.fqn for p in pins.values()
                           if simple_name(p.fqn) == simple_name(site.fqn))
        if same_name:
            return (f"{where}: forbidden custom axiom declaration {site.name}: "
                    f"{site.fqn} is not the pinned residual {', '.join(same_name)}; a "
                    f"scripts/residual_axioms.txt entry pins one fully qualified "
                    f"declaration in one file, so a copy or relocation under another "
                    f"namespace is not a documented assumption")
        full = "" if site.fqn == canonical_name(site.name) else f" ({site.fqn})"
        return (f"{where}: forbidden custom axiom declaration {site.name}{full}; "
                f"prove it or state it as an explicit Prop. Only a documented, tracked "
                f"residual may be pinned in scripts/residual_axioms.txt, after review, as "
                f"{suggestion}")
    if pin.file != rel or pin.digest != site.digest:
        return (f"{where}: residual axiom {site.fqn} does not match its reviewed pin "
                f"(scripts/residual_axioms.txt:{pin.line} expects {pin.file} "
                f"{pin.digest}; found {rel} {site.digest}): its statement, an in-scope "
                f"variable/universe/open/export/include/omit command, or its file changed. "
                f"Review the new statement; only if it is still the intended documented "
                f"assumption, update the entry to {suggestion}")
    return None


def main() -> int:
    args = parse_args(sys.argv[1:])
    files, full_arklib_scan, path_errors = scan_plan(args.paths)
    if path_errors:
        print("\n".join(path_errors), file=sys.stderr)
        return 1

    pins, manifest_errors = load_manifest(args.allowlist)
    residual_names = set(pins) | {simple_name(fqn) for fqn in pins}
    inherited = InheritedSourcePolicy()
    failures: list[str] = list(manifest_errors)
    allowed_hits: list[str] = []
    inherited_hits: list[str] = []
    present: set[str] = set()
    pinned_sites: dict[str, list[str]] = {}
    manifest_sites: list[tuple[Path, str, str, AxiomSite]] = []
    for path in files:
        text = path.read_text(encoding="utf-8", errors="replace")
        rel = repo_path(path, args.root)
        readings, exhausted = lean_lexer.explore(text)
        base = readings[0]
        live_text = base.code_text()
        if args.print_residual_manifest:
            manifest_sites += [(path, text, rel, s) for s in axiom_sites(base, live_text)]
            continue
        if exhausted:
            failures.append(
                f"{path}: more than {lean_lexer.DEFAULT_BUDGET} readings of its ambiguous "
                f"plain/interpolated string literals; the scan cannot be trusted, so "
                f"rewrite those literals"
            )
        reported: set[int] = set()
        for other in disagreeing_readings(readings, live_text):
            offset = min(other.flips)
            if offset not in reported:
                reported.add(offset)
                failures.append(ambiguity_failure(path, text, offset))
        # Code in at least one reading, interpolation holes included.
        any_live = text if exhausted else lean_lexer.blank(text, lean_lexer.live_mask(readings))
        for m in TOKEN_RE.finditer(any_live):
            line = text.count("\n", 0, m.start()) + 1
            failures.append(f"{path}:{line}: forbidden token {m.group(1)}")
        native_forms = {
            hit
            for reading in readings
            for hit in native_eval_hits(lean_lexer.blank(text, reading.code_mask()), reading.quoted)
        }
        for offset, form in sorted(native_forms):
            line = text.count("\n", 0, offset) + 1
            failures.append(f"{path}:{line}: forbidden native evaluation configuration `{form}`")
        for m in META_DECL_RE.finditer(any_live):
            line = text.count("\n", 0, m.start()) + 1
            failures.append(
                f"{path}:{line}: forbidden metaprogram declaration `{m.group(0)}` "
                f"(adds a kernel declaration, e.g. an axiom, without an `axiom` "
                f"keyword; state residuals as `def ...Residual : Prop`)"
            )
        for off in exit_hits(any_live, base):
            line = text.count("\n", 0, off) + 1
            failures.append(
                f"{path}:{line}: forbidden `#exit` (Lean stops checking the file here, "
                f"but text-based gates such as the residual census still read what "
                f"follows; delete the unchecked tail or move it to a scratch file)"
            )
        for m in DEBUG_OPTION_RE.finditer(text):
            if any(reading.kind[m.start()] != COMMENT for reading in readings):
                line = text.count("\n", 0, m.start()) + 1
                failures.append(
                    f"{path}:{line}: forbidden Lean debug option `debug.{m.group(1)}` "
                    f"(skips the kernel type checker or replaces the proof with `sorryAx` "
                    f"without a `sorry` token)"
                )
        scopes = TrueScopes(live_text, base.quoted)
        for m in UNSAFE_DECL_RE.finditer(live_text):
            if not outside_quoted(m.start(), base.quoted):
                continue
            line = text.count("\n", 0, m.start()) + 1
            failures.append(
                f"{path}:{line}: forbidden unsafe declaration "
                f"(repository policy rejects live `unsafe` decls; prove in safe "
                f"Lean or track a residual — this precheck is not a kernel-escape claim)"
            )
        decls = declaration_heads(live_text, base)
        for decl_index, dm in enumerate(decls):
            kind, name = dm.group(1), dm.group(2)
            next_decl_start = decls[decl_index + 1].start() if decl_index + 1 < len(decls) else None
            if kind in OPAQUE_KINDS:
                limit = next_decl_start if next_decl_start is not None else len(live_text)
                if not opaque_has_body(live_text, dm.end(), limit, base.quoted):
                    line = text.count("\n", 0, dm.start()) + 1
                    failures.append(
                        f"{path}:{line}: bodyless {kind} declaration {name} introduces an "
                        f"unproven inhabitant of its statement type (axiom-equivalent "
                        f"laundering); provide a real ':=' proof/definition and parenthesize a "
                        f"complex result type, or state the "
                        f"obligation as an explicit Prop or a tracked sorry"
                    )
                continue
            if kind in {"theorem", "lemma"}:
                continue
            if not is_residual_like(name, residual_names):
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
        for site in axiom_sites(base, live_text):
            if site.fqn is not None:
                present.add(site.fqn)
            problem = check_axiom(path, text, rel, site, pins)
            if problem:
                failures.append(problem)
                continue
            where = f"{path}:{text.count(chr(10), 0, site.start) + 1}"
            pinned_sites.setdefault(site.fqn, []).append(where)
            allowed_hits.append(f"{where}: allowed documented residual axiom {site.fqn} "
                                f"(pinned assumption, not a proof)")

        for offset in antiquoted_axiom_hits(live_text, base):
            line = text.count("\n", 0, offset) + 1
            failures.append(
                f"{path}:{line}: forbidden custom axiom declaration with an antiquoted "
                f"name (`axiom $…` in a syntax quotation lets a macro or elaborator "
                f"declare an axiom whose name the allowlist never sees)"
            )

        for line_no, name in find_true_placebos(base, live_text):
            if inherited.allows(path, name, "vacuous_true_theorem"):
                inherited_hits.append(f"{path}:{line_no}: inherited upstream True stub {name} "
                                      "(byte-pinned debt; scripts/upstream-source-policy.json)")
                continue
            failures.append(
                f"{path}:{line_no}: forbidden vacuous placebo "
                f"`theorem/lemma {name} : True` proves nothing about the named "
                f"obligation (axiom-laundering pattern, #169/#171). Prove the real "
                f"statement or track it by its GitHub issue, not a `True` theorem."
            )

    if args.print_residual_manifest:
        return print_manifest(manifest_sites, pins)

    for lakefile in lakefile_paths(args.paths):
        try:
            hits = lakefile_debug_option_hits(lakefile.read_text(encoding="utf-8"))
        except (OSError, UnicodeError, tomllib.TOMLDecodeError) as exc:
            failures.append(f"{lakefile}: cannot read Lake configuration: {exc}")
            continue
        for location, option in hits:
            failures.append(
                f"{lakefile}: forbidden Lean debug option `debug.{option}` in the "
                f"Lake configuration at {location}"
            )

    for fqn, sites in sorted(pinned_sites.items()):
        unique_sites = sorted(set(sites))
        if len(unique_sites) > 1:
            failures.append(
                f"{fqn}: pinned residual axiom declared {len(unique_sites)} times "
                f"({', '.join(unique_sites)}); one residual_axioms.txt entry documents "
                f"exactly one declaration"
            )

    stale = sorted(set(pins) - present)
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
    if inherited_hits:
        print("\n".join(inherited_hits))
    print(
        "forbidden-token precheck: clean (no native_decide / bv_decide / "
        "ofReduceBool / ofReduceNat / trustCompiler / reduceBool / reduceNat / "
        "unsafe declaration / unsafeCast / implemented_by / "
        "undocumented custom axiom / new vacuous `: True` placebo / "
        "kernel-skip or proof-as-sorry debug option; "
        f"{len(allowed_hits)} allowlisted residual axiom(s), "
        f"{len(inherited_hits)} byte-pinned upstream True stub(s))"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
