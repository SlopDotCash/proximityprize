#!/usr/bin/env python3
"""Residual census for the ArkLib source tree: a syntactic inventory.

ArkLib encodes many open proof obligations as named Prop definitions:

  def <Name>Residual ... : Prop := ...

End-to-end theorems consume these as hypotheses.  This script inventories
every `def` under ArkLib/ or ProximityPrize/ whose name ends in `Residual` and
whose result type is exactly `Prop` (multiline signatures handled), and triages
each one from **source text alone**.

Scope and limits.  Only `ArkLib/**/*.lean` and `ProximityPrize/**/*.lean`
(including relocated classic extensions) are scanned: residuals under
`Research/` (including migrated campaign residuals) and named `Prop` or
structure hypotheses outside the strict suffix pattern are not counted.  Lean
is never elaborated, so binders, section variables, instance arguments and
result types are read as text.  Every label is a conservative heuristic, not
a kernel check: the census is a syntactic inventory, not a verified
completion ledger, and a `discharged` row is a candidate to review, not a
certified proof.

Providers.  A candidate provider of a census residual `R` is a theorem,
lemma, def or instance whose result has `R` at the head of a *conclusion
atom*: after outer parentheses and leading `∀` binders are stripped, the
result is split at top-level `↔`, `→`, `∨`, `∧`, `¬` and relations; the last
`→` target is the conclusion and each of its top-level conjuncts is an atom.
Every provider gets a verdict:

  not_provider -- `R` heads the result but is only related to another
                  proposition (`R ↔ Q`, `R → Q`, `R ∨ Q`, `R = Q`).
  ambiguous    -- several census residuals share the last name and the
                  provider could not be narrowed by qualification/namespace.
  conditional  -- the provider assumes something: a census residual; a
                  proof-like binder (named `h…`, proposition-shaped, or typed
                  by a known proposition such as `False` or an in-tree
                  `Prop`-valued declaration); a premise of the result
                  (`P → R`, `∀ x ∈ s, R x`, `∀ (h : P), R`); a proof-like
                  section `variable` that Lean includes in the declaration
                  (named by `include`, mentioned in the header, or a
                  dependency of one); or an instance binder missing from the
                  residual's own binders other than an always-satisfiable one
                  such as `DecidableEq` (for example `[Fact p.Prime]`,
                  `[Fintype α]`, or an instance of an in-tree
                  `class C : Prop`).  A conditional reduction is not a proof.
  instance     -- no assumption was recognised, but only an *instance* of the
                  residual family is proved: an argument of `R` is a literal
                  or compound term, a bound name is passed twice, or a
                  parameter type is a literal instance of the residual's (a
                  section variable `pSpec₂ : ProtocolSpec 0` where the
                  residual is stated for `ProtocolSpec n`).
  uniform      -- no assumption was recognised and every argument of `R` is
                  a distinct bound name: a candidate uniform discharge.

Refutations are declarations proving `¬ R ...`.  One counts only when it has
no proof-like binder, premise, included proof-like section variable or
`Prop`-class instance assumption.

Row status:

  refuted       -- an unconditional refutation exists: some instance is
                   false, so the family is not uniformly true.  This outranks
                   every provider; proved instances stay listed, because an
                   instance proof plus an instance refutation is mixed
                   parameter-scope coverage, not a contradiction.
  discharged    -- a `uniform` provider exists (a syntactic candidate only).
  instance_only -- only `instance` providers exist; their proved regimes are
                   listed, but the general residual is not discharged.
  open          -- everything else.

Known blind spots, which are why a `discharged` row still needs review: data
binders absent from the result are assumed inhabited; an implicit argument
fixed by unification is caught only when a same-named binder has a literal
type; section-variable inclusion for definitions is approximated from text;
and an argument that is a bound name may still have a narrower type than the
residual's parameter.

A residual name appearing only in hypothesis position is consumption, not
provision.  Residual-like defs that miss the strict pattern are reported as
near misses but kept out of the census.

Usage:
  python3 scripts/residual_census.py                 # summary + JSON
  python3 scripts/residual_census.py --root <dir>    # explicit checkout root
  python3 scripts/residual_census.py --out <file>    # JSON destination
  python3 scripts/residual_census.py --wiki-out docs/wiki/residual-census.md

Writes scripts/residual_census.json by default.  Python 3 stdlib only.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path


def configure_stdio() -> None:
    """Prefer UTF-8 output for declaration names on Windows consoles."""
    for stream in (sys.stdout, sys.stderr):
        reconfigure = getattr(stream, "reconfigure", None)
        if reconfigure is not None:
            reconfigure(encoding="utf-8")


DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|scoped\s+|unsafe\s+|nonrec\s+)*"
    r"(theorem|lemma|def|instance|abbrev|opaque)\s+([^\s({\[:⦃]+)"
)
# Type-forming declarations are scanned only to learn which names denote
# propositions (`structure Foo : Prop`, `class Bar : Prop`, ...).
TYPE_DECL_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|unsafe\s+)*"
    r"(class\s+inductive|class|structure|inductive)\s+([^\s({\[:⦃]+)"
)
NAMESPACE_RE = re.compile(r"^\s*namespace\s+(\S+)")
SECTION_RE = re.compile(r"^\s*(?:noncomputable\s+)?section(?:\s+(\S+))?\s*$")
END_RE = re.compile(r"^\s*end(?:\s+(\S+))?\s*$")
MUTUAL_RE = re.compile(r"^\s*mutual\s*$")
VARIABLE_RE = re.compile(r"^(\s*)variable\b(.*)$")
INCLUDE_OMIT_RE = re.compile(r"^(\s*)(include|omit)\b(.*)$")
HEAD_IDENT_RE = re.compile(r"[^\s({\[⦃⟨:,]+")
IDENT_RE = re.compile(r"[^\W\d][\w'!?]*(?:\.[^\W\d][\w'!?]*)*")
TOKEN_RE = re.compile(r"[^\W\d][\w'!?]*(?:\.[^\W\d][\w'!?]*)*|\d+(?:\.\d+)?|\S")
UNIVERSE_ARGS_RE = re.compile(r"\.\{[^{}]*\}")
SORT_LEVEL_RE = re.compile(
    r"\b(Type|Sort)\s*(?:\*|_(?![\w'])|[uvw][\w']*(?![\w'])|\((?:max|imax)[^()]*\))"
)

OPEN_BRACKETS = "([{⟨⦃"
CLOSE_BRACKETS = ")]}⟩⦄"

PROVIDER_KINDS = {"theorem", "lemma", "def", "instance"}
# Declarations whose bodies (not only headers) decide which section variables
# Lean includes.  Theorems include section variables only through the header,
# `include`, and instance dependencies.
DEF_LIKE_KINDS = {"def", "abbrev", "instance", "opaque"}
PROP_DECL_KINDS = {"def", "abbrev", "opaque", "structure", "class", "class inductive", "inductive"}

CAMPAIGN_ADDENDUM_PREFIX = "> **Campaign addendum"

SCOPE = "ArkLib/**/*.lean and ProximityPrize/**/*.lean only"

# Last name components that always denote propositions.  In-tree declarations
# whose result is `Prop` (or a `Prop`-valued family) are added at scan time.
KNOWN_PROP_HEADS = frozenset(
    {
        "False", "True", "Not", "Eq", "Ne", "HEq", "And", "Or", "Iff", "Exists",
        "Nonempty", "Fact", "NeZero", "IsEmpty", "Subsingleton", "Nontrivial",
        "Finite", "Infinite", "Countable", "NeverFail", "Disjoint", "Irreducible",
        "Prime", "IsUnit", "Squarefree", "IsCoprime", "Coprime", "Monotone",
        "Antitone", "StrictMono", "StrictAnti", "Continuous", "Even", "Odd",
        "IsPrimitiveRoot", "CharP", "ExpChar", "CharZero", "IsDomain",
        "NoZeroDivisors", "IsCyclic", "IsField", "LinearIndependent", "Injective",
        "Surjective", "Bijective", "InjOn", "SurjOn", "BijOn", "MapsTo", "Monic",
        "Separable", "Splits",
    }
)
# Typeclasses whose instances are propositions (last name component).  In-tree
# `class ... : Prop` declarations are added at scan time.
KNOWN_PROP_CLASSES = frozenset(
    {
        "Fact", "NeZero", "Nonempty", "Nontrivial", "IsEmpty", "Subsingleton",
        "Finite", "Infinite", "Countable", "CharP", "ExpChar", "CharZero", "IsDomain",
        "NoZeroDivisors", "IsCyclic", "IsAlgClosed", "IsGalois", "FiniteDimensional",
        "IsScalarTower", "SMulCommClass", "IsNoetherianRing", "IsReduced",
        "PerfectField", "IsSeparable", "Free", "IsCyclotomicExtension",
    }
)
# Instance arguments that every type admits (classically), so an extra binder
# of one of these classes does not restrict the residual instance proved.
ALWAYS_SATISFIABLE_CLASSES = frozenset(
    {"DecidableEq", "DecidablePred", "DecidableRel", "Decidable", "BEq", "LawfulBEq",
     "Hashable", "Repr", "ToString"}
)
LITERAL_RE = re.compile(r"^(?:\d+(?:\.\d+)?|0x[0-9a-fA-F]+|∅|⊥|⊤|true|false|!\[\]|\[\])$")

STATUSES = ("open", "instance_only", "discharged", "refuted")


def strip_comments(text: str) -> str:
    """Blank out line comments, block comments, and docstrings (newlines kept).

    String literals in live code are not comments: a ``"/-"`` or ``"--"``
    inside a double-quoted string must not open a phantom block/line
    comment and hide the declarations that follow it from the census.
    Inside a block comment, comment scanning wins (Lean lexes the comment
    first), so string markers there are not treated as string starts.
    """
    out = list(text)
    i, n, depth = 0, len(text), 0
    while i < n:
        if depth == 0 and text[i] == "'":
            # Char literal: 'x' or an escaped char such as '\n'. Skip it
            # whole so a '"' char literal is not mistaken for a string.
            if i + 2 < n and text[i + 2] == "'":
                i += 3
                continue
            if i + 3 < n and text[i + 1] == "\\" and text[i + 3] == "'":
                i += 4
                continue
        if depth == 0 and text[i] == '"':
            i += 1
            while i < n and text[i] != '"':
                if text[i] == "\\" and i + 1 < n:
                    i += 2
                else:
                    i += 1
            if i < n:
                i += 1
            continue
        if depth == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j == -1 else j
            for k in range(i, j):
                out[k] = " "
            i = j
        elif text.startswith("/-", i):
            depth += 1
            out[i] = " "
            if i + 1 < n:
                out[i + 1] = " "
            i += 2
        elif depth > 0 and text.startswith("-/", i):
            depth -= 1
            out[i] = " "
            if i + 1 < n:
                out[i + 1] = " "
            i += 2
        else:
            if depth > 0 and text[i] != "\n":
                out[i] = " "
            i += 1
    return "".join(out)


def _signature_bounds(window: str) -> tuple[int | None, int]:
    """(signature colon index or None, index of the first depth-0 `:=`)."""
    depth = 0
    sig_colon = None
    end = len(window)
    i = 0
    while i < len(window):
        c = window[i]
        if c in OPEN_BRACKETS:
            depth += 1
        elif c in CLOSE_BRACKETS:
            depth = max(0, depth - 1)
        elif depth == 0 and c == ":":
            if i + 1 < len(window) and window[i + 1] == "=":
                end = i
                break
            if sig_colon is None:
                sig_colon = i
        i += 1
    return sig_colon, end


def split_signature(window: str) -> tuple[str, str]:
    """Split a declaration tail (after the name) into (binders, result type).

    The signature colon is the first `:` at bracket depth 0 that is not part
    of `:=`; the signature ends at the first depth-0 `:=`.  Bracket depth
    tracks (), [], {}, ⟨⟩, ⦃⦄ so binder-internal colons and named arguments
    `(k := k)` are skipped.
    """
    sig_colon, end = _signature_bounds(window)
    if sig_colon is None:
        return window[:end], ""
    return window[:sig_colon], window[sig_colon + 1 : end]


def split_declaration(window: str) -> tuple[str, str, str]:
    """(binders, result type, body after `:=`) of a declaration tail."""
    sig_colon, end = _signature_bounds(window)
    body = window[end + 2 :] if end < len(window) else ""
    if sig_colon is None:
        return window[:end], "", body
    return window[:sig_colon], window[sig_colon + 1 : end], body


def type_declaration_result(window: str) -> str:
    """Result type of a `structure`/`class`/`inductive` header, or ``""``.

    The header ends at the first depth-0 `where`, `extends`, `:=`, `|` or
    `deriving`; a colon after that point belongs to a field or constructor.
    """
    flat = flatten_top_level(window)
    m = re.search(r"(?<![\w'])(?:where|extends|deriving)(?![\w'])|:=|\|", flat)
    head = window[: m.start()] if m else window
    sig_colon, _end = _signature_bounds(head)
    if sig_colon is None:
        return ""
    return head[sig_colon + 1 :]


def norm_space(text: str) -> str:
    return " ".join(text.split())


def flatten_top_level(text: str, scoped: bool = False) -> str:
    """`text` with every bracketed region (brackets included) blanked out.

    With `scoped`, the body of a depth-0 binder (see `scope_limit`) is blanked
    as well.
    """
    out = []
    depth = 0
    limit = scope_limit(text) if scoped else len(text)
    for i, c in enumerate(text):
        if i >= limit:
            out.append(" ")
        elif c in OPEN_BRACKETS:
            depth += 1
            out.append(" ")
        elif c in CLOSE_BRACKETS:
            depth = max(0, depth - 1)
            out.append(" ")
        else:
            out.append(c if depth == 0 else " ")
    return "".join(out)


def matching_close(text: str, start: int) -> int | None:
    """Index of the bracket closing the one opened at `text[start]`."""
    depth = 0
    for i in range(start, len(text)):
        c = text[i]
        if c in OPEN_BRACKETS:
            depth += 1
        elif c in CLOSE_BRACKETS:
            depth -= 1
            if depth == 0:
                return i
    return None


def strip_outer_parens(text: str) -> str:
    """Remove parentheses that wrap the whole of `text`."""
    s = text.strip()
    while s.startswith("(") and matching_close(s, 0) == len(s) - 1:
        s = s[1:-1].strip()
    return s


SCOPE_BINDER_RE = re.compile(r"[∀∃]|(?<![\w'.])(?:fun|λ)(?![\w'])")


def scope_limit(text: str) -> int:
    """Index where a depth-0 binder (`∀`, `∃`, `fun`, `λ`) after position 0 starts.

    Such a binder extends as far right as possible, so a connective after it
    belongs to the binder's body: in `A ∧ ∀ B, R B → C` the `→` is inside the
    `∀`, not a top-level arrow.
    """
    depth = 0
    for i, c in enumerate(text):
        if c in OPEN_BRACKETS:
            depth += 1
        elif c in CLOSE_BRACKETS:
            depth = max(0, depth - 1)
        elif depth == 0 and i > 0 and SCOPE_BINDER_RE.match(text, i):
            return i
    return len(text)


def depth0_index(text: str, token: str, scoped: bool = False) -> int | None:
    """Index of the first depth-0 occurrence of `token`.

    With `scoped`, occurrences inside the body of a depth-0 binder are skipped.
    """
    depth = 0
    limit = scope_limit(text) if scoped else len(text)
    i = 0
    while i < limit:
        c = text[i]
        if c in OPEN_BRACKETS:
            depth += 1
        elif c in CLOSE_BRACKETS:
            depth = max(0, depth - 1)
        elif depth == 0 and text.startswith(token, i):
            return i
        i += 1
    return None


def split_top_level(text: str, sep: str) -> list[str]:
    """Split `text` at every depth-0 `sep` outside the body of a depth-0 binder."""
    parts: list[str] = []
    depth = 0
    start = 0
    limit = scope_limit(text)
    i = 0
    while i < limit:
        c = text[i]
        if c in OPEN_BRACKETS:
            depth += 1
        elif c in CLOSE_BRACKETS:
            depth = max(0, depth - 1)
        elif depth == 0 and text.startswith(sep, i):
            parts.append(text[start:i])
            i += len(sep)
            start = i
            continue
        i += 1
    parts.append(text[start:])
    return parts


def strip_forall_prefix(result: str) -> str:
    """Strip leading `∀ ...,` binders from a result type."""
    s = result.strip()
    for _ in range(8):
        if not s.startswith("∀"):
            break
        comma = depth0_index(s, ",")
        if comma is None:
            return ""
        s = s[comma + 1 :].strip()
    return s


def atom_head(text: str) -> str:
    """Head identifier of an application, ignoring a leading `@`."""
    s = strip_outer_parens(text)
    if s.startswith("@"):
        s = s[1:]
    m = HEAD_IDENT_RE.match(s)
    return m.group(0) if m else ""


def result_head(result: str) -> str:
    """Head identifier of a result type, stripping leading `∀ ...,` binders."""
    return atom_head(strip_forall_prefix(result))


def split_top_level_once(text: str, sep: str) -> tuple[str, str] | None:
    """Split at the first top-level separator inside one binder group."""
    idx = depth0_index(text, sep)
    if idx is None:
        return None
    return text[:idx], text[idx + len(sep) :]


def is_ident_char(c: str) -> bool:
    return c.isalnum() or c in "_'"


def mentions_word(text: str, word: str) -> bool:
    """Whole-identifier occurrence of `word`; allows a qualifying dot before,
    rejects a dot after (that would be a namespace use, not the residual)."""
    start = 0
    while True:
        idx = text.find(word, start)
        if idx == -1:
            return False
        before = text[idx - 1] if idx > 0 else " "
        after = text[idx + len(word)] if idx + len(word) < len(text) else " "
        if not is_ident_char(before) and not is_ident_char(after) and after != ".":
            return True
        start = idx + 1


def binder_groups(binders: str) -> list[tuple[str, str, str]]:
    """Return top-level binder groups as (open delimiter, content, close delimiter)."""
    close_for = {"(": ")", "{": "}", "[": "]", "⦃": "⦄"}
    groups: list[tuple[str, str, str]] = []
    i = 0
    while i < len(binders):
        opener = None
        if binders.startswith("⦃", i):
            opener = "⦃"
            close = "⦄"
            start = i
        elif binders[i] in "({[":
            opener = binders[i]
            close = close_for[opener]
            start = i
        if opener is None:
            i += 1
            continue
        depth = 0
        j = i
        while j < len(binders):
            if binders.startswith("⦃", j):
                depth += 1
                j += 1
            elif binders.startswith("⦄", j):
                depth = max(0, depth - 1)
                if depth == 0 and close == "⦄":
                    groups.append((opener, binders[start + 1 : j], close))
                    i = j + 1
                    break
                j += 1
            else:
                c = binders[j]
                if c in OPEN_BRACKETS:
                    depth += 1
                elif c in CLOSE_BRACKETS:
                    depth = max(0, depth - 1)
                    if depth == 0 and c == close:
                        groups.append((opener, binders[start + 1 : j], close))
                        i = j + 1
                        break
                j += 1
        else:
            i += 1
    return groups


ANONYMOUS = "_"


def group_entries(opener: str, content: str) -> list[dict]:
    """Binder entries `{opener, name, type}` for one binder group.

    Anonymous and `_`-prefixed names are kept (an unused hypothesis is still a
    hypothesis), groups without a type keep their names, and an instance group
    without a name gets `name=None`.
    """
    split = split_top_level_once(content, ":")
    if split is None:
        if opener == "[":
            return [{"opener": opener, "name": None, "type": norm_space(content)}]
        return [
            {"opener": opener, "name": tok, "type": ""}
            for tok in content.split()
            if not any(ch in tok for ch in ":=<>|\\/()")
        ]
    names_txt, typ = split
    default = split_top_level_once(typ, ":=")
    if default is not None:
        typ = default[0]
    typ = norm_space(typ)
    names: list[str] = []
    for tok in re.findall(r"[^\s,]+", names_txt):
        tok = tok.strip("(){}[]⦃⦄")
        if not tok or any(ch in tok for ch in ":=<>|\\/"):
            continue
        names.append(ANONYMOUS if tok == "_" else tok)
    if opener == "[":
        return [{"opener": opener, "name": names[0] if names else None, "type": typ}]
    return [{"opener": opener, "name": n, "type": typ} for n in names]


def own_entries(binders: str) -> list[dict]:
    entries: list[dict] = []
    for opener, content, _close in binder_groups(binders):
        entries.extend(group_entries(opener, content))
    return entries


# Surface syntax that can only spell a proposition.  `=` is matched only when
# it is neither part of a `:=` / `=>` named argument nor `==`; comparisons must
# be whitespace-delimited so the mathlib data types `ℝ≥0`, `ℝ≥0∞`, and `ℚ≥0`
# do not match.
BARE_EQUAL_RE = re.compile(r"(?<![=:])=(?![=>])")
COMPARISON_RE = re.compile(r"(?<=\s)[<>≤≥](?=\s)")
PROPOSITION_MARKERS = ("≠", "∈", "∉", "↔", "∨", "∧")


def is_proposition_shaped(typ: str) -> bool:
    """True when a flattened binder type can only be a proposition.

    Subtypes (`{x // p x}`) are excluded: such a binder carries an element,
    and its membership proof is part of the data type, not an extra
    hypothesis.  Type families (`ι → Type`) carry no propositional syntax and
    are excluded by the marker set itself.
    """
    if "//" in typ:
        return False
    return bool(
        re.fullmatch(r"(?:_root_\.)?(?:True|False)", typ.strip())
        or BARE_EQUAL_RE.search(typ)
        or COMPARISON_RE.search(typ)
        or any(marker in typ for marker in PROPOSITION_MARKERS)
    )


def type_head_last(typ: str) -> str:
    """Last name component of the head of a type's codomain, seen through `∀ ...,`.

    The codomain decides: `P → Q` is a proposition exactly when `Q` is.
    """
    s = strip_forall_prefix(typ.strip())
    s = strip_outer_parens(split_top_level(s, "→")[-1])
    if s.startswith("¬"):
        return "Not"
    if s.startswith("@"):
        s = s[1:]
    if s.startswith("("):
        close = matching_close(s, 0)
        if close is not None:
            m = re.match(r"\.([^\W\d][\w'!?]*)", s[close + 1 :])
            return m.group(1) if m else ""
        return ""
    m = IDENT_RE.match(s)
    return m.group(0).rsplit(".", 1)[-1] if m else ""


def looks_like_proof_assumption(
    names: list[str], typ: str, prop_heads: frozenset[str] | set[str] = frozenset()
) -> bool:
    """Heuristic for explicit binders that are hypotheses rather than data.

    We intentionally do not classify every explicit binder absent from a result
    as conditional: Lean result heads often omit inferred type/data parameters.
    Instead, we flag binders whose names or types look proof-like.

    Proposition-shaped types join the `h`-prefix and literal `Prop`/`¬` tests:
    hypotheses are not always named `h…`.  The motivating case is the
    `coupling` binder of `fiatShamir_hvzkTransfer_of_coupling`
    (ArkLib/OracleReduction/FiatShamir/HVZKTransferReduction.lean), whose
    docstring calls it "an explicit hypothesis" — it was previously recorded
    as an unconditional provider.  A type headed by a known proposition
    (`False`, `Fact`, a census residual, an in-tree `Prop`-valued
    declaration passed in `prop_heads`) is a hypothesis whatever the binder
    is called: `(p : False)` and `(h : False)` must classify alike.
    """
    typ_flat = " ".join(typ.split())
    if any(name.startswith("h") or name.startswith("H") for name in names):
        return not (typ_flat.startswith("Type") or typ_flat.startswith("Sort"))
    # Keep this conservative: function/relation data parameters often contain
    # `∀`, `→`, or even bounded polynomial notation.  Residual dependencies are
    # tracked separately by exact name, so this field is just for obvious
    # hypothesis binders whose names do not appear in the residual instance.
    if "Prop" in typ_flat or "¬" in typ_flat:
        return True
    head = type_head_last(typ_flat)
    if head and (head in KNOWN_PROP_HEADS or head in prop_heads):
        return True
    return is_proposition_shaped(typ_flat)


def extra_explicit_binders(
    binders: str, result: str, prop_heads: frozenset[str] | set[str] = frozenset()
) -> list[str]:
    """Proof-like explicit/implicit non-instance binders not used in the result type.

    These are proof/data assumptions for a candidate provider rather than
    parameters of the residual instance it provides.  Square-bracket instance
    binders are compared with the residual's own instances in `assess`.
    """
    extras: list[str] = []
    for entry in own_entries(binders):
        if entry["opener"] == "[":
            continue
        name = entry["name"]
        if not looks_like_proof_assumption([name], entry["type"], prop_heads):
            continue
        if name == ANONYMOUS or not mentions_word(result, name):
            extras.append(name)
    return sorted(set(extras))


def has_top_level(text: str, token: str) -> bool:
    """True when `token` occurs at bracket depth 0 of `text`, outside the body of
    a depth-0 binder."""
    return depth0_index(text, token, scoped=True) is not None


TOP_LEVEL_CONNECTIVES = ("↔", "→", "∧", "∨", "=")
REDUCTION_CONNECTIVES = frozenset({"→", "∨", "="})
# Lean 4 precedences: a lower number binds more loosely.
CONNECTIVE_PRECEDENCE = {"↔": 20, "→": 25, "∨": 30, "∧": 35, "=": 50}


def top_level_connective(result: str) -> str | None:
    """The depth-0 connective that decides the shape of the result after its head.

    A top-level `∧` still proves the residual when it is the left conjunct,
    while `→`, `∨` and `=` only relate the residual to another proposition
    (`R → Q` assumes `R`; `R ∨ Q` and `R = Q` prove neither side).  `=` binds
    tighter than the logical connectives, so a first `=` decides
    (`R = Q ∧ P` is `(R = Q) ∧ P`); otherwise the loosest connective does, so
    `R ∧ Q → P` is `(R ∧ Q) → P` and reports `→`.  When the result starts with
    an identifier, scanning stops at a depth-0 `∀`, `∃`, `λ` or `fun`, whose
    body runs to the end of the result (`R ∧ ∀ x, P x → Q x` reports `∧`).
    """
    s = strip_forall_prefix(result)
    m = HEAD_IDENT_RE.match(s)
    if not m:
        return None
    stop_at_binders = is_ident_char(s[0]) or s[0] in "@«"
    found: list[str] = []
    depth = 0
    i = m.end()
    while i < len(s):
        c = s[i]
        if c in OPEN_BRACKETS:
            depth += 1
        elif c in CLOSE_BRACKETS:
            depth = max(0, depth - 1)
        elif depth == 0:
            if stop_at_binders and (
                c in "∀∃λ"
                or (
                    s.startswith("fun", i)
                    and not is_ident_char(s[i - 1])
                    and s[i + 3 : i + 4].isspace()
                )
            ):
                break
            for conn in TOP_LEVEL_CONNECTIVES:
                if s.startswith(conn, i):
                    found.append(conn)
                    break
        i += 1
    if not found:
        return None
    if found[0] == "=":
        return "="
    return min(found, key=CONNECTIVE_PRECEDENCE.__getitem__)


BOUNDED_BINDER_OPS = ("∈", "∉", "⊆", "⊂", "⊇", "⊃", "≠", "≤", "≥", "<", ">")


def forall_binders(text: str) -> tuple[list[dict], list[str]]:
    """Binder entries and premises of the binder part of a `∀ ...,`."""
    text = text.strip()
    groups = binder_groups(text)
    if groups:
        entries: list[dict] = []
        for opener, content, _close in groups:
            entries.extend(group_entries(opener, content))
        return entries, []
    split = split_top_level_once(text, ":")
    if split is not None:
        names, typ = split
        return [
            {"opener": "(", "name": n, "type": norm_space(typ)} for n in names.split()
        ], []
    flat = flatten_top_level(text)
    for op in BOUNDED_BINDER_OPS:
        idx = flat.find(op)
        if idx != -1:
            names = text[:idx].split()
            return [{"opener": "(", "name": n, "type": ""} for n in names], [norm_space(text)]
    return [{"opener": "(", "name": n, "type": ""} for n in text.split()], []


def arrow_binder(part: str) -> list[dict] | None:
    """Entries when an arrow premise is a dependent binder `(x : T) → ...`."""
    s = part.strip()
    groups = binder_groups(s)
    if len(groups) != 1:
        return None
    opener, content, close = groups[0]
    if not (s.startswith(opener) and s.endswith(close)):
        return None
    if split_top_level_once(content, ":") is None:
        return None
    return group_entries(opener, content)


def _has_relation(text: str) -> bool:
    flat = flatten_top_level(text, scoped=True)
    return bool(BARE_EQUAL_RE.search(flat) or COMPARISON_RE.search(flat) or "≠" in flat)


def conclusion_atoms(result: str) -> list[dict]:
    """Split a result type into its conclusion atoms.

    Each atom is ``{"kind", "text", "premises", "binders"}`` where kind is
    ``atom`` (a plain application), ``negation`` (``¬ X``), ``iff``, ``or``,
    ``relation`` or ``other``.  Premises collect `→` antecedents and bounded
    `∀ x ∈ s` conditions; binders collect `∀` and dependent-arrow binders.
    Precedence follows Lean: `↔` < `→` < `∨` < `∧` < `¬` < relations.
    """
    out: list[dict] = []

    def walk(s: str, premises: list[str], binders: list[dict], depth: int) -> None:
        s = strip_outer_parens(s)
        if depth > 32:
            out.append({"kind": "other", "text": s, "premises": premises, "binders": binders})
            return
        while s.startswith("∀"):
            comma = depth0_index(s, ",")
            if comma is None:
                out.append({"kind": "other", "text": s, "premises": premises, "binders": binders})
                return
            entries, bounded = forall_binders(s[1:comma])
            binders = binders + entries
            premises = premises + bounded
            s = strip_outer_parens(s[comma + 1 :])
        if has_top_level(s, "↔"):
            out.append({"kind": "iff", "text": s, "premises": premises, "binders": binders})
            return
        parts = split_top_level(s, "→")
        if len(parts) > 1:
            new_premises: list[str] = []
            new_binders: list[dict] = []
            for part in parts[:-1]:
                dependent = arrow_binder(part)
                if dependent is not None:
                    new_binders.extend(dependent)
                else:
                    new_premises.append(norm_space(part))
            walk(parts[-1], premises + new_premises, binders + new_binders, depth + 1)
            return
        if has_top_level(s, "∨"):
            out.append({"kind": "or", "text": s, "premises": premises, "binders": binders})
            return
        conjuncts = split_top_level(s, "∧")
        if len(conjuncts) > 1:
            for c in conjuncts:
                walk(c, premises, binders, depth + 1)
            return
        if s.startswith("¬"):
            out.append({"kind": "negation", "text": s, "premises": premises, "binders": binders})
            return
        if _has_relation(s):
            out.append({"kind": "relation", "text": s, "premises": premises, "binders": binders})
            return
        if not atom_head(s) or s.startswith(("∃", "fun", "λ", "Σ", "∑", "∏")):
            out.append({"kind": "other", "text": s, "premises": premises, "binders": binders})
            return
        out.append({"kind": "atom", "text": s, "premises": premises, "binders": binders})

    walk(result.strip(), [], [], 0)
    return out


def negated_target(text: str) -> tuple[str, list[dict]] | None:
    """(plain atom, inner `∀` binders) for `¬ X` when `X` is an application."""
    s = text.strip()
    if not s.startswith("¬"):
        return None
    s = strip_outer_parens(s[1:])
    binders: list[dict] = []
    while s.startswith("∀"):
        comma = depth0_index(s, ",")
        if comma is None:
            return None
        entries, _bounded = forall_binders(s[1:comma])
        binders.extend(entries)
        s = strip_outer_parens(s[comma + 1 :])
    for tok in ("↔", "→", "∨", "∧"):
        if has_top_level(s, tok):
            return None
    if s.startswith("¬") or _has_relation(s) or not atom_head(s):
        return None
    return s, binders


def residual_arguments(atom: str) -> list[tuple[str | None, str]]:
    """Top-level arguments of an application: (name or None, text).

    Named arguments `(x := e)` report `x`; every other argument (bare token or
    bracketed group, brackets kept) is positional.
    """
    s = strip_outer_parens(atom)
    if s.startswith("@"):
        s = s[1:]
    m = HEAD_IDENT_RE.match(s)
    if not m:
        return []
    rest = s[m.end() :]
    args: list[tuple[str | None, str]] = []
    i = 0
    while i < len(rest):
        c = rest[i]
        if c.isspace():
            i += 1
            continue
        if c in OPEN_BRACKETS:
            close = matching_close(rest, i)
            if close is None:
                args.append((None, rest[i:].strip()))
                break
            group = rest[i : close + 1]
            named = re.match(r"\(\s*([^\s:()]+)\s*:=\s*(.+?)\s*\)$", group, re.S)
            if named:
                args.append((named.group(1), norm_space(named.group(2))))
            else:
                args.append((None, norm_space(group)))
            i = close + 1
            continue
        j = i
        stops = OPEN_BRACKETS + CLOSE_BRACKETS
        while j < len(rest) and not rest[j].isspace() and rest[j] not in stops:
            j += 1
        args.append((None, rest[i:j]))
        i = j if j > i else i + 1
    return args


def bare_identifier(text: str) -> str | None:
    """The identifier when `text` is just one (possibly parenthesised)."""
    s = strip_outer_parens(text)
    if s == "_":
        return "_"
    m = IDENT_RE.fullmatch(s)
    return m.group(0) if m else None


def _collapse_parens(tokens: list[str]) -> list[str]:
    """Drop redundant parentheses: `((x))` becomes `(x)`."""
    changed = True
    while changed:
        changed = False
        match: dict[int, int] = {}
        stack: list[int] = []
        for i, tok in enumerate(tokens):
            if tok == "(":
                stack.append(i)
            elif tok == ")" and stack:
                match[stack.pop()] = i
        for i, j in match.items():
            if i + 1 < len(tokens) and tokens[i + 1] == "(" and match.get(i + 1) == j - 1:
                tokens = tokens[:i] + tokens[i + 1 : j] + tokens[j + 1 :]
                changed = True
                break
    return tokens


def alpha_normalize(text: str, bound: set[str]) -> str:
    """Token string of `text` with bound names and universe levels erased."""
    s = UNIVERSE_ARGS_RE.sub("", text)
    s = SORT_LEVEL_RE.sub(r"\1", s)
    tokens = _collapse_parens(TOKEN_RE.findall(s))
    return " ".join("_" if tok in bound else tok for tok in tokens)


def literal_instance(provider_type: str, residual_type: str) -> bool:
    """True when `provider_type` is `residual_type` with some `_` replaced by literals."""
    p = provider_type.split()
    r = residual_type.split()
    if len(p) != len(r) or p == r:
        return False
    changed = False
    for a, b in zip(p, r):
        if a == b:
            continue
        if b == "_" and LITERAL_RE.match(a):
            changed = True
            continue
        return False
    return changed


def command_text(lines: list[str], idx: int, first_rest: str) -> tuple[str, int]:
    """Text of a multi-line command starting at `lines[idx]` and its last line index.

    Continuation lines are indented more deeply than the command's first line;
    blank lines are skipped only when an indented continuation follows them.
    """
    first = lines[idx]
    indent = len(first) - len(first.lstrip())
    parts = [first_rest]
    j = idx + 1
    last = idx
    while j < len(lines):
        ln = lines[j].rstrip("\n")
        if not ln.strip():
            k = j + 1
            while k < len(lines) and not lines[k].strip():
                k += 1
            if k < len(lines) and len(lines[k]) - len(lines[k].lstrip()) > indent:
                j = k
                continue
            break
        if len(ln) - len(ln.lstrip()) <= indent:
            break
        parts.append(ln)
        last = j
        j += 1
    return " ".join(parts), last


def body_until_next_command(body: str) -> str:
    """A declaration body up to the next column-0 line (the next command)."""
    m = re.search(r"\n(?=\S)", body)
    return body[: m.start()] if m else body


def _one_shot(text: str) -> tuple[str, bool]:
    """Strip a trailing `in` modifier; report whether it was present."""
    m = re.search(r"(?:^|\s)in\s*$", text)
    if m:
        return text[: m.start()], True
    return text, False


def _dedupe_vars(entries: list[dict]) -> list[dict]:
    """Keep the innermost declaration of each named section variable."""
    seen: set[str] = set()
    out: list[dict] = []
    for e in reversed(entries):
        name = e["name"]
        if name is not None and name != ANONYMOUS:
            if name in seen:
                continue
            seen.add(name)
        out.append(e)
    out.reverse()
    return out


def parse_file(path: Path, root: Path) -> list[dict]:
    """All top-level-ish declarations in one file, with parsed signatures.

    Section `variable`s, `include` and `omit` commands are tracked per
    namespace/section frame so that each declaration records the section
    variables in scope (see `included_section_entries`).
    """
    text = path.read_text(encoding="utf-8", errors="replace")
    code = strip_comments(text)
    lines = code.splitlines(keepends=True)

    line_starts: list[int] = []
    pos = 0
    for ln in lines:
        line_starts.append(pos)
        pos += len(ln)

    def new_frame(kind: str, name: str | None) -> dict:
        return {
            "kind": kind,
            "name": name,
            "vars": [],
            "includes": set(),
            "omit_names": set(),
            "omit_types": set(),
        }

    file_frame = new_frame("file", None)
    ns_stack: list[dict] = []
    pending = {"vars": [], "includes": set(), "omit_names": set(), "omit_types": set()}
    headers: list[dict] = []
    skip_until = -1
    for idx, raw in enumerate(lines):
        if idx <= skip_until:
            continue
        ln = raw.rstrip("\n")
        m = NAMESPACE_RE.match(ln)
        if m:
            ns_stack.append(new_frame("namespace", m.group(1)))
            continue
        if SECTION_RE.match(ln):
            ns_stack.append(new_frame("section", None))
            continue
        if MUTUAL_RE.match(ln):
            ns_stack.append(new_frame("mutual", None))
            continue
        if END_RE.match(ln):
            if ns_stack:
                ns_stack.pop()
            continue
        frame = ns_stack[-1] if ns_stack else file_frame
        m = VARIABLE_RE.match(ln)
        if m:
            body, skip_until = command_text(lines, idx, m.group(2))
            body, once = _one_shot(body)
            entries = own_entries(body)
            (pending["vars"] if once else frame["vars"]).extend(entries)
            continue
        m = INCLUDE_OMIT_RE.match(ln)
        if m:
            body, skip_until = command_text(lines, idx, m.group(3))
            body, once = _one_shot(body)
            target = pending if once else frame
            if m.group(2) == "include":
                target["includes"].update(re.findall(r"[^\s\[\]()]+", flatten_top_level(body)))
            else:
                for opener, content, _close in binder_groups(body):
                    if opener == "[":
                        target["omit_types"].add(norm_space(content))
                target["omit_names"].update(IDENT_RE.findall(flatten_top_level(body)))
            continue
        m = DECL_RE.match(ln)
        kind = name = None
        if m:
            kind, name, end_name = m.group(1), m.group(2), m.end(2)
        else:
            m = TYPE_DECL_RE.match(ln)
            if m:
                kind, name, end_name = " ".join(m.group(1).split()), m.group(2), m.end(2)
        if kind is None:
            continue
        frames = [file_frame] + ns_stack
        section_vars = [e for f in frames for e in f["vars"]] + pending["vars"]
        includes = set().union(*(f["includes"] for f in frames)) | pending["includes"]
        omit_names = set().union(*(f["omit_names"] for f in frames)) | pending["omit_names"]
        omit_types = set().union(*(f["omit_types"] for f in frames)) | pending["omit_types"]
        pending = {"vars": [], "includes": set(), "omit_names": set(), "omit_types": set()}
        prefix = ".".join(f["name"] for f in ns_stack if f["kind"] == "namespace" and f["name"])
        headers.append(
            {
                "kind": kind,
                "name": name,
                "line": idx + 1,
                "start": line_starts[idx],
                "sig_from": line_starts[idx] + end_name,
                "namespace": prefix,
                "section_vars": _dedupe_vars(section_vars),
                "includes": sorted(includes),
                "omit_names": sorted(omit_names),
                "omit_types": sorted(omit_types),
            }
        )

    decls: list[dict] = []
    rel = path.relative_to(root).as_posix()
    for i, h in enumerate(headers):
        window_end = headers[i + 1]["start"] if i + 1 < len(headers) else len(code)
        window = code[h["sig_from"] : window_end]
        if h["kind"] in {"structure", "class", "class inductive", "inductive"}:
            binders, result, body = "", type_declaration_result(window), ""
        else:
            binders, result, body = split_declaration(window)
            body = body_until_next_command(body)
        name = h["name"]
        fq = f"{h['namespace']}.{name}" if h["namespace"] else name
        decls.append(
            {
                "kind": h["kind"],
                "name": name,
                "fq_name": fq,
                "file": rel,
                "line": h["line"],
                "binders": binders,
                "result": result,
                "body": body if h["kind"] in DEF_LIKE_KINDS else "",
                "section_vars": h["section_vars"],
                "includes": h["includes"],
                "omit_names": h["omit_names"],
                "omit_types": h["omit_types"],
            }
        )
    return decls


def is_prop_valued(result: str) -> bool:
    """True when a declaration's result type is `Prop` or a `Prop`-valued family."""
    s = strip_forall_prefix(norm_space(result))
    parts = split_top_level(s, "→")
    return re.match(r"Prop(?![\w'])", parts[-1].strip()) is not None


def collect(root: Path) -> tuple[list[dict], list[dict], list[dict]]:
    """Return (all decls, census residual rows, near-miss rows)."""
    all_decls: list[dict] = []
    # Relocated classic production declarations and their providers retain the
    # same census status after canonical ownership moves to ArkLib. Research is
    # deliberately outside this historical production-residual census.
    for source_root in ("ArkLib", "ProximityPrize"):
        for f in sorted((root / source_root).rglob("*.lean")):
            if ".lake" in f.parts:
                continue
            all_decls.extend(parse_file(f, root))

    residuals: list[dict] = []
    near_misses: list[dict] = []
    for d in all_decls:
        if d["kind"] not in {"theorem", "lemma", "def", "instance", "abbrev", "opaque"}:
            continue
        last = d["name"].rsplit(".", 1)[-1]
        if "Residual" not in last and "residual" not in last:
            continue
        result_norm = " ".join(d["result"].split())
        strict = d["kind"] == "def" and last.endswith("Residual") and result_norm == "Prop"
        if strict:
            residuals.append(
                {
                    "name": last,
                    "fq_name": d["fq_name"],
                    "file": d["file"],
                    "line": d["line"],
                }
            )
        elif d["kind"] in {"def", "abbrev"}:
            if not last.endswith("Residual"):
                reason = "name does not end in `Residual`"
            elif d["kind"] != "def":
                reason = f"declared as `{d['kind']}`, not `def`"
            else:
                reason = f"result type is `{result_norm or '<none>'}`, not `Prop`"
            near_misses.append(
                {
                    "name": last,
                    "fq_name": d["fq_name"],
                    "kind": d["kind"],
                    "file": d["file"],
                    "line": d["line"],
                    "reason": reason,
                }
            )
    return all_decls, residuals, near_misses


def prop_vocabulary(all_decls: list[dict]) -> tuple[frozenset[str], frozenset[str]]:
    """(last names of in-tree `Prop`-valued declarations, in-tree `Prop` classes)."""
    heads: set[str] = set()
    classes: set[str] = set()
    for d in all_decls:
        if d["kind"] in PROP_DECL_KINDS and is_prop_valued(d["result"]):
            last = d["name"].rsplit(".", 1)[-1]
            heads.add(last)
            if d["kind"].startswith("class"):
                classes.add(last)
    return frozenset(heads), frozenset(classes)


def included_section_entries(decl: dict) -> list[dict]:
    """Section variables Lean adds as parameters of `decl` (approximated).

    A variable is included when it is named by `include`, mentioned in the
    header (for definitions: anywhere in the declaration), a dependency of an
    included variable, or an instance-implicit variable all of whose variable
    dependencies are included; `omit` and shadowing by the declaration's own
    binders exclude it.
    """
    variables = decl.get("section_vars") or []
    if not variables:
        return []
    own_names = {e["name"] for e in own_entries(decl["binders"]) if e["name"]}
    mention_text = decl["binders"] + "\n" + decl["result"]
    if decl["kind"] in DEF_LIKE_KINDS:
        mention_text += "\n" + decl.get("body", "")
    includes = set(decl.get("includes") or [])
    omit_names = set(decl.get("omit_names") or [])
    omit_types = set(decl.get("omit_types") or [])
    var_names = [e["name"] for e in variables if e["name"] and e["name"] != ANONYMOUS]

    def excluded(e: dict) -> bool:
        if e["name"] and (e["name"] in omit_names or e["name"] in own_names):
            return True
        return e["opener"] == "[" and norm_space(e["type"]) in omit_types

    included: set[int] = set()
    for i, e in enumerate(variables):
        name = e["name"]
        if excluded(e) or not name or name == ANONYMOUS:
            continue
        if name in includes or mentions_word(mention_text, name):
            included.add(i)
    changed = True
    while changed:
        changed = False
        for i in sorted(included):
            for j, w in enumerate(variables):
                if j in included or excluded(w) or not w["name"] or w["name"] == ANONYMOUS:
                    continue
                if mentions_word(variables[i]["type"], w["name"]):
                    included.add(j)
                    changed = True
        included_names = {variables[i]["name"] for i in included if variables[i]["name"]}
        for j, w in enumerate(variables):
            if j in included or w["opener"] != "[" or excluded(w):
                continue
            deps = [n for n in var_names if mentions_word(w["type"], n)]
            if all(n in included_names for n in deps):
                included.add(j)
                changed = True
    return [variables[i] for i in sorted(included)]


def effective_entries(decl: dict) -> list[dict]:
    """Included section variables followed by the declaration's own binders."""
    sec = [dict(e, source="section") for e in included_section_entries(decl)]
    own = [dict(e, source="binder") for e in own_entries(decl["binders"])]
    return sec + own


def explicit_parameters(entries: list[dict]) -> list[str]:
    return [e["name"] or "?" for e in entries if e["opener"] == "("]


def _ns_of(fq: str) -> str:
    return fq.rsplit(".", 1)[0] if "." in fq else ""


def _ns_affinity(c_ns: str, p_ns: str) -> bool:
    """Loose namespace kinship between a candidate residual and a provider."""
    if not c_ns or not p_ns:
        return False
    return (
        p_ns == c_ns
        or p_ns.endswith("." + c_ns)
        or c_ns.endswith("." + p_ns)
        or p_ns.split(".")[-1] == c_ns.split(".")[-1]
    )


def _resolve(candidates: list[dict], head_full: str, provider_ns: str) -> tuple[list[dict], bool]:
    """Narrow same-named census rows via a qualified result head or namespace
    affinity.  Returns (rows, ambiguous): ambiguous providers never count as a
    discharge on their own."""
    def ambiguity(rows: list[dict]) -> bool:
        # Same fq name in several files is one logical declaration duplicated,
        # not an ambiguity.
        return len({c["fq_name"] for c in rows}) > 1

    if not ambiguity(candidates):
        return candidates, False
    if "." in head_full:
        qualified = [
            c
            for c in candidates
            if c["fq_name"] == head_full or c["fq_name"].endswith("." + head_full)
        ]
        if qualified:
            return qualified, ambiguity(qualified)
    affine = [c for c in candidates if _ns_affinity(_ns_of(c["fq_name"]), provider_ns)]
    if affine:
        return affine, ambiguity(affine)
    return candidates, True


class _ResidualShape:
    """Parameters of one census residual, as seen by the source scan."""

    def __init__(self, decl: dict | None):
        entries = effective_entries(decl) if decl else []
        self.bound = {e["name"] for e in entries if e["name"]}
        self.explicit = explicit_parameters(entries)
        self.types = {
            e["name"]: alpha_normalize(e["type"], self.bound)
            for e in entries
            if e["name"] and e["name"] != ANONYMOUS and e["type"]
        }
        self.instance_types = [e["type"] for e in entries if e["opener"] == "["]

    def instances(self, keep: set[str]) -> set[str]:
        """Instance binder types, erasing bound names except those in `keep`."""
        erase = self.bound - keep
        return {alpha_normalize(t, erase) for t in self.instance_types}


def _argument_label(index: int, name: str | None, explicit: list[str], positional: int) -> str:
    if name is not None:
        return name
    if positional < len(explicit) and explicit[positional] != "?":
        return explicit[positional]
    return f"#{index + 1}"


def _short(text: str, limit: int = 120) -> str:
    text = norm_space(text)
    return text if len(text) <= limit else text[: limit - 1] + "…"


def assess(
    atom: dict,
    eff: list[dict],
    shape: _ResidualShape,
    census_names: list[str],
    prop_heads: frozenset[str],
    prop_classes: frozenset[str],
    refutation: bool = False,
    extra_bound: frozenset[str] | set[str] = frozenset(),
) -> dict:
    """Assumptions and specialisations of one declaration for one residual atom.

    `extra_bound` names variables bound inside the atom itself (the `∀` under a
    negation `¬ ∀ k, R k`); they are arguments, not assumptions.
    """
    entries = eff + [dict(e, source="result") for e in atom["binders"]]
    bound = {e["name"] for e in entries if e["name"]} | set(extra_bound)
    text = atom["text"]
    args = residual_arguments(text)
    argument_names = {bare_identifier(t) for _n, t in args} - {None, "_"}

    def mentioned(name: str | None) -> bool:
        return bool(name) and name != ANONYMOUS and (
            name in argument_names or mentions_word(text, name)
        )

    consumed: set[str] = set()
    extra: set[str] = set()
    section_hyps: set[str] = set()
    instances: list[str] = []
    # Names bound by both declarations are taken to denote the same parameter;
    # other bound names are erased, so renamed type variables still compare.
    keep = bound & shape.bound
    residual_instances = shape.instances(keep)
    for e in entries:
        if e["opener"] == "[":
            normalized = alpha_normalize(e["type"], bound - keep)
            head = type_head_last(e["type"])
            if normalized in residual_instances or head in ALWAYS_SATISFIABLE_CLASSES:
                continue
            if refutation and head not in KNOWN_PROP_CLASSES and head not in prop_classes:
                continue
            instances.append(norm_space(e["type"]))
            continue
        if mentioned(e["name"]):
            continue
        for n in census_names:
            if mentions_word(e["type"], n):
                consumed.add(n)
        if looks_like_proof_assumption([e["name"] or ANONYMOUS], e["type"], prop_heads):
            extra.add(e["name"] or ANONYMOUS)
            if e.get("source") == "section":
                section_hyps.add(e["name"] or ANONYMOUS)
    for premise in atom["premises"]:
        for n in census_names:
            if mentions_word(premise, n):
                consumed.add(n)

    specialised: list[str] = []
    seen: dict[str, str] = {}
    positional = 0
    for index, (name, arg) in enumerate(args):
        label = _argument_label(index, name, shape.explicit, positional)
        if name is None:
            positional += 1
        ident = bare_identifier(arg)
        if ident == "_":
            continue
        if ident is not None and ident in bound:
            if ident in seen:
                specialised.append(f"{label} := {ident} (same as {seen[ident]})")
            seen[ident] = label
            continue
        specialised.append(f"{label} := {_short(arg, 80)}")
    parameter_types: list[str] = []
    for e in entries:
        name = e["name"]
        if not name or name == ANONYMOUS or name not in shape.types or not e["type"]:
            continue
        mine = alpha_normalize(e["type"], bound)
        if literal_instance(mine, shape.types[name]):
            parameter_types.append(f"{name} : {_short(e['type'], 80)}")
    return {
        "conditional_on_residuals": sorted(consumed),
        "extra_explicit_binders": sorted(extra),
        "section_hypotheses": sorted(section_hyps),
        "result_premises": [_short(p) for p in atom["premises"]],
        "extra_instance_assumptions": sorted(set(instances)),
        "specialised_arguments": specialised,
        "specialised_parameter_types": parameter_types,
    }


VERDICT_RANK = {
    "uniform": 0,
    "unconditional": 0,
    "instance": 1,
    "conditional": 2,
    "ambiguous": 3,
    "not_provider": 4,
}


def provider_verdict(p: dict) -> str:
    if p.get("equivalence") or p.get("reduction_only"):
        return "not_provider"
    if p.get("ambiguous_name_match"):
        return "ambiguous"
    if (
        p.get("conditional_on_residuals")
        or p.get("extra_explicit_binders")
        or p.get("result_premises")
        or p.get("extra_instance_assumptions")
    ):
        return "conditional"
    if p.get("specialised_arguments") or p.get("specialised_parameter_types"):
        return "instance"
    return "uniform"


def refutation_verdict(p: dict) -> str:
    if p.get("ambiguous_name_match"):
        return "ambiguous"
    if (
        p.get("conditional_on_residuals")
        or p.get("extra_explicit_binders")
        or p.get("result_premises")
        or p.get("extra_instance_assumptions")
    ):
        return "conditional"
    return "unconditional"


def find_providers(all_decls: list[dict], residuals: list[dict]) -> None:
    """Attach providers/refutations + status to each census row, in place."""
    census_names = sorted({r["name"] for r in residuals})
    by_name: dict[str, list[dict]] = {}
    for r in residuals:
        r["providers"] = []
        r["refutations"] = []
        by_name.setdefault(r["name"], []).append(r)

    decl_at = {(d["file"], d["line"]): d for d in all_decls}
    def_sites = {(r["file"], r["line"]) for r in residuals}
    shapes = {
        (r["file"], r["line"]): _ResidualShape(decl_at.get((r["file"], r["line"])))
        for r in residuals
    }
    prop_heads, prop_classes = prop_vocabulary(all_decls)
    prop_heads = prop_heads | frozenset(census_names)

    for d in all_decls:
        if d["kind"] not in PROVIDER_KINDS:
            continue
        if (d["file"], d["line"]) in def_sites:
            continue  # the residual definition itself is never its provider
        atoms = conclusion_atoms(d["result"])
        provider_ns = _ns_of(d["fq_name"])

        candidates: dict[str, list[tuple[str, dict]]] = {}
        refuted: dict[str, list[tuple[str, dict]]] = {}
        for atom in atoms:
            if atom["kind"] == "atom":
                head = atom_head(atom["text"])
                last = head.rsplit(".", 1)[-1]
                if last in by_name:
                    candidates.setdefault(last, []).append((head, atom))
            elif atom["kind"] == "negation":
                target = negated_target(atom["text"])
                if target is None:
                    continue
                inner, inner_binders = target
                head = atom_head(inner)
                last = head.rsplit(".", 1)[-1]
                if last in by_name:
                    # Binders under the negation (`¬ ∀ k, R k`) are part of the
                    # refuted proposition, not assumptions of the refutation.
                    refuted.setdefault(last, []).append(
                        (head, dict(atom, text=inner, inner_binders=inner_binders))
                    )

        whole_head = result_head(d["result"])
        whole_last = whole_head.rsplit(".", 1)[-1]
        related_only = whole_last in by_name and whole_last not in candidates
        if not candidates and not refuted and not related_only:
            continue
        eff = effective_entries(d)

        if related_only:
            stripped = strip_forall_prefix(d["result"])
            equivalence = has_top_level(stripped, "↔")
            rows, ambiguous = _resolve(by_name[whole_last], whole_head, provider_ns)
            for row in rows:
                record = {
                    "name": d["fq_name"],
                    "kind": d["kind"],
                    "file": d["file"],
                    "line": d["line"],
                    "conditional_on_residuals": [],
                    "extra_explicit_binders": [],
                    "ambiguous_name_match": ambiguous,
                    "equivalence": equivalence,
                    "reduction_only": not equivalence,
                    "specialised_arguments": [],
                    "result_premises": [],
                    "section_hypotheses": [],
                    "extra_instance_assumptions": [],
                    "specialised_parameter_types": [],
                }
                record["verdict"] = provider_verdict(record)
                row["providers"].append(record)

        for rname, hits in candidates.items():
            for head, atom in hits:
                head_for_resolution = head if "." in head else ""
                rows, ambiguous = _resolve(by_name[rname], head_for_resolution, provider_ns)
                for row in rows:
                    shape = shapes[(row["file"], row["line"])]
                    found = assess(atom, eff, shape, census_names, prop_heads, prop_classes)
                    record = {
                        "name": d["fq_name"],
                        "kind": d["kind"],
                        "file": d["file"],
                        "line": d["line"],
                        "conditional_on_residuals": found["conditional_on_residuals"],
                        "extra_explicit_binders": found["extra_explicit_binders"],
                        "ambiguous_name_match": ambiguous,
                        "equivalence": False,
                        "reduction_only": False,
                        "specialised_arguments": found["specialised_arguments"],
                        "result_premises": found["result_premises"],
                        "section_hypotheses": found["section_hypotheses"],
                        "extra_instance_assumptions": found["extra_instance_assumptions"],
                        "specialised_parameter_types": found["specialised_parameter_types"],
                    }
                    record["verdict"] = provider_verdict(record)
                    row["providers"].append(record)

        for rname, hits in refuted.items():
            for head, atom in hits:
                head_for_resolution = head if "." in head else ""
                rows, ambiguous = _resolve(by_name[rname], head_for_resolution, provider_ns)
                for row in rows:
                    shape = shapes[(row["file"], row["line"])]
                    inner_bound = {e["name"] for e in atom["inner_binders"] if e["name"]}
                    found = assess(
                        atom,
                        eff,
                        shape,
                        census_names,
                        prop_heads,
                        prop_classes,
                        refutation=True,
                        extra_bound=inner_bound,
                    )
                    record = {
                        "name": d["fq_name"],
                        "kind": d["kind"],
                        "file": d["file"],
                        "line": d["line"],
                        "conditional_on_residuals": found["conditional_on_residuals"],
                        "extra_explicit_binders": found["extra_explicit_binders"],
                        "ambiguous_name_match": ambiguous,
                        "result_premises": found["result_premises"],
                        "section_hypotheses": found["section_hypotheses"],
                        "extra_instance_assumptions": found["extra_instance_assumptions"],
                        "refuted_arguments": found["specialised_arguments"],
                    }
                    record["verdict"] = refutation_verdict(record)
                    row["refutations"].append(record)

    def dedupe_entries(entries: list[dict]) -> list[dict]:
        best: dict[tuple, dict] = {}
        order: list[tuple] = []
        for p in sorted(entries, key=lambda p: (p["file"], p["line"], p["name"])):
            key = (p["name"], p["file"], p["line"])
            if key not in best:
                best[key] = p
                order.append(key)
                continue
            if VERDICT_RANK[p["verdict"]] < VERDICT_RANK[best[key]["verdict"]]:
                best[key] = p
        return [best[k] for k in order]

    for r in residuals:
        r["providers"] = dedupe_entries(r["providers"])
        r["refutations"] = dedupe_entries(r["refutations"])
        verdicts = {p["verdict"] for p in r["providers"]}
        if any(p["verdict"] == "unconditional" for p in r["refutations"]):
            r["status"] = "refuted"
        elif "uniform" in verdicts:
            r["status"] = "discharged"
        elif "instance" in verdicts:
            r["status"] = "instance_only"
        else:
            r["status"] = "open"


def top_dir(file: str) -> str:
    parts = Path(file).parts
    if parts[:2] == ("ProximityPrize", "Extensions"):
        parts = parts[1:]
    return parts[1] if len(parts) > 2 else "(root)"


def summarize(residuals: list[dict]) -> dict:
    by_dir: dict[str, dict[str, int]] = {}
    for r in residuals:
        d = by_dir.setdefault(top_dir(r["file"]), {"total": 0, **{s: 0 for s in STATUSES}})
        d["total"] += 1
        d[r["status"]] += 1
    out: dict = {"total": len(residuals)}
    for s in STATUSES:
        out[s] = sum(1 for r in residuals if r["status"] == s)
    out["by_top_dir"] = dict(sorted(by_dir.items()))
    return out


METADATA = {
    "kind": "syntactic inventory",
    "scope": SCOPE,
    "source_roots": ["ArkLib", "ProximityPrize"],
    "method": (
        "Lean source text is scanned without elaboration; binders, section variables, "
        "instances and result types are read as text."
    ),
    "caveat": (
        "Labels are conservative triage heuristics, not kernel-checked facts. `discharged` "
        "marks a candidate uniform provider to review, not a verified proof, and these totals "
        "are not a whole-project or production-completion ledger: Research/ residuals and named "
        "hypotheses outside the strict `def ...Residual ... : Prop` pattern are not counted."
    ),
    "statuses": {
        "open": "no unconditional provider or refutation was recognised",
        "instance_only": "only providers of specific instances (literal/compound arguments, "
        "repeated bound names, or literal parameter types) were recognised",
        "discharged": "a candidate uniform provider with no recognised assumption was found",
        "refuted": "a declaration with no recognised assumption proves the negation of some "
        "instance, so the family is not uniformly true; proved instances stay listed",
    },
    "provider_verdicts": {
        "uniform": "no recognised assumption; every residual argument is a distinct bound name",
        "instance": "no recognised assumption, but only an instance of the residual is proved",
        "conditional": "assumes a census residual, a proof-like binder, a result premise, an "
        "included proof-like section variable, or an instance missing from the residual",
        "ambiguous": "the residual name could not be resolved across namespaces",
        "not_provider": "the residual heads the result only as one side of ↔, →, ∨ or =",
    },
}


def conditional_notes(r: dict) -> str:
    """Human-readable summary of why available providers are conditional."""
    providers = [p for p in r["providers"] if p.get("verdict") == "conditional"]
    conds = sorted({c for p in providers for c in p["conditional_on_residuals"]})
    binders = sorted({b for p in providers for b in p.get("extra_explicit_binders", [])})
    instances = sorted({b for p in providers for b in p.get("extra_instance_assumptions", [])})
    premises = sum(1 for p in providers if p.get("result_premises"))
    notes = []
    if conds:
        notes.append(f"residual deps: {', '.join(f'`{c}`' for c in conds)}")
    if binders:
        notes.append(f"extra assumptions: {', '.join(f'`{b}`' for b in binders)}")
    if instances:
        shown = ", ".join(f"`[{_short(b, 60)}]`" for b in instances[:6])
        more = f" and {len(instances) - 6} more" if len(instances) > 6 else ""
        notes.append(f"instance assumptions: {shown}{more}")
    if premises:
        notes.append(f"result premises in {premises} provider(s)")
    return "; ".join(notes)


def _scope_label(p: dict, key: str = "specialised_arguments") -> str:
    parts = list(p.get(key, [])) + list(p.get("specialised_parameter_types", []))
    return ", ".join(f"`{_short(s, 70)}`" for s in parts)


def instance_labels(r: dict, limit: int = 4) -> list[str]:
    rows = [p for p in r["providers"] if p.get("verdict") == "instance"]
    out = [
        f"`{p['name']}` ({p['file']}:{p['line']}) at {_scope_label(p)}" for p in rows[:limit]
    ]
    if len(rows) > limit:
        out.append(f"and {len(rows) - limit} more")
    return out


def concrete_refutation_labels(r: dict) -> list[str]:
    refs = [p for p in r.get("refutations", []) if p.get("verdict") == "unconditional"]
    out = []
    for p in refs:
        at = _scope_label(p, "refuted_arguments")
        suffix = f" at {at}" if at else ""
        out.append(f"`{p['name']}` ({p['file']}:{p['line']}){suffix}")
    return out


def uniform_labels(r: dict, limit: int = 3) -> list[str]:
    rows = [p for p in r["providers"] if p.get("verdict") == "uniform"]
    out = [f"`{p['name']}` ({p['file']}:{p['line']})" for p in rows[:limit]]
    if len(rows) > limit:
        out.append(f"and {len(rows) - limit} more")
    return out


SECTION_TITLES = {
    "open": "Open Residuals",
    "instance_only": "Instance-Only Residuals",
    "discharged": "Discharged Residuals (syntactic candidates)",
    "refuted": "Refuted Residuals",
}


def markdown_for_status(residuals: list[dict], status: str) -> list[str]:
    rows = [r for r in residuals if r["status"] == status]
    out: list[str] = [f"## {SECTION_TITLES[status]}", ""]
    if not rows:
        return out + ["None.", ""]
    for r in rows:
        suffix = ""
        if status == "open":
            notes = conditional_notes(r)
            if notes:
                suffix = f" — conditional providers only ({notes})"
        elif status == "instance_only":
            suffix = " — proved instances only: " + "; ".join(instance_labels(r))
        elif status == "refuted":
            refs = concrete_refutation_labels(r)
            if refs:
                suffix = f" — refuted by {', '.join(refs)}"
            proved = instance_labels(r)
            if proved:
                suffix += "; proved instances: " + "; ".join(proved)
        elif status == "discharged":
            suffix = " — candidate provider: " + ", ".join(uniform_labels(r))
        out.append(f"- `{r['fq_name']}` — `{r['file']}:{r['line']}`{suffix}")
    out.append("")
    return out


def markdown_for_near_misses(near_misses: list[dict]) -> list[str]:
    """Human-readable list of residual-like declarations outside the strict pattern."""
    out: list[str] = ["## Residual-Like Near Misses", ""]
    if not near_misses:
        return out + ["None.", ""]
    out.extend(
        [
            "These declarations contain `Residual`/`residual` in their name but are outside the",
            "strict `def ...Residual ... : Prop` census convention. They are not counted in the",
            "strict totals, but they are still audit surfaces for hidden proof debt and naming",
            "drift.",
            "",
        ]
    )
    for r in near_misses:
        out.append(
            f"- `{r['fq_name']}` — `{r['file']}:{r['line']}` — "
            f"`{r['kind']}`; {r['reason']}"
        )
    out.append("")
    return out


def extract_campaign_addenda(path: Path) -> list[str]:
    """Hand-maintained "Campaign addendum" blockquotes from the ledger currently
    at `path`, carried forward so regeneration does not silently erase them.

    A blockquote is a contiguous run of `>`-prefixed lines; only runs whose
    first line starts with `CAMPAIGN_ADDENDUM_PREFIX` are kept, in file order.
    Other blockquotes (for example a dated "Regeneration note") are specific
    to the run that produced them and are correctly left to be dropped.
    """
    if not path.is_file():
        return []
    blocks: list[str] = []
    current: list[str] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if line.startswith(">"):
            current.append(line)
            continue
        if current:
            if current[0].startswith(CAMPAIGN_ADDENDUM_PREFIX):
                blocks.append("\n".join(current))
            current = []
    if current and current[0].startswith(CAMPAIGN_ADDENDUM_PREFIX):
        blocks.append("\n".join(current))
    return blocks


WIKI_HEADER = [
    "# ArkLib Residual Census (auto-generated syntactic inventory, v5)",
    "",
    "Generated by `python3 scripts/residual_census.py --wiki-out docs/wiki/residual-census.md`.",
    "",
    "**Scope.** Only `ArkLib/**/*.lean` and `ProximityPrize/**/*.lean` (including relocated",
    "classic extensions) are scanned, and only declarations of the strict form",
    "`def ...Residual ... : Prop` are counted. Residuals under `Research/` (including migrated",
    "campaign residuals) and named `Prop`/`structure` hypotheses outside the suffix convention",
    "are not counted, so these totals are neither a whole-project inventory nor a",
    "production-completion ledger.",
    "",
    "**Method.** The census reads Lean source text and never elaborates a declaration. Every",
    "label is a conservative triage heuristic, not a kernel-checked fact:",
    "",
    "- **discharged** — a candidate *uniform* provider was found: the residual is a conclusion",
    "  of its result (not one side of `↔`, a premise of `→`, a disjunct or an equation side),",
    "  every argument of the residual is a distinct bound name, and no assumption was recognised",
    "  (no census residual, proof-like binder, result premise, included proof-like section",
    "  `variable`, or instance binder missing from the residual's own binders). The listed",
    "  candidate still needs review: elaborated types and unrecognised side conditions are",
    "  invisible to a source scan.",
    "- **instance-only** — only unconditional providers of *instances* were found (an argument",
    "  fixed to a literal or compound term, a bound name passed twice, or a parameter type",
    "  specialised to a literal such as `ProtocolSpec 0`). The proved regimes are listed, but the",
    "  general residual is not discharged.",
    "- **refuted** — a declaration with no recognised assumption proves the negation of some",
    "  instance, so the residual family is not uniformly true. A refutation outranks every",
    "  provider; proved instances stay listed, since an instance proof next to an instance",
    "  refutation is mixed parameter-scope coverage, not a contradiction.",
    "- **open** — everything else, including residuals with conditional providers only.",
    "",
    "The named-residual convention is a modularity pattern, not an incompleteness marker:",
    "check this census before treating a `*Residual` name as open proof debt, and check the",
    "listed provider before treating a `discharged` label as a proof.",
    "",
]

ADDENDA_NOTE = [
    "The campaign addenda below are hand-maintained notes that regeneration carries forward",
    "verbatim. Each describes the dated snapshot it names; none of them is the current generated",
    "summary, which follows the addenda.",
    "",
]


def write_wiki_markdown(path: Path, summary: dict, residuals: list[dict], near_misses: list[dict]) -> None:
    """Write the human-facing residual ledger from the same payload as JSON."""
    lines: list[str] = list(WIKI_HEADER)
    addenda = extract_campaign_addenda(path)
    if addenda:
        lines.extend(ADDENDA_NOTE)
    for block in addenda:
        lines.extend(block.split("\n"))
        lines.append("")
    lines.extend(
        [
            "## Summary",
            "",
            f"- **Total strict residuals (`ArkLib/` and `ProximityPrize/`):** {summary['total']}",
            f"- **Open:** {summary['open']}",
            f"- **Instance-only:** {summary['instance_only']}",
            f"- **Discharged (syntactic candidates):** {summary['discharged']}",
            f"- **Refuted:** {summary['refuted']}",
            f"- **Residual-like near misses:** {len(near_misses)} (listed below and in `scripts/residual_census.json`)",
            "",
            "| top-level directory | total | open | instance-only | discharged | refuted |",
            "|---|---:|---:|---:|---:|---:|",
        ]
    )
    for name, c in summary["by_top_dir"].items():
        lines.append(
            f"| `{name}` | {c['total']} | {c['open']} | {c['instance_only']} | "
            f"{c['discharged']} | {c['refuted']} |"
        )
    lines.append("")
    lines.extend(markdown_for_status(residuals, "open"))
    lines.extend(markdown_for_status(residuals, "instance_only"))
    lines.extend(markdown_for_near_misses(near_misses))
    lines.extend(markdown_for_status(residuals, "refuted"))
    lines.extend(markdown_for_status(residuals, "discharged"))
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines).rstrip() + "\n", encoding="utf-8")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="ArkLib checkout root (default: parent of scripts/)",
    )
    ap.add_argument(
        "--out",
        type=Path,
        default=None,
        help="JSON output path (default: scripts/residual_census.json)",
    )
    ap.add_argument(
        "--wiki-out",
        type=Path,
        default=None,
        help="Optional Markdown ledger output path (for docs/wiki/residual-census.md)",
    )
    args = ap.parse_args()

    root = args.root.expanduser().resolve()
    out_path = args.out or root / "scripts" / "residual_census.json"

    all_decls, residuals, near_misses = collect(root)
    find_providers(all_decls, residuals)
    residuals.sort(key=lambda r: (r["file"], r["line"]))
    near_misses.sort(key=lambda r: (r["file"], r["line"]))
    summary = summarize(residuals)

    payload_residuals = []
    for r in residuals:
        row = dict(r)
        if not row.get("refutations"):
            row.pop("refutations", None)
        payload_residuals.append(row)
    payload = {
        "metadata": METADATA,
        "summary": summary,
        "residuals": payload_residuals,
        "near_misses": near_misses,
    }
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(
        json.dumps(payload, indent=1, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    if args.wiki_out is not None:
        wiki_out = args.wiki_out
        if not wiki_out.is_absolute():
            wiki_out = root / wiki_out
        write_wiki_markdown(wiki_out, summary, residuals, near_misses)

    print(
        f"residual census ({SCOPE}; syntactic heuristic, not a verified ledger): "
        f"total {summary['total']} | open {summary['open']} | "
        f"instance-only {summary['instance_only']} | "
        f"discharged (candidates) {summary['discharged']} | refuted {summary['refuted']}"
    )
    print("\nby top-level directory (total / open / instance-only / discharged / refuted):")
    for name, c in summary["by_top_dir"].items():
        print(
            f"  {name:<16} {c['total']:>3} / {c['open']:>3} / {c['instance_only']:>3} / "
            f"{c['discharged']:>3} / {c['refuted']:>3}"
        )

    for status, title in (
        ("open", "open residual(s)"),
        ("instance_only", "instance-only residual(s)"),
        ("refuted", "refuted residual(s)"),
    ):
        rows = [r for r in residuals if r["status"] == status]
        if not rows:
            continue
        print(f"\n{len(rows)} {title}:")
        for r in rows:
            if status == "open":
                notes = conditional_notes(r)
                extra = f"  [only conditional providers, {notes}]" if notes else ""
            elif status == "instance_only":
                extra = "  [instances: " + "; ".join(instance_labels(r, limit=2)) + "]"
            else:
                refs = concrete_refutation_labels(r)
                extra = f"  [refuted by: {', '.join(refs)}]" if refs else ""
            print(f"  {r['fq_name']}  ({r['file']}:{r['line']}){extra}")
    if near_misses:
        print(
            f"\nnote: {len(near_misses)} residual-like def(s) outside the strict pattern "
            "(see near_misses in JSON)"
        )
    print(f"\nwrote {out_path}")
    if args.wiki_out is not None:
        print(f"wrote {wiki_out}")
    return 0


if __name__ == "__main__":
    configure_stdio()
    sys.exit(main())
