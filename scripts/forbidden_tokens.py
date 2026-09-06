#!/usr/bin/env python3
"""Reject axiom-laundering tokens in live library and research source.

By default, scans every .lean file under ArkLib/ and Research/. If one or more paths are
provided, scans only those Lean files/directories. Fails if live
(non-comment) code contains:
  - `native_decide` / `bv_decide` (kernel-bypassing decision procedures), or
  - a custom `axiom` declaration whose name is not an allowlisted, documented
    residual (see scripts/residual_axioms.txt), or
  - a `theorem`/`lemma` whose statement type is exactly `True` (a vacuous
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

Comment and docstring occurrences are ignored. `sorry`/`admit` are handled
separately by scripts/sorry_census.py --fail-on-holes; this precheck runs
before any Lean toolchain is set up, so CI fails fast on laundering attempts.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

TOKEN_RE = re.compile(r"\b(native_decide|bv_decide)\b")
# Capture the declared axiom name so it can be checked against the residual
# allowlist. The name may be namespaced/contain primes; we keep the simple
# token as written at the declaration site.
AXIOM_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:protected\s+|private\s+|scoped\s+)*axiom\s+"
    r"([A-Za-z_][A-Za-z0-9_'.]*)"
)
DECL_RE = re.compile(
    # Keep leading indentation on one line: masked block comments can contain
    # thousands of whitespace-only lines, making ^\s* retry their whole suffix.
    r"^[ \t]*(?:@\[[^\]]*\]\s*)?"
    r"(?:protected\s+|private\s+|scoped\s+|noncomputable\s+)*"
    r"(axiom|theorem|lemma|def|abbrev|opaque|constant)\s+([A-Za-z_][A-Za-z0-9_'.]*)",
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
# vacuous `True`. Anchored at a line start (after optional attributes/modifiers)
# so it matches a real declaration, not an in-proof `have … : True`.
PLACEBO_DECL_RE = re.compile(
    r"(?m)^[ \t]*(?:@\[[^\]]*\]\s*)*"
    r"(?:noncomputable\s+|protected\s+|private\s+|scoped\s+|local\s+|partial\s+|unsafe\s+)*"
    r"(theorem|lemma)\s+([A-Za-z_][A-Za-z0-9_'.]*)"
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


def comment_mask(text: str) -> list[bool]:
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
        or final.endswith("_residual")
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


def top_level_result_type(header: str) -> str | None:
    """Return the text after the last top-level ':' in a declaration header."""
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
    if last_colon is None:
        return None
    return strip_outer_parens(header[last_colon + 1:])


def declaration_header_end(live_text: str, start: int, next_decl_start: int | None) -> int:
    """Best-effort end offset for a Lean declaration header."""
    limit = next_decl_start if next_decl_start is not None else len(live_text)
    candidates = [pos for token in (":=", " where") if (pos := live_text.find(token, start, limit)) != -1]
    if candidates:
        return min(candidates)
    return limit


def find_true_placebos(text: str, mask: list[bool]) -> list[tuple[int, str]]:
    """Find `theorem`/`lemma` declarations whose statement type is exactly `True`.

    Returns a list of `(line, name)`. Comment/docstring characters are blanked
    first (newlines preserved, so line numbers stay accurate). For each
    declaration head we walk its signature tracking bracket depth, locate the
    top-level statement colon (binder colons live inside brackets) and the
    top-level `:=` that begins the proof, and flag it when the type between them
    is exactly `True`. Stopping at `:=` keeps in-proof `have … : True := …`
    steps from being mistaken for the declaration's statement.
    """
    live = "".join(
        ch if (ch == "\n" or not masked) else " "
        for ch, masked in zip(text, mask)
    )
    decls = list(PLACEBO_DECL_RE.finditer(live))
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
                    if stmt_colon != -1 and live[stmt_colon + 1:i].strip() == "True":
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
    for path in files:
        text = path.read_text(encoding="utf-8", errors="replace")
        mask = comment_mask(text)
        live_text = "".join(
            ch if (ch == "\n" or not mask[i]) else " "
            for i, ch in enumerate(text)
        )
        for m in TOKEN_RE.finditer(text):
            if not mask[m.start()]:
                line = text.count("\n", 0, m.start()) + 1
                failures.append(f"{path}:{line}: forbidden token {m.group(1)}")
        decls = list(DECL_RE.finditer(live_text))
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
            if result_type == "True":
                line = text.count("\n", 0, dm.start()) + 1
                failures.append(
                    f"{path}:{line}: obligation-like name {name} is declared as "
                    f"a vacuous {kind} of type True; keep real residual debt as an "
                    f"explicit axiom/Prop, or remove the allowlist entry"
                )
        pos = 0
        for idx, line in enumerate(text.splitlines(True), start=1):
            first_live = next((off for off, ch in enumerate(line) if not ch.isspace()), None)
            if first_live is None or mask[pos + first_live]:
                pos += len(line)
                continue
            am = AXIOM_RE.match(line)
            if am:
                name = am.group(1)
                if is_allowlisted(name, allowlist):
                    seen_allowed.add(simple_name(name))
                    allowed_hits.append(f"{path}:{idx}: allowed documented residual axiom {name}")
                else:
                    failures.append(
                        f"{path}:{idx}: forbidden custom axiom declaration {name} "
                        f"(add to scripts/residual_axioms.txt only if it is a documented, "
                        f"tracked residual)"
                    )
            pos += len(line)

        for line_no, name in find_true_placebos(text, mask):
            failures.append(
                f"{path}:{line_no}: forbidden vacuous placebo "
                f"`theorem/lemma {name} : True` proves nothing about the named "
                f"obligation (axiom-laundering pattern, #169/#171). Prove the real "
                f"statement or track it by its GitHub issue, not a `True` theorem."
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
        "undocumented custom axiom / vacuous `: True` placebo; "
        f"{len(allowed_hits)} allowlisted residual axiom(s))"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
