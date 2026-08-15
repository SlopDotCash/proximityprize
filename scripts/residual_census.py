#!/usr/bin/env python3
"""Residual census for the ArkLib source tree.

ArkLib encodes open proof obligations as named Prop definitions:

  def <Name>Residual ... : Prop := ...

End-to-end theorems consume these as hypotheses; the mission metric is the
number of *open* residuals falling over time.  This script inventories every
`def` under ArkLib/ whose name ends in `Residual` and whose result type is
exactly `Prop` (multiline signatures handled), then conservatively classifies
each as:

  discharged — a concrete providing declaration exists: a theorem/def
               elsewhere whose *result type* head is that residual (this
               covers `: <Name>Residual ...` providers, including ones proved
               by anonymous constructor `⟨...⟩`), or a `<name>_holds*` /
               `<name>_proved*` theorem whose result mentions the residual.
               Providers whose own hypotheses consume a census residual, or
               whose explicit non-instance binders are extra assumptions not
               appearing in the provided residual instance, are recorded but do
               NOT count as a discharge (a conditional reduction is not a
               proof).  When several census residuals share a last name across
               namespaces, a provider is narrowed via its qualified result head
               or namespace affinity; if it stays ambiguous it is recorded but
               does not discharge.
  refuted    — a concrete declaration proves a negated instance of the residual
               (for example `theorem ..._false : ¬ FooResidual ...`).  This is
               not a discharge; it means the statement surface is known false
               or too broad and should be repaired/retired rather than carried
               as open proof debt.
  open       — everything else.

A residual name appearing only in hypothesis position (`(h : <Name>Residual
...)`) is consumption, not provision, and never counts.

Residual-like defs that miss the strict pattern (name contains `Residual` /
`residual` but not as a `Residual` suffix, or suffix-matching defs whose
result type is not literally `Prop`) are reported as near-misses but kept out
of the census.

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
NAMESPACE_RE = re.compile(r"^\s*namespace\s+(\S+)")
SECTION_RE = re.compile(r"^\s*(?:noncomputable\s+)?section(?:\s+(\S+))?\s*$")
END_RE = re.compile(r"^\s*end(?:\s+(\S+))?\s*$")
HEAD_IDENT_RE = re.compile(r"[^\s({\[⦃⟨:,]+")

OPEN_BRACKETS = "([{⟨⦃"
CLOSE_BRACKETS = ")]}⟩⦄"

PROVIDER_KINDS = {"theorem", "lemma", "def", "instance"}

CAMPAIGN_ADDENDUM_PREFIX = "> **Campaign addendum"


def strip_comments(text: str) -> str:
    """Blank out line comments, block comments, and docstrings (newlines kept)."""
    out = list(text)
    i, n, depth = 0, len(text), 0
    while i < n:
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


def split_signature(window: str) -> tuple[str, str]:
    """Split a declaration tail (after the name) into (binders, result type).

    The signature colon is the first `:` at bracket depth 0 that is not part
    of `:=`; the signature ends at the first depth-0 `:=`.  Bracket depth
    tracks (), [], {}, ⟨⟩, ⦃⦄ so binder-internal colons and named arguments
    `(k := k)` are skipped.
    """
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
    if sig_colon is None:
        return window[:end], ""
    return window[:sig_colon], window[sig_colon + 1 : end]


def strip_forall_prefix(result: str) -> str:
    """Strip leading `∀ ...,` binders from a result type."""
    s = result.strip()
    for _ in range(8):
        if not s.startswith("∀"):
            break
        depth = 0
        for i, c in enumerate(s):
            if c in OPEN_BRACKETS:
                depth += 1
            elif c in CLOSE_BRACKETS:
                depth = max(0, depth - 1)
            elif c == "," and depth == 0:
                s = s[i + 1 :].strip()
                break
        else:
            return ""
    return s


def result_head(result: str) -> str:
    """Head identifier of a result type, stripping leading `∀ ...,` binders."""
    s = strip_forall_prefix(result)
    m = HEAD_IDENT_RE.match(s)
    return m.group(0) if m else ""


def split_top_level_once(text: str, sep: str) -> tuple[str, str] | None:
    """Split at the first top-level separator inside one binder group."""
    depth = 0
    for i, c in enumerate(text):
        if c in OPEN_BRACKETS:
            depth += 1
        elif c in CLOSE_BRACKETS:
            depth = max(0, depth - 1)
        elif c == sep and depth == 0:
            return text[:i], text[i + 1 :]
    return None


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


def binder_names_and_type(content: str) -> tuple[list[str], str] | None:
    """Names and type introduced by a binder group with a top-level type colon."""
    split = split_top_level_once(content, ":")
    if split is None:
        return None
    names, typ = split
    out: list[str] = []
    for tok in re.findall(r"[^\s,]+", names):
        tok = tok.strip()
        tok = tok.strip("(){}[]⦃⦄")
        if not tok or tok == "_" or tok.startswith("_"):
            continue
        if any(ch in tok for ch in ":=<>|\\/"):
            continue
        out.append(tok)
    return out, typ.strip()


def looks_like_proof_assumption(names: list[str], typ: str) -> bool:
    """Heuristic for explicit binders that are hypotheses rather than data.

    We intentionally do not classify every explicit binder absent from a result
    as conditional: Lean result heads often omit inferred type/data parameters.
    Instead, we flag binders whose names or types look proof-like.
    """
    typ_flat = " ".join(typ.split())
    if any(name.startswith("h") or name.startswith("H") for name in names):
        return not (typ_flat.startswith("Type") or typ_flat.startswith("Sort"))
    # Keep this conservative: function/relation data parameters often contain
    # `∀`, `→`, or even bounded polynomial notation.  Residual dependencies are
    # tracked separately by exact name, so this field is just for obvious
    # hypothesis binders whose names do not appear in the residual instance.
    proof_markers = ["Prop", "¬"]
    return any(marker in typ_flat for marker in proof_markers)


def extra_explicit_binders(binders: str, result: str) -> list[str]:
    """Proof-like explicit/implicit non-instance binders not used in the result type.

    These are proof/data assumptions for a candidate provider rather than
    parameters of the residual instance it provides.  Square-bracket instance
    binders are ignored because they are typeclass search side conditions.
    """
    extras: list[str] = []
    for opener, content, _close in binder_groups(binders):
        if opener == "[":
            continue
        parsed = binder_names_and_type(content)
        if parsed is None:
            continue
        names, typ = parsed
        if not looks_like_proof_assumption(names, typ):
            continue
        for name in names:
            if not mentions_word(result, name):
                extras.append(name)
    return sorted(set(extras))


def lower_first(name: str) -> str:
    return name[:1].lower() + name[1:] if name else name


def parse_file(path: Path, root: Path) -> list[dict]:
    """All top-level-ish declarations in one file, with parsed signatures."""
    text = path.read_text(encoding="utf-8", errors="replace")
    code = strip_comments(text)
    lines = code.splitlines(keepends=True)

    line_starts: list[int] = []
    pos = 0
    for ln in lines:
        line_starts.append(pos)
        pos += len(ln)

    ns_stack: list[tuple[str, str | None]] = []  # (kind, name)
    headers: list[dict] = []
    for idx, raw in enumerate(lines):
        ln = raw.rstrip("\n")
        m = NAMESPACE_RE.match(ln)
        if m:
            ns_stack.append(("namespace", m.group(1)))
            continue
        if SECTION_RE.match(ln):
            ns_stack.append(("section", None))
            continue
        if END_RE.match(ln):
            if ns_stack:
                ns_stack.pop()
            continue
        m = DECL_RE.match(ln)
        if m:
            prefix = ".".join(n for k, n in ns_stack if k == "namespace" and n)
            headers.append(
                {
                    "kind": m.group(1),
                    "name": m.group(2),
                    "line": idx + 1,
                    "start": line_starts[idx],
                    "sig_from": line_starts[idx] + m.end(2),
                    "namespace": prefix,
                }
            )

    decls: list[dict] = []
    rel = path.relative_to(root).as_posix()
    for i, h in enumerate(headers):
        window_end = headers[i + 1]["start"] if i + 1 < len(headers) else len(code)
        binders, result = split_signature(code[h["sig_from"] : window_end])
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
            }
        )
    return decls


def collect(root: Path) -> tuple[list[dict], list[dict], list[dict]]:
    """Return (all decls, census residual rows, near-miss rows)."""
    all_decls: list[dict] = []
    for f in sorted((root / "ArkLib").rglob("*.lean")):
        if ".lake" in f.parts:
            continue
        all_decls.extend(parse_file(f, root))

    residuals: list[dict] = []
    near_misses: list[dict] = []
    for d in all_decls:
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


def find_providers(all_decls: list[dict], residuals: list[dict]) -> None:
    """Attach providers/refutations + status to each census row, in place."""
    census_names = sorted({r["name"] for r in residuals})
    by_name: dict[str, list[dict]] = {}
    for r in residuals:
        r["providers"] = []
        r["refutations"] = []
        by_name.setdefault(r["name"], []).append(r)

    def_sites = {(r["file"], r["line"]) for r in residuals}

    for d in all_decls:
        if d["kind"] not in PROVIDER_KINDS:
            continue
        if (d["file"], d["line"]) in def_sites:
            continue  # the residual definition itself is never its provider
        last = d["name"].rsplit(".", 1)[-1]
        head_full = result_head(d["result"])
        head_last = head_full.rsplit(".", 1)[-1]
        result_no_forall = strip_forall_prefix(d["result"])
        extra_binders = extra_explicit_binders(d["binders"], d["result"])

        targets: set[str] = set()
        if head_last in by_name:
            targets.add(head_last)
        for rname in census_names:
            for stem in (rname, lower_first(rname)):
                if re.match(re.escape(stem) + r"_(holds|proved)(_|$)", last):
                    # name-based hit must still mention the residual in its
                    # result type, else it is about something adjacent.
                    if mentions_word(d["result"], rname):
                        targets.add(rname)
        consumed = [n for n in census_names if mentions_word(d["binders"], n)]
        provider_ns = _ns_of(d["fq_name"])
        for rname in targets:
            head_for_resolution = head_full if head_last == rname else ""
            rows, ambiguous = _resolve(by_name[rname], head_for_resolution, provider_ns)
            for row in rows:
                row["providers"].append(
                    {
                        "name": d["fq_name"],
                        "kind": d["kind"],
                        "file": d["file"],
                        "line": d["line"],
                        "conditional_on_residuals": consumed,
                        "extra_explicit_binders": extra_binders,
                        "ambiguous_name_match": ambiguous,
                    }
                )

        refuted_targets: set[str] = set()
        if result_no_forall.startswith("¬"):
            negated = result_no_forall[1:].strip()
            neg_head_full = result_head(negated)
            neg_head_last = neg_head_full.rsplit(".", 1)[-1]
            if neg_head_last in by_name:
                refuted_targets.add(neg_head_last)
            for rname in census_names:
                if mentions_word(negated, rname):
                    refuted_targets.add(rname)
            for rname in refuted_targets:
                head_for_resolution = neg_head_full if neg_head_last == rname else ""
                rows, ambiguous = _resolve(by_name[rname], head_for_resolution, provider_ns)
                for row in rows:
                    row["refutations"].append(
                        {
                            "name": d["fq_name"],
                            "kind": d["kind"],
                            "file": d["file"],
                            "line": d["line"],
                            "conditional_on_residuals": consumed,
                            "extra_explicit_binders": extra_binders,
                            "ambiguous_name_match": ambiguous,
                        }
                    )

    def dedupe_entries(entries: list[dict]) -> list[dict]:
        seen: set[tuple] = set()
        out: list[dict] = []
        for p in sorted(entries, key=lambda p: (p["file"], p["line"], p["name"])):
            key = (
                p["name"],
                p["file"],
                p["line"],
                tuple(p["conditional_on_residuals"]),
                tuple(p["extra_explicit_binders"]),
                p["ambiguous_name_match"],
            )
            if key in seen:
                continue
            seen.add(key)
            out.append(p)
        return out

    for r in residuals:
        r["providers"] = dedupe_entries(r["providers"])
        r["refutations"] = dedupe_entries(r["refutations"])
        concrete = [
            p
            for p in r["providers"]
            if not p["conditional_on_residuals"]
            and not p["extra_explicit_binders"]
            and not p["ambiguous_name_match"]
        ]
        concrete_refutations = [
            p
            for p in r["refutations"]
            if not p["conditional_on_residuals"]
            and not p["extra_explicit_binders"]
            and not p["ambiguous_name_match"]
        ]
        if concrete:
            r["status"] = "discharged"
        elif concrete_refutations:
            r["status"] = "refuted"
        else:
            r["status"] = "open"


def top_dir(file: str) -> str:
    parts = Path(file).parts  # ('ArkLib', <top>, ..., '<name>.lean')
    return parts[1] if len(parts) > 2 else "(root)"


def summarize(residuals: list[dict]) -> dict:
    by_dir: dict[str, dict[str, int]] = {}
    for r in residuals:
        d = by_dir.setdefault(
            top_dir(r["file"]),
            {"total": 0, "open": 0, "discharged": 0, "refuted": 0},
        )
        d["total"] += 1
        d[r["status"]] += 1
    return {
        "total": len(residuals),
        "open": sum(1 for r in residuals if r["status"] == "open"),
        "discharged": sum(1 for r in residuals if r["status"] == "discharged"),
        "refuted": sum(1 for r in residuals if r["status"] == "refuted"),
        "by_top_dir": dict(sorted(by_dir.items())),
    }


def conditional_notes(r: dict) -> str:
    """Human-readable summary of why available providers are conditional."""
    conds = sorted({c for p in r["providers"] for c in p["conditional_on_residuals"]})
    binders = sorted({b for p in r["providers"] for b in p.get("extra_explicit_binders", [])})
    notes = []
    if conds:
        notes.append(f"residual deps: {', '.join(f'`{c}`' for c in conds)}")
    if binders:
        notes.append(f"extra assumptions: {', '.join(f'`{b}`' for b in binders)}")
    return "; ".join(notes)


def concrete_refutation_labels(r: dict) -> list[str]:
    refs = [
        p for p in r.get("refutations", [])
        if not p["conditional_on_residuals"]
        and not p["extra_explicit_binders"]
        and not p["ambiguous_name_match"]
    ]
    return [f"`{p['name']}` ({p['file']}:{p['line']})" for p in refs]


def markdown_for_status(residuals: list[dict], status: str) -> list[str]:
    rows = [r for r in residuals if r["status"] == status]
    out: list[str] = [f"## {status.title()} Residuals", ""]
    if not rows:
        return out + ["None.", ""]
    for r in rows:
        suffix = ""
        if status == "open":
            notes = conditional_notes(r)
            if notes:
                suffix = f" — conditional providers only ({notes})"
        elif status == "refuted":
            refs = concrete_refutation_labels(r)
            if refs:
                suffix = f" — refuted by {', '.join(refs)}"
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
            "strict open/discharged/refuted totals, but they are still audit surfaces for hidden",
            "proof debt and naming drift.",
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


def write_wiki_markdown(path: Path, summary: dict, residuals: list[dict], near_misses: list[dict]) -> None:
    """Write the human-facing residual ledger from the same payload as JSON."""
    lines: list[str] = [
        "# ArkLib Residual Census (auto-generated, v4)",
        "",
        "Generated by `python3 scripts/residual_census.py --wiki-out docs/wiki/residual-census.md`.",
        "",
        "The strict census counts declarations under `ArkLib/` of the form",
        "`def ...Residual ... : Prop`. A residual is **discharged** only when a concrete",
        "provider has no residual dependencies, no extra proof-like explicit binders, and no",
        "ambiguous namespace match. Conditional reductions are useful proof plumbing, but they",
        "remain **open** until their side conditions are proved. A residual is **refuted** when",
        "the tree contains a concrete theorem of a negated residual instance.",
        "",
        "The named-residual convention is a modularity pattern, not an incompleteness marker:",
        "always check this census before treating a `*Residual` name as open proof debt.",
        "",
    ]
    for block in extract_campaign_addenda(path):
        lines.extend(block.split("\n"))
        lines.append("")
    lines.extend(
        [
            "## Summary",
            "",
            f"- **Total strict residuals:** {summary['total']}",
            f"- **Open:** {summary['open']}",
            f"- **Discharged:** {summary['discharged']}",
            f"- **Refuted:** {summary['refuted']}",
            f"- **Residual-like near misses:** {len(near_misses)} (listed below and in `scripts/residual_census.json`)",
            "",
            "| top-level directory | total | open | discharged | refuted |",
            "|---|---:|---:|---:|---:|",
        ]
    )
    for name, c in summary["by_top_dir"].items():
        lines.append(
            f"| `{name}` | {c['total']} | {c['open']} | {c['discharged']} | {c['refuted']} |"
        )
    lines.append("")
    lines.extend(markdown_for_status(residuals, "open"))
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
    payload = {"summary": summary, "residuals": payload_residuals, "near_misses": near_misses}
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
        f"residual census: total {summary['total']} | "
        f"open {summary['open']} | discharged {summary['discharged']} | "
        f"refuted {summary['refuted']}"
    )
    print("\nby top-level directory (total / open / discharged / refuted):")
    for name, c in summary["by_top_dir"].items():
        print(
            f"  {name:<16} {c['total']:>3} / {c['open']:>3} / "
            f"{c['discharged']:>3} / {c['refuted']:>3}"
        )

    open_rows = [r for r in residuals if r["status"] == "open"]
    if open_rows:
        print(f"\n{len(open_rows)} open residual(s):")
        for r in open_rows:
            conds = sorted(
                {c for p in r["providers"] for c in p["conditional_on_residuals"]}
            )
            binders = sorted(
                {b for p in r["providers"] for b in p.get("extra_explicit_binders", [])}
            )
            notes = []
            if conds:
                notes.append(f"residual deps: {', '.join(conds)}")
            if binders:
                notes.append(f"extra assumptions: {', '.join(binders)}")
            extra = f"  [only conditional providers, {'; '.join(notes)}]" if notes else ""
            print(f"  {r['fq_name']}  ({r['file']}:{r['line']}){extra}")
    refuted_rows = [r for r in residuals if r["status"] == "refuted"]
    if refuted_rows:
        print(f"\n{len(refuted_rows)} refuted residual(s):")
        for r in refuted_rows:
            refs = [
                p for p in r["refutations"]
                if not p["conditional_on_residuals"]
                and not p["extra_explicit_binders"]
                and not p["ambiguous_name_match"]
            ]
            ref_labels = [f"{p['name']} ({p['file']}:{p['line']})" for p in refs]
            extra = f"  [refuted by: {', '.join(ref_labels)}]" if refs else ""
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
