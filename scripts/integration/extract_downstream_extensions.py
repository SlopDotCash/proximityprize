#!/usr/bin/env python3
"""Preserve classic downstream additions beside the authoritative ArkLib modules.

This is a conservative source migration aid, not a Lean elaborator. It removes a
named command only when its fully qualified public name already exists in the
upstream production tree. Anonymous/syntax commands are removed only when their
normalized code, namespace and active context exactly match upstream. An identical
private helper promoted to a public upstream owner is reused only after comparing
its context, signature, and body. Other private helpers and section context remain intact. The
audit records every retained or removed declaration; compilation must still
check that the retained proofs use the new upstream APIs correctly.

The splitter deliberately accepts only column-zero commands, the convention in
the input corpus. Nested comments and literals are masked before locating them.
An indented declaration is rejected rather than silently truncated.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys


PROVENANCE_HEADER = (
    "/-\n"
    "Downstream additions retained during the ArkLib integration.\n"
    "Initial source and revision: scripts/integration/downstream-extension-audit.json.\n"
    "Shared declarations come from the canonical ArkLib modules.\n"
    "Checked-in source owns later API ports. Generate separate review candidates with:\n"
    "scripts/integration/extract_downstream_extensions.py --output-dir <directory>.\n"
    "-/\n"
)


DECL_KINDS = {
    "theorem", "lemma", "def", "abbrev", "structure", "inductive", "class",
    "instance", "opaque", "axiom", "alias",
}
SEMANTIC_KINDS = DECL_KINDS | {
    "macro", "macro_rules", "syntax", "notation", "notation3", "infix",
    "infixl", "infixr", "prefix", "postfix", "elab", "elab_rules",
    "initialize", "builtin_initialize", "declare_syntax_cat", "simproc",
}
MODIFIERS = {
    "private", "protected", "public", "noncomputable", "partial", "unsafe",
    "meta", "scoped", "local",
}
NAME = r"(?:«[^»\n]+»|[\w][\w'!?]*)(?:\.(?:«[^»\n]+»|[\w][\w'!?]*))*"
NAME_RE = re.compile(NAME, re.UNICODE)
START_RE = re.compile(
    r"^(?:@\[|#\w+\b|(?:theorem|lemma|def|abbrev|structure|inductive|class|"
    r"instance|opaque|axiom|alias|private|protected|public|noncomputable|partial|"
    r"unsafe|meta|scoped|local|namespace|section|end|universe|universes|variable|"
    r"variables|include|omit|open|export|attribute|set_option|macro|macro_rules|"
    r"syntax|notation|notation3|infix|infixl|infixr|prefix|postfix|elab|elab_rules|"
    r"initialize|builtin_initialize|declare_syntax_cat|simproc|example|seal|unseal|"
    r"mutual|module|import)(?=\s|:|$))"
)


@dataclass
class Command:
    start: int
    end: int
    kind: str
    name: str | None
    namespace: str
    private: bool
    line: int
    token_start: int
    context: tuple[str, ...] = ()

    @property
    def full_name(self) -> str | None:
        if not self.name:
            return None
        if self.name.startswith("_root_."):
            return self.name[len("_root_."):]
        return ".".join(x for x in (self.namespace, self.name) if x)


def lexical_mask(text: str) -> tuple[str, list[tuple[int, int, str]]]:
    """Mask nested comments and literals, keeping offsets and newlines stable."""
    chars = list(text)
    comments: list[tuple[int, int, str]] = []
    i = 0

    def hide(start: int, end: int) -> None:
        for j in range(start, end):
            if chars[j] != "\n":
                chars[j] = " "

    while i < len(text):
        raw_string = re.match(r'r(#+)?"', text[i:]) if text[i] == "r" else None
        if raw_string and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'")):
            start = i
            hashes = raw_string.group(1) or ""
            end_marker = '"' + hashes
            end = text.find(end_marker, i + len(raw_string.group(0)))
            if end < 0:
                raise ValueError(f"unclosed raw string at byte {start}")
            i = end + len(end_marker)
            hide(start, i)
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            comments.append((i, end, "line"))
            hide(i, end)
            i = end
        elif text.startswith("/-", i):
            start, depth = i, 1
            i += 2
            while i < len(text) and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ValueError(f"unclosed block comment at byte {start}")
            comments.append((start, i, "doc" if text.startswith("/--", start) else "block"))
            hide(start, i)
        elif text[i] == '"':
            start = i
            i += 1
            closed = False
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    closed = True
                    break
                else:
                    i += 1
            if not closed:
                raise ValueError(f"unclosed string at byte {start}")
            hide(start, min(i, len(text)))
        elif (text[i] == "'" and i + 2 < len(text)
              and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'"))):
            # A character literal has a closing quote; identifier primes do not.
            end = i + 2
            if text[i + 1] == "\\":
                end = i + 3
                while end < len(text) and text[end] != "'" and end - i < 16:
                    end += 1
            if end < len(text) and text[end] == "'":
                hide(i, end + 1)
                i = end + 1
            else:
                i += 1
        else:
            i += 1
    return "".join(chars), comments


def head_info(masked: str) -> tuple[str, str | None, bool, str]:
    """Read attributes/modifiers and the explicit name of one command head."""
    remaining = masked.lstrip()
    while remaining.startswith("@["):
        depth, i = 1, 2
        while i < len(remaining) and depth:
            depth += (remaining[i] == "[") - (remaining[i] == "]")
            i += 1
        if depth:
            return "attribute-prefix", None, False, ""
        remaining = remaining[i:].lstrip()
    modifiers = []
    while True:
        match = re.match(r"([A-Za-z_]+)\b", remaining)
        if not match or match.group(1) not in MODIFIERS:
            break
        modifiers.append(match.group(1))
        remaining = remaining[match.end():].lstrip()
    match = re.match(r"(#[\w]+|[A-Za-z_][A-Za-z_0-9]*)(?=\s|:|$)", remaining)
    if not match:
        return "attribute-prefix" if not remaining else "unknown", None, False, remaining
    kind = match.group(1)
    tail = remaining[match.end():].lstrip()
    name_match = NAME_RE.match(tail) if kind in DECL_KINDS | {"namespace", "section", "end"} else None
    name = name_match.group(0) if name_match else None
    # `instance (x : X) : ...` and `instance : ...` are anonymous.
    if kind == "instance" and name in {"where", "priority"}:
        name = None
    return kind, name, any(x in modifiers for x in ("private", "local")), tail


def normalize_command(text: str) -> str:
    """Ignore comments/formatting while preserving every literal's exact bytes."""
    masked, comments = lexical_mask(text)
    hidden = {i for start, end, _ in comments for i in range(start, end)}
    output = []
    whitespace = False
    i = 0
    while i < len(text):
        if i in hidden:
            whitespace = True
            i += 1
        elif masked[i] == " " and text[i] not in " \t\r\n":
            # A masked non-comment run is a literal. Preserve it verbatim.
            end = i + 1
            while end < len(text) and end not in hidden and (
                    masked[end] == " " or text[end] == "\n"):
                end += 1
            if whitespace and output:
                output.append(" ")
            output.append(text[i:end])
            whitespace = False
            i = end
        elif text[i].isspace():
            whitespace = True
            i += 1
        else:
            if whitespace and output:
                output.append(" ")
            output.append(text[i])
            whitespace = False
            i += 1
    return "".join(output).strip()


def semantic_key(text: str, command: Command) -> tuple:
    return (command.kind, command.namespace, command.context,
            normalize_command(text[command.start:command.end]))


def promotion_key(text: str, command: Command) -> tuple | None:
    """Compare an explicit private helper with its identical new public owner.

    Only declaration visibility is ignored. Attributes, other modifiers, the full
    signature/body, namespace, and active context must remain identical. Scoped
    command prefixes and local declarations stay conservative review cases.
    """
    code = normalize_command(text[command.start:command.end])
    masked, _ = lexical_mask(code)
    offset = 0
    while code.startswith("@[", offset):
        depth, end = 1, offset + 2
        while end < len(code) and depth:
            depth += (masked[end] == "[") - (masked[end] == "]")
            end += 1
        if depth:
            return None
        offset = end
        while offset < len(code) and code[offset].isspace():
            offset += 1
    modifier = "|".join(sorted(MODIFIERS, key=len, reverse=True))
    head = re.match(r"((?:(?:" + modifier + r")\s+)*)" + re.escape(command.kind)
                    + r"(?=\s|:|$)", code[offset:])
    if not head:
        return None
    modifiers = head[1].split()
    if "local" in modifiers or (command.private and "private" not in modifiers):
        return None
    kept = [item for item in modifiers if item not in {"private", "public"}]
    normalized = (code[:offset] + " ".join([*kept, command.kind])
                  + code[offset + head.end():])
    return command.kind, command.namespace, command.context, normalized


def promoted_private_duplicate(text: str, command: Command,
                               definitions: dict, sources: dict) -> tuple | None:
    """Return an authoritative owner only for a byte-equivalent visibility promotion."""
    if not command.private or not command.full_name or command.kind not in DECL_KINDS:
        return None
    candidate = definitions.get(command.full_name)
    if candidate is None:
        return None
    owner, original = candidate
    if original.private or original.kind != command.kind:
        return None
    key = promotion_key(text, command)
    return candidate if key is not None and key == promotion_key(sources[owner], original) else None


def parse_commands(text: str, *, strict: bool = True) -> list[Command]:
    """Split the corpus's column-zero commands while keeping their full context."""
    masked, comments = lexical_mask(text)
    candidates = []
    offset = 0
    for number, line in enumerate(masked.splitlines(keepends=True), 1):
        if START_RE.match(line):
            candidates.append((offset, number))
        elif strict and line.strip() and not line[0].isspace():
            # These are continuations of a preceding declaration, not new
            # commands. Any other column-zero token needs a parser update.
            import_continuation = (candidates and
                                   head_info(masked[candidates[-1][0]:offset])[0] == "import"
                                   and re.fullmatch(NAME + r"\s*", line))
            if not import_continuation and not re.match(
                    r"^(?:where\b|deriving\b|termination_by\b|decreasing_by\b|fun\b|by\b|[{}()\[\]:=|])", line):
                raise ValueError(f"unrecognized column-zero command at line {number}: {line.strip()[:80]}")
        elif strict and line[0:1].isspace() and head_info(line)[0] in DECL_KINDS:
            raise ValueError(f"indented declaration boundary needs review at line {number}")
        offset += len(line)
    starts: list[tuple[int, int, int, str, str | None, bool, str]] = []
    pending: int | None = None
    for index, (offset, number) in enumerate(candidates):
        end = candidates[index + 1][0] if index + 1 < len(candidates) else len(text)
        body = masked[offset:end]
        kind, name, private, tail = head_info(body)
        if strict and kind in {"unknown", "mutual"}:
            raise ValueError(f"ambiguous {kind} command at line {number}")
        if kind == "attribute-prefix" or (
            kind in {"omit", "include", "open", "set_option", "seal", "unseal"}
            and re.search(r"\bin\s*$", body)
        ):
            pending = offset if pending is None else pending
            continue
        start = pending if pending is not None else offset
        pending = None
        # Attach only a declaration docstring immediately before the command;
        # this prevents deleting the following declaration's documentation.
        for a, b, comment_kind in reversed(comments):
            if b > start:
                continue
            # Ordinary comments between a docstring and its declaration are
            # accepted by Lean. They must travel with the removed command too.
            if masked[b:start].strip():
                break
            if comment_kind == "doc":
                start = a
                break
        starts.append((start, offset, number, kind, name, private, tail))
    if pending is not None:
        raise ValueError("dangling command prefix at end of source")
    stack: list[tuple[str, str]] = []
    frames: list[list[str]] = [[]]
    result = []

    def namespace() -> str:
        value = ""
        for kind, part in stack:
            if kind == "namespace":
                value = part[len("_root_."):] if part.startswith("_root_.") else ".".join(
                    x for x in (value, part) if x)
        return value

    for index, (start, token, number, kind, name, private, tail) in enumerate(starts):
        end = starts[index + 1][0] if index + 1 < len(starts) else len(text)
        result.append(Command(start, end, kind, name, namespace(), private, number, token,
                              tuple(item for frame in frames for item in frame)))
        if kind in {"variable", "variables", "universe", "universes", "include", "omit", "open", "set_option"}:
            frames[-1].append(normalize_command(text[start:end]))
        if kind == "namespace":
            # Lean permits both `end A.B` and `end B; end A` after
            # `namespace A.B`, so compound namespaces create nested scopes.
            parts = (name or "").split(".")
            if parts and parts[0] == "_root_":
                parts = ["_root_." + parts[1], *parts[2:]]
            stack.extend((kind, part) for part in parts)
            frames.extend([] for _ in parts)
        elif kind == "section":
            stack.append((kind, name or ""))
            frames.append([])
        elif kind == "end" and stack:
            if name:
                matching = [i for i, (scope, label) in enumerate(stack)
                            if label == name or (scope == "namespace" and ".".join(
                                part for kind, part in stack[i:] if kind == "namespace") == name)]
                if strict and not matching:
                    raise ValueError(f"unmatched end {name} at line {number}")
                if matching:
                    del stack[matching[-1]:]
                    frames = frames[:len(stack) + 1]
            elif stack:
                stack.pop()
                frames.pop()
    return result


def declaration_names(text: str) -> set[str]:
    return {c.full_name for c in parse_commands(text)
            if c.kind in DECL_KINDS and c.full_name and not c.private}


def git_sources(root: Path, revision: str) -> tuple[str, dict[str, str]]:
    sha = subprocess.check_output(["git", "rev-parse", revision], cwd=root, text=True).strip()
    tree = subprocess.check_output(["git", "ls-tree", "-r", sha], cwd=root, text=True)
    entries = []
    for line in tree.splitlines():
        metadata, path = line.split("\t", 1)
        if path.startswith("ArkLib/") and path.endswith(".lean"):
            entries.append((path, metadata.split()[2]))
    process = subprocess.Popen(["git", "cat-file", "--batch"], cwd=root,
                               stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    assert process.stdin and process.stdout
    sources = {}
    try:
        for path, blob in entries:
            process.stdin.write((blob + "\n").encode())
            process.stdin.flush()
            header = process.stdout.readline().split()
            content = process.stdout.read(int(header[2]))
            process.stdout.read(1)
            sources[path] = content.decode("utf-8")
    finally:
        process.stdin.close()
        process.wait()
    return sha, sources


def module_name(path: str) -> str:
    return path.removesuffix(".lean").replace("/", ".")


def extension_path(path: str) -> str:
    return "ProximityPrize/Extensions/" + path.removeprefix("ArkLib/")


def canonical_owner_modules(path: str, removed: list[dict]) -> set[str]:
    """A removed declaration may be supplied by a new canonical submodule."""
    return {module_name(path)} | {module_name(record["upstream_owner"]) for record in removed}


def remap_imports(text: str, mapping: dict[str, str]) -> str:
    masked, _ = lexical_mask(text)
    replacements = []
    pattern = re.compile(r"(?m)^(?:(?:public|meta)\s+)*import\s+(?:all\s+)?([^\n]+)")
    for match in pattern.finditer(masked):
        for token in re.finditer(NAME, match.group(1)):
            old = token.group(0)
            if old in mapping:
                start = match.start(1) + token.start()
                replacements.append((start, start + len(old), mapping[old]))
    for start, end, replacement in reversed(replacements):
        text = text[:start] + replacement + text[end:]
    return text


def prune_exact(root: Path, mapping: dict[str, str], upstream_revision: str,
                upstream_semantic: dict[tuple, tuple[str, Command]]) -> dict:
    """Prune only exact current-source duplicates; never regenerate manual ports."""
    prepared = {}
    records = {}
    for module in mapping.values():
        path = module.replace(".", "/") + ".lean"
        # This file is now a hand-authored compatibility API, rather than an
        # extraction template. Its aliases and PMF bridges have their own checks.
        if path == "ProximityPrize/Extensions/Data/CodingTheory/ProximityGap/Errors.lean":
            continue
        target = root / path
        if not target.exists():
            raise ValueError(f"missing checked-in extension {path}")
        source = target.read_text()
        commands = parse_commands(source)
        removed = []
        selected = []
        for command in commands:
            if (command.kind not in SEMANTIC_KINDS or command.private
                    or (command.name and command.kind in DECL_KINDS)):
                continue
            duplicate = upstream_semantic.get(semantic_key(source, command))
            if duplicate:
                owner, original = duplicate
                selected.append(command)
                removed.append({
                    "kind": command.kind, "name": command.full_name, "line": command.line,
                    "namespace": command.namespace,
                    "active_context": list(command.context),
                    "upstream_owner": owner, "upstream_line": original.line,
                    "normalized_command_sha256": hashlib.sha256(
                        normalize_command(source[command.start:command.end]).encode()).hexdigest(),
                })
        if not selected:
            continue
        result = source
        selected_spans = {(command.start, command.end) for command in selected}
        expected = [(c.kind, c.full_name, c.private) for c in commands
                    if c.kind in SEMANTIC_KINDS and (c.start, c.end) not in selected_spans]
        for command in reversed(selected):
            result = result[:command.start] + result[command.end:]
        result = result.rstrip() + "\n"
        actual = [(c.kind, c.full_name, c.private) for c in parse_commands(result)
                  if c.kind in SEMANTIC_KINDS]
        if expected != actual:
            raise ValueError(f"exact-pruning retained declaration audit failed for {path}")
        prepared[path] = result
        records[path] = {
            "before_sha256": hashlib.sha256(source.encode()).hexdigest(),
            "after_sha256": hashlib.sha256(result.encode()).hexdigest(),
            "removed": removed,
        }
    for path, result in prepared.items():
        (root / path).write_text(result)
    report = {
        "upstream_revision": upstream_revision,
        "method": "identical normalized command, namespace and active context in current source and upstream",
        "manual_ports_preserved": ["ProximityPrize.Extensions.Data.CodingTheory.ProximityGap.Errors"],
        "summary": {"files": len(records), "commands": sum(len(r["removed"]) for r in records.values())},
        "files": records,
    }
    if records:
        target = root / "scripts/integration/exact-semantic-dedup.json"
        target.write_text(json.dumps(report, indent=2, ensure_ascii=False) + "\n")
    return report


def self_test() -> None:
    assert all(len(line) <= 100 for line in PROVENANCE_HEADER.splitlines())
    source = '''import ArkLib.Sample
namespace Code
variable (n : Nat)
/-- Kept documentation. -/
@[simp]
theorem 𝓛 : True := by
  have h : True := by trivial
  exact h
/-- Removed documentation. -/
omit n in
theorem duplicate : True := by trivial
instance : Nonempty Nat := inferInstance
-- theorem ghost : False := by sorry
/- outer /- theorem ghost : False := by sorry -/ -/
end Code
'''
    commands = parse_commands(source)
    declarations = [c for c in commands if c.kind in DECL_KINDS]
    assert [(c.full_name, c.kind) for c in declarations] == [
        ("Code.𝓛", "theorem"), ("Code.duplicate", "theorem"), (None, "instance")]
    duplicate = declarations[1]
    assert "omit n in" in source[duplicate.start:duplicate.end]
    assert "Removed documentation" in source[duplicate.start:duplicate.end]
    kept = source[:duplicate.start] + source[duplicate.end:]
    assert "Kept documentation" in kept and "instance :" in kept
    assert "Removed documentation" not in kept
    interrupted_doc = '''namespace N
/-- Attached despite explanatory comments. -/
-- Explanation one.
/- Explanation two. -/
theorem duplicate : True := by trivial
end N
'''
    duplicate_doc = next(c for c in parse_commands(interrupted_doc) if c.kind == "theorem")
    assert interrupted_doc[duplicate_doc.start:duplicate_doc.end].startswith('/-- Attached')
    without_duplicate = interrupted_doc[:duplicate_doc.start] + interrupted_doc[duplicate_doc.end:]
    assert '/--' not in without_duplicate and '-- Explanation' not in without_duplicate
    assert remap_imports('import ArkLib.A\n-- import ArkLib.A\n',
                         {"ArkLib.A": "ProximityPrize.Extensions.A"}) == (
        'import ProximityPrize.Extensions.A\n-- import ArkLib.A\n')
    assert declaration_names('namespace A\nprivate def helper := 1\ndef φ := 1\nend A\n') == {"A.φ"}
    contexts = '''namespace A.B
section Scope
variable (n : Nat)
open Nat in
@[simp] theorem one : n = n := rfl
include n in
theorem two : n = n := rfl
set_option maxRecDepth 300 in
theorem three : True := by trivial
structure Box where
  value : Nat
  property : value = value
deriving Inhabited
end Scope
end B
end A
'''
    parsed = parse_commands(contexts)
    assert [c.full_name for c in parsed if c.kind in DECL_KINDS] == [
        "A.B.one", "A.B.two", "A.B.three", "A.B.Box"]
    assert "open Nat in" in contexts[parsed[3].start:parsed[3].end]
    structure = next(c for c in parsed if c.kind == "structure")
    assert "property : value = value" in contexts[structure.start:structure.end]
    assert "deriving Inhabited" in contexts[structure.start:structure.end]
    literals = '''namespace N
def text := "line one\nnamespace Fake\ntheorem ghost : False := by sorry\n"
def quoted := 'x'
/- namespace Hidden /- theorem nested : False := by sorry -/ -/
theorem real : True := by trivial
end N
'''
    assert declaration_names(literals) == {"N.text", "N.quoted", "N.real"}
    assert declaration_names('def raw := r##"quoted \\"\nnamespace Fake\ntheorem ghost := 1\n"##\ndef real := 2\n') == {"raw", "real"}
    same_a = 'universe u\nnamespace N\nvariable (α : Type u)\ninstance : Nonempty (List α) := ⟨[]⟩\nend N\n'
    same_b = 'module\n@[expose] public section\nuniverse u\nnamespace N\nvariable (α : Type u)\n/-- Same. -/\ninstance : Nonempty (List α) := ⟨[]⟩\nend N\n'
    inst_a = next(c for c in parse_commands(same_a) if c.kind == "instance")
    inst_b = next(c for c in parse_commands(same_b) if c.kind == "instance")
    assert semantic_key(same_a, inst_a) == semantic_key(same_b, inst_b)
    other = same_a.replace('namespace N', 'namespace M').replace('end N', 'end M')
    assert semantic_key(other, next(c for c in parse_commands(other) if c.kind == "instance")) != semantic_key(same_a, inst_a)
    assert normalize_command('def a := "two  spaces"') != normalize_command('def a := "two spaces"')
    assert normalize_command('instance /- ignored -/ : Foo := bar') == normalize_command('instance : Foo := bar')
    for ambiguous in (
        'namespace A\ncustom_command foo\ntheorem t : True := by trivial\nend A\n',
        'namespace A\n  theorem indented : True := by trivial\nend A\n',
        'mutual\ndef a := 1\nend\n',
        'namespace A.B\nend C\n',
        'def broken := "unterminated\n',
    ):
        try:
            parse_commands(ambiguous)
        except ValueError:
            pass
        else:
            raise AssertionError("uncertain command boundary did not fail closed")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument("--downstream-ref", default="883e99d61e51264327b5fee859732d047f7d7038")
    parser.add_argument("--upstream-ref", default="arklib-readonly/main")
    parser.add_argument("--mapping", type=Path,
                        default=Path("scripts/integration/downstream-extensions.json"))
    parser.add_argument("--audit", type=Path,
                        default=Path("scripts/integration/downstream-extension-audit.json"))
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--output-dir", type=Path,
                        help="write review candidates outside the source checkout")
    parser.add_argument("--prune-exact", action="store_true",
                        help="remove only exact semantic/context duplicates from current extension sources")
    args = parser.parse_args()
    self_test()
    if args.self_test:
        print("Extension extractor self-tests passed.")
        return 0
    root = args.root.resolve()
    output_root = args.output_dir.resolve() if args.output_dir else root
    existing_mapping = (json.loads((root / args.mapping).read_text())
                        if (root / args.mapping).exists() else {})
    downstream_sha, downstream = git_sources(root, args.downstream_ref)
    upstream_sha, upstream = git_sources(root, args.upstream_ref)
    upstream_commands = {}
    for path, text in upstream.items():
        try:
            # Upstream defines extensible commands such as `assert_toy_ir`.
            # Index explicit names without editing that source; strict boundary
            # checks are required on the downstream source we actually split.
            upstream_commands[path] = parse_commands(text, strict=False)
        except ValueError as error:
            raise ValueError(f"upstream {path}: {error}") from error
    upstream_definitions = {command.full_name: (path, command)
                            for path, commands in upstream_commands.items()
                            for command in commands if command.kind in DECL_KINDS
                            and command.full_name and not command.private}
    upstream_names = set(upstream_definitions)
    upstream_semantic = {}
    for path, commands in upstream_commands.items():
        for command in commands:
            if (command.kind in SEMANTIC_KINDS and not command.private
                    and (not command.name or command.kind not in DECL_KINDS)):
                upstream_semantic[semantic_key(upstream[path], command)] = (path, command)
    if args.prune_exact:
        if args.output_dir:
            raise ValueError("--prune-exact edits current source; do not combine it with --output-dir")
        report = prune_exact(root, existing_mapping, upstream_sha, upstream_semantic)
        print(json.dumps(report["summary"], indent=2))
        return 0
    extensions = {}
    records = {}
    proof_improvements = []
    for path in sorted(downstream.keys() & upstream.keys()):
        source = downstream[path]
        if source == upstream[path]:
            continue
        try:
            commands = parse_commands(source)
        except ValueError as error:
            raise ValueError(f"downstream {path}: {error}") from error
        retained = []
        removed = []
        replacements = []
        for command in commands:
            if command.kind not in SEMANTIC_KINDS:
                continue
            record = {"kind": command.kind, "name": command.full_name,
                      "line": command.line, "private": command.private}
            promoted = promoted_private_duplicate(source, command, upstream_definitions, upstream)
            duplicate = (upstream_semantic.get(semantic_key(source, command))
                         if not command.private and (not command.name or command.kind not in DECL_KINDS)
                         else None)
            if (command.full_name in upstream_names and not command.private) or duplicate or promoted:
                record["reason"] = ("identical private helper promoted to authoritative upstream public definition"
                                    if promoted else "exact semantic command and active context supplied by authoritative upstream"
                                    if duplicate else "public name supplied by authoritative upstream production module")
                if duplicate:
                    owner, original = duplicate
                    record["upstream_owner"] = owner
                    record["upstream_line"] = original.line
                    record["normalized_command_sha256"] = hashlib.sha256(
                        normalize_command(source[command.start:command.end]).encode()).hexdigest()
                upstream_path, upstream_command = (promoted or duplicate or upstream_definitions[command.full_name])
                record["upstream_owner"] = upstream_path
                record["upstream_line"] = upstream_command.line
                removed.append(record)
                replacements.append((command.start, command.end))
                upstream_body = upstream[upstream_path][upstream_command.start:upstream_command.end]
                downstream_body = source[command.start:command.end]
                hole_pattern = r"\b(?:sorry|admit|sorryAx)\b"
                if (re.search(hole_pattern, lexical_mask(upstream_body)[0])
                        and not re.search(hole_pattern, lexical_mask(downstream_body)[0])):
                    proof_improvements.append({
                        "name": command.full_name, "downstream_file": path,
                        "upstream_file": upstream_path, "downstream_line": command.line,
                        "upstream_line": upstream_command.line,
                        "downstream_command": downstream_body,
                        "upstream_command": upstream_body,
                        "downstream_has_residual_argument": bool(re.search(r"\bhResidual\b", downstream_body)),
                        "status": "syntactically complete downstream candidate; statement equivalence and API compatibility unverified",
                    })
            else:
                record["reason"] = ("private helper retained with its original context" if command.private
                                    else "no upstream public name match" if command.full_name
                                    else "unnamed or syntax command retained conservatively")
                retained.append(record)
        # Private helpers alone are not a downstream public extension. Keep
        # unnamed/syntax commands because their generated names are not inferred.
        if (not any(not entry["private"] for entry in retained)
                and module_name(path) not in existing_mapping):
            continue
        for start, end in reversed(replacements):
            source = source[:start] + source[end:]
        # Reparse after deletion: every retained command must have the same
        # namespace and kind, including anonymous instances and private helpers.
        expected = [(r["kind"], r["name"], r["private"]) for r in retained]
        actual = [(c.kind, c.full_name, c.private) for c in parse_commands(source)
                  if c.kind in SEMANTIC_KINDS]
        if expected != actual:
            raise ValueError(f"retained declaration/context audit failed for {path}")
        extensions[path] = source
        records[path] = {
            "extension": extension_path(path),
            "downstream_sha256": hashlib.sha256(downstream[path].encode()).hexdigest(),
            "upstream_sha256": hashlib.sha256(upstream[path].encode()).hexdigest(),
            "retained": retained, "removed": removed,
            "status": "source preserved; API compatibility requires Lean compilation",
        }
    mapping = {module_name(path): module_name(extension_path(path)) for path in extensions}
    outputs = {}
    for path, source in extensions.items():
        imports = {name: target for name, target in mapping.items() if name != module_name(path)}
        source = remap_imports(source, imports)
        owner_modules = canonical_owner_modules(path, records[path]["removed"])
        prefix = (PROVENANCE_HEADER
                  + "".join(f"import {owner}\n" for owner in sorted(owner_modules)) + "\n")
        outputs[extension_path(path)] = (prefix + source).rstrip() + "\n"
        records[path]["extracted_output_sha256"] = hashlib.sha256(
            outputs[extension_path(path)].encode()).hexdigest()
    changed_existing = [path for path, content in outputs.items()
                        if (output_root / path).exists() and (output_root / path).read_text() != content]
    if changed_existing:
        raise ValueError("existing extensions contain edits; use --output-dir for review candidates: "
                         + ", ".join(changed_existing))
    for path, content in outputs.items():
        target = output_root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(content)
    audit = {
        "downstream_revision": downstream_sha, "upstream_revision": upstream_sha,
        "method": "conservative lexical extraction; public-name and exact semantic/context deduplication",
        "limitations": [
            "Source migration does not establish Lean elaboration or mathematical equivalence.",
            "Anonymous instances and syntax commands are retained unless exact code/namespace/context duplicates.",
            "Private helpers are retained unless an identical helper with the same context became public upstream; namespace, section, variable, open and option context is retained.",
            "Upstream public declarations win even if their downstream statements or proofs differ.",
            "Generated modules require a joint compilation against the authoritative upstream API.",
        ],
        "summary": {"extension_modules": len(records),
                    "retained_commands": sum(len(r["retained"]) for r in records.values()),
                    "removed_commands": sum(len(r["removed"]) for r in records.values()),
                    "downstream_proofs_of_upstream_admissions": len(proof_improvements)},
        "upstream_proof_improvements": proof_improvements,
        "files": records,
    }
    for relative, value in ((args.mapping, mapping), (args.audit, audit)):
        target = output_root / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n")
    print(json.dumps(audit["summary"], indent=2))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (ValueError, subprocess.CalledProcessError) as error:
        print(f"Extension extraction stopped: {error}", file=sys.stderr)
        raise SystemExit(1)
