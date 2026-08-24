"""Unit coverage for scripts/check-docs-integrity.py.

Exercises the symlink check (missing/mispointed/non-symlink CLAUDE.md) and
the markdown link resolver (fragment-only, absolute, relative, external
URLs, code-fence stripping, broken-link detection) against a synthetic repo
tree. The module is loaded by path so its REPO_ROOT points at the temp tree.
"""

import importlib.util
import os
import sys
from pathlib import Path

import pytest


def load_module(repo_root: Path):
    spec = importlib.util.spec_from_file_location(
        "check_docs_integrity", str((Path(__file__).resolve().parents[1] / "scripts/check-docs-integrity.py"))
    )
    module = importlib.util.module_from_spec(spec)
    sys.modules["check_docs_integrity"] = module
    spec.loader.exec_module(module)
    # Point REPO_ROOT at the synthetic tree AFTER exec (exec redefines it),
    # and refresh the derived module-level path constants.
    module.REPO_ROOT = repo_root
    module.CLAUDE_PATH = repo_root / "CLAUDE.md"
    module.AGENTS_PATH = repo_root / "AGENTS.md"
    return module


@pytest.fixture()
def repo(tmp_path: Path):
    (tmp_path / "docs" / "kb").mkdir(parents=True)
    (tmp_path / "scripts").mkdir()
    (tmp_path / "AGENTS.md").write_text("# Agents\n", encoding="utf-8")
    (tmp_path / "scripts" / "README.md").write_text("# Scripts\n", encoding="utf-8")
    return tmp_path


def test_claude_symlink_ok(repo: Path) -> None:
    os.symlink("AGENTS.md", repo / "CLAUDE.md")
    mod = load_module(repo)
    assert mod.check_claude_symlink() == []


def test_claude_symlink_missing(repo: Path) -> None:
    mod = load_module(repo)
    errors = mod.check_claude_symlink()
    assert any("Missing CLAUDE.md" in e for e in errors)


def test_claude_symlink_not_symlink(repo: Path) -> None:
    (repo / "CLAUDE.md").write_text("not a symlink", encoding="utf-8")
    mod = load_module(repo)
    errors = mod.check_claude_symlink()
    assert any("must be a symlink" in e for e in errors)


def test_claude_symlink_wrong_target(repo: Path) -> None:
    (repo / "OTHER.md").write_text("# Other\n", encoding="utf-8")
    os.symlink("OTHER.md", repo / "CLAUDE.md")
    mod = load_module(repo)
    errors = mod.check_claude_symlink()
    assert any("must point to AGENTS.md" in e for e in errors)


def test_resolve_link_relative_and_absolute(repo: Path) -> None:
    mod = load_module(repo)
    source = repo / "docs" / "kb" / "page.md"
    (repo / "docs" / "kb" / "other.md").write_text("x", encoding="utf-8")
    (repo / "docs" / "top.md").write_text("y", encoding="utf-8")

    rel = mod.resolve_link(source, "other.md")
    assert rel == (repo / "docs" / "kb" / "other.md").resolve()
    abs_link = mod.resolve_link(source, "/docs/top.md")
    assert abs_link == (repo / "docs" / "top.md").resolve()


def test_resolve_link_ignores_fragments_and_external(repo: Path) -> None:
    mod = load_module(repo)
    source = repo / "docs" / "kb" / "page.md"
    assert mod.resolve_link(source, "#section") is None
    assert mod.resolve_link(source, "https://example.com/x") is None
    assert mod.resolve_link(source, "mailto:a@b.c") is None
    assert mod.resolve_link(source, "") is None
    assert mod.resolve_link(source, "`code.md`") == (repo / "docs" / "kb" / "code.md").resolve()


def test_check_markdown_links_finds_broken(repo: Path) -> None:
    mod = load_module(repo)
    (repo / "docs" / "kb" / "page.md").write_text(
        "[good](other.md)\n[broken](../missing.md)\n", encoding="utf-8"
    )
    (repo / "docs" / "kb" / "other.md").write_text("x", encoding="utf-8")
    errors = mod.check_markdown_links()
    assert any("missing.md" in e for e in errors)
    assert not any("other.md" in e for e in errors)


def test_check_markdown_links_skips_code_blocks(repo: Path) -> None:
    mod = load_module(repo)
    (repo / "docs" / "kb" / "page.md").write_text(
        "```\n[not-a-link](fake.md)\n```\n[real](other.md)\n", encoding="utf-8"
    )
    (repo / "docs" / "kb" / "other.md").write_text("x", encoding="utf-8")
    errors = mod.check_markdown_links()
    assert not any("fake.md" in e for e in errors)


def test_tracked_markdown_files_excludes_generated(repo: Path) -> None:
    mod = load_module(repo)
    (repo / "docs" / "kb" / "_generated").mkdir()
    (repo / "docs" / "kb" / "a.md").write_text("x", encoding="utf-8")
    (repo / "docs" / "kb" / "_generated" / "b.md").write_text("y", encoding="utf-8")
    files = mod.tracked_markdown_files()
    names = [f.name for f in files]
    assert "a.md" in names
    assert "b.md" not in names
    assert "README.md" in names  # scripts/README.md is always included
