"""Unit coverage for scripts/sorry-tracker.py.

Exercises the pure parsing logic: import resolution (package map, repo
root, src/, size cap), diff parsing for newly-added sorries (file
tracking, comment skipping, declaration context extraction), and the
declaration-name regexes.
"""

import importlib.util
import sys
import types
from pathlib import Path

import pytest


def load_module():
    # Stub the heavy google.generativeai dependency (not needed for parsing).
    fake_genai = types.ModuleType("google.generativeai")
    fake_google = types.ModuleType("google")
    fake_google.generativeai = fake_genai
    sys.modules.setdefault("google", fake_google)
    sys.modules.setdefault("google.generativeai", fake_genai)
    spec = importlib.util.spec_from_file_location(
        "sorry_tracker", str((Path(__file__).resolve().parents[1] / "scripts/sorry-tracker.py"))
    )
    module = importlib.util.module_from_spec(spec)
    sys.modules["sorry_tracker"] = module
    spec.loader.exec_module(module)
    return module


mod = load_module()


def test_find_and_read_imports_repo_root(tmp_path: Path) -> None:
    src = tmp_path / "ImportTarget.lean"
    src.write_text("def target : Nat := 1\n", encoding="utf-8")
    content = "import ImportTarget\n"
    result = mod.find_and_read_imports(content, str(tmp_path), web_search=False)
    assert "def target" in result
    assert "Content from: ImportTarget" in result


def test_find_and_read_imports_src_dir(tmp_path: Path) -> None:
    src_dir = tmp_path / "src"
    src_dir.mkdir()
    (src_dir / "Nested.lean").write_text("def n : Nat := 2\n", encoding="utf-8")
    content = "import Nested\n"
    result = mod.find_and_read_imports(content, str(tmp_path), web_search=False)
    assert "def n" in result


def test_find_and_read_imports_package_map(tmp_path: Path) -> None:
    lake = tmp_path / ".lake" / "packages" / "mathlib"
    (lake / "Mathlib" / "Data").mkdir(parents=True)
    (lake / "Mathlib" / "Data" / "Nat.lean").write_text("def nat_x : Nat := 0\n", encoding="utf-8")
    content = "import Mathlib.Data.Nat\n"
    result = mod.find_and_read_imports(content, str(tmp_path), web_search=False)
    assert "nat_x" in result


def test_find_and_read_imports_skips_large(tmp_path: Path) -> None:
    src = tmp_path / "Big.lean"
    src.write_text("x" * (mod.MAX_IMPORT_FILE_SIZE + 100), encoding="utf-8")
    content = "import Big\n"
    result = mod.find_and_read_imports(content, str(tmp_path), web_search=False)
    assert result == ""


def test_find_and_read_imports_missing(tmp_path: Path) -> None:
    content = "import DoesNotExist\n"
    result = mod.find_and_read_imports(content, str(tmp_path), web_search=False)
    assert result == ""


def _make_diff_and_repo(tmp_path: Path):
    repo = tmp_path / "repo"
    repo.mkdir()
    lean_file = repo / "Test.lean"
    lean_file.write_text(
        "theorem existing : True := by trivial\n"
        "def with_sorry : Nat := by\n"
        "  sorry\n",
        encoding="utf-8",
    )
    diff = tmp_path / "changes.diff"
    diff.write_text(
        "diff --git a/Test.lean b/Test.lean\n"
        "--- a/Test.lean\n"
        "+++ b/Test.lean\n"
        "+def with_sorry : Nat := by\n"
        "+  sorry\n",
        encoding="utf-8",
    )
    return repo, diff


def test_find_sorries_in_diff_basic(tmp_path: Path) -> None:
    repo, diff = _make_diff_and_repo(tmp_path)
    sorries = mod.find_sorries_in_diff(str(diff), str(repo), web_search=False)
    assert len(sorries) == 1
    assert sorries[0]["decl_name"] == "with_sorry"
    assert sorries[0]["file_path"] == "Test.lean"
    assert sorries[0]["line_num"] == 3
    assert "sorry" in sorries[0]["snippet"]


def test_find_sorries_in_diff_ignores_comments(tmp_path: Path) -> None:
    repo = tmp_path / "repo"
    repo.mkdir()
    (repo / "Test.lean").write_text(
        "def clean : Nat := 1\n-- sorry comment\n", encoding="utf-8"
    )
    diff = tmp_path / "changes.diff"
    diff.write_text(
        "diff --git a/Test.lean b/Test.lean\n"
        "--- a/Test.lean\n"
        "+++ b/Test.lean\n"
        "+-- sorry comment\n",
        encoding="utf-8",
    )
    sorries = mod.find_sorries_in_diff(str(diff), str(repo), web_search=False)
    assert sorries == []


def test_find_sorries_in_diff_ignores_non_lean(tmp_path: Path) -> None:
    repo = tmp_path / "repo"
    repo.mkdir()
    diff = tmp_path / "changes.diff"
    diff.write_text(
        "diff --git a/README.md b/README.md\n"
        "--- a/README.md\n"
        "+++ b/README.md\n"
        "+sorry\n",
        encoding="utf-8",
    )
    sorries = mod.find_sorries_in_diff(str(diff), str(repo), web_search=False)
    assert sorries == []
