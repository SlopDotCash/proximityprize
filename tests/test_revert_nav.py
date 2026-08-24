"""Unit coverage for scripts/revert_nav.py.

Exercises the nav-reversion logic against a synthetic site tree: CSS-link
removal, nested-div block removal (the injected nav has nested divs), and
idempotence.
"""

import importlib.util
import sys
from pathlib import Path

import pytest


def load_module():
    spec = importlib.util.spec_from_file_location(
        "revert_nav", str((Path(__file__).resolve().parents[1] / "scripts/revert_nav.py"))
    )
    module = importlib.util.module_from_spec(spec)
    sys.modules["revert_nav"] = module
    spec.loader.exec_module(module)
    return module


mod = load_module()


INJECTED = (
    '<html><head><link rel="stylesheet" href="../global_nav.css"></head>'
    '<body><div id="arklib-global-nav">'
    '<div class="container"><a href="../index.html">ArkLib</a></div>'
    '</div><p>content</p></body></html>'
)


def test_revert_nav_removes_css_and_nav(tmp_path: Path) -> None:
    (tmp_path / "docs").mkdir()
    page = tmp_path / "docs" / "index.html"
    page.write_text(INJECTED, encoding="utf-8")

    mod.revert_nav(tmp_path / "docs")

    content = page.read_text(encoding="utf-8")
    assert "global_nav.css" not in content
    assert 'id="arklib-global-nav"' not in content
    assert "<p>content</p>" in content


def test_revert_nav_keeps_clean_files(tmp_path: Path) -> None:
    (tmp_path / "docs").mkdir()
    page = tmp_path / "docs" / "index.html"
    page.write_text("<html><body><p>no nav</p></body></html>", encoding="utf-8")

    mod.revert_nav(tmp_path / "docs")

    content = page.read_text(encoding="utf-8")
    assert "<p>no nav</p>" in content
    assert 'id="arklib-global-nav"' not in content


def test_revert_nav_idempotent(tmp_path: Path) -> None:
    (tmp_path / "docs").mkdir()
    page = tmp_path / "docs" / "index.html"
    page.write_text(INJECTED, encoding="utf-8")

    mod.revert_nav(tmp_path / "docs")
    first = page.read_text(encoding="utf-8")
    mod.revert_nav(tmp_path / "docs")
    second = page.read_text(encoding="utf-8")
    assert first == second


def test_revert_nav_handles_nested_divs_correctly(tmp_path: Path) -> None:
    # The injected nav has nested divs: outer + container + links. The
    # revert must remove the whole outer block, not stop at the first </div>.
    (tmp_path / "docs").mkdir()
    page = tmp_path / "docs" / "index.html"
    page.write_text(INJECTED, encoding="utf-8")

    mod.revert_nav(tmp_path / "docs")

    content = page.read_text(encoding="utf-8")
    # Content after the nav block survives.
    assert "<p>content</p>" in content
    # No leftover fragment of the nav.
    assert "container" not in content
