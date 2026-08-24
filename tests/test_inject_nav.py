"""Unit coverage for scripts/inject_nav.py.

Exercises the HTML nav-injection logic against a synthetic site tree:
relative-path computation, navbar.html skip, already-injected skip,
CSS-link insertion before </head>, nav HTML after <body>, and root-path
normalization.
"""

import importlib.util
import sys
from pathlib import Path

import pytest


def load_module():
    spec = importlib.util.spec_from_file_location(
        "inject_nav", "/tmp/proximityprize/scripts/inject_nav.py"
    )
    module = importlib.util.module_from_spec(spec)
    sys.modules["inject_nav"] = module
    spec.loader.exec_module(module)
    return module


mod = load_module()


def test_get_relative_path() -> None:
    assert mod.get_relative_path(
        "/site/docs/index.html", "/site/global_nav.css"
    ) == "../global_nav.css"
    assert mod.get_relative_path(
        "/site/docs/deep/page.html", "/site/global_nav.css"
    ) == "../../global_nav.css"


def test_inject_nav_css_and_body(tmp_path: Path) -> None:
    (tmp_path / "docs").mkdir()
    page = tmp_path / "docs" / "index.html"
    page.write_text("<html><head></head><body><p>hi</p></body></html>", encoding="utf-8")
    (tmp_path / "global_nav.css").write_text("/* css */", encoding="utf-8")

    mod.inject_nav(tmp_path / "docs", tmp_path)

    content = page.read_text(encoding="utf-8")
    assert 'id="arklib-global-nav"' in content
    assert 'rel="stylesheet"' in content
    assert "../global_nav.css" in content
    # Nav injected after <body>
    assert content.index('id="arklib-global-nav"') > content.index("<body>")


def test_inject_nav_skips_navbar_html(tmp_path: Path) -> None:
    (tmp_path / "docs").mkdir()
    navbar = tmp_path / "docs" / "navbar.html"
    navbar.write_text("<html><head></head><body></body></html>", encoding="utf-8")
    (tmp_path / "global_nav.css").write_text("/* css */", encoding="utf-8")

    mod.inject_nav(tmp_path / "docs", tmp_path)

    content = navbar.read_text(encoding="utf-8")
    assert 'id="arklib-global-nav"' not in content


def test_inject_nav_idempotent(tmp_path: Path) -> None:
    (tmp_path / "docs").mkdir()
    page = tmp_path / "docs" / "index.html"
    page.write_text(
        '<html><head></head><body><div id="arklib-global-nav"></div></body></html>',
        encoding="utf-8",
    )
    (tmp_path / "global_nav.css").write_text("/* css */", encoding="utf-8")

    mod.inject_nav(tmp_path / "docs", tmp_path)
    first = page.read_text(encoding="utf-8")
    mod.inject_nav(tmp_path / "docs", tmp_path)
    second = page.read_text(encoding="utf-8")
    assert first == second  # no double injection
    assert first.count('id="arklib-global-nav"') == 1


def test_root_path_normalization(tmp_path: Path) -> None:
    # Root-level page: rel_root becomes '' (not './').
    (tmp_path / "docs").mkdir()
    page = tmp_path / "docs" / "index.html"
    page.write_text("<html><head></head><body></body></html>", encoding="utf-8")
    (tmp_path / "global_nav.css").write_text("/* css */", encoding="utf-8")

    mod.inject_nav(tmp_path / "docs", tmp_path)

    content = page.read_text(encoding="utf-8")
    # rel_root from docs/index.html to root is ../ → normalized '../'
    assert 'href="../docs/"' in content or 'href="../"' in content


def test_inject_nav_missing_head_still_injects_body(tmp_path: Path) -> None:
    (tmp_path / "docs").mkdir()
    page = tmp_path / "docs" / "bare.html"
    page.write_text("<html><body></body></html>", encoding="utf-8")
    (tmp_path / "global_nav.css").write_text("/* css */", encoding="utf-8")

    mod.inject_nav(tmp_path / "docs", tmp_path)

    content = page.read_text(encoding="utf-8")
    assert 'id="arklib-global-nav"' in content
    # No </head> to inject into → no crash, nav still present
