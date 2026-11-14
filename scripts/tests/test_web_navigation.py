# Copyright (c) 2026 nubs. All rights reserved.
# Released under the MIT and Apache 2.0 licenses as described in
# LICENSE-MIT and LICENSE.
# Authors: nubs (with Codex assistance)
"""Check navigation against the assembled public site, independently of source layout."""
import importlib.util
from html.parser import HTMLParser
from pathlib import Path
import shutil
import tempfile
import unittest
from urllib.parse import urlsplit


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location("inject_nav", ROOT / "scripts/inject_nav.py")
NAV = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(NAV)


class Links(HTMLParser):
    def __init__(self, html):
        super().__init__()
        self.hrefs = []
        self.feed(html)

    def handle_starttag(self, tag, attrs):
        self.hrefs.extend(value for name, value in attrs if name == "href")


class WebNavigationTests(unittest.TestCase):
    def fixture(self, directory):
        site = Path(directory) / "site"
        shutil.copytree(ROOT / "website/library", site)
        for name in ("docs/index.html", "blueprint/index.html", "blueprint.pdf"):
            path = site / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("placeholder")
        return site

    def assert_local_links_exist(self, html, current):
        for href in Links(html).hrefs:
            url = urlsplit(href)
            if url.scheme or url.netloc or not url.path:
                continue
            self.assertTrue((current.parent / url.path).exists(), href)

    def test_authored_homepage_uses_public_output_paths(self):
        with tempfile.TemporaryDirectory() as directory:
            site = self.fixture(directory)
            homepage = site / "index.html"
            html = homepage.read_text()
            self.assert_local_links_exist(html, homepage)
            self.assertIn("https://github.com/SlopDotCash/proximityprize", Links(html).hrefs)

    def test_nested_document_navigation_resolves_and_is_idempotent(self):
        with tempfile.TemporaryDirectory() as directory:
            site = self.fixture(directory)
            document = site / "docs/ArkLib/Basic.html"
            document.parent.mkdir(parents=True)
            document.write_text('<html><head></head><body class="docs">API</body></html>')
            NAV.inject_nav(str(site), str(site))
            html = document.read_text()
            self.assertEqual(html.count('id="arklib-global-nav"'), 1)
            self.assert_local_links_exist(html, document)
            self.assertIn("https://github.com/SlopDotCash/proximityprize", Links(html).hrefs)
            NAV.inject_nav(str(site), str(site))
            self.assertEqual(document.read_text(), html)

    def test_navigation_does_not_rewrite_symlinked_html(self):
        with tempfile.TemporaryDirectory() as directory:
            site = self.fixture(directory)
            outside = Path(directory) / "outside.html"
            original = "<html><head></head><body>outside</body></html>"
            outside.write_text(original)
            (site / "docs/linked.html").symlink_to(outside)
            NAV.inject_nav(str(site), str(site))
            self.assertEqual(outside.read_text(), original)


if __name__ == "__main__":
    unittest.main()
