#!/usr/bin/env python3
"""Regression tests for unsafe / unsafeCast / implemented_by policy gates.

CI gate 1 (`scripts/forbidden_tokens.py`) previously caught only native_decide,
bv_decide, undocumented axioms, True placebos, and bodyless opaque/constant.
This module pins a repository policy precheck that also rejects live `unsafe`
declarations, `unsafeCast`, and `implemented_by`. That is independent of whether
pinned Lean accepts a given fixture: Lean 4.30 rejects `unsafe theorem`, and a
safe theorem cannot consume an unsafe def. The gate still matters as a fast
policy check (including accepted forms like `unsafe nonrec def`) and against
evaluator-diverging `implemented_by` wrappers. The honesty-audit checklist
already required reviewers to look for `unsafe` / `implemented_by` by hand;
these tests pin the automated gate.

Aesop's `(add unsafe …)` tactic hints and `attribute [aesop unsafe N%]` must
remain allowed: they use the word "unsafe" but are not Lean declaration
modifiers.
"""

from __future__ import annotations

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "forbidden_tokens.py"


def run_scan(source: str) -> subprocess.CompletedProcess[str]:
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "Probe.lean"
        path.write_text(source, encoding="utf-8")
        return subprocess.run(
            [sys.executable, str(SCRIPT), str(path)],
            capture_output=True,
            text=True,
            cwd=ROOT,
        )


class ForbiddenTokensUnsafeTests(unittest.TestCase):
    def assert_rejected(self, source: str, needle: str) -> None:
        result = run_scan(source)
        combined = result.stdout + result.stderr
        self.assertNotEqual(result.returncode, 0, combined)
        self.assertIn(needle, combined)

    def assert_clean(self, source: str) -> None:
        result = run_scan(source)
        combined = result.stdout + result.stderr
        self.assertEqual(result.returncode, 0, combined)

    def test_unsafe_theorem_with_unsafecast_is_rejected(self) -> None:
        self.assert_rejected(
            "unsafe theorem launder (P : Prop) : P := unsafeCast ()\n",
            "unsafe",
        )

    def test_unsafecast_alone_is_rejected(self) -> None:
        self.assert_rejected(
            "def bad : False := unsafeCast ()\n",
            "unsafeCast",
        )

    def test_implemented_by_is_rejected(self) -> None:
        self.assert_rejected(
            "def impl : Nat := 0\n@[implemented_by impl]\ndef wrapped : Nat := 1\n",
            "implemented_by",
        )

    def test_unsafe_nonrec_def_is_rejected(self) -> None:
        # Lean accepts modifiers between `unsafe` and the decl keyword.
        self.assert_rejected(
            "unsafe nonrec def helper : Nat := 0\n#check helper\n",
            "unsafe",
        )

    def test_nonrec_unsafe_def_is_rejected(self) -> None:
        self.assert_rejected(
            "nonrec unsafe def helper : Nat := 0\n",
            "unsafe",
        )

    def test_aesop_add_unsafe_hint_is_allowed(self) -> None:
        self.assert_clean(
            "theorem t (n : Nat) : n = n := by\n  aesop (add unsafe (by rfl))\n"
        )

    def test_aesop_unsafe_priority_attribute_is_allowed(self) -> None:
        self.assert_clean("attribute [aesop unsafe 50%] Eq.refl\n")

    def test_commented_unsafe_is_ignored(self) -> None:
        self.assert_clean(
            "-- unsafe theorem t : False := unsafeCast ()\n"
            "theorem ok (n : Nat) : n = n := rfl\n"
        )

    def test_block_commented_unsafe_is_ignored(self) -> None:
        self.assert_clean(
            "/- unsafe theorem t : False := unsafeCast () -/\n"
            "theorem ok (n : Nat) : n = n := rfl\n"
        )

    def test_native_decide_still_rejected(self) -> None:
        self.assert_rejected(
            "theorem t : True := by native_decide\n",
            "native_decide",
        )


if __name__ == "__main__":
    unittest.main()
