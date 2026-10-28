#!/usr/bin/env python3
"""Every declaration head Lean accepts must reach the axiom allowlist check.

The precheck used to match only one attribute group followed by
`protected|private|scoped` at the start of a *physical* line, and only ASCII
names. Each form below therefore hid a custom axiom from
`scripts/residual_axioms.txt` even though Lean parses it as a real
declaration:

* a same-line doc comment (`/-- ... -/ axiom ...`), because the line's first
  non-space character was masked and the whole line was skipped;
* `set_option <opt> <value> in <command>` (a trailing parser over
  `commandParser` in Lean 4.30), because the line does not start with `axiom`;
* a Unicode or `«quoted»` identifier, because the name class was ASCII-only,
  which made the entire regex fail rather than just the name;
* a line break after `axiom` (allowed by `"axiom " >> declId`), because the
  scan was line-local;
* `noncomputable`/`unsafe`/`public` modifiers, which `declModifiers` accepts
  before `axiom` but the old modifier list did not include.

The same name-class gap also let bodyless `opaque` declarations and vacuous
`theorem ... : True` placebos through, so those are pinned here too.
"""

from __future__ import annotations

import os
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
            encoding="utf-8",
            # Windows defaults the child's streams to the console code page;
            # the failure messages echo Unicode declaration names.
            env={**os.environ, "PYTHONIOENCODING": "utf-8"},
            cwd=ROOT,
        )


class AxiomHeadForms(unittest.TestCase):
    def assert_rejected(self, source: str, needle: str) -> None:
        result = run_scan(source)
        combined = (result.stdout or "") + (result.stderr or "")
        self.assertNotEqual(result.returncode, 0, combined)
        self.assertIn(needle, combined)

    def assert_clean(self, source: str) -> None:
        result = run_scan(source)
        combined = (result.stdout or "") + (result.stderr or "")
        self.assertEqual(result.returncode, 0, combined)

    def test_same_line_doc_comment_does_not_hide_an_axiom(self) -> None:
        self.assert_rejected(
            "/-- tracked as a residual -/ axiom hidden : False\n",
            "forbidden custom axiom declaration hidden",
        )

    def test_set_option_in_prefix_does_not_hide_an_axiom(self) -> None:
        # `set_option <id> <value> in <command>` is documented Lean syntax;
        # the `in` is a trailing parser over commandParser.
        self.assert_rejected(
            "set_option autoImplicit false in axiom hidden : False\n",
            "forbidden custom axiom declaration hidden",
        )

    def test_unicode_identifier_is_still_a_declared_axiom(self) -> None:
        # `α` is an ordinary Lean identifier; `ident`/`declId` are Unicode.
        self.assert_rejected(
            "axiom \u03b1 : False\n",
            "forbidden custom axiom declaration \u03b1",
        )

    def test_quoted_identifier_is_still_a_declared_axiom(self) -> None:
        self.assert_rejected(
            "axiom \u00abhidden name\u00bb : False\n",
            "forbidden custom axiom declaration",
        )

    def test_line_break_after_the_keyword_is_still_a_declaration(self) -> None:
        self.assert_rejected(
            "axiom\n  hidden : False\n",
            "forbidden custom axiom declaration hidden",
        )

    def test_decl_modifiers_before_axiom_are_not_a_shield(self) -> None:
        for modifier in ("noncomputable", "unsafe", "public", "private"):
            with self.subTest(modifier=modifier):
                self.assert_rejected(
                    f"{modifier} axiom hidden : False\n",
                    "forbidden custom axiom declaration hidden",
                )

    def test_allowlisted_residual_axiom_still_passes(self) -> None:
        # A name from scripts/residual_axioms.txt must remain installable.
        self.assert_clean("axiom no_selfReciprocal_factor : False\n")

    def test_commented_out_axiom_stays_invisible(self) -> None:
        self.assert_clean(
            "/- axiom hidden : False -/\n"
            "-- axiom alsoHidden : False\n"
            "theorem helper (h : P) : Q := h\n"
        )

    def test_ordinary_declarations_stay_clean(self) -> None:
        self.assert_clean(
            "@[simp] theorem id_apply (x : Nat) : x = x := rfl\n"
            "private def two : Nat := 2\n"
            "def uses_option : String := \"set_option x y in axiom nope\"\n"
        )


class UnicodeNameCoverage(unittest.TestCase):
    """The widened name class must also reach the opaque and placebo checks."""

    def assert_rejected(self, source: str, needle: str) -> None:
        result = run_scan(source)
        combined = (result.stdout or "") + (result.stderr or "")
        self.assertNotEqual(result.returncode, 0, combined)
        self.assertIn(needle, combined)

    def test_bodyless_unicode_opaque_is_axiom_equivalent(self) -> None:
        self.assert_rejected(
            "opaque \u03b1 : False\n",
            "bodyless opaque declaration",
        )

    def test_unicode_true_placebo_is_still_vacuous(self) -> None:
        self.assert_rejected(
            "theorem \u03b1 : True := by trivial\n",
            "vacuous placebo",
        )


if __name__ == "__main__":
    unittest.main()
