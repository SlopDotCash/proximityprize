"""One residual_axioms.txt entry must document exactly one `axiom` declaration.

The allowlist stores simple names, so an entry matches an `axiom` declared inside
any namespace.  Without the one-declaration rule a new axiom that clones an
allowlisted name (`namespace Sneaky … axiom <allowlisted> : False … end`) inherits
the documented entry and passes the precheck.
"""

import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "forbidden_tokens.py"
ALLOWLISTED = "foldOracleVerifier_rbrKnowledgeSoundness"
OTHER_ALLOWLISTED = "no_selfReciprocal_factor"


def scan(*paths: Path) -> "subprocess.CompletedProcess[str]":
    """Run the precheck over `paths`, with the script's own directory as cwd."""
    return subprocess.run(
        [sys.executable, str(SCRIPT), *[str(path) for path in paths]],
        capture_output=True,
        text=True,
        cwd=str(SCRIPT.parent.parent),
    )


class AllowlistIdentity(unittest.TestCase):
    def test_documented_declaration_inside_a_namespace_passes(self):
        with tempfile.TemporaryDirectory() as tmp:
            tree = Path(tmp)
            (tree / "Legit.lean").write_text(
                "namespace Binius.BinaryBasefold.CoreInteraction\n\n"
                f"axiom {ALLOWLISTED} (i : Nat) : i = i\n\n"
                "end Binius.BinaryBasefold.CoreInteraction\n",
                encoding="utf-8",
            )
            proc = scan(tree)
            self.assertEqual(proc.returncode, 0, proc.stderr)
            self.assertIn("1 allowlisted residual axiom(s)", proc.stdout)

    def test_distinct_allowlisted_names_pass(self):
        with tempfile.TemporaryDirectory() as tmp:
            tree = Path(tmp)
            (tree / "One.lean").write_text(
                f"namespace A\n\naxiom {ALLOWLISTED} : 1 = 1\n\nend A\n",
                encoding="utf-8",
            )
            (tree / "Two.lean").write_text(
                f"namespace B\n\naxiom {OTHER_ALLOWLISTED} : 1 = 1\n\nend B\n",
                encoding="utf-8",
            )
            proc = scan(tree)
            self.assertEqual(proc.returncode, 0, proc.stderr)
            self.assertIn("2 allowlisted residual axiom(s)", proc.stdout)

    def test_clone_in_a_second_file_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            tree = Path(tmp)
            (tree / "Legit.lean").write_text(
                f"namespace Binius.BinaryBasefold.CoreInteraction\n\n"
                f"axiom {ALLOWLISTED} (i : Nat) : i = i\n\n"
                f"end Binius.BinaryBasefold.CoreInteraction\n",
                encoding="utf-8",
            )
            (tree / "Clone.lean").write_text(
                f"namespace Sneaky\n\naxiom {ALLOWLISTED} : False\n\n"
                f"theorem cheat : False := {ALLOWLISTED}\n\nend Sneaky\n",
                encoding="utf-8",
            )
            proc = scan(tree)
            self.assertEqual(proc.returncode, 1, proc.stdout)
            self.assertIn(f"{ALLOWLISTED}: allowlisted residual axiom declared 2 times", proc.stderr)

    def test_clone_in_the_same_file_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            tree = Path(tmp)
            (tree / "Both.lean").write_text(
                f"namespace Legit\n\naxiom {ALLOWLISTED} : 1 = 1\n\nend Legit\n\n"
                f"namespace Sneaky\n\naxiom {ALLOWLISTED} : False\n\nend Sneaky\n",
                encoding="utf-8",
            )
            proc = scan(tree)
            self.assertEqual(proc.returncode, 1, proc.stdout)
            self.assertIn("declared 2 times", proc.stderr)

    def test_unnamespaced_clone_after_the_documented_one_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            tree = Path(tmp)
            (tree / "Legit.lean").write_text(
                f"namespace Legit\n\naxiom {ALLOWLISTED} : 1 = 1\n\nend Legit\n",
                encoding="utf-8",
            )
            (tree / "Clone.lean").write_text(
                f"axiom {ALLOWLISTED} : False\n", encoding="utf-8"
            )
            proc = scan(tree)
            self.assertEqual(proc.returncode, 1, proc.stdout)
            self.assertIn("declared 2 times", proc.stderr)


if __name__ == "__main__":
    unittest.main()
