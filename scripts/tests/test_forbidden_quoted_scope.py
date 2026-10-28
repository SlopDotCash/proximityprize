"""Real Lean quoted identifiers must not introduce command scope state."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCANNER = Path(__file__).resolve().parents[1] / 'forbidden_tokens.py'
LEAN = os.environ.get('LEAN_TEST_EXECUTABLE')

@unittest.skipUnless(LEAN, 'requires the pinned Lean fixture compiler')
class QuotedScopeRegression(unittest.TestCase):
    def check_fixture(self, quoted_lines):
        source = ('def «marker\n' + quoted_lines + '» : Nat := 0\n'
                  'theorem mcaPrizeResidual : True := trivial\n'
                  '#check mcaPrizeResidual\n#print axioms mcaPrizeResidual\n')
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / 'Probe.lean'
            path.write_text(source, encoding='utf-8')
            compiled = subprocess.run([LEAN, str(path)], capture_output=True,
                                      text=True, timeout=30)
            self.assertEqual(compiled.returncode, 0, compiled.stdout + compiled.stderr)
            self.assertIn('mcaPrizeResidual : True', compiled.stdout)
            self.assertIn("'mcaPrizeResidual' does not depend on any axioms", compiled.stdout)
            scanned = subprocess.run([sys.executable, str(SCANNER), str(path)],
                                     capture_output=True, text=True, timeout=30)
            self.assertNotEqual(scanned.returncode, 0, scanned.stdout + scanned.stderr)
            self.assertIn('forbidden vacuous placebo', scanned.stderr)

    def test_quoted_variable_does_not_rebind_true(self):
        self.check_fixture('variable (True : Prop)')

    def test_quoted_namespace_does_not_open_scope(self):
        self.check_fixture('namespace Fake\ndef True')
