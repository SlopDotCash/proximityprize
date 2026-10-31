"""The coset-escape probe must report its true escape dimension (audit L117).

The synthetic q=1009 cell has nullity k - n = 56, not 1, so the probe must not
claim a one-dimensional escape dichotomy; the constant-proportional scalar pin
is reported only as a conditional lemma.
"""
from pathlib import Path
import subprocess
import sys
import unittest

path = Path(__file__).resolve().parents[1] / 'probes/probe_rate_quarter_p1_stepanov_weld.py'


class EscapeDimension(unittest.TestCase):
    def test_reported_dimension_and_scope(self):
        run = subprocess.run([sys.executable, str(path)], capture_output=True, text=True,
                             timeout=300, check=False)
        self.assertEqual(run.returncode, 0, run.stderr)
        out = run.stdout
        self.assertIn('exact solution dim = 56 (vars 112)', out)
        self.assertIn('NO one-dimensional escape dichotomy is established', out)
        self.assertIn('CONDITIONAL', out)
        for stale in ('All known escapes are dim-1', 'the honest residual is',
                      'kernel-provable', 'the collapse is exact'):
            self.assertNotIn(stale, out)


if __name__ == '__main__':
    unittest.main()
