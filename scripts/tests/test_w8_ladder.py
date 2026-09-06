"""Verify the integer ladder formula against its original feasibility predicate."""
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'probes'))
import probe_w8_multicore_ladder as probe

class LadderMaximum(unittest.TestCase):
    def test_formula_against_exhaustive_search(self):
        for s in range(8, 258, 2):
            for c in range(1, 21):
                for budget in (1, 2):
                    expected = max((g for g in range(1, s//2)
                                    if probe.feasible(s, c, g, budget)), default=None)
                    self.assertEqual(probe.largest_feasible_g(s, c, budget), expected)
        with self.assertRaises(ValueError):
            probe.largest_feasible_g(64, 0, 1)

if __name__ == '__main__':
    unittest.main()
