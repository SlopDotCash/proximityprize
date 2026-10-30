"""The P1 decoder's MCA clause must depend only on finite-field row values."""
import contextlib
import io
from itertools import product
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'probes'))
import probe_fsmf_predecessor_miniature_census as probe


class ResidueInvariance(unittest.TestCase):
    def setUp(self):
        self.p = 5
        self.xs = [1, 2, 3, 4]
        self.engine = probe.Census(5, 4, 2, 3, self.xs)
        self.code = [tuple((a + b*x) % 5 for x in self.xs)
                     for a, b in product(range(5), repeat=2)]

    def exhaustive_bad(self, u0, u1):
        bad = []
        for gamma in range(self.p):
            word = [(a + gamma*b) % self.p for a, b in zip(u0, u1)]
            for codeword in self.code:
                support = [i for i in range(4) if word[i] == codeword[i]]
                if len(support) < 3:
                    continue
                joint = all(any(all(c[i] == row[i] % self.p for i in support)
                                for c in self.code) for row in (u0, u1))
                if not joint:
                    bad.append(gamma)
                    break
        return bad

    def test_zero_codeword_does_not_refute_the_four_point_budget(self):
        with contextlib.redirect_stdout(io.StringIO()):
            bad, listing = self.engine.full_census([5]*4, [0]*4, 'lifted zero')
        self.assertEqual(bad, [])
        self.assertEqual(self.exhaustive_bad([5]*4, [0]*4), [])
        self.assertEqual(set(listing), set(range(5)))
        self.assertTrue(all(joint for rows in listing.values() for _, _, joint in rows))

    def test_genuine_nonjoint_witnesses_and_all_codeword_rows_are_invariant(self):
        rows = list(self.code) + [(0, 0, 0, 1), (0, 0, 1, 1)]
        direction = (0, 0, 1, 1)
        witnessed_bad = False
        for row in rows:
            expected = self.exhaustive_bad(row, direction)
            witnessed_bad |= bool(expected)
            lifted0 = [a + 5*(i - 2) for i, a in enumerate(row)]
            lifted1 = [a - 5*(i + 1) for i, a in enumerate(direction)]
            for gamma in range(5):
                original = self.engine.gamma_report(row, direction, gamma)
                actual = self.engine.gamma_report(lifted0, lifted1, gamma)
                self.assertEqual(actual, original)
                self.assertEqual(any(not joint for _, _, joint in actual), gamma in expected)
        self.assertTrue(witnessed_bad)


if __name__ == '__main__':
    unittest.main()
