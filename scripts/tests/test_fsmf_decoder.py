"""Compare the GS candidate decoder with exhaustive low-degree codewords."""
import itertools
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'probes'))
import probe_fsmf_predecessor_miniature_census as probe

class CompleteDecoder(unittest.TestCase):
    def test_every_word_over_five(self):
        p, xs, k, threshold = 5, [1, 2, 3, 4], 2, 3
        engine = probe.Census(p, len(xs), k, threshold, xs)
        polynomials = [tuple(probe.trim(list(c), p))
                       for c in itertools.product(range(p), repeat=k)]
        for word in itertools.product(range(p), repeat=len(xs)):
            expected = {c for c in polynomials
                        if sum(probe.peval(c, x, p) == value
                               for x, value in zip(xs, word)) >= threshold}
            actual = {c for c, _, _ in engine.gamma_report(word, [0]*len(xs), 0)}
            self.assertEqual(actual, expected, word)

if __name__ == '__main__':
    unittest.main()
