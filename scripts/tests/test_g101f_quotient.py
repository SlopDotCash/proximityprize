"""Check the offset quotient against exhaustive scalar/codeword enumeration."""
import itertools
from pathlib import Path
import sys
import unittest
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'probes'))
import probe_g101f_monomial_baseline as probe

class OffsetQuotient(unittest.TestCase):
    def test_every_offset_matches_unique_representative(self):
        q, n, k, a = 5, 4, 1, 2
        amb = probe.g92.Ambient(n, k, q)
        offsets = list(itertools.product(range(q), repeat=n))
        for exponent in (1, 3):
            direction = amb.mono(exponent)
            pivots, rank = probe.rref_pivots([amb.mono(0), direction], q)
            self.assertEqual(rank, 2)
            def count(u):
                return sum(any(sum((u[i] + gamma * int(direction[i])) % q == c
                                   for i in range(n)) >= a for c in range(q))
                           for gamma in range(q))
            independent = {u: count(u) for u in offsets}
            engine = amb.fast_counts(np.array(offsets), amb.pack(direction), a)
            self.assertEqual(engine.tolist(), list(independent.values()))
            representatives = {u for u in offsets if all(u[i] == 0 for i in pivots)}
            self.assertEqual(len(representatives), q ** (n-rank))
            for u in offsets:
                reduced = {tuple((u[i]+c+beta*int(direction[i])) % q for i in range(n))
                           for c in range(q) for beta in range(q)} & representatives
                self.assertEqual(len(reduced), 1)
                self.assertEqual(independent[u], independent[reduced.pop()])
            self.assertEqual(max(independent.values()),
                             max(independent[u] for u in representatives))

if __name__ == '__main__':
    unittest.main()
