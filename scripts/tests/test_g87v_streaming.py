"""Check bounded-storage census summaries against the original full matrices."""
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'probes'))
import probe_466_g87v_census_rank as probe


class StreamingCensus(unittest.TestCase):
    def test_summaries_match_full_enumeration(self):
        for n, p in ((4, 17), (8, 17), (8, 41)):
            roots = probe.nth_roots(n, p)
            for t in roots:
                matrix = probe.census_rows(n, p, t)
                expected = (len(matrix), tuple(probe.rank_mod(matrix, q) for q in
                            (probe.Q_AUX, probe.Q_AUX2, p)),
                            probe.common_coverage(matrix, roots, p, n))
                self.assertEqual(probe.census_summary(n, p, t, roots, 37), expected)
                self.assertTrue(all(len(batch) <= 37 for batch in
                                    probe.census_batches(n, p, t, 37)))


if __name__ == '__main__':
    unittest.main()
