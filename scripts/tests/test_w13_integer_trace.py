"""Independent integer check of the W13 directed-edge matrix construction."""
from pathlib import Path
import sys
import unittest

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'probes'))
import probe_w13_wavekernel_trace as probe


class IntegerTraceComparison(unittest.TestCase):
    def test_directed_edge_powers_match_exact_integers(self):
        p, mu = 13, [1, 5, 8, 12]
        edges = [(u, (u + x) % p) for u in range(p) for x in mu]
        # Construct by endpoint incidence, independently of the producer's index formula.
        matrix = np.array([[int(v == s and t != u) for s, t in edges]
                           for u, v in edges], dtype=object)
        power = np.eye(len(edges), dtype=object)
        traces = []
        for _ in range(10):
            power = power @ matrix
            traces.append(sum(power[i, i] for i in range(len(edges))))
        self.assertEqual(probe.hashimoto_traces(p, mu, 10)[0], traces)
        self.assertEqual(traces, [0, 0, 0, 104, 520, 624, 1820, 6968, 18720, 60320])


if __name__ == '__main__':
    unittest.main()
