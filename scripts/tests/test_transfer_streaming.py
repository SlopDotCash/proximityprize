"""Compare complete streamed maxima against materialized coset sums."""
from pathlib import Path
import sys
import unittest
import numpy as np
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "probes"))
import probe_466r10_transfer_skeptic as probe

class TransferStreaming(unittest.TestCase):
    def test_all_cosets_and_partial_batches(self):
        for p in (17, 41, 97, 193):
            for n in (2, 4, 8):
                S = probe.subgroup(p, n)
                eta, _, g = probe.eta_complex_cosets(p, S, n)
                expected = float(np.max(np.abs(eta)))
                for batch in (1, 3, 17, 32768):
                    self.assertEqual(probe.max_eta_complex_cosets(p, S, n, g, batch), expected)
        with self.assertRaises(ValueError):
            probe.max_eta_complex_cosets(17, [1, 16], 2, batch_size=0)

if __name__ == "__main__":
    unittest.main()
