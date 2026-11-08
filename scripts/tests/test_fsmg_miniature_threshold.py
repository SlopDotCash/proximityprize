"""Regression: the fixed-degree FSMG census must not run below agreement 18.

`probe_fsmg_miniature_extremal.census` uses a multiplicity-1 GS decoder of
(1,7)-weighted degree 17, which is complete only at agreement >= 18.  On the
isolated-fibre F_97 [32,8] stack the complete multiplicity-2 engine of
`probe_fsmf_predecessor_miniature_census` finds 36 bad scalars at agreement 17
while the fixed decoder would report 0, so lower thresholds must be rejected.
"""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'probes'))
import probe_fsmg_miniature_extremal as fsmg  # noqa: E402

try:
    import probe_fsmf_predecessor_miniature_census as fsmf  # noqa: E402
except ImportError:  # numpy missing
    fsmf = None

BAD_AT_17 = [1, 8, 12, 17, 18, 19, 20, 22, 26, 27, 28, 30, 33, 34, 40, 42, 46,
             47, 50, 51, 55, 57, 63, 64, 67, 69, 70, 71, 75, 77, 78, 79, 80, 85,
             89, 96]


class FixedDecoderThreshold(unittest.TestCase):
    def setUp(self):
        self.p = fsmg.ISOLATED_FIBRE_P
        self.xs = fsmg.isolated_fibre_domain()
        self.u0 = fsmg.ISOLATED_FIBRE_U0
        self.u1 = fsmg.ISOLATED_FIBRE_U1

    def test_rejects_threshold_below_decoder_radius(self):
        for thresh in (17, 10, 0):
            with self.assertRaises(ValueError):
                fsmg.census(self.u0, self.u1, self.xs, self.p, thresh=thresh)

    def test_agreement_18_is_zero(self):
        self.assertEqual(fsmg.census(self.u0, self.u1, self.xs, self.p), [])

    @unittest.skipIf(fsmf is None, 'numpy unavailable')
    def test_complete_engine_finds_36_at_17_and_0_at_18(self):
        engine17 = fsmf.Census(self.p, 32, 8, 17, self.xs)
        bad17, _ = engine17.full_census(self.u0, self.u1, 'fsmg-threshold-17')
        self.assertEqual(bad17, BAD_AT_17)
        engine18 = fsmf.Census(self.p, 32, 8, 18, self.xs)
        bad18, _ = engine18.full_census(self.u0, self.u1, 'fsmg-threshold-18')
        self.assertEqual(bad18, [])


if __name__ == '__main__':
    unittest.main()
