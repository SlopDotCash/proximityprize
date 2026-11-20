"""Field primes used by the G85 predecessor sweep and the cubic high ladder must be certified.

The twelve-base Miller-Rabin set 2..37 is deterministic only below
318665857834031151167461 (Sorenson-Webster, Thm 1.1). That composite itself
passes every one of those bases. The thirteen-base set 2..41 is deterministic
below 3317044064679887385961981, which is the bound the G85 sweep actually needs:
its published 2^80 field sits strictly between the two limits.
"""
from math import isqrt
from pathlib import Path
import sys
import unittest

PROBES = Path(__file__).resolve().parents[1] / "probes"
sys.path.insert(0, str(PROBES))
import probe_rate_half_predecessor_count_largefield as g85  # noqa: E402
import probe_ztz_beta3_high_ladder as high  # noqa: E402

TWELVE_BASE_PSEUDOPRIME = 318665857834031151167461
THIRTEEN_BASE_LIMIT = 3317044064679887385961981
# Smallest prime >= 2^80 with p ≡ 1 (mod 64). It is above the twelve-base proof
# and below the thirteen-base proof, so only the longer witness set certifies it.
FIELD_AT_TWO_TO_EIGHTY = 1208925819614629174707521


class G85FieldPrimeCertificate(unittest.TestCase):
    def test_twelve_base_pseudoprime_is_not_a_field(self):
        self.assertEqual(399165290221 * 798330580441, TWELVE_BASE_PSEUDOPRIME)
        self.assertFalse(g85.is_prime(TWELVE_BASE_PSEUDOPRIME))
        self.assertLess(TWELVE_BASE_PSEUDOPRIME, 1 << 80)
        self.assertLess(1 << 80, THIRTEEN_BASE_LIMIT)

    def test_published_two_to_the_eighty_field_stays_certified(self):
        selected = g85.next_prime_1_mod(64, 1 << 80)
        self.assertEqual(selected, FIELD_AT_TWO_TO_EIGHTY)
        self.assertEqual(selected % 64, 1)
        self.assertGreaterEqual(selected, TWELVE_BASE_PSEUDOPRIME)
        self.assertLess(selected, g85._MR13_DET_LIMIT)
        self.assertEqual(
            g85._MR_BASES,
            (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41),
        )
        self.assertTrue(g85.is_prime(selected))

    def test_thirteen_base_limit_is_refused(self):
        self.assertEqual(g85._MR13_DET_LIMIT, THIRTEEN_BASE_LIMIT)
        with self.assertRaises(ValueError):
            g85.is_prime(THIRTEEN_BASE_LIMIT)
        with self.assertRaises(ValueError):
            g85.next_prime_1_mod(64, THIRTEEN_BASE_LIMIT)

    def test_in_range_cells_agree_with_trial_division(self):
        def trial(m):
            return m >= 2 and all(m % d for d in range(2, isqrt(m) + 1))

        for m in range(0, 3000):
            self.assertEqual(g85.is_prime(m), trial(m), m)
        self.assertTrue(g85.is_prime((1 << 31) - 1))
        self.assertFalse(g85.is_prime(3215031751))
        self.assertEqual(g85.next_prime_1_mod(64, 1 << 57), 144115188075856001)


class HighLadderTwelveBaseRange(unittest.TestCase):
    def test_known_pseudoprime_is_outside_the_proven_range(self):
        self.assertEqual(high._MR12_DET_LIMIT, TWELVE_BASE_PSEUDOPRIME)
        with self.assertRaises(ValueError):
            high.is_prime(TWELVE_BASE_PSEUDOPRIME)
        with self.assertRaises(ValueError):
            high.is_prime(THIRTEEN_BASE_LIMIT - 1)

    def test_default_windows_remain_inside_the_twelve_base_proof(self):
        for n in (8192, 16384):
            self.assertLess(2 * n ** 3, high._MR12_DET_LIMIT)
        self.assertTrue(high.is_prime(8191))
        self.assertFalse(high.is_prime(8191 * 8191))
        self.assertFalse(high.is_prime(4))
        self.assertTrue(high.is_prime((1 << 31) - 1))


if __name__ == "__main__":
    unittest.main()
