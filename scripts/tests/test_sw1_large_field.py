"""Large-prime parity minors must preserve exact SW1 MCA witnesses."""
from pathlib import Path
import random
import sys
import unittest

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'probes'))
import probe_syz53_p_scaling as scalar
import sw1_f1_middle_slot_lift as sw1


class LargeFieldCloseness(unittest.TestCase):
    def test_planted_zero_codeword_is_not_lost_to_overflow(self):
        p = 4294967291
        u0 = [827498355, 1483646168, 1452515851]
        u1 = [946785248, 1929338154, 2530876844]
        z = 1194819984
        self.assertEqual([(x + z*y) % p for x, y in zip(u0, u1)], [0, 0, 0])
        engine = sw1.ExactCloseness([1, 2, 3], 1, 3, p)
        self.assertEqual(engine.bad_z(u0, u1), ({z}, False, False))

    def test_matches_independent_scalar_nullspace_oracle(self):
        rng = random.Random(416)
        alpha = [1, 2, 3, 4, 5]
        for p in (17, 2147483647, 4294967291, (1 << 61) - 1):
            engine = sw1.ExactCloseness(alpha, 2, 4, p)
            for _ in range(12):
                u1 = [rng.randrange(p) for _ in alpha]
                z = rng.randrange(p)
                u0 = [(3 + 2*x - z*y) % p for x, y in zip(alpha, u1)]
                expected = scalar.exact_badz(u0, u1, alpha, 2, 4, p)[:3]
                with self.subTest(p=p):
                    self.assertEqual(engine.bad_z(u0, u1), expected)

    def test_object_matvec_uses_exact_integer_accumulation(self):
        p = (1 << 61) - 1
        H = np.full((2, 4), p - 1, dtype=object)
        u = np.full(4, p - 1, dtype=object)
        self.assertEqual(sw1.matvec_mod(H, u, p).tolist(), [4, 4])


if __name__ == '__main__':
    unittest.main()
