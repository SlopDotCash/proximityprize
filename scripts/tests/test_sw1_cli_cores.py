# Copyright (c) 2026 nubs. All rights reserved.
# Released under the MIT and Apache 2.0 licenses as described in
# LICENSE-MIT and LICENSE.
# Authors: nubs (with Codex assistance)
"""Exercise all three main-path lifts on field domains distinct from indices."""

from contextlib import redirect_stdout
import io
import os
from pathlib import Path
import random
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'probes'))
import sw1_f1_middle_slot_lift as sw1


class SW1CLICores(unittest.TestCase):
    def test_main_translates_all_three_lift_paths(self):
        # Keep the real Part A/C/D certificate checks and lift parity construction.
        # Zero sampling trials avoid expensive parity tensors and sampled statistics.
        # Seed the Part C search with the known, genuine Part A linear occupant.
        sac = [2, 25, 37, 23, 39, 1]
        sbc = [8, 18, 16, 10, 5, 36]
        original_random = random.Random

        class OccupantRandom(original_random):
            def __init__(self, seed=None):
                super().__init__(seed)
                self.review_seed = seed

            def shuffle(self, values):
                if self.review_seed == 7041:
                    leading = sac + sbc
                    values[:] = leading + [x for x in values if x not in leading]
                else:
                    super().shuffle(values)

        calls = []
        original_lift = sw1.lift_test

        def record_lift(alpha, k, s, p, cores, engine, seed, trials):
            self.assertNotEqual(alpha, list(range(len(alpha))))
            self.assertTrue(all(0 <= j < len(alpha) for core in cores for j in core))
            self.assertTrue(all(len(core) == s for core in cores))
            calls.append((len(alpha), p, seed))
            return original_lift(alpha, k, s, p, cores, engine, seed, trials)

        options = dict(SW1_B_TRIALS='0', SW1_C_PAIRS='1', SW1_C_TRIALS='0',
                       SW1_D_TRIALS='0', SW1_QUICK='1', SW1_D_N24='0')
        output = io.StringIO()
        with patch.dict(os.environ, options), \
                patch.object(sw1.random, 'Random', OccupantRandom), \
                patch.object(sw1, 'ExactCloseness', return_value=object()), \
                patch.object(sw1, 'lift_test', side_effect=record_lift), \
                redirect_stdout(output):
            self.assertEqual(sw1.main(), 0, output.getvalue())

        self.assertEqual(calls.count((20, 41, 101)), 1)  # Part B
        self.assertEqual(calls.count((20, 41, 52)), 1)   # Part C found a real occupant
        # Part D exercises both coset variants for every configured quick prime.
        coset_calls = [call for call in calls if call[2] in (31 + call[1], 32 + call[1])]
        self.assertEqual(len(coset_calls), 16)
        self.assertEqual({n for n, _, _ in coset_calls}, {16, 20})
        self.assertIn('PASS (all exact verifications hold', output.getvalue())


if __name__ == '__main__':
    unittest.main()
