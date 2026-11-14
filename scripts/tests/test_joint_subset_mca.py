# Copyright (c) 2026 Jonas Augustinus. All rights reserved.
# Released under the MIT and Apache 2.0 licenses as described in
# LICENSE-MIT and LICENSE.
# Authors: Jonas Augustinus (GitHub: Jonas-Augustinus-Linus)
"""An existential MCA witness survives a different, jointly decoded subset."""
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'probes'))
import probe_syz53_p_scaling as syz
import sw1_f1_middle_slot_lift as sw1


class JointSubsetMCA(unittest.TestCase):
    def test_nonjoint_witness_survives_joint_subset(self):
        # Coordinates 0,1 are joint. At z=4, coordinates 0,3 agree with zero,
        # but u1 differs on that SAME witness set: this is still MCA badness.
        u0, u1, alpha = [0, 0, 1, 1], [0, 0, 0, 1], [1, 2, 3, 4]
        bad, inf, joint, wholefield = syz.exact_badz(u0, u1, alpha, 1, 2, 5)
        self.assertEqual(bad, {0, 4})
        self.assertTrue(joint and wholefield)
        self.assertEqual(sw1.ExactCloseness(alpha, 1, 2, 5).bad_z(u0, u1),
                         (bad, inf, joint))

    def check_all_stacks_counted(self, run, owner, name):
        observed = []
        original = getattr(owner, name)

        def record(*args):
            value = original(*args)
            observed.append(value)
            return value

        with patch.object(owner, name, side_effect=record):
            result = run()
        self.assertTrue(any(value[0] and value[2] for value in observed))
        self.assertEqual(result['stacks'], len(observed))
        self.assertEqual(sum(result['dist'].values()), len(observed))

    def test_syz53_keeps_stacks_with_nonjoint_witnesses(self):
        self.check_all_stacks_counted(lambda: syz.lift_test_exact(
            [1, 2, 3, 4], 1, 2, 5, [[0, 1], [1, 2], [0, 3]], trials=20, seed=0),
            syz, 'exact_badz')

    def test_sw1_keeps_stacks_with_nonjoint_witnesses(self):
        engine = sw1.ExactCloseness([1, 2, 3, 4], 1, 2, 5)
        self.check_all_stacks_counted(lambda: sw1.lift_test(
            [1, 2, 3, 4], 1, 2, 5, [[0, 1], [1, 2], [0, 3]], engine, 0, 20),
            engine, 'bad_z')


if __name__ == '__main__':
    unittest.main()
