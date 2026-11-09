"""Finite scalar budgets must not include the pencil point at infinity."""
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'probes'))
import probe_syz53_p_scaling as syz
import sw1_f1_middle_slot_lift as sw1


class FinitePencilCounts(unittest.TestCase):
    def test_four_point_witness_has_three_finite_scalars(self):
        args = ([0, 0, 1, 1], [0, 1, 0, 1], [1, 2, 3, 4], 1, 2, 5)
        bad, inf, joint, wholefield = syz.exact_badz(*args)
        self.assertEqual(bad, {0, 1, 4})
        self.assertTrue(inf)
        self.assertFalse(joint or wholefield)
        engine = sw1.ExactCloseness(args[2], 1, 2, 5)
        self.assertEqual(engine.bad_z(*args[:2]), (bad, inf, joint))

    def check_counts(self, run, owner, name):
        observed = []
        original = getattr(owner, name)

        def record(*args):
            value = original(*args)
            observed.append(value)
            return value

        with patch.object(owner, name, side_effect=record):
            result = run()
        finite = [len(value[0]) for value in observed]
        self.assertTrue(any(value[1] and not value[2] for value in observed))
        self.assertEqual(result['maxbad'], max(finite))
        self.assertLessEqual(result['maxbad'], 5)
        self.assertTrue(all(n <= 5 for n in result['dist']))
        self.assertEqual(sum(result['dist'].values()), result['stacks'])

    def test_syz53_aggregation_uses_finite_budget(self):
        self.check_counts(lambda: syz.lift_test_exact(
            [1, 2, 3, 4], 1, 2, 5, [[0, 1], [1, 2], [0, 3]], trials=20, seed=0),
            syz, 'exact_badz')

    def test_sw1_aggregation_uses_finite_budget(self):
        engine = sw1.ExactCloseness([1, 2, 3, 4], 1, 2, 5)
        self.check_counts(lambda: sw1.lift_test(
            [1, 2, 3, 4], 1, 2, 5, [[0, 1], [1, 2], [0, 3]], engine, 0, 20),
            engine, 'bad_z')


if __name__ == '__main__':
    unittest.main()
