"""Compare source-coupled interpolation against known polynomial evaluations."""
import importlib.util
from pathlib import Path
import unittest
import numpy as np

path = Path(__file__).resolve().parents[1] / 'probes/probe_noeight_source7_root_coupled_lines.py'
spec = importlib.util.spec_from_file_location('root_probe', path)
probe = importlib.util.module_from_spec(spec)
spec.loader.exec_module(probe)


class Interpolation(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = probe.setup()

    def test_every_anchor_recovers_known_coefficients(self):
        coefficients = np.asarray([3, 5, 7, 2])
        values = coefficients @ self.data['vand_v'].T % 17
        result = probe.classify_batch(values[None, :], np.zeros((1, 9), dtype=np.int64), self.data)
        recovered = result[1]
        self.assertTrue(np.all(recovered == coefficients))
        self.assertTrue(np.all(result[2] == 9))

    def test_joint_core_contains_the_source(self):
        # Arbitrary nonpolynomial rows still share their seven prescribed zeros.
        row0 = np.asarray([1, 4, 8, 2, 9, 3, 6, 5, 7])
        row1 = np.asarray([2, 7, 3, 8, 4, 9, 1, 6, 5])
        maximum, a, b = probe.global_core_max(row0, row1, self.data)
        self.assertGreaterEqual(maximum, 7)
        full0 = np.concatenate([row0, np.zeros(7, dtype=np.int64)])
        full1 = np.concatenate([row1, np.zeros(7, dtype=np.int64)])
        joint = (self.data['vandermonde'] @ a % 17 == full0) & (self.data['vandermonde'] @ b % 17 == full1)
        self.assertEqual(int(joint.sum()), maximum)
