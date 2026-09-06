"""Regression for configurable domains and affine scalar reparameterization."""
import contextlib
import importlib.util
import io
from pathlib import Path
import unittest

path = Path(__file__).resolve().parents[1] / 'probes/probe_noeight_n9k4_weight3_lines.py'
spec = importlib.util.spec_from_file_location('noeight', path)
probe = importlib.util.module_from_spec(spec)
spec.loader.exec_module(probe)


class CouplingInputs(unittest.TestCase):
    def test_rotated_domain_and_shifted_scalar(self):
        domain, columns, supports, low, high = probe.setup(tuple(range(1, 10)))
        base = (12, 8, 5, 8, 10)
        direction = (13, 0, 14, 15, 4)
        # Rotate evaluation points by 3, and replace gamma with gamma + 2.
        rotated_base = tuple((base[j] + 2 * direction[j]) * pow(3, j, 17) % 17 for j in range(5))
        rotated_direction = tuple(direction[j] * pow(3, j, 17) % 17 for j in range(5))
        witnesses = probe.certificate(rotated_base, rotated_direction, columns, supports, low, high)
        self.assertEqual(len(witnesses), 13)
        # Explicitly exercise anchors other than the formerly required 0 and 1.
        selected = [w for w in witnesses if w['gamma'] not in (0, 1)]
        with contextlib.redirect_stdout(io.StringIO()):
            result = probe.source_root_coupling_audit(selected, domain)
        self.assertTrue(set(result['anchor_gammas']).isdisjoint({0, 1}))
        self.assertEqual(set(result['source_core']), {pow(3, i, 17) for i in range(16)} - set(domain))
        self.assertEqual(result['candidate_lifts_checked'], 560 ** 2)

    def test_invalid_search_inputs(self):
        for samples, batch, domain in [(0, 1, range(9)), (1, 0, range(9)), (1, 1, [0] * 9), (1, 1, range(8, 17))]:
            with self.assertRaises(ValueError):
                probe.run(samples, batch, 0, tuple(domain))
