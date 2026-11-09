"""The G92 exact-counter self-test must run under optimized Python too."""
from pathlib import Path
import subprocess
import sys
import textwrap
import unittest


PROBES = Path(__file__).resolve().parents[1] / "probes"


class G92OptimizationGuards(unittest.TestCase):
    def test_self_test_rejects_a_disagreeing_engine_under_optimization(self):
        code = textwrap.dedent(
            f"""
            import sys
            sys.path.insert(0, {str(PROBES)!r})
            import numpy as np
            import probe_g92_spread_excess_c3 as probe

            class WrongAmbient:
                n, k, q = 8, 2, 4129

                def __init__(self, *args): pass
                def mono(self, exponent): return np.zeros(8, dtype=np.int64)
                def pack(self, direction): return object()
                def fast_counts(self, offsets, pack, threshold):
                    return np.ones(len(offsets), dtype=np.int64)
                def fast_bad_list(self, offset, pack, threshold): return [0]
                def brute_count(self, offset, direction, threshold,
                                gchunk=256, collect=False):
                    return (0, []) if collect else 0

            probe.Ambient = WrongAmbient
            probe.chain_seed = lambda amb, direction, threshold, rng: np.zeros(8)
            probe.self_test(np.random.default_rng(0))
            """
        )
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = subprocess.run(
                    [sys.executable, flag, "-c", code],
                    capture_output=True,
                    text=True,
                    check=False,
                )
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("MISMATCH #0: fast=1 brute=0", result.stderr)


if __name__ == "__main__":
    unittest.main()
