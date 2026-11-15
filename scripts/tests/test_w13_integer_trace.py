"""Independent integer check of the W13 directed-edge matrix construction."""
from pathlib import Path
import subprocess
import sys
import unittest

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'probes'))
import probe_w13_wavekernel_trace as probe


class IntegerTraceComparison(unittest.TestCase):
    def test_directed_edge_powers_match_exact_integers(self):
        p, mu = 13, [1, 5, 8, 12]
        edges = [(u, (u + x) % p) for u in range(p) for x in mu]
        # Construct by endpoint incidence, independently of the producer's index formula.
        matrix = np.array([[int(v == s and t != u) for s, t in edges]
                           for u, v in edges], dtype=object)
        power = np.eye(len(edges), dtype=object)
        traces = []
        for _ in range(10):
            power = power @ matrix
            traces.append(sum(power[i, i] for i in range(len(edges))))
        self.assertEqual(probe.hashimoto_traces(p, mu, 10)[0], traces)
        self.assertEqual(traces, [0, 0, 0, 104, 520, 624, 1820, 6968, 18720, 60320])

    def run_optimized_trace(self, flag, value):
        code = (
            "import runpy\n"
            "import numpy as np\n"
            f"m = runpy.run_path({str(probe.__file__)!r})\n"
            f"print(m['_exact_int_trace'](np.array([[{value}]], dtype=np.float64)))\n"
        )
        return subprocess.run(
            [sys.executable, flag, "-c", code],
            capture_output=True,
            text=True,
            check=False,
        )

    def test_exact_integer_trace_guards_survive_optimization(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                valid = self.run_optimized_trace(flag, "5.0")
                self.assertEqual(valid.returncode, 0, valid.stderr)
                self.assertEqual(valid.stdout.strip(), "5")

                fractional = self.run_optimized_trace(flag, "0.5")
                self.assertNotEqual(fractional.returncode, 0, fractional.stdout)
                self.assertIn("non-integer trace", fractional.stderr)

                out_of_range = self.run_optimized_trace(flag, "9007199254740992.0")
                self.assertNotEqual(out_of_range.returncode, 0, out_of_range.stdout)
                self.assertIn("int-exactness range exceeded", out_of_range.stderr)


if __name__ == '__main__':
    unittest.main()
