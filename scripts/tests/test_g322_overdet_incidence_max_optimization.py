"""The G322 overdet incidence-max guards must survive Python optimization."""
from pathlib import Path
import importlib.util
import subprocess
import sys
import textwrap
import unittest


PROBE = (
    Path(__file__).resolve().parents[1]
    / "probes"
    / "g322_overdet_incidence_max_extended.py"
)


def run_probe(flag, old=None, new=None):
    """Run the probe, optionally with one source line replaced."""
    if old is None:
        args = [sys.executable] + ([flag] if flag else []) + [str(PROBE)]
        return subprocess.run(
            args,
            capture_output=True,
            text=True,
            check=False,
        )
    code = textwrap.dedent(
        f"""
        source = open({str(PROBE)!r}, encoding="utf-8").read()
        assert source.count({old!r}) == 1
        source = source.replace({old!r}, {new!r})
        exec(compile(source, "probe", "exec"), {{"__name__": "__main__"}})
        print("ALL CHECKS PASSED")
        """
    )
    args = [sys.executable] + ([flag] if flag else []) + ["-c", code]
    return subprocess.run(
        args,
        capture_output=True,
        text=True,
        check=False,
    )


def run_binomial(flag, m):
    """Call I_max_binomial(m) in a fresh interpreter."""
    code = textwrap.dedent(
        f"""
        import importlib.util
        spec = importlib.util.spec_from_file_location("g322", {str(PROBE)!r})
        mod = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(mod)
        print(mod.I_max_binomial({m}))
        """
    )
    args = [sys.executable] + ([flag] if flag else []) + ["-c", code]
    return subprocess.run(
        args,
        capture_output=True,
        text=True,
        check=False,
    )


class G322OverdetIncidenceMaxOptimization(unittest.TestCase):
    def test_published_certificate_passes_under_optimization(self):
        baseline = run_probe("")
        self.assertEqual(baseline.returncode, 0, baseline.stderr)
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = run_probe(flag)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertEqual(result.stdout, baseline.stdout)
                self.assertIn("ALL CHECKS PASSED", result.stdout)
                self.assertIn("Closed form I_max(m) = 2m^3 - 2m^2 + 1 verified", result.stdout)

    def test_odd_product_is_rejected_under_optimization(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = run_probe(
                    flag,
                    "    prod = m * (m - 1)\n",
                    "    prod = m * (m - 1) + 1\n",
                )
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("is not even", result.stderr)
                self.assertNotIn("ALL CHECKS PASSED", result.stdout)

    def test_out_of_domain_m_is_rejected_under_optimization(self):
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = run_binomial(flag, 0)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("m must be at least 1", result.stderr)


if __name__ == "__main__":
    unittest.main()
