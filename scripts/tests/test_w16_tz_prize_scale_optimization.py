"""The W16 TZ prime-witness checks must survive Python optimization."""
from pathlib import Path
import contextlib
import importlib.util
import io
import subprocess
import sys
import tempfile
import textwrap
import unittest
from unittest.mock import patch


PROBES = Path(__file__).resolve().parents[1] / "probes"


def run_probe(flag, body):
    code = textwrap.dedent(
        f"""
        import sys
        sys.path.insert(0, {str(PROBES)!r})
        import probe_w16_tz_prize_scale as probe
        """
    ) + textwrap.dedent(body)
    return subprocess.run(
        [sys.executable, flag, "-c", code],
        capture_output=True,
        text=True,
        check=False,
    )


class W16TZPrizeScaleOptimization(unittest.TestCase):
    def test_main_writes_all_rungs_to_a_portable_temp_directory(self):
        spec = importlib.util.spec_from_file_location(
            "w16_tz_prize_scale_output_test", PROBES / "probe_w16_tz_prize_scale.py"
        )
        probe = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(probe)
        rows = [(17, 1, 4, 3)]
        output = io.StringIO()
        with tempfile.TemporaryDirectory() as scratch:
            with (
                patch.object(probe, "sieve_rung", return_value=rows),
                patch.object(probe, "s128_budget_note"),
                patch.object(probe, "emit_rung", side_effect=lambda k, _: f"rung {k}\n"),
                patch.object(probe.tempfile, "mkdtemp", return_value=scratch) as make_temp,
                contextlib.redirect_stdout(output),
            ):
                probe.main()

            make_temp.assert_called_once_with(prefix="w16-tz-prize-scale-")
            files = sorted(Path(scratch).glob("*.lean"))
            expected_names = [f"rung_{k}.lean" for k in range(16, 31)]
            self.assertEqual([path.name for path in files], expected_names)
            for k in range(16, 31):
                self.assertEqual((Path(scratch) / f"rung_{k}.lean").read_text(), f"rung {k}\n")
            self.assertIn(f"Lean blocks written to {scratch}/rung_<k>.lean", output.getvalue())

    def test_composite_witness_is_rejected_under_optimization(self):
        body = """
            probe.is_prime = lambda n: n % 2 == 1 and n > 1
            probe.sieve_rung(16)
            print("ALL CHECKS PASSED")
            """
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = run_probe(flag, body)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("Fermat check fails for p=4295032833", result.stderr)
                self.assertNotIn("ALL CHECKS PASSED", result.stdout)

    def test_number_above_the_deterministic_limit_is_rejected_under_optimization(self):
        body = """
            probe.is_prime(probe.DET_LIMIT)
            print("ALL CHECKS PASSED")
            """
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = run_probe(flag, body)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("above the deterministic Miller-Rabin limit", result.stderr)
                self.assertNotIn("ALL CHECKS PASSED", result.stdout)


if __name__ == "__main__":
    unittest.main()
