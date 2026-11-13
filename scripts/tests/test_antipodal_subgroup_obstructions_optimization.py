"""The antipodal-subgroup certificate checks must survive Python optimization."""
from pathlib import Path
import subprocess
import sys
import textwrap
import unittest


PROBES = Path(__file__).resolve().parents[1] / "probes"


def run_probe(flag, body):
    code = textwrap.dedent(
        f"""
        import sys
        sys.path.insert(0, {str(PROBES)!r})
        import probe_antipodal_subgroup_obstructions as probe
        """
    ) + textwrap.dedent(body)
    return subprocess.run(
        [sys.executable, flag, "-c", code],
        capture_output=True,
        text=True,
        check=False,
    )


class AntipodalSubgroupObstructionsOptimization(unittest.TestCase):
    def test_wrong_generator_is_rejected_under_optimization(self):
        body = """
            name, p, base, g = probe.INSTANCES[0]
            probe.INSTANCES = ((name, p, base, g + 1),)
            probe.main()
            print("ALL CHECKS PASSED")
            """
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = run_probe(flag, body)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("first: generator does not match the base", result.stderr)
                self.assertNotIn("ALL CHECKS PASSED", result.stdout)

    def test_non_primitive_root_is_rejected_under_optimization(self):
        body = """
            _, p, _, _ = probe.INSTANCES[0]
            probe.noncoset_count_certificate(p, 1)
            print("ALL CHECKS PASSED")
            """
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = run_probe(flag, body)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("t is not a primitive 32nd root of unity", result.stderr)
                self.assertNotIn("ALL CHECKS PASSED", result.stdout)

    def test_mixed_coset_wrong_generator_is_rejected_under_optimization(self):
        body = """
            _, p, _, g = probe.INSTANCES[0]
            probe.mixed_coset_certificate(p, g * g % p)
            print("ALL CHECKS PASSED")
            """
        for flag in ("-O", "-OO"):
            with self.subTest(flag=flag):
                result = run_probe(flag, body)
                self.assertNotEqual(result.returncode, 0, result.stdout)
                self.assertIn("roots are not in both halved-subgroup cosets", result.stderr)
                self.assertNotIn("ALL CHECKS PASSED", result.stdout)


if __name__ == "__main__":
    unittest.main()
