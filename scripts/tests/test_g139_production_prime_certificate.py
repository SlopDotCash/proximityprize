"""The production-like prime gate must not certify the seven-base pseudoprime."""

from pathlib import Path
import subprocess
import sys
import textwrap
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "probes"))
import probe_g139_production_accident_census as census


# Jaeschke 1993: least odd composite that is a strong pseudoprime to every
# base in {2, 3, 5, 7, 11, 13, 17}. Seven-base Miller-Rabin is a proof only
# strictly below this integer.
SEVEN_BASE_PSEUDOPRIME = 10670053 * 32010157

# Published rows of scripts/probes/_out_g139_production_accident_census.txt.
PUBLISHED_PRODUCTION_PRIMES = {
    16: 2196401,
    32: 84551969,
    64: 3254976577,
    128: 125306187649,
    256: 4823887276289,
}


class ProductionPrimeCertificate(unittest.TestCase):
    def test_seven_base_pseudoprime_is_not_certified(self):
        self.assertEqual(SEVEN_BASE_PSEUDOPRIME, 341550071728321)
        with self.assertRaises(ValueError):
            census.is_prime(SEVEN_BASE_PSEUDOPRIME)
        with self.assertRaises(ValueError):
            census.is_prime(SEVEN_BASE_PSEUDOPRIME + 2)

    def test_seven_base_pseudoprime_stays_rejected_under_optimization(self):
        script = textwrap.dedent(
            f"""
            import sys
            sys.path.insert(0, {str(Path(census.__file__).parent)!r})
            import probe_g139_production_accident_census as census
            try:
                result = census.is_prime({SEVEN_BASE_PSEUDOPRIME})
            except ValueError:
                sys.exit(0)
            sys.stderr.write(repr(result))
            sys.exit(1)
            """
        )
        for flags in ((), ("-O",), ("-OO",)):
            with self.subTest(flags=flags):
                completed = subprocess.run(
                    [sys.executable, *flags, "-c", script],
                    capture_output=True,
                    text=True,
                    timeout=30,
                )
                self.assertEqual(completed.returncode, 0, completed.stderr)

    def test_published_production_primes_stay_certified(self):
        for n, prime in PUBLISHED_PRODUCTION_PRIMES.items():
            with self.subTest(n=n):
                self.assertLess(prime, SEVEN_BASE_PSEUDOPRIME)
                self.assertTrue(census.is_prime(prime))
                self.assertEqual(census.first_production_like_prime(n), prime)
                self.assertEqual(census.v2(prime - 1), n.bit_length() - 1)

    def test_small_primes_and_composites(self):
        for prime in (2, 3, 17, 19):
            with self.subTest(prime=prime):
                self.assertTrue(census.is_prime(prime))
        for composite in (1, 9, 25, 91, 341, 2047):
            with self.subTest(composite=composite):
                self.assertFalse(census.is_prime(composite))


if __name__ == "__main__":
    unittest.main()
