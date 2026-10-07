"""Run the exhaustive C++ integer-optimizer regression in routine validation."""
from pathlib import Path
import subprocess
import tempfile
import unittest


class ExactJumpCpp(unittest.TestCase):
    def test_exhaustive_optimizer(self):
        source = Path(__file__).with_name('test_exact_jump_dp.cpp').resolve()
        with tempfile.TemporaryDirectory(prefix='exact-jump-test-') as directory:
            executable = Path(directory) / 'test-exact-jump'
            subprocess.run(['c++', '-O2', '-std=c++20', str(source), '-o', str(executable)],
                           check=True, capture_output=True, text=True)
            result = subprocess.run([str(executable)], check=True,
                                    capture_output=True, text=True)
        self.assertEqual(result.stdout.strip(), 'PASS 1875 exhaustive DP comparisons')
