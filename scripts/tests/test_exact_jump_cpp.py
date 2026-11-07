"""Run the exhaustive C++ integer-optimizer regression in routine validation."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


def find_cxx_compiler() -> str | None:
    for candidate in [os.environ.get("CXX"), "c++", "g++", "clang++"]:
        if candidate and shutil.which(candidate):
            return candidate
    return None


class ExactJumpCpp(unittest.TestCase):
    def test_exhaustive_optimizer(self):
        cxx = find_cxx_compiler()
        if not cxx:
            self.skipTest("C++ compiler (c++, g++, or clang++) not available")
        source = Path(__file__).with_name('test_exact_jump_dp.cpp').resolve()
        with tempfile.TemporaryDirectory(prefix='exact-jump-test-') as directory:
            executable = Path(directory) / 'test-exact-jump'
            subprocess.run([cxx, '-O2', '-std=c++20', str(source), '-o', str(executable)],
                           check=True, capture_output=True, text=True)
            run_target = executable
            if not run_target.is_file() and run_target.with_suffix(".exe").is_file():
                run_target = run_target.with_suffix(".exe")
            result = subprocess.run([str(run_target)], check=True,
                                    capture_output=True, text=True)
        self.assertEqual(result.stdout.strip(), 'PASS 1875 exhaustive DP comparisons')
