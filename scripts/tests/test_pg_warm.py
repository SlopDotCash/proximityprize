"""Exercise warm-up diagnostics without invoking Lean or taking build locks."""

import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


class WarmDiagnostics(unittest.TestCase):
    def run_warm(self, fail):
        with tempfile.TemporaryDirectory(prefix="pg-warm-test-") as directory:
            root = Path(directory)
            script = root / "pg-warm.sh"
            shutil.copy2(Path(__file__).resolve().parents[1] / "pg-warm.sh", script)
            wrapper = root / "lake-locked.sh"
            wrapper.write_text('''#!/usr/bin/env bash
echo "first compiler diagnostic"
echo "second compiler diagnostic" >&2
echo "last compiler diagnostic"
if [[ "${FAIL_WARM:-0}" == "1" ]]; then
  exit 37
fi
''')
            wrapper.chmod(0o755)
            result = subprocess.run(
                ["bash", str(script)], capture_output=True, text=True,
                env={**os.environ, "TMPDIR": str(root), "FAIL_WARM": str(int(fail))},
                check=False,
            )
            self.assertEqual(list(root.glob("pg-warm.??????")), [])
            return result

    def test_failure_preserves_full_log_status_and_omits_ready_message(self):
        result = self.run_warm(fail=True)
        self.assertEqual(result.returncode, 37)
        self.assertEqual(result.stderr.splitlines(), [
            "first compiler diagnostic", "second compiler diagnostic", "last compiler diagnostic"])
        self.assertNotIn("Done.", result.stdout)

    def test_success_keeps_only_last_two_build_lines(self):
        result = self.run_warm(fail=False)
        self.assertEqual(result.returncode, 0)
        self.assertNotIn("first compiler diagnostic", result.stdout)
        self.assertIn("second compiler diagnostic\nlast compiler diagnostic\nDone.", result.stdout)
        self.assertEqual(result.stderr, "")


if __name__ == "__main__":
    unittest.main()
