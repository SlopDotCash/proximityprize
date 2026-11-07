"""The research umbrella must not silently skip untracked Lean modules."""
import contextlib
import importlib.util
import io
import subprocess
from pathlib import Path
import tempfile
import unittest


spec = importlib.util.spec_from_file_location(
    'update_research_lib',
    Path(__file__).resolve().parents[1] / 'update-research-lib.py')
updater = importlib.util.module_from_spec(spec)
spec.loader.exec_module(updater)


def git(root: Path, *args: str) -> None:
    subprocess.run(['git', '-C', str(root), *args], check=True, capture_output=True)


class ResearchUmbrellaUntracked(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='research-umbrella-')
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        git(self.root, 'init', '-q')
        git(self.root, 'config', 'user.email', 'test@example.invalid')
        git(self.root, 'config', 'user.name', 'Test')
        frontier = self.root / 'Research/ProximityPrize/Frontier'
        frontier.mkdir(parents=True)
        (frontier / 'Tracked.lean').write_text('theorem tracked : True := trivial\n')
        excluded = frontier / '_FSMA_SecondMomentPairPartition.lean'
        excluded.write_text('theorem excluded : True := trivial\n')
        git(self.root, 'add', '--', 'Research/ProximityPrize/Frontier/Tracked.lean',
            'Research/ProximityPrize/Frontier/_FSMA_SecondMomentPairPartition.lean')
        git(self.root, 'commit', '-qm', 'tracked')

    def test_tracked_modules_are_imported_and_exclusions_stay_out(self):
        self.assertEqual(updater.update(self.root), 0)
        text = (self.root / updater.TARGET).read_text()
        self.assertEqual(
            text,
            'import Research.ProximityPrize.Frontier.Tracked\n')

    def test_untracked_nested_module_is_rejected_without_rewriting_the_umbrella(self):
        self.assertEqual(updater.update(self.root), 0)
        git(self.root, 'add', '--', updater.TARGET)
        before = (self.root / updater.TARGET).read_text()
        hidden = self.root / 'Research/ProximityPrize/Frontier/Untracked.lean'
        hidden.write_text('theorem untracked : True := trivial\n')
        stderr = io.StringIO()
        with contextlib.redirect_stderr(stderr):
            status = updater.update(self.root)
        self.assertEqual(status, 1)
        self.assertEqual((self.root / updater.TARGET).read_text(), before)
        self.assertNotIn('Untracked', before)
        message = stderr.getvalue()
        self.assertIn('git add Research/ProximityPrize/Frontier/Untracked.lean\n', message)
        self.assertNotIn('git add Research/ProximityPrize/All.lean', message)

    def test_staged_module_is_imported(self):
        hidden = self.root / 'Research/ProximityPrize/Frontier/Staged.lean'
        hidden.write_text('theorem staged : True := trivial\n')
        git(self.root, 'add', '--', 'Research/ProximityPrize/Frontier/Staged.lean')
        self.assertEqual(updater.update(self.root), 0)
        text = (self.root / updater.TARGET).read_text()
        self.assertIn('import Research.ProximityPrize.Frontier.Staged\n', text)
        self.assertIn('import Research.ProximityPrize.Frontier.Tracked\n', text)

    def test_gitignored_lean_file_is_not_a_missing_import(self):
        (self.root / '.gitignore').write_text('*.skip.lean\n')
        skipped = self.root / 'Research/ProximityPrize/Scratch.skip.lean'
        skipped.parent.mkdir(parents=True, exist_ok=True)
        skipped.write_text('theorem skipped : True := trivial\n')
        self.assertEqual(updater.update(self.root), 0)
        self.assertNotIn('Scratch', (self.root / updater.TARGET).read_text())


if __name__ == '__main__':
    unittest.main()
