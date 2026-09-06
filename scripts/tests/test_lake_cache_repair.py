"""A corrupt restored package must not poison every subsequent CI attempt."""
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest import mock

spec = importlib.util.spec_from_file_location(
    'cache_repair', Path(__file__).resolve().parents[1] / 'repair-lake-cache.py')
repair = importlib.util.module_from_spec(spec)
spec.loader.exec_module(repair)


class CacheRepair(unittest.TestCase):
    def test_preserves_valid_cache_and_quarantines_broken_heads(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            packages = root / '.lake/packages'
            packages.mkdir(parents=True)
            names = ['good', 'bad', 'missing', 'no-git']
            (root / 'lake-manifest.json').write_text(json.dumps({
                'packages': [{'type': 'git', 'name': name} for name in names]}))
            for name in ['good', 'bad']:
                path = packages / name
                subprocess.run(['git', 'init', '-q', str(path)], check=True)
                subprocess.run(['git', '-C', str(path), '-c', 'user.name=Test',
                                '-c', 'user.email=test@example.invalid', 'commit',
                                '--allow-empty', '-qm', 'test'], check=True)
                (path / 'artifact.olean').write_text('cached artifact')
            (packages / 'bad/.git/HEAD').write_text('ref: refs/heads/nonexistent\n')
            (packages / 'no-git').mkdir()
            # A parent Git repository must not make no-git look healthy.
            subprocess.run(['git', 'init', '-q', str(root)], check=True)
            with mock.patch.object(repair.tempfile, 'mkdtemp',
                                            return_value=str(root / 'quarantine')):
                (root / 'quarantine').mkdir()
                self.assertEqual(repair.repair(root), ['bad', 'no-git'])
            self.assertEqual((packages / 'good/artifact.olean').read_text(), 'cached artifact')
            self.assertFalse((packages / 'bad').exists())
            self.assertEqual((root / 'quarantine/bad/artifact.olean').read_text(), 'cached artifact')
            self.assertEqual(repair.repair(root), [])


if __name__ == '__main__':
    unittest.main()
