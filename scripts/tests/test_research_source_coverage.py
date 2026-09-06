"""Regression tests for proof-audit coverage across the research split."""
import importlib.util
import os
from pathlib import Path
import sys
import tempfile
import unittest

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))
import forbidden_tokens
import sorry_census
sys.path.insert(0, str(SCRIPTS / "kb"))
from extract_lean_citations import extract_citations

spec = importlib.util.spec_from_file_location('boundary', SCRIPTS / 'check-research-boundary.py')
boundary = importlib.util.module_from_spec(spec)
spec.loader.exec_module(boundary)


class ResearchCoverage(unittest.TestCase):
    def test_default_and_checkout_scans_include_both_trees(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            for name in ('ArkLib', 'Research'):
                (root / name).mkdir()
                (root / name / 'Probe.lean').write_text('theorem unfinished : True := by sorry\n')
            previous = Path.cwd()
            try:
                os.chdir(root)
                for arguments in ([], ['.']):
                    files, full, errors = forbidden_tokens.scan_plan(arguments)
                    self.assertEqual({p.resolve() for p in files},
                                     {root / name / 'Probe.lean' for name in ('ArkLib', 'Research')})
                    self.assertTrue(full)
                    self.assertEqual(errors, [])
                holes = [row for row in sorry_census.census(root) if row['kind'] == 'hole']
                self.assertEqual({row['file'] for row in holes},
                                 {'ArkLib/Probe.lean', 'Research/Probe.lean'})
            finally:
                os.chdir(previous)

    def test_citation_catalog_keeps_both_roots(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            roots = [root / name for name in ('ArkLib', 'Research')]
            for source in roots:
                source.mkdir()
                (source / 'Citation.lean').write_text('/- [Example] -/\n')
            payload = extract_citations(roots, ['Example'])
            self.assertEqual(payload['keys']['Example'],
                             ['ArkLib/Citation.lean', 'Research/Citation.lean'])
            self.assertEqual(payload['lean_roots'], ['ArkLib', 'Research'])

    def test_boundary_rejects_each_live_research_import(self):
        self.assertEqual(boundary.research_imports(
            'import ArkLib.Basic Research.ProximityPrize.All\npublic import Research.Other\n'),
            [(1, 'Research.ProximityPrize.All'), (2, 'Research.Other')])

    def test_boundary_ignores_nested_comments(self):
        self.assertEqual(boundary.research_imports(
            '/- outer\n/- nested -/\nimport Research.Hidden\n-/\n'
            '-- import Research.Hidden\nimport ArkLib.Basic\n'), [])


if __name__ == '__main__':
    unittest.main()
