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
    def test_default_and_checkout_scans_include_production_and_research_only(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory).resolve()
            sources = {
                'ArkLib/Data/Probe.lean',
                'ArkLib/Extensions/Data/Probe.lean',
                'ArkLib/Compatibility/Probe.lean',
                'ArkLib/Research/ProximityGap/Probe.lean',
            }
            test_source = root / 'ArkLib/Tests/Probe.lean'
            for name in sources | {'ArkLib/Tests/Probe.lean'}:
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text('theorem unfinished : True := by sorry\n')
            previous = Path.cwd()
            try:
                os.chdir(root)
                for arguments in ([], ['.'], ['ArkLib']):
                    files, full, errors = forbidden_tokens.scan_plan(arguments)
                    self.assertEqual({p.resolve() for p in files},
                                     {root / name for name in sources})
                    self.assertEqual(len(files), len(sources))
                    self.assertTrue(full)
                    self.assertEqual(errors, [])
                files, full, errors = forbidden_tokens.scan_plan([str(test_source)])
                self.assertEqual([p.resolve() for p in files], [test_source])
                self.assertFalse(full)
                self.assertEqual(errors, [])
                holes = [row for row in sorry_census.census(root) if row['kind'] == 'hole']
                self.assertEqual({row['file'] for row in holes}, sources)
                self.assertEqual(len(holes), len(sources))
            finally:
                os.chdir(previous)

    def test_citation_catalog_keeps_both_roots(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            roots = [root / name for name in ('ArkLib', 'Research', 'ProximityPrize')]
            for source in roots:
                source.mkdir()
                (source / 'Citation.lean').write_text('/- [Example] -/\n')
            payload = extract_citations(roots, ['Example'])
            self.assertEqual(payload['keys']['Example'],
                             ['ArkLib/Citation.lean', 'ProximityPrize/Citation.lean', 'Research/Citation.lean'])
            self.assertEqual(payload['lean_roots'], ['ArkLib', 'Research', 'ProximityPrize'])

    def test_citation_catalog_deterministic_posix_sort_order(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / 'ArkLib'
            source.mkdir()
            (source / 'Curves.lean').write_text('/- [Example] -/\n', encoding='utf-8')
            (source / 'Curves').mkdir()
            (source / 'Curves' / 'AgreementCount.lean').write_text('/- [Example] -/\n', encoding='utf-8')
            (source / '_B2.lean').write_text('/- [Example] -/\n', encoding='utf-8')
            (source / 'Basic.lean').write_text('/- [Example] -/\n', encoding='utf-8')
            payload = extract_citations([source], ['Example'])
            self.assertEqual(payload['keys']['Example'],
                             ['ArkLib/Basic.lean',
                              'ArkLib/Curves/AgreementCount.lean',
                              'ArkLib/Curves.lean',
                              'ArkLib/_B2.lean'])

    def test_boundary_rejects_each_live_research_import(self):
        self.assertEqual(boundary.research_imports(
            'import ArkLib.Basic ArkLib.Research.ProximityGap.All\n'
            'public import ArkLib.Research\npublic import Research.Other\n'),
            [(1, 'ArkLib.Research.ProximityGap.All'), (2, 'ArkLib.Research'),
             (3, 'Research.Other')])

    def test_boundary_rejects_meta_and_public_meta_imports(self):
        # Lean 4.30 module files accept `meta import` and `public meta import`;
        # both bring Research declarations into the importing module.
        self.assertEqual(boundary.research_imports(
            'module\nmeta import ArkLib.Research.A\npublic meta import ArkLib.Research.B\n'
            'import all ArkLib.Research.C\nmeta import ArkLib.Basic\n'
            'meta import Research.Legacy\n'),
            [(2, 'ArkLib.Research.A'), (3, 'ArkLib.Research.B'),
             (4, 'ArkLib.Research.C'), (6, 'Research.Legacy')])

    def test_boundary_rejects_escaped_nested_research_components(self):
        rejected = (
            'ArkLib.«Research».A',
            '«ArkLib».Research.A',
            '«ArkLib».«Research».«ProximityGap».A',
            '«ArkLib».«Research»',
        )
        text = ''.join(f'public meta import all {module}\n' for module in rejected)
        text += (
            'import «ArkLib.Research».A\n'
            'import ArkLib.«Research.A»\n'
            'import ArkLib.ResearchOther.A\n'
            'import Other.ArkLib.Research.A\n'
        )
        self.assertEqual(boundary.research_imports(text), list(enumerate(rejected, 1)))

    def test_production_boundary_excludes_research_and_test_sources(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            production = {
                'ArkLib.lean',
                'ArkLib/Data/Probe.lean',
                'ArkLib/Extensions/Probe.lean',
                'ArkLib/Compatibility/Probe.lean',
                'ArkLib/Downstream/Probe.lean',
            }
            excluded = {'ArkLib/Research/ProximityGap/Probe.lean',
                        'ArkLib/Tests/Probe.lean'}
            for name in production | excluded:
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text('import ArkLib.Research.ProximityGap.All\n')
            paths = list(boundary.production_sources(root))
            self.assertEqual({path.relative_to(root).as_posix() for path in paths}, production)
            findings = [(path.relative_to(root).as_posix(), line, module)
                        for path in paths
                        for line, module in boundary.research_imports(path.read_text())]
            self.assertEqual(set(findings),
                             {(name, 1, 'ArkLib.Research.ProximityGap.All') for name in production})

    def test_boundary_rejects_escaped_research_root(self):
        # Lean 4.30 resolves `«Research».A` to the module `Research.A`; a single
        # escaped component `«Research.A»` names a different module.
        self.assertEqual(boundary.research_imports(
            'import «Research».A\nimport «Research».«B»\n'
            'import ArkLib.Basic «Research»\nimport «Research.C»\n'
            'import «ResearchD».E\nimport all «Research».C\n'
            'meta import «Research».D\nimport Foo.«Research».Bar\n'),
            [(1, '«Research».A'), (2, '«Research».«B»'), (3, '«Research»'),
             (6, '«Research».C'), (7, '«Research».D')])

    def test_boundary_ignores_nested_comments(self):
        self.assertEqual(boundary.research_imports(
            '/- outer\n/- nested -/\nimport ArkLib.Research.Hidden\n-/\n'
            '-- import Research.Hidden\nimport ArkLib.Basic\n'), [])

    def test_boundary_handles_unicode_content(self):
        content = (
            '/- Mathematical notation: ∀ ε > 0, ∃ δ > 0, λ x, x ∈ ℝ ∧ x ∉ ℤ -/\n'
            '-- Note: α → β ↔ γ\n'
            'import ArkLib.Basic\n'
            'public import ArkLib.Research.UnicodeModule\n'
        )
        self.assertEqual(
            boundary.research_imports(content),
            [(4, 'ArkLib.Research.UnicodeModule')]
        )


if __name__ == '__main__':
    unittest.main()
