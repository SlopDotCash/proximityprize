"""Regression coverage for Lean axiom reports with primed declaration names."""
import importlib.util
from pathlib import Path
import unittest

path = Path(__file__).resolve().parents[1] / "axiom_audit.py"
spec = importlib.util.spec_from_file_location("axiom_audit", path)
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)


class AxiomReportParser(unittest.TestCase):
    def test_primed_root_keeps_full_name_and_multiline_dependencies(self):
        output = "'Domain.log_right_inverse\'' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n"
        report = audit.DEP_RE.search(output)
        self.assertIsNotNone(report)
        self.assertEqual(report.group(1), "Domain.log_right_inverse'")
        self.assertEqual({x.strip() for x in report.group(2).split(',')}, audit.ALLOWED)

    def test_primed_root_with_forbidden_axiom_is_not_lost(self):
        output = "'Example.bound'' depends on axioms: [propext, sorryAx]\n"
        report = audit.DEP_RE.search(output)
        self.assertIsNotNone(report)
        self.assertEqual(report.group(1), "Example.bound'")
        self.assertNotEqual({x.strip() for x in report.group(2).split(',')} - audit.ALLOWED, set())

    def test_adjacent_axiom_free_and_dependent_reports_remain_separate(self):
        output = "'Example.first'' does not depend on any axioms\n'Example.second' depends on axioms: [propext]\n"
        self.assertEqual([m.group(1) for m in audit.NODEP_RE.finditer(output)], ["Example.first'"])
        self.assertEqual([m.group(1) for m in audit.DEP_RE.finditer(output)], ["Example.second"])


if __name__ == "__main__":
    unittest.main()
