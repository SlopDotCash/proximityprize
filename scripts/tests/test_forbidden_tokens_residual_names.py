"""Obligation-like name coverage in forbidden_tokens' vacuous-True guard."""
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from forbidden_tokens import is_residual_like, main

ALLOWLIST: set[str] = set()


class ResidualLikeNames(unittest.TestCase):
    def test_camel_case_residual_name_is_obligation_like(self):
        # The library's residual declarations are camelCase
        # (`fiatShamir_hvzkTransferResidual`), never `foo_residual`; the
        # obligation-like heuristic must recognize them so the vacuous-`True`
        # guard applies to the names it exists for.
        self.assertTrue(
            is_residual_like("fiatShamir_hvzkTransferResidual", ALLOWLIST)
        )
        self.assertTrue(is_residual_like("FrankUncrossingResidual", ALLOWLIST))
        self.assertTrue(is_residual_like("claim57Residuals", ALLOWLIST))

    def test_snake_case_residual_name_still_matched(self):
        self.assertTrue(is_residual_like("foo_residual", ALLOWLIST))

    def test_unrelated_names_stay_data(self):
        self.assertFalse(is_residual_like("helperCompute", ALLOWLIST))
        self.assertFalse(is_residual_like("residualWorklist", ALLOWLIST))
        self.assertFalse(is_residual_like("distanceBound", ALLOWLIST))


class AuditIntegration(unittest.TestCase):
    def _run_audit(self, source: str) -> int:
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "Case.lean"
            path.write_text(source, encoding="utf-8")
            with mock.patch.object(sys, "argv", ["forbidden_tokens.py", str(path)]):
                return main()

    def test_camel_residual_declared_true_fails_audit(self):
        # A def whose obligation-like name is camelCase and whose result type
        # is the vacuous `True` must fail, exactly like the snake_case case.
        source = "def fiatShamir_hvzkTransferResidual : True := trivial\n"
        self.assertEqual(self._run_audit(source), 1)

    def test_genuine_residual_stays_clean(self):
        source = (
            "def fiatShamir_hvzkTransferResidual : Prop :=\n"
            "  ∀ init impl fsInit fsImpl rel R,\n"
            "    impl.correct init fsInit rel R → fsImpl.correct init fsInit rel R\n"
            "theorem helper (h : p) : q := h\n"
        )
        self.assertEqual(self._run_audit(source), 0)


if __name__ == "__main__":
    unittest.main()
