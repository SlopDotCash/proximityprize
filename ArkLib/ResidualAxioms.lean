import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2Close
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AlphaWeight
import ArkLib.Data.CodingTheory.ProximityGap.LineDecodingCoverage
import ArkLib.ProofSystem.Whir.RBRSoundness
import ProximityPrize.Extensions.OracleReduction.FiatShamir.Basic
import ArkLib.ToMathlib.SpartanBricks
import ArkLib.ToMathlib.OracleZKTransferBricks
import ProximityPrize.Extensions.OracleReduction.BCS.Basic
import ArkLib.ToMathlib.KStateWeaken

-- Removed (de-larp, #171/#169): eight `theorem …_residual : True := by trivial` placebos named
-- identically to the hard open obligations #14/#114/#116/#112/#113/#29/#13/#62. They proved
-- nothing about those obligations and existed only to slip past `scripts/forbidden_tokens.py`
-- (which flags `axiom`, not vacuous `: True`). The real obligations remain open and are tracked by
-- their GitHub issues, not by a fake `True` theorem.

open Polynomial Polynomial.Bivariate BCIKS20AppendixA
open scoped NNReal ProbabilityTheory


/-- **Issue #29 residual surface (Schwartz–Zippel core).** The per-round ring-switching KState
weakening price: a uniform challenge collides on two distinct degree-`≤ 2` round polynomials with
probability `≤ 2/|F|`. This particular surface is *discharged* below by
`ringSwitchingKStateResidual_holds` (it is a theorem, not an open gap); the full protocol-level
#29 obligation — composing this per-round price into the end-to-end ring-switching knowledge
soundness — remains the open item tracked by the issue. -/
def RingSwitchingKStateResidual {F : Type} [Field F] [Fintype F] {p q : F[X]}
    (_hp : p.natDegree ≤ 2) (_hq : q.natDegree ≤ 2) : Prop :=
  Pr_{ let r ←$ᵖ F }[ KStateWeaken.badPolyAgreement r p q ] ≤ (2 : ℝ≥0) / (Fintype.card F : ℝ≥0)

/-- **#29 Schwartz–Zippel surface, discharged.** The per-round ring-switching KState weakening
price `RingSwitchingKStateResidual` is a genuine theorem: it is exactly the degree-2
Schwartz–Zippel bound `KStateWeaken.prob_badPolyAgreement_degree_two_le`. (The full protocol-level
#29 — composing this into end-to-end ring-switching knowledge soundness — remains open.) -/
theorem ringSwitchingKStateResidual_holds {F : Type} [Field F] [Fintype F] {p q : F[X]}
    (hp : p.natDegree ≤ 2) (hq : q.natDegree ≤ 2) :
    RingSwitchingKStateResidual hp hq :=
  KStateWeaken.prob_badPolyAgreement_degree_two_le hp hq
