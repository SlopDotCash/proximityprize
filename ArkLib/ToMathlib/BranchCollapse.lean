/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.CurvePlaceReadingSupply
import ArkLib.ToMathlib.GSGradedBundle

/-!
# Issue #304 — the branch-collapse dichotomy: the three residual cores reduce to one

The three remaining named residuals of the faithful chain were: branch rationality (`hbranch`),
the windowed Claim-5.9 successor residual at `d_H ≥ 3`, and `MonicHighYResidual`.  This file
proves the **dichotomy that collapses them**:

* `eval_eval_eq_evalEval` — evaluation composition: substituting the fiber variable by a
  polynomial section and then the place equals the place-pair evaluation.
* `eval_branch_eq_zero_of_agreement` / `branch_section_dvd_of_rational_agreement` —
  **the collapse**: if the per-place branch values agree with a polynomial `b` on more places
  than the degree budget, then `b` is a genuine *section*: `H̃′(Z, b(Z)) = 0` identically, hence
  `(T − b) ∣ H̃′`.
* `natDegree_eq_one_of_irreducible_of_branch` — for an irreducible monicization this forces
  `natDegree H̃′ = 1`: **branch rationality is satisfiable only at fiber-linear factors.**
  Consequently the windowed Claim-5.9 residual at `d_H ≥ 3` is architecturally vacuous on the
  faithful path (factors carrying a rational branch through enough places are linear), and the
  `d_H ≥ 3` sharp escape of `ZLinearRatFuncDegreeOne` is not an obstruction but a confirmation.
* `monic_bundle_of_isUnit_leadingCoeff` — **the monic half of `MonicHighYResidual` discharged at
  the endpoint**: any bundle whose factor has a *unit* leading coefficient (forced at the
  endpoint by `ZLinearRatFuncDegreeOne.isUnit_leadingCoeff_of_gammaGenuine_Z_linear_target_all`)
  transports to a bundle with `H` **monic** — same `R`, associate `H`, the `Hypotheses`
  transported along the unit.

Together: the faithful chain's residual surface is now **one** core — the §5/§6 production of
the rational branch with the cardinality budget (the `FactorPigeonhole` lane) — everything
downstream of it is proven, and the factor shape it forces (fiber-linear, unit-lc, monicizable)
is exactly what the rest of the chain consumes.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (the polynomial-root factor), §6.2.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open scoped BigOperators

namespace ArkLib

namespace BranchCollapse

variable {F : Type} [Field F]

/-! ## Part 1 — evaluation composition -/

/-- Substituting the fiber variable by a polynomial and then evaluating the place equals the
place-pair evaluation at the section's value. -/
theorem eval_eval_eq_evalEval (z : F) (b : F[X]) (p : F[X][Y]) :
    Polynomial.eval z (Polynomial.eval b p) = Polynomial.evalEval z (b.eval z) p := by
  have hhom : (Polynomial.evalRingHom z).comp (Polynomial.evalRingHom b)
      = Polynomial.evalEvalRingHom z (b.eval z) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [Polynomial.evalEval_C]
    · simp [Polynomial.evalEval_X]
  calc Polynomial.eval z (Polynomial.eval b p)
      = ((Polynomial.evalRingHom z).comp (Polynomial.evalRingHom b)) p := rfl
    _ = Polynomial.evalEvalRingHom z (b.eval z) p := by rw [hhom]
    _ = Polynomial.evalEval z (b.eval z) p := rfl

/-! ## Part 2 — the branch collapse -/

/-- **The section identity.**  If the branch values at the places of `S` agree with the
polynomial `b`, and `S` is larger than the degree of the substituted polynomial, then
`H̃′(Z, b(Z)) = 0` identically. -/
theorem eval_branch_eq_zero_of_agreement {H : F[X][Y]}
    {S : Finset F} {b : F[X]}
    (root : (z : F) → z ∈ S → rationalRoot (H_tilde' H) z)
    (hagree : ∀ z (hz : z ∈ S), (root z hz).1 = b.eval z)
    (hcard : (Polynomial.eval b (H_tilde' H)).natDegree < S.card) :
    Polynomial.eval b (H_tilde' H) = 0 := by
  refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ S (fun z hz => ?_) hcard
  rw [eval_eval_eq_evalEval, ← hagree z hz]
  exact (root z hz).2

/-- **The branch collapse.**  A rational branch through more places than the degree budget is a
genuine polynomial *section* of the monicization: `(T − b) ∣ H̃′`. -/
theorem branch_section_dvd_of_rational_agreement {H : F[X][Y]}
    {S : Finset F} {b : F[X]}
    (root : (z : F) → z ∈ S → rationalRoot (H_tilde' H) z)
    (hagree : ∀ z (hz : z ∈ S), (root z hz).1 = b.eval z)
    (hcard : (Polynomial.eval b (H_tilde' H)).natDegree < S.card) :
    (Polynomial.X - Polynomial.C b) ∣ H_tilde' H := by
  rw [Polynomial.dvd_iff_isRoot]
  exact eval_branch_eq_zero_of_agreement root hagree hcard

/-- **Fiber-linearity.**  For an irreducible monicization, the branch collapse forces
`natDegree H̃′ = 1`: branch rationality is satisfiable only at fiber-linear factors.  (The
windowed Claim-5.9 residual at `d_H ≥ 3` is therefore architecturally vacuous on the faithful
path.) -/
theorem natDegree_eq_one_of_irreducible_of_branch {H : F[X][Y]}
    (hirr : Irreducible (H_tilde' H))
    {S : Finset F} {b : F[X]}
    (root : (z : F) → z ∈ S → rationalRoot (H_tilde' H) z)
    (hagree : ∀ z (hz : z ∈ S), (root z hz).1 = b.eval z)
    (hcard : (Polynomial.eval b (H_tilde' H)).natDegree < S.card) :
    (H_tilde' H).natDegree = 1 := by
  obtain ⟨q, hq⟩ := branch_section_dvd_of_rational_agreement root hagree hcard
  have hXb : ¬ IsUnit (Polynomial.X - Polynomial.C b) := by
    intro hu
    have := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [Polynomial.natDegree_X_sub_C] at this
    omega
  rcases (hirr.isUnit_or_isUnit hq).resolve_left hXb with hqu
  have hq0 : q.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hqu
  have hXb0 : (Polynomial.X - Polynomial.C b) ≠ 0 := by
    intro h0
    have := congrArg Polynomial.natDegree h0
    rw [Polynomial.natDegree_X_sub_C, Polynomial.natDegree_zero] at this
    omega
  have hq0' : q ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hq
    exact hirr.ne_zero hq
  rw [hq, Polynomial.natDegree_mul hXb0 hq0', Polynomial.natDegree_X_sub_C, hq0]

/-! ## Part 3 — the monic transport at unit leading coefficient -/

/-- **The monic bundle transport.**  Any GS bundle whose factor has a unit leading coefficient
(the shape forced at the endpoint by the Claim-5.9 necessity) transports to a bundle with the
factor **monic**: same `R`, the associate factor `lc⁻¹ • H`, the `Hypotheses` carried along the
unit.  This discharges the `hmonic` half of `MonicHighYResidual` at the endpoint. -/
noncomputable def monic_bundle_of_isUnit_leadingCoeff {x₀ : F}
    (bdl : GSFactorData.Bundle (F := F) x₀) (hu : IsUnit bdl.H.leadingCoeff) :
    { b' : GSFactorData.Bundle (F := F) x₀ //
        b'.H.Monic ∧ b'.R = bdl.R ∧ Associated bdl.H b'.H } := by
  classical
  haveI := bdl.hIrr
  haveI := bdl.hPos
  set u : (F[X])ˣ := hu.unit with hu_def
  have hu_eq : (u : F[X]) = bdl.H.leadingCoeff := hu.unit_spec
  set H' : F[X][Y] := Polynomial.C (↑u⁻¹ : F[X]) * bdl.H with hH'
  have hCu : IsUnit ((Polynomial.C (↑u⁻¹ : F[X])) : F[X][Y]) :=
    Polynomial.isUnit_C.mpr (Units.isUnit u⁻¹)
  have hassoc : Associated bdl.H H' := ⟨hCu.unit, by rw [hCu.unit_spec, hH']; ring⟩
  have hmonic : H'.Monic := by
    rw [Polynomial.Monic, hH', Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      ← hu_eq]
    exact Units.inv_mul u
  have hdeg : H'.natDegree = bdl.H.natDegree := by
    rw [hH', Polynomial.natDegree_C_mul (Units.ne_zero u⁻¹)]
  have hirr' : Irreducible H' := Associated.irreducible hassoc bdl.hIrr.out
  have hpos' : 0 < H'.natDegree := by rw [hdeg]; exact bdl.hH
  refine ⟨{ R := bdl.R, H := H', hIrr := ⟨hirr'⟩, hPos := ⟨hpos'⟩,
            hHyp := ?_, hH := hpos',
            D := max bdl.D (Bivariate.totalDegree H'), hD := le_max_right _ _ },
    hmonic, rfl, hassoc⟩
  constructor
  · exact (Associated.dvd_iff_dvd_left hassoc).mp bdl.hHyp.dvd_evalX
  · exact bdl.hHyp.separable_evalX

end BranchCollapse

end ArkLib

/-! ## Axiom audit. -/
#print axioms ArkLib.BranchCollapse.eval_eval_eq_evalEval
#print axioms ArkLib.BranchCollapse.eval_branch_eq_zero_of_agreement
#print axioms ArkLib.BranchCollapse.branch_section_dvd_of_rational_agreement
#print axioms ArkLib.BranchCollapse.natDegree_eq_one_of_irreducible_of_branch
#print axioms ArkLib.BranchCollapse.monic_bundle_of_isUnit_leadingCoeff
