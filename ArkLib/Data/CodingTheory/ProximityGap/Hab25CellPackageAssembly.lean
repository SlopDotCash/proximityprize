/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CellTailFree
import ArkLib.ToMathlib.RationalRootSupply

/-!
# The assembled per-cell `himpr` at the section branch (#348, item-1 closure)

The closing assembly of the Johnson-regime per-cell production: at the section branch
(`H := Y − C (w.eval (C x₀))`), the §5 machinery legs of
`cell_improvement_of_pinning_package'` are discharged BY CONSTRUCTION —

* `hHyp`/monicity/irreducibility/positivity — `hypotheses_of_surface` + the
  `sectionBranch` facts (GK1 collapse);
* `htail` — `htail_of_surface` (the tail collapse);
* the root family + `hbaseA`/`hbase₀` — `sectionRoot`: at the linear branch the canonical
  rational root at `z` IS the base value `(w.eval (C x₀)).eval z` (monic ⟹ the `H̃′`
  normalization is trivial);

leaving **`cell_improvement_of_surface`**: the dichotomy funnel's `himpr`, per large
factor cell, from the cell's own divisibilities + the surface + the genuinely
quantitative §5 data alone (per-place separability readings, fold readings at the nodes,
the `ξ`-weight bound, and the cardinality/numeric legs).  Every consumer below it —
`exists_dichotomyData_of_cell_improvement → badCount → johnsonNumericBound →
mca_johnson_bound_CONJECTURE` — is landed and axiom-clean.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audited at end of file).
-/

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Polynomial Polynomial.Bivariate PowerSeries
open BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open BCIKS20.HenselNumerator
open _root_.ProximityGap Code
open CodingTheory.ProximityGap.Hab25Core
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame
open BCIKS20.CellSelectionFree BCIKS20.CellTailFree BCIKS20.CellPencilJohnson
open ArkLib ArkLib.RationalRootSupply
open scoped NNReal ENNReal

namespace BCIKS20.CellPackageAssembly

variable {F₀ : Type} [Field F₀]

/-- **The canonical root family of the section branch**: at the linear monic branch the
rational root at `z` is the base value itself. -/
noncomputable def sectionRoot (w : F₀[X][Y]) (x₀ : F₀) (z : F₀) :
    rationalRoot (H_tilde' (sectionBranch w x₀)) z :=
  rationalRoot_of_evalEval
    (by rw [sectionBranch_natDegree]; omega)
    (by
      show Polynomial.evalEval z ((w.eval (Polynomial.C x₀)).eval z) (sectionBranch w x₀) = 0
      rw [sectionBranch, Polynomial.evalEval, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, Polynomial.eval_sub]
      simp)

/-- The section root's value is the base value (monic ⟹ leading coefficient `1`). -/
theorem sectionRoot_val (w : F₀[X][Y]) (x₀ z : F₀) :
    (sectionRoot w x₀ z).1 = (w.eval (Polynomial.C x₀)).eval z := by
  rw [sectionRoot, rationalRoot_of_evalEval_val]
  have hm := sectionBranch_monic w x₀
  rw [show (sectionBranch w x₀).coeff (sectionBranch w x₀).natDegree
    = (sectionBranch w x₀).leadingCoeff from rfl, hm.leadingCoeff]
  simp

variable [Fintype F₀] [DecidableEq F₀]

/-- **THE ASSEMBLED PER-CELL `himpr` (item-1 closure shape)**: the dichotomy funnel's
input from the cell's own divisibilities + the surface + the quantitative §5 data alone —
every machinery leg (`hHyp`, monicity, tail, root family, base readings) discharged by
construction at the section branch. -/
theorem cell_improvement_of_surface
    {n k : ℕ} (hn : 0 < n) [NeZero n] {domain : Fin n ↪ F₀} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) (Fin n)}
    {T : ℕ} (hT : 1 ≤ T) (hk : 0 < k)
    (R : (F₀[X])[X][Y]) (hRirr : Irreducible R)
    (E : Finset F₀) (P : F₀ → F₀[X])
    (hdec : ∀ γ ∈ E, ∃ d : McaDecode domain k δ u γ, d.P = P γ)
    (hdvdR : ∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)))
    -- the surface (the S10-converse output)
    (x₀ : F₀) {w : F₀[X][Y]} (hwdeg : w.natDegree < n)
    (hwdvd : (Polynomial.X - Polynomial.C w) ∣ R)
    -- the quantitative §5 data (the genuine remaining content)
    (e : Fin n → F₀) (he : Function.Injective e) (u₀ u₁ : Fin n → F₀)
    {D : ℕ} (hD : D ≥ Bivariate.totalDegree (sectionBranch w x₀))
    (matchingSet : Fin n → Finset F₀)
    (hsepA : ∀ j, ∀ z ∈ matchingSet j,
      letI : Fact (Irreducible (sectionBranch w x₀)) := (sectionBranch_facts w x₀).1
      letI : Fact (0 < (sectionBranch w x₀).natDegree) := (sectionBranch_facts w x₀).2
      ((R.map (coeffHom_loc x₀ (hypotheses_of_surface hRirr hwdvd x₀))).map
        (PowerSeries.map (π_hat_z (hypotheses_of_surface hRirr hwdvd x₀) z
          (sectionRoot w x₀ z)
          (BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic
            (hypotheses_of_surface hRirr hwdvd x₀)
            (sectionBranch_monic w x₀).leadingCoeff z
            (sectionRoot w x₀ z))))).Separable)
    (hfold : ∀ j, ∀ z ∈ matchingSet j,
      (w.eval (Polynomial.C (e j) + Polynomial.C x₀)).eval z = u₀ j + z * u₁ j)
    {W : ℕ}
    (hweight : ∀ j,
      letI : Fact (Irreducible (sectionBranch w x₀)) := (sectionBranch_facts w x₀).1
      letI : Fact (0 < (sectionBranch w x₀).natDegree) := (sectionBranch_facts w x₀).2
      weight_Λ_over_𝒪 (Fact.out (p := 0 < (sectionBranch w x₀).natDegree))
        (Claim510Kill.killTarget (sectionBranch w x₀) x₀ R
          (hypotheses_of_surface hRirr hwdvd x₀) n (e j) (u₀ j) (u₁ j)) D
        ≤ (W : WithBot ℕ))
    (hcard : ∀ j, W * (sectionBranch w x₀).natDegree < (matchingSet j).card)
    (S₀ : Finset F₀)
    (hsep₀ : ∀ z ∈ S₀,
      letI : Fact (Irreducible (sectionBranch w x₀)) := (sectionBranch_facts w x₀).1
      letI : Fact (0 < (sectionBranch w x₀).natDegree) := (sectionBranch_facts w x₀).2
      ((R.map (coeffHom_loc x₀ (hypotheses_of_surface hRirr hwdvd x₀))).map
        (PowerSeries.map (π_hat_z (hypotheses_of_surface hRirr hwdvd x₀) z
          (sectionRoot w x₀ z)
          (BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic
            (hypotheses_of_surface hRirr hwdvd x₀)
            (sectionBranch_monic w x₀).leadingCoeff z
            (sectionRoot w x₀ z))))).Separable)
    {Bw : ℕ} (hBw : ∀ t, ((Polynomial.taylor (Polynomial.C x₀) w).coeff t).natDegree ≤ Bw)
    (hS₀ : max Bw 1 < S₀.card) :
    E.card ≤ T ∨ ∃ d₀ d₁ : Fin n → F₀, ∀ z ∈ E,
      ∃ x ∈ disagreeSet d₀ d₁, affineGap d₀ d₁ z x = 0 := by
  letI : Fact (Irreducible (sectionBranch w x₀)) := (sectionBranch_facts w x₀).1
  letI : Fact (0 < (sectionBranch w x₀).natDegree) := (sectionBranch_facts w x₀).2
  exact cell_improvement_of_pinning_package' (H := sectionBranch w x₀) hn hT hk
    R hRirr E P hdec hdvdR x₀
    (hypotheses_of_surface hRirr hwdvd x₀)
    (Fact.out)
    (sectionBranch_monic w x₀)
    (htail_of_surface hRirr hwdeg hwdvd x₀)
    e he u₀ u₁ hD matchingSet
    (sectionRoot w x₀)
    hwdeg hwdvd
    (fun j z _ => (sectionRoot_val w x₀ z).symm)
    hsepA hfold hweight hcard
    S₀
    (fun z _ => (sectionRoot_val w x₀ z).symm)
    hsep₀ hBw hS₀

end BCIKS20.CellPackageAssembly

/-! ## Axiom audit — all kernel-clean. -/
#print axioms BCIKS20.CellPackageAssembly.sectionRoot
#print axioms BCIKS20.CellPackageAssembly.sectionRoot_val
#print axioms BCIKS20.CellPackageAssembly.cell_improvement_of_surface
