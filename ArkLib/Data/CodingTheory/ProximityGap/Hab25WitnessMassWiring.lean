/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25FactorBudgetSupply
import ArkLib.Data.CodingTheory.ProximityGap.Hab25RichCoordinateGate

/-!
# Witness-mass → rich-factor wiring (#302, the R-K5 residual item 1)

The rich-coordinate gate (`global_branch_of_perCoordinate_rich` /
`exists_global_branch_of_proximity`) consumes, per chosen coordinate, ONE witness-rich
irreducible budgeted factor.  This file produces that factor from **interpolant-level**
data — closing the "witnessed-mass → rich-factor wiring at the interpolant fiber" residual
of the gate's status note:

* **`exists_rich_factor_of_witness_mass`** — pigeonhole over the attribution cover: if the
  fold section's value is a live fiber root of a budgeted interpolant `Q` at more than
  `deg_Y Q · (B + deg_Y Q·(L−1))` scalars, then SOME normalized irreducible factor of `Q`
  carries more than `B + deg_Y(that factor)·(L−1)` of those agreements — exactly the gate's
  `(hirr, hB, hrich, hwit)` package at the coordinate (the per-factor threshold is absorbed
  into the uniform one via `natDegree_le_of_dvd`);
* **`exists_global_branch_of_interpolant_mass`** — the composed gate: per-scalar proximity
  data + the Claim 5.11 numeric leg + **per-coordinate budgeted interpolants carrying
  witness mass at the rich coordinates** + the decode degree/divisibility data + the count
  leg produce the global branch `(Y − C pHat_T) ∣ R` at some `k`-subset `T`.

After this file, the counting lane's input surface is: proximity data, numeric legs, and
"the fold value is a mass-witnessed fiber root of SOME budgeted interpolant at each rich
coordinate" — the latter being precisely the GS-side supply shape (the specialized sloped
interpolant; `GSInterpolantSloped` provides the budgets, the GS root relation provides the
vanishing).

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audited at end of file).
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Polynomial Polynomial.Bivariate Finset
open _root_.ProximityGap Code

attribute [local instance] Classical.propDecidable

variable {F₀ : Type} [Field F₀]

/-- **Pigeonhole over the attribution cover**: witness mass
`> deg_Y Q · (B + deg_Y Q·(L−1))` on a budgeted interpolant concentrates in one normalized
irreducible factor above ITS OWN threshold `B + deg_Y(factor)·(L−1)`. -/
theorem exists_rich_factor_of_witness_mass
    (Q : F₀[X][Y]) (hQ0 : Q ≠ 0) {B : ℕ} (hB : ∀ b : ℕ, (Q.coeff b).natDegree ≤ B)
    (L : ℕ) (w : F₀[X]) (Wit : Finset F₀)
    (hlive : ∀ ζ ∈ Wit, Q.map (Polynomial.evalRingHom ζ) ≠ 0)
    (hvan : ∀ ζ ∈ Wit, (Q.map (Polynomial.evalRingHom ζ)).eval (w.eval ζ) = 0)
    (hmass : Q.natDegree * (B + Q.natDegree * (L - 1)) < Wit.card) :
    ∃ Hp : F₀[X][Y], ∃ S : Finset F₀, Irreducible Hp ∧
      (∀ k : ℕ, (Hp.coeff k).natDegree ≤ B) ∧
      (B + Hp.natDegree * (L - 1) < S.card) ∧
      (∀ ζ ∈ S, (Hp.map (Polynomial.evalRingHom ζ)).eval (w.eval ζ) = 0) := by
  classical
  set supply := factorBudgetSupply Q hQ0 hB with hsupply
  set τ : ℕ := B + Q.natDegree * (L - 1) with hτ
  -- the attribution cover: every witnessed scalar lies in some factor's agreement fiber
  have hcover : Wit ⊆ supply.Index.biUnion (fun Hp => Wit.filter (fun ζ =>
      (Hp.map (Polynomial.evalRingHom ζ)).eval (w.eval ζ) = 0)) := by
    intro ζ hζ
    obtain ⟨Hp, hHp, hroot⟩ := supply.attribution ζ (w.eval ζ) (hlive ζ hζ) (hvan ζ hζ)
    exact Finset.mem_biUnion.mpr ⟨Hp, hHp, Finset.mem_filter.mpr ⟨hζ, hroot⟩⟩
  -- some indexed factor's fiber exceeds the uniform threshold τ
  have hrichIdx : ∃ Hp ∈ supply.Index, τ <
      (Wit.filter (fun ζ =>
        (Hp.map (Polynomial.evalRingHom ζ)).eval (w.eval ζ) = 0)).card := by
    by_contra hcon
    push Not at hcon
    have hsum : Wit.card ≤ ∑ Hp ∈ supply.Index,
        (Wit.filter (fun ζ =>
          (Hp.map (Polynomial.evalRingHom ζ)).eval (w.eval ζ) = 0)).card :=
      le_trans (Finset.card_le_card hcover) Finset.card_biUnion_le
    have hbound : Wit.card ≤ supply.Index.card * τ := by
      calc Wit.card
          ≤ ∑ Hp ∈ supply.Index, (Wit.filter (fun ζ =>
              (Hp.map (Polynomial.evalRingHom ζ)).eval (w.eval ζ) = 0)).card := hsum
        _ ≤ ∑ _Hp ∈ supply.Index, τ := Finset.sum_le_sum hcon
        _ = supply.Index.card * τ := by rw [Finset.sum_const, smul_eq_mul]
    have hall : Wit.card ≤ Q.natDegree * τ :=
      le_trans hbound (Nat.mul_le_mul_right τ supply.card_le)
    rw [hτ] at hall
    exact absurd hmass (not_lt.mpr hall)
  obtain ⟨Hp, hHp, hbig⟩ := hrichIdx
  -- the factor's own threshold is ≤ the uniform τ
  have hdegle : Hp.natDegree ≤ Q.natDegree :=
    Polynomial.natDegree_le_of_dvd (supply.dvd Hp hHp) hQ0
  have hthr : B + Hp.natDegree * (L - 1) ≤ τ := by
    rw [hτ]
    have := Nat.mul_le_mul_right (L - 1) hdegle
    omega
  exact ⟨Hp, Wit.filter (fun ζ =>
      (Hp.map (Polynomial.evalRingHom ζ)).eval (w.eval ζ) = 0),
    supply.irr Hp hHp, fun k => supply.budget Hp hHp k,
    lt_of_le_of_lt hthr hbig, fun ζ hζ => (Finset.mem_filter.mp hζ).2⟩

variable [Fintype F₀] [DecidableEq F₀]

/-- **The interpolant-mass gate**: the global branch from per-coordinate budgeted
interpolants carrying witness mass at the rich coordinates (the GS-side supply shape),
through the rich-coordinate gate. -/
theorem exists_global_branch_of_interpolant_mass {n L k : ℕ} (hk : 0 < k) (hL : 0 < L)
    [NeZero n]
    {domain : Fin n ↪ F₀} {u : WordStack F₀ (Fin L) (Fin n)}
    (R : (F₀[X])[X][Y]) {BR : ℕ}
    (hRB : ∀ b a : ℕ, ((R.coeff b).coeff a).natDegree ≤ BR)
    (E : Finset F₀) (P : F₀ → F₀[X])
    (e M : ℕ) (hkn : k ≤ n)
    (hprox : ∀ γ ∈ E, n - e ≤
      (Finset.univ.filter (fun t => decodeAgreesAt domain u P t γ)).card)
    (hnum : e * E.card < (M + 1) * (n - k + 1))
    (hdeg : ∀ γ ∈ E, (P γ).degree < (k : ℕ))
    (hdvdP : ∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)))
    (Q : Fin n → F₀[X][Y]) {B : ℕ}
    (Wit : Fin n → Finset F₀)
    (hsupply : ∀ t : Fin n,
      E.card - M ≤ (E.filter (fun γ => decodeAgreesAt domain u P t γ)).card →
      Q t ≠ 0 ∧ (∀ b : ℕ, ((Q t).coeff b).natDegree ≤ B) ∧
      (∀ ζ ∈ Wit t, (Q t).map (Polynomial.evalRingHom ζ) ≠ 0) ∧
      (∀ ζ ∈ Wit t, ((Q t).map (Polynomial.evalRingHom ζ)).eval
        ((foldSectionAt u t).eval ζ) = 0) ∧
      ((Q t).natDegree * (B + (Q t).natDegree * (L - 1)) < (Wit t).card))
    (hbig : BR + R.natDegree * (L - 1) + k * M < E.card) :
    ∃ T : Finset (Fin n), T.card = k ∧
      (Polynomial.X - Polynomial.C
          (branchOfCurveTuple (fun j => lagrangeCurveTuple domain u T j))) ∣ R := by
  classical
  -- per rich coordinate, extract the rich factor by pigeonhole; junk elsewhere
  have hchoice : ∀ t : Fin n,
      E.card - M ≤ (E.filter (fun γ => decodeAgreesAt domain u P t γ)).card →
      ∃ Hp : F₀[X][Y], ∃ S : Finset F₀, Irreducible Hp ∧
        (∀ k' : ℕ, (Hp.coeff k').natDegree ≤ B) ∧
        (B + Hp.natDegree * (L - 1) < S.card) ∧
        (∀ ζ ∈ S, (Hp.map (Polynomial.evalRingHom ζ)).eval
          ((foldSectionAt u t).eval ζ) = 0) := by
    intro t hrich
    obtain ⟨hQ0, hQB, hlive, hvan, hmass⟩ := hsupply t hrich
    exact exists_rich_factor_of_witness_mass
      (Q t) hQ0 hQB L (foldSectionAt u t) (Wit t) hlive hvan hmass
  -- package as total functions (junk where the coordinate is not rich)
  set HpF : Fin n → F₀[X][Y] := fun t =>
    if h : E.card - M ≤ (E.filter (fun γ => decodeAgreesAt domain u P t γ)).card
    then Classical.choose (hchoice t h) else Polynomial.X with hHpF
  set SF : Fin n → Finset F₀ := fun t =>
    if h : E.card - M ≤ (E.filter (fun γ => decodeAgreesAt domain u P t γ)).card
    then Classical.choose (Classical.choose_spec (hchoice t h)) else ∅ with hSF
  refine exists_global_branch_of_proximity hk hL R hRB E P e M hkn hprox hnum hdeg hdvdP
    HpF (B := B) SF (fun t hrich => ?_) hbig
  have hspec := Classical.choose_spec (Classical.choose_spec (hchoice t hrich))
  rw [hHpF, hSF]
  simp only [dif_pos hrich]
  exact ⟨hspec.1, hspec.2.1, hspec.2.2.1, hspec.2.2.2⟩

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms exists_rich_factor_of_witness_mass
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms exists_global_branch_of_interpolant_mass
