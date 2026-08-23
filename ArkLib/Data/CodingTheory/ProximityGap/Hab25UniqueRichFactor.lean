/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CoordinateUpgradeWeld

/-!
# The unique rich factor at a coordinate (#302, task R-K2)

At a fixed coordinate, the weld (`coordinateUpgrade_of_assigned_factor_rich`) consumes, for
each cell scalar, an assigned fiber factor carrying more than `B + deg_Y·dw` *witnessed*
agreements with the fold section `w`.  This file proves that such a **witness-rich factor is
unique**: richness forces `(Y − C w) ∣ Hp` (the flat-budget kill,
`ArkLib.FactorKill.section_root_of_many_agreements` + the factor theorem), and two factors
without a common non-unit divisor — in particular two non-associated irreducibles, or two
coprime factors — cannot share the non-unit divisor `Y − C w`.

Main declarations (`w` a section of degree `≤ dw`, all factors with flat coefficient
budget `B`):

* `WitnessRich Hp w B dw` — `Hp` carries strictly more than `B + deg_Y Hp · dw` witnessed
  fiber agreements with `w` (the exact `hrich`/`hwit` data shape of the weld;
  `witnessRich_of_weld_data` is the literal bridge);
* `WitnessRich.section_dvd` — a rich budgeted factor satisfies `(Y − C w) ∣ Hp`;
* `WitnessRich.associated_section` — a rich budgeted **irreducible** factor is an associate
  of `Y − C w` (the `c·(Y − w(Z))` shape of the per-factor kill, stated as `Associated`);
* `witnessRich_at_most_one` — two non-associated irreducible budgeted factors cannot both
  be rich;
* `not_witnessRich_both_of_relPrime` / `not_witnessRich_both_of_isCoprime` — the
  coprime formulations (no irreducibility needed): factors with no common non-unit divisor
  cannot both be rich;
* `witnessRich_factor_unique` — the family version: in a family of pairwise non-associated
  irreducible budgeted factors, at most one index is rich;
* `exists_unique_witnessRich_factor` — **richness concentration**: if the total fold
  agreement mass at the coordinate exceeds `(#factors)·(B + d·dw)`, then a rich factor
  exists (pigeonhole, `ArkLib.FactorKill.exists_witness_rich_factor`, budgets inherited by
  `coeff_budget_of_dvd`) AND it is the unique rich index.

Design note: `F₀[X][Y]` is a UFD but not Euclidean, so "coprime" is taken in the
no-common-non-unit-divisor sense (`relPrime` hypothesis) or Mathlib's Bezout-style
`IsCoprime` (which implies it via `IsCoprime.isUnit_of_dvd'`); for the weld's actual data —
irreducible factors — non-association is the right notion and is what the family version
uses.

## References

* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, Claims 5.9–5.11, Appendix A.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Polynomial Polynomial.Bivariate Finset
open _root_.ProximityGap Code

attribute [local instance] Classical.propDecidable

variable {F₀ : Type} [Field F₀]

/-! ## Witness-richness: the weld's per-factor data shape -/

/-- A fiber factor `Hp : F₀[X][Y]` is **witness-rich** for the section `w : F₀[X]` (with flat
coefficient budget `B` and section degree bound `dw`) when some scalar set of size strictly
above the kill threshold `B + deg_Y Hp · dw` witnesses fiber agreements of `Hp` with `w`.
This is exactly the `hrich`/`hwit` data the weld
(`coordinateUpgrade_of_assigned_factor_rich`) demands of each assigned factor. -/
def WitnessRich (Hp : F₀[X][Y]) (w : F₀[X]) (B dw : ℕ) : Prop :=
  ∃ S : Finset F₀, B + Hp.natDegree * dw < S.card ∧
    ∀ ζ ∈ S, (Hp.map (Polynomial.evalRingHom ζ)).eval (w.eval ζ) = 0

/-- Bridge to the weld's data shape: at a coordinate `t` and scalar `γ`, the weld's
`hrich`/`hwit` hypotheses say precisely that the assigned factor is `WitnessRich` for the
fold section `foldSectionAt u t` with `dw = L − 1`. -/
lemma witnessRich_of_weld_data {n L : ℕ} {u : WordStack F₀ (Fin L) (Fin n)}
    {ι : Type} (Hf : Fin n → ι → F₀[X][Y]) {B : ℕ}
    (assign : Fin n → F₀ → ι) (S : Fin n → ι → Finset F₀) (t : Fin n) (γ : F₀)
    (hrich : B + (Hf t (assign t γ)).natDegree * (L - 1) < (S t (assign t γ)).card)
    (hwit : ∀ ζ ∈ S t (assign t γ),
      ((Hf t (assign t γ)).map (Polynomial.evalRingHom ζ)).eval
        ((foldSectionAt u t).eval ζ) = 0) :
    WitnessRich (Hf t (assign t γ)) (foldSectionAt u t) B (L - 1) :=
  ⟨S t (assign t γ), hrich, hwit⟩

/-- The candidate common divisor `Y − C w` is not a unit (it has `Y`-degree `1`). -/
lemma not_isUnit_Y_sub_section (w : F₀[X]) :
    ¬ IsUnit (Polynomial.X - Polynomial.C w : F₀[X][Y]) := by
  intro hu
  have h1 := Polynomial.natDegree_eq_zero_of_isUnit hu
  rw [Polynomial.natDegree_X_sub_C] at h1
  exact one_ne_zero h1

/-! ## Richness forces the section divisor -/

/-- **Richness forces the section divisor.**  A witness-rich factor with flat coefficient
budget `B` has `w` as an identical `Y`-root, i.e. `(Y − C w) ∣ Hp`: the flat-budget kill
(`ArkLib.FactorKill.section_root_of_many_agreements`) plus the factor theorem. -/
theorem WitnessRich.section_dvd {Hp : F₀[X][Y]} {w : F₀[X]} {B dw : ℕ}
    (hB : ∀ k, (Hp.coeff k).natDegree ≤ B) (hw : w.natDegree ≤ dw)
    (hrich : WitnessRich Hp w B dw) :
    (Polynomial.X - Polynomial.C w) ∣ Hp := by
  obtain ⟨S, hcard, hvan⟩ := hrich
  exact Polynomial.dvd_iff_isRoot.mpr
    (ArkLib.FactorKill.section_root_of_many_agreements hB hw S hcard hvan)

/-- **The rich irreducible factor is `c·(Y − w(Z))`.**  A witness-rich budgeted factor that
is irreducible is an associate of `Y − C w` — the `Associated` form of the conclusion of
`ArkLib.FactorKill.fiber_root_eq_section_of_irreducible_of_many_agreements`. -/
theorem WitnessRich.associated_section {Hp : F₀[X][Y]} {w : F₀[X]} {B dw : ℕ}
    (hirr : Irreducible Hp)
    (hB : ∀ k, (Hp.coeff k).natDegree ≤ B) (hw : w.natDegree ≤ dw)
    (hrich : WitnessRich Hp w B dw) :
    Associated Hp (Polynomial.X - Polynomial.C w) := by
  obtain ⟨q, hq⟩ := hrich.section_dvd hB hw
  have hqu : IsUnit q :=
    (hirr.isUnit_or_isUnit hq).resolve_left (not_isUnit_Y_sub_section w)
  exact Associated.symm ⟨hqu.unit, by rw [IsUnit.unit_spec]; exact hq.symm⟩

/-! ## Uniqueness: at most one rich factor -/

/-- **At most one rich factor — coprime form, no irreducibility.**  Two budgeted factors
with no common non-unit divisor cannot both be witness-rich for the same section: both
would be divisible by the non-unit `Y − C w`. -/
theorem not_witnessRich_both_of_relPrime {Hp₁ Hp₂ : F₀[X][Y]}
    (hcop : ∀ q : F₀[X][Y], q ∣ Hp₁ → q ∣ Hp₂ → IsUnit q)
    {w : F₀[X]} {B dw : ℕ}
    (hB₁ : ∀ k, (Hp₁.coeff k).natDegree ≤ B) (hB₂ : ∀ k, (Hp₂.coeff k).natDegree ≤ B)
    (hw : w.natDegree ≤ dw)
    (h₁ : WitnessRich Hp₁ w B dw) (h₂ : WitnessRich Hp₂ w B dw) : False :=
  not_isUnit_Y_sub_section w
    (hcop _ (h₁.section_dvd hB₁ hw) (h₂.section_dvd hB₂ hw))

/-- **At most one rich factor — `IsCoprime` form.**  Mathlib-coprime budgeted factors cannot
both be witness-rich for the same section. -/
theorem not_witnessRich_both_of_isCoprime {Hp₁ Hp₂ : F₀[X][Y]}
    (hcop : IsCoprime Hp₁ Hp₂)
    {w : F₀[X]} {B dw : ℕ}
    (hB₁ : ∀ k, (Hp₁.coeff k).natDegree ≤ B) (hB₂ : ∀ k, (Hp₂.coeff k).natDegree ≤ B)
    (hw : w.natDegree ≤ dw)
    (h₁ : WitnessRich Hp₁ w B dw) (h₂ : WitnessRich Hp₂ w B dw) : False :=
  not_witnessRich_both_of_relPrime
    (fun _ hq₁ hq₂ => hcop.isUnit_of_dvd' hq₁ hq₂) hB₁ hB₂ hw h₁ h₂

/-- **At most one rich factor — irreducible form.**  Two non-associated irreducible budgeted
factors cannot both be witness-rich for the same section: each would be an associate of
`Y − C w`, hence of the other. -/
theorem witnessRich_at_most_one {Hp₁ Hp₂ : F₀[X][Y]}
    (hirr₁ : Irreducible Hp₁) (hirr₂ : Irreducible Hp₂)
    (hnassoc : ¬ Associated Hp₁ Hp₂)
    {w : F₀[X]} {B dw : ℕ}
    (hB₁ : ∀ k, (Hp₁.coeff k).natDegree ≤ B) (hB₂ : ∀ k, (Hp₂.coeff k).natDegree ≤ B)
    (hw : w.natDegree ≤ dw)
    (h₁ : WitnessRich Hp₁ w B dw) (h₂ : WitnessRich Hp₂ w B dw) : False :=
  hnassoc ((h₁.associated_section hirr₁ hB₁ hw).trans
    (h₂.associated_section hirr₂ hB₂ hw).symm)

/-- **The family uniqueness.**  In a family of pairwise non-associated irreducible budgeted
factors — the weld's `Hf` data shape — at most one index is witness-rich for a given
section: any two rich indices coincide. -/
theorem witnessRich_factor_unique {ι : Type*} {s : Finset ι} {Hf : ι → F₀[X][Y]}
    (hirr : ∀ i ∈ s, Irreducible (Hf i))
    (hsep : ∀ i ∈ s, ∀ j ∈ s, Associated (Hf i) (Hf j) → i = j)
    {w : F₀[X]} {B dw : ℕ}
    (hB : ∀ i ∈ s, ∀ k, ((Hf i).coeff k).natDegree ≤ B)
    (hw : w.natDegree ≤ dw)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s)
    (hrichi : WitnessRich (Hf i) w B dw) (hrichj : WitnessRich (Hf j) w B dw) :
    i = j :=
  hsep i hi j hj
    ((hrichi.associated_section (hirr i hi) (hB i hi) hw).trans
      (hrichj.associated_section (hirr j hj) (hB j hj) hw).symm)

/-! ## Richness concentration: the rich factor exists and is unique -/

/-- **Richness concentration.**  If the fiber `G = ∏ Hf i` (budgeted by `B`, factor
`Y`-degrees `≤ d`) vanishes along the section `w` on a witness set `W` of size exceeding
`(#factors)·(B + d·dw)`, then a witness-rich factor exists — pigeonhole,
`ArkLib.FactorKill.exists_witness_rich_factor`, with the per-factor budgets inherited via
`ArkLib.FactorKill.coeff_budget_of_dvd` — and, the family being pairwise non-associated
irreducibles, it is the UNIQUE rich index. -/
theorem exists_unique_witnessRich_factor {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {Hf : ι → F₀[X][Y]} {G : F₀[X][Y]} (hG : G = ∏ i ∈ s, Hf i) (hG0 : G ≠ 0)
    (hirr : ∀ i ∈ s, Irreducible (Hf i))
    (hsep : ∀ i ∈ s, ∀ j ∈ s, Associated (Hf i) (Hf j) → i = j)
    {B d dw : ℕ} (hB : ∀ k, (G.coeff k).natDegree ≤ B)
    (hd : ∀ i ∈ s, (Hf i).natDegree ≤ d)
    {w : F₀[X]} (hw : w.natDegree ≤ dw)
    (W : Finset F₀)
    (hvan : ∀ ζ ∈ W, (G.map (Polynomial.evalRingHom ζ)).eval (w.eval ζ) = 0)
    (hcount : s.card * (B + d * dw) < W.card) :
    ∃ i ∈ s, WitnessRich (Hf i) w B dw ∧
      ∀ j ∈ s, WitnessRich (Hf j) w B dw → j = i := by
  obtain ⟨i, hi, hcard⟩ :=
    ArkLib.FactorKill.exists_witness_rich_factor hG W (B + d * dw) hvan hcount
  have hBi : ∀ j ∈ s, ∀ k, ((Hf j).coeff k).natDegree ≤ B := by
    intro j hj k
    refine ArkLib.FactorKill.coeff_budget_of_dvd ?_ hG0 hB k
    rw [hG]
    exact Finset.dvd_prod_of_mem Hf hj
  have hrichi : WitnessRich (Hf i) w B dw := by
    refine ⟨W.filter (fun ζ =>
      ((Hf i).map (Polynomial.evalRingHom ζ)).eval (w.eval ζ) = 0), ?_, ?_⟩
    · exact lt_of_le_of_lt
        (Nat.add_le_add_left (Nat.mul_le_mul_right dw (hd i hi)) B) hcard
    · exact fun ζ hζ => (Finset.mem_filter.mp hζ).2
  exact ⟨i, hi, hrichi, fun j hj hrichj =>
    witnessRich_factor_unique hirr hsep hBi hw hj hi hrichj hrichi⟩

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms witnessRich_of_weld_data
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms not_isUnit_Y_sub_section
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms WitnessRich.section_dvd
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms WitnessRich.associated_section
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms not_witnessRich_both_of_relPrime
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms not_witnessRich_both_of_isCoprime
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms witnessRich_at_most_one
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms witnessRich_factor_unique
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms exists_unique_witnessRich_factor
