/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CoordinateUpgradeWeld
import ArkLib.Data.CodingTheory.ProximityGap.Hab25DegreeBudget

/-!
# Factor budget supply for the CoordinateUpgrade weld (#302, R-K4)

The weld `coordinateUpgrade_of_assigned_factor_rich` consumes abstract per-coordinate factor
data: an index type `ι`, factors `Hf : Fin n → ι → F₀[X][Y]`, per-factor irreducibility
(`hirr`), and a flat per-factor coefficient budget (`hB`).  This file PRODUCES that data from
a bivariate interpolant `Q : F₀[X][Y]` with a flat coefficient budget — the budget-supply
instantiation promised by the weld's docstring (`coeff_budget_of_dvd` + interpolant budget):

* `factorBudgetIndex` — the finite index set of distinct positive-`Y`-degree normalized
  irreducible factors of `Q`, with `card ≤ Q.natDegree` (= `deg_Y Q`, via the landed
  `Issue68Hab25.card_natDegreePos_normalizedFactors_le_natDegree`);
* `factorBudgetIndex_attribution` — **root attribution**: any fiber root of `Q` at a scalar
  `γ` with live fiber (`Q.map (evalRingHom γ) ≠ 0`) is a fiber root of some indexed factor
  (content factors are excluded exactly by fiber liveness);
* `FactorBudgetSupply` / `factorBudgetSupply` — the one-coordinate package: index set,
  cardinality bound, positivity, irreducibility, divisor-inherited flat budget
  (`ArkLib.FactorKill.coeff_budget_of_dvd`), divisibility, and root attribution;
* `weldFactorFamily` + lemmas — the `Fin n`-indexed wrapper with the weld's exact shapes:
  uniform index type `ι := F₀[X][Y]`, total irreducibility (junk indices map to the
  irreducible default `Y`), total budget, and per-coordinate root attribution feeding the
  weld's `assign`;
* `exists_weldFactorInputs` — the single existence capstone: from a per-coordinate
  interpolant family with a flat budget, the weld inputs `(ι, Hf, hirr, hB)` exist, plus
  attribution and divisibility.

## Honest scope

This file supplies the *factor data* inputs `(ι, Hf t, hirr, hB)` of
`coordinateUpgrade_of_assigned_factor_rich`, plus the root-attribution step needed to define
`assign` (each decode value at a live fiber roots in SOME indexed factor).  It does NOT
discharge the assignment-coherence richness residual (`hrich`/`hwit`): that each assigned
factor carries `> B + deg_Y·(L−1)` *witnessed* fold agreements remains the open core
(pigeonhole for witnessed scalars via `exists_witness_rich_factor`; the `≤ M` unwitnessed
scalars per coordinate are the genuine residual, per the weld's docstring).

## References

* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, Claims 5.9–5.11.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Polynomial Polynomial.Bivariate Finset

variable {F₀ : Type} [Field F₀] [DecidableEq F₀]

/-! ## The one-coordinate factor index -/

/-- The factor index of a bivariate interpolant `Q : F₀[X][Y]`: its distinct
positive-`Y`-degree normalized irreducible factors, as a concrete `Finset`. -/
noncomputable def factorBudgetIndex (Q : F₀[X][Y]) : Finset (F₀[X][Y]) :=
  ((UniqueFactorizationMonoid.normalizedFactors Q).toFinset).filter
    (fun q => 0 < q.natDegree)

/-- Membership unfolding: an indexed factor is a normalized factor of positive `Y`-degree. -/
lemma mem_factorBudgetIndex {Q Hp : F₀[X][Y]} :
    Hp ∈ factorBudgetIndex Q ↔
      Hp ∈ UniqueFactorizationMonoid.normalizedFactors Q ∧ 0 < Hp.natDegree := by
  rw [factorBudgetIndex, Finset.mem_filter, Multiset.mem_toFinset]

/-- The index count is bounded by the `Y`-degree of the interpolant
(the `hYbound` shape, via the landed degree-budget count). -/
theorem factorBudgetIndex_card_le (Q : F₀[X][Y]) (hQ0 : Q ≠ 0) :
    (factorBudgetIndex Q).card ≤ Q.natDegree :=
  Issue68Hab25.card_natDegreePos_normalizedFactors_le_natDegree Q hQ0

/-- Indexed factors are irreducible. -/
theorem factorBudgetIndex_irreducible {Q Hp : F₀[X][Y]} (h : Hp ∈ factorBudgetIndex Q) :
    Irreducible Hp :=
  UniqueFactorizationMonoid.irreducible_of_normalized_factor Hp
    (mem_factorBudgetIndex.mp h).1

/-- Indexed factors divide the interpolant. -/
theorem factorBudgetIndex_dvd {Q Hp : F₀[X][Y]} (h : Hp ∈ factorBudgetIndex Q) : Hp ∣ Q :=
  UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (mem_factorBudgetIndex.mp h).1

/-- **The budget supply**: indexed factors inherit the interpolant's flat coefficient
budget, by divisor inheritance (`ArkLib.FactorKill.coeff_budget_of_dvd`). -/
theorem factorBudgetIndex_budget {Q Hp : F₀[X][Y]} (h : Hp ∈ factorBudgetIndex Q)
    (hQ0 : Q ≠ 0) {B : ℕ} (hB : ∀ b : ℕ, (Q.coeff b).natDegree ≤ B) (k : ℕ) :
    (Hp.coeff k).natDegree ≤ B :=
  ArkLib.FactorKill.coeff_budget_of_dvd (factorBudgetIndex_dvd h) hQ0 hB k

/-- **Root attribution.**  Any fiber root of `Q` at a scalar `γ` whose fiber is alive
(`Q.map (evalRingHom γ) ≠ 0`) is a fiber root of some indexed factor: specializing the
normalized factorization, the unit and the content (degree-`0`) factors cannot absorb the
root — a vanishing content factor would kill the whole fiber. -/
theorem factorBudgetIndex_attribution (Q : F₀[X][Y]) (hQ0 : Q ≠ 0) (γ y : F₀)
    (hfib : Q.map (Polynomial.evalRingHom γ) ≠ 0)
    (hroot : (Q.map (Polynomial.evalRingHom γ)).eval y = 0) :
    ∃ Hp ∈ factorBudgetIndex Q, (Hp.map (Polynomial.evalRingHom γ)).eval y = 0 := by
  classical
  -- the full specialize-then-evaluate ring hom
  set ψ : F₀[X][Y] →+* F₀ :=
    (Polynomial.evalRingHom y).comp (Polynomial.mapRingHom (Polynomial.evalRingHom γ))
    with hψ
  have hψapply : ∀ p : F₀[X][Y], ψ p = (p.map (Polynomial.evalRingHom γ)).eval y := by
    intro p
    rw [hψ, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.coe_evalRingHom]
  -- specialize the normalized factorization
  obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.prod_normalizedFactors (a := Q) hQ0
  have h1 : ψ ((UniqueFactorizationMonoid.normalizedFactors Q).prod * ↑u) = 0 := by
    rw [hu, hψapply]; exact hroot
  rw [map_mul] at h1
  have hunit : IsUnit (ψ (↑u : F₀[X][Y])) := u.isUnit.map ψ
  have h2 : ψ ((UniqueFactorizationMonoid.normalizedFactors Q).prod) = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h hunit.ne_zero
  rw [map_multiset_prod] at h2
  obtain ⟨f, hf, hf0⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp h2)
  -- the root-absorbing factor has positive `Y`-degree, else the fiber dies
  have hpos : 0 < f.natDegree := by
    by_contra hnd
    have hc : f = Polynomial.C (f.coeff 0) :=
      Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_not_pos hnd)
    have hcγ : (f.coeff 0).eval γ = 0 := by
      have := hf0
      rw [hψapply, hc, Polynomial.map_C, Polynomial.eval_C, Polynomial.coe_evalRingHom]
        at this
      exact this
    have hfmap : f.map (Polynomial.evalRingHom γ) = 0 := by
      rw [hc, Polynomial.map_C]
      rw [show Polynomial.evalRingHom γ (f.coeff 0) = (f.coeff 0).eval γ from rfl, hcγ,
        Polynomial.C_0]
    obtain ⟨g, hg⟩ := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hf
    apply hfib
    rw [hg, Polynomial.map_mul, hfmap, zero_mul]
  refine ⟨f, mem_factorBudgetIndex.mpr ⟨hf, hpos⟩, ?_⟩
  rw [← hψapply]; exact hf0

/-! ## The one-coordinate package -/

/-- **The one-coordinate factor budget supply**: exactly the per-coordinate factor data the
weld `coordinateUpgrade_of_assigned_factor_rich` consumes — a finite factor index with a
`Y`-degree cardinality bound, positivity, irreducibility, the divisor-inherited flat
coefficient budget, divisibility into the interpolant, and root attribution at live
fibers. -/
structure FactorBudgetSupply (Q : F₀[X][Y]) (B : ℕ) : Type where
  /-- The finite factor index. -/
  Index : Finset (F₀[X][Y])
  /-- The `hYbound`-shaped count: at most `deg_Y Q` indexed factors. -/
  card_le : Index.card ≤ Q.natDegree
  /-- Indexed factors have positive `Y`-degree. -/
  pos : ∀ Hp ∈ Index, 0 < Polynomial.natDegree Hp
  /-- Indexed factors are irreducible (the weld's `hirr`). -/
  irr : ∀ Hp ∈ Index, Irreducible Hp
  /-- Indexed factors carry the flat coefficient budget (the weld's `hB`). -/
  budget : ∀ Hp ∈ Index, ∀ k : ℕ, ((Hp : F₀[X][Y]).coeff k).natDegree ≤ B
  /-- Indexed factors divide the interpolant. -/
  dvd : ∀ Hp ∈ Index, Hp ∣ Q
  /-- Root attribution: fiber roots at live fibers root in some indexed factor. -/
  attribution : ∀ γ y : F₀, Q.map (Polynomial.evalRingHom γ) ≠ 0 →
    (Q.map (Polynomial.evalRingHom γ)).eval y = 0 →
    ∃ Hp ∈ Index, (Hp.map (Polynomial.evalRingHom γ)).eval y = 0

/-- **The budget supply instantiation (one coordinate)**: a nonzero interpolant with a flat
coefficient budget yields a full `FactorBudgetSupply`. -/
noncomputable def factorBudgetSupply (Q : F₀[X][Y]) (hQ0 : Q ≠ 0)
    {B : ℕ} (hB : ∀ b : ℕ, (Q.coeff b).natDegree ≤ B) :
    FactorBudgetSupply Q B where
  Index := factorBudgetIndex Q
  card_le := factorBudgetIndex_card_le Q hQ0
  pos := fun _ h => (mem_factorBudgetIndex.mp h).2
  irr := fun _ h => factorBudgetIndex_irreducible h
  budget := fun _ h k => factorBudgetIndex_budget h hQ0 hB k
  dvd := fun _ h => factorBudgetIndex_dvd h
  attribution := factorBudgetIndex_attribution Q hQ0

/-! ## The `Fin n`-indexed wrapper, in the weld's exact shapes

The weld takes ONE index type `ι` uniform over coordinates and demands irreducibility and
budget for EVERY `i : ι`.  We take `ι := F₀[X][Y]` and send junk indices to the irreducible
default `Y` (the variable `Polynomial.X` of the outer ring), which has flat budget `0 ≤ B`. -/

variable {n : ℕ} {Qc : Fin n → F₀[X][Y]} {B : ℕ}

/-- The weld-shaped factor family: at coordinate `t`, indexed factors are themselves, junk
indices default to the irreducible `Y`. -/
noncomputable def weldFactorFamily (supply : ∀ t, FactorBudgetSupply (Qc t) B) :
    Fin n → F₀[X][Y] → F₀[X][Y] :=
  fun t i => if i ∈ (supply t).Index then i else Polynomial.X

/-- On indexed factors the family is the identity. -/
lemma weldFactorFamily_eq_of_mem (supply : ∀ t, FactorBudgetSupply (Qc t) B)
    {t : Fin n} {i : F₀[X][Y]} (h : i ∈ (supply t).Index) :
    weldFactorFamily supply t i = i := by
  unfold weldFactorFamily
  exact if_pos h

/-- The weld's `hirr`, total over the uniform index type. -/
theorem weldFactorFamily_irreducible (supply : ∀ t, FactorBudgetSupply (Qc t) B)
    (t : Fin n) (i : F₀[X][Y]) : Irreducible (weldFactorFamily supply t i) := by
  unfold weldFactorFamily
  split
  · next h => exact (supply t).irr i h
  · exact Polynomial.irreducible_X

/-- The weld's `hB`, total over the uniform index type. -/
theorem weldFactorFamily_budget (supply : ∀ t, FactorBudgetSupply (Qc t) B)
    (t : Fin n) (i : F₀[X][Y]) (k : ℕ) :
    ((weldFactorFamily supply t i).coeff k).natDegree ≤ B := by
  unfold weldFactorFamily
  split
  · next h => exact (supply t).budget i h k
  · rw [Polynomial.coeff_X]
    split <;> simp

/-- Per-coordinate root attribution in family form: the `assign`-feeder.  Any decode value
rooting in a live fiber of the coordinate interpolant roots in `weldFactorFamily supply t i`
for some index `i` that is moreover a genuine divisor of the interpolant. -/
theorem weldFactorFamily_attribution (supply : ∀ t, FactorBudgetSupply (Qc t) B)
    (t : Fin n) (γ y : F₀)
    (hfib : (Qc t).map (Polynomial.evalRingHom γ) ≠ 0)
    (hroot : ((Qc t).map (Polynomial.evalRingHom γ)).eval y = 0) :
    ∃ i : F₀[X][Y],
      ((weldFactorFamily supply t i).map (Polynomial.evalRingHom γ)).eval y = 0 ∧
        weldFactorFamily supply t i ∣ Qc t := by
  obtain ⟨Hp, hmem, hr⟩ := (supply t).attribution γ y hfib hroot
  refine ⟨Hp, ?_, ?_⟩ <;> rw [weldFactorFamily_eq_of_mem supply hmem]
  · exact hr
  · exact (supply t).dvd Hp hmem

/-! ## The capstone existence theorem -/

/-- **The budget supply instantiation (capstone).**  From a per-coordinate interpolant
family `Qc : Fin n → F₀[X][Y]`, nonzero with a flat coefficient budget `B`, the weld inputs
exist: a factor family `Hf` over the uniform index type `ι := F₀[X][Y]` that is totally
irreducible (`hirr`), totally budgeted (`hB`), and attributes every live-fiber root to a
divisor factor — the data feeding `assign`/`hroot` of
`coordinateUpgrade_of_assigned_factor_rich`.  (The richness data `hrich`/`hwit` is NOT
produced here; that is the assignment-coherence residual.) -/
theorem exists_weldFactorInputs (Qc : Fin n → F₀[X][Y]) {B : ℕ}
    (hQ0 : ∀ t, Qc t ≠ 0) (hB : ∀ t (b : ℕ), ((Qc t).coeff b).natDegree ≤ B) :
    ∃ Hf : Fin n → F₀[X][Y] → F₀[X][Y],
      (∀ t (i : F₀[X][Y]), Irreducible (Hf t i)) ∧
      (∀ t (i : F₀[X][Y]) (k : ℕ), ((Hf t i).coeff k).natDegree ≤ B) ∧
      (∀ t (γ y : F₀), (Qc t).map (Polynomial.evalRingHom γ) ≠ 0 →
        ((Qc t).map (Polynomial.evalRingHom γ)).eval y = 0 →
        ∃ i : F₀[X][Y],
          ((Hf t i).map (Polynomial.evalRingHom γ)).eval y = 0 ∧ Hf t i ∣ Qc t) := by
  refine ⟨weldFactorFamily (fun t => factorBudgetSupply (Qc t) (hQ0 t) (hB t)),
    weldFactorFamily_irreducible _, weldFactorFamily_budget _,
    weldFactorFamily_attribution _⟩

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms factorBudgetIndex_card_le
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms factorBudgetIndex_irreducible
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms factorBudgetIndex_budget
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms factorBudgetIndex_attribution
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms factorBudgetSupply
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms weldFactorFamily_irreducible
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms weldFactorFamily_budget
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms weldFactorFamily_attribution
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms exists_weldFactorInputs
