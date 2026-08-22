/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R321ShadowAutocorrelationDoubling

/-!
# LANE B2 (#466 round 330): the zero shadow mode dominates every relation mass

R321 identifies the mass carried by a realized kernel relation `d` with the doubled-depth
characteristic-zero histogram coefficient `NR(2m,m,2r,d)`.  This file proves the missing
pointwise estimate

```text
NR(2m,m,2r,d) <= NR(2m,m,2r,0).
```

The proof is the elementary positive-definiteness argument for a symmetric random walk,
written without Fourier analysis.  At depth `r`, pairs with difference `d` form a matching
between shadow keys.  Apply `2ab <= a^2+b^2` on every matched edge; each endpoint occurs at
most once.  At `d=0` the matching is the diagonal, whose weight is exactly the sum of squares.

Consequently the per-relation mass obligation in R314 is discharged unconditionally:

```text
shadowCollisionMass
  <= card(shadowKernelRelations) * NR(2m,m,2r,0).
```

This discharges the per-relation estimate in the **uncentered** R314 split.  It is not by itself
a prize closure: the corrected prize target subtracts the mandatory DC mass `n^(2r)`, whereas
the uniform zero-mode cap does not.  The final theorem below quantifies the resulting loss: the
DC floor forces `(card relations + 1) * shadowEnergy` to be at least `n^(2r)/q`.  Thus R330 is
a useful universal cap and a rigorous delimiter; a winning fixed-prime proof still needs the
length-stratified R322 envelope or an equally sharp centered estimate.
Issue #466, round 330.  Axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R330ZeroModeDominatesShadowRelations

open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor
open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.R310ShadowFloorToRFoldEnergy
open ArkLib.ProximityGap.Frontier.R312ShadowCollisionMassIdentity
open ArkLib.ProximityGap.Frontier.R313LocalShadowCollisionLoad
open ArkLib.ProximityGap.Frontier.R314KernelRelationMassDecomposition
open ArkLib.ProximityGap.Frontier.R321ShadowAutocorrelationDoubling
open ArkLib.ProximityGap.Frontier.R240GeneralRFoldVariance
open ArkLib.ProximityGap.SubgroupGaussSumMoment

/-- A shadow difference vanishes exactly on the diagonal. -/
theorem shadowDifference_eq_zero_iff {m : ℕ}
    (p : (Fin m → ℤ) × (Fin m → ℤ)) :
    shadowDifference p = 0 ↔ p.2 = p.1 := by
  constructor
  · intro h
    funext j
    have hj := congrFun h j
    simpa [shadowDifference] using sub_eq_zero.mp hj
  · intro h
    funext j
    simp [shadowDifference, h]

/-- In a fixed nonzero-difference fiber, the left projection is injective. -/
theorem shadowDifferenceFiber_fst_injective {m : ℕ} {d : Fin m → ℤ}
    {p q : (Fin m → ℤ) × (Fin m → ℤ)}
    (hp : shadowDifference p = d) (hq : shadowDifference q = d)
    (hfst : p.1 = q.1) : p = q := by
  apply Prod.ext hfst
  funext j
  have hpj := congrFun hp j
  have hqj := congrFun hq j
  have hfstj := congrFun hfst j
  simp only [shadowDifference] at hpj hqj
  omega

/-- In a fixed difference fiber, the right projection is injective. -/
theorem shadowDifferenceFiber_snd_injective {m : ℕ} {d : Fin m → ℤ}
    {p q : (Fin m → ℤ) × (Fin m → ℤ)}
    (hp : shadowDifference p = d) (hq : shadowDifference q = d)
    (hsnd : p.2 = q.2) : p = q := by
  apply Prod.ext
  · funext j
    have hpj := congrFun hp j
    have hqj := congrFun hq j
    have hsndj := congrFun hsnd j
    simp only [shadowDifference] at hpj hqj
    omega
  · exact hsnd

/-- Weighted difference fibers of a finite set are maximal at zero.  This is the finite
positive-definiteness/Cauchy--Schwarz fact needed by the shadow histogram, proved by AM--GM
on the matching cut out by a fixed difference. -/
theorem weighted_difference_sum_le_zero {m : ℕ}
    (S : Finset (Fin m → ℤ)) (f : (Fin m → ℤ) → ℕ) (d : Fin m → ℤ) :
    ∑ p ∈ (S ×ˢ S).filter (fun p ↦ shadowDifference p = d), f p.1 * f p.2
      ≤ ∑ v ∈ S, (f v) ^ 2 := by
  classical
  let P := (S ×ˢ S).filter (fun p ↦ shadowDifference p = d)
  let L := P.image Prod.fst
  let R := P.image Prod.snd
  have hLsub : L ⊆ S := by
    intro v hv
    change v ∈ P.image Prod.fst at hv
    rw [Finset.mem_image] at hv
    obtain ⟨p, hp, rfl⟩ := hv
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  have hRsub : R ⊆ S := by
    intro v hv
    change v ∈ P.image Prod.snd at hv
    rw [Finset.mem_image] at hv
    obtain ⟨p, hp, rfl⟩ := hv
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2
  have hleft : ∑ p ∈ P, (f p.1) ^ 2 ≤ ∑ v ∈ S, (f v) ^ 2 := by
    calc
      (∑ p ∈ P, (f p.1) ^ 2) = ∑ v ∈ L, (f v) ^ 2 := by
        refine Finset.sum_bij (fun p _ ↦ p.1) ?_ ?_ ?_ (fun _ _ ↦ rfl)
        · intro p hp
          exact Finset.mem_image_of_mem Prod.fst hp
        · intro p hp q hq hpq
          exact shadowDifferenceFiber_fst_injective
            (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2 hpq
        · intro v hv
          change v ∈ P.image Prod.fst at hv
          rw [Finset.mem_image] at hv
          obtain ⟨p, hp, hpv⟩ := hv
          exact ⟨p, hp, hpv⟩
      _ ≤ ∑ v ∈ S, (f v) ^ 2 := Finset.sum_le_sum_of_subset hLsub
  have hright : ∑ p ∈ P, (f p.2) ^ 2 ≤ ∑ v ∈ S, (f v) ^ 2 := by
    calc
      (∑ p ∈ P, (f p.2) ^ 2) = ∑ v ∈ R, (f v) ^ 2 := by
        refine Finset.sum_bij (fun p _ ↦ p.2) ?_ ?_ ?_ (fun _ _ ↦ rfl)
        · intro p hp
          exact Finset.mem_image_of_mem Prod.snd hp
        · intro p hp q hq hpq
          exact shadowDifferenceFiber_snd_injective
            (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2 hpq
        · intro v hv
          change v ∈ P.image Prod.snd at hv
          rw [Finset.mem_image] at hv
          obtain ⟨p, hp, hpv⟩ := hv
          exact ⟨p, hp, hpv⟩
      _ ≤ ∑ v ∈ S, (f v) ^ 2 := Finset.sum_le_sum_of_subset hRsub
  have hedge :
      2 * (∑ p ∈ P, f p.1 * f p.2)
        ≤ (∑ p ∈ P, (f p.1) ^ 2) + ∑ p ∈ P, (f p.2) ^ 2 := by
    calc
      2 * (∑ p ∈ P, f p.1 * f p.2)
          = ∑ p ∈ P, 2 * (f p.1 * f p.2) := by rw [Finset.mul_sum]
      _ ≤ ∑ p ∈ P, ((f p.1) ^ 2 + (f p.2) ^ 2) := by
        exact Finset.sum_le_sum fun p _ ↦ by
          have h := two_mul_le_add_sq (f p.1 : ℤ) (f p.2 : ℤ)
          have hn : 2 * f p.1 * f p.2 ≤ (f p.1) ^ 2 + (f p.2) ^ 2 := by
            exact_mod_cast h
          simpa only [mul_assoc] using hn
      _ = (∑ p ∈ P, (f p.1) ^ 2) + ∑ p ∈ P, (f p.2) ^ 2 := by
        rw [Finset.sum_add_distrib]
  change ∑ p ∈ P, f p.1 * f p.2 ≤ _
  omega

/-- The zero difference fiber is exactly the squared `L2` mass of the weights. -/
theorem weighted_zero_difference_sum_eq_sq {m : ℕ}
    (S : Finset (Fin m → ℤ)) (f : (Fin m → ℤ) → ℕ) :
    ∑ p ∈ (S ×ˢ S).filter (fun p ↦ shadowDifference p = 0), f p.1 * f p.2
      = ∑ v ∈ S, (f v) ^ 2 := by
  classical
  have hset : (S ×ˢ S).filter (fun p ↦ shadowDifference p = 0) = S.diag := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_diag]
    constructor
    · rintro ⟨⟨hp1, hp2⟩, hdiff⟩
      have heq := shadowDifference_eq_zero_iff p |>.mp hdiff
      exact ⟨hp1, heq.symm⟩
    · rintro ⟨hp1, hp⟩
      refine ⟨⟨hp1, hp ▸ hp1⟩, ?_⟩
      exact shadowDifference_eq_zero_iff p |>.mpr hp.symm
  rw [hset, Finset.sum_diag]
  exact Finset.sum_congr rfl fun v _ ↦ (pow_two (f v)).symm

/-- **ZERO-MODE MAXIMUM.**  Every doubled-depth signed-basis histogram coefficient is at
most the return coefficient. -/
theorem NR_double_le_zero (m r : ℕ) (d : Fin m → ℤ) :
    NR (2 * m) m (r + r) d ≤ NR (2 * m) m (r + r) 0 := by
  rw [← tuplePairDifferenceCount_eq_NR, tuplePairDifferenceCount_eq_sum_keyPairs]
  rw [← tuplePairDifferenceCount_eq_NR, tuplePairDifferenceCount_eq_sum_keyPairs]
  calc
    (∑ p ∈ ((keysR (2 * m) m r) ×ˢ (keysR (2 * m) m r)).filter
        (fun p ↦ shadowDifference p = d),
        NR (2 * m) m r p.1 * NR (2 * m) m r p.2)
      ≤ ∑ v ∈ keysR (2 * m) m r, (NR (2 * m) m r v) ^ 2 :=
        weighted_difference_sum_le_zero (keysR (2 * m) m r) (NR (2 * m) m r) d
    _ = ∑ p ∈ ((keysR (2 * m) m r) ×ˢ (keysR (2 * m) m r)).filter
        (fun p ↦ shadowDifference p = 0),
        NR (2 * m) m r p.1 * NR (2 * m) m r p.2 :=
          (weighted_zero_difference_sum_eq_sq
            (keysR (2 * m) m r) (NR (2 * m) m r)).symm

/-- The doubled-depth return coefficient is exactly the full depth-`r` shadow energy. -/
theorem NR_double_zero_eq_shadowEnergy (m r : ℕ) :
    NR (2 * m) m (r + r) 0 = shadowEnergy (2 * m) m r := by
  rw [← tuplePairDifferenceCount_eq_NR, tuplePairDifferenceCount_eq_sum_keyPairs]
  rw [weighted_zero_difference_sum_eq_sq]
  rfl

/-- Every realized relation carries at most the zero-mode doubled-depth mass. -/
theorem shadowRelationMass_le_NR_double_zero
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r : ℕ) {d : Fin m → ℤ}
    (hd : d ∈ shadowKernelRelations g (2 * m) m r) :
    shadowRelationMass g (2 * m) m r d ≤ NR (2 * m) m (r + r) 0 := by
  rw [shadowRelationMass_eq_NR_double g m r hd]
  exact NR_double_le_zero m r d

/-- Field-facing form: a realized relation carries at most the whole characteristic-zero
depth-`r` energy. -/
theorem shadowRelationMass_le_shadowEnergy
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r : ℕ) {d : Fin m → ℤ}
    (hd : d ∈ shadowKernelRelations g (2 * m) m r) :
    shadowRelationMass g (2 * m) m r d ≤ shadowEnergy (2 * m) m r := by
  rw [← NR_double_zero_eq_shadowEnergy]
  exact shadowRelationMass_le_NR_double_zero g m r hd

/-- **COUNT-ONLY COLLISION BOUND.**  The full wraparound surplus is controlled by the
number of realized kernel relations times one explicit characteristic-zero return count. -/
theorem shadowCollisionMass_le_relation_card_mul_NR_zero
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r : ℕ) :
    shadowCollisionMass g (2 * m) m r
      ≤ (shadowKernelRelations g (2 * m) m r).card * NR (2 * m) m (r + r) 0 := by
  exact shadowCollisionMass_le_relation_count_mul g (2 * m) m r
    (shadowKernelRelations g (2 * m) m r).card (NR (2 * m) m (r + r) 0)
    le_rfl (fun d hd ↦ shadowRelationMass_le_NR_double_zero g m r hd)

/-- Equivalent clean endpoint: collision mass is at most relation count times shadow energy. -/
theorem shadowCollisionMass_le_relation_card_mul_shadowEnergy
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r : ℕ) :
    shadowCollisionMass g (2 * m) m r
      ≤ (shadowKernelRelations g (2 * m) m r).card * shadowEnergy (2 * m) m r := by
  rw [← NR_double_zero_eq_shadowEnergy]
  exact shadowCollisionMass_le_relation_card_mul_NR_zero g m r

/-- Exact-order power-root consumer: counting realized kernel relations is now enough to
bound the full field-level energy. -/
theorem rEnergy_powerRootSet_le_shadowEnergy_add_relation_card_mul_NR_zero
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r : ℕ) (hg0 : g ≠ 0) (hord : orderOf g = 2 * m)
    (hm : 0 < m) (hg : g ^ m = -1) :
    rEnergy (powerRootSet g (2 * m)) r
      ≤ shadowEnergy (2 * m) m r
        + (shadowKernelRelations g (2 * m) m r).card * NR (2 * m) m (r + r) 0 := by
  rw [rEnergy_powerRootSet_eq_shadowEnergy_add_collisionMass_of_orderOf
    g (2 * m) m r hg0 hord hm rfl hg]
  exact Nat.add_le_add_left (shadowCollisionMass_le_relation_card_mul_NR_zero g m r) _

/-- **MULTIPLICATIVE COUNT-ONLY ENDPOINT.**  The field energy is at most one plus the
number of realized nonzero relations times its characteristic-zero counterpart. -/
theorem rEnergy_powerRootSet_le_relation_card_succ_mul_shadowEnergy
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r : ℕ) (hg0 : g ≠ 0) (hord : orderOf g = 2 * m)
    (hm : 0 < m) (hg : g ^ m = -1) :
    rEnergy (powerRootSet g (2 * m)) r
      ≤ ((shadowKernelRelations g (2 * m) m r).card + 1) * shadowEnergy (2 * m) m r := by
  rw [rEnergy_powerRootSet_eq_shadowEnergy_add_collisionMass_of_orderOf
    g (2 * m) m r hg0 hord hm rfl hg]
  calc
    shadowEnergy (2 * m) m r + shadowCollisionMass g (2 * m) m r
        ≤ shadowEnergy (2 * m) m r
          + (shadowKernelRelations g (2 * m) m r).card * shadowEnergy (2 * m) m r :=
            Nat.add_le_add_left
              (shadowCollisionMass_le_relation_card_mul_shadowEnergy g m r) _
    _ = ((shadowKernelRelations g (2 * m) m r).card + 1)
          * shadowEnergy (2 * m) m r := by ring

/-- Exact order makes the first `n` powers a set of cardinality `n`. -/
theorem powerRootSet_card_of_orderOf
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (n : ℕ) (hg0 : g ≠ 0) (hord : orderOf g = n) :
    (powerRootSet g n).card = n := by
  classical
  unfold powerRootSet
  rw [Finset.card_image_of_injective _
    (power_index_injective_of_orderOf g n hg0 hord), Finset.card_univ, Fintype.card_fin]

/-- **DC-FLOOR DELIMITER FOR THE COUNT-ONLY ROUTE.**  The field-level DC floor and the
zero-mode upper bound force the relation-count factor to carry at least the uniform mass.
In particular, a prize argument cannot simply prove that the raw number of relations is
small; it must retain relation-length weights or the centered subtraction. -/
theorem dc_floor_le_relation_card_succ_mul_shadowEnergy
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r : ℕ) (hg0 : g ≠ 0) (hord : orderOf g = 2 * m)
    (hm : 0 < m) (hg : g ^ m = -1) :
    ((2 * m : ℕ) : ℝ) ^ (2 * r)
      ≤ (Fintype.card F : ℝ)
        * ((((shadowKernelRelations g (2 * m) m r).card + 1)
            * shadowEnergy (2 * m) m r : ℕ) : ℝ) := by
  have hfloor := dc_floor (powerRootSet g (2 * m)) r
  rw [powerRootSet_card_of_orderOf g (2 * m) hg0 hord] at hfloor
  have hupperNat := rEnergy_powerRootSet_le_relation_card_succ_mul_shadowEnergy
    g m r hg0 hord hm hg
  have hupper : (rEnergy (powerRootSet g (2 * m)) r : ℝ)
      ≤ ((((shadowKernelRelations g (2 * m) m r).card + 1)
          * shadowEnergy (2 * m) m r : ℕ) : ℝ) := by
    exact_mod_cast hupperNat
  exact hfloor.trans
    (mul_le_mul_of_nonneg_left hupper (by positivity))

end ArkLib.ProximityGap.Frontier.R330ZeroModeDominatesShadowRelations

/-! ## Axiom audit (must contain no `sorryAx`) -/
#print axioms
  ArkLib.ProximityGap.Frontier.R330ZeroModeDominatesShadowRelations.weighted_difference_sum_le_zero
#print axioms
  ArkLib.ProximityGap.Frontier.R330ZeroModeDominatesShadowRelations.NR_double_le_zero
#print axioms
  ArkLib.ProximityGap.Frontier.R330ZeroModeDominatesShadowRelations.NR_double_zero_eq_shadowEnergy
#print axioms
  ArkLib.ProximityGap.Frontier.R330ZeroModeDominatesShadowRelations.shadowRelationMass_le_NR_double_zero
#print axioms
  ArkLib.ProximityGap.Frontier.R330ZeroModeDominatesShadowRelations.shadowCollisionMass_le_relation_card_mul_NR_zero
#print axioms
  ArkLib.ProximityGap.Frontier.R330ZeroModeDominatesShadowRelations.rEnergy_powerRootSet_le_shadowEnergy_add_relation_card_mul_NR_zero
#print axioms
  ArkLib.ProximityGap.Frontier.R330ZeroModeDominatesShadowRelations.rEnergy_powerRootSet_le_relation_card_succ_mul_shadowEnergy
#print axioms
  ArkLib.ProximityGap.Frontier.R330ZeroModeDominatesShadowRelations.dc_floor_le_relation_card_succ_mul_shadowEnergy
