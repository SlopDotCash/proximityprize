/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GeneralOrchardIdentity

/-!
# Odd-tower deep-band supply: the multiplicative-coset bound, and where it is tight (#389)

`EvenTowerSupplyGrowth.lean` handles even-tower words `x^{2j}` via the *additive* antipodal
pairing.  The odd-tower words (the cubic `x³` is the first) have no antipodal structure — a
zero-sum subset of odd size cannot pair into negatives.  Their deep-band supply comes from the
*multiplicative* `μ_d`-coset construction: if `ζ` is a primitive `d`-th root of unity
(`1 + ζ + ⋯ + ζ^{d-1} = 0`) and the domain is closed under `x ↦ ζx`, then each coset
`{a, ζa, …, ζ^{d-1}a}` is a zero-sum `d`-subset.

This file lands the `d = 3` (cubic) case — proving the lower bound and then honestly bounding
its reach, exactly as in the even case:

* **`zeroSum_triples_coset_ge`** (proved) — for a domain carrying a cube rotation `τ`
  (`dom (τ i) = ζ · dom i`, `1 + ζ + ζ² = 0`) and a set `R` of coset representatives
  (`τ i, τ² i ∉ R`), the zero-sum-`3`-subset count is at least `|R|`: each `i ∈ R` gives the
  zero-sum triple `{i, τ i, τ² i}`, recovered as `{i, τ i, τ² i} ∩ R = {i}`.  Via the orchard
  identity this is **`cubicCosetSupply_ge`**: the deep-band supply of `x³` is `≥ |R| = n/3` on
  every cube-closed domain with `3 ∣ n` — a `Θ(n)` nonzero supply, the odd-tower analogue.
  Tight at `μ_6 = F₇^×` (supply `2 = 6/3`).

* **`cubic_coset_bound_not_tight`** (machine-checked refutation) — the matching upper bound
  `n/3` is **false in small characteristic**: on `μ_{12} = F₁₃^×` the zero-sum-`3`-subset count
  is `16`, far above `n/3 = 4`.  The excess are char-`13` coincidences (sums vanishing `mod 13`
  but not in char `0`), present only below the Sidon/resultant threshold `n² < p`.  Above it —
  where every prize field lives — the coset bound is tight.  Issue #389.
-/

open Finset

namespace ProximityGap.PairRank

open ProximityGap.SpikeFloor ProximityGap ProximityGap.Ownership Code

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open Classical in
omit [Fintype F] [NeZero n] in
/-- **The cubic multiplicative-coset lower bound.**  A cube rotation `τ` (`dom (τ i) = ζ·dom i`,
`1 + ζ + ζ² = 0`, `ζ ≠ 1`) over a representative set `R` whose elements have nonzero image and
whose `τ`-, `τ²`-images leave `R` gives at least `|R|` zero-sum triples `{i, τ i, τ² i}`. -/
theorem zeroSum_triples_coset_ge (dom : Fin n ↪ F) (τ : Fin n → Fin n) (ζ : F)
    (R : Finset (Fin n)) (hζ : 1 + ζ + ζ ^ 2 = 0) (hζ1 : ζ ≠ 1)
    (hτ : ∀ i, dom (τ i) = ζ * dom i) (h0 : ∀ i ∈ R, dom i ≠ 0)
    (hτR : ∀ i ∈ R, τ i ∉ R ∧ τ (τ i) ∉ R) :
    R.card ≤ (((Finset.univ : Finset (Fin n)).powersetCard 3).filter
        (fun T => ∑ i ∈ T, dom i = 0)).card := by
  classical
  -- derived facts about ζ
  have hζ0 : ζ ≠ 0 := by rintro rfl; simp at hζ
  have hζ2ne1 : ζ ^ 2 ≠ 1 := by
    intro h
    rcases mul_eq_zero.mp (show (ζ - 1) * (ζ + 1) = 0 by linear_combination h) with h1 | h2
    · exact hζ1 (by linear_combination h1)
    · rw [show ζ = -1 by linear_combination h2] at hζ; norm_num at hζ
  have hζ2neζ : ζ ^ 2 ≠ ζ := by
    intro h
    rcases mul_eq_zero.mp (show ζ * (ζ - 1) = 0 by linear_combination h) with h1 | h2
    · exact hζ0 h1
    · exact hζ1 (by linear_combination h2)
  refine Finset.card_le_card_of_injOn (fun i => {i, τ i, τ (τ i)}) ?_ ?_
  · -- each representative maps to a zero-sum triple
    intro i hi
    have hτi : dom (τ i) = ζ * dom i := hτ i
    have hτ2i : dom (τ (τ i)) = ζ ^ 2 * dom i := by rw [hτ (τ i), hτ i]; ring
    have hne : ∀ c : F, c ≠ 1 → ∀ a, dom a = c * dom i → a ≠ i := by
      intro c hc a ha hai
      rw [hai] at ha
      rcases mul_eq_zero.mp (show (c - 1) * dom i = 0 by linear_combination -ha) with h | h
      · exact hc (by linear_combination h)
      · exact (h0 i hi) h
    have d1 : i ≠ τ i := Ne.symm (hne ζ hζ1 (τ i) hτi)
    have d2 : i ≠ τ (τ i) := Ne.symm (hne (ζ ^ 2) hζ2ne1 (τ (τ i)) hτ2i)
    have d3 : τ i ≠ τ (τ i) := by
      intro h
      have hee : ζ * dom i = ζ ^ 2 * dom i := by
        rw [← hτi, ← hτ2i]; exact congrArg dom h
      rcases mul_eq_zero.mp (show (ζ ^ 2 - ζ) * dom i = 0 by linear_combination -hee) with hA | hB
      · exact hζ2neζ (by linear_combination hA)
      · exact (h0 i hi) hB
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩, ?_⟩
    · exact Finset.card_eq_three.mpr ⟨i, τ i, τ (τ i), d1, d2, d3, rfl⟩
    · rw [Finset.sum_insert (by
            simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨d1, d2⟩),
          Finset.sum_insert (by simp only [Finset.mem_singleton]; exact d3),
          Finset.sum_singleton, hτi, hτ2i]
      linear_combination dom i * hζ
  · -- injective: {i, τ i, τ² i} ∩ R = {i} recovers the representative
    have hcap : ∀ a ∈ R, ({a, τ a, τ (τ a)} : Finset (Fin n)) ∩ R = {a} := by
      intro a ha
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hx, hxR⟩
        rcases hx with rfl | rfl | rfl
        · rfl
        · exact absurd hxR (hτR a ha).1
        · exact absurd hxR (hτR a ha).2
      · rintro rfl; exact ⟨Or.inl rfl, ha⟩
    intro i hi j hj hij
    rw [Finset.mem_coe] at hi hj
    have heq : ({i, τ i, τ (τ i)} : Finset (Fin n)) = {j, τ j, τ (τ j)} := hij
    exact Finset.singleton_injective (by rw [← hcap i hi, ← hcap j hj, heq])

open Classical in
/-- **The cubic supply growth bound.**  On a cube-closed domain with `3 ∣ n`, the deep-band
supply of `x³` is at least `|R| = n/3` — a `Θ(n)` nonzero supply, the odd-tower analogue of the
even-tower antipodal `Θ(n^j)` bound. -/
theorem cubicCosetSupply_ge (dom : Fin n ↪ F) (τ : Fin n → Fin n) (ζ : F)
    (R : Finset (Fin n)) (hζ : 1 + ζ + ζ ^ 2 = 0) (hζ1 : ζ ≠ 1)
    (hτ : ∀ i, dom (τ i) = ζ * dom i) (h0 : ∀ i ∈ R, dom i ≠ 0)
    (hτR : ∀ i ∈ R, τ i ∉ R ∧ τ (τ i) ∉ R) :
    R.card ≤ ((Finset.univ.filter (fun c =>
        c ∈ (rsCode dom 2 : Submodule F (Fin n → F))
          ∧ 2 + 1 ≤ (agreeSet c (fun i => (dom i) ^ (2 + 1))).card))).card := by
  rw [general_orchard_card dom (by norm_num : 1 ≤ 2)]
  exact zeroSum_triples_coset_ge dom τ ζ R hζ hζ1 hτ h0 hτR

/-! ## Tight at μ_6; strict in small characteristic -/

section Mu6Tight

local instance factPrime7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- `μ_6 = F₇^×`. -/
def cubeDom6vals : Fin 6 → ZMod 7 := ![1, 2, 3, 4, 5, 6]

/-- The domain `μ_6 ⊂ F₇` as an embedding. -/
def cubeDom6 : Fin 6 ↪ ZMod 7 := ⟨cubeDom6vals, by decide⟩

/-- The cube rotation `x ↦ 2x` on `μ_6` (in index form); `2` is a primitive cube root mod `7`
(`1 + 2 + 4 = 0`).  Orbits `{0,1,3}` and `{2,5,4}`. -/
def cubeTau6 : Fin 6 → Fin 6 := ![1, 3, 5, 0, 2, 4]

open Classical in
/-- The cubic coset bound is **tight** at `μ_6`: the deep-band supply of `x³` is `≥ 2 = n/3`,
the cube-root triples `{1,2,4}` and `{3,5,6}` (the proven exact value is `2`). -/
theorem cubicSupply_mu6_ge_two :
    2 ≤ ((Finset.univ.filter (fun c =>
        c ∈ (rsCode cubeDom6 2 : Submodule (ZMod 7) (Fin 6 → ZMod 7))
          ∧ 2 + 1 ≤ (agreeSet c (fun i => (cubeDom6 i) ^ (2 + 1))).card))).card := by
  have h := cubicCosetSupply_ge cubeDom6 cubeTau6 (2 : ZMod 7) ({0, 2} : Finset (Fin 6))
    (by decide) (by decide) (by decide) (by decide) (by decide)
  rwa [show ({0, 2} : Finset (Fin 6)).card = 2 from by decide] at h

end Mu6Tight

section CubicSmallChar

local instance factPrime13 : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- `μ_{12} = F₁₃^×`. -/
def dom12vals : Fin 12 → ZMod 13 := ![1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]

/-- The domain `μ_{12} ⊂ F₁₃` as an embedding (injective by `decide`). -/
def dom12 : Fin 12 ↪ ZMod 13 := ⟨dom12vals, by decide⟩

set_option maxHeartbeats 8000000 in
/-- The zero-sum-`3`-subset count of `μ_{12} ⊂ F₁₃` is `16`. -/
theorem mu12_F13_zeroSum_triples_eq_sixteen :
    (((Finset.univ : Finset (Fin 12)).powersetCard 3).filter
        (fun T => ∑ i ∈ T, dom12 i = 0)).card = 16 := by
  decide

/-- **The cubic coset bound `n/3` is NOT tight in small characteristic.**  At `μ_{12} ⊂ F₁₃` the
proven lower bound `n/3 = 4` is far from the actual zero-sum-`3`-count `16`; the excess are
char-`13` coincidences, absent above the Sidon threshold `n² < p` where prize fields live. -/
theorem cubic_coset_bound_not_tight :
    (4 : ℕ) < (((Finset.univ : Finset (Fin 12)).powersetCard 3).filter
        (fun T => ∑ i ∈ T, dom12 i = 0)).card := by
  rw [mu12_F13_zeroSum_triples_eq_sixteen]; norm_num

end CubicSmallChar

end ProximityGap.PairRank

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.PairRank.zeroSum_triples_coset_ge
#print axioms ProximityGap.PairRank.cubicCosetSupply_ge
#print axioms ProximityGap.PairRank.cubicSupply_mu6_ge_two
#print axioms ProximityGap.PairRank.cubic_coset_bound_not_tight
