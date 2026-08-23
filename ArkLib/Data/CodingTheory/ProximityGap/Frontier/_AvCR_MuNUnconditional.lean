/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvCR_CharZeroSelfContained
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvF1_BesselMfoldSymbolic
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvX_PrimitiveTwoPowRootHalfPowerEq

/-!
# The char-0 Wick bound, LITERALLY unconditional for `μ_n = nthRootsFinset (2^μ)` (#444, avenue CR)

This brick instantiates the abstract self-contained capstone `charZeroWick_selfContained` at the
GENUINE `μ_n` family: the `m = 2^{μ-1}` antipodal directions `{ζ^j, −ζ^j}` of a primitive
`2^μ`-th root `ζ` in a characteristic-`0` field. It proves the **cover lemma**
`unionUpto D m = nthRootsFinset (2^μ) 1` (the `m` antipodal pairs exactly tile the `2^μ`-th roots,
using `ζ^m = ζ^{2^{μ-1}} = -1`), discharges the three capstone hypotheses (`hw`, `hD`, `hdisj`,
`hroot`) directly from primitivity, and composes the final, hypothesis-free theorem

  `charZero_wick_muN : zeroSumCount (nthRootsFinset (2^μ) 1) (2r) ≤ (2r−1)‼·(2^μ)^r`.

So `E_r^{char0}(μ_n) ≤ (2r−1)‼·n^r` with `n = 2^μ` is now LITERALLY unconditional and
self-contained — no named hypothesis, no `sorry`, no `native_decide`.

## Honest scope (#444)

This is the **char-0 layer ONLY**, NOT prize closure. Over `𝔽_p` the identity
`E_r^{𝔽_p} = E_r^{char0} + W_r` carries a wraparound excess `W_r` positive once `r ≥ r₀(n)`
(`r₀ ≈ ln p` at prize scale); the prize lives at the moment-saddle `r ≈ ln p` where `W_r > 0`,
the BGK wall, untouched here.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`, no `native_decide`.
-/

set_option linter.style.longLine false
set_option autoImplicit false

open Finset Polynomial
open scoped Nat
open ArkLib.ProximityGap.NegationClosedWalk
open ArkLib.ProximityGap.Frontier.AvF1
open ArkLib.ProximityGap.Frontier.AvCRSelfContained
open ArkLib.ProximityGap.Frontier (PrimitiveTwoPowRootHalfPowerEqNegOne)

namespace ArkLib.ProximityGap.Frontier.AvCRMuN

variable {F : Type*} [Field F] [DecidableEq F]

/-- The `μ_n` antipodal-direction family: `D j = {ζ^j, −ζ^j}` for `j < m = 2^{μ-1}`. -/
noncomputable def muD (ζ : F) (μ : ℕ) : Fin (2 ^ (μ - 1)) → Finset F :=
  fun j => antiPair (ζ ^ (j : ℕ))

/-- The per-direction generator `w j = ζ^j`. -/
noncomputable def muW (ζ : F) (μ : ℕ) : Fin (2 ^ (μ - 1)) → F :=
  fun j => ζ ^ (j : ℕ)

/-! ## The `unionUpto` of the antipodal directions: membership characterization. -/

/-- Membership in the union of the first `k` antipodal directions of `μ_n`:
`x ∈ unionUpto (muD ζ μ) k ↔ ∃ j < k, x = ζ^j ∨ x = −ζ^j`. -/
theorem mem_unionUpto_muD (μ : ℕ) {ζ : F} (k : ℕ) (hk : k ≤ 2 ^ (μ - 1)) {x : F} :
    x ∈ unionUpto (muD ζ μ) k ↔ ∃ j < k, x = ζ ^ j ∨ x = -ζ ^ j := by
  induction k with
  | zero => simp [unionUpto]
  | succ k ih =>
    have hkm : k < 2 ^ (μ - 1) := by omega
    rw [unionUpto, dif_pos hkm]
    simp only [Finset.mem_union, ih (by omega), muD, mem_antiPair]
    constructor
    · rintro (⟨j, hj, hx⟩ | hx)
      · exact ⟨j, by omega, hx⟩
      · exact ⟨k, by omega, hx⟩
    · rintro ⟨j, hj, hx⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
      · exact Or.inl ⟨j, hj', hx⟩
      · exact Or.inr hx

/-! ## THE COVER LEMMA: the `m` antipodal pairs tile the `2^μ`-th roots exactly. -/

/-- **THE COVER LEMMA.** For a primitive `2^μ`-th root `ζ` (`μ ≥ 1`, `m = 2^{μ-1}`), the `m`
antipodal directions `{ζ^j, −ζ^j}_{j<m}` cover the `2^μ`-th roots of unity exactly:
`unionUpto (muD ζ μ) m = nthRootsFinset (2^μ) 1`. The key is `ζ^m = ζ^{2^{μ-1}} = −1`
(`PrimitiveTwoPowRootHalfPowerEqNegOne`), folding `−ζ^j = ζ^{j+m}` so the union is `{ζ^i : i < 2m}`,
which has `2m = 2^μ` distinct elements (power-injectivity), all `2^μ`-th roots, hence equal by card. -/
theorem cover_muD (μ : ℕ) (hμ : 1 ≤ μ) {ζ : F} (hζ : IsPrimitiveRoot ζ (2 ^ μ)) :
    unionUpto (muD ζ μ) (2 ^ (μ - 1)) = nthRootsFinset (2 ^ μ) (1 : F) := by
  set m := 2 ^ (μ - 1) with hm
  have htwo : 2 * m = 2 ^ μ := by
    rw [hm, ← pow_succ']; congr 1; omega
  have hpos : 0 < 2 ^ μ := by positivity
  -- ζ^m = -1
  have hhalf : ζ ^ m = -1 := by
    have hμeq : μ = (μ - 1) + 1 := by omega
    rw [hm, show μ - 1 = μ - 1 from rfl]
    have hζ' : IsPrimitiveRoot ζ (2 ^ ((μ - 1) + 1)) := by rwa [← hμeq]
    exact PrimitiveTwoPowRootHalfPowerEqNegOne hζ'
  -- the union equals the image of range (2m)
  have hneg : ∀ (e : ℕ), -ζ ^ e = ζ ^ (e + m) := by
    intro e; rw [pow_add, hhalf]; ring
  have himg : unionUpto (muD ζ μ) m = (Finset.range (2 * m)).image (fun i => ζ ^ i) := by
    ext x
    rw [mem_unionUpto_muD μ m (le_refl _), Finset.mem_image]
    simp only [Finset.mem_range]
    constructor
    · rintro ⟨j, hj, hx | hx⟩
      · exact ⟨j, by omega, hx.symm⟩
      · exact ⟨j + m, by omega, by rw [← hneg, hx]⟩
    · rintro ⟨i, hi, hx⟩
      by_cases hib : i < m
      · exact ⟨i, hib, Or.inl hx.symm⟩
      · refine ⟨i - m, by omega, Or.inr ?_⟩
        have hsplit : (i - m) + m = i := by omega
        rw [hneg, hsplit, hx]
  rw [himg]
  -- image ⊆ nthRootsFinset, and both have card 2^μ
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, _, hx⟩ := hx
    rw [mem_nthRootsFinset hpos]
    rw [← hx, ← pow_mul]
    have : i * 2 ^ μ = (2 ^ μ) * i := by ring
    rw [this, pow_mul, hζ.pow_eq_one, one_pow]
  · rw [hζ.card_nthRootsFinset]
    rw [Finset.card_image_of_injOn]
    · rw [Finset.card_range]; omega
    · rw [htwo]; exact hζ.injOn_pow

/-! ## THE FINAL THEOREM: the char-0 Wick bound, LITERALLY unconditional for `μ_n`. -/

/-- **THE FINAL THEOREM — char-0 Wick bound for `μ_n = nthRootsFinset (2^μ)`, hypothesis-free.**
For a primitive `2^μ`-th root `ζ` in a characteristic-`0` field (`μ ≥ 1`), the char-0 additive-energy
collision count of the `2^μ`-th roots of unity satisfies the Gaussian/Wick bound

  `E_r^{char0}(μ_n) = zeroSumCount (nthRootsFinset (2^μ) 1) (2r) ≤ (2r−1)‼·(2^μ)^r`   (`n = 2^μ`).

This is LITERALLY unconditional and self-contained: it instantiates the abstract capstone
`charZeroWick_selfContained` at the genuine `μ_n` antipodal family `D j = {ζ^j, −ζ^j}` and rewrites
through the cover lemma `cover_muD`. No named hypothesis, no `sorry`, no `native_decide`. -/
theorem charZero_wick_muN [CharZero F] {μ : ℕ} (hμ : 1 ≤ μ) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ μ)) (r : ℕ) :
    (zeroSumCount (nthRootsFinset (2 ^ μ) (1 : F)) (2 * r) : ℚ)
      ≤ ((2 * r - 1)‼ : ℚ) * ((2 ^ μ : ℕ) : ℚ) ^ r := by
  set m := 2 ^ (μ - 1) with hm
  have htwo : 2 * m = 2 ^ μ := by
    rw [hm, ← pow_succ']; congr 1; omega
  -- the half-period fact ζ^m = -1
  have hhalf : ζ ^ m = -1 := by
    have hμeq : μ = (μ - 1) + 1 := by omega
    have hζ' : IsPrimitiveRoot ζ (2 ^ ((μ - 1) + 1)) := by rwa [← hμeq]
    exact PrimitiveTwoPowRootHalfPowerEqNegOne hζ'
  have hζne : ζ ≠ 0 := hζ.ne_zero (by positivity)
  -- the capstone hypotheses for D = muD, w = muW
  have hw : ∀ j : Fin m, muW ζ μ j ≠ 0 := fun j => pow_ne_zero _ hζne
  have hD : ∀ j : Fin m, muD ζ μ j = antiPair (muW ζ μ j) := fun j => rfl
  -- disjointness: antiPair (ζ^i) ∩ antiPair (ζ^j) = ∅ for i ≠ j < m
  have hdisj : ∀ i j : Fin m, i ≠ j → Disjoint (muD ζ μ i) (muD ζ μ j) := by
    intro i j hij
    have hinm : (i : ℕ) < m := i.isLt
    have hjnm : (j : ℕ) < m := j.isLt
    have hijn : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    -- the pow-injectivity on exponents < 2^μ = 2m
    have hpi : ∀ a b : ℕ, a < 2 ^ μ → b < 2 ^ μ → ζ ^ a = ζ ^ b → a = b :=
      fun a b ha hb h => hζ.pow_inj ha hb h
    have hneg : ∀ (e : ℕ), -ζ ^ e = ζ ^ (e + m) := by
      intro e; rw [pow_add, hhalf]; ring
    rw [Finset.disjoint_left]
    intro x hxi hxj
    simp only [muD, mem_antiPair] at hxi hxj
    -- x = ζ^a with a ∈ {i, i+m}, a < 2^μ
    obtain ⟨a, ha_lt, ha_set, ha_eq⟩ :
        ∃ a, a < 2 ^ μ ∧ (a = (i : ℕ) ∨ a = (i : ℕ) + m) ∧ x = ζ ^ a := by
      rcases hxi with h | h
      · exact ⟨(i : ℕ), by omega, Or.inl rfl, h⟩
      · exact ⟨(i : ℕ) + m, by omega, Or.inr rfl, by rw [h, hneg]⟩
    obtain ⟨b, hb_lt, hb_set, hb_eq⟩ :
        ∃ b, b < 2 ^ μ ∧ (b = (j : ℕ) ∨ b = (j : ℕ) + m) ∧ x = ζ ^ b := by
      rcases hxj with h | h
      · exact ⟨(j : ℕ), by omega, Or.inl rfl, h⟩
      · exact ⟨(j : ℕ) + m, by omega, Or.inr rfl, by rw [h, hneg]⟩
    have hab : a = b := hpi a b ha_lt hb_lt (by rw [← ha_eq, ← hb_eq])
    rcases ha_set with rfl | rfl <;> rcases hb_set with hbb | hbb <;> omega
  -- root-of-unity property: every element of muD is a 2^μ-th root
  have hroot : ∀ (j : Fin m), ∀ x ∈ muD ζ μ j, x ^ (2 ^ μ) = 1 := by
    intro j x hx
    simp only [muD, mem_antiPair] at hx
    have hpow : (ζ ^ (j : ℕ)) ^ (2 ^ μ) = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    rcases hx with rfl | rfl
    · exact hpow
    · rw [neg_pow, hpow, mul_one]
      have heven : Even (2 ^ μ) := by
        rw [Nat.even_pow]; exact ⟨even_two, by omega⟩
      rw [Even.neg_one_pow heven]
  -- compose via the capstone, rewriting 2*m = 2^μ and the cover
  have hcap := charZeroWick_selfContained (k := μ) (m := m) (muD ζ μ) (muW ζ μ)
    hw hD hdisj (by intro j x hx; exact hroot j x hx) r
  rw [cover_muD μ hμ hζ] at hcap
  rw [hm] at htwo
  calc (zeroSumCount (nthRootsFinset (2 ^ μ) (1 : F)) (2 * r) : ℚ)
      ≤ ((2 * r - 1)‼ : ℚ) * ((2 * m : ℕ) : ℚ) ^ r := hcap
    _ = ((2 * r - 1)‼ : ℚ) * ((2 ^ μ : ℕ) : ℚ) ^ r := by rw [htwo]

#print axioms cover_muD
#print axioms charZero_wick_muN

end ArkLib.ProximityGap.Frontier.AvCRMuN
