/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26PolyFieldCeiling
import ArkLib.Data.CodingTheory.ProximityGap.KKH26FixedRResultantBound

/-!
# Tightened [KKH26] δ* ceiling — the `(2r)` collision-resultant bound (#334)

`kkh26_mcaDeltaStar_le_of_TZ` (`KKH26PolyFieldCeiling.lean`) feeds the **loose** collision
resultant bound `M = (2^μ)^{2^{μ−1}}` (`natAbs_collisionResultant_le`) into
the Thorner–Zaman good-prime budget.  But the **fixed-`r`** bound
`natAbs_collisionResultant_le_two_mul_r_pow` (`KKH26FixedRResultantBound.lean`)
already proves the sharper `|collisionResultant| ≤ (2r)^{2^{μ−1}}` -- and "do
not coarsen `2r` to `2^μ`".

This file wires that sharper bound through the *same* counting argument, giving a δ* ceiling
whose only-unproven input (`hcount`) is **strictly weaker**: the supply must merely exceed
`|collisionPairs μ r| · log((2r)^{2^{μ−1}}) / log(n^β)` instead of the coarse
`... log((2^μ)^{2^{μ−1}}) ...`.  For a rate-`ρ` evaluation code
`r = ρ·2^μ < 2^{μ−1}` this cuts the bad-prime budget by the factor
`log(2r)/log(2^μ) = (1 + log₂ r)/μ < 1`, relaxing the [TZ24] prime-supply
requirement the prize rows need.  No new analysis -- only the already-proven
sharper resultant bound, wired through the already-proven good-prime existence.
Issue #334.
-/

open Polynomial Finset
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.KKH26

/-- The logarithmic factor for the sharp `(2r)` resultant budget is nonnegative once `r > 0`
and the prime window starts at `n^β ≥ 2`. -/
lemma tightResultantLogRatio_nonneg {n : ℕ} {β : ℝ} (μ r : ℕ) (hr0 : 0 < r)
    (hx : 2 ≤ (n : ℝ) ^ β) :
    0 ≤
      Real.log (((2 * r) ^ 2 ^ (μ - 1) : ℕ) : ℝ) /
        Real.log ((n : ℝ) ^ β) := by
  have hMpos : 0 < ((2 * r) ^ 2 ^ (μ - 1) : ℕ) :=
    pow_pos (Nat.mul_pos (by norm_num) hr0) _
  have hMone : (1 : ℝ) ≤ (((2 * r) ^ 2 ^ (μ - 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hMpos
  have hnum : 0 ≤ Real.log (((2 * r) ^ 2 ^ (μ - 1) : ℕ) : ℝ) :=
    Real.log_nonneg hMone
  have hden : 0 < Real.log ((n : ℝ) ^ β) := Real.log_pos (by linarith)
  exact div_nonneg hnum hden.le

/-- **Good prime avoiding all collision resultants, with the sharp `(2r)` budget.**  Identical
to `kkh26_good_prime_avoids_collisions_of_TZ` except the bad-prime budget uses the fixed-`r`
bound `(2r)^{2^{μ−1}}` in place of the coarse `(2^μ)^{2^{μ−1}}`. -/
theorem kkh26_good_prime_avoids_collisions_of_TZ_tight {n : ℕ} {β : ℝ} {supply : ℕ}
    (hTZ : TZPrimeSupply n β supply) {μ r : ℕ} (hμ : 1 ≤ μ) (_hr : r ≤ 2 ^ (μ - 1))
    (hx : 2 ≤ (n : ℝ) ^ β)
    (hcount : ((collisionPairs μ r).card : ℝ) *
        (Real.log (((2 * r) ^ 2 ^ (μ - 1) : ℕ) : ℝ) / Real.log ((n : ℝ) ^ β))
      < (supply : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD n] ∧
      (n : ℝ) ^ β ≤ p ∧ (p : ℝ) ≤ 2 * (n : ℝ) ^ β ∧
      ∀ d₁ ∈ sigData (2 ^ (μ - 1)) r,
      ∀ d₂ ∈ sigData (2 ^ (μ - 1)) r, d₁ ≠ d₂ →
        ¬ (p : ℤ) ∣ collisionResultant μ d₁ d₂ := by
  classical
  obtain ⟨p, hp, hmod, hlb, hub, hgood⟩ :=
    kkh26_good_prime_of_TZ (M := (((2 * r) ^ 2 ^ (μ - 1) : ℕ) : ℝ)) hTZ
      (R := fun i : Fin (collisionPairs μ r).card =>
        collisionResultant μ ((collisionPairs μ r).equivFin.symm i).1.1
          ((collisionPairs μ r).equivFin.symm i).1.2)
      (fun i => by
        obtain ⟨h1, h2, h3⟩ :=
          mem_collisionPairs.mp ((collisionPairs μ r).equivFin.symm i).2
        exact collisionResultant_ne_zero hμ h1 h2 h3)
      (fun i => by
        obtain ⟨h1, h2, _⟩ :=
          mem_collisionPairs.mp ((collisionPairs μ r).equivFin.symm i).2
        exact_mod_cast natAbs_collisionResultant_le_two_mul_r_pow hμ h1 h2)
      hx hcount
  refine ⟨p, hp, hmod, hlb, hub, fun d₁ hd₁ d₂ hd₂ hne => ?_⟩
  have hq : (d₁, d₂) ∈ collisionPairs μ r := mem_collisionPairs.mpr ⟨hd₁, hd₂, hne⟩
  have h := hgood ((collisionPairs μ r).equivFin ⟨(d₁, d₂), hq⟩)
  rwa [Equiv.symm_apply_apply] at h

/-- **Square-budget version of the sharp `(2r)` good-prime step.**  This consumes the familiar
`(2^r * C(2^(μ-1), r))^2` collision-family upper bound while keeping the sharper fixed-`r`
resultant-size logarithm. -/
theorem kkh26_good_prime_avoids_collisions_of_TZ_tight_square_bound {n : ℕ} {β : ℝ}
    {supply : ℕ} (hTZ : TZPrimeSupply n β supply) {μ r : ℕ}
    (hμ : 1 ≤ μ) (hr0 : 0 < r) (hr : r ≤ 2 ^ (μ - 1))
    (hx : 2 ≤ (n : ℝ) ^ β)
    (hcount : (((2 ^ r * (2 ^ (μ - 1)).choose r) ^ 2 : ℕ) : ℝ) *
        (Real.log (((2 * r) ^ 2 ^ (μ - 1) : ℕ) : ℝ) / Real.log ((n : ℝ) ^ β))
      < (supply : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD n] ∧
      (n : ℝ) ^ β ≤ p ∧ (p : ℝ) ≤ 2 * (n : ℝ) ^ β ∧
      ∀ d₁ ∈ sigData (2 ^ (μ - 1)) r,
      ∀ d₂ ∈ sigData (2 ^ (μ - 1)) r, d₁ ≠ d₂ →
        ¬ (p : ℤ) ∣ collisionResultant μ d₁ d₂ := by
  refine kkh26_good_prime_avoids_collisions_of_TZ_tight hTZ hμ hr hx ?_
  have hcard : ((collisionPairs μ r).card : ℝ) ≤
      (((2 ^ r * (2 ^ (μ - 1)).choose r) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast card_collisionPairs_le_square μ r
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right hcard (tightResultantLogRatio_nonneg μ r hr0 hx)) hcount

/-- **The [KKH26] δ* ceiling with the sharp `(2r)` collision budget.**  Identical conclusion to
`kkh26_mcaDeltaStar_le_of_TZ`, but the unproven supply hypothesis `hcount` is the strictly
weaker fixed-`r` form.  For `r < 2^{μ−1}` (rate below `½`) this is a genuine relaxation of the
Thorner–Zaman prime-supply the polynomial-field-size ceiling requires. -/
theorem kkh26_mcaDeltaStar_le_of_TZ_tight {n : ℕ} {β : ℝ} {supply : ℕ} [NeZero n]
    (hTZ : TZPrimeSupply n β supply) {μ m r : ℕ}
    (hμ : 1 ≤ μ) (hm : 1 ≤ m) (hn : n = 2 ^ μ * m)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (μ - 1))
    (hx : 2 ≤ (n : ℝ) ^ β)
    (hpl : (((2 : ℕ) ^ μ : ℕ) : ℝ) < (n : ℝ) ^ β)
    (hcount : ((collisionPairs μ r).card : ℝ) *
        (Real.log (((2 * r) ^ 2 ^ (μ - 1) : ℕ) : ℝ) / Real.log ((n : ℝ) ^ β))
      < (supply : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD n] ∧
      (n : ℝ) ^ β ≤ p ∧ (p : ℝ) ≤ 2 * (n : ℝ) ^ β ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = n ∧
        ∀ εstar : ℝ≥0∞,
          εstar < ((2 ^ r * (2 ^ (μ - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) →
          ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
              (evalCode g n ((r - 2) * m)) εstar
            ≤ 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) := by
  obtain ⟨p, hp, hmod, hlb, hub, hndvd⟩ :=
    kkh26_good_prime_avoids_collisions_of_TZ_tight hTZ hμ hr hx hcount
  haveI hfact : Fact p.Prime := ⟨hp⟩
  have hplp : (2 : ℕ) ^ μ < p := by
    exact_mod_cast lt_of_lt_of_le hpl hlb
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  -- a generator of order `n` in `F_p^×` (the private `exists_orderOf_eq_of_modEq`, inlined)
  obtain ⟨g, hg⟩ : ∃ g : ZMod p, orderOf g = n := by
    have hp2 : 2 ≤ p := hp.two_le
    have hdvd : n ∣ p - 1 := (Nat.modEq_iff_dvd' (by omega)).mp hmod.symm
    obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
    have hord : orderOf u = p - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hu, Nat.card_eq_fintype_card, ZMod.card_units]
    have hdvd' : n ∣ orderOf u := hord ▸ hdvd
    have hne : orderOf u ≠ 0 := by omega
    exact ⟨((u ^ (orderOf u / n) : (ZMod p)ˣ) : ZMod p), by
      rw [orderOf_units, orderOf_pow_orderOf_div hne hdvd']⟩
  refine ⟨p, hp, hmod, hlb, hub, hfact, g, hg, fun εstar hεstar => ?_⟩
  exact kkh26_mcaDeltaStar_le_of_not_dvd hμ hm hn (hn ▸ hg) hplp hr2 hr hndvd
    εstar hεstar

/-- **The sharp `(2r)` [KKH26] δ* ceiling from the square collision-family budget.**  This is the
fixed-`r` analogue of `kkh26_mcaDeltaStar_le_of_TZ_square_bound`: the supply only has to beat
`(2^r * C(2^(μ-1), r))^2 * log((2r)^(2^(μ-1))) / log(n^β)`. -/
theorem kkh26_mcaDeltaStar_le_of_TZ_tight_square_bound {n : ℕ} {β : ℝ} {supply : ℕ}
    [NeZero n] (hTZ : TZPrimeSupply n β supply) {μ m r : ℕ}
    (hμ : 1 ≤ μ) (hm : 1 ≤ m) (hn : n = 2 ^ μ * m)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (μ - 1))
    (hx : 2 ≤ (n : ℝ) ^ β)
    (hpl : (((2 : ℕ) ^ μ : ℕ) : ℝ) < (n : ℝ) ^ β)
    (hcount : (((2 ^ r * (2 ^ (μ - 1)).choose r) ^ 2 : ℕ) : ℝ) *
        (Real.log (((2 * r) ^ 2 ^ (μ - 1) : ℕ) : ℝ) / Real.log ((n : ℝ) ^ β))
      < (supply : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ p ≡ 1 [MOD n] ∧
      (n : ℝ) ^ β ≤ p ∧ (p : ℝ) ≤ 2 * (n : ℝ) ^ β ∧
      ∃ (_ : Fact p.Prime) (g : ZMod p), orderOf g = n ∧
        ∀ εstar : ℝ≥0∞,
          εstar < ((2 ^ r * (2 ^ (μ - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) →
          ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p)
              (evalCode g n ((r - 2) * m)) εstar
            ≤ 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) := by
  refine kkh26_mcaDeltaStar_le_of_TZ_tight hTZ hμ hm hn hr2 hr hx hpl ?_
  have hcard : ((collisionPairs μ r).card : ℝ) ≤
      (((2 ^ r * (2 ^ (μ - 1)).choose r) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast card_collisionPairs_le_square μ r
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right hcard
      (tightResultantLogRatio_nonneg μ r (by omega) hx)) hcount

end ArkLib.ProximityGap.KKH26

#print axioms ArkLib.ProximityGap.KKH26.tightResultantLogRatio_nonneg
#print axioms ArkLib.ProximityGap.KKH26.kkh26_good_prime_avoids_collisions_of_TZ_tight
#print axioms ArkLib.ProximityGap.KKH26.kkh26_good_prime_avoids_collisions_of_TZ_tight_square_bound
#print axioms ArkLib.ProximityGap.KKH26.kkh26_mcaDeltaStar_le_of_TZ_tight
#print axioms ArkLib.ProximityGap.KKH26.kkh26_mcaDeltaStar_le_of_TZ_tight_square_bound
