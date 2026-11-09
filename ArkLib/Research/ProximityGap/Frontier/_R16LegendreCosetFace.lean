/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# LANE LEGENDRE (#466 round 16): the deg=2 face of corrected Problem B — exact coset structure

The deg=2 face of the corrected (off-diagonal) Problem B is the shifted-subgroup Legendre sum
`W(s₀) := ∑_{x∈μ_n} (s₀−x | p)` (quadratic character of shifts of the thin subgroup), with
empirical target `|W(s₀)| ≤ √2·M` off the diagonal.  This file lands the exact algebraic
skeleton of that face, axiom-clean, for an arbitrary multiplicative character (so it covers
every `T_χ` in the round-15 Gauss decomposition, not just deg=2), plus the two Legendre-specific
exact integer identities.  All verified exactly (integer arithmetic) in
`scratchpad/r16_legendre_face.py` at n = 8/16/32, 83 primes:

* `shiftedCharSum_mul_left` — **μ_n-equivariance**: for `u` with `u·G = G`,
  `W(u·s₀) = χ(u)·W(s₀)`.  Hence `|W|` depends ONLY on the coset `s₀·μ_n` — the face has just
  `m = (p−1)/n` degrees of freedom, not `p−1`.
* `shiftedCharSum_completion` — **multiplicative completion**: for `s₀ ≠ 0`,
  `W(s₀) = χ(s₀)·∑_{x∈G} χ(1 − s₀⁻¹x)`, i.e. `|W|` is a coset-shifted sum of `χ(1−y)`.
* `quadraticChar_two_point` — the two-point orthogonality
  `∑_a χ(a)·χ(a+b) = −1` for `b ≠ 0` (quadratic character, `char F ≠ 2`).
* `sum_sq_shiftedQuadSum` — **the exact second moment over ALL offsets** (pure ℤ identity,
  arbitrary finite evaluation set `G`, no subgroup structure needed):
  `∑_{s₀∈F} W(s₀)² = |G|·q − |G|²`.
  With coset invariance this pins the coset-averaged square to
  `avg_{cosets}|W|² = (q−n−W(0)²/n)·n/(q−1) ≈ n`: the AVERAGE coset obeys the √n (Wick) scale
  EXACTLY; the open deg=2 face is, once again, purely worst-coset-vs-average — the same
  worst-vs-average gap as Problem A/B, now on only `m` cosets.

No closure claimed: the worst-coset bound `|W| ≤ √2·M` (or `≤ C√(n ln p)`) remains open; the
probe shows max|W_off|/M ∈ [0.61, 1.60] with WEAK per-prime correlation to M (corr ≈ 0.2) —
the face shares the VALUE √(n ln p) but is statistically a distinct object.  Issue #466, round
16, Legendre lane.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.R16LegendreCosetFace

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {R : Type*} [CommRing R]

/-- The shifted-set character sum `W_χ(s₀) = ∑_{x∈G} χ(s₀ − x)`.  For `χ` the quadratic
character and `G = μ_n` this is the deg=2 face of corrected Problem B; for general `χ` it is
the `T_χ` family of the round-15 Gauss decomposition (up to the excluded `x = s₀` term, which
vanishes anyway since `χ(0) = 0`). -/
def shiftedCharSum (χ : MulChar F R) (G : Finset F) (s₀ : F) : R :=
  ∑ x ∈ G, χ (s₀ - x)

omit [Fintype F] [DecidableEq F] in
/-- **Equivariance / coset invariance.** If `G` is stable under multiplication by `u ≠ 0`
(e.g. `G = μ_n` and `u ∈ μ_n`), then `W(u·s₀) = χ(u)·W(s₀)`.  Consequently `‖W‖` is constant
on cosets of `μ_n`: the deg=2 face has only `(q−1)/n` degrees of freedom. -/
theorem shiftedCharSum_mul_left (χ : MulChar F R) (G : Finset F) (u s₀ : F) (hu : u ≠ 0)
    (hG : ∀ x, u * x ∈ G ↔ x ∈ G) :
    shiftedCharSum χ G (u * s₀) = χ u * shiftedCharSum χ G s₀ := by
  unfold shiftedCharSum
  rw [Finset.mul_sum]
  refine Finset.sum_nbij' (fun y => u⁻¹ * y) (fun x => u * x) ?_ ?_ ?_ ?_ ?_
  · intro y hy
    exact (hG (u⁻¹ * y)).mp (by rw [mul_inv_cancel_left₀ hu]; exact hy)
  · intro x hx; exact (hG x).mpr hx
  · intro y _; exact mul_inv_cancel_left₀ hu y
  · intro x _; exact inv_mul_cancel_left₀ hu x
  · intro y hy
    rw [← map_mul, mul_sub, mul_inv_cancel_left₀ hu]

omit [Fintype F] [DecidableEq F] in
/-- **Multiplicative completion.** For `s₀ ≠ 0`,
`W(s₀) = χ(s₀)·∑_{x∈G} χ(1 − s₀⁻¹·x)`: the shifted-subgroup sum is `χ(s₀)` times a sum of
`χ(1−y)` over the coset `s₀⁻¹·G` — the object only depends on the coset of `s₀` mod the
stabilizer of `G`. -/
theorem shiftedCharSum_completion (χ : MulChar F R) (G : Finset F) (s₀ : F) (hs : s₀ ≠ 0) :
    shiftedCharSum χ G s₀ = χ s₀ * ∑ x ∈ G, χ (1 - s₀⁻¹ * x) := by
  unfold shiftedCharSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← map_mul, mul_sub, mul_one, mul_inv_cancel_left₀ hs]

section Quadratic

variable (F)

/-- The sum of `χ(a)²` over the field: `q − 1` (each nonzero `a` contributes `1`, zero
contributes `0`). -/
theorem sum_quadraticChar_sq :
    ∑ a : F, quadraticChar F a ^ 2 = (Fintype.card F : ℤ) - 1 := by
  classical
  have h2 : ∑ a : F, quadraticChar F a ^ 2
      = ∑ a ∈ ({0}ᶜ : Finset F), quadraticChar F a ^ 2 := by
    symm
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro a _ ha
    have : a = 0 := by simpa using ha
    simp [this]
  have h1 : ∑ a ∈ ({0}ᶜ : Finset F), quadraticChar F a ^ 2
      = ∑ _a ∈ ({0}ᶜ : Finset F), (1 : ℤ) :=
    Finset.sum_congr rfl fun a ha =>
      quadraticChar_sq_one (by simpa using (Finset.mem_compl.mp ha))
  rw [h2, h1, Finset.sum_const, Finset.card_compl, Finset.card_singleton,
    nsmul_eq_mul, mul_one, Nat.cast_sub Fintype.card_pos, Nat.cast_one]

variable {F}

/-- **Two-point orthogonality for the quadratic character**: for `b ≠ 0`,
`∑_a χ(a)·χ(a+b) = −1`.  (Substitute `t = 1 + b·a⁻¹`; `χ(a)·χ(a+b) = χ(1 + b·a⁻¹)` for
`a ≠ 0`, and `a ↦ 1 + b·a⁻¹` is a bijection `F∖{0} → F∖{1}`.) -/
theorem quadraticChar_two_point (hF : ringChar F ≠ 2) {b : F} (hb : b ≠ 0) :
    ∑ a : F, quadraticChar F a * quadraticChar F (a + b) = -1 := by
  classical
  -- restrict to a ≠ 0
  have h0 : ∑ a : F, quadraticChar F a * quadraticChar F (a + b)
      = ∑ a ∈ ({0}ᶜ : Finset F), quadraticChar F a * quadraticChar F (a + b) := by
    rw [← Finset.sum_subset (Finset.subset_univ _)]
    intro a _ ha
    simp only [Finset.mem_compl, Finset.mem_singleton, not_not] at ha
    simp [ha]
  rw [h0]
  -- rewrite each term as χ(1 + b·a⁻¹)
  have hterm : ∀ a ∈ ({0}ᶜ : Finset F),
      quadraticChar F a * quadraticChar F (a + b) = quadraticChar F (1 + b * a⁻¹) := by
    intro a ha
    have ha0 : a ≠ 0 := by simpa using (Finset.mem_compl.mp ha)
    have hab : a + b = a * (1 + b * a⁻¹) := by
      rw [mul_add, mul_one, mul_comm b a⁻¹, mul_inv_cancel_left₀ ha0]
    rw [hab, map_mul, ← mul_assoc, ← pow_two, quadraticChar_sq_one ha0, one_mul]
  rw [Finset.sum_congr rfl hterm]
  -- reindex by t = 1 + b·a⁻¹, a bijection {0}ᶜ → {1}ᶜ
  have hre : ∑ a ∈ ({0}ᶜ : Finset F), quadraticChar F (1 + b * a⁻¹)
      = ∑ t ∈ ({1}ᶜ : Finset F), quadraticChar F t := by
    refine Finset.sum_nbij' (fun a => 1 + b * a⁻¹) (fun t => b * (t - 1)⁻¹) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      have ha0 : a ≠ 0 := by simpa using (Finset.mem_compl.mp ha)
      simp only [Finset.mem_compl, Finset.mem_singleton]
      intro h
      have : b * a⁻¹ = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with h' | h'
      · exact hb h'
      · exact ha0 (inv_eq_zero.mp h')
    · intro t ht
      have ht1 : t ≠ 1 := by simpa using (Finset.mem_compl.mp ht)
      have ht1' : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
      simp only [Finset.mem_compl, Finset.mem_singleton]
      exact mul_ne_zero hb (inv_ne_zero ht1')
    · intro a ha
      have ha0 : a ≠ 0 := by simpa using (Finset.mem_compl.mp ha)
      show b * ((1 + b * a⁻¹) - 1)⁻¹ = a
      have h1 : (1 : F) + b * a⁻¹ - 1 = b * a⁻¹ := by ring
      rw [h1, mul_inv, inv_inv, mul_inv_cancel_left₀ hb]
    · intro t ht
      have ht1 : t ≠ 1 := by simpa using (Finset.mem_compl.mp ht)
      have ht1' : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
      show 1 + b * (b * (t - 1)⁻¹)⁻¹ = t
      rw [mul_inv, inv_inv, mul_inv_cancel_left₀ hb]
      ring
    · intro a _; rfl
  rw [hre]
  -- ∑_{t≠1} χ(t) = (∑_t χ(t)) − χ(1) = 0 − 1
  have hsplit := Finset.sum_compl_add_sum ({1} : Finset F)
    (f := fun t => (quadraticChar F t : ℤ))
  rw [Finset.sum_singleton, quadraticChar_sum_zero hF] at hsplit
  have hone : quadraticChar F (1 : F) = 1 := map_one _
  rw [hone] at hsplit
  linarith [hsplit]

/-- **The exact second moment of the deg=2 face over all offsets** (pure integer identity,
any finite evaluation set `G` — subgroup structure not needed):
`∑_{s₀∈F} W(s₀)² = |G|·q − |G|²` where `W(s₀) = ∑_{x∈G} χ(s₀−x)`, `χ` the quadratic character.
Combined with `shiftedCharSum_mul_left` (|W| constant on `μ_n`-cosets), the coset-averaged
square is exactly Wick-scale `≈ n`; the open content of the deg=2 face is worst-coset vs
average-coset only. -/
theorem sum_sq_shiftedQuadSum (hF : ringChar F ≠ 2) (G : Finset F) :
    ∑ s₀ : F, (shiftedCharSum (quadraticChar F) G s₀) ^ 2
      = (G.card : ℤ) * (Fintype.card F : ℤ) - (G.card : ℤ) ^ 2 := by
  classical
  have expand : ∀ s₀ : F, (shiftedCharSum (quadraticChar F) G s₀) ^ 2
      = ∑ x ∈ G, ∑ y ∈ G, quadraticChar F (s₀ - x) * quadraticChar F (s₀ - y) := by
    intro s₀
    rw [shiftedCharSum, pow_two, Finset.sum_mul_sum]
  calc ∑ s₀ : F, (shiftedCharSum (quadraticChar F) G s₀) ^ 2
      = ∑ s₀ : F, ∑ x ∈ G, ∑ y ∈ G,
          quadraticChar F (s₀ - x) * quadraticChar F (s₀ - y) := by
        exact Finset.sum_congr rfl fun s₀ _ => expand s₀
    _ = ∑ x ∈ G, ∑ y ∈ G, ∑ s₀ : F,
          quadraticChar F (s₀ - x) * quadraticChar F (s₀ - y) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ x ∈ G, ∑ y ∈ G,
          (if x = y then (Fintype.card F : ℤ) - 1 else -1) := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        -- substitute a = s₀ − x  (bijection s₀ ↦ s₀ − x)
        have hsub : ∑ s₀ : F, quadraticChar F (s₀ - x) * quadraticChar F (s₀ - y)
            = ∑ a : F, quadraticChar F a * quadraticChar F (a + (x - y)) := by
          refine Fintype.sum_equiv (Equiv.subRight x) _ _ fun s₀ => ?_
          simp only [Equiv.subRight_apply]
          rw [show s₀ - y = s₀ - x + (x - y) from by ring]
        rw [hsub]
        by_cases hxy : x = y
        · subst hxy
          simp only [sub_self, add_zero, if_true, ← pow_two]
          exact sum_quadraticChar_sq F
        · rw [if_neg hxy]
          exact quadraticChar_two_point hF (sub_ne_zero.mpr hxy)
    _ = (G.card : ℤ) * (Fintype.card F : ℤ) - (G.card : ℤ) ^ 2 := by
        have hinner : ∀ x ∈ G, (∑ y ∈ G,
            (if x = y then (Fintype.card F : ℤ) - 1 else -1))
            = (Fintype.card F : ℤ) - (G.card : ℤ) := by
          intro x hx
          have hsplit : ∀ y ∈ G, (if x = y then (Fintype.card F : ℤ) - 1 else -1)
              = -1 + (if x = y then (Fintype.card F : ℤ) else 0) := by
            intro y _; split_ifs <;> ring
          rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_const,
            Finset.sum_ite_eq G x (fun _ => (Fintype.card F : ℤ)), if_pos hx]
          ring
        rw [Finset.sum_congr rfl hinner, Finset.sum_const]
        ring

end Quadratic

end ArkLib.ProximityGap.Frontier.R16LegendreCosetFace

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R16LegendreCosetFace.shiftedCharSum_mul_left
#print axioms ArkLib.ProximityGap.Frontier.R16LegendreCosetFace.shiftedCharSum_completion
#print axioms ArkLib.ProximityGap.Frontier.R16LegendreCosetFace.sum_quadraticChar_sq
#print axioms ArkLib.ProximityGap.Frontier.R16LegendreCosetFace.quadraticChar_two_point
#print axioms ArkLib.ProximityGap.Frontier.R16LegendreCosetFace.sum_sq_shiftedQuadSum
