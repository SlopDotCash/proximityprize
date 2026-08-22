/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.TwoPowerSubsetSumSpectrum

/-!
# G330: the order-eight weight-{1,3} spectrum boundary is exactly `p = 17`

The G328 lane (PR #531) refuted unguarded field-uniformity of the dimension-two `40`-value
spectrum: in `ZMod 17` the weight-one datum `+1` collides with the weight-three datum
`-1 - g + g²`, and its exact scan found the count profile `16` at `p = 17` and `40` at every
tested prime `p ≡ 1 (mod 8)` in `[41, 10000]`.  The scan leaves a gap: above `10000` the
stable profile is only empirical.

This file closes the collision half of that gap with a machine-checked certificate: for
**every** prime `p ≡ 1 (mod 8)` with `p ≠ 17`, the signed weight-{1,3} spectrum map on the
order-eight subgroup is injective, so the spectrum has exactly `40` distinct values.  With
G328's explicit collision at `17`, the exceptional set is exactly `{17}` — no tested-range
cutoff remains.

The proof avoids resultants entirely.  For `g⁴ = -1` the algebraic norm of
`c₀ + c₁g + c₂g² + c₃g³` factors through two antipodal-squaring steps
(`R(x)·R(-x)` has the same cubic shape in `x²`), each a pure ring identity, so the norm of
each of the `780` pairwise data differences is a concrete integer computable by `decide`.
Every such norm lies in the explicit thirteen-element set `normOkSet`, whose only divisors
congruent to `1 (mod 8)` are `{1, 9, 17, 25, 49}` — of these only `17` is prime.  A collision
at `p` forces `p` to divide one of the norms, which is impossible for a prime
`p ≡ 1 (mod 8)`, `p ≠ 17`.

Honest scope: this certifies the *spectrum-collision* half of the G328 boundary at every
prime.  The full MCA census profile (the bad-scalar set equals the negated triple sums, and
the below-ceiling maximum `9`) remains per-prime executable evidence in the G328 probe; a
field-uniform witness/exclusion statement is a separate open brick.
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.G330SpectrumExactBoundary

open ArkLib.ProximityGap.KKH26

/-! ## The cubic evaluation shape and the norm ladder -/

/-- Evaluation of the cubic `c₀ + c₁x + c₂x² + c₃x³`. -/
def cubicEval {F : Type*} [CommRing F] (c₀ c₁ c₂ c₃ x : F) : F :=
  c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3

/-- **One antipodal-squaring step.**  `R(x)·R(-x)` is again a cubic shape, in `x²`, with the
classical coefficient map.  A pure ring identity — no hypothesis on `x`. -/
lemma cubicEval_mul_neg {F : Type*} [CommRing F] (c₀ c₁ c₂ c₃ x : F) :
    cubicEval c₀ c₁ c₂ c₃ x * cubicEval c₀ c₁ c₂ c₃ (-x) =
      cubicEval (c₀ ^ 2) (2 * c₀ * c₂ - c₁ ^ 2) (c₂ ^ 2 - 2 * c₁ * c₃) (-c₃ ^ 2)
        (x ^ 2) := by
  simp only [cubicEval]; ring

/-- The algebraic norm of `c₀ + c₁ζ + c₂ζ² + c₃ζ³` over the relation `ζ⁴ = -1`: two
antipodal-squaring steps evaluated at `-1`.  Defined for any commutative ring, computable,
and `decide`-friendly over `ℤ`. -/
def quarticNorm {F : Type*} [CommRing F] (c₀ c₁ c₂ c₃ : F) : F :=
  cubicEval ((c₀ ^ 2) ^ 2)
    (2 * c₀ ^ 2 * (c₂ ^ 2 - 2 * c₁ * c₃) - (2 * c₀ * c₂ - c₁ ^ 2) ^ 2)
    ((c₂ ^ 2 - 2 * c₁ * c₃) ^ 2 - 2 * (2 * c₀ * c₂ - c₁ ^ 2) * (-c₃ ^ 2))
    (-(-c₃ ^ 2) ^ 2) (-1)

/-- **The norm factors through any `g` with `g⁴ = -1`.**  Two squaring steps and one
`congrArg` at `(g²)² = g⁴ = -1`. -/
lemma quarticNorm_eq_mul {F : Type*} [CommRing F] {g : F} (hg : g ^ 4 = -1)
    (c₀ c₁ c₂ c₃ : F) :
    quarticNorm c₀ c₁ c₂ c₃ =
      cubicEval c₀ c₁ c₂ c₃ g *
        (cubicEval c₀ c₁ c₂ c₃ (-g) *
          cubicEval (c₀ ^ 2) (2 * c₀ * c₂ - c₁ ^ 2) (c₂ ^ 2 - 2 * c₁ * c₃) (-c₃ ^ 2)
            (-(g ^ 2))) := by
  have hgg : (g ^ 2) ^ 2 = -1 := by
    rw [← pow_mul]; norm_num [hg]
  have h1 := cubicEval_mul_neg c₀ c₁ c₂ c₃ g
  have h2 := cubicEval_mul_neg (c₀ ^ 2) (2 * c₀ * c₂ - c₁ ^ 2) (c₂ ^ 2 - 2 * c₁ * c₃)
    (-c₃ ^ 2) (g ^ 2)
  rw [hgg] at h2
  calc quarticNorm c₀ c₁ c₂ c₃
      = cubicEval (c₀ ^ 2) (2 * c₀ * c₂ - c₁ ^ 2) (c₂ ^ 2 - 2 * c₁ * c₃) (-c₃ ^ 2)
          (g ^ 2) *
        cubicEval (c₀ ^ 2) (2 * c₀ * c₂ - c₁ ^ 2) (c₂ ^ 2 - 2 * c₁ * c₃) (-c₃ ^ 2)
          (-(g ^ 2)) := h2.symm
    _ = (cubicEval c₀ c₁ c₂ c₃ g * cubicEval c₀ c₁ c₂ c₃ (-g)) *
        cubicEval (c₀ ^ 2) (2 * c₀ * c₂ - c₁ ^ 2) (c₂ ^ 2 - 2 * c₁ * c₃) (-c₃ ^ 2)
          (-(g ^ 2)) := by rw [h1]
    _ = cubicEval c₀ c₁ c₂ c₃ g *
        (cubicEval c₀ c₁ c₂ c₃ (-g) *
          cubicEval (c₀ ^ 2) (2 * c₀ * c₂ - c₁ ^ 2) (c₂ ^ 2 - 2 * c₁ * c₃) (-c₃ ^ 2)
            (-(g ^ 2))) := by ring

/-- A root of the cubic kills the norm. -/
lemma quarticNorm_eq_zero_of_root {F : Type*} [CommRing F] {g : F} (hg : g ^ 4 = -1)
    {c₀ c₁ c₂ c₃ : F} (h0 : cubicEval c₀ c₁ c₂ c₃ g = 0) :
    quarticNorm c₀ c₁ c₂ c₃ = 0 := by
  rw [quarticNorm_eq_mul hg, h0, zero_mul]

/-- The integer norm casts through any ring morphism target. -/
lemma quarticNorm_intCast {F : Type*} [CommRing F] (c₀ c₁ c₂ c₃ : ℤ) :
    ((quarticNorm c₀ c₁ c₂ c₃ : ℤ) : F) =
      quarticNorm (c₀ : F) (c₁ : F) (c₂ : F) (c₃ : F) := by
  simp only [quarticNorm, cubicEval]; push_cast; ring

/-- **Divisibility core.**  A `ZMod p` root of an integer cubic at some `g` with `g⁴ = -1`
forces `p` to divide the integer quartic norm of its coefficients. -/
lemma dvd_quarticNorm_of_root {p : ℕ} {g : ZMod p} (hg : g ^ 4 = -1) {c₀ c₁ c₂ c₃ : ℤ}
    (h0 : cubicEval (c₀ : ZMod p) (c₁ : ZMod p) (c₂ : ZMod p) (c₃ : ZMod p) g = 0) :
    (p : ℤ) ∣ quarticNorm c₀ c₁ c₂ c₃ := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, quarticNorm_intCast,
    quarticNorm_eq_zero_of_root hg h0]

/-! ## Signed data as cubic coefficients -/

/-- The `i`-th signed coefficient of a signed datum `(U, T)`: `+1` on `T`, `-1` on `U \ T`,
`0` off the support. -/
def sigCoeff (d : (_ : Finset ℕ) × Finset ℕ) (i : ℕ) : ℤ :=
  (if i ∈ d.2 then 1 else 0) - (if i ∈ d.1 \ d.2 then 1 else 0)

/-- **The bridge.**  On the `h = 4` window, the signed sum `sVal` is the cubic evaluation at
the signed coefficients. -/
lemma sVal_eq_cubicEval {F : Type*} [CommRing F] (g : F) {d : (_ : Finset ℕ) × Finset ℕ}
    (hU : d.1 ⊆ Finset.range 4) (hT : d.2 ⊆ d.1) :
    sVal g d = cubicEval ((sigCoeff d 0 : ℤ) : F) ((sigCoeff d 1 : ℤ) : F)
      ((sigCoeff d 2 : ℤ) : F) ((sigCoeff d 3 : ℤ) : F) g := by
  have hTr : d.2 ⊆ Finset.range 4 := hT.trans hU
  have hDr : d.1 \ d.2 ⊆ Finset.range 4 := Finset.sdiff_subset.trans hU
  have h1 : ∑ i ∈ d.2, g ^ i = ∑ i ∈ Finset.range 4, if i ∈ d.2 then g ^ i else 0 := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hTr]
  have h2 : ∑ i ∈ d.1 \ d.2, g ^ i =
      ∑ i ∈ Finset.range 4, if i ∈ d.1 \ d.2 then g ^ i else 0 := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hDr]
  have hpt : ∀ i ∈ Finset.range 4,
      ((if i ∈ d.2 then g ^ i else 0) - (if i ∈ d.1 \ d.2 then g ^ i else 0)) =
        ((sigCoeff d i : ℤ) : F) * g ^ i := by
    intro i _
    simp only [sigCoeff, Int.cast_sub, apply_ite (fun z : ℤ => (z : F)), Int.cast_one,
      Int.cast_zero]
    split_ifs <;> ring
  rw [sVal, h1, h2, ← Finset.sum_sub_distrib, Finset.sum_congr rfl hpt]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, cubicEval, pow_zero, pow_one]
  ring

/-! ## The finite certificate -/

/-- The complete value set of `|quarticNorm|` over the `780` pairwise differences of the
weight-{1,3} signed spectrum data on `h = 4`. -/
def normOkSet : Finset ℕ := {2, 4, 8, 16, 18, 32, 34, 36, 50, 64, 68, 98, 144}

/-- **Pair certificate** (kernel computation): every difference of two distinct spectrum
data has quartic norm of absolute value in `normOkSet`.  In particular no difference norm
vanishes. -/
lemma pair_norm_mem :
    ∀ e₁ ∈ spectrumData 4 ({1, 3} : Finset ℕ), ∀ e₂ ∈ spectrumData 4 ({1, 3} : Finset ℕ),
      e₁ ≠ e₂ →
        (quarticNorm (sigCoeff e₁.2 0 - sigCoeff e₂.2 0) (sigCoeff e₁.2 1 - sigCoeff e₂.2 1)
          (sigCoeff e₁.2 2 - sigCoeff e₂.2 2)
          (sigCoeff e₁.2 3 - sigCoeff e₂.2 3)).natAbs ∈ normOkSet := by
  decide

/-- Every certificate value is positive and at most `144`. -/
lemma normOkSet_bounds : ∀ n ∈ normOkSet, 0 < n ∧ n ≤ 144 := by decide

set_option maxRecDepth 4000 in
/-- **Divisor census** (kernel computation): the only divisors of certificate values that
are `≡ 1 (mod 8)` are `1, 9, 17, 25, 49`. -/
lemma normOkSet_mod8_divisors :
    ∀ n ∈ normOkSet, ∀ q ≤ 144, q ∣ n → q % 8 = 1 →
      q = 1 ∨ q = 9 ∨ q = 17 ∨ q = 25 ∨ q = 49 := by
  decide

/-! ## The exact-boundary theorems -/

/-- **Injectivity away from the boundary prime.**  For every prime `p ≡ 1 (mod 8)` with
`p ≠ 17` and any `g` with `g⁴ = -1` (equivalently, any element of order eight), the
weight-{1,3} signed spectrum map is injective.  Together with the explicit `p = 17`
collision of the G328 lane, the exceptional set of the dimension-two spectrum is exactly
`{17}`. -/
theorem spectrumVal_injOn_of_ne17 (p : ℕ) [Fact p.Prime] (hp8 : p % 8 = 1) (hp17 : p ≠ 17)
    {g : ZMod p} (hg : g ^ 4 = -1) :
    Set.InjOn (spectrumVal g) (spectrumData 4 ({1, 3} : Finset ℕ)) := by
  intro e₁ he₁ e₂ he₂ heq
  by_contra hne
  have he₁' : e₁ ∈ spectrumData 4 ({1, 3} : Finset ℕ) := Finset.mem_coe.mp he₁
  have he₂' : e₂ ∈ spectrumData 4 ({1, 3} : Finset ℕ) := Finset.mem_coe.mp he₂
  have hm₁ : e₁.2 ∈ sigData 4 e₁.1 := (Finset.mem_sigma.mp he₁').2
  have hm₂ : e₂.2 ∈ sigData 4 e₂.1 := (Finset.mem_sigma.mp he₂').2
  obtain ⟨⟨hU₁, -⟩, hT₁⟩ := mem_sigData.mp hm₁
  obtain ⟨⟨hU₂, -⟩, hT₂⟩ := mem_sigData.mp hm₂
  have heq' : sVal g e₁.2 = sVal g e₂.2 := heq
  rw [sVal_eq_cubicEval g hU₁ hT₁, sVal_eq_cubicEval g hU₂ hT₂] at heq'
  have hroot : cubicEval ((sigCoeff e₁.2 0 - sigCoeff e₂.2 0 : ℤ) : ZMod p)
      ((sigCoeff e₁.2 1 - sigCoeff e₂.2 1 : ℤ) : ZMod p)
      ((sigCoeff e₁.2 2 - sigCoeff e₂.2 2 : ℤ) : ZMod p)
      ((sigCoeff e₁.2 3 - sigCoeff e₂.2 3 : ℤ) : ZMod p) g = 0 := by
    simp only [cubicEval] at heq' ⊢
    push_cast
    linear_combination heq'
  have hdvd : (p : ℤ) ∣ quarticNorm (sigCoeff e₁.2 0 - sigCoeff e₂.2 0)
      (sigCoeff e₁.2 1 - sigCoeff e₂.2 1) (sigCoeff e₁.2 2 - sigCoeff e₂.2 2)
      (sigCoeff e₁.2 3 - sigCoeff e₂.2 3) := dvd_quarticNorm_of_root hg hroot
  have hmem := pair_norm_mem e₁ he₁' e₂ he₂' hne
  have hpn : p ∣ (quarticNorm (sigCoeff e₁.2 0 - sigCoeff e₂.2 0)
      (sigCoeff e₁.2 1 - sigCoeff e₂.2 1) (sigCoeff e₁.2 2 - sigCoeff e₂.2 2)
      (sigCoeff e₁.2 3 - sigCoeff e₂.2 3)).natAbs := by
    have h := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa using h
  obtain ⟨hpos, hle⟩ := normOkSet_bounds _ hmem
  have hple : p ≤ 144 := le_trans (Nat.le_of_dvd hpos hpn) hle
  have hcases := normOkSet_mod8_divisors _ hmem p hple hpn hp8
  have hprime : p.Prime := Fact.out
  rcases hcases with h | h | h | h | h
  · subst h; exact absurd hprime (by norm_num)
  · subst h; exact absurd hprime (by norm_num)
  · exact hp17 h
  · subst h; exact absurd hprime (by norm_num)
  · subst h; exact absurd hprime (by norm_num)

/-- Order-eight (primitive-root) form of the hypothesis. -/
theorem spectrumVal_injOn_of_primitiveRoot (p : ℕ) [Fact p.Prime] (hp8 : p % 8 = 1)
    (hp17 : p ≠ 17) {g : ZMod p} (hg : IsPrimitiveRoot g 8) :
    Set.InjOn (spectrumVal g) (spectrumData 4 ({1, 3} : Finset ℕ)) := by
  refine spectrumVal_injOn_of_ne17 p hp8 hp17 ?_
  have h8 : IsPrimitiveRoot g (2 ^ 3) := by norm_num [hg]
  have := pow_half_eq_neg_one (m := 3) (by norm_num) h8
  simpa using this

/-- **The exact spectrum count away from the boundary.**  For every prime `p ≡ 1 (mod 8)`
with `p ≠ 17`, the weight-{1,3} spectrum on the order-eight subgroup has exactly `40`
distinct values — the tested-range cutoff of the G328 scan is removed. -/
theorem spectrum_card_eq_forty (p : ℕ) [Fact p.Prime] (hp8 : p % 8 = 1) (hp17 : p ≠ 17)
    {g : ZMod p} (hg : g ^ 4 = -1) :
    ((spectrumData 4 ({1, 3} : Finset ℕ)).image (spectrumVal g)).card = 40 := by
  rw [subsetSumSpectrum_card g 4 ({1, 3} : Finset ℕ)
    (spectrumVal_injOn_of_ne17 p hp8 hp17 hg)]
  decide

end ArkLib.ProximityGap.Frontier.G330SpectrumExactBoundary

/-! ## Axiom audit -/

#print axioms ArkLib.ProximityGap.Frontier.G330SpectrumExactBoundary.quarticNorm_eq_mul
#print axioms ArkLib.ProximityGap.Frontier.G330SpectrumExactBoundary.sVal_eq_cubicEval
#print axioms ArkLib.ProximityGap.Frontier.G330SpectrumExactBoundary.pair_norm_mem
#print axioms
  ArkLib.ProximityGap.Frontier.G330SpectrumExactBoundary.spectrumVal_injOn_of_ne17
#print axioms
  ArkLib.ProximityGap.Frontier.G330SpectrumExactBoundary.spectrumVal_injOn_of_primitiveRoot
#print axioms
  ArkLib.ProximityGap.Frontier.G330SpectrumExactBoundary.spectrum_card_eq_forty
