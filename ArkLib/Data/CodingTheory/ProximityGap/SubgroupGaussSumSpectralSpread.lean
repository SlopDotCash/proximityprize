/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumFourthMarkovMuN
import Mathlib.Algebra.Order.Chebyshev

/-!
# Spectral spreading for the thin `2`-power subgroup `μ_n`: a Cauchy–Schwarz support lower bound (#444)

The two exact-moment facts for the thin `2`-power NTT subgroup `μ_n ⊂ F_p`
(`n = 2^m`, `m ≥ 1`, `p > 2^n`) —

* `subgroup_gaussSum_secondMoment` : `∑_b ‖η_b‖² = q·|G| = q·n`, and
* the exact thin energy `∑_b ‖η_b‖⁴ = q·E(μ_n) = q·(3n² − 3n)` (`AdditiveEnergyBridge`) —

combine via **Cauchy–Schwarz** (`sq_sum_le_card_mul_sum_sq`, `(∑f)² ≤ #s·∑f²`) into a **lower bound
on the spectral support**: the energy cannot be carried by a few frequencies.

> **`card_support_muN_ge`** —
>   `#{b : η_b(μ_n) ≠ 0} ≥ (q·n)² / (q·(3n²−3n)) = q·n / (3(n−1))`.

So at least a `~1/3` fraction of **all** `q` frequencies have a nonzero incomplete character sum
over `μ_n`: the `√n`-cancellation is **spread** across `Ω(q)` frequencies, not concentrated. This is
the **lower-count complement** to `SubgroupGaussSumFourthMarkovMuN.card_johnson_scale_frequencies_muN_le`
(an *upper* bound on the count reaching the *Johnson* scale) — together they pin the η-mass to a
broad mid-scale band, neither localized nor reaching `√q`.

## Thinness-essential (rule 3)

The bound is the L⁴/L²-ratio inequality with the **exact** `μ_n` energy `3n²−3n`. For a thick
subgroup with `E ≫ 3n²` the same Cauchy–Schwarz gives only `#support ≥ qn/E ≪ q`, no spreading
claim. The `Ω(q)` support spread is the thin-subgroup Sidon-mod-negation phenomenon.

## Scope (honest, rules 1,3,6)

This is an exact-moment / Cauchy–Schwarz **average-case spreading** fact, NOT a CORE closure and not
a per-frequency sup bound. It says the η-mass is spread broadly; it says **nothing** about whether
the *worst* frequency stays at the prize floor `√(n·log(p/n))` — that worst-case sup is the open BGK
content. No capacity over-claim. CORE `M(μ_n) ≤ C·√(n·log(p/n))` stays **open**.

See `SubgroupGaussSumFourthMarkovMuN.lean` (the exact `μ_n` fourth moment + the upper-count companion)
and `SubgroupGaussSumSecondMoment.lean` (the exact second moment).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


open Finset AddChar Polynomial
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment
open ArkLib.ProximityGap.AdditiveEnergyBridge
open ArkLib.ProximityGap.AdditiveEnergySidonModNeg
open ArkLib.ProximityGap.SubgroupGaussSumFourthMarkovMuN

namespace ArkLib.ProximityGap.SubgroupGaussSumSpectralSpread

variable {p : ℕ} [Fact p.Prime] {n m : ℕ}

/-- **Spectral-support lower bound for `μ_n` (multiplied form).**
For `n = 2^m` (`m ≥ 1`), `p > 2^n`, a primitive `n`-th root `ω` and a primitive additive character
`ψ`, the number of frequencies with `η_b(μ_n) ≠ 0` obeys

  `#{b : η_b ≠ 0} · (q·(3n²−3n)) ≥ (q·n)²`,

i.e. the Cauchy–Schwarz `(∑‖η‖²)² ≤ #support · ∑‖η‖⁴` instantiated with the **exact** second moment
`q·n` and fourth moment `q·(3n²−3n)`. -/
theorem card_support_muN_mul_ge (hn2 : n = 2 ^ m) (hm : 1 ≤ m) (hp : 2 ^ n < p)
    {ω : ZMod p} (hω : IsPrimitiveRoot ω n) {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    ((Finset.univ.filter
        (fun b : ZMod p => eta ψ (nthRootsFinset n (1 : ZMod p)) b ≠ 0)).card : ℝ)
        * ((Fintype.card (ZMod p) : ℝ) * (3 * (n : ℝ) ^ 2 - 3 * n))
      ≥ ((Fintype.card (ZMod p) : ℝ) * n) ^ 2 := by
  classical
  set G : Finset (ZMod p) := nthRootsFinset n (1 : ZMod p) with hGdef
  have hn0 : n ≠ 0 := by rw [hn2]; positivity
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hGmem : ∀ z : ZMod p, z ∈ G ↔ z ^ n = 1 := fun z => mem_nthRootsFinset hnpos 1
  have hcard : G.card = n := hω.card_nthRootsFinset
  have h2n : 2 ≤ 2 ^ n :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hn0))
  have hp2 : 2 < p := by omega
  have h2F : (2 : ZMod p) ≠ 0 := by
    intro hcontra
    have hdvd : (p : ℕ) ∣ 2 := by rw [← ZMod.natCast_eq_zero_iff]; exact_mod_cast hcontra
    have := Nat.le_of_dvd (by norm_num) hdvd; omega
  have h0 : (0 : ZMod p) ∉ G := by rw [hGmem]; simp [zero_pow hn0]
  have hneg : ∀ x ∈ G, -x ∈ G := muN_neg_closed hn2 hm
  have hS := sidonModNeg_mu_n hn2 hm hp hω hGmem
  have hEnat : addEnergy G = 3 * G.card ^ 2 - 3 * G.card :=
    addEnergy_eq_of_sidonModNeg h2F h0 hneg hS
  have hsub : 3 * G.card ≤ 3 * G.card ^ 2 := by
    nlinarith [Nat.le_self_pow (two_ne_zero) G.card]
  -- exact second & fourth moments as real numbers
  set S := Finset.univ.filter (fun b : ZMod p => eta ψ G b ≠ 0) with hSdef
  -- the squared-norm function
  set f : ZMod p → ℝ := fun b => ‖eta ψ G b‖ ^ 2 with hf
  have hf_nonneg : ∀ b, 0 ≤ f b := fun b => sq_nonneg _
  -- off the support f = 0, so the universe sum equals the support sum
  have hsum2_eq : ∑ b ∈ S, f b = ∑ b : ZMod p, f b := by
    rw [hSdef]
    refine Finset.sum_filter_of_ne (fun b _ hfb => ?_)
    -- f b ≠ 0 ⟹ ‖η_b‖² ≠ 0 ⟹ η_b ≠ 0
    intro hzero
    apply hfb
    show ‖eta ψ G b‖ ^ 2 = 0
    rw [hzero]; simp
  have hsum4_eq : ∑ b ∈ S, (f b) ^ 2 = ∑ b : ZMod p, (f b) ^ 2 := by
    rw [hSdef]
    refine Finset.sum_filter_of_ne (fun b _ hfb => ?_)
    intro hzero
    apply hfb
    show (‖eta ψ G b‖ ^ 2) ^ 2 = 0
    rw [hzero]; simp
  -- the two exact moments
  have hmom2 : ∑ b : ZMod p, f b = (Fintype.card (ZMod p) : ℝ) * n := by
    rw [hf]
    have := subgroup_gaussSum_secondMoment hψ G
    rw [this, hcard]
  have hmom4 : ∑ b : ZMod p, (f b) ^ 2 = (Fintype.card (ZMod p) : ℝ) * (3 * (n : ℝ) ^ 2 - 3 * n) := by
    have hfsq : ∀ b, (f b) ^ 2 = ‖eta ψ G b‖ ^ 4 := by intro b; rw [hf]; ring
    simp_rw [hfsq]
    rw [subgroup_gaussSum_fourthMoment hψ G]
    have hEreal : (addEnergy G : ℝ) = 3 * (n : ℝ) ^ 2 - 3 * n := by
      rw [hEnat, Nat.cast_sub hsub, hcard]; push_cast; ring
    rw [hEreal]
  -- Cauchy–Schwarz over the support
  have hcs : (∑ b ∈ S, f b) ^ 2 ≤ (S.card : ℝ) * ∑ b ∈ S, (f b) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  rw [hsum2_eq, hsum4_eq, hmom2, hmom4] at hcs
  -- rearrange to the ≥ form
  linarith [hcs]

/-- **Spectral-support lower bound for `μ_n` (divided form).**
`#{b : η_b(μ_n) ≠ 0} ≥ (q·n)² / (q·(3n²−3n)) = q·n / (3(n−1))`. At least a `~1/3` fraction of all `q`
frequencies have a nonzero incomplete character sum over the thin subgroup — the `√n`-cancellation is
spread across `Ω(q)` frequencies, the thin Sidon-mod-negation spreading. Thinness-essential. -/
theorem card_support_muN_ge (hn2 : n = 2 ^ m) (hm : 1 ≤ m) (hp : 2 ^ n < p)
    {ω : ZMod p} (hω : IsPrimitiveRoot ω n) {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive)
    (hn2le : 2 ≤ n) :
    ((Finset.univ.filter
        (fun b : ZMod p => eta ψ (nthRootsFinset n (1 : ZMod p)) b ≠ 0)).card : ℝ)
      ≥ ((Fintype.card (ZMod p) : ℝ) * n) ^ 2
          / ((Fintype.card (ZMod p) : ℝ) * (3 * (n : ℝ) ^ 2 - 3 * n)) := by
  have hkey := card_support_muN_mul_ge hn2 hm hp hω hψ
  have hqpos : (0 : ℝ) < (Fintype.card (ZMod p) : ℝ) := by exact_mod_cast Fintype.card_pos
  have hnr : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2le
  have hEpos : (0 : ℝ) < 3 * (n : ℝ) ^ 2 - 3 * n := by nlinarith [hnr]
  have hdenpos : (0 : ℝ) < (Fintype.card (ZMod p) : ℝ) * (3 * (n : ℝ) ^ 2 - 3 * n) :=
    mul_pos hqpos hEpos
  rw [ge_iff_le, div_le_iff₀ hdenpos]
  linarith [hkey]

end ArkLib.ProximityGap.SubgroupGaussSumSpectralSpread

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSpectralSpread.card_support_muN_mul_ge
#print axioms ArkLib.ProximityGap.SubgroupGaussSumSpectralSpread.card_support_muN_ge
