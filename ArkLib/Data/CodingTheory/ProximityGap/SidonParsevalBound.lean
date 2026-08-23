/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.BigOperators.Fin

/-!
# PARSEVAL FOR THE FOUR-TERM + AM-GM: toward the improved Sidon resultant bound (#389)

`CyclotomicResultantBound.abs_resultant_le` bounds the cyclotomic resultant of the four-term
`f = X^i+X^j−X^k−X^l` by the **pointwise** estimate `‖f(ζ)‖ ≤ 4`, giving `|Res| ≤ 4^{φ(n)} = 2^n`
(for `n = 2^m`) and hence the Sidon threshold `p > 2^n`.  Numerically (`probe_resultant_bound.py`)
this is loose: the true `max |Res|` over four-terms with pairwise-distinct exponents mod `n` is
**exactly `2^{3n/4}`** — the bound `‖f(ζ)‖ ≤ 4` is replaced by the **`ℓ²` (Parseval) average**
`∑_{ζ:ζ^n=1} ‖f(ζ)‖² = 4n`, which through AM-GM over the `φ(n) = n/2` primitive roots gives
`|Res|² = ∏_{prim} ‖f(ζ)‖² ≤ (4n/φ(n))^{φ(n)} = 8^{n/2}`, i.e. `|Res| ≤ 2^{3n/4}`.  That would
sharpen the small-subgroup Sidon threshold from `p > 2^n` to `p > 2^{3n/4}`.

This file establishes the two genuinely novel analytic inputs, both axiom-clean:

* **`parseval_fourTerm`** — the exact second moment of the four-term over the `n`-th roots of unity:
  for pairwise-distinct unit values `v : Fin 4 → ℂ`, `∑_{t<n} ‖∑ₐ sₐ (vₐ)ᵗ‖² = 4n` (the DFT/Parseval
  identity, via the root-of-unity geometric sum `geom_sum_rou`);
* **`prod_le_of_sum_le`** — the AM-GM product bound `∏ xᵢ ≤ Bᵏ` from `∑ xᵢ ≤ k·B`
  (`Real.geom_mean_le_arith_mean_weighted` with uniform weights).

The remaining step — wiring these to the in-tree `resultant_cast_eq_prod` /
`nnnorm_prod_eval_cyclotomic_roots_le` product form over the primitive roots (a subset of the
`n`-th roots) — is the resultant assembly.  Issue #389.
-/

open Complex Finset BigOperators

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

/-- Geometric sum of an `n`-th root of unity: `n` if it is `1`, else `0`. -/
theorem geom_sum_rou {n : ℕ} {g : ℂ} (hg : g ^ n = 1) :
    ∑ t ∈ Finset.range n, g ^ t = if g = 1 then (n : ℂ) else 0 := by
  by_cases h1 : g = 1
  · simp [h1]
  · rw [if_neg h1, geom_sum_eq h1, hg]; simp

/-- For a norm-one complex number, conjugation is inversion. -/
theorem conj_eq_inv_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) : (starRingEnd ℂ) z = z⁻¹ := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have h1 : (starRingEnd ℂ) z * z = 1 := by
    rw [mul_comm, Complex.mul_conj', hz]; norm_num
  field_simp
  linear_combination h1

/-- **Parseval / exact second moment of the four-term over the `n`-th roots of unity.**  For
pairwise-distinct unit values `v : Fin 4 → ℂ`, each an `n`-th root of unity, and signs `s` with
`s a · s a = 1` (real), `∑_{t<n} ‖∑ₐ sₐ (vₐ)ᵗ‖² = 4n`.  The off-diagonal terms cancel by the
root-of-unity orthogonality `geom_sum_rou`; the diagonal contributes `n` per index, `4n` total. -/
theorem parseval_fourTerm {n : ℕ} (v : Fin 4 → ℂ) (hvn : ∀ a, v a ^ n = 1)
    (hnorm : ∀ a, ‖v a‖ = 1) (hdist : Function.Injective v)
    (s : Fin 4 → ℂ) (hs2 : ∀ a, s a * s a = 1) (hsconj : ∀ a, (starRingEnd ℂ) (s a) = s a) :
    ∑ t ∈ Finset.range n, ‖∑ a : Fin 4, s a * (v a) ^ t‖ ^ 2 = 4 * n := by
  have hvb0 : ∀ b, v b ≠ 0 := fun b h => by simpa [h] using hnorm b
  have hper : ∀ a b : Fin 4,
      (∑ t ∈ Finset.range n, s a * (v a) ^ t * (s b * ((v b)⁻¹) ^ t))
        = s a * s b * (if a = b then (n : ℂ) else 0) := by
    intro a b
    have hg : (v a * (v b)⁻¹) ^ n = 1 := by rw [mul_pow, inv_pow, hvn a, hvn b]; simp
    have hrw : ∀ t, s a * (v a) ^ t * (s b * ((v b)⁻¹) ^ t)
        = (s a * s b) * (v a * (v b)⁻¹) ^ t := fun t => by rw [mul_pow]; ring
    simp_rw [hrw]
    rw [← Finset.mul_sum, geom_sum_rou hg]
    have hiff : (v a * (v b)⁻¹ = 1) ↔ (a = b) := by
      rw [mul_inv_eq_one₀ (hvb0 b)]
      exact ⟨fun h => hdist h, fun h => by rw [h]⟩
    by_cases hab : a = b
    · rw [if_pos (hiff.mpr hab), if_pos hab]
    · rw [if_neg (fun h => hab (hiff.mp h)), if_neg hab]
  have hcomplex : ∑ t ∈ Finset.range n,
      ((∑ a : Fin 4, s a * (v a) ^ t) * (starRingEnd ℂ) (∑ a : Fin 4, s a * (v a) ^ t))
      = (4 * n : ℂ) := by
    have hcj : ∀ t, (starRingEnd ℂ) (∑ a : Fin 4, s a * (v a) ^ t)
        = ∑ b : Fin 4, s b * ((v b)⁻¹) ^ t := by
      intro t
      rw [map_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      simp only [map_mul, map_pow, hsconj b, conj_eq_inv_of_norm_one (hnorm b)]
    simp_rw [hcj, Finset.sum_mul_sum]
    rw [Finset.sum_comm, Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hper a b))]
    have hinner : ∀ a : Fin 4,
        (∑ b : Fin 4, s a * s b * (if a = b then (n : ℂ) else 0)) = s a * s a * n := by
      intro a
      rw [Finset.sum_eq_single a]
      · rw [if_pos rfl]
      · intro b _ hba; rw [if_neg (Ne.symm hba), mul_zero]
      · intro h; exact absurd (Finset.mem_univ a) h
    rw [Finset.sum_congr rfl (fun a _ => hinner a), ← Finset.sum_mul]
    have hs4 : ∑ a : Fin 4, s a * s a = 4 := by simp_rw [hs2]; simp
    rw [hs4]
  have hsum_eq : (∑ t ∈ Finset.range n, ((∑ a : Fin 4, s a * (v a) ^ t) *
        (starRingEnd ℂ) (∑ a : Fin 4, s a * (v a) ^ t)))
      = (↑(∑ t ∈ Finset.range n, ‖∑ a : Fin 4, s a * (v a) ^ t‖ ^ 2) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun t _ => by rw [Complex.mul_conj']; norm_cast)
  rw [hsum_eq] at hcomplex
  exact_mod_cast hcomplex

/-- **The four-term Parseval, specialized.**  For a primitive `n`-th root `ω` (`n ≠ 0`) whose powers
`ω^i, ω^j, ω^k, ω^l` are pairwise distinct, `∑_{t<n} ‖ω^{ti}+ω^{tj}−ω^{tk}−ω^{tl}‖² = 4n`. -/
theorem parseval_fourTerm_pow {n : ℕ} (hn : n ≠ 0) {ω : ℂ} (hω : IsPrimitiveRoot ω n) {i j k l : ℕ}
    (hdist : Function.Injective (![ω ^ i, ω ^ j, ω ^ k, ω ^ l] : Fin 4 → ℂ)) :
    ∑ t ∈ Finset.range n, ‖ω ^ (i * t) + ω ^ (j * t) - ω ^ (k * t) - ω ^ (l * t)‖ ^ 2 = 4 * n := by
  have hωn : ω ^ n = 1 := hω.pow_eq_one
  have hω1 : ‖ω‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hωn hn
  have heq : ∀ t : ℕ, ω ^ (i * t) + ω ^ (j * t) - ω ^ (k * t) - ω ^ (l * t)
      = ∑ a : Fin 4,
          (![1, 1, -1, -1] : Fin 4 → ℂ) a * (![ω ^ i, ω ^ j, ω ^ k, ω ^ l] : Fin 4 → ℂ) a ^ t := by
    intro t; rw [Fin.sum_univ_four]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, pow_mul]; ring
  simp_rw [heq]
  refine parseval_fourTerm _ ?_ ?_ hdist _ ?_ ?_
  · intro a; fin_cases a <;> simp <;> rw [pow_right_comm, hωn, one_pow]
  · intro a; fin_cases a <;> simp [norm_pow, hω1]
  · intro a; fin_cases a <;> norm_num
  · intro a; fin_cases a <;> simp

/-- **AM-GM product bound.**  If the arithmetic mean of nonnegative reals is `≤ B`
(`∑ xᵢ ≤ k·B`, `k = |s|`), then `∏ xᵢ ≤ Bᵏ`.  This feeds the Parseval bound:
`∏_{prim} ‖f(ζ)‖² ≤ 8^{φ(n)}` from `∑ ‖f(ζ)‖² ≤ 4n = φ(n)·8` (`n = 2^m`). -/
theorem prod_le_of_sum_le {ι : Type*} (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i)
    (k : ℕ) (hk : s.card = k) (B : ℝ) (hsum : ∑ i ∈ s, x i ≤ (k : ℝ) * B) :
    ∏ i ∈ s, x i ≤ B ^ k := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0; rw [Finset.card_eq_zero] at hk; subst hk; simp
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
  set w : ι → ℝ := fun _ => (k : ℝ)⁻¹ with hw_def
  have hw : ∀ i ∈ s, 0 ≤ w i := fun i _ => by positivity
  have hwsum : ∑ i ∈ s, w i = 1 := by
    rw [hw_def]; simp only [Finset.sum_const, hk, nsmul_eq_mul]; field_simp
  have hAMGM : ∏ i ∈ s, (x i) ^ (w i) ≤ ∑ i ∈ s, w i * x i :=
    Real.geom_mean_le_arith_mean_weighted s w x hw hwsum hx
  have hLHS : ∏ i ∈ s, (x i) ^ (w i) = (∏ i ∈ s, x i) ^ ((k : ℝ)⁻¹) := by
    rw [hw_def]; exact Real.finset_prod_rpow s x hx _
  have hRHS : ∑ i ∈ s, w i * x i ≤ B := by
    have hsplit : ∑ i ∈ s, w i * x i = (k : ℝ)⁻¹ * ∑ i ∈ s, x i := by
      rw [hw_def, Finset.mul_sum]
    rw [hsplit]
    calc (k : ℝ)⁻¹ * ∑ i ∈ s, x i
        ≤ (k : ℝ)⁻¹ * ((k : ℝ) * B) := by apply mul_le_mul_of_nonneg_left hsum; positivity
      _ = B := by field_simp
  have hcombined : (∏ i ∈ s, x i) ^ ((k : ℝ)⁻¹) ≤ B := by rw [← hLHS]; exact le_trans hAMGM hRHS
  have hprodnn : 0 ≤ ∏ i ∈ s, x i := Finset.prod_nonneg hx
  have key : ((∏ i ∈ s, x i) ^ ((k : ℝ)⁻¹)) ^ k = ∏ i ∈ s, x i :=
    Real.rpow_inv_natCast_pow hprodnn (by omega)
  calc ∏ i ∈ s, x i
      = ((∏ i ∈ s, x i) ^ ((k : ℝ)⁻¹)) ^ k := key.symm
    _ ≤ B ^ k := by apply pow_le_pow_left₀ _ hcombined; positivity

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.parseval_fourTerm
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.parseval_fourTerm_pow
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.prod_le_of_sum_le
