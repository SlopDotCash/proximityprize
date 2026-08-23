/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SidonParsevalBound

/-!
# THE GENERAL DFT PARSEVAL OVER ROOTS OF UNITY (#389)

`SidonParsevalBound.parseval_fourTerm` is the four-term special case of the **general** Parseval
identity for any linear combination of *distinct* `n`-th roots of unity with arbitrary complex
coefficients:

> **`parseval_general`** — `∑_{t<n} ‖∑ₐ sₐ (vₐ)ᵗ‖² = n · ∑ₐ ‖sₐ‖²`.

Off-diagonal terms cancel by the root-of-unity orthogonality (`geom_sum_rou`); the diagonal gives
`n · ‖sₐ‖²` per index.  Specializes to the four-term `S = ∑|coeff|² ∈ {4, 6}` cases that feed the
improved resultant bound (`|Res|² ≤ (2S)^{φ(n)}`).  Axiom-clean.  Issue #389.
-/

open Complex Finset BigOperators
namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

/-- **The general DFT Parseval over the `n`-th roots of unity.**  For pairwise-distinct unit values
`v : ι → ℂ` each an `n`-th root of unity, and *arbitrary* complex coefficients `s : ι → ℂ`,
`∑_{t<n} ‖∑ₐ sₐ (vₐ)ᵗ‖² = n · ∑ₐ ‖sₐ‖²`.  (The four-term case `parseval_fourTerm` is `ι = Fin 4`,
`‖sₐ‖ = 1`, giving `4n`; the doubled `S=6` case is `ι = Fin 3`, `s = ![2,-1,-1]`, giving `6n`.) -/
theorem parseval_general {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (v : ι → ℂ) (hvn : ∀ a, v a ^ n = 1) (hnorm : ∀ a, ‖v a‖ = 1)
    (hdist : Function.Injective v) (s : ι → ℂ) :
    ∑ t ∈ Finset.range n, ‖∑ a, s a * (v a) ^ t‖ ^ 2 = n * ∑ a, ‖s a‖ ^ 2 := by
  have hvb0 : ∀ b, v b ≠ 0 := fun b h => by simpa [h] using hnorm b
  have hper : ∀ a b : ι,
      (∑ t ∈ Finset.range n, s a * (v a) ^ t * ((starRingEnd ℂ) (s b) * ((v b)⁻¹) ^ t))
        = s a * (starRingEnd ℂ) (s b) * (if a = b then (n : ℂ) else 0) := by
    intro a b
    have hg : (v a * (v b)⁻¹) ^ n = 1 := by rw [mul_pow, inv_pow, hvn a, hvn b]; simp
    have hrw : ∀ t, s a * (v a) ^ t * ((starRingEnd ℂ) (s b) * ((v b)⁻¹) ^ t)
        = (s a * (starRingEnd ℂ) (s b)) * (v a * (v b)⁻¹) ^ t := fun t => by rw [mul_pow]; ring
    simp_rw [hrw]
    rw [← Finset.mul_sum, geom_sum_rou hg]
    have hiff : (v a * (v b)⁻¹ = 1) ↔ (a = b) := by
      rw [mul_inv_eq_one₀ (hvb0 b)]; exact ⟨fun h => hdist h, fun h => by rw [h]⟩
    by_cases hab : a = b
    · rw [if_pos (hiff.mpr hab), if_pos hab]
    · rw [if_neg (fun h => hab (hiff.mp h)), if_neg hab]
  have hcomplex : ∑ t ∈ Finset.range n,
      ((∑ a, s a * (v a) ^ t) * (starRingEnd ℂ) (∑ a, s a * (v a) ^ t))
      = (n : ℂ) * ∑ a, ((s a) * (starRingEnd ℂ) (s a)) := by
    have hcj : ∀ t, (starRingEnd ℂ) (∑ a, s a * (v a) ^ t)
        = ∑ b, (starRingEnd ℂ) (s b) * ((v b)⁻¹) ^ t := by
      intro t
      rw [map_sum]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [map_mul, map_pow, conj_eq_inv_of_norm_one (hnorm b)]
    simp_rw [hcj, Finset.sum_mul_sum]
    rw [Finset.sum_comm, Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hper a b))]
    have hinner : ∀ a : ι,
        (∑ b, s a * (starRingEnd ℂ) (s b) * (if a = b then (n : ℂ) else 0))
          = (n : ℂ) * (s a * (starRingEnd ℂ) (s a)) := by
      intro a
      rw [Finset.sum_eq_single a]
      · rw [if_pos rfl]; ring
      · intro b _ hba; rw [if_neg (Ne.symm hba), mul_zero]
      · intro h; exact absurd (Finset.mem_univ a) h
    rw [Finset.sum_congr rfl (fun a _ => hinner a), ← Finset.mul_sum]
  -- transfer back to reals
  have hsq : ∀ a : ι, (s a) * (starRingEnd ℂ) (s a) = ((‖s a‖ ^ 2 : ℝ) : ℂ) := by
    intro a; rw [Complex.mul_conj']; norm_cast
  have hsum_eq : (∑ t ∈ Finset.range n, ((∑ a, s a * (v a) ^ t) *
        (starRingEnd ℂ) (∑ a, s a * (v a) ^ t)))
      = (↑(∑ t ∈ Finset.range n, ‖∑ a, s a * (v a) ^ t‖ ^ 2) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun t _ => by rw [Complex.mul_conj']; norm_cast)
  rw [hsum_eq] at hcomplex
  rw [Finset.sum_congr rfl (fun a _ => hsq a), ← Complex.ofReal_sum, ← Complex.ofReal_natCast,
    ← Complex.ofReal_mul] at hcomplex
  exact_mod_cast hcomplex

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.parseval_general
