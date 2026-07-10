/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Determinant certificate from a unique support-perfect matching

A simultaneous alternative to sequential leaf elimination is to select a square minor whose
nonzero-entry bipartite graph has a unique perfect matching.  In the Leibniz expansion every other
permutation term contains a zero entry, so the determinant is the single surviving signed product.
There is no cancellation and no elimination order is required.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.UniqueMatchingMinor

variable {R I : Type} [CommRing R] [Fintype I] [DecidableEq I]

/-- Exact determinant when one permutation is the unique support-perfect matching. -/
theorem det_eq_term_of_unique_nonzero_permutation
    (M : Matrix I I R) (sigma₀ : Equiv.Perm I)
    (hunique : ∀ sigma : Equiv.Perm I, sigma ≠ sigma₀ →
      ∃ i, M (sigma i) i = 0) :
    M.det = Equiv.Perm.sign sigma₀ • ∏ i, M (sigma₀ i) i := by
  rw [Matrix.det_apply]
  apply Finset.sum_eq_single sigma₀
  · intro sigma _hsigma hne
    obtain ⟨i, hi⟩ := hunique sigma hne
    have hprod : ∏ j, M (sigma j) j = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hi
    rw [hprod, smul_zero]
  · intro hnot
    exact (hnot (Finset.mem_univ sigma₀)).elim

/-- A unique support-perfect matching with a nonzero surviving term gives a nonsingular minor. -/
theorem det_ne_zero_of_unique_nonzero_permutation
    (M : Matrix I I R) (sigma₀ : Equiv.Perm I)
    (hunique : ∀ sigma : Equiv.Perm I, sigma ≠ sigma₀ →
      ∃ i, M (sigma i) i = 0)
    (hterm : Equiv.Perm.sign sigma₀ • ∏ i, M (sigma₀ i) i ≠ 0) :
    M.det ≠ 0 := by
  rw [det_eq_term_of_unique_nonzero_permutation M sigma₀ hunique]
  exact hterm

/-- Factorwise form over a domain: nonzero entries along the unique matching suffice. -/
theorem det_ne_zero_of_unique_matching
    [IsDomain R] (M : Matrix I I R) (sigma₀ : Equiv.Perm I)
    (hunique : ∀ sigma : Equiv.Perm I, sigma ≠ sigma₀ →
      ∃ i, M (sigma i) i = 0)
    (hdiag : ∀ i, M (sigma₀ i) i ≠ 0) :
    M.det ≠ 0 := by
  apply det_ne_zero_of_unique_nonzero_permutation M sigma₀ hunique
  have hprod : (∏ i : I, M (sigma₀ i) i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _hi => hdiag i
  exact (smul_ne_zero_iff_ne (Equiv.Perm.sign sigma₀)).mpr hprod

/-- A dense `2 × 2` block already forbids support-level uniqueness: besides the identity matching,
the transposition matching also has no zero entry.  Vandermonde component blocks in the P1
operator are dense on the nonzero evaluation domain, so a raw unique-support-matching argument
cannot see their nonsingularity; it must use determinant algebra inside each block. -/
theorem not_unique_refl_of_dense_fin_two
    (M : Matrix (Fin 2) (Fin 2) R) (hdense : ∀ i j, M i j ≠ 0) :
    ¬(∀ sigma : Equiv.Perm (Fin 2), sigma ≠ Equiv.refl (Fin 2) →
      ∃ i, M (sigma i) i = 0) := by
  intro hunique
  let tau : Equiv.Perm (Fin 2) := Equiv.swap (0 : Fin 2) 1
  have htau : tau ≠ Equiv.refl (Fin 2) := by
    intro h
    have hzero := DFunLike.congr_fun h (0 : Fin 2)
    simp [tau] at hzero
  obtain ⟨i, hi⟩ := hunique tau htau
  exact hdense (tau i) i hi

end ArkLib.ProximityGap.Frontier.UniqueMatchingMinor

#print axioms ArkLib.ProximityGap.Frontier.UniqueMatchingMinor.det_eq_term_of_unique_nonzero_permutation
#print axioms ArkLib.ProximityGap.Frontier.UniqueMatchingMinor.det_ne_zero_of_unique_nonzero_permutation
#print axioms ArkLib.ProximityGap.Frontier.UniqueMatchingMinor.det_ne_zero_of_unique_matching
#print axioms ArkLib.ProximityGap.Frontier.UniqueMatchingMinor.not_unique_refl_of_dense_fin_two
