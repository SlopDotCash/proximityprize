/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26GapCensusLaw

/-!
# Fiber unions satisfy the gap band structurally (the O141/O142 mechanism, formalized)

DISPROOF_LOG O141 identified *why* the KKH26 fiber construction reaches deep radii at
arbitrary fields while generic subsets die: a union of fibers of `x ↦ x^m` satisfies the
gap-band moment constraints **structurally** — for every field at once — because its
vanishing polynomial is a polynomial in `X^m`. O142 then verified (exactly, five primes)
that at the first KKH26-shaped instance these fiber unions are the *only* field-independent
solutions. This file proves the structural half:

* `monic_eq_prod_of_subset_roots` — the (thrice-used, now factored) monic-root-forcing
  argument: a monic polynomial of degree `d` with `d` distinct roots *is* the vanishing
  polynomial of its root set;
* `fiberUnion_vanishing_poly` — the vanishing polynomial of a union of `r` distinct
  `m`-fibers is `∏_{t∈T}(X^m − t)`: a polynomial in `X^m`;
* `fiberUnion_gapBand` — hence the union satisfies `GapBand` for the KKH26 stack
  `(X^{rm}, X^{(r−1)m})` at code degree `< (r−2)m + 1`, with pivot `λ = −∑T`
  (via the in-tree `gap_expansion`);
* `kkh26_badScalar_of_fiberUnion` — composed with `badScalar_of_gapBand`: every fiber-union
  sum is a bad scalar of the KKH26 line. The [KKH26] close-point construction, re-derived
  inside the census framework — and the structural (backward) half of the O142
  classification. The forward half (fiber unions are the *only* field-independent
  solutions) is the remaining open classification, exactly probeable per instance.

## References
* Issue #357, DISPROOF_LOG O141/O142; [KKH26] ePrint 2026/782 Proposition 1.
-/

set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.KKH26

open Polynomial Finset

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Monic root forcing (factored helper).** A monic polynomial of degree `d` that vanishes
on a `d`-element set is the vanishing polynomial of that set. -/
theorem monic_eq_prod_of_subset_roots {P : Polynomial F} {U : Finset F} {d : ℕ}
    (hmonic : P.Monic) (hdeg : P.natDegree = d) (hcard : U.card = d)
    (hroots : ∀ x ∈ U, P.IsRoot x) :
    P = ∏ x ∈ U, (X - C x) := by
  classical
  set Q : Polynomial F := ∏ x ∈ U, (X - C x) with hQ
  have hQmonic : Q.Monic := monic_prod_of_monic _ _ fun c _ => monic_X_sub_C c
  have hQdeg : Q.natDegree = d := by
    rw [hQ, natDegree_prod_of_monic _ _ fun c _ => monic_X_sub_C c]
    simp [hcard]
  by_contra hne
  have hsubne : P - Q ≠ 0 := sub_ne_zero.mpr hne
  have hroots' : ∀ x ∈ U, (P - Q).IsRoot x := by
    intro x hx
    have h2 : Q.IsRoot x := by
      rw [hQ]
      simp only [IsRoot.def, eval_prod, eval_sub, eval_X, eval_C]
      exact Finset.prod_eq_zero hx (by ring)
    have h1 := hroots x hx
    simp only [IsRoot.def, eval_sub] at h1 h2 ⊢
    rw [h1, h2, sub_zero]
  have hdegsub : (P - Q).natDegree < d := by
    have hcoeffd : (P - Q).coeff d = 0 := by
      rw [coeff_sub]
      have h1 : P.coeff d = 1 := by
        have := hmonic.coeff_natDegree
        rwa [hdeg] at this
      have h2 : Q.coeff d = 1 := by
        have := hQmonic.coeff_natDegree
        rwa [hQdeg] at this
      rw [h1, h2, sub_self]
    have hdegle : (P - Q).natDegree ≤ d := by
      refine le_trans (natDegree_sub_le _ _) ?_
      rw [hdeg, hQdeg]; simp
    rcases lt_or_eq_of_le hdegle with h | h
    · exact h
    · exfalso
      have hlc : (P - Q).leadingCoeff = 0 := by
        rw [leadingCoeff, h, hcoeffd]
      exact hsubne (leadingCoeff_eq_zero.mp hlc)
  have hsubroots : U ⊆ (P - Q).roots.toFinset := by
    intro x hx
    rw [Multiset.mem_toFinset, mem_roots hsubne]
    exact hroots' x hx
  have : d ≤ (P - Q).natDegree := by
    calc d = U.card := hcard.symm
      _ ≤ (P - Q).roots.toFinset.card := Finset.card_le_card hsubroots
      _ ≤ Multiset.card (P - Q).roots := Multiset.toFinset_card_le _
      _ ≤ (P - Q).natDegree := (P - Q).card_roots'
  omega

section FiberUnion

variable {m r : ℕ} {T : Finset F} {S : F → Finset F}

/-- Distinct fibers are disjoint: an element's `m`-th power pins its fiber. -/
theorem fiber_pairwise_disjoint (hroot : ∀ t ∈ T, ∀ x ∈ S t, x ^ m = t) :
    ∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → Disjoint (S t₁) (S t₂) := by
  intro t₁ h₁ t₂ h₂ hne
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  exact hne ((hroot t₁ h₁ x hx₁).symm.trans (hroot t₂ h₂ x hx₂))

/-- The cardinality of a fiber union. -/
theorem fiberUnion_card (hcard : ∀ t ∈ T, (S t).card = m)
    (hroot : ∀ t ∈ T, ∀ x ∈ S t, x ^ m = t) :
    (T.biUnion S).card = T.card * m := by
  classical
  rw [Finset.card_biUnion (fiber_pairwise_disjoint hroot)]
  calc ∑ t ∈ T, (S t).card = ∑ _t ∈ T, m := Finset.sum_congr rfl hcard
    _ = T.card * m := by simp [Finset.sum_const, smul_eq_mul]

/-- **The vanishing polynomial of a fiber union is a polynomial in `X^m`:**
`∏_{x ∈ ⋃_{t∈T} S_t} (X − x) = ∏_{t∈T} (X^m − t)`. -/
theorem fiberUnion_vanishing_poly (hm : 1 ≤ m)
    (hcard : ∀ t ∈ T, (S t).card = m)
    (hroot : ∀ t ∈ T, ∀ x ∈ S t, x ^ m = t) :
    (∏ t ∈ T, (X ^ m - C t) : Polynomial F) = ∏ x ∈ T.biUnion S, (X - C x) := by
  classical
  refine monic_eq_prod_of_subset_roots (d := T.card * m) ?_ ?_ ?_ ?_
  · exact monic_prod_of_monic _ _ fun t _ => monic_X_pow_sub_C t (by omega)
  · rw [natDegree_prod_of_monic _ _ fun t _ => monic_X_pow_sub_C t (by omega)]
    calc ∑ t ∈ T, (X ^ m - C t : Polynomial F).natDegree = ∑ _t ∈ T, m :=
          Finset.sum_congr rfl fun t _ => natDegree_X_pow_sub_C
      _ = T.card * m := by simp [Finset.sum_const, smul_eq_mul]
  · rw [fiberUnion_card hcard hroot]
  · intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨t, ht, hxt⟩ := hx
    simp only [IsRoot.def, eval_prod, eval_sub, eval_pow, eval_X, eval_C]
    refine Finset.prod_eq_zero ht ?_
    rw [hroot t ht x hxt]
    ring

/-- **Fiber unions satisfy the gap band structurally.** A union of `r ≥ 2` distinct
`m`-fibers satisfies `GapBand` for the KKH26 stack `(X^{rm}, X^{(r−1)m})` at code degree
`< (r−2)m + 1`, with pivot `λ = −∑T` — in every field, with no arithmetic conditions:
the off-stride coefficients vanish because the vanishing polynomial is a polynomial in
`X^m` (concretely, via `gap_expansion`). -/
theorem fiberUnion_gapBand (hm : 1 ≤ m) (hr : 2 ≤ r) (hT : T.card = r)
    (hcard : ∀ t ∈ T, (S t).card = m)
    (hroot : ∀ t ∈ T, ∀ x ∈ S t, x ^ m = t) :
    GapBand (T.biUnion S) (r * m) ((r - 1) * m) ((r - 2) * m + 1) (-∑ t ∈ T, t) := by
  classical
  obtain ⟨E, hEeq, hEdeg⟩ := gap_expansion T hm (by omega)
  rw [hT] at hEeq hEdeg
  have hvan := fiberUnion_vanishing_poly hm hcard hroot
  -- The coefficients of `∏_{x∈U}(X − x)` are those of `X^{rm} − (∑T)X^{(r−1)m} + E`.
  have hcoeff : ∀ d, (∏ x ∈ T.biUnion S, (X - C x) : Polynomial F).coeff d =
      (X ^ (r * m) - C (∑ t ∈ T, t) * X ^ ((r - 1) * m) + E).coeff d := by
    intro d
    rw [← hvan, hEeq]
  constructor
  · -- off-pivot band
    intro d hkd hdA hdB
    rw [hcoeff d, coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X_pow]
    have hE0 : E.coeff d = 0 :=
      coeff_eq_zero_of_natDegree_lt (by omega : E.natDegree < d)
    simp [show ¬ d = r * m by omega, show ¬ d = (r - 1) * m by omega, hE0]
  · -- pivot
    rw [hcoeff _, coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X_pow]
    have hlt : (r - 2) * m < (r - 1) * m := by
      have : r - 2 < r - 1 := by omega
      exact Nat.mul_lt_mul_of_lt_of_le this le_rfl (by omega)
    have hE0 : E.coeff ((r - 1) * m) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by omega : E.natDegree < (r - 1) * m)
    have hne : ¬ ((r - 1) * m = r * m) := by
      have : (r - 1) * m < r * m := by
        have : r - 1 < r := by omega
        exact Nat.mul_lt_mul_of_lt_of_le this le_rfl (by omega)
      omega
    simp [hne, hE0]

/-- **The KKH26 close-point construction, re-derived through the census framework.** Every
fiber-union sum is a bad scalar of the KKH26 line `(X^{rm}, X^{(r−1)m})` against
polynomials of degree `≤ (r−2)m` at agreement threshold `rm` — structurally, in every
field. This is the backward (construction) half of the O142 classification; the forward
half (fiber unions are the only field-independent gap-band solutions) is the open
classification, exactly probeable per instance. -/
theorem kkh26_badScalar_of_fiberUnion {H : Finset F} (hm : 1 ≤ m) (hr : 2 ≤ r)
    (hT : T.card = r)
    (hcard : ∀ t ∈ T, (S t).card = m)
    (hroot : ∀ t ∈ T, ∀ x ∈ S t, x ^ m = t)
    (hsub : T.biUnion S ⊆ H) :
    ∃ q : Polynomial F, q.natDegree ≤ (r - 2) * m ∧
      r * m ≤ (gapAgreeSet H (r * m) ((r - 1) * m) (-∑ t ∈ T, t) q).card := by
  have hband := fiberUnion_gapBand hm hr hT hcard hroot
  have hcardU : (T.biUnion S).card = r * m := by
    rw [fiberUnion_card hcard hroot, hT]
  have h := badScalar_of_gapBand (k := (r - 2) * m + 1)
    (by omega) ?_ ?_ hsub hcardU hband
  · obtain ⟨q, hq, hagree⟩ := h
    exact ⟨q, by omega, hagree⟩
  · -- B < A
    have : r - 1 < r := by omega
    exact Nat.mul_lt_mul_of_lt_of_le this le_rfl (by omega)
  · -- k ≤ B
    have : r - 2 < r - 1 := by omega
    have := Nat.mul_lt_mul_of_lt_of_le this (le_refl m) (by omega : 0 < m)
    omega

end FiberUnion

/-! ## Source audit -/

#print axioms monic_eq_prod_of_subset_roots
#print axioms fiberUnion_vanishing_poly
#print axioms fiberUnion_gapBand
#print axioms kkh26_badScalar_of_fiberUnion

end ArkLib.ProximityGap.KKH26
