/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26GapCensusLaw
import ArkLib.Data.CodingTheory.ProximityGap.LamLeungUnconditionalGeneral

/-!
# The census classification, characteristic zero: gap-band solutions are antipodal-closed

DISPROOF_LOG O142/O145 verified exactly (three instances, multi-prime intersection) that the
field-independent solutions of the gap-band system over 2-power smooth domains are precisely
the fiber unions, with each finite prime contributing exactly one rotation orbit of
prime-specific halo. This file proves the characteristic-zero layer of that classification —
the layer that *is* the field-independent core (O134/O145: the char-0 census is what every
large prime sees, plus its own halo):

* `subset_neg_mem_of_sum_zero` — the bridge from the in-tree Lam–Leung engine
  (`antipodal_of_sum_zero` / `antipodal_unconditional`): in a characteristic-zero field, any
  *subset* of the `2^m`-th roots of unity whose elements sum to zero is **antipodal-closed**
  (`x ∈ A → −x ∈ A`). This is the subset form of Lam–Leung at 2-powers: vanishing subset
  sums of 2-power roots of unity decompose into antipodal pairs.
* `gapBand_antipodal_charZero` — the census consequence: any gap-band solution `T` (for a
  stack `(X^A, X^B)` with `B < A − 1`, i.e. stride ≥ 2, over a `2^m`-th-root domain in a
  characteristic-zero field) is antipodal-closed — the `e₁`-coefficient of the band forces
  `∑ T = 0` and Lam–Leung does the rest. Antipodal closure *is* the fiber-union property for
  the squaring map: `T` is a union of fibers of `x ↦ x²`.

Why characteristic zero is the right home: for `p ≡ 1 (mod 2^m)` the root powers are NOT
linearly independent over `F_p` (they live in the prime field), and the per-prime halos
(O145: exactly one rotation orbit each at every prime tested) are genuine — the finite-field
classification can only ever be "char-0 core + named no-halo hypothesis," which is exactly
how the O134 correction layer is organized. This file pins the core.

## References
* Issue #357, DISPROOF_LOG O142/O145; the in-tree `LamLeungUnconditionalGeneral`.
-/

set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.KKH26

open Polynomial Finset

/-! ## The subset form of Lam–Leung at 2-powers -/

section Bridge

variable {L : Type*} [Field L] [CharZero L]

/-- **Vanishing subset sums of `2^m`-th roots of unity are antipodal-closed** (the subset
form of the in-tree Lam–Leung engine). If `A` is a finite set of `2^m`-th roots of unity in
a characteristic-zero field and `∑_{x∈A} x = 0`, then `A = −A`. -/
theorem subset_neg_mem_of_sum_zero {ζ : L} {m : ℕ} (hm : 1 ≤ m)
    (hζ : IsPrimitiveRoot ζ (2 ^ m))
    (A : Finset L) (hA : ∀ x ∈ A, x ^ (2 ^ m) = 1)
    (hsum : ∑ x ∈ A, x = 0) :
    ∀ x ∈ A, -x ∈ A := by
  classical
  set N : ℕ := 2 ^ (m - 1) with hN
  have hNN : 2 * N = 2 ^ m := by
    rw [hN, ← pow_succ']
    congr 1
    omega
  have hζN : ζ ^ N = -1 := R12.pow_half_eq_neg_one hm hζ
  -- The indexed set: which antipodal-pair slots land in `A`.
  set E : Finset (Fin N × Bool) :=
    Finset.univ.filter (fun jb => R12.root ζ jb ∈ A) with hE
  -- `root` is injective: the `2N` values `±ζ^j` are the `2N` distinct powers of `ζ`.
  have hroot_pow : ∀ jb : Fin N × Bool,
      R12.root ζ jb = ζ ^ ((jb.1 : ℕ) + if jb.2 then N else 0) := by
    rintro ⟨j, b⟩
    cases b
    · simp [R12.root]
    · simpa using R12.root_true_eq ζ hζN j
  have hinj : Function.Injective (R12.root ζ : Fin N × Bool → L) := by
    rintro ⟨j₁, b₁⟩ ⟨j₂, b₂⟩ heq
    rw [hroot_pow ⟨j₁, b₁⟩, hroot_pow ⟨j₂, b₂⟩] at heq
    have hlt₁ : (j₁ : ℕ) + (if b₁ then N else 0) < 2 ^ m := by
      have := j₁.isLt
      cases b₁ <;> simp <;> omega
    have hlt₂ : (j₂ : ℕ) + (if b₂ then N else 0) < 2 ^ m := by
      have := j₂.isLt
      cases b₂ <;> simp <;> omega
    have := IsPrimitiveRoot.pow_inj hζ hlt₁ hlt₂ heq
    cases b₁ <;> cases b₂ <;> simp_all <;> omega
  -- Every element of `A` is in the image of `root`.
  have hcover : ∀ x ∈ A, ∃ jb : Fin N × Bool, R12.root ζ jb = x := by
    intro x hx
    obtain ⟨i, hilt, hieq⟩ := hζ.eq_pow_of_pow_eq_one (hA x hx)
    rcases Nat.lt_or_ge i N with hi | hi
    · exact ⟨⟨⟨i, hi⟩, false⟩, by simp [R12.root, hieq]⟩
    · refine ⟨⟨⟨i - N, by omega⟩, true⟩, ?_⟩
      have hpow : ζ ^ i = ζ ^ (i - N) * ζ ^ N := by
        rw [← pow_add]
        congr 1
        omega
      simp only [R12.root, if_true]
      rw [← hieq, hpow, hζN]
      ring
  -- `A` is the image of `E` under `root`, so the sums agree.
  have hAimg : A = E.image (R12.root ζ) := by
    ext x
    constructor
    · intro hx
      obtain ⟨jb, hjb⟩ := hcover x hx
      exact Finset.mem_image.mpr ⟨jb, by simp [hE, hjb, hx], hjb⟩
    · intro hx
      obtain ⟨jb, hjb, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hjb).2
  have hEsum : ∑ a ∈ E, R12.root ζ a = 0 := by
    rw [hAimg, Finset.sum_image (fun x _ y _ h => hinj h)] at hsum
    exact hsum
  -- Apply the engine.
  have hpair := R12.antipodal_of_sum_zero (K := ℚ) ζ
    (R12.linearIndependent_pow_primitiveRoot hm hζ) E hEsum
  -- Transfer back: `x = root (j,b) ∈ A`, so `(j,b) ∈ E`, so `(j,!b) ∈ E`, and
  -- `root (j,!b) = −x`.
  intro x hx
  obtain ⟨⟨j, b⟩, hjb⟩ := hcover x hx
  have hmemE : (⟨j, b⟩ : Fin N × Bool) ∈ E := by
    simp [hE, hjb, hx]
  have hmemE' : (⟨j, !b⟩ : Fin N × Bool) ∈ E := by
    cases b
    · exact ((hpair j).mp (by simpa using hmemE))
    · exact ((hpair j).mpr (by simpa using hmemE))
  have hval : R12.root ζ (⟨j, !b⟩ : Fin N × Bool) = -x := by
    cases b <;> simp [R12.root] at hjb ⊢ <;> rw [← hjb] <;> ring
  have := (Finset.mem_filter.mp hmemE').2
  rwa [hval] at this

end Bridge

/-! ## The census consequence -/

variable {L : Type*} [Field L] [CharZero L] [DecidableEq L]

/-- **The characteristic-zero classification, stride ≥ 2:** every gap-band solution over a
`2^m`-th-root domain is antipodal-closed — i.e. a union of fibers of the squaring map. The
band's `e₁` coefficient (present whenever `B < A − 1` and `k ≤ A − 1`) forces `∑ T = 0`,
and the subset Lam–Leung theorem forces the antipodal pairing. Combined with
`fiberUnion_gapBand` (the converse construction) this pins the char-0 census of stride-≥2
two-monomial stacks exactly; the finite-prime census is this core plus the per-prime halo
(O145: one rotation orbit per prime), which is precisely the named no-halo surface. -/
theorem gapBand_antipodal_charZero {ζ : L} {m : ℕ} (hm : 1 ≤ m)
    (hζ : IsPrimitiveRoot ζ (2 ^ m))
    {T : Finset L} (hT : ∀ x ∈ T, x ^ (2 ^ m) = 1)
    {A B k : ℕ} (hk : 1 ≤ k) (hBA1 : B < A - 1) (hkA : k ≤ A - 1) (hA2 : 2 ≤ A)
    (hTcard : T.card = A) {lam : L}
    (hband : GapBand T A B k lam) :
    ∀ x ∈ T, -x ∈ T := by
  classical
  -- The `A − 1` coefficient of the vanishing polynomial is in the off-pivot band.
  have hcoeff : (∏ x ∈ T, (X - C x)).coeff (A - 1) = 0 :=
    hband.1 (A - 1) hkA (by omega) (by omega)
  -- That coefficient is `−∑ T` (Vieta).
  have hQdeg : (∏ x ∈ T, (X - C x)).natDegree = A := by
    rw [natDegree_prod_of_monic _ _ fun c _ => monic_X_sub_C c]
    simp [hTcard]
  have hnext : (∏ x ∈ T, (X - C x)).coeff (A - 1) = -∑ x ∈ T, x := by
    have h1 : (∏ x ∈ T, (X - C x)).nextCoeff = -∑ x ∈ T, x :=
      prod_X_sub_C_nextCoeff (fun x => x)
    have h2 : (∏ x ∈ T, (X - C x)).nextCoeff
        = (∏ x ∈ T, (X - C x)).coeff ((∏ x ∈ T, (X - C x)).natDegree - 1) :=
      nextCoeff_of_natDegree_pos (by rw [hQdeg]; omega)
    rw [h2, hQdeg] at h1
    exact h1
  have hsum : ∑ x ∈ T, x = 0 := by
    have h := hcoeff
    rw [hnext] at h
    exact neg_eq_zero.mp h
  exact subset_neg_mem_of_sum_zero hm hζ T hT hsum

/-! ## Source audit -/

#print axioms subset_neg_mem_of_sum_zero
#print axioms gapBand_antipodal_charZero

end ArkLib.ProximityGap.KKH26
