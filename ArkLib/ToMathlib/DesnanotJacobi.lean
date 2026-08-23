/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.MvPolynomial
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The Desnanot–Jacobi identity (updateRow form)

For any square matrix `B` over a commutative ring and indices `i₁ ≠ i₂`,
`c₁ ≠ c₂`:

  `adj B i₁ c₁ * adj B i₂ c₂ − adj B i₁ c₂ * adj B i₂ c₁
     = det B * det ((B.updateRow c₁ (Pi.single i₁ 1)).updateRow c₂ (Pi.single i₂ 1))`

— the 2×2 minors of the adjugate factor through the determinant, with the
complementary cofactor expressed in the same `updateRow` normal form Mathlib
uses for `adjugate_apply` (no submatrix index plumbing).  This is the engine of
Dodgson condensation and, in ArkLib (#371), of the window-pencil coincidence
factorization: the pair-coincidence polynomial of the graded ladder is divisible
by the pencil determinant, with an explicitly degree-bounded quotient.

Proof: Mathlib's `det_adjugate`/`adjugate_adjugate` pattern — establish the
identity for the generic matrix `mvPolynomialX` mapped into its fraction field
(where the matrix is invertible and `U = E·B` splits the updated determinant),
then transfer to every commutative ring by `aeval`.

A candidate for upstreaming to `Mathlib.LinearAlgebra.Matrix.Adjugate`.
-/

open Matrix

namespace ArkLib.DesnanotJacobi

variable {n : Type} [Fintype n] [DecidableEq n]

/-- A permutation all of whose moved points land in `{c₁, c₂}` is the identity
or the transposition `swap c₁ c₂`. -/
theorem perm_eq_one_or_swap {σ : Equiv.Perm n} {c₁ c₂ : n}
    (hkey : ∀ c, σ c ≠ c → σ c = c₁ ∨ σ c = c₂) :
    σ = 1 ∨ σ = Equiv.swap c₁ c₂ := by
  classical
  by_cases hσ1 : σ = 1
  · exact Or.inl hσ1
  refine Or.inr ?_
  -- moved points have σ-order two
  have hmove2 : ∀ c, σ c ≠ c → σ (σ c) ≠ σ c := fun c hc h => hc (σ.injective h)
  have hinv : ∀ c, σ c ≠ c → σ (σ c) = c := by
    intro c hc
    by_contra hne
    have h1 := hkey c hc
    have hm2 := hmove2 c hc
    have h2 := hkey (σ c) hm2
    have hm3 : σ (σ (σ c)) ≠ σ (σ c) := hmove2 (σ c) hm2
    have h4 := hkey (σ (σ c)) hm3
    have h31 : σ (σ (σ c)) = σ c := by
      rcases h1 with f | f <;> rcases h2 with g | g <;> rcases h4 with h | h <;>
        first
          | (exfalso; exact hm2 (g.trans f.symm))
          | (exfalso; exact hm3 (h.trans g.symm))
          | (exact h.trans f.symm)
    exact hne (σ.injective h31)
  -- moved points themselves lie in {c₁, c₂}
  have hsub : ∀ c, σ c ≠ c → c = c₁ ∨ c = c₂ := by
    intro c hc
    have hm2 := hmove2 c hc
    have h2 := hkey (σ c) hm2
    rw [hinv c hc] at h2
    exact h2
  -- extract a moved point and pin the swap values
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    by_contra h
    push_neg at h
    exact hσ1 (Equiv.ext h)
  have hswap : σ c₁ = c₂ ∧ σ c₂ = c₁ := by
    rcases hsub a ha with h | h
    · have h1 : σ a = c₂ := by
        rcases hkey a ha with h' | h'
        · exact absurd (h'.trans h.symm) ha
        · exact h'
      constructor
      · rw [← h]
        exact h1
      · rw [← h1, hinv a ha, h]
    · have h1 : σ a = c₁ := by
        rcases hkey a ha with h' | h'
        · exact h'
        · exact absurd (h'.trans h.symm) ha
      constructor
      · rw [← h1, hinv a ha, h]
      · rw [← h]
        exact h1
  refine Equiv.ext fun x => ?_
  by_cases hx1 : x = c₁
  · subst hx1
    rw [Equiv.swap_apply_left]
    exact hswap.1
  by_cases hx2 : x = c₂
  · subst hx2
    rw [Equiv.swap_apply_right]
    exact hswap.2
  · rw [Equiv.swap_apply_of_ne_of_ne hx1 hx2]
    by_contra hne
    rcases hsub x hne with h | h
    · exact hx1 h
    · exact hx2 h

/-- Determinant of the identity with two rows replaced: only the identity
permutation and the transposition survive. -/
theorem det_one_updateRow_updateRow {K : Type} [CommRing K] {c₁ c₂ : n}
    (hc : c₁ ≠ c₂) (u v : n → K) :
    (((1 : Matrix n n K).updateRow c₁ u).updateRow c₂ v).det
      = u c₁ * v c₂ - u c₂ * v c₁ := by
  classical
  set E := ((1 : Matrix n n K).updateRow c₁ u).updateRow c₂ v with hEdef
  have hErow : ∀ r c, E r c = if r = c₂ then v c else if r = c₁ then u c
      else (1 : Matrix n n K) r c := by
    intro r c
    by_cases h2 : r = c₂
    · subst h2
      rw [hEdef, Matrix.updateRow_self, if_pos rfl]
    · by_cases h1 : r = c₁
      · subst h1
        rw [hEdef, Matrix.updateRow_ne h2, Matrix.updateRow_self, if_neg h2,
          if_pos rfl]
      · rw [hEdef, Matrix.updateRow_ne h2, Matrix.updateRow_ne h1, if_neg h2,
          if_neg h1]
  rw [Matrix.det_apply]
  rw [Finset.sum_eq_add_of_mem (1 : Equiv.Perm n) (Equiv.swap c₁ c₂)
    (Finset.mem_univ _) (Finset.mem_univ _)
    (fun h => hc (by
      have := congrArg (fun σ : Equiv.Perm n => σ c₁) h
      simpa using this))
    ?_]
  · have hid : ((1 : Equiv.Perm n).sign : ℤˣ) • ∏ c, E ((1 : Equiv.Perm n) c) c
        = u c₁ * v c₂ := by
      rw [Equiv.Perm.sign_one, one_smul]
      rw [Finset.prod_eq_mul_of_mem c₁ c₂ (Finset.mem_univ _) (Finset.mem_univ _)
        hc (fun c _ hcc => by
          rw [Equiv.Perm.one_apply, hErow c c, if_neg hcc.2, if_neg hcc.1,
            Matrix.one_apply_eq])]
      rw [Equiv.Perm.one_apply, Equiv.Perm.one_apply, hErow c₁ c₁, if_neg hc,
        if_pos rfl, hErow c₂ c₂, if_pos rfl]
    have hswap : ((Equiv.swap c₁ c₂).sign : ℤˣ) • ∏ c, E (Equiv.swap c₁ c₂ c) c
        = -(u c₂ * v c₁) := by
      rw [Equiv.Perm.sign_swap hc]
      rw [Finset.prod_eq_mul_of_mem c₁ c₂ (Finset.mem_univ _) (Finset.mem_univ _)
        hc (fun c _ hcc => by
          rw [Equiv.swap_apply_of_ne_of_ne hcc.1 hcc.2, hErow c c, if_neg hcc.2,
            if_neg hcc.1, Matrix.one_apply_eq])]
      rw [Equiv.swap_apply_left, Equiv.swap_apply_right, hErow c₂ c₁, if_pos rfl,
        hErow c₁ c₂, if_neg hc, if_pos rfl]
      rw [Units.neg_smul, one_smul]
      ring
    rw [hid, hswap]
    ring
  · intro σ _ hσne
    obtain ⟨hσ1, hσswap⟩ := hσne
    -- some moved column lands outside {c₁, c₂}: the entry is an off-diagonal of 1
    have hexists : ∃ c, σ c ≠ c ∧ σ c ≠ c₁ ∧ σ c ≠ c₂ := by
      by_contra hcon
      push_neg at hcon
      have hkey : ∀ c, σ c ≠ c → σ c = c₁ ∨ σ c = c₂ := by
        intro c hcne
        by_cases h1 : σ c = c₁
        · exact Or.inl h1
        · exact Or.inr (hcon c hcne h1)
      rcases perm_eq_one_or_swap hkey with h | h
      · exact hσ1 h
      · exact hσswap h
    obtain ⟨c, hcne, hc1, hc2⟩ := hexists
    have hzero : E (σ c) c = 0 := by
      rw [hErow (σ c) c, if_neg hc2, if_neg hc1, Matrix.one_apply_ne hcne]
    have hprod : (∏ i, E (σ i) i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ c) hzero
    rw [hprod, smul_zero]

/-- The Desnanot–Jacobi identity over a field, at invertible matrices: split the
doubly-updated determinant through `U = E · M`. -/
theorem desnanot_jacobi_of_isUnit {K : Type} [Field K] {M : Matrix n n K}
    (hM : IsUnit M.det) {i₁ i₂ c₁ c₂ : n} (hc : c₁ ≠ c₂) :
    M.adjugate i₁ c₁ * M.adjugate i₂ c₂ - M.adjugate i₁ c₂ * M.adjugate i₂ c₁
      = M.det * ((M.updateRow c₁ (Pi.single i₁ 1)).updateRow c₂
          (Pi.single i₂ 1)).det := by
  classical
  have hMinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hM
  have hadj : ∀ i j, M.adjugate i j = M.det * M⁻¹ i j := by
    intro i j
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, ← mul_assoc,
      Ring.mul_inverse_cancel _ hM, one_mul]
  -- the factorization U = E * M
  set E := ((1 : Matrix n n K).updateRow c₁ (fun c => M⁻¹ i₁ c)).updateRow c₂
    (fun c => M⁻¹ i₂ c) with hEdef
  have hEM : E * M = (M.updateRow c₁ (Pi.single i₁ 1)).updateRow c₂
      (Pi.single i₂ 1) := by
    ext r c
    rw [Matrix.mul_apply]
    by_cases h2 : r = c₂
    · have hrow : ∀ j, E r j = M⁻¹ i₂ j := fun j => by
        rw [hEdef, h2, Matrix.updateRow_self]
      rw [Finset.sum_congr rfl fun j _ => by rw [hrow j]]
      have hM2 := congrFun (congrFun hMinv i₂) c
      rw [Matrix.mul_apply] at hM2
      rw [hM2, h2, Matrix.updateRow_self]
      rw [Matrix.one_apply, Pi.single_apply]
      by_cases h : i₂ = c
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg (Ne.symm h)]
    · by_cases h1 : r = c₁
      · have hrow : ∀ j, E r j = M⁻¹ i₁ j := fun j => by
          rw [hEdef, h1, Matrix.updateRow_ne hc, Matrix.updateRow_self]
        rw [Finset.sum_congr rfl fun j _ => by rw [hrow j]]
        have hM1 := congrFun (congrFun hMinv i₁) c
        rw [Matrix.mul_apply] at hM1
        rw [hM1, h1, Matrix.updateRow_ne hc, Matrix.updateRow_self]
        rw [Matrix.one_apply, Pi.single_apply]
        by_cases h : i₁ = c
        · rw [if_pos h, if_pos h.symm]
        · rw [if_neg h, if_neg (Ne.symm h)]
      · have hrow : ∀ j, E r j = (1 : Matrix n n K) r j := fun j => by
          rw [hEdef, Matrix.updateRow_ne h2, Matrix.updateRow_ne h1]
        rw [Finset.sum_congr rfl fun j _ => by rw [hrow j]]
        rw [Matrix.updateRow_ne h2, Matrix.updateRow_ne h1]
        simp [Matrix.one_apply]
    -- end ext
  have hdetE : E.det = M⁻¹ i₁ c₁ * M⁻¹ i₂ c₂ - M⁻¹ i₁ c₂ * M⁻¹ i₂ c₁ :=
    det_one_updateRow_updateRow hc _ _
  calc M.adjugate i₁ c₁ * M.adjugate i₂ c₂ - M.adjugate i₁ c₂ * M.adjugate i₂ c₁
      = M.det * M.det * (M⁻¹ i₁ c₁ * M⁻¹ i₂ c₂ - M⁻¹ i₁ c₂ * M⁻¹ i₂ c₁) := by
        rw [hadj, hadj, hadj, hadj]
        ring
    _ = M.det * (E.det * M.det) := by
        rw [hdetE]
        ring
    _ = M.det * ((M.updateRow c₁ (Pi.single i₁ 1)).updateRow c₂
          (Pi.single i₂ 1)).det := by
        rw [← Matrix.det_mul, hEM]

/-- **The Desnanot–Jacobi identity** (updateRow form), over every commutative
ring: 2×2 minors of the adjugate factor through the determinant. -/
theorem desnanot_jacobi {α : Type} [CommRing α] (B : Matrix n n α)
    {i₁ i₂ c₁ c₂ : n} (hc : c₁ ≠ c₂) :
    B.adjugate i₁ c₁ * B.adjugate i₂ c₂ - B.adjugate i₁ c₂ * B.adjugate i₂ c₁
      = B.det * ((B.updateRow c₁ (Pi.single i₁ 1)).updateRow c₂
          (Pi.single i₂ 1)).det := by
  classical
  -- the generic matrix
  let R := MvPolynomial (n × n) ℤ
  let A' : Matrix n n R := mvPolynomialX n n ℤ
  -- the aeval transfer map
  let φ : R →ₐ[ℤ] α := MvPolynomial.aeval fun p : n × n => B p.1 p.2
  have hsingleφ : ∀ i : n, (⇑φ ∘ Pi.single i (1 : R)) = Pi.single i (1 : α) := by
    intro i
    funext x
    by_cases h : x = i
    · subst h
      simp
    · simp [Pi.single_eq_of_ne h]
  suffices h : A'.adjugate i₁ c₁ * A'.adjugate i₂ c₂
      - A'.adjugate i₁ c₂ * A'.adjugate i₂ c₁
      = A'.det * ((A'.updateRow c₁ (Pi.single i₁ 1)).updateRow c₂
          (Pi.single i₂ 1)).det by
    have hB : φ.mapMatrix A' = B := mvPolynomialX_mapMatrix_aeval ℤ B
    have := congrArg φ h
    rw [map_sub, map_mul, map_mul, map_mul] at this
    have hadjφ : ∀ i j, φ (A'.adjugate i j) = B.adjugate i j := by
      intro i j
      rw [show B = φ.mapMatrix A' from hB.symm, ← AlgHom.map_adjugate]
      rfl
    have hdetφ : φ A'.det = B.det := by
      rw [← hB, ← AlgHom.map_det]
    have hupdφ : φ (((A'.updateRow c₁ (Pi.single i₁ 1)).updateRow c₂
        (Pi.single i₂ 1)).det)
        = ((B.updateRow c₁ (Pi.single i₁ 1)).updateRow c₂
            (Pi.single i₂ 1)).det := by
      rw [AlgHom.map_det]
      congr 1
      rw [AlgHom.mapMatrix_apply, Matrix.map_updateRow, Matrix.map_updateRow,
        hsingleφ i₁, hsingleφ i₂, ← AlgHom.mapMatrix_apply, hB]
    rw [hadjφ, hadjφ, hadjφ, hadjφ, hdetφ, hupdφ] at this
    exact this
  -- prove the generic identity inside the fraction field
  let K := FractionRing R
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  apply hinj
  let ψ : R →+* K := algebraMap R K
  have hψadj : ∀ i j, ψ (A'.adjugate i j) = (ψ.mapMatrix A').adjugate i j := by
    intro i j
    rw [← RingHom.map_adjugate]
    rfl
  have hψdet : ψ A'.det = (ψ.mapMatrix A').det := by
    rw [← RingHom.map_det]
  have hsingleψ : ∀ i : n, (⇑ψ ∘ Pi.single i (1 : R)) = Pi.single i (1 : K) := by
    intro i
    funext x
    by_cases h : x = i
    · subst h
      simp
    · simp [Pi.single_eq_of_ne h]
  have hψupd : ψ (((A'.updateRow c₁ (Pi.single i₁ 1)).updateRow c₂
      (Pi.single i₂ 1)).det)
      = (((ψ.mapMatrix A').updateRow c₁ (Pi.single i₁ 1)).updateRow c₂
          (Pi.single i₂ 1)).det := by
    rw [RingHom.map_det]
    congr 1
    rw [RingHom.mapMatrix_apply, Matrix.map_updateRow, Matrix.map_updateRow,
      hsingleψ i₁, hsingleψ i₂, ← RingHom.mapMatrix_apply]
  rw [map_sub, map_mul, map_mul, map_mul, hψadj, hψadj, hψadj, hψadj, hψdet,
    hψupd]
  -- the mapped generic matrix is invertible over the fraction field
  have hdet0 : (ψ.mapMatrix A').det ≠ 0 := by
    rw [← hψdet]
    intro h
    exact det_mvPolynomialX_ne_zero n ℤ (hinj (by rwa [map_zero]))
  exact desnanot_jacobi_of_isUnit (isUnit_iff_ne_zero.mpr hdet0) hc

end ArkLib.DesnanotJacobi

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.DesnanotJacobi.det_one_updateRow_updateRow
#print axioms ArkLib.DesnanotJacobi.desnanot_jacobi_of_isUnit
#print axioms ArkLib.DesnanotJacobi.desnanot_jacobi
