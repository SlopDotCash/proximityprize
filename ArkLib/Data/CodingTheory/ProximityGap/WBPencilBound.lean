/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WBPencilAbsorption
import ArkLib.Data.CodingTheory.ProximityGap.WBPencilSubmatrix

/-!
# Theorem WB-1: the Welch–Berlekamp pencil bound (#371)

**For any direction `u₁` that is not itself WB-solvable at slack `w`, at most `w + 2`
scalars `γ` make the line `u₀ + γ·u₁` WB-solvable** — hence (with the absorption
lemma) at most `w + 2` bad scalars at radius `w/n`, for every offset `u₀`.

The proof is a linear-pencil argument with no decoding theory:
* `wbMatrix` — the WB system as an `n × (2w+k+1)` matrix; `WBSolvable ⟺ nontrivial
  kernel` (`wbSolvable_iff_exists_kernel`);
* the far direction anchors an invertible row selection `I` on the `u₁`-matrix
  (`exists_invertible_row_submatrix`);
* the reversed pencil `E(ε) := det(wbMatrix(ε·u₀ + u₁)[I])` is a polynomial of degree
  ≤ `w+1` with `E(0) ≠ 0`;
* the diagonal factorization `det(wbMatrix(u₀ + γ·u₁)[I]) = γ^{w+1}·E(γ⁻¹)` for
  `γ ≠ 0` maps solvable scalars to roots of `E`: at most `w+1` of them, plus
  possibly `γ = 0`.

If `n ≤ 2w+k` every direction is WB-solvable (the system is underdetermined), so the
far hypothesis silently confines the statement to the meaningful range `n ≥ 2w+k+1`
(strictly below the unique-decoding slack).  Downstream: the unconditional
below-UDR MCA bound and the production-floor extension `(1−ρ)/3 → (1−ρ)/2`.
-/

open Finset Polynomial Matrix

namespace ProximityGap.WBPencil

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The Welch–Berlekamp coefficient matrix of a received word `y` at slack `w`:
columns `inl t` carry `x_i^t·y_i` (the locator block), columns `inr s` carry
`−x_i^s` (the numerator block). -/
def wbMatrix (dom : Fin n ↪ F) (k w : ℕ) (y : Fin n → F) :
    Matrix (Fin n) (Fin (w + 1) ⊕ Fin (w + k)) F :=
  fun i => Sum.elim (fun t => (dom i) ^ (t : ℕ) * y i) (fun s => -((dom i) ^ (s : ℕ)))

/-- The locator polynomial of a coefficient vector. -/
noncomputable def locPoly {k w : ℕ} (v : Fin (w + 1) ⊕ Fin (w + k) → F) : F[X] :=
  ∑ t : Fin (w + 1), C (v (Sum.inl t)) * X ^ (t : ℕ)

/-- The numerator polynomial of a coefficient vector. -/
noncomputable def numPoly {k w : ℕ} (v : Fin (w + 1) ⊕ Fin (w + k) → F) : F[X] :=
  ∑ s : Fin (w + k), C (v (Sum.inr s)) * X ^ (s : ℕ)

theorem locPoly_eval {k w : ℕ} (v : Fin (w + 1) ⊕ Fin (w + k) → F) (x : F) :
    (locPoly v).eval x = ∑ t : Fin (w + 1), v (Sum.inl t) * x ^ (t : ℕ) := by
  rw [locPoly, eval_finset_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [eval_mul, eval_C, eval_pow, eval_X]

theorem numPoly_eval {k w : ℕ} (v : Fin (w + 1) ⊕ Fin (w + k) → F) (x : F) :
    (numPoly v).eval x = ∑ s : Fin (w + k), v (Sum.inr s) * x ^ (s : ℕ) := by
  rw [numPoly, eval_finset_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [eval_mul, eval_C, eval_pow, eval_X]

theorem locPoly_natDegree_le {k w : ℕ} (v : Fin (w + 1) ⊕ Fin (w + k) → F) :
    (locPoly v).natDegree ≤ w := by
  refine natDegree_sum_le_of_forall_le _ _ fun t _ => ?_
  calc (C (v (Sum.inl t)) * X ^ (t : ℕ)).natDegree
      ≤ (C (v (Sum.inl t))).natDegree + (X ^ (t : ℕ) : F[X]).natDegree :=
        natDegree_mul_le
    _ ≤ 0 + t := by
        refine Nat.add_le_add (le_of_eq (natDegree_C _)) ?_
        rw [natDegree_X_pow]
    _ ≤ w := by
        have := t.2
        omega

theorem numPoly_natDegree_le {k w : ℕ} (v : Fin (w + 1) ⊕ Fin (w + k) → F) :
    (numPoly v).natDegree ≤ w + k - 1 := by
  refine natDegree_sum_le_of_forall_le _ _ fun s _ => ?_
  calc (C (v (Sum.inr s)) * X ^ (s : ℕ)).natDegree
      ≤ (C (v (Sum.inr s))).natDegree + (X ^ (s : ℕ) : F[X]).natDegree :=
        natDegree_mul_le
    _ ≤ 0 + s := by
        refine Nat.add_le_add (le_of_eq (natDegree_C _)) ?_
        rw [natDegree_X_pow]
    _ ≤ w + k - 1 := by
        have := s.2
        omega

theorem locPoly_coeff {k w : ℕ} (v : Fin (w + 1) ⊕ Fin (w + k) → F) (t : Fin (w + 1)) :
    (locPoly v).coeff (t : ℕ) = v (Sum.inl t) := by
  rw [locPoly, finset_sum_coeff]
  rw [Finset.sum_eq_single t]
  · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
  · intro t' _ hne
    rw [coeff_C_mul, coeff_X_pow, if_neg (by
      intro h
      exact hne (Fin.ext h.symm)), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ t) h

theorem numPoly_coeff {k w : ℕ} (v : Fin (w + 1) ⊕ Fin (w + k) → F) (s : Fin (w + k)) :
    (numPoly v).coeff (s : ℕ) = v (Sum.inr s) := by
  rw [numPoly, finset_sum_coeff]
  rw [Finset.sum_eq_single s]
  · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
  · intro s' _ hne
    rw [coeff_C_mul, coeff_X_pow, if_neg (by
      intro h
      exact hne (Fin.ext h.symm)), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ s) h

/-- The kernel form of the WB system: `mulVec` computes `ℓ_v(x_i)·y_i − R_v(x_i)`. -/
theorem wbMatrix_mulVec {k w : ℕ} (dom : Fin n ↪ F) (y : Fin n → F)
    (v : Fin (w + 1) ⊕ Fin (w + k) → F) (i : Fin n) :
    (wbMatrix dom k w y).mulVec v i
      = (locPoly v).eval (dom i) * y i - (numPoly v).eval (dom i) := by
  simp only [wbMatrix, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr]
  rw [locPoly_eval, numPoly_eval, Finset.sum_mul, sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun t _ => by ring
  · exact Finset.sum_congr rfl fun s _ => by ring

/-- **WB solvability ⟺ nontrivial kernel** (the `ℓ = 0 ⟹ R = 0` collapse needs
`w + k ≤ n`: a numerator with `n` distinct roots and degree `< n` is zero). -/
theorem wbSolvable_iff_exists_kernel (dom : Fin n ↪ F) {k w : ℕ} (hk : 1 ≤ k)
    (hwk : w + k ≤ n) (y : Fin n → F) :
    WBSolvable dom k w y ↔
      ∃ v : Fin (w + 1) ⊕ Fin (w + k) → F, v ≠ 0 ∧
        (wbMatrix dom k w y).mulVec v = 0 := by
  constructor
  · rintro ⟨ℓ, R, hℓ0, hℓdeg, hRdeg, hrel⟩
    refine ⟨Sum.elim (fun t => ℓ.coeff t) (fun s => R.coeff s), ?_, ?_⟩
    · intro h
      apply hℓ0
      ext t'
      by_cases ht' : t' < w + 1
      · have := congrFun h (Sum.inl ⟨t', ht'⟩)
        simpa using this
      · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hℓdeg (by omega))]
        simp
    · funext i
      rw [wbMatrix_mulVec]
      have hℓev : (locPoly (Sum.elim (fun t : Fin (w+1) => ℓ.coeff t)
          (fun s : Fin (w+k) => R.coeff s))).eval (dom i) = ℓ.eval (dom i) := by
        rw [locPoly_eval,
          eval_eq_sum_range' (lt_of_le_of_lt hℓdeg (by omega : w < w + 1)),
          ← Fin.sum_univ_eq_sum_range (fun t => ℓ.coeff t * (dom i) ^ t)]
        simp
      have hRev : (numPoly (Sum.elim (fun t : Fin (w+1) => ℓ.coeff t)
          (fun s : Fin (w+k) => R.coeff s))).eval (dom i) = R.eval (dom i) := by
        rw [numPoly_eval,
          eval_eq_sum_range' (lt_of_le_of_lt hRdeg (by omega : w + k - 1 < w + k)),
          ← Fin.sum_univ_eq_sum_range (fun s => R.coeff s * (dom i) ^ s)]
        simp
      rw [hℓev, hRev, hrel i, Pi.zero_apply, sub_self]
  · rintro ⟨v, hv0, hker⟩
    by_cases hℓ : locPoly v = 0
    · -- the locator block vanishes; the numerator has n distinct roots, so v = 0
      exfalso
      have hRzero : numPoly v = 0 := by
        by_contra hR0
        have hroots : ∀ i : Fin n, (numPoly v).eval (dom i) = 0 := by
          intro i
          have := congrFun hker i
          rw [wbMatrix_mulVec, hℓ, eval_zero, zero_mul, zero_sub,
            Pi.zero_apply, neg_eq_zero] at this
          exact this
        have hcard : n ≤ (numPoly v).roots.card := by
          have hinj : ∀ i j : Fin n, dom i = dom j → i = j := fun i j h =>
            dom.injective h
          have : (Finset.univ.image dom).card = n := by
            rw [Finset.card_image_of_injective _ dom.injective, Finset.card_univ,
              Fintype.card_fin]
          calc n = (Finset.univ.image dom).card := this.symm
            _ ≤ (numPoly v).roots.toFinset.card := by
                refine Finset.card_le_card ?_
                intro x hx
                obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
                rw [Multiset.mem_toFinset, mem_roots hR0]
                exact hroots i
            _ ≤ (numPoly v).roots.card := (numPoly v).roots.toFinset_card_le
        have hdeg := (numPoly v).card_roots'
        have hd := numPoly_natDegree_le v
        omega
      apply hv0
      funext j
      rcases j with t | s
      · have := locPoly_coeff v t
        rw [hℓ] at this
        simpa using this.symm
      · have := numPoly_coeff v s
        rw [hRzero] at this
        simpa using this.symm
    · refine ⟨locPoly v, numPoly v, hℓ, locPoly_natDegree_le v,
        numPoly_natDegree_le v, fun i => ?_⟩
      have := congrFun hker i
      rw [wbMatrix_mulVec, Pi.zero_apply, sub_eq_zero] at this
      exact this

/-! ## The reversed pencil and the bound -/

/-- The reversed-pencil polynomial: `E(ε) = det(wbMatrix(ε·u₀ + u₁)[I])` as a
polynomial in `ε`, of degree ≤ `w+1` (one `ε` per locator column). -/
noncomputable def pencilE (dom : Fin n ↪ F) (k w : ℕ) (u₀ u₁ : Fin n → F)
    (I : Fin (w + 1) ⊕ Fin (w + k) → Fin n) : F[X] :=
  Matrix.det (fun a b => Sum.elim
    (fun t : Fin (w + 1) =>
      C ((dom (I a)) ^ (t : ℕ)) * (X * C (u₀ (I a)) + C (u₁ (I a))))
    (fun s : Fin (w + k) => C (-((dom (I a)) ^ (s : ℕ)))) b)

theorem pencilE_eval (dom : Fin n ↪ F) (k w : ℕ) (u₀ u₁ : Fin n → F)
    (I : Fin (w + 1) ⊕ Fin (w + k) → Fin n) (ε : F) :
    (pencilE dom k w u₀ u₁ I).eval ε
      = ((wbMatrix dom k w (fun i => ε * u₀ i + u₁ i)).submatrix I id).det := by
  rw [pencilE, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  funext a b
  rcases b with t | s
  · show Polynomial.eval ε (C ((dom (I a)) ^ (t : ℕ))
        * (X * C (u₀ (I a)) + C (u₁ (I a))))
      = (dom (I a)) ^ (t : ℕ) * (ε * u₀ (I a) + u₁ (I a))
    rw [eval_mul, eval_C, eval_add, eval_mul, eval_X, eval_C, eval_C]
  · show Polynomial.eval ε (C (-((dom (I a)) ^ (s : ℕ))))
      = -((dom (I a)) ^ (s : ℕ))
    rw [eval_C]

theorem pencilE_eval_zero (dom : Fin n ↪ F) (k w : ℕ) (u₀ u₁ : Fin n → F)
    (I : Fin (w + 1) ⊕ Fin (w + k) → Fin n) :
    (pencilE dom k w u₀ u₁ I).eval 0
      = ((wbMatrix dom k w u₁).submatrix I id).det := by
  rw [pencilE_eval]
  congr 1
  funext a b
  rcases b with t | s <;> simp [wbMatrix]

theorem pencilE_natDegree_le (dom : Fin n ↪ F) (k w : ℕ) (u₀ u₁ : Fin n → F)
    (I : Fin (w + 1) ⊕ Fin (w + k) → Fin n) :
    (pencilE dom k w u₀ u₁ I).natDegree ≤ w + 1 := by
  classical
  have hentry : ∀ (a b : Fin (w + 1) ⊕ Fin (w + k)),
      ((Sum.elim
        (fun t : Fin (w + 1) =>
          C ((dom (I a)) ^ (t : ℕ)) * (X * C (u₀ (I a)) + C (u₁ (I a))))
        (fun s : Fin (w + k) => C (-((dom (I a)) ^ (s : ℕ)))) b : F[X])).natDegree
        ≤ Sum.elim (fun _ : Fin (w + 1) => 1) (fun _ : Fin (w + k) => 0) b := by
    intro a b
    rcases b with t | s
    · simp only [Sum.elim_inl]
      calc (C ((dom (I a)) ^ (t : ℕ)) * (X * C (u₀ (I a)) + C (u₁ (I a)))).natDegree
          ≤ (C ((dom (I a)) ^ (t : ℕ))).natDegree
            + (X * C (u₀ (I a)) + C (u₁ (I a))).natDegree := natDegree_mul_le
        _ ≤ 0 + 1 := by
            refine Nat.add_le_add (le_of_eq (natDegree_C _)) ?_
            refine le_trans (natDegree_add_le _ _) ?_
            refine max_le ?_ ?_
            · refine le_trans natDegree_mul_le ?_
              rw [natDegree_X, natDegree_C]
            · rw [natDegree_C]
              omega
        _ = 1 := by omega
    · simp only [Sum.elim_inr, natDegree_C, le_refl]
  rw [pencilE, Matrix.det_apply]
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  have hprod' : (∏ b : Fin (w + 1) ⊕ Fin (w + k),
      (fun a b => Sum.elim
        (fun t : Fin (w + 1) =>
          C ((dom (I a)) ^ (t : ℕ)) * (X * C (u₀ (I a)) + C (u₁ (I a))))
        (fun s : Fin (w + k) => C (-((dom (I a)) ^ (s : ℕ)))) b) (σ b) b).natDegree
      ≤ w + 1 := by
    refine le_trans (natDegree_prod_le _ _) ?_
    calc ∑ b : Fin (w + 1) ⊕ Fin (w + k), ((fun a b => Sum.elim
          (fun t : Fin (w + 1) =>
            C ((dom (I a)) ^ (t : ℕ)) * (X * C (u₀ (I a)) + C (u₁ (I a))))
          (fun s : Fin (w + k) => C (-((dom (I a)) ^ (s : ℕ)))) b) (σ b) b).natDegree
        ≤ ∑ b : Fin (w + 1) ⊕ Fin (w + k),
            Sum.elim (fun _ : Fin (w + 1) => 1) (fun _ : Fin (w + k) => 0) b :=
          Finset.sum_le_sum fun b _ => hentry (σ b) b
      _ = w + 1 := by
          rw [Fintype.sum_sum_type]
          simp
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h, one_smul]
    exact hprod'
  · rw [h]
    refine le_trans (le_of_eq ?_) hprod'
    rw [Units.neg_smul, one_smul, natDegree_neg]

/-- **The diagonal factorization**: for `γ ≠ 0`,
`det(wbMatrix(u₀ + γ·u₁)[I]) = γ^{w+1} · E(γ⁻¹)`. -/
theorem det_line_eq_pow_mul_pencilE (dom : Fin n ↪ F) (k w : ℕ) (u₀ u₁ : Fin n → F)
    (I : Fin (w + 1) ⊕ Fin (w + k) → Fin n) {γ : F} (hγ : γ ≠ 0) :
    ((wbMatrix dom k w (fun i => u₀ i + γ * u₁ i)).submatrix I id).det
      = γ ^ (w + 1) * (pencilE dom k w u₀ u₁ I).eval γ⁻¹ := by
  rw [pencilE_eval]
  have hfac : (wbMatrix dom k w (fun i => u₀ i + γ * u₁ i)).submatrix I id
      = ((wbMatrix dom k w (fun i => γ⁻¹ * u₀ i + u₁ i)).submatrix I id)
        * Matrix.diagonal (Sum.elim (fun _ : Fin (w + 1) => γ)
            (fun _ : Fin (w + k) => 1)) := by
    funext a b
    rw [Matrix.mul_diagonal]
    rcases b with t | s
    · show (dom (I a)) ^ (t : ℕ) * (u₀ (I a) + γ * u₁ (I a))
        = (dom (I a)) ^ (t : ℕ) * (γ⁻¹ * u₀ (I a) + u₁ (I a)) * γ
      have hcomb : (γ⁻¹ * u₀ (I a) + u₁ (I a)) * γ = u₀ (I a) + γ * u₁ (I a) := by
        rw [add_mul, mul_comm γ⁻¹ (u₀ (I a)), mul_assoc, inv_mul_cancel₀ hγ, mul_one,
          mul_comm (u₁ (I a)) γ]
      rw [mul_assoc, hcomb]
    · show -((dom (I a)) ^ (s : ℕ)) = -((dom (I a)) ^ (s : ℕ)) * 1
      rw [mul_one]
  rw [hfac, Matrix.det_mul, Matrix.det_diagonal]
  have hdiag : (∏ b : Fin (w + 1) ⊕ Fin (w + k),
      Sum.elim (fun _ : Fin (w + 1) => γ) (fun _ : Fin (w + k) => (1 : F)) b)
      = γ ^ (w + 1) := by
    rw [Fintype.prod_sum_type]
    simp
  rw [hdiag]
  ring

open Classical in
/-- **THEOREM WB-1 (the Welch–Berlekamp pencil bound).**  If the direction `u₁` is
not itself WB-solvable at slack `w`, then at most `w + 2` scalars make the line
`u₀ + γ·u₁` WB-solvable — for EVERY offset `u₀`.  (When `n ≤ 2w+k` the hypothesis
is unsatisfiable, so the theorem lives strictly below the unique-decoding slack.) -/
theorem wbSolvable_line_card_le (dom : Fin n ↪ F) {k w : ℕ} (hk : 1 ≤ k)
    (hwk : w + k ≤ n) {u₀ u₁ : Fin n → F}
    (hfar : ¬ WBSolvable dom k w u₁) :
    (Finset.univ.filter (fun γ : F =>
      WBSolvable dom k w (fun i => u₀ i + γ * u₁ i))).card ≤ w + 2 := by
  -- the far direction anchors an invertible row selection
  have hker : ∀ v : Fin (w + 1) ⊕ Fin (w + k) → F,
      (wbMatrix dom k w u₁).mulVec v = 0 → v = 0 := by
    intro v hv
    by_contra hv0
    exact hfar ((wbSolvable_iff_exists_kernel dom hk hwk u₁).mpr ⟨v, hv0, hv⟩)
  obtain ⟨I, hIinj, hIdet⟩ := exists_invertible_row_submatrix
    (wbMatrix dom k w u₁) hker
  set E : F[X] := pencilE dom k w u₀ u₁ I with hE
  have hE0 : E.eval 0 ≠ 0 := by
    rw [hE, pencilE_eval_zero]
    exact hIdet
  have hEne : E ≠ 0 := fun h => hE0 (by rw [h, eval_zero])
  -- every nonzero solvable scalar inverts into a root of E
  have hroot : ∀ γ : F, γ ≠ 0 →
      WBSolvable dom k w (fun i => u₀ i + γ * u₁ i) → E.eval γ⁻¹ = 0 := by
    intro γ hγ hsolv
    obtain ⟨v, hv0, hvker⟩ :=
      (wbSolvable_iff_exists_kernel dom hk hwk _).mp hsolv
    have hsq : ((wbMatrix dom k w (fun i => u₀ i + γ * u₁ i)).submatrix I id).det
        = 0 := by
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      refine ⟨v, hv0, ?_⟩
      funext a
      have := congrFun hvker (I a)
      simpa [Matrix.mulVec, Matrix.submatrix_apply, dotProduct] using this
    rw [det_line_eq_pow_mul_pencilE dom k w u₀ u₁ I hγ] at hsq
    rcases mul_eq_zero.mp hsq with h | h
    · exact absurd h (pow_ne_zero _ hγ)
    · exact h
  -- count: the nonzero solvable scalars inject into the roots of E
  set S := Finset.univ.filter (fun γ : F =>
    WBSolvable dom k w (fun i => u₀ i + γ * u₁ i)) with hS
  have hsub : S.erase 0 ⊆ (E.roots.toFinset).image (fun x => x⁻¹) := by
    intro γ hγ
    have hγ0 : γ ≠ 0 := Finset.ne_of_mem_erase hγ
    have hγS := Finset.mem_of_mem_erase hγ
    have hsolv := (Finset.mem_filter.mp hγS).2
    refine Finset.mem_image.mpr ⟨γ⁻¹, ?_, inv_inv γ⟩
    rw [Multiset.mem_toFinset, mem_roots hEne]
    exact hroot γ hγ0 hsolv
  calc S.card ≤ (insert (0 : F) (S.erase 0)).card := Finset.card_le_card (by
        intro γ hγ
        by_cases h0 : γ = 0
        · subst h0
          exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨h0, hγ⟩))
    _ ≤ (S.erase 0).card + 1 := Finset.card_insert_le _ _
    _ ≤ ((E.roots.toFinset).image (fun x => x⁻¹)).card + 1 :=
        Nat.add_le_add_right (Finset.card_le_card hsub) 1
    _ ≤ E.roots.toFinset.card + 1 :=
        Nat.add_le_add_right Finset.card_image_le 1
    _ ≤ E.roots.card + 1 := Nat.add_le_add_right (E.roots.toFinset_card_le) 1
    _ ≤ E.natDegree + 1 := Nat.add_le_add_right (E.card_roots') 1
    _ ≤ (w + 1) + 1 := Nat.add_le_add_right (pencilE_natDegree_le dom k w u₀ u₁ I) 1
    _ = w + 2 := by omega

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.wbSolvable_iff_exists_kernel
#print axioms ProximityGap.WBPencil.pencilE_natDegree_le
#print axioms ProximityGap.WBPencil.det_line_eq_pow_mul_pencilE
#print axioms ProximityGap.WBPencil.wbSolvable_line_card_le
