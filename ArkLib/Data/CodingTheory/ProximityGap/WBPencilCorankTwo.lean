/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WBPencilWindowLaw

/-!
# WB-5: the corank-2 count — pairwise coincidence cracks the multi-parameter wall (#371)

One slice above the boundary (`n = 2w+k−1`) the window pencil has generic corank
2 and the WB-4 anchor provably dies (`windowPencil_adjugate_eq_zero_of_lt_boundary`).
This file proves the corank-2 counting law with the SAME adjugate/updateRow
toolkit, one level deeper:

* the **double-update anchor**: `B₂ := B.updateRow c₀ (single cs 1) |>.updateRow
  c₀' (single cs' 1)` with `det B₂ ≢ 0` — its two adjugate columns `K¹, K²`
  (γ-polynomial entries, degree ≤ w+1) SPAN every evaluated kernel where the
  determinant survives: `det(γ)·v = v_{cs}·K¹(γ) + v_{cs'}·K²(γ)`;
* a bad scalar with error set `E` (`|E| ≥ 2`) forces, for every pair `i ≠ j ∈ E`,
  the **pair-coincidence polynomial** `g_{ij} := G¹_i·G²_j − G¹_j·G²_i`
  (degree ≤ 2w+2; `Gᵇ_i` = the locator block of `Kᵇ` evaluated at `x_i`) to
  vanish at `γ` — eliminating the two kernel parameters pairwise converts the
  multi-parameter split-incidence problem into univariate root counting;
* small-error-set scalars (`|E| ≤ 1`) share witness sets of size ≥ n−1, of which
  there are only n+1: the in-tree rigidity (`unique_bad_gamma_common_witness`)
  caps the class at n+1.

**`badScalars_card_le_of_corank2`**: under the double anchor and twin-freeness
(`g_{ij} ≠ 0` for all `i ≠ j` — the named residual; the twin classes are where
the normalizer/Möbius alignment families live),

  `#bad ≤ (w+1) + (n+1) + n²·(2w+2)`.

Probe record (`probe_wb_corank2_coincidence.py`, `probe_wb_corank2_qscaling.py`):
generic corank exactly 2 at the slice (222/222); the coincidence necessary
condition has 0 violations at q = 449; max bad saturates at exactly `C(n,2)` —
inside this budget.  Applies at EVERY radius `δ ≤ w/n` (no slice hypothesis) —
in particular it also covers the corank-2 (class-V) part of `UnanchoredLinear`.
-/

open Finset Polynomial Matrix
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The doubly-updated square selection: rows `c₀, c₀'` replaced by coordinate
singletons. -/
noncomputable def pencilSqDU (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) (c₀ c₀' cs cs' : WCol n k w) :
    Matrix (WCol n k w) (WCol n k w) F[X] :=
  (((windowPencil dom k w ℓ₀ R₀ ℓ₁ R₁).submatrix J id).updateRow c₀
    (Pi.single cs 1)).updateRow c₀' (Pi.single cs' 1)

/-- The two Cramer kernel candidates: adjugate columns `c₀` and `c₀'`. -/
noncomputable def pencilK (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) (c₀ c₀' cs cs' : WCol n k w)
    (col : WCol n k w) : WCol n k w → F[X] :=
  fun i => (pencilSqDU dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs').adjugate i col

/-- The locator-block evaluation polynomials of an adjugate column. -/
noncomputable def pencilG (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) (c₀ c₀' cs cs' col : WCol n k w)
    (i : Fin n) : F[X] :=
  ∑ t : Fin (w + 1),
    pencilK dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' col (Sum.inl t) * C ((dom i) ^ (t : ℕ))

/-- The pair-coincidence polynomial of a domain pair. -/
noncomputable def coincPoly (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) (c₀ c₀' cs cs' : WCol n k w)
    (i j : Fin n) : F[X] :=
  pencilG dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' c₀ i
      * pencilG dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' c₀' j
    - pencilG dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' c₀ j
      * pencilG dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' c₀' i

/-! ## Degree bounds -/

theorem pencilSqDU_natDegree_le (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) (c₀ c₀' cs cs' : WCol n k w)
    (a b : WCol n k w) :
    ((pencilSqDU dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs') a b).natDegree
      ≤ Sum.elim (fun _ : Fin (w + 1) => 1)
          (Sum.elim (fun _ : Fin (w + k) => 0) (fun _ : Fin (3 * w + k - n) => 0)) b := by
  rw [pencilSqDU, Matrix.updateRow_apply, Matrix.updateRow_apply]
  by_cases ha' : a = c₀'
  · rw [if_pos ha']
    by_cases hb : b = cs'
    · rw [Pi.single_apply, if_pos hb]
      rcases b with t | s | m <;> simp
    · rw [Pi.single_apply, if_neg hb]
      rcases b with t | s | m <;> simp
  · rw [if_neg ha']
    by_cases ha : a = c₀
    · rw [if_pos ha]
      by_cases hb : b = cs
      · rw [Pi.single_apply, if_pos hb]
        rcases b with t | s | m <;> simp
      · rw [Pi.single_apply, if_neg hb]
        rcases b with t | s | m <;> simp
    · rw [if_neg ha]
      exact windowPencil_natDegree_le dom k w ℓ₀ R₀ ℓ₁ R₁ (J a) b

theorem pencilSqDU_det_natDegree_le (dom : Fin n ↪ F) (k w : ℕ)
    (ℓ₀ R₀ ℓ₁ R₁ : F[X]) (J : WCol n k w → Fin (3 * w + k))
    (c₀ c₀' cs cs' : WCol n k w) :
    (pencilSqDU dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs').det.natDegree ≤ w + 1 := by
  refine le_trans (natDegree_det_le_sum_colBound _
    (Sum.elim (fun _ : Fin (w + 1) => 1)
      (Sum.elim (fun _ : Fin (w + k) => 0) (fun _ : Fin (3 * w + k - n) => 0)))
    (pencilSqDU_natDegree_le dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs'))
    (le_of_eq (windowPencil_colBound_sum n k w))

theorem pencilK_natDegree_le (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) (c₀ c₀' cs cs' col i : WCol n k w) :
    (pencilK dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' col i).natDegree ≤ w + 1 := by
  classical
  rw [pencilK, Matrix.adjugate_apply]
  refine le_trans (natDegree_det_le_sum_colBound _
    (Sum.elim (fun _ : Fin (w + 1) => 1)
      (Sum.elim (fun _ : Fin (w + k) => 0) (fun _ : Fin (3 * w + k - n) => 0))) ?_)
    (le_of_eq (windowPencil_colBound_sum n k w))
  intro a b
  rw [Matrix.updateRow_apply]
  by_cases ha : a = col
  · rw [if_pos ha]
    by_cases hb : b = i
    · rw [Pi.single_apply, if_pos hb]
      rcases b with t | s | m <;> simp
    · rw [Pi.single_apply, if_neg hb]
      rcases b with t | s | m <;> simp
  · rw [if_neg ha]
    exact pencilSqDU_natDegree_le dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' a b

theorem pencilG_natDegree_le (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) (c₀ c₀' cs cs' col : WCol n k w) (i : Fin n) :
    (pencilG dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' col i).natDegree ≤ w + 1 := by
  refine natDegree_sum_le_of_forall_le _ _ fun t _ => ?_
  calc (pencilK dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' col (Sum.inl t)
        * C ((dom i) ^ (t : ℕ))).natDegree
      ≤ (pencilK dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' col (Sum.inl t)).natDegree
        + (C ((dom i) ^ (t : ℕ)) : F[X]).natDegree := natDegree_mul_le
    _ ≤ (w + 1) + 0 := Nat.add_le_add
        (pencilK_natDegree_le dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' col _)
        (le_of_eq (natDegree_C _))
    _ = w + 1 := by omega

theorem coincPoly_natDegree_le (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) (c₀ c₀' cs cs' : WCol n k w) (i j : Fin n) :
    (coincPoly dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' i j).natDegree ≤ 2 * w + 2 := by
  rw [coincPoly]
  refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_) <;>
  · refine le_trans natDegree_mul_le ?_
    have h1 := pencilG_natDegree_le dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs'
    calc _ ≤ (w + 1) + (w + 1) := Nat.add_le_add (h1 _ _) (h1 _ _)
      _ = 2 * w + 2 := by omega

/-! ## The span lemma -/

/-- **The corank-2 span**: wherever the double-update determinant survives, every
evaluated kernel vector of the full pencil is the explicit combination of the two
adjugate columns: `det(γ)·v = v_{cs}·K¹(γ) + v_{cs'}·K²(γ)`. -/
theorem corank2_span (dom : Fin n ↪ F) {k w : ℕ} {ℓ₀ R₀ ℓ₁ R₁ : F[X]}
    {J : WCol n k w → Fin (3 * w + k)} {c₀ c₀' cs cs' : WCol n k w}
    (hcc : c₀ ≠ c₀') {γ : F}
    {v : WCol n k w → F}
    (hv : ((windowPencil dom k w ℓ₀ R₀ ℓ₁ R₁).map (Polynomial.eval γ)).mulVec v = 0)
    (hdet : ((pencilSqDU dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs').det).eval γ ≠ 0) :
    ∀ b, ((pencilSqDU dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs').det).eval γ * v b
      = v cs * (pencilK dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' c₀ b).eval γ
        + v cs' * (pencilK dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' c₀' b).eval γ := by
  classical
  set B2 := pencilSqDU dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' with hB2def
  set Bev := B2.map (Polynomial.eval γ) with hBevdef
  -- the evaluated determinant and adjugate
  have hadj : Bev.adjugate = (B2.adjugate).map (Polynomial.eval γ) := by
    have h := RingHom.map_adjugate (Polynomial.evalRingHom γ) B2
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at h
    rw [hBevdef]
    exact h.symm
  have hdetev : Bev.det = (B2.det).eval γ := by
    rw [hBevdef, ← Polynomial.coe_evalRingHom, ← RingHom.mapMatrix_apply,
      ← RingHom.map_det]
  -- B₂(γ) · v = v_{cs}·e_{c₀} + v_{cs'}·e_{c₀'}
  have hBv : ∀ a, Bev a ⬝ᵥ v
      = (if a = c₀' then v cs' else if a = c₀ then v cs else 0) := by
    intro a
    by_cases ha' : a = c₀'
    · subst ha'
      have hrow : Bev a = Pi.single cs' 1 := by
        rw [hBevdef, hB2def, pencilSqDU]
        funext b
        rw [Matrix.map_apply, Matrix.updateRow_self]
        by_cases hb : b = cs'
        · subst hb
          rw [Pi.single_eq_same, Pi.single_eq_same]
          simp
        · rw [Pi.single_eq_of_ne hb, Pi.single_eq_of_ne hb]
          simp
      rw [hrow, single_dotProduct, one_mul, if_pos rfl]
    · by_cases ha : a = c₀
      · subst ha
        have hrow : Bev a = Pi.single cs 1 := by
          rw [hBevdef, hB2def, pencilSqDU]
          funext b
          rw [Matrix.map_apply, Matrix.updateRow_ne ha', Matrix.updateRow_self]
          by_cases hb : b = cs
          · subst hb
            rw [Pi.single_eq_same, Pi.single_eq_same]
            simp
          · rw [Pi.single_eq_of_ne hb, Pi.single_eq_of_ne hb]
            simp
        rw [hrow, single_dotProduct, one_mul, if_neg ha', if_pos rfl]
      · have hrow : Bev a = fun b =>
            ((windowPencil dom k w ℓ₀ R₀ ℓ₁ R₁).map (Polynomial.eval γ)) (J a) b := by
          rw [hBevdef, hB2def, pencilSqDU]
          funext b
          rw [Matrix.map_apply, Matrix.updateRow_ne ha', Matrix.updateRow_ne ha,
            Matrix.submatrix_apply, Matrix.map_apply]
          rfl
        rw [hrow, if_neg ha', if_neg ha]
        have := congrFun hv (J a)
        simpa [Matrix.mulVec, dotProduct] using this
  -- the two adjugate columns
  have hBK : ∀ (col : WCol n k w) a, Bev a ⬝ᵥ (fun i => (B2.adjugate i col).eval γ)
      = Bev.det * (1 : Matrix (WCol n k w) (WCol n k w) F) a col := by
    intro col a
    have hmul := congrFun (congrFun (Matrix.mul_adjugate Bev) a) col
    rw [Matrix.smul_apply, smul_eq_mul] at hmul
    rw [← hmul, Matrix.mul_apply]
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hadj, Matrix.map_apply]
  -- the cross combination dies
  set u' : WCol n k w → F := fun b => Bev.det * v b
    - v cs * (B2.adjugate b c₀).eval γ - v cs' * (B2.adjugate b c₀').eval γ
    with hu'def
  have hu'app : ∀ b, u' b = Bev.det * v b
      - v cs * (B2.adjugate b c₀).eval γ - v cs' * (B2.adjugate b c₀').eval γ :=
    fun b => by rw [hu'def]
  have hBu' : Bev.mulVec u' = 0 := by
    funext a
    show Bev a ⬝ᵥ u' = 0
    have hsplit : Bev a ⬝ᵥ u' = Bev.det * (Bev a ⬝ᵥ v)
        - v cs * (Bev a ⬝ᵥ (fun i => (B2.adjugate i c₀).eval γ))
        - v cs' * (Bev a ⬝ᵥ (fun i => (B2.adjugate i c₀').eval γ)) := by
      simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hu'app b]
      ring
    rw [hsplit, hBv a, hBK c₀ a, hBK c₀' a]
    by_cases ha' : a = c₀'
    · subst ha'
      rw [if_pos rfl, Matrix.one_apply_ne hcc.symm, Matrix.one_apply_eq]
      ring
    · by_cases ha : a = c₀
      · subst ha
        rw [if_neg ha', if_pos rfl, Matrix.one_apply_eq, Matrix.one_apply_ne hcc]
        ring
      · rw [if_neg ha', if_neg ha, Matrix.one_apply_ne ha, Matrix.one_apply_ne ha']
        ring
  have hu'0 : u' = 0 := by
    by_contra hne
    have hdet0 : Bev.det = 0 := (Matrix.exists_mulVec_eq_zero_iff).mp ⟨u', hne, hBu'⟩
    rw [hdetev] at hdet0
    exact hdet hdet0
  intro b
  have h := congrFun hu'0 b
  rw [hu'app b] at h
  have h' : Bev.det * v b - v cs * (B2.adjugate b c₀).eval γ
      - v cs' * (B2.adjugate b c₀').eval γ = 0 := h
  rw [hdetev] at h'
  have : (B2.det).eval γ * v b = v cs * (B2.adjugate b c₀).eval γ
      + v cs' * (B2.adjugate b c₀').eval γ := by linear_combination h'
  exact this

/-! ## The eval bridges -/

theorem pencilG_eval (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) (c₀ c₀' cs cs' col : WCol n k w)
    (i : Fin n) (γ : F) :
    (pencilG dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' col i).eval γ
      = ∑ t : Fin (w + 1),
          (pencilK dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' col (Sum.inl t)).eval γ
            * (dom i) ^ (t : ℕ) := by
  rw [pencilG, eval_finset_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [eval_mul, eval_C]

/-- The span identity summed against the locator block: at every domain point,
`det(γ)·Z(x_i) = v_{cs}·G¹_i(γ) + v_{cs'}·G²_i(γ)`. -/
theorem corank2_span_eval (dom : Fin n ↪ F) {k w : ℕ} {ℓ₀ R₀ ℓ₁ R₁ : F[X]}
    {J : WCol n k w → Fin (3 * w + k)} {c₀ c₀' cs cs' : WCol n k w}
    (hcc : c₀ ≠ c₀') {γ : F} {Z Q h : F[X]} (hZdeg : Z.natDegree ≤ w)
    (hQdeg : Q.natDegree < w + k) (hhco : ∀ j, 3 * w + k - n ≤ j → h.coeff j = 0)
    (hid : (ℓ₁ * R₀ + C γ * (ℓ₀ * R₁)) * Z = ℓ₀ * ℓ₁ * Q + domVanish dom * h)
    (hdet : ((pencilSqDU dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs').det).eval γ ≠ 0)
    (i : Fin n) :
    ((pencilSqDU dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs').det).eval γ * Z.eval (dom i)
      = (coeffVec n k w Z Q h) cs
          * (pencilG dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' c₀ i).eval γ
        + (coeffVec n k w Z Q h) cs'
          * (pencilG dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' c₀' i).eval γ := by
  classical
  set v := coeffVec n k w Z Q h with hvdef
  have hker : ((windowPencil dom k w ℓ₀ R₀ ℓ₁ R₁).map (Polynomial.eval γ)).mulVec v
      = 0 := windowPencil_mulVec_eq_zero dom k w hZdeg hQdeg hhco hid
  have hspan := corank2_span dom hcc hker hdet
  have hwzv : wzPoly v = Z := wzPoly_coeffVec hZdeg
  have hZeval : Z.eval (dom i)
      = ∑ t : Fin (w + 1), v (Sum.inl t) * (dom i) ^ (t : ℕ) := by
    rw [← hwzv, wzPoly, eval_finset_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [eval_mul, eval_C, eval_pow, eval_X]
  rw [hZeval, Finset.mul_sum, pencilG_eval, pencilG_eval, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hb := hspan (Sum.inl t)
  calc ((pencilSqDU dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs').det).eval γ
        * (v (Sum.inl t) * (dom i) ^ (t : ℕ))
      = (((pencilSqDU dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs').det).eval γ
          * v (Sum.inl t)) * (dom i) ^ (t : ℕ) := by ring
    _ = (v cs * (pencilK dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' c₀ (Sum.inl t)).eval γ
          + v cs' * (pencilK dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' c₀'
              (Sum.inl t)).eval γ) * (dom i) ^ (t : ℕ) := by rw [hb]
    _ = _ := by ring

/-! ## The count theorem -/

open Classical in
/-- **THE CORANK-2 COUNT (WB-5).**  Under the double-update anchor
(`det B₂ ≢ 0`) and twin-freeness, every stack with WB representations has at
most `(w+1) + (n+1) + n²(2w+2)` mca-bad scalars — at every radius `δ ≤ w/n`,
with no slice hypothesis: this covers the first above-boundary slice
`n = 2w+k−1` (where the WB-4 anchor provably dies) and the corank-2 part of
`UnanchoredLinear` below it. -/
theorem badScalars_card_le_of_corank2 (dom : Fin n ↪ F) {k w : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    {u₀ u₁ : Fin n → F} {ℓ₀ R₀ ℓ₁ R₁ : F[X]}
    (hd₀ : ℓ₀.natDegree ≤ w) (hd₁ : ℓ₁.natDegree ≤ w)
    (hr₀ : R₀.natDegree ≤ w + k - 1) (hr₁ : R₁.natDegree ≤ w + k - 1)
    (hrel₀ : ∀ i, ℓ₀.eval (dom i) * u₀ i = R₀.eval (dom i))
    (hrel₁ : ∀ i, ℓ₁.eval (dom i) * u₁ i = R₁.eval (dom i))
    {J : WCol n k w → Fin (3 * w + k)} {c₀ c₀' cs cs' : WCol n k w}
    (hcc : c₀ ≠ c₀')
    (hdet : (pencilSqDU dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs').det ≠ 0)
    (htwin : ∀ i j : Fin n, i ≠ j →
      coincPoly dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' i j ≠ 0) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      ≤ (w + 1) + (n + 1) + n * n * (2 * w + 2) := by
  classical
  set Bad := Finset.univ.filter (fun γ : F => mcaEvent (F := F)
    ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)
    with hBadDef
  set B2det := (pencilSqDU dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs').det with hB2detdef
  -- the size-converted witness, as in WB-4
  have hwitness : ∀ γ ∈ Bad, ∃ S : Finset (Fin n), n - w ≤ S.card ∧
      (∃ c ∈ ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)),
        ∀ i ∈ S, c i = u₀ i + γ • u₁ i) ∧
      ¬ pairJointAgreesOn
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) S u₀ u₁ := by
    intro γ hγ
    obtain ⟨S, hsz, hcw, hno⟩ := (Finset.mem_filter.mp hγ).2
    refine ⟨S, ?_, hcw, hno⟩
    have h1 : ((n - w : ℕ) : ℝ≥0) ≤ (S.card : ℝ≥0) := by
      have hnw : ((n - w : ℕ) : ℝ≥0) = (n : ℝ≥0) - (w : ℝ≥0) := by
        rw [Nat.cast_tsub]
      have hδ1 : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0)
          = (Fintype.card (Fin n) : ℝ≥0) - δ * (Fintype.card (Fin n) : ℝ≥0) := by
        rw [tsub_mul, one_mul]
      have hcardn : (Fintype.card (Fin n) : ℝ≥0) = (n : ℝ≥0) := by
        rw [Fintype.card_fin]
      calc ((n - w : ℕ) : ℝ≥0) = (n : ℝ≥0) - (w : ℝ≥0) := hnw
        _ ≤ (n : ℝ≥0) - δ * (Fintype.card (Fin n) : ℝ≥0) := by
            exact tsub_le_tsub_left (by rw [hcardn] at hδn ⊢; exact hδn) _
        _ = (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) := by
            rw [hδ1, hcardn]
        _ ≤ (S.card : ℝ≥0) := hsz
    exact_mod_cast h1
  -- a global witness choice
  set f : F → Finset (Fin n) := fun γ =>
    if h : ∃ S : Finset (Fin n), n - w ≤ S.card ∧
        (∃ c ∈ ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)),
          ∀ i ∈ S, c i = u₀ i + γ • u₁ i) ∧
        ¬ pairJointAgreesOn
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) S u₀ u₁
    then h.choose else ∅ with hfdef
  have hf : ∀ γ ∈ Bad, n - w ≤ (f γ).card ∧
      (∃ c ∈ ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)),
        ∀ i ∈ f γ, c i = u₀ i + γ • u₁ i) ∧
      ¬ pairJointAgreesOn
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) (f γ) u₀ u₁ := by
    intro γ hγ
    have hex := hwitness γ hγ
    simp only [hfdef]
    rw [dif_pos hex]
    exact hex.choose_spec
  -- the three classes
  set Bad₁ := Bad.filter (fun γ => B2det.eval γ = 0) with hB1def
  set Bad₂ := Bad.filter (fun γ => B2det.eval γ ≠ 0 ∧ n - 1 ≤ (f γ).card) with hB2def
  set Bad₃ := Bad.filter (fun γ => B2det.eval γ ≠ 0 ∧ (f γ).card < n - 1) with hB3def
  have hcover : Bad ⊆ Bad₁ ∪ Bad₂ ∪ Bad₃ := by
    intro γ hγ
    by_cases h1 : B2det.eval γ = 0
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hγ, h1⟩))
    · by_cases h2 : n - 1 ≤ (f γ).card
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hγ, h1, h2⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ, h1, by omega⟩)
  -- class 1: anchor roots
  have hb1 : Bad₁.card ≤ w + 1 := by
    have hsub : Bad₁ ⊆ B2det.roots.toFinset := by
      intro γ hγ
      rw [Multiset.mem_toFinset, mem_roots hdet]
      exact (Finset.mem_filter.mp hγ).2
    calc Bad₁.card ≤ B2det.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card B2det.roots := B2det.roots.toFinset_card_le
      _ ≤ B2det.natDegree := B2det.card_roots'
      _ ≤ w + 1 := pencilSqDU_det_natDegree_le dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs'
  -- class 2: big witness sets, killed by rigidity
  have hb2 : Bad₂.card ≤ n + 1 := by
    have hinj : Set.InjOn f Bad₂ := by
      intro γ₁ h₁ γ₂ h₂ hff
      have hm₁ := Finset.mem_filter.mp h₁
      have hm₂ := Finset.mem_filter.mp h₂
      obtain ⟨-, hcw₁, hno₁⟩ := hf γ₁ hm₁.1
      obtain ⟨-, hcw₂, -⟩ := hf γ₂ hm₂.1
      refine ProximityGap.MCAWitnessSpread.unique_bad_gamma_common_witness
        (C := rsCode dom k) (S := f γ₁) (u₀ := u₀) (u₁ := u₁) hno₁ hcw₁ ?_
      rw [hff]
      exact hcw₂
    have hmaps : ∀ γ ∈ Bad₂, f γ ∈ Finset.powersetCard (n - 1) Finset.univ
        ∪ Finset.powersetCard n (Finset.univ : Finset (Fin n)) := by
      intro γ hγ
      have hm := Finset.mem_filter.mp hγ
      have hcard : (f γ).card ≤ n := by
        calc (f γ).card ≤ (Finset.univ : Finset (Fin n)).card :=
              Finset.card_le_card (Finset.subset_univ _)
          _ = n := by simp
      have hge := hm.2.2
      rcases Nat.eq_or_lt_of_le hge with heq | hlt
      · exact Finset.mem_union_left _ (Finset.mem_powersetCard.mpr
          ⟨Finset.subset_univ _, heq.symm⟩)
      · have : (f γ).card = n := by omega
        exact Finset.mem_union_right _ (Finset.mem_powersetCard.mpr
          ⟨Finset.subset_univ _, this⟩)
    have hcard := Finset.card_le_card_of_injOn f hmaps hinj
    have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
    calc Bad₂.card ≤ (Finset.powersetCard (n - 1) Finset.univ
          ∪ Finset.powersetCard n (Finset.univ : Finset (Fin n))).card := hcard
      _ ≤ (Finset.powersetCard (n - 1) (Finset.univ : Finset (Fin n))).card
          + (Finset.powersetCard n (Finset.univ : Finset (Fin n))).card :=
            Finset.card_union_le _ _
      _ = n.choose (n - 1) + n.choose n := by
          rw [Finset.card_powersetCard, Finset.card_powersetCard]
          simp
      _ = n + 1 := by
          rw [Nat.choose_self]
          congr 1
          rw [← Nat.choose_symm (Nat.sub_le n 1), Nat.sub_sub_self hn1,
            Nat.choose_one_right]
  -- class 3: pairwise coincidence roots
  have hb3 : Bad₃.card ≤ n * n * (2 * w + 2) := by
    have hsub : Bad₃ ⊆ (Finset.univ ×ˢ (Finset.univ : Finset (Fin n))).biUnion
        (fun p => (coincPoly dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' p.1 p.2).roots.toFinset) := by
      intro γ hγ
      have hm := Finset.mem_filter.mp hγ
      have hdetγ : B2det.eval γ ≠ 0 := hm.2.1
      obtain ⟨hS, ⟨c, hcmem, hag⟩, hno⟩ := hf γ hm.1
      obtain ⟨P, hPdeg, rfl⟩ := hcmem
      have hag' : ∀ i ∈ f γ, P.eval (dom i) = u₀ i + γ * u₁ i := by
        intro i hi
        have := hag i hi
        simpa [smul_eq_mul] using this
      obtain ⟨Q, h, hQdeg, hhco, hid⟩ := identity_of_agreement dom hk hd₀ hd₁ hr₀ hr₁
        hrel₀ hrel₁ hS hPdeg hag'
      set Z : F[X] := ∏ i ∈ Finset.univ \ f γ, (X - C (dom i)) with hZdef
      have hZne : Z ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun i _ => X_sub_C_ne_zero (dom i)
      have hEcard : 2 ≤ (Finset.univ \ f γ).card := by
        have h1 : (Finset.univ \ f γ).card = n - (f γ).card := by
          rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
          simp
        have h2 := hm.2.2
        have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
        omega
      have hZdeg : Z.natDegree ≤ w := by
        rw [hZdef, Polynomial.natDegree_prod _ _ fun i _ => X_sub_C_ne_zero (dom i)]
        simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
        have h1 : (Finset.univ \ f γ).card = n - (f γ).card := by
          rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
          simp
        have h2 : (f γ).card ≤ n :=
          le_trans (Finset.card_le_card (Finset.subset_univ _)) (by simp)
        omega
      -- two distinct error points
      obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < (Finset.univ \ f γ).card)
      -- the span at both points; Z vanishes there
      have hZi : Z.eval (dom i) = 0 := by
        rw [hZdef, eval_prod]
        exact Finset.prod_eq_zero hi (by rw [eval_sub, eval_X, eval_C, sub_self])
      have hZj : Z.eval (dom j) = 0 := by
        rw [hZdef, eval_prod]
        exact Finset.prod_eq_zero hj (by rw [eval_sub, eval_X, eval_C, sub_self])
      have hsi := corank2_span_eval dom hcc hZdeg hQdeg hhco hid hdetγ i
      have hsj := corank2_span_eval dom hcc hZdeg hQdeg hhco hid hdetγ j
      rw [hZi, mul_zero] at hsi
      rw [hZj, mul_zero] at hsj
      set v := coeffVec n k w Z Q h with hvdef
      set Gi1 := (pencilG dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' c₀ i).eval γ with hGi1
      set Gi2 := (pencilG dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' c₀' i).eval γ with hGi2
      set Gj1 := (pencilG dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' c₀ j).eval γ with hGj1
      set Gj2 := (pencilG dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' c₀' j).eval γ with hGj2
      -- (v cs, v cs') is nontrivial
      have hvnz : v cs ≠ 0 ∨ v cs' ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        have hker : ((windowPencil dom k w ℓ₀ R₀ ℓ₁ R₁).map (Polynomial.eval γ)).mulVec v
            = 0 := windowPencil_mulVec_eq_zero dom k w hZdeg hQdeg hhco hid
        have hspan := corank2_span dom hcc hker hdetγ
        have hv0 : v = 0 := by
          funext b
          have hb := hspan b
          rw [hcon.1, hcon.2, zero_mul, zero_mul, add_zero] at hb
          rcases mul_eq_zero.mp hb with hd | hv
          · exact absurd hd hdetγ
          · exact hv
        apply hZne
        rw [← wzPoly_coeffVec (Q := Q) (h := h) hZdeg, ← hvdef, hv0, wzPoly_zero]
      -- the 2×2 determinant vanishes
      have hdet2 : Gi1 * Gj2 - Gj1 * Gi2 = 0 := by
        have hi' : v cs * Gi1 + v cs' * Gi2 = 0 := hsi.symm
        have hj' : v cs * Gj1 + v cs' * Gj2 = 0 := hsj.symm
        rcases hvnz with hcs | hcs'
        · have : v cs * (Gi1 * Gj2 - Gj1 * Gi2) = 0 := by
            linear_combination Gj2 * hi' - Gi2 * hj'
          rcases mul_eq_zero.mp this with hh | hh
          · exact absurd hh hcs
          · exact hh
        · have : v cs' * (Gi1 * Gj2 - Gj1 * Gi2) = 0 := by
            linear_combination Gi1 * hj' - Gj1 * hi'
          rcases mul_eq_zero.mp this with hh | hh
          · exact absurd hh hcs'
          · exact hh
      refine Finset.mem_biUnion.mpr ⟨(i, j), Finset.mem_product.mpr
        ⟨Finset.mem_univ i, Finset.mem_univ j⟩, ?_⟩
      have hijne : i ≠ j := hij
      rw [Multiset.mem_toFinset, mem_roots (htwin i j hijne)]
      show (coincPoly dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' i j).eval γ = 0
      rw [coincPoly, eval_sub, eval_mul, eval_mul]
      rw [← hGi1, ← hGi2, ← hGj1, ← hGj2]
      exact hdet2
    calc Bad₃.card ≤ ((Finset.univ ×ˢ (Finset.univ : Finset (Fin n))).biUnion
          (fun p => (coincPoly dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs'
            p.1 p.2).roots.toFinset)).card := Finset.card_le_card hsub
      _ ≤ ∑ p ∈ Finset.univ ×ˢ (Finset.univ : Finset (Fin n)),
            (coincPoly dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs'
              p.1 p.2).roots.toFinset.card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ Finset.univ ×ˢ (Finset.univ : Finset (Fin n)), (2 * w + 2) := by
          refine Finset.sum_le_sum fun p _ => ?_
          calc (coincPoly dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs'
                p.1 p.2).roots.toFinset.card
              ≤ Multiset.card (coincPoly dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs'
                  p.1 p.2).roots := Multiset.toFinset_card_le _
            _ ≤ (coincPoly dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs'
                  p.1 p.2).natDegree := Polynomial.card_roots' _
            _ ≤ 2 * w + 2 := coincPoly_natDegree_le dom k w ℓ₀ R₀ ℓ₁ R₁ J
                  c₀ c₀' cs cs' p.1 p.2
      _ = n * n * (2 * w + 2) := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_product]
          simp [mul_assoc]
  calc Bad.card ≤ (Bad₁ ∪ Bad₂ ∪ Bad₃).card := Finset.card_le_card hcover
    _ ≤ (Bad₁ ∪ Bad₂).card + Bad₃.card := Finset.card_union_le _ _
    _ ≤ Bad₁.card + Bad₂.card + Bad₃.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ (w + 1) + (n + 1) + n * n * (2 * w + 2) := by
        have := hb1
        have := hb2
        have := hb3
        omega

open Classical in
omit [DecidableEq F] in
/-- Probability form of `badScalars_card_le_of_corank2`: under the same
double-update anchor and twin-freeness hypotheses, the fixed-stack `mcaEvent`
probability is bounded by the corank-2 count divided by the field size. -/
theorem mcaEvent_prob_le_of_corank2 (dom : Fin n ↪ F) {k w : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    {u₀ u₁ : Fin n → F} {ℓ₀ R₀ ℓ₁ R₁ : F[X]}
    (hd₀ : ℓ₀.natDegree ≤ w) (hd₁ : ℓ₁.natDegree ≤ w)
    (hr₀ : R₀.natDegree ≤ w + k - 1) (hr₁ : R₁.natDegree ≤ w + k - 1)
    (hrel₀ : ∀ i, ℓ₀.eval (dom i) * u₀ i = R₀.eval (dom i))
    (hrel₁ : ∀ i, ℓ₁.eval (dom i) * u₁ i = R₁.eval (dom i))
    {J : WCol n k w → Fin (3 * w + k)} {c₀ c₀' cs cs' : WCol n k w}
    (hcc : c₀ ≠ c₀')
    (hdet : (pencilSqDU dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs').det ≠ 0)
    (htwin : ∀ i j : Fin n, i ≠ j →
      coincPoly dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' i j ≠ 0) :
    Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ]
      ≤ (((((w + 1) + (n + 1) + n * n * (2 * w + 2) : ℕ) : ℝ≥0) : ℝ≥0∞)
          / (((Fintype.card F : ℕ) : ℝ≥0) : ℝ≥0∞)) := by
  rw [prob_uniform_eq_card_filter_div_card]
  gcongr
  exact badScalars_card_le_of_corank2 dom hk hδn hd₀ hd₁ hr₀ hr₁
    hrel₀ hrel₁ hcc hdet htwin

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.corank2_span
#print axioms ProximityGap.WBPencil.pencilSqDU_det_natDegree_le
#print axioms ProximityGap.WBPencil.coincPoly_natDegree_le
#print axioms ProximityGap.WBPencil.badScalars_card_le_of_corank2
#print axioms ProximityGap.WBPencil.mcaEvent_prob_le_of_corank2
