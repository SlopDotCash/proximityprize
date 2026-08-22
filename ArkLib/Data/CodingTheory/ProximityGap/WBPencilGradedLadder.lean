/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WBPencilWindowLaw

/-!
# WB-6: the graded pencil ladder — one count theorem for every corank level (#371)

The uniform generalization of WB-4 (`c = 1`) and WB-5 (`c = 2`): replace any SET
`C₀` of rows of a square pencil selection by coordinate singletons (`a ↦
Pi.single (τ a) 1`), in ONE definition — no iterated `updateRow`.  The `|C₀|`
adjugate columns indexed by `C₀` span every evaluated kernel wherever the
determinant survives:

  `det(γ)·v = ∑_{col ∈ C₀} v_{τ(col)} · K^{col}(γ)`     (`graded_span`)

and a bad scalar whose error set has `≥ c := |C₀|` points kills the `c × c`
minor of the locator-evaluation matrix on every `c`-subset `T` of its error set
— the **graded coincidence polynomial** `gradedCoinc T` (degree ≤ `c(w+1)`).

**`badScalars_card_le_of_graded`**: under the graded anchor (`det ≢ 0`) and
`c`-twin-freeness (`gradedCoinc T ≢ 0` for every `c`-subset `T`),

  `#bad ≤ (w+1) + (∑_{j<c} C(n, n−j)) + C(n,c)·c(w+1)`

— polynomial in `n` for every fixed grade `c`, at EVERY radius `δ ≤ w/n`.

**Termination of the ladder**: replacing ALL rows (`C₀ = univ`, `τ = id`) gives
the identity matrix — determinant `1 ≠ 0` — so every stack is anchored at SOME
grade; the minimal grade is (one more than) the pencil corank, which grows by
one per slice above the boundary.  The graded ladder therefore yields a poly(n)
count at every fixed number of slices past UDR, with the residual at each grade
exactly `c`-twin-freeness — and the wall is `c ~ εn`: the deep window interior,
i.e. the recognized four-face open core, now approached by a graded formal
ladder.  Probe record: `probe_wb_corank2_coincidence.py` (grade 2 exact),
`probe_wb_boundary_slice_anchor.py` (grade 1 at the boundary).
-/

open Finset Polynomial Matrix
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The graded square selection: rows in `C₀` replaced by coordinate singletons. -/
noncomputable def pencilSqG (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) (C₀ : Finset (WCol n k w))
    (τ : WCol n k w → WCol n k w) : Matrix (WCol n k w) (WCol n k w) F[X] :=
  fun a => if a ∈ C₀ then Pi.single (τ a) 1
    else ((windowPencil dom k w ℓ₀ R₀ ℓ₁ R₁).submatrix J id) a

/-- The graded locator-evaluation polynomials. -/
noncomputable def pencilGG (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) (C₀ : Finset (WCol n k w))
    (τ : WCol n k w → WCol n k w) (col : WCol n k w) (i : Fin n) : F[X] :=
  ∑ t : Fin (w + 1),
    (pencilSqG dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ).adjugate (Sum.inl t) col
      * C ((dom i) ^ (t : ℕ))

/-! ## Degree bounds -/

theorem pencilSqG_natDegree_le (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) (C₀ : Finset (WCol n k w))
    (τ : WCol n k w → WCol n k w) (a b : WCol n k w) :
    ((pencilSqG dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ) a b).natDegree
      ≤ Sum.elim (fun _ : Fin (w + 1) => 1)
          (Sum.elim (fun _ : Fin (w + k) => 0) (fun _ : Fin (3 * w + k - n) => 0)) b := by
  rw [pencilSqG]
  by_cases ha : a ∈ C₀
  · rw [if_pos ha]
    by_cases hb : b = τ a
    · rw [Pi.single_apply, if_pos hb]
      rcases b with t | s | m <;> simp
    · rw [Pi.single_apply, if_neg hb]
      rcases b with t | s | m <;> simp
  · rw [if_neg ha]
    exact windowPencil_natDegree_le dom k w ℓ₀ R₀ ℓ₁ R₁ (J a) b

theorem pencilSqG_det_natDegree_le (dom : Fin n ↪ F) (k w : ℕ)
    (ℓ₀ R₀ ℓ₁ R₁ : F[X]) (J : WCol n k w → Fin (3 * w + k))
    (C₀ : Finset (WCol n k w)) (τ : WCol n k w → WCol n k w) :
    (pencilSqG dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ).det.natDegree ≤ w + 1 :=
  le_trans (natDegree_det_le_sum_colBound _
    (Sum.elim (fun _ : Fin (w + 1) => 1)
      (Sum.elim (fun _ : Fin (w + k) => 0) (fun _ : Fin (3 * w + k - n) => 0)))
    (pencilSqG_natDegree_le dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ))
    (le_of_eq (windowPencil_colBound_sum n k w))

theorem pencilSqG_adjugate_natDegree_le (dom : Fin n ↪ F) (k w : ℕ)
    (ℓ₀ R₀ ℓ₁ R₁ : F[X]) (J : WCol n k w → Fin (3 * w + k))
    (C₀ : Finset (WCol n k w)) (τ : WCol n k w → WCol n k w)
    (i col : WCol n k w) :
    ((pencilSqG dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ).adjugate i col).natDegree ≤ w + 1 := by
  classical
  rw [Matrix.adjugate_apply]
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
    exact pencilSqG_natDegree_le dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ a b

theorem pencilGG_natDegree_le (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) (C₀ : Finset (WCol n k w))
    (τ : WCol n k w → WCol n k w) (col : WCol n k w) (i : Fin n) :
    (pencilGG dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ col i).natDegree ≤ w + 1 := by
  refine natDegree_sum_le_of_forall_le _ _ fun t _ => ?_
  calc ((pencilSqG dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ).adjugate (Sum.inl t) col
        * C ((dom i) ^ (t : ℕ))).natDegree
      ≤ ((pencilSqG dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ).adjugate (Sum.inl t) col).natDegree
        + (C ((dom i) ^ (t : ℕ)) : F[X]).natDegree := natDegree_mul_le
    _ ≤ (w + 1) + 0 := Nat.add_le_add
        (pencilSqG_adjugate_natDegree_le dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ _ col)
        (le_of_eq (natDegree_C _))
    _ = w + 1 := by omega

/-! ## The graded span -/

/-- **The graded span**: wherever the determinant of the graded selection
survives, every evaluated kernel vector of the full pencil is the explicit
combination of the `C₀`-indexed adjugate columns. -/
theorem graded_span (dom : Fin n ↪ F) {k w : ℕ} {ℓ₀ R₀ ℓ₁ R₁ : F[X]}
    {J : WCol n k w → Fin (3 * w + k)} {C₀ : Finset (WCol n k w)}
    {τ : WCol n k w → WCol n k w} {γ : F}
    {v : WCol n k w → F}
    (hv : ((windowPencil dom k w ℓ₀ R₀ ℓ₁ R₁).map (Polynomial.eval γ)).mulVec v = 0)
    (hdet : ((pencilSqG dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ).det).eval γ ≠ 0) :
    ∀ b, ((pencilSqG dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ).det).eval γ * v b
      = ∑ col ∈ C₀, v (τ col)
          * ((pencilSqG dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ).adjugate b col).eval γ := by
  classical
  set BG := pencilSqG dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ with hBGdef
  set Bev := BG.map (Polynomial.eval γ) with hBevdef
  have hadj : Bev.adjugate = (BG.adjugate).map (Polynomial.eval γ) := by
    have h := RingHom.map_adjugate (Polynomial.evalRingHom γ) BG
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at h
    rw [hBevdef]
    exact h.symm
  have hdetev : Bev.det = (BG.det).eval γ := by
    rw [hBevdef, ← Polynomial.coe_evalRingHom, ← RingHom.mapMatrix_apply,
      ← RingHom.map_det]
  -- the rows of the evaluated graded selection
  have hBv : ∀ a, Bev a ⬝ᵥ v = (if a ∈ C₀ then v (τ a) else 0) := by
    intro a
    by_cases ha : a ∈ C₀
    · have hrow : Bev a = Pi.single (τ a) 1 := by
        funext b
        rw [hBevdef, Matrix.map_apply, hBGdef, pencilSqG]
        rw [if_pos ha]
        by_cases hb : b = τ a
        · subst hb
          rw [Pi.single_eq_same, Pi.single_eq_same]
          simp
        · rw [Pi.single_eq_of_ne hb, Pi.single_eq_of_ne hb]
          simp
      rw [hrow, single_dotProduct, one_mul, if_pos ha]
    · have hrow : Bev a = fun b =>
          ((windowPencil dom k w ℓ₀ R₀ ℓ₁ R₁).map (Polynomial.eval γ)) (J a) b := by
        funext b
        rw [hBevdef, Matrix.map_apply, hBGdef, pencilSqG, if_neg ha,
          Matrix.submatrix_apply, Matrix.map_apply]
        rfl
      rw [hrow, if_neg ha]
      have := congrFun hv (J a)
      simpa [Matrix.mulVec, dotProduct] using this
  have hBK : ∀ (col : WCol n k w) a,
      Bev a ⬝ᵥ (fun i => (BG.adjugate i col).eval γ)
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
    - ∑ col ∈ C₀, v (τ col) * (BG.adjugate b col).eval γ with hu'def
  have hu'app : ∀ b, u' b = Bev.det * v b
      - ∑ col ∈ C₀, v (τ col) * (BG.adjugate b col).eval γ := fun b => by rw [hu'def]
  have hBu' : Bev.mulVec u' = 0 := by
    funext a
    show Bev a ⬝ᵥ u' = 0
    have hsplit : Bev a ⬝ᵥ u' = Bev.det * (Bev a ⬝ᵥ v)
        - ∑ col ∈ C₀, v (τ col)
            * (Bev a ⬝ᵥ (fun i => (BG.adjugate i col).eval γ)) := by
      simp only [dotProduct]
      calc ∑ b, Bev a b * u' b
          = ∑ b, (Bev.det * (Bev a b * v b)
              - ∑ col ∈ C₀, v (τ col)
                  * (Bev a b * (BG.adjugate b col).eval γ)) := by
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [hu'app b, mul_sub, Finset.mul_sum]
            congr 1
            · ring
            · refine Finset.sum_congr rfl fun col _ => ?_
              ring
        _ = Bev.det * ∑ b, Bev a b * v b
            - ∑ b, ∑ col ∈ C₀, v (τ col)
                * (Bev a b * (BG.adjugate b col).eval γ) := by
            rw [Finset.sum_sub_distrib, Finset.mul_sum]
        _ = Bev.det * ∑ b, Bev a b * v b
            - ∑ col ∈ C₀, v (τ col)
                * ∑ b, Bev a b * (BG.adjugate b col).eval γ := by
            congr 1
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun col _ => ?_
            rw [Finset.mul_sum]
    rw [hsplit, hBv a]
    have hsum : ∑ col ∈ C₀, v (τ col)
        * (Bev a ⬝ᵥ (fun i => (BG.adjugate i col).eval γ))
        = ∑ col ∈ C₀, v (τ col)
            * (Bev.det * (1 : Matrix (WCol n k w) (WCol n k w) F) a col) := by
      refine Finset.sum_congr rfl fun col _ => ?_
      rw [hBK col a]
    rw [hsum]
    by_cases ha : a ∈ C₀
    · rw [if_pos ha]
      have hcollapse : ∑ col ∈ C₀, v (τ col)
          * (Bev.det * (1 : Matrix (WCol n k w) (WCol n k w) F) a col)
          = v (τ a) * Bev.det := by
        rw [Finset.sum_eq_single a (fun col _ hne => by
            rw [Matrix.one_apply_ne (Ne.symm hne)]
            ring)
          (fun hnotmem => absurd ha hnotmem)]
        rw [Matrix.one_apply_eq]
        ring
      rw [hcollapse]
      ring
    · rw [if_neg ha]
      have hzero : ∑ col ∈ C₀, v (τ col)
          * (Bev.det * (1 : Matrix (WCol n k w) (WCol n k w) F) a col) = 0 :=
        Finset.sum_eq_zero fun col hcol => by
          have hne : a ≠ col := fun h => ha (h ▸ hcol)
          rw [Matrix.one_apply_ne hne]
          ring
      rw [hzero]
      ring
  have hu'0 : u' = 0 := by
    by_contra hne
    have hdet0 : Bev.det = 0 := (Matrix.exists_mulVec_eq_zero_iff).mp ⟨u', hne, hBu'⟩
    rw [hdetev] at hdet0
    exact hdet hdet0
  intro b
  have h := congrFun hu'0 b
  rw [hu'app b] at h
  have h' : Bev.det * v b
      - ∑ col ∈ C₀, v (τ col) * (BG.adjugate b col).eval γ = 0 := h
  rw [hdetev] at h'
  exact sub_eq_zero.mp h'

/-! ## The graded coincidence polynomial -/

/-- A canonical enumeration of a finset (choice-based, fixed per term). -/
noncomputable def finsetEnum {α : Type} [DecidableEq α] (s : Finset α) :
    Fin s.card ≃ ↥s :=
  ((Fintype.equivFin ↥s).trans (finCongr (Fintype.card_coe s))).symm

/-- **The graded coincidence polynomial** of a `c`-subset `T` of the domain:
the determinant of the `c × c` matrix of locator evaluations `G^{col}_i`,
`col ∈ C₀`, `i ∈ T`.  Zero (by convention) when `|T| ≠ |C₀|`. -/
noncomputable def gradedCoinc (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) (C₀ : Finset (WCol n k w))
    (τ : WCol n k w → WCol n k w) (T : Finset (Fin n)) : F[X] :=
  if h : T.card = C₀.card then
    Matrix.det (fun r s : Fin C₀.card =>
      pencilGG dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ
        ((finsetEnum C₀ s : ↥C₀) : WCol n k w)
        ((finsetEnum T (finCongr h.symm r) : ↥T) : Fin n))
  else 0

theorem gradedCoinc_natDegree_le (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) (C₀ : Finset (WCol n k w))
    (τ : WCol n k w → WCol n k w) (T : Finset (Fin n)) :
    (gradedCoinc dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ T).natDegree
      ≤ C₀.card * (w + 1) := by
  rw [gradedCoinc]
  by_cases h : T.card = C₀.card
  · rw [dif_pos h]
    refine le_trans (natDegree_det_le_sum_colBound _
      (fun _ : Fin C₀.card => w + 1) ?_) (by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul])
    intro r s
    exact pencilGG_natDegree_le dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ _ _
  · rw [dif_neg h]
    simp

/-! ## The graded count theorem -/

open Classical in
/-- **WB-6: THE GRADED LADDER COUNT.**  Under the grade-`c` anchor
(`det (pencilSqG …) ≢ 0`, `c = |C₀|`) and `c`-twin-freeness, every stack with WB
representations has at most

  `(w+1) + (∑_{j<c} C(n, n−j)) + C(n,c) · c(w+1)`

mca-bad scalars, at every radius `δ ≤ w/n` — subsuming WB-4 (`c = 1`) and WB-5
(`c = 2`), and yielding a poly(n) count at every fixed number of slices past
the unique-decoding boundary. -/
theorem badScalars_card_le_of_graded (dom : Fin n ↪ F) {k w : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    {u₀ u₁ : Fin n → F} {ℓ₀ R₀ ℓ₁ R₁ : F[X]}
    (hd₀ : ℓ₀.natDegree ≤ w) (hd₁ : ℓ₁.natDegree ≤ w)
    (hr₀ : R₀.natDegree ≤ w + k - 1) (hr₁ : R₁.natDegree ≤ w + k - 1)
    (hrel₀ : ∀ i, ℓ₀.eval (dom i) * u₀ i = R₀.eval (dom i))
    (hrel₁ : ∀ i, ℓ₁.eval (dom i) * u₁ i = R₁.eval (dom i))
    {J : WCol n k w → Fin (3 * w + k)} {C₀ : Finset (WCol n k w)}
    {τ : WCol n k w → WCol n k w} (hc : 1 ≤ C₀.card)
    (hdet : (pencilSqG dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ).det ≠ 0)
    (htwin : ∀ T ∈ Finset.powersetCard C₀.card (Finset.univ : Finset (Fin n)),
      gradedCoinc dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ T ≠ 0) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      ≤ (w + 1) + (∑ j ∈ Finset.range C₀.card, n.choose (n - j))
        + n.choose C₀.card * (C₀.card * (w + 1)) := by
  classical
  set c := C₀.card with hcdef
  have hc1 : 1 ≤ c := hc
  set Bad := Finset.univ.filter (fun γ : F => mcaEvent (F := F)
    ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)
    with hBadDef
  set BGdet := (pencilSqG dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ).det with hBGdetdef
  have hwitness : ∀ γ ∈ Bad, ∃ S : Finset (Fin n), n - w ≤ S.card ∧
      (∃ cw ∈ ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)),
        ∀ i ∈ S, cw i = u₀ i + γ • u₁ i) ∧
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
  set f : F → Finset (Fin n) := fun γ =>
    if h : ∃ S : Finset (Fin n), n - w ≤ S.card ∧
        (∃ cw ∈ ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)),
          ∀ i ∈ S, cw i = u₀ i + γ • u₁ i) ∧
        ¬ pairJointAgreesOn
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) S u₀ u₁
    then h.choose else ∅ with hfdef
  have hf : ∀ γ ∈ Bad, n - w ≤ (f γ).card ∧
      (∃ cw ∈ ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)),
        ∀ i ∈ f γ, cw i = u₀ i + γ • u₁ i) ∧
      ¬ pairJointAgreesOn
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) (f γ) u₀ u₁ := by
    intro γ hγ
    have hex := hwitness γ hγ
    simp only [hfdef]
    rw [dif_pos hex]
    exact hex.choose_spec
  set Bad₁ := Bad.filter (fun γ => BGdet.eval γ = 0) with hB1def
  set Bad₂ := Bad.filter (fun γ => BGdet.eval γ ≠ 0 ∧ n - (c - 1) ≤ (f γ).card)
    with hB2def
  set Bad₃ := Bad.filter (fun γ => BGdet.eval γ ≠ 0 ∧ (f γ).card < n - (c - 1))
    with hB3def
  have hcover : Bad ⊆ Bad₁ ∪ Bad₂ ∪ Bad₃ := by
    intro γ hγ
    by_cases h1 : BGdet.eval γ = 0
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hγ, h1⟩))
    · by_cases h2 : n - (c - 1) ≤ (f γ).card
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hγ, h1, h2⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ, h1, by omega⟩)
  have hb1 : Bad₁.card ≤ w + 1 := by
    have hsub : Bad₁ ⊆ BGdet.roots.toFinset := by
      intro γ hγ
      rw [Multiset.mem_toFinset, mem_roots hdet]
      exact (Finset.mem_filter.mp hγ).2
    calc Bad₁.card ≤ BGdet.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card BGdet.roots := BGdet.roots.toFinset_card_le
      _ ≤ BGdet.natDegree := BGdet.card_roots'
      _ ≤ w + 1 := pencilSqG_det_natDegree_le dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ
  have hb2 : Bad₂.card ≤ ∑ j ∈ Finset.range c, n.choose (n - j) := by
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
    have hmaps : ∀ γ ∈ Bad₂, f γ ∈ (Finset.range c).biUnion
        (fun j => Finset.powersetCard (n - j) (Finset.univ : Finset (Fin n))) := by
      intro γ hγ
      have hm := Finset.mem_filter.mp hγ
      have hcard : (f γ).card ≤ n :=
        le_trans (Finset.card_le_card (Finset.subset_univ _)) (by simp)
      have hge := hm.2.2
      refine Finset.mem_biUnion.mpr ⟨n - (f γ).card, ?_, ?_⟩
      · rw [Finset.mem_range]
        omega
      · refine Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩
        omega
    have hcard := Finset.card_le_card_of_injOn f hmaps hinj
    calc Bad₂.card ≤ ((Finset.range c).biUnion
          (fun j => Finset.powersetCard (n - j)
            (Finset.univ : Finset (Fin n)))).card := hcard
      _ ≤ ∑ j ∈ Finset.range c, (Finset.powersetCard (n - j)
            (Finset.univ : Finset (Fin n))).card := Finset.card_biUnion_le
      _ = ∑ j ∈ Finset.range c, n.choose (n - j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.card_powersetCard]
          simp
  have hb3 : Bad₃.card ≤ n.choose c * (c * (w + 1)) := by
    have hsub : Bad₃ ⊆ (Finset.powersetCard c
        (Finset.univ : Finset (Fin n))).biUnion
        (fun T => (gradedCoinc dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ T).roots.toFinset) := by
      intro γ hγ
      have hm := Finset.mem_filter.mp hγ
      have hdetγ : BGdet.eval γ ≠ 0 := hm.2.1
      obtain ⟨hS, ⟨cw, hcmem, hag⟩, hno⟩ := hf γ hm.1
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
      have hcardn : (Finset.univ \ f γ).card = n - (f γ).card := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
        simp
      have hfcard : (f γ).card ≤ n :=
        le_trans (Finset.card_le_card (Finset.subset_univ _)) (by simp)
      have hEcard : c ≤ (Finset.univ \ f γ).card := by
        have h2 := hm.2.2
        omega
      have hZdeg : Z.natDegree ≤ w := by
        rw [hZdef, Polynomial.natDegree_prod _ _ fun i _ => X_sub_C_ne_zero (dom i)]
        simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
        omega
      have hker : ((windowPencil dom k w ℓ₀ R₀ ℓ₁ R₁).map
          (Polynomial.eval γ)).mulVec (coeffVec n k w Z Q h) = 0 :=
        windowPencil_mulVec_eq_zero dom k w hZdeg hQdeg hhco hid
      have hspan := graded_span (J := J) (C₀ := C₀) (τ := τ) dom hker hdetγ
      set v := coeffVec n k w Z Q h with hvdef
      -- the C₀-vector is nontrivial
      have hvnz : ∃ col ∈ C₀, v (τ col) ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        have hv0 : v = 0 := by
          funext b
          have hb := hspan b
          rw [Finset.sum_eq_zero (fun col hcol => by
            rw [hcon col hcol, zero_mul])] at hb
          rcases mul_eq_zero.mp hb with hd | hv
          · exact absurd hd hdetγ
          · exact hv
        apply hZne
        rw [← wzPoly_coeffVec (Q := Q) (h := h) hZdeg, ← hvdef, hv0, wzPoly_zero]
      -- a c-subset of the error set
      obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hEcard
      -- the evaluated coincidence matrix has the nontrivial kernel
      have hAker : ∃ x : Fin c → F, x ≠ 0 ∧
          Matrix.mulVec (fun r s : Fin c =>
            (pencilGG dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ
              ((finsetEnum C₀ s : ↥C₀) : WCol n k w)
              ((finsetEnum T (finCongr hTcard.symm r) : ↥T) : Fin n)).eval γ)
            x = 0 := by
        refine ⟨fun s => v (τ ((finsetEnum C₀ s : ↥C₀) : WCol n k w)), ?_, ?_⟩
        · obtain ⟨col, hcol, hvcol⟩ := hvnz
          intro hx0
          apply hvcol
          have := congrFun hx0 ((finsetEnum C₀).symm ⟨col, hcol⟩)
          simpa using this
        · funext r
          set i : Fin n := ((finsetEnum T (finCongr hTcard.symm r) : ↥T) : Fin n)
            with hidef
          have hiE : i ∈ Finset.univ \ f γ := hTsub (Subtype.coe_prop _)
          have hZi : Z.eval (dom i) = 0 := by
            rw [hZdef, eval_prod]
            exact Finset.prod_eq_zero hiE
              (by rw [eval_sub, eval_X, eval_C, sub_self])
          -- the span summed against the locator block at x_i
          have hwzv : wzPoly v = Z := wzPoly_coeffVec hZdeg
          have hZeval : Z.eval (dom i)
              = ∑ t : Fin (w + 1), v (Sum.inl t) * (dom i) ^ (t : ℕ) := by
            rw [← hwzv, wzPoly, eval_finset_sum]
            refine Finset.sum_congr rfl fun t _ => ?_
            rw [eval_mul, eval_C, eval_pow, eval_X]
          have hrow : BGdet.eval γ * Z.eval (dom i)
              = ∑ col ∈ C₀, v (τ col)
                  * (pencilGG dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ col i).eval γ := by
            rw [hZeval, Finset.mul_sum]
            calc ∑ t : Fin (w + 1), BGdet.eval γ * (v (Sum.inl t) * (dom i) ^ (t : ℕ))
                = ∑ t : Fin (w + 1), ∑ col ∈ C₀, v (τ col)
                    * ((pencilSqG dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ).adjugate
                        (Sum.inl t) col).eval γ * (dom i) ^ (t : ℕ) := by
                  refine Finset.sum_congr rfl fun t _ => ?_
                  rw [show BGdet.eval γ * (v (Sum.inl t) * (dom i) ^ (t : ℕ))
                      = (BGdet.eval γ * v (Sum.inl t)) * (dom i) ^ (t : ℕ) by ring,
                    hspan (Sum.inl t), Finset.sum_mul]
              _ = ∑ col ∈ C₀, ∑ t : Fin (w + 1), v (τ col)
                    * ((pencilSqG dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ).adjugate
                        (Sum.inl t) col).eval γ * (dom i) ^ (t : ℕ) :=
                  Finset.sum_comm
              _ = ∑ col ∈ C₀, v (τ col)
                  * (pencilGG dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ col i).eval γ := by
                  refine Finset.sum_congr rfl fun col _ => ?_
                  rw [pencilGG, eval_finset_sum, Finset.mul_sum]
                  refine Finset.sum_congr rfl fun t _ => ?_
                  rw [eval_mul, eval_C]
                  ring
          have h0 : ∑ col ∈ C₀, v (τ col)
              * (pencilGG dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ col i).eval γ = 0 := by
            rw [← hrow, hZi, mul_zero]
          -- reindex the C₀-sum through the enumeration
          have hconv : ∑ s : Fin c, v (τ ((finsetEnum C₀ s : ↥C₀) : WCol n k w))
              * (pencilGG dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ
                  ((finsetEnum C₀ s : ↥C₀) : WCol n k w) i).eval γ = 0 := by
            rw [Equiv.sum_comp (finsetEnum C₀) (fun cc : ↥C₀ => v (τ (cc : WCol n k w))
              * (pencilGG dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ (cc : WCol n k w) i).eval γ)]
            rw [Finset.sum_coe_sort C₀ (fun col => v (τ col)
              * (pencilGG dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ col i).eval γ)]
            exact h0
          show (fun j => (pencilGG dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ
              ((finsetEnum C₀ j : ↥C₀) : WCol n k w)
              ((finsetEnum T (finCongr hTcard.symm r) : ↥T) : Fin n)).eval γ) ⬝ᵥ
            (fun s => v (τ ((finsetEnum C₀ s : ↥C₀) : WCol n k w))) = 0
          simp only [dotProduct, ← hidef]
          rw [← hconv]
          exact Finset.sum_congr rfl fun s _ => by ring
      -- the graded coincidence polynomial vanishes at γ
      have hcoinc0 : (gradedCoinc dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ T).eval γ = 0 := by
        obtain ⟨x, hx0, hxker⟩ := hAker
        have hdet0 : (Matrix.det (fun r s : Fin c =>
            (pencilGG dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ
              ((finsetEnum C₀ s : ↥C₀) : WCol n k w)
              ((finsetEnum T (finCongr hTcard.symm r) : ↥T) : Fin n)).eval γ)) = 0 :=
          (Matrix.exists_mulVec_eq_zero_iff).mp ⟨x, hx0, hxker⟩
        rw [gradedCoinc, dif_pos hTcard, ← Polynomial.coe_evalRingHom,
          RingHom.map_det]
        exact hdet0
      refine Finset.mem_biUnion.mpr ⟨T, ?_, ?_⟩
      · exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hTcard⟩
      · rw [Multiset.mem_toFinset,
          mem_roots (htwin T (Finset.mem_powersetCard.mpr
            ⟨Finset.subset_univ _, hTcard⟩))]
        exact hcoinc0
    calc Bad₃.card ≤ ((Finset.powersetCard c
          (Finset.univ : Finset (Fin n))).biUnion
          (fun T => (gradedCoinc dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ T).roots.toFinset)).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ T ∈ Finset.powersetCard c (Finset.univ : Finset (Fin n)),
            (gradedCoinc dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ T).roots.toFinset.card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _T ∈ Finset.powersetCard c (Finset.univ : Finset (Fin n)),
            c * (w + 1) := by
          refine Finset.sum_le_sum fun T _ => ?_
          calc (gradedCoinc dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ T).roots.toFinset.card
              ≤ Multiset.card (gradedCoinc dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ T).roots :=
                Multiset.toFinset_card_le _
            _ ≤ (gradedCoinc dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ T).natDegree :=
                Polynomial.card_roots' _
            _ ≤ c * (w + 1) :=
                gradedCoinc_natDegree_le dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ T
      _ = n.choose c * (c * (w + 1)) := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_powersetCard]
          simp
  calc Bad.card ≤ (Bad₁ ∪ Bad₂ ∪ Bad₃).card := Finset.card_le_card hcover
    _ ≤ (Bad₁ ∪ Bad₂).card + Bad₃.card := Finset.card_union_le _ _
    _ ≤ Bad₁.card + Bad₂.card + Bad₃.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ (w + 1) + (∑ j ∈ Finset.range c, n.choose (n - j))
        + n.choose c * (c * (w + 1)) := by
        have := hb1
        have := hb2
        have := hb3
        omega

open Classical in
omit [DecidableEq F] in
/-- Probability form of `badScalars_card_le_of_graded`: under the same grade-`|C₀|`
anchor and `c`-twin-freeness hypotheses, the fixed-stack `mcaEvent` probability is bounded
by the WB-6 graded count divided by the field size. -/
theorem mcaEvent_prob_le_of_graded (dom : Fin n ↪ F) {k w : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    {u₀ u₁ : Fin n → F} {ℓ₀ R₀ ℓ₁ R₁ : F[X]}
    (hd₀ : ℓ₀.natDegree ≤ w) (hd₁ : ℓ₁.natDegree ≤ w)
    (hr₀ : R₀.natDegree ≤ w + k - 1) (hr₁ : R₁.natDegree ≤ w + k - 1)
    (hrel₀ : ∀ i, ℓ₀.eval (dom i) * u₀ i = R₀.eval (dom i))
    (hrel₁ : ∀ i, ℓ₁.eval (dom i) * u₁ i = R₁.eval (dom i))
    {J : WCol n k w → Fin (3 * w + k)} {C₀ : Finset (WCol n k w)}
    {τ : WCol n k w → WCol n k w} (hc : 1 ≤ C₀.card)
    (hdet : (pencilSqG dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ).det ≠ 0)
    (htwin : ∀ T ∈ Finset.powersetCard C₀.card (Finset.univ : Finset (Fin n)),
      gradedCoinc dom k w ℓ₀ R₀ ℓ₁ R₁ J C₀ τ T ≠ 0) :
    Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ]
      ≤ (((((w + 1) + (∑ j ∈ Finset.range C₀.card, n.choose (n - j))
              + n.choose C₀.card * (C₀.card * (w + 1)) : ℕ) : ℝ≥0) : ℝ≥0∞)
          / (((Fintype.card F : ℕ) : ℝ≥0) : ℝ≥0∞)) := by
  rw [prob_uniform_eq_card_filter_div_card]
  gcongr
  exact badScalars_card_le_of_graded dom hk hδn hd₀ hd₁ hr₀ hr₁
    hrel₀ hrel₁ hc hdet htwin

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.graded_span
#print axioms ProximityGap.WBPencil.gradedCoinc_natDegree_le
#print axioms ProximityGap.WBPencil.badScalars_card_le_of_graded
#print axioms ProximityGap.WBPencil.mcaEvent_prob_le_of_graded
