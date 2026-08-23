/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WBPencilWindowMatrix
import ArkLib.Data.CodingTheory.ProximityGap.WBPencilRationalReduction
import ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessSpread

/-!
# The window pencil law (#371, WB-4): poly(n) bad scalars below UDR

**THE THEOREM.**  For any WB representations `(ℓ₀,R₀,ℓ₁,R₁)` of a stack (degree
caps `w` / `w+k−1` and the relations `ℓ_j(x_i)·u_j(x_i) = R_j(x_i)` — no reduced
form, no coprimality, no nonvanishing needed), if some adjugate entry of some
square row-selection of the window pencil is a nonzero `γ`-polynomial (the
**anchor**), then the stack has at most

  `(w+1) + n·(w+1) + 1`

mca-bad scalars.  Mechanism, validated by `probe_wb_window_kernel_family.py`
(bad set = split-locus of the Cramer kernel family, 4/4 exact at the probed
extremals; the scale-2 max `3 = n/w`, not `w+1`, is this law's incidence count):

1. every bad scalar's witness produces a kernel vector of the evaluated pencil
   (`WBPencilWindowMatrix`);
2. where the anchor entry `K_{c*}(γ) ≠ 0`, the witness vector is **proportional
   to the adjugate column** `K(γ)` — the `updateRow`-determinant trick: the
   matrix `B(γ)` with row `c₀` replaced by `Pi.single c*` has determinant exactly
   the anchor entry (`Matrix.adjugate_apply`), and it kills the cross difference
   `K_{c*}(γ)·v − v_{c*}·K(γ)`;
3. hence the witness complement is **pinned**: `univ∖S = {i : g_i(γ) = 0}` for
   fixed polynomials `g_i` of `γ`-degree ≤ w+1 (the locator part of `K`
   evaluated at `x_i`);
4. count: anchor roots (≤ w+1) + incidence union bound over the non-identically-
   vanishing `g_i` (≤ n(w+1)) + the constant-complement class, which shares ONE
   witness set and is killed by the in-tree rigidity
   `unique_bad_gamma_common_witness` (≤ 1).

**The consumer**: with WB-2 (`epsMCA_le_max_doublyRational`), the below-UDR MCA
error is `≤ ((n+1)(w+1)+1)/q` conditional on exactly ONE named Prop —
`WindowPencilAnchored` (every doubly-WB-solvable stack admits anchored
representations; equivalently the pencil has corank ≤ 1 over `F(γ)`).  Probe
record: 0/4000 genuine rational pairs violate it; every probed extremal
satisfies it.  At production shape (`q ≥ ((n+1)(w+1)+1)·2¹²⁸`, true for
`q ≥ n²·2¹²⁸` at `w < n`), this moves the unconditional-modulo-one-Prop floor
from the ladder reach `(1−ρ)/3` to the unique-decoding radius `(1−ρ)/2` — and
the budget `poly(n)/q` strictly subsumes the previous `w+3` architecture.
-/

open Finset Polynomial Matrix
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

open ProximityGap.SpikeFloor

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The square row-selection of the window pencil. -/
noncomputable def pencilSq (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) : Matrix (WCol n k w) (WCol n k w) F[X] :=
  (windowPencil dom k w ℓ₀ R₀ ℓ₁ R₁).submatrix J id

/-- The Cramer kernel candidate: column `c₀` of the adjugate of a square
row-selection.  Entries are `γ`-polynomials of degree ≤ w+1. -/
noncomputable def pencilKvec (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) (c₀ : WCol n k w) : WCol n k w → F[X] :=
  fun i => (pencilSq dom k w ℓ₀ R₀ ℓ₁ R₁ J).adjugate i c₀

/-- The per-domain-point root polynomial: the locator part of the Cramer kernel
evaluated at `x_i`, as a polynomial in `γ`. -/
noncomputable def pencilGpoly (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) (c₀ : WCol n k w) (i : Fin n) : F[X] :=
  ∑ t : Fin (w + 1),
    pencilKvec dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ (Sum.inl t) * C ((dom i) ^ (t : ℕ))

/-! ## Degree bounds -/

theorem pencilKvec_natDegree_le (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) (c₀ i : WCol n k w) :
    (pencilKvec dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ i).natDegree ≤ w + 1 := by
  classical
  rw [pencilKvec, Matrix.adjugate_apply]
  refine le_trans (natDegree_det_le_sum_colBound _
    (Sum.elim (fun _ : Fin (w + 1) => 1)
      (Sum.elim (fun _ : Fin (w + k) => 0) (fun _ : Fin (3 * w + k - n) => 0))) ?_)
    (le_of_eq (windowPencil_colBound_sum n k w))
  intro a b
  rw [Matrix.updateRow_apply]
  by_cases ha : a = c₀
  · rw [if_pos ha]
    by_cases hb : b = i
    · rw [Pi.single_apply, if_pos hb]
      rcases b with t | s | m <;> simp
    · rw [Pi.single_apply, if_neg hb]
      rcases b with t | s | m <;> simp
  · rw [if_neg ha]
    exact windowPencil_natDegree_le dom k w ℓ₀ R₀ ℓ₁ R₁ (J a) b

theorem pencilGpoly_natDegree_le (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) (c₀ : WCol n k w) (i : Fin n) :
    (pencilGpoly dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ i).natDegree ≤ w + 1 := by
  refine natDegree_sum_le_of_forall_le _ _ fun t _ => ?_
  calc (pencilKvec dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ (Sum.inl t) * C ((dom i) ^ (t : ℕ))).natDegree
      ≤ (pencilKvec dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ (Sum.inl t)).natDegree
        + (C ((dom i) ^ (t : ℕ)) : F[X]).natDegree := natDegree_mul_le
    _ ≤ (w + 1) + 0 := Nat.add_le_add
        (pencilKvec_natDegree_le dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ _) (le_of_eq (natDegree_C _))
    _ = w + 1 := by omega

/-! ## The witness-pinning lemma -/

/-- **Witness complement pinned by the Cramer column.**  If a degree-`< k`
codeword explains the line on `S` (`|S| ≥ n−w`), the WB relations hold, and the
anchor entry does not vanish at `γ`, then the complement of `S` is exactly the
vanishing set of the `g_i` at `γ`. -/
theorem witness_complement_pinned (dom : Fin n ↪ F) {k w : ℕ} (hk : 1 ≤ k)
    {ℓ₀ R₀ ℓ₁ R₁ : F[X]} (hd₀ : ℓ₀.natDegree ≤ w) (hd₁ : ℓ₁.natDegree ≤ w)
    (hr₀ : R₀.natDegree ≤ w + k - 1) (hr₁ : R₁.natDegree ≤ w + k - 1)
    {u₀ u₁ : Fin n → F}
    (hrel₀ : ∀ i, ℓ₀.eval (dom i) * u₀ i = R₀.eval (dom i))
    (hrel₁ : ∀ i, ℓ₁.eval (dom i) * u₁ i = R₁.eval (dom i))
    {J : WCol n k w → Fin (3 * w + k)} {c₀ cs : WCol n k w} {γ : F}
    (hKγ : (pencilKvec dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ cs).eval γ ≠ 0)
    {S : Finset (Fin n)} (hS : n - w ≤ S.card)
    {P : F[X]} (hPdeg : P.degree < k)
    (hag : ∀ i ∈ S, P.eval (dom i) = u₀ i + γ * u₁ i) :
    Finset.univ \ S = Finset.univ.filter
      (fun i => (pencilGpoly dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ i).eval γ = 0) := by
  classical
  -- the identity and its kernel vector
  obtain ⟨Q, h, hQdeg, hhco, hid⟩ := identity_of_agreement dom hk hd₀ hd₁ hr₀ hr₁
    hrel₀ hrel₁ hS hPdeg hag
  set Z : F[X] := ∏ i ∈ Finset.univ \ S, (X - C (dom i)) with hZdef
  have hZne : Z ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => X_sub_C_ne_zero (dom i)
  have hZdeg : Z.natDegree ≤ w := by
    rw [hZdef, Polynomial.natDegree_prod _ _ fun i _ => X_sub_C_ne_zero (dom i)]
    simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
    have h1 : (Finset.univ \ S).card = n - S.card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ S)]
      simp
    have h2 : S.card ≤ n :=
      le_trans (Finset.card_le_card (Finset.subset_univ S)) (by simp)
    omega
  set v := coeffVec n k w Z Q h with hvdef
  have hker : ((windowPencil dom k w ℓ₀ R₀ ℓ₁ R₁).map (Polynomial.eval γ)).mulVec v
      = 0 := windowPencil_mulVec_eq_zero dom k w hZdeg hQdeg hhco hid
  -- restrict to the square selection
  set B := pencilSq dom k w ℓ₀ R₀ ℓ₁ R₁ J with hBdef
  set Bev := B.map (Polynomial.eval γ) with hBevdef
  have hBv : Bev.mulVec v = 0 := by
    funext a
    have hrow := congrFun hker (J a)
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, Matrix.map_apply] at hrow ⊢
    simpa [hBevdef, hBdef, pencilSq, Matrix.submatrix_apply, Matrix.map_apply]
      using hrow
  -- the evaluated adjugate column
  set Kev : WCol n k w → F :=
    fun i => (pencilKvec dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ i).eval γ with hKevdef
  have hKevapp : ∀ i, Kev i = (pencilKvec dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ i).eval γ :=
    fun i => by rw [hKevdef]
  have hKγ' : Kev cs ≠ 0 := by
    rw [hKevapp]
    exact hKγ
  have hadj : Bev.adjugate = (B.adjugate).map (Polynomial.eval γ) := by
    have h := RingHom.map_adjugate (Polynomial.evalRingHom γ) B
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at h
    rw [hBevdef]
    exact h.symm
  have hKevadj : ∀ i, Kev i = Bev.adjugate i c₀ := by
    intro i
    rw [hadj, Matrix.map_apply, hKevapp]
    rfl
  have hBK : ∀ a, Bev a ⬝ᵥ Kev
      = Bev.det * (1 : Matrix (WCol n k w) (WCol n k w) F) a c₀ := by
    intro a
    have hmul := congrFun (congrFun (Matrix.mul_adjugate Bev) a) c₀
    rw [Matrix.smul_apply, smul_eq_mul] at hmul
    rw [← hmul, Matrix.mul_apply]
    simp only [dotProduct]
    exact Finset.sum_congr rfl fun j _ => by rw [hKevadj j]
  -- the updateRow determinant is the anchor entry at γ
  set Bt := Bev.updateRow c₀ (Pi.single cs 1) with hBtdef
  have hdetBt : Bt.det = Kev cs := by
    rw [hBtdef, ← Matrix.adjugate_apply, hKevadj cs]
  have hdetBt0 : Bt.det ≠ 0 := by
    rw [hdetBt]
    exact hKγ'
  -- the cross difference dies
  set u' : WCol n k w → F := fun j => Kev cs * v j - v cs * Kev j with hu'def
  have hu'app : ∀ j, u' j = Kev cs * v j - v cs * Kev j := fun j => by rw [hu'def]
  have hBtu' : Bt.mulVec u' = 0 := by
    funext a
    show Bt.mulVec u' a = 0
    by_cases ha : a = c₀
    · subst ha
      have hrow : Bt a = Pi.single cs 1 := by
        rw [hBtdef]
        exact Matrix.updateRow_self
      calc Bt.mulVec u' a = Bt a ⬝ᵥ u' := rfl
        _ = Pi.single cs 1 ⬝ᵥ u' := by rw [hrow]
        _ = 1 * u' cs := by rw [single_dotProduct]
        _ = u' cs := one_mul _
        _ = 0 := by
            rw [hu'app]
            ring
    · have hrow : Bt a = Bev a := by
        rw [hBtdef]
        exact Matrix.updateRow_ne ha
      have hv0 : Bev a ⬝ᵥ v = 0 := congrFun hBv a
      have hK0 := hBK a
      have h1 : (1 : Matrix (WCol n k w) (WCol n k w) F) a c₀ = 0 :=
        Matrix.one_apply_ne ha
      calc Bt.mulVec u' a = Bt a ⬝ᵥ u' := rfl
        _ = Bev a ⬝ᵥ u' := by rw [hrow]
        _ = Kev cs * (Bev a ⬝ᵥ v) - v cs * (Bev a ⬝ᵥ Kev) := by
            simp only [dotProduct, Finset.mul_sum, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hu'app j]
            ring
        _ = 0 := by
            rw [hv0, hK0, h1, mul_zero, mul_zero, mul_zero, sub_zero]
  have hu'0 : u' = 0 := by
    by_contra hne
    exact hdetBt0 ((Matrix.exists_mulVec_eq_zero_iff).mp ⟨u', hne, hBtu'⟩)
  have hprop : ∀ j, Kev cs * v j = v cs * Kev j := by
    intro j
    have h : u' j = 0 := by
      rw [hu'0]
      rfl
    rw [hu'app j] at h
    exact sub_eq_zero.mp h
  -- v ≠ 0 hence v cs ≠ 0
  have hwzv : wzPoly v = Z := wzPoly_coeffVec hZdeg
  have hvne : v ≠ 0 := by
    intro h0
    apply hZne
    rw [← hwzv, h0, wzPoly_zero]
  have hvcs : v cs ≠ 0 := by
    intro h0
    apply hvne
    funext j
    have h := hprop j
    rw [h0, zero_mul] at h
    rcases mul_eq_zero.mp h with hc | hv
    · exact absurd hc hKγ'
    · exact hv
  -- eval-level proportionality on the domain
  have hgeval : ∀ i : Fin n, (pencilGpoly dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ i).eval γ
      = ∑ t : Fin (w + 1), Kev (Sum.inl t) * (dom i) ^ (t : ℕ) := by
    intro i
    rw [pencilGpoly, eval_finset_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [eval_mul, eval_C, hKevapp]
  have hZeval : ∀ i : Fin n, Z.eval (dom i)
      = ∑ t : Fin (w + 1), v (Sum.inl t) * (dom i) ^ (t : ℕ) := by
    intro i
    rw [← hwzv, wzPoly, eval_finset_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [eval_mul, eval_C, eval_pow, eval_X]
  have hpropD : ∀ i : Fin n, Kev cs * Z.eval (dom i)
      = v cs * (pencilGpoly dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ i).eval γ := by
    intro i
    rw [hZeval i, hgeval i, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have h := hprop (Sum.inl t)
    calc Kev cs * (v (Sum.inl t) * (dom i) ^ (t : ℕ))
        = (Kev cs * v (Sum.inl t)) * (dom i) ^ (t : ℕ) := by ring
      _ = (v cs * Kev (Sum.inl t)) * (dom i) ^ (t : ℕ) := by rw [h]
      _ = v cs * (Kev (Sum.inl t) * (dom i) ^ (t : ℕ)) := by ring
  -- conclude the set equality
  ext i
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_filter]
  constructor
  · intro hiS
    have hZi : Z.eval (dom i) = 0 := by
      rw [hZdef, eval_prod]
      refine Finset.prod_eq_zero (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hiS⟩) ?_
      rw [eval_sub, eval_X, eval_C, sub_self]
    have h := hpropD i
    rw [hZi, mul_zero] at h
    rcases mul_eq_zero.mp h.symm with hc | hg
    · exact absurd hc hvcs
    · exact hg
  · intro hg
    have h := hpropD i
    rw [hg, mul_zero] at h
    have hZi : Z.eval (dom i) = 0 := by
      rcases mul_eq_zero.mp h with hc | hz
      · exact absurd hc hKγ'
      · exact hz
    rw [hZdef, eval_prod] at hZi
    obtain ⟨j, hj, hzero⟩ := Finset.prod_eq_zero_iff.mp hZi
    rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hzero
    have : i = j := dom.injective hzero
    subst this
    exact (Finset.mem_sdiff.mp hj).2

/-! ## The count theorem -/

open Classical in
/-- **THE WINDOW PENCIL LAW (WB-4).**  Any stack with WB representations whose
window pencil is anchored has at most `(w+1) + n(w+1) + 1` mca-bad scalars. -/
theorem badScalars_card_le_of_anchor (dom : Fin n ↪ F) {k w : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    {u₀ u₁ : Fin n → F} {ℓ₀ R₀ ℓ₁ R₁ : F[X]}
    (hd₀ : ℓ₀.natDegree ≤ w) (hd₁ : ℓ₁.natDegree ≤ w)
    (hr₀ : R₀.natDegree ≤ w + k - 1) (hr₁ : R₁.natDegree ≤ w + k - 1)
    (hrel₀ : ∀ i, ℓ₀.eval (dom i) * u₀ i = R₀.eval (dom i))
    (hrel₁ : ∀ i, ℓ₁.eval (dom i) * u₁ i = R₁.eval (dom i))
    {J : WCol n k w → Fin (3 * w + k)} {c₀ cs : WCol n k w}
    (hanchor : pencilKvec dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ cs ≠ 0) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      ≤ (w + 1) + n * (w + 1) + 1 := by
  classical
  set Bad := Finset.univ.filter (fun γ : F => mcaEvent (F := F)
    ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)
    with hBadDef
  set K := pencilKvec dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ with hKdef
  set g : Fin n → F[X] := pencilGpoly dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ with hgdef
  -- every bad scalar has a size-converted witness
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
  -- the pinned-complement consequence for anchored scalars
  have hpinned : ∀ γ ∈ Bad, (K cs).eval γ ≠ 0 →
      ∃ S : Finset (Fin n),
        (∃ c ∈ ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)),
          ∀ i ∈ S, c i = u₀ i + γ • u₁ i) ∧
        ¬ pairJointAgreesOn
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) S u₀ u₁ ∧
        Finset.univ \ S = Finset.univ.filter (fun i => (g i).eval γ = 0) := by
    intro γ hγ hKγ
    rw [hKdef] at hKγ
    obtain ⟨S, hS, ⟨c, hcmem, hag⟩, hno⟩ := hwitness γ hγ
    obtain ⟨P, hPdeg, rfl⟩ := hcmem
    have hag' : ∀ i ∈ S, P.eval (dom i) = u₀ i + γ * u₁ i := by
      intro i hi
      have := hag i hi
      simpa [smul_eq_mul] using this
    have hpin := witness_complement_pinned dom hk hd₀ hd₁ hr₀ hr₁ hrel₀ hrel₁
      (J := J) (c₀ := c₀) (cs := cs) hKγ hS hPdeg hag'
    rw [← hgdef] at hpin
    exact ⟨S, ⟨fun i => P.eval (dom i), ⟨P, hPdeg, rfl⟩, hag⟩, hno, hpin⟩
  -- the three-piece cover
  set Bad₁ := Bad.filter (fun γ => (K cs).eval γ = 0) with hB1def
  set Bad₂ := Bad.filter (fun γ => (K cs).eval γ ≠ 0 ∧
    ∃ i : Fin n, g i ≠ 0 ∧ (g i).eval γ = 0) with hB2def
  set Bad₃ := Bad.filter (fun γ => (K cs).eval γ ≠ 0 ∧
    ∀ i : Fin n, g i ≠ 0 → (g i).eval γ ≠ 0) with hB3def
  have hcover : Bad ⊆ Bad₁ ∪ Bad₂ ∪ Bad₃ := by
    intro γ hγ
    by_cases h1 : (K cs).eval γ = 0
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hγ, h1⟩))
    · by_cases h2 : ∃ i : Fin n, g i ≠ 0 ∧ (g i).eval γ = 0
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hγ, h1, h2⟩))
      · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hγ, h1, ?_⟩)
        intro i hgi hgiv
        exact h2 ⟨i, hgi, hgiv⟩
  -- piece 1: roots of the anchor entry
  have hb1 : Bad₁.card ≤ w + 1 := by
    have hsub : Bad₁ ⊆ (K cs).roots.toFinset := by
      intro γ hγ
      rw [Multiset.mem_toFinset, mem_roots hanchor]
      exact (Finset.mem_filter.mp hγ).2
    calc Bad₁.card ≤ (K cs).roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card (K cs).roots := (K cs).roots.toFinset_card_le
      _ ≤ (K cs).natDegree := (K cs).card_roots'
      _ ≤ w + 1 := pencilKvec_natDegree_le dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ cs
  -- piece 2: the incidence union bound
  have hb2 : Bad₂.card ≤ n * (w + 1) := by
    have hsub : Bad₂ ⊆ Finset.univ.biUnion
        (fun i : Fin n => (g i).roots.toFinset) := by
      intro γ hγ
      obtain ⟨-, -, i, hgi, hgiv⟩ := Finset.mem_filter.mp hγ
      refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ?_⟩
      rw [Multiset.mem_toFinset, mem_roots hgi]
      exact hgiv
    calc Bad₂.card ≤ (Finset.univ.biUnion
          (fun i : Fin n => (g i).roots.toFinset)).card := Finset.card_le_card hsub
      _ ≤ ∑ i : Fin n, (g i).roots.toFinset.card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin n, (w + 1) := by
          refine Finset.sum_le_sum fun i _ => ?_
          calc (g i).roots.toFinset.card
              ≤ Multiset.card (g i).roots := (g i).roots.toFinset_card_le
            _ ≤ (g i).natDegree := (g i).card_roots'
            _ ≤ w + 1 := pencilGpoly_natDegree_le dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ i
      _ = n * (w + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  -- piece 3: the shared-witness class is rigid
  have hb3 : Bad₃.card ≤ 1 := by
    refine Finset.card_le_one.mpr fun γ₁ h₁ γ₂ h₂ => ?_
    obtain ⟨hγ₁bad, hK₁, hall₁⟩ := Finset.mem_filter.mp h₁
    obtain ⟨hγ₂bad, hK₂, hall₂⟩ := Finset.mem_filter.mp h₂
    obtain ⟨S₁, hcw₁, hno₁, hpin₁⟩ := hpinned γ₁ hγ₁bad hK₁
    obtain ⟨S₂, hcw₂, hno₂, hpin₂⟩ := hpinned γ₂ hγ₂bad hK₂
    -- both complements equal the polynomial vanishing set
    have hfix : ∀ γ', ((K cs).eval γ' ≠ 0) →
        (∀ i : Fin n, g i ≠ 0 → (g i).eval γ' ≠ 0) →
        Finset.univ.filter (fun i => (g i).eval γ' = 0)
          = Finset.univ.filter (fun i => g i = 0) := by
      intro γ' hK' hall'
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hv
        by_contra hgi
        exact hall' i hgi hv
      · intro hgi
        rw [hgi]
        simp
    have hS₁ : S₁ = Finset.univ \ Finset.univ.filter (fun i => g i = 0) := by
      rw [← hfix γ₁ hK₁ hall₁, ← hpin₁, Finset.sdiff_sdiff_self_left,
        Finset.univ_inter]
    have hS₂ : S₂ = Finset.univ \ Finset.univ.filter (fun i => g i = 0) := by
      rw [← hfix γ₂ hK₂ hall₂, ← hpin₂, Finset.sdiff_sdiff_self_left,
        Finset.univ_inter]
    have hSS : S₁ = S₂ := by rw [hS₁, hS₂]
    -- the same witness set carries both: rigidity
    refine ProximityGap.MCAWitnessSpread.unique_bad_gamma_common_witness
      (C := rsCode dom k) (S := S₁) (u₀ := u₀) (u₁ := u₁) hno₁ hcw₁ ?_
    rw [hSS]
    exact hcw₂
  -- assemble
  calc Bad.card ≤ (Bad₁ ∪ Bad₂ ∪ Bad₃).card := Finset.card_le_card hcover
    _ ≤ (Bad₁ ∪ Bad₂).card + Bad₃.card := Finset.card_union_le _ _
    _ ≤ Bad₁.card + Bad₂.card + Bad₃.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ (w + 1) + n * (w + 1) + 1 := by
        have := hb1
        have := hb2
        have := hb3
        omega

/-! ## The named residual and the consumer -/

/-- **The single named residual of the window law**: the stack admits WB
representations whose window pencil is anchored — some adjugate entry of some
square row-selection is a nonzero `γ`-polynomial.  Equivalently (not needed
formally): the pencil has corank ≤ 1 over `F(γ)`.  Probe record
(`probe_wb_window_pencil_extremal_class.py`, `probe_wb_window_kernel_family.py`):
0/4000 genuine rational pairs violate corank ≤ 1, and every probed extremal —
including all `w+1`-bad Möbius-symmetric ones — is anchored.

**Post-landing correction (see DISPROOF_LOG 2026-06-12 + `WBPencilWindowCapstone`)**:
anchoredness is NOT universal — class-V stacks (vanishing-denominator rows) can
have corank ≥ 2 for every representation pair; the corrected residual is
`UnanchoredLinear` (unanchored stacks have ≤ n bad scalars; probe record ≤ 2). -/
def WindowPencilAnchored (dom : Fin n ↪ F) (k w : ℕ) (u₀ u₁ : Fin n → F) : Prop :=
  ∃ ℓ₀ R₀ ℓ₁ R₁ : F[X],
    ℓ₀.natDegree ≤ w ∧ ℓ₁.natDegree ≤ w ∧
    R₀.natDegree ≤ w + k - 1 ∧ R₁.natDegree ≤ w + k - 1 ∧
    (∀ i, ℓ₀.eval (dom i) * u₀ i = R₀.eval (dom i)) ∧
    (∀ i, ℓ₁.eval (dom i) * u₁ i = R₁.eval (dom i)) ∧
    ∃ (J : WCol n k w → Fin (3 * w + k)) (c₀ cs : WCol n k w),
      pencilKvec dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ cs ≠ 0

open Classical in
/-- The count under the named residual. -/
theorem badScalars_card_le_of_windowPencilAnchored (dom : Fin n ↪ F) {k w : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    {u₀ u₁ : Fin n → F} (hanch : WindowPencilAnchored dom k w u₀ u₁) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      ≤ (w + 1) + n * (w + 1) + 1 := by
  obtain ⟨ℓ₀, R₀, ℓ₁, R₁, hd₀, hd₁, hr₀, hr₁, hrel₀, hrel₁, J, c₀, cs, hK⟩ := hanch
  exact badScalars_card_le_of_anchor dom hk hδn hd₀ hd₁ hr₀ hr₁ hrel₀ hrel₁ hK

open Classical in
/-- **THE BELOW-UDR LAW, poly(n) form** (conditional on exactly
`WindowPencilAnchored` for doubly-WB-solvable stacks): at every radius
`δ ≤ w/n` below the unique-decoding slack,
`ε_mca(RS, δ) ≤ ((w+1) + n(w+1) + 1)/q`. -/
theorem epsMCA_le_of_anchored (dom : Fin n ↪ F) {k w : ℕ} (hk : 1 ≤ k)
    (hwk : w + k ≤ n) {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    (hanch : ∀ u₀ u₁ : Fin n → F, WBSolvable dom k w u₀ → WBSolvable dom k w u₁ →
      WindowPencilAnchored dom k w u₀ u₁) :
    epsMCA (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
      ≤ (((w + 1) + n * (w + 1) + 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  rw [epsMCA]
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  refine ENNReal.div_le_div_right ?_ _
  by_cases h1 : WBSolvable dom k w (u 1)
  · by_cases h0 : WBSolvable dom k w (u 0)
    · -- doubly solvable: the anchored count
      have := badScalars_card_le_of_windowPencilAnchored dom hk hδn
        (hanch (u 0) (u 1) h0 h1)
      exact_mod_cast this
    · -- offset row far: swap + pencil, ≤ (w+2)+1 ≤ the poly bound
      have hswap := badScalars_card_swap_le
        (rsCode dom k : Submodule F (Fin n → F)) δ (u 0) (u 1)
      have hfar := badScalars_card_le_of_far_snd dom hk hwk hδn
        (u₀ := u 1) (u₁ := u 0) h0
      have : (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
          ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
          (u 0) (u 1) γ)).card ≤ (w + 1) + n * (w + 1) + 1 := by
        have hb := le_trans hswap (Nat.add_le_add_right hfar 1)
        have hnw : w + 1 ≤ n * (w + 1) := Nat.le_mul_of_pos_left _ (by omega)
        omega
      exact_mod_cast this
  · -- direction row far: the pencil bound directly
    have hfar := badScalars_card_le_of_far_snd dom hk hwk hδn
      (u₀ := u 0) (u₁ := u 1) h1
    have : (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
        (u 0) (u 1) γ)).card ≤ (w + 1) + n * (w + 1) + 1 := by
      have hnw : w + 1 ≤ n * (w + 1) := Nat.le_mul_of_pos_left _ (by omega)
      omega
    exact_mod_cast this

open Classical in
/-- The threshold form: under the anchor residual at a below-UDR radius with the
poly(n) budget, the threshold clears it: at production
(`ε* = 2^{−128}`, `q ≥ ((n+1)(w+1)+1)·2^{128}`) the floor moves to the
unique-decoding radius. -/
theorem le_mcaDeltaStar_of_anchored (dom : Fin n ↪ F) {k w : ℕ} (hk : 1 ≤ k)
    (hwk : w + k ≤ n) {δ : ℝ≥0} (hδ1 : δ ≤ 1)
    (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    (hanch : ∀ u₀ u₁ : Fin n → F, WBSolvable dom k w u₀ → WBSolvable dom k w u₁ →
      WindowPencilAnchored dom k w u₀ u₁)
    {εstar : ℝ≥0∞}
    (hbudget : (((w + 1) + n * (w + 1) + 1 : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
      ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := F) (A := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) εstar :=
  ProximityGap.MCAThresholdLedger.le_mcaDeltaStar_of_good _ _ hδ1
    (le_trans (epsMCA_le_of_anchored dom hk hwk hδn hanch) hbudget)

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.witness_complement_pinned
#print axioms ProximityGap.WBPencil.badScalars_card_le_of_anchor
#print axioms ProximityGap.WBPencil.epsMCA_le_of_anchored
#print axioms ProximityGap.WBPencil.le_mcaDeltaStar_of_anchored
