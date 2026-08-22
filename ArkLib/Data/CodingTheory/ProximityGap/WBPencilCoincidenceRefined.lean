/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.WBPencilCorankTwo
import ArkLib.ToMathlib.DesnanotJacobi

/-!
# The refined coincidence count (#371): the Desnanot–Jacobi factorization in Lean

The probe-discovered factorization (`probe_wb_jacobi_factorization.py`: exact
divisibility 8/8, linear quotient) becomes theorem:

* `coincPoly_eq_det_mul_hPair` — **the factorization**
  `coincPoly i j = det B₂ · hPair i j`, where `hPair` is the Vandermonde-weighted
  sum of doubly-updated determinants `DU(t,t')`.  Summing Desnanot–Jacobi over
  ALL `(t,t')` (the diagonal self-cancels inside the identity) avoids
  antisymmetrization plumbing.
* `natDegree_det_le_of_single_rows` — **the degree engine**: singleton rows
  force every permutation through their target columns at degree 0, so the
  determinant degree is bounded by the caps OFF the targets.  Hence
  `deg DU ≤ w−1` and `deg hPair ≤ w−1`: the one-rational-root law is formal
  structure (linear quotient at `w = 2`).
* `badScalars_card_le_of_corank2_refined` — **the refined count**

    `#bad ≤ (w+1) + (n+1) + n²·(w−1)`

  under the double anchor and `hPair`-twin-freeness: the per-pair budget drops
  from `2w+2` to `w−1`, and at `w = 1` the coincidence class is empty.
-/

open Finset Polynomial Matrix
open scoped NNReal ENNReal ProbabilityTheory

set_option linter.unusedSectionVars false

namespace ProximityGap.WBPencil

open ProximityGap.SpikeFloor ArkLib.DesnanotJacobi

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-! ## The singleton-row degree refinement -/

/-- **Degree bound with singleton rows**: rows in `S` of the form
`Pi.single (τ r) 1` route every surviving permutation through their target
columns at degree 0. -/
theorem natDegree_det_le_of_single_rows {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι F[X]) (d : ι → ℕ) (S : Finset ι) (τ : ι → ι)
    (hrow : ∀ r ∈ S, A r = Pi.single (τ r) 1)
    (hA : ∀ i j, (A i j).natDegree ≤ d j) :
    A.det.natDegree ≤ ∑ c ∈ Finset.univ.filter (fun c => c ∉ S.image τ), d c := by
  classical
  rw [Matrix.det_apply]
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  by_cases hforce : ∀ r ∈ S, σ (τ r) = r
  · have hterm : ∀ c : ι, ((A (σ c) c).natDegree)
        ≤ (if c ∈ S.image τ then 0 else d c) := by
      intro c
      by_cases hcim : c ∈ S.image τ
      · rw [if_pos hcim]
        obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hcim
        rw [hforce r hr, hrow r hr, Pi.single_eq_same]
        simp
      · rw [if_neg hcim]
        exact hA _ _
    have hprod : (∏ c, A (σ c) c).natDegree
        ≤ ∑ c, (if c ∈ S.image τ then 0 else d c) :=
      le_trans (natDegree_prod_le _ _) (Finset.sum_le_sum fun c _ => hterm c)
    have hsum : (∑ c, (if c ∈ S.image τ then 0 else d c))
        = ∑ c ∈ Finset.univ.filter (fun c => c ∉ S.image τ), d c := by
      rw [Finset.sum_ite, Finset.sum_const, smul_eq_mul, mul_zero, zero_add]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · rw [h, one_smul, ← hsum]
      exact hprod
    · rw [h, Units.neg_smul, one_smul, natDegree_neg, ← hsum]
      exact hprod
  · push_neg at hforce
    obtain ⟨r, hr, hne⟩ := hforce
    have hzero : A (σ (σ.symm r)) (σ.symm r) = 0 := by
      rw [Equiv.apply_symm_apply, hrow r hr, Pi.single_apply]
      rw [if_neg ?_]
      intro h
      apply hne
      rw [← h, Equiv.apply_symm_apply]
    have hprod : (∏ c, A (σ c) c) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ (σ.symm r)) hzero
    rw [hprod]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · rw [h, one_smul]
      simp
    · rw [h, Units.neg_smul, one_smul, neg_zero]
      simp

/-! ## The factorization -/

/-- The doubly-updated determinant at a locator pair. -/
noncomputable def pencilDU (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) (c₀ c₀' cs cs' : WCol n k w)
    (t t' : Fin (w + 1)) : F[X] :=
  (((pencilSqDU dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs').updateRow c₀
    (Pi.single (Sum.inl t) 1)).updateRow c₀' (Pi.single (Sum.inl t') 1)).det

/-- The refined coincidence cofactor. -/
noncomputable def pencilHPair (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) (c₀ c₀' cs cs' : WCol n k w)
    (i j : Fin n) : F[X] :=
  ∑ t : Fin (w + 1), ∑ t' : Fin (w + 1),
    C ((dom i) ^ (t : ℕ)) * C ((dom j) ^ (t' : ℕ))
      * pencilDU dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' t t'

/-- **The Desnanot–Jacobi factorization of the coincidence polynomial.** -/
theorem coincPoly_eq_det_mul_hPair (dom : Fin n ↪ F) (k w : ℕ)
    (ℓ₀ R₀ ℓ₁ R₁ : F[X]) (J : WCol n k w → Fin (3 * w + k))
    {c₀ c₀' : WCol n k w} (cs cs' : WCol n k w) (hcc : c₀ ≠ c₀') (i j : Fin n) :
    coincPoly dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' i j
      = (pencilSqDU dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs').det
        * pencilHPair dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' i j := by
  classical
  set B2 := pencilSqDU dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' with hB2
  have hDJ : ∀ t t' : Fin (w + 1),
      B2.adjugate (Sum.inl t) c₀ * B2.adjugate (Sum.inl t') c₀'
        - B2.adjugate (Sum.inl t) c₀' * B2.adjugate (Sum.inl t') c₀
      = B2.det * pencilDU dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' t t' := by
    intro t t'
    exact desnanot_jacobi B2 (i₁ := Sum.inl t) (i₂ := Sum.inl t') hcc
  have hK : ∀ (col : WCol n k w) (t : Fin (w + 1)),
      pencilK dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' col (Sum.inl t)
        = B2.adjugate (Sum.inl t) col := fun col t => rfl
  calc coincPoly dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' i j
      = (∑ t : Fin (w + 1), B2.adjugate (Sum.inl t) c₀ * C ((dom i) ^ (t : ℕ)))
          * (∑ t' : Fin (w + 1), B2.adjugate (Sum.inl t') c₀' * C ((dom j) ^ (t' : ℕ)))
        - (∑ t : Fin (w + 1), B2.adjugate (Sum.inl t) c₀ * C ((dom j) ^ (t : ℕ)))
          * (∑ t' : Fin (w + 1), B2.adjugate (Sum.inl t') c₀' * C ((dom i) ^ (t' : ℕ))) := by
        rw [coincPoly, pencilG, pencilG, pencilG, pencilG]
        simp only [hK]
    _ = (∑ t : Fin (w + 1), ∑ t' : Fin (w + 1),
          C ((dom i) ^ (t : ℕ)) * C ((dom j) ^ (t' : ℕ))
            * (B2.adjugate (Sum.inl t) c₀ * B2.adjugate (Sum.inl t') c₀'))
        - (∑ t : Fin (w + 1), ∑ t' : Fin (w + 1),
          C ((dom i) ^ (t : ℕ)) * C ((dom j) ^ (t' : ℕ))
            * (B2.adjugate (Sum.inl t) c₀' * B2.adjugate (Sum.inl t') c₀)) := by
        congr 1
        · rw [Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => ?_
          ring
        · rw [Finset.sum_mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => ?_
          ring
    _ = ∑ t : Fin (w + 1), ∑ t' : Fin (w + 1),
          C ((dom i) ^ (t : ℕ)) * C ((dom j) ^ (t' : ℕ))
            * (B2.adjugate (Sum.inl t) c₀ * B2.adjugate (Sum.inl t') c₀'
              - B2.adjugate (Sum.inl t) c₀' * B2.adjugate (Sum.inl t') c₀) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun t' _ => ?_
        ring
    _ = ∑ t : Fin (w + 1), ∑ t' : Fin (w + 1),
          C ((dom i) ^ (t : ℕ)) * C ((dom j) ^ (t' : ℕ))
            * (B2.det * pencilDU dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' t t') := by
        refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => ?_
        rw [hDJ t t']
    _ = B2.det * pencilHPair dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' i j := by
        rw [pencilHPair, Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t' _ => ?_
        ring

/-! ## The degree refinement -/

theorem pencilDU_natDegree_le (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) {c₀ c₀' : WCol n k w} (cs cs' : WCol n k w)
    (hcc : c₀ ≠ c₀') (t t' : Fin (w + 1)) (htt : t ≠ t') :
    (pencilDU dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' t t').natDegree ≤ w - 1 := by
  classical
  rw [pencilDU]
  set τ : WCol n k w → WCol n k w := fun c =>
    if c = c₀ then Sum.inl t else Sum.inl t' with hτ
  have hτ0 : τ c₀ = Sum.inl t := by
    simp [hτ]
  have hτ0' : τ c₀' = Sum.inl t' := by
    simp [hτ, Ne.symm hcc]
  have hbound := natDegree_det_le_of_single_rows (F := F)
    (((pencilSqDU dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs').updateRow c₀
      (Pi.single (Sum.inl t) 1)).updateRow c₀' (Pi.single (Sum.inl t') 1))
    (Sum.elim (fun _ : Fin (w + 1) => 1)
      (Sum.elim (fun _ : Fin (w + k) => 0) (fun _ : Fin (3 * w + k - n) => 0)))
    ({c₀, c₀'} : Finset (WCol n k w)) τ ?_ ?_
  · refine le_trans hbound (le_of_eq ?_)
    -- the image is the two locator columns; the cap-sum off them is w − 1
    have himg : ({c₀, c₀'} : Finset (WCol n k w)).image τ
        = ({Sum.inl t, Sum.inl t'} : Finset (WCol n k w)) := by
      rw [Finset.image_insert, Finset.image_singleton, hτ0, hτ0']
    rw [himg]
    -- sum of caps off {inl t, inl t'}: total (w+1) minus the two units
    have htotal : (∑ c : WCol n k w, Sum.elim (fun _ : Fin (w + 1) => 1)
        (Sum.elim (fun _ : Fin (w + k) => 0)
          (fun _ : Fin (3 * w + k - n) => 0)) c) = w + 1 :=
      windowPencil_colBound_sum n k w
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset (WCol n k w))
      (fun c => c ∉ ({Sum.inl t, Sum.inl t'} : Finset (WCol n k w)))
      (Sum.elim (fun _ : Fin (w + 1) => 1)
        (Sum.elim (fun _ : Fin (w + k) => 0) (fun _ : Fin (3 * w + k - n) => 0)))
    have hin : (∑ c ∈ Finset.univ.filter
        (fun c => ¬ c ∉ ({Sum.inl t, Sum.inl t'} : Finset (WCol n k w))),
        Sum.elim (fun _ : Fin (w + 1) => 1)
          (Sum.elim (fun _ : Fin (w + k) => 0)
            (fun _ : Fin (3 * w + k - n) => 0)) c) = 2 := by
      have hfilter : Finset.univ.filter
          (fun c => ¬ c ∉ ({Sum.inl t, Sum.inl t'} : Finset (WCol n k w)))
          = ({Sum.inl t, Sum.inl t'} : Finset (WCol n k w)) := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
      rw [hfilter, Finset.sum_pair (fun h => htt (Sum.inl.inj h))]
      simp
    omega
  · intro r hr
    rcases Finset.mem_insert.mp hr with h | h
    · rw [h, hτ0]
      rw [Matrix.updateRow_ne hcc, Matrix.updateRow_self]
    · have h' : r = c₀' := Finset.mem_singleton.mp h
      rw [h', hτ0', Matrix.updateRow_self]
  · intro a b
    by_cases h2 : a = c₀'
    · rw [h2, Matrix.updateRow_self, Pi.single_apply]
      by_cases hb : b = Sum.inl t'
      · rw [if_pos hb]
        rcases b with x | x | x <;> simp
      · rw [if_neg hb]
        rcases b with x | x | x <;> simp
    · rw [Matrix.updateRow_ne h2]
      by_cases h1 : a = c₀
      · rw [h1, Matrix.updateRow_self, Pi.single_apply]
        by_cases hb : b = Sum.inl t
        · rw [if_pos hb]
          rcases b with x | x | x <;> simp
        · rw [if_neg hb]
          rcases b with x | x | x <;> simp
      · rw [Matrix.updateRow_ne h1]
        exact pencilSqDU_natDegree_le dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' a b

theorem pencilHPair_natDegree_le (dom : Fin n ↪ F) (k w : ℕ) (ℓ₀ R₀ ℓ₁ R₁ : F[X])
    (J : WCol n k w → Fin (3 * w + k)) {c₀ c₀' : WCol n k w} (cs cs' : WCol n k w)
    (hcc : c₀ ≠ c₀') (i j : Fin n) :
    (pencilHPair dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' i j).natDegree ≤ w - 1 := by
  classical
  refine natDegree_sum_le_of_forall_le _ _ fun t _ => ?_
  refine natDegree_sum_le_of_forall_le _ _ fun t' _ => ?_
  by_cases htt : t = t'
  · -- the diagonal term vanishes: duplicate singleton rows
    have hzero : pencilDU dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' t t' = 0 := by
      rw [pencilDU]
      refine Matrix.det_zero_of_row_eq hcc ?_
      rw [Matrix.updateRow_ne hcc, Matrix.updateRow_self, Matrix.updateRow_self,
        htt]
    rw [hzero, mul_zero]
    simp
  · calc (C ((dom i) ^ (t : ℕ)) * C ((dom j) ^ (t' : ℕ))
        * pencilDU dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' t t').natDegree
        ≤ (C ((dom i) ^ (t : ℕ)) * C ((dom j) ^ (t' : ℕ))).natDegree
          + (pencilDU dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' t t').natDegree :=
          natDegree_mul_le
      _ ≤ 0 + (w - 1) := Nat.add_le_add
          (by rw [← C_mul]; exact le_of_eq (natDegree_C _))
          (pencilDU_natDegree_le dom k w ℓ₀ R₀ ℓ₁ R₁ J cs cs' hcc t t' htt)
      _ = w - 1 := by omega

/-! ## The refined count -/

open Classical in
/-- **THE REFINED CORANK-2 COUNT**: with the Desnanot–Jacobi factorization, the
per-pair coincidence budget drops from `2w+2` to `w−1`:

  `#bad ≤ (w+1) + (n+1) + n²·(w−1)`

under the double anchor and `hPair`-twin-freeness.  At `w = 1` the coincidence
class is empty. -/
theorem badScalars_card_le_of_corank2_refined (dom : Fin n ↪ F) {k w : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0} (hδn : δ * (Fintype.card (Fin n) : ℝ≥0) ≤ w)
    {u₀ u₁ : Fin n → F} {ℓ₀ R₀ ℓ₁ R₁ : F[X]}
    (hd₀ : ℓ₀.natDegree ≤ w) (hd₁ : ℓ₁.natDegree ≤ w)
    (hr₀ : R₀.natDegree ≤ w + k - 1) (hr₁ : R₁.natDegree ≤ w + k - 1)
    (hrel₀ : ∀ i, ℓ₀.eval (dom i) * u₀ i = R₀.eval (dom i))
    (hrel₁ : ∀ i, ℓ₁.eval (dom i) * u₁ i = R₁.eval (dom i))
    {J : WCol n k w → Fin (3 * w + k)} {c₀ c₀' cs cs' : WCol n k w}
    (hcc : c₀ ≠ c₀')
    (hdet : (pencilSqDU dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs').det ≠ 0)
    (htwin : ∀ i j : Fin n, i ≠ j →
      pencilHPair dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' i j ≠ 0) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)).card
      ≤ (w + 1) + (n + 1) + n * n * (w - 1) := by
  classical
  -- the coincidence twin-freeness transfers through the factorization
  have htwin' : ∀ i j : Fin n, i ≠ j →
      coincPoly dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' i j ≠ 0 := by
    intro i j hij
    rw [coincPoly_eq_det_mul_hPair dom k w ℓ₀ R₀ ℓ₁ R₁ J cs cs' hcc i j]
    exact mul_ne_zero hdet (htwin i j hij)
  -- run the un-refined count's argument, replacing the root bound:
  -- every bad scalar in the coincidence class roots hPair (the det factor is
  -- excluded by the class condition), so the per-pair budget is w − 1.
  have hbase := badScalars_card_le_of_corank2 dom hk hδn hd₀ hd₁ hr₀ hr₁
    hrel₀ hrel₁ hcc hdet htwin'
  -- we reprove the count with the refined class-3 budget by repeating the
  -- cover argument; the only changed piece is the biUnion target.
  set Bad := Finset.univ.filter (fun γ : F => mcaEvent (F := F)
    ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ)
    with hBadDef
  set B2det := (pencilSqDU dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs').det with hB2detdef
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
  have hb1 : Bad₁.card ≤ w + 1 := by
    have hsub : Bad₁ ⊆ B2det.roots.toFinset := by
      intro γ hγ
      rw [Multiset.mem_toFinset, mem_roots hdet]
      exact (Finset.mem_filter.mp hγ).2
    calc Bad₁.card ≤ B2det.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card B2det.roots := B2det.roots.toFinset_card_le
      _ ≤ B2det.natDegree := B2det.card_roots'
      _ ≤ w + 1 := pencilSqDU_det_natDegree_le dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs'
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
  -- class 3 with the REFINED budget: bad scalars root hPair (degree ≤ w−1)
  have hb3 : Bad₃.card ≤ n * n * (w - 1) := by
    have hsub : Bad₃ ⊆ (Finset.univ ×ˢ (Finset.univ : Finset (Fin n))).biUnion
        (fun p => (pencilHPair dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs'
          p.1 p.2).roots.toFinset) := by
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
      obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp
        (by omega : 1 < (Finset.univ \ f γ).card)
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
      -- the coincidence value vanishes; the det-factor does not: hPair roots γ
      have hcoincγ : (coincPoly dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' i j).eval γ
          = 0 := by
        rw [coincPoly, eval_sub, eval_mul, eval_mul]
        rw [← hGi1, ← hGi2, ← hGj1, ← hGj2]
        exact hdet2
      have hHγ : (pencilHPair dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' i j).eval γ
          = 0 := by
        have := hcoincγ
        rw [coincPoly_eq_det_mul_hPair dom k w ℓ₀ R₀ ℓ₁ R₁ J cs cs' hcc i j,
          eval_mul] at this
        rcases mul_eq_zero.mp this with hd | hh
        · exact absurd hd hdetγ
        · exact hh
      refine Finset.mem_biUnion.mpr ⟨(i, j), Finset.mem_product.mpr
        ⟨Finset.mem_univ i, Finset.mem_univ j⟩, ?_⟩
      rw [Multiset.mem_toFinset, mem_roots (htwin i j hij)]
      exact hHγ
    calc Bad₃.card ≤ ((Finset.univ ×ˢ (Finset.univ : Finset (Fin n))).biUnion
          (fun p => (pencilHPair dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs'
            p.1 p.2).roots.toFinset)).card := Finset.card_le_card hsub
      _ ≤ ∑ p ∈ Finset.univ ×ˢ (Finset.univ : Finset (Fin n)),
            (pencilHPair dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs'
              p.1 p.2).roots.toFinset.card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ Finset.univ ×ˢ (Finset.univ : Finset (Fin n)), (w - 1) := by
          refine Finset.sum_le_sum fun p _ => ?_
          calc (pencilHPair dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs'
                p.1 p.2).roots.toFinset.card
              ≤ Multiset.card (pencilHPair dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs'
                  p.1 p.2).roots := Multiset.toFinset_card_le _
            _ ≤ (pencilHPair dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs'
                  p.1 p.2).natDegree := Polynomial.card_roots' _
            _ ≤ w - 1 := pencilHPair_natDegree_le dom k w ℓ₀ R₀ ℓ₁ R₁ J cs cs'
                  hcc p.1 p.2
      _ = n * n * (w - 1) := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_product]
          simp [mul_assoc]
  calc Bad.card ≤ (Bad₁ ∪ Bad₂ ∪ Bad₃).card := Finset.card_le_card hcover
    _ ≤ (Bad₁ ∪ Bad₂).card + Bad₃.card := Finset.card_union_le _ _
    _ ≤ Bad₁.card + Bad₂.card + Bad₃.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ (w + 1) + (n + 1) + n * n * (w - 1) := by
        have := hb1
        have := hb2
        have := hb3
        omega

open Classical in
omit [DecidableEq F] in
/-- Probability form of `badScalars_card_le_of_corank2_refined`: under the same
double-update anchor and `hPair`-twin-freeness hypotheses, the fixed-stack
`mcaEvent` probability is bounded by the refined corank-2 count divided by the
field size. -/
theorem mcaEvent_prob_le_of_corank2_refined (dom : Fin n ↪ F) {k w : ℕ} (hk : 1 ≤ k)
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
      pencilHPair dom k w ℓ₀ R₀ ℓ₁ R₁ J c₀ c₀' cs cs' i j ≠ 0) :
    Pr_{ let γ ←$ᵖ F }[mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ]
      ≤ (((((w + 1) + (n + 1) + n * n * (w - 1) : ℕ) : ℝ≥0) : ℝ≥0∞)
          / (((Fintype.card F : ℕ) : ℝ≥0) : ℝ≥0∞)) := by
  rw [prob_uniform_eq_card_filter_div_card]
  gcongr
  exact badScalars_card_le_of_corank2_refined dom hk hδn hd₀ hd₁ hr₀ hr₁
    hrel₀ hrel₁ hcc hdet htwin

end ProximityGap.WBPencil

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.WBPencil.natDegree_det_le_of_single_rows
#print axioms ProximityGap.WBPencil.coincPoly_eq_det_mul_hPair
#print axioms ProximityGap.WBPencil.pencilHPair_natDegree_le
#print axioms ProximityGap.WBPencil.badScalars_card_le_of_corank2_refined
#print axioms ProximityGap.WBPencil.mcaEvent_prob_le_of_corank2_refined
