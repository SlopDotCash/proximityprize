/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BoundarySliceExact

/-!
# The Schur-ladder reduction (#371): the bad set as a subset-sum set

The probe-discovered, here-proven law behind the ratio-collision census: at the
**ladder stack** `(u₀, u₁) = (x^{k+1}, x^k)` the interpolation residual obeys the
classical Schur identity

  **`e_t(x^{k+1}) = (∑ points of t) · e_t(x^k)`**

(`det[1, x, …, x^{k-1}, x^{k+1}] = e₁ · Vandermonde`, by reducing the top column
modulo `∏ (X − xᵢ)`: the difference `X^{k+1} − e₁X^k − ∏(X − xᵢ)` has degree `< k`,
so its value column is spanned by the power columns).  Hence the residual *ratio*
of every tuple is `−(sum of its domain points)`, and the boundary-slice exact law
specializes to

  **`badSet = −{ subset sums of (k+1)-subsets of the domain }`**

— the bad-scalar set at the boundary radius IS the negated `(k+1)`-fold subset-sum
set of the evaluation domain.  For smooth domains (2-power multiplicative
subgroups) the cardinality of this set is computed EXACTLY by the subset-sum
spectrum (`TwoPowerSubsetSumSpectrum`: `Σ_a 2^a·C(h,a)` per stratum), so the two
census results fuse: the threshold count for the ladder stack is the spectrum, the
collisions are classified by antipodal pairs (`x + (−x)` cancels, leaving a domain
point), and the probe-measured `40 = spectrum < 56 = C(8,3)` instance is explained
in full.

Probe verification (`scripts/probes/probe_ratio_collision_census.py`): the Schur
law holds at `56/56` triples (`k = 2`) and `70/70` quadruples (`k = 3`) at
`p = 12289, n = 8`; the collided ratios at the ladder stack are exactly `μ₈`, each
owned by the `3` triples containing an antipodal pair.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- The residual depends only on the values of `y` on the tuple. -/
theorem residual_congr (dom : Fin n ↪ F) (k : ℕ) (t : Fin (k + 1) → Fin n)
    {y z : Fin n → F} (h : ∀ a : Fin (k + 1), y (t a) = z (t a)) :
    residual dom k t y = residual dom k t z := by
  unfold residual borderedMatrix
  congr 1
  funext a b
  by_cases hb : (b : ℕ) < k
  · rw [if_pos hb, if_pos hb]
  · rw [if_neg hb, if_neg hb, h a]

/-- **The Schur-ladder identity**: the residual of the `(k+1)`-st power column is
the point sum times the residual of the `k`-th power column (no injectivity
needed). -/
theorem residual_ladder_schur (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    (t : Fin (k + 1) → Fin n) :
    residual dom k t (fun i => (dom i) ^ (k + 1))
      = (∑ a, dom (t a)) * residual dom k t (fun i => (dom i) ^ k) := by
  set e₁ : F := ∑ a, dom (t a) with he₁
  set P : F[X] := ∏ a : Fin (k + 1), (X - C (dom (t a))) with hP
  have hPmonic : P.Monic :=
    monic_prod_of_monic _ _ fun a _ => monic_X_sub_C _
  have hPdeg : P.natDegree = k + 1 := by
    rw [hP, natDegree_prod_of_monic _ _ fun a _ => monic_X_sub_C _]
    simp
  have hPk : P.coeff k = -e₁ := by
    have h := prod_X_sub_C_coeff_card_pred (Finset.univ : Finset (Fin (k + 1)))
      (fun a => dom (t a)) (by simp)
    simpa [he₁] using h
  set R : F[X] := X ^ (k + 1) - C e₁ * X ^ k - P with hR
  -- all coefficients of R at index ≥ k vanish
  have hcoeff : ∀ m : ℕ, k ≤ m → R.coeff m = 0 := by
    intro m hm
    rw [hR]
    simp only [coeff_sub, coeff_C_mul, coeff_X_pow]
    rcases Nat.lt_trichotomy m (k + 1) with h | rfl | h
    · have hmk : m = k := by omega
      subst hmk
      rw [if_neg (by omega), if_pos rfl, hPk]
      ring
    · rw [if_pos rfl, if_neg (by omega),
        show P.coeff (k + 1) = 1 from hPdeg ▸ hPmonic.coeff_natDegree]
      ring
    · rw [if_neg (by omega), if_neg (by omega),
        coeff_eq_zero_of_natDegree_lt (by rw [hPdeg]; omega)]
      ring
  have hRdeg : R.natDegree < k := by
    by_cases hR0 : R = 0
    · rw [hR0, natDegree_zero]
      omega
    · rw [Polynomial.natDegree_lt_iff_degree_lt hR0]
      rw [Polynomial.degree_lt_iff_coeff_zero]
      intro m hm
      exact hcoeff m (by exact_mod_cast hm)
  -- the pointwise column decomposition
  have hpoint : ∀ a : Fin (k + 1),
      (dom (t a)) ^ (k + 1) = R.eval (dom (t a)) + e₁ * (dom (t a)) ^ k := by
    intro a
    have hPz : P.eval (dom (t a)) = 0 := by
      rw [hP, eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp)
    rw [hR]
    simp only [eval_sub, eval_pow, eval_mul, eval_C, eval_X, hPz]
    ring
  calc residual dom k t (fun i => (dom i) ^ (k + 1))
      = residual dom k t (fun i => R.eval (dom i) + e₁ * (dom i) ^ k) :=
        residual_congr dom k t fun a => hpoint a
    _ = residual dom k t (fun i => R.eval (dom i))
          + e₁ * residual dom k t (fun i => (dom i) ^ k) :=
        residual_line dom k t _ _ e₁
    _ = e₁ * residual dom k t (fun i => (dom i) ^ k) := by
        rw [residual_eq_zero_of_extends dom k t (P := R) hRdeg fun a => rfl,
          zero_add]

/-- **The ladder ratio law**: every tuple's residual ratio at the ladder stack is
the negated sum of its domain points. -/
theorem ladder_ratio_eq (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    (t : Fin (k + 1) → Fin n)
    (h1 : residual dom k t (fun i => (dom i) ^ k) ≠ 0) :
    -(residual dom k t (fun i => (dom i) ^ (k + 1)))
        / residual dom k t (fun i => (dom i) ^ k)
      = -∑ a, dom (t a) := by
  rw [residual_ladder_schur dom hk t, neg_div, mul_div_assoc, div_self h1,
    mul_one]

open Classical in
/-- The injective-tuple sum image is the `(k+1)`-subset sum image. -/
theorem injTuple_image_sum_eq (g : Fin n → F) (k : ℕ) :
    (Finset.univ.filter
        (fun t : Fin (k + 1) → Fin n => Function.Injective t)).image
      (fun t => ∑ a, g (t a))
    = (Finset.univ.powersetCard (k + 1)).image (fun S => ∑ i ∈ S, g i) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_powersetCard]
  constructor
  · rintro ⟨t, htinj, rfl⟩
    refine ⟨Finset.univ.image t, ⟨Finset.subset_univ _, ?_⟩, ?_⟩
    · rw [Finset.card_image_of_injective _ htinj, Finset.card_univ,
        Fintype.card_fin]
    · rw [Finset.sum_image fun a _ b _ h => htinj h]
  · rintro ⟨S, ⟨-, hcard⟩, rfl⟩
    set t : Fin (k + 1) → Fin n :=
      fun a => (S.equivFin.symm (Fin.cast hcard.symm a) : Fin n) with ht
    have htinj : Function.Injective t := by
      intro a b hab
      have h1 : (S.equivFin.symm (Fin.cast hcard.symm a))
          = S.equivFin.symm (Fin.cast hcard.symm b) := Subtype.ext hab
      exact Fin.cast_injective _ (S.equivFin.symm.injective h1)
    refine ⟨t, htinj, ?_⟩
    have himg : Finset.univ.image t = S := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
        exact (S.equivFin.symm (Fin.cast hcard.symm a)).2
      · rw [Finset.card_image_of_injective _ htinj, Finset.card_univ,
          Fintype.card_fin, hcard]
    rw [← himg, Finset.sum_image fun a _ b _ h => htinj h]

open Classical in
/-- **THE LADDER-STACK BAD SET IS THE NEGATED SUBSET-SUM SET**: at the boundary
radius and under strong farness of `x^k`, the bad scalars of the ladder stack
`(x^{k+1}, x^k)` are exactly the negated `(k+1)`-fold subset sums of the domain.
This fuses the boundary-slice exact law with the subset-sum spectrum: for 2-power
smooth domains the bad-scalar COUNT is computed exactly by
`TwoPowerSubsetSumSpectrum`. -/
theorem boundary_slice_ladder_badSet_eq (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (k + 1 : ℕ))
    (hμ : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c (fun i => (dom i) ^ k)).card ≤ k) :
    Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
        (fun i => (dom i) ^ (k + 1)) (fun i => (dom i) ^ k) γ)
      = (Finset.univ.powersetCard (k + 1)).image
          (fun S : Finset (Fin n) => -∑ i ∈ S, dom i) := by
  -- strong farness gives every injective tuple a nonzero direction residual
  have hallres : ∀ t : Fin (k + 1) → Fin n, Function.Injective t →
      residual dom k t (fun i => (dom i) ^ k) ≠ 0 := by
    intro t htinj hres
    obtain ⟨c, hcC, hcag⟩ := extension_of_residual_eq_zero dom t htinj hres
    have hsub : Finset.univ.image t ⊆ agreeSet c (fun i => (dom i) ^ k) := by
      intro x hx
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
      rw [agreeSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hcag a⟩
    have hcard : k + 1 ≤ (agreeSet c (fun i => (dom i) ^ k)).card := by
      calc k + 1 = (Finset.univ.image t).card := by
            rw [Finset.card_image_of_injective _ htinj, Finset.card_univ,
              Fintype.card_fin]
        _ ≤ _ := Finset.card_le_card hsub
    have := hμ c hcC
    omega
  refine (boundary_slice_badSet_eq dom hk hlo hhi
    (u₀ := fun i => (dom i) ^ (k + 1)) hμ).trans ?_
  -- the ratio image is the negated-point-sum image
  have h1 : (Finset.univ.filter
        (fun t : Fin (k + 1) → Fin n => Function.Injective t)).image
      (fun t => -(residual dom k t (fun i => (dom i) ^ (k + 1)))
        / residual dom k t (fun i => (dom i) ^ k))
      = (Finset.univ.filter
        (fun t : Fin (k + 1) → Fin n => Function.Injective t)).image
      (fun t => ∑ a, (fun i => -(dom i)) (t a)) := by
    refine Finset.image_congr fun t ht => ?_
    have htinj : Function.Injective t := by
      have := Finset.mem_coe.mp ht
      exact (Finset.mem_filter.mp this).2
    rw [ladder_ratio_eq dom hk t (hallres t htinj)]
    simp
  rw [h1, injTuple_image_sum_eq (fun i => -(dom i)) k]
  refine Finset.image_congr fun S _ => ?_
  simp

open Classical in
/-- Cardinality form of `boundary_slice_ladder_badSet_eq`: at the boundary slice, the
ladder-stack bad-scalar count is the number of distinct `(k+1)`-subset sums of the
domain.  The negation in the set-level statement does not change cardinality. -/
theorem boundary_slice_ladder_badSet_card_eq (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (k + 1 : ℕ))
    (hμ : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c (fun i => (dom i) ^ k)).card ≤ k) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
        (fun i => (dom i) ^ (k + 1)) (fun i => (dom i) ^ k) γ)).card
      = ((Finset.univ.powersetCard (k + 1)).image
          (fun S : Finset (Fin n) => ∑ i ∈ S, dom i)).card := by
  classical
  set A : Finset (Finset (Fin n)) := Finset.univ.powersetCard (k + 1) with hA
  set σ : Finset (Fin n) → F := fun S => ∑ i ∈ S, dom i with hσ
  calc
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
        (fun i => (dom i) ^ (k + 1)) (fun i => (dom i) ^ k) γ)).card
        = (A.image fun S => -σ S).card := by
          rw [boundary_slice_ladder_badSet_eq dom hk hlo hhi hμ, hA, hσ]
    _ = (A.image σ).card := by
          rw [← Finset.card_image_of_injective (A.image σ) neg_injective]
          congr 1
          ext x
          simp [hσ]
    _ = ((Finset.univ.powersetCard (k + 1)).image
          (fun S : Finset (Fin n) => ∑ i ∈ S, dom i)).card := by
          rw [hA, hσ]

open Classical in
/-- Coarse counting form of `boundary_slice_ladder_badSet_card_eq`: the ladder-stack
bad-scalar count at the boundary slice is bounded by the number of `(k+1)`-subsets of
the domain.  Exact-count arguments should use `boundary_slice_ladder_badSet_card_eq`;
this corollary is the import-light generic ceiling. -/
theorem boundary_slice_ladder_badSet_card_le_choose (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (k + 1 : ℕ))
    (hμ : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c (fun i => (dom i) ^ k)).card ≤ k) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
        (fun i => (dom i) ^ (k + 1)) (fun i => (dom i) ^ k) γ)).card
      ≤ n.choose (k + 1) := by
  rw [boundary_slice_ladder_badSet_card_eq dom hk hlo hhi hμ]
  calc
    ((Finset.univ.powersetCard (k + 1)).image
        (fun S : Finset (Fin n) => ∑ i ∈ S, dom i)).card
        ≤ (Finset.univ.powersetCard (k + 1) : Finset (Finset (Fin n))).card :=
          Finset.card_image_le
    _ = n.choose (k + 1) := by
          rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.residual_ladder_schur
#print axioms ProximityGap.Ownership.boundary_slice_ladder_badSet_eq
#print axioms ProximityGap.Ownership.boundary_slice_ladder_badSet_card_eq
#print axioms ProximityGap.Ownership.boundary_slice_ladder_badSet_card_le_choose
