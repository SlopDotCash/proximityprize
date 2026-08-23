/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LadderSchurReduction

/-!
# The master modular reduction (#371): every residual is a remainder coefficient

The full generalization of the Schur-ladder identity: for ANY polynomial `Q`, the
interpolation residual of the value column `Q ∘ dom` factors through reduction
modulo the tuple's node polynomial `P = ∏ (X − xᵢ)`:

  **`e_t(Q ∘ dom) = (Q %ₘ P).coeff k · e_t(x^k)`**

(the remainder has degree ≤ k; its sub-`k` part is spanned by the power columns
and dies, its `X^k`-coefficient survives as the multiplier of the Vandermonde
column).  Since EVERY word on the domain is a polynomial evaluation, this turns
the entire boundary-slice census into modular arithmetic:

  **`badSet(Q₀, Q₁) = { −(Q₀ %ₘ P_S).coeff k / (Q₁ %ₘ P_S).coeff k :
       S a (k+1)-subset }`** — exactly,

for strongly-far `Q₁`-columns at the boundary radius
(`boundary_slice_badSet_modular`).  The threshold value `ε_mca` for every far
stack is the number of distinct values of this *modular Wronskian ratio* over
`(k+1)`-subsets of the domain, divided by `q`.  The Schur-ladder law is the case
`Q₀ = X^{k+1}, Q₁ = X^k` (remainder coefficients `−e₁` and `1`); general monomial
stacks `X^{k+d}` give complete homogeneous symmetric values `h_d` of the nodes.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- Full-domain Lagrange interpolant of an arbitrary word on an injective RS
domain. -/
noncomputable def wordInterpolant (dom : Fin n ↪ F) (u : Fin n → F) : F[X] :=
  Lagrange.interpolate Finset.univ (fun i => dom i) u

omit [Fintype F] [DecidableEq F] [NeZero n] in
@[simp]
theorem wordInterpolant_eval (dom : Fin n ↪ F) (u : Fin n → F) (i : Fin n) :
    (wordInterpolant dom u).eval (dom i) = u i := by
  exact Lagrange.eval_interpolate_at_node u dom.injective.injOn (Finset.mem_univ i)

/-- **The master modular reduction**: the residual of any polynomial-valued
column is the `X^k`-coefficient of its remainder mod the node polynomial, times
the residual of the `k`-th power column (no injectivity needed). -/
theorem residual_eq_remainder_coeff (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    (t : Fin (k + 1) → Fin n) (Q : F[X]) :
    residual dom k t (fun i => Q.eval (dom i))
      = (Q %ₘ ∏ a, (X - C (dom (t a)))).coeff k
          * residual dom k t (fun i => (dom i) ^ k) := by
  set P : F[X] := ∏ a : Fin (k + 1), (X - C (dom (t a))) with hP
  have hPmonic : P.Monic :=
    monic_prod_of_monic _ _ fun a _ => monic_X_sub_C _
  have hPdeg : P.natDegree = k + 1 := by
    rw [hP, natDegree_prod_of_monic _ _ fun a _ => monic_X_sub_C _]
    simp
  set rem : F[X] := Q %ₘ P with hrem
  have hremdeg : rem.natDegree ≤ k := by
    by_cases h0 : rem = 0
    · simp [h0]
    · have hd := degree_modByMonic_lt Q hPmonic
      rw [degree_eq_natDegree hPmonic.ne_zero, hPdeg] at hd
      have := (Polynomial.natDegree_lt_iff_degree_lt h0).mpr
        (by exact_mod_cast hd)
      omega
  set R' : F[X] := rem - C (rem.coeff k) * X ^ k with hR'
  have hR'coeff : ∀ m : ℕ, k ≤ m → R'.coeff m = 0 := by
    intro m hm
    rw [hR']
    simp only [coeff_sub, coeff_C_mul, coeff_X_pow]
    rcases eq_or_lt_of_le hm with rfl | h
    · rw [if_pos rfl]
      ring
    · rw [if_neg (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]
      ring
  have hR'deg : R'.natDegree < k := by
    by_cases hR0 : R' = 0
    · rw [hR0, natDegree_zero]
      omega
    · rw [Polynomial.natDegree_lt_iff_degree_lt hR0,
        Polynomial.degree_lt_iff_coeff_zero]
      intro m hm
      exact hR'coeff m (by exact_mod_cast hm)
  have hpoint : ∀ a : Fin (k + 1),
      Q.eval (dom (t a)) = R'.eval (dom (t a))
        + rem.coeff k * (dom (t a)) ^ k := by
    intro a
    have hPz : P.eval (dom (t a)) = 0 := by
      rw [hP, eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp)
    have hQ : Q.eval (dom (t a)) = rem.eval (dom (t a)) := by
      conv_lhs => rw [← modByMonic_add_div Q P]
      simp [eval_add, eval_mul, hPz, hrem]
    rw [hQ, hR']
    simp only [eval_sub, eval_mul, eval_pow, eval_C, eval_X]
    ring
  calc residual dom k t (fun i => Q.eval (dom i))
      = residual dom k t
          (fun i => R'.eval (dom i) + rem.coeff k * (dom i) ^ k) :=
        residual_congr dom k t fun a => hpoint a
    _ = residual dom k t (fun i => R'.eval (dom i))
          + rem.coeff k * residual dom k t (fun i => (dom i) ^ k) :=
        residual_line dom k t _ _ _
    _ = rem.coeff k * residual dom k t (fun i => (dom i) ^ k) := by
        rw [residual_eq_zero_of_extends dom k t (P := R') hR'deg fun a => rfl,
          zero_add]

omit [Field F] [Fintype F] [NeZero n] in
open Classical in
/-- The injective-tuple image of any SET function of the tuple's image is the
`(k+1)`-subset image. -/
theorem injTuple_image_setFn_eq (φ : Finset (Fin n) → F) (k : ℕ) :
    (Finset.univ.filter
        (fun t : Fin (k + 1) → Fin n => Function.Injective t)).image
      (fun t => φ (Finset.univ.image t))
    = (Finset.univ.powersetCard (k + 1)).image φ := by
  ext x
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_powersetCard]
  constructor
  · rintro ⟨t, htinj, rfl⟩
    exact ⟨Finset.univ.image t, ⟨Finset.subset_univ _, by
      rw [Finset.card_image_of_injective _ htinj, Finset.card_univ,
        Fintype.card_fin]⟩, rfl⟩
  · rintro ⟨S, ⟨-, hcard⟩, rfl⟩
    set t : Fin (k + 1) → Fin n :=
      fun a => (S.equivFin.symm (Fin.cast hcard.symm a) : Fin n) with ht
    have htinj : Function.Injective t := by
      intro a b hab
      have h1 : (S.equivFin.symm (Fin.cast hcard.symm a))
          = S.equivFin.symm (Fin.cast hcard.symm b) := Subtype.ext hab
      exact Fin.cast_injective _ (S.equivFin.symm.injective h1)
    have himg : Finset.univ.image t = S := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
        exact (S.equivFin.symm (Fin.cast hcard.symm a)).2
      · rw [Finset.card_image_of_injective _ htinj, Finset.card_univ,
          Fintype.card_fin, hcard]
    exact ⟨t, htinj, by rw [himg]⟩

open Classical in
/-- **THE MODULAR CENSUS**: at the boundary radius, for any polynomial stack
`(Q₀, Q₁)` whose direction column is strongly far, the bad-scalar set is exactly
the set of modular Wronskian ratios over `(k+1)`-subsets:

  `badSet = { −(Q₀ %ₘ P_S).coeff k / (Q₁ %ₘ P_S).coeff k : |S| = k+1 }`,

`P_S = ∏_{i∈S} (X − xᵢ)`.  The exact threshold count for EVERY far stack is a
remainder-coefficient census in `F[X]/P`. -/
theorem boundary_slice_badSet_modular (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (k + 1 : ℕ))
    (Q₀ Q₁ : F[X])
    (hμ : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c (fun i => Q₁.eval (dom i))).card ≤ k) :
    Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
        (fun i => Q₀.eval (dom i)) (fun i => Q₁.eval (dom i)) γ)
      = (Finset.univ.powersetCard (k + 1)).image
          (fun S : Finset (Fin n) =>
            -((Q₀ %ₘ ∏ i ∈ S, (X - C (dom i))).coeff k)
              / (Q₁ %ₘ ∏ i ∈ S, (X - C (dom i))).coeff k) := by
  have hallres : ∀ t : Fin (k + 1) → Fin n, Function.Injective t →
      residual dom k t (fun i => Q₁.eval (dom i)) ≠ 0 := by
    intro t htinj hres
    obtain ⟨c, hcC, hcag⟩ := extension_of_residual_eq_zero dom t htinj hres
    have hsub : Finset.univ.image t
        ⊆ agreeSet c (fun i => Q₁.eval (dom i)) := by
      intro x hx
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
      rw [agreeSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hcag a⟩
    have hcard : k + 1 ≤ (agreeSet c (fun i => Q₁.eval (dom i))).card := by
      calc k + 1 = (Finset.univ.image t).card := by
            rw [Finset.card_image_of_injective _ htinj, Finset.card_univ,
              Fintype.card_fin]
        _ ≤ _ := Finset.card_le_card hsub
    have := hμ c hcC
    omega
  have hPmatch : ∀ t : Fin (k + 1) → Fin n, Function.Injective t →
      (∏ a, (X - C (dom (t a))) : F[X])
        = ∏ i ∈ Finset.univ.image t, (X - C (dom i)) := by
    intro t htinj
    rw [Finset.prod_image fun a _ b _ h => htinj h]
  refine (boundary_slice_badSet_eq dom hk hlo hhi
    (u₀ := fun i => Q₀.eval (dom i)) hμ).trans ?_
  set φ : Finset (Fin n) → F := fun S =>
    -((Q₀ %ₘ ∏ i ∈ S, (X - C (dom i))).coeff k)
      / (Q₁ %ₘ ∏ i ∈ S, (X - C (dom i))).coeff k with hφ
  have h1 : (Finset.univ.filter
        (fun t : Fin (k + 1) → Fin n => Function.Injective t)).image
      (fun t => -(residual dom k t (fun i => Q₀.eval (dom i)))
        / residual dom k t (fun i => Q₁.eval (dom i)))
      = (Finset.univ.filter
        (fun t : Fin (k + 1) → Fin n => Function.Injective t)).image
      (fun t => φ (Finset.univ.image t)) := by
    refine Finset.image_congr fun t ht => ?_
    have htinj : Function.Injective t := by
      have := Finset.mem_coe.mp ht
      exact (Finset.mem_filter.mp this).2
    have hres1 := hallres t htinj
    have hm0 := residual_eq_remainder_coeff dom hk t Q₀
    have hm1 := residual_eq_remainder_coeff dom hk t Q₁
    have hr : residual dom k t (fun i => (dom i) ^ k) ≠ 0 := by
      intro h
      rw [hm1, h, mul_zero] at hres1
      exact hres1 rfl
    rw [hm0, hm1, hφ]
    change _ = -((Q₀ %ₘ ∏ i ∈ Finset.univ.image t, (X - C (dom i))).coeff k)
      / (Q₁ %ₘ ∏ i ∈ Finset.univ.image t, (X - C (dom i))).coeff k
    rw [← hPmatch t htinj, neg_div, neg_div, mul_div_mul_right _ _ hr]
  rw [h1, injTuple_image_setFn_eq φ k]

open Classical in
/-- Cardinality form of `boundary_slice_badSet_modular`: the boundary-slice
bad-scalar count is exactly the number of distinct modular Wronskian ratios over
`(k+1)`-subsets. -/
theorem boundary_slice_badSet_modular_card_eq (dom : Fin n ↪ F) {k : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (k + 1 : ℕ))
    (Q₀ Q₁ : F[X])
    (hμ : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c (fun i => Q₁.eval (dom i))).card ≤ k) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
        (fun i => Q₀.eval (dom i)) (fun i => Q₁.eval (dom i)) γ)).card
      = ((Finset.univ.powersetCard (k + 1)).image
          (fun S : Finset (Fin n) =>
            -((Q₀ %ₘ ∏ i ∈ S, (X - C (dom i))).coeff k)
              / (Q₁ %ₘ ∏ i ∈ S, (X - C (dom i))).coeff k)).card := by
  rw [boundary_slice_badSet_modular dom hk hlo hhi Q₀ Q₁ hμ]

open Classical in
/-- Coarse counting form of the modular census: every strongly-far polynomial
stack at the boundary slice has at most one bad scalar per `(k+1)`-subset of the
domain, before quotienting by modular-ratio collisions. -/
theorem boundary_slice_badSet_modular_card_le_choose (dom : Fin n ↪ F) {k : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (k + 1 : ℕ))
    (Q₀ Q₁ : F[X])
    (hμ : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c (fun i => Q₁.eval (dom i))).card ≤ k) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
        (fun i => Q₀.eval (dom i)) (fun i => Q₁.eval (dom i)) γ)).card
      ≤ n.choose (k + 1) := by
  rw [boundary_slice_badSet_modular_card_eq dom hk hlo hhi Q₀ Q₁ hμ]
  calc
    ((Finset.univ.powersetCard (k + 1)).image
        (fun S : Finset (Fin n) =>
          -((Q₀ %ₘ ∏ i ∈ S, (X - C (dom i))).coeff k)
            / (Q₁ %ₘ ∏ i ∈ S, (X - C (dom i))).coeff k)).card
        ≤ (Finset.univ.powersetCard (k + 1) : Finset (Finset (Fin n))).card :=
          Finset.card_image_le
    _ = n.choose (k + 1) := by
          rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

open Classical in
/-- Word-level form of `boundary_slice_badSet_modular`.  Full-domain Lagrange
interpolation transports the polynomial modular census to arbitrary rows on the
domain, under the same strong-farness hypothesis for the direction row. -/
theorem boundary_slice_badSet_modular_words (dom : Fin n ↪ F) {k : ℕ}
    (hk : 1 ≤ k) {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (k + 1 : ℕ))
    (u₀ u₁ : Fin n → F)
    (hμ : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c u₁).card ≤ k) :
    Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
        u₀ u₁ γ)
      = (Finset.univ.powersetCard (k + 1)).image
          (fun S : Finset (Fin n) =>
            -(((wordInterpolant dom u₀) %ₘ ∏ i ∈ S, (X - C (dom i))).coeff k)
              / ((wordInterpolant dom u₁) %ₘ ∏ i ∈ S, (X - C (dom i))).coeff k) := by
  let Q₀ : F[X] := wordInterpolant dom u₀
  let Q₁ : F[X] := wordInterpolant dom u₁
  have hμQ : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c (fun i => Q₁.eval (dom i))).card ≤ k := by
    intro c hc
    simpa [Q₁] using hμ c hc
  have h := boundary_slice_badSet_modular dom hk hlo hhi Q₀ Q₁ hμQ
  simpa [Q₀, Q₁] using h

open Classical in
/-- Cardinality form for arbitrary rows: at the boundary slice, every strongly-far
direction word has bad-scalar count equal to the modular-ratio image size of the
full-domain interpolants. -/
theorem boundary_slice_badSet_modular_words_card_eq (dom : Fin n ↪ F)
    {k : ℕ} (hk : 1 ≤ k) {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (k + 1 : ℕ))
    (u₀ u₁ : Fin n → F)
    (hμ : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c u₁).card ≤ k) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
        u₀ u₁ γ)).card
      = ((Finset.univ.powersetCard (k + 1)).image
          (fun S : Finset (Fin n) =>
            -(((wordInterpolant dom u₀) %ₘ ∏ i ∈ S, (X - C (dom i))).coeff k)
              / ((wordInterpolant dom u₁) %ₘ ∏ i ∈ S, (X - C (dom i))).coeff k)).card := by
  let Q₀ : F[X] := wordInterpolant dom u₀
  let Q₁ : F[X] := wordInterpolant dom u₁
  have hμQ : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c (fun i => Q₁.eval (dom i))).card ≤ k := by
    intro c hc
    simpa [Q₁] using hμ c hc
  have h := boundary_slice_badSet_modular_card_eq dom hk hlo hhi Q₀ Q₁ hμQ
  simpa [Q₀, Q₁] using h

open Classical in
/-- Coarse counting form for arbitrary rows: at the boundary slice, every
strongly-far direction word has at most one bad scalar per `(k+1)`-subset before
modular-ratio collisions of the interpolants. -/
theorem boundary_slice_badSet_modular_words_card_le_choose (dom : Fin n ↪ F)
    {k : ℕ} (hk : 1 ≤ k) {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (k + 1 : ℕ))
    (u₀ u₁ : Fin n → F)
    (hμ : ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c u₁).card ≤ k) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
        u₀ u₁ γ)).card
      ≤ n.choose (k + 1) := by
  rw [boundary_slice_badSet_modular_words_card_eq dom hk hlo hhi u₀ u₁ hμ]
  calc
    ((Finset.univ.powersetCard (k + 1)).image
        (fun S : Finset (Fin n) =>
          -(((wordInterpolant dom u₀) %ₘ ∏ i ∈ S, (X - C (dom i))).coeff k)
            / ((wordInterpolant dom u₁) %ₘ ∏ i ∈ S, (X - C (dom i))).coeff k)).card
        ≤ (Finset.univ.powersetCard (k + 1) : Finset (Finset (Fin n))).card :=
          Finset.card_image_le
    _ = n.choose (k + 1) := by
          rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.residual_eq_remainder_coeff
#print axioms ProximityGap.Ownership.boundary_slice_badSet_modular
#print axioms ProximityGap.Ownership.boundary_slice_badSet_modular_card_eq
#print axioms ProximityGap.Ownership.boundary_slice_badSet_modular_card_le_choose
#print axioms ProximityGap.Ownership.wordInterpolant_eval
#print axioms ProximityGap.Ownership.boundary_slice_badSet_modular_words
#print axioms ProximityGap.Ownership.boundary_slice_badSet_modular_words_card_eq
#print axioms ProximityGap.Ownership.boundary_slice_badSet_modular_words_card_le_choose
