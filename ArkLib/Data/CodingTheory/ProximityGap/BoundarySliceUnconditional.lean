/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ResidualModularReduction

/-!
# The unconditional boundary-slice census (#371): strong farness discharged

The strong-farness hypothesis of the boundary-slice exact laws is a THEOREM for
direction columns of degree exactly `k`: a degree-`k` polynomial minus a
degree-`< k` codeword polynomial is a nonzero polynomial of degree ≤ `k`, hence
has at most `k` roots on the embedded domain
(`agreeSet_card_le_of_natDegree_eq`).  Consequently:

* `boundary_slice_ladder_badSet_eq_unconditional` — the ladder-stack law
  `badSet(x^{k+1}, x^k) = −{(k+1)-fold subset sums of the domain}` holds at the
  boundary radius with NO farness hypothesis: only the radius window
  `k < (1−δ)n ≤ k+1`.

* `boundary_slice_badSet_modular_of_natDegree` — the modular Wronskian census
  `badSet(Q₀, Q₁) = {−(Q₀ %ₘ P_S).coeff k / (Q₁ %ₘ P_S).coeff k}` holds for
  every stack whose direction polynomial has degree exactly `k`.

The exact bad-set formulas above Johnson are now hypothesis-free on the farness
side for the canonical stack classes; what remains open is only the *count* of
distinct values (the collision census), not the *description* of the set.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.Ownership

open ProximityGap.SpikeFloor ProximityGap

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **The farness discharge**: a column of degree exactly `k` is automatically
strongly far from the degree-`< k` code — every codeword agrees with it on at
most `k` points. -/
theorem agreeSet_card_le_of_natDegree_eq (dom : Fin n ↪ F) {k : ℕ}
    (hk : 1 ≤ k) {Q : F[X]} (hdeg : Q.natDegree = k) :
    ∀ c ∈ (rsCode dom k : Submodule F (Fin n → F)),
      (agreeSet c (fun i => Q.eval (dom i))).card ≤ k := by
  rintro c ⟨P, hPdeg, rfl⟩
  have hD0 : Q - P ≠ 0 := by
    intro h
    have hQP : Q = P := sub_eq_zero.mp h
    rw [hQP] at hdeg
    have hP0 : P ≠ 0 := by
      intro h0
      rw [h0, natDegree_zero] at hdeg
      omega
    have := (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hPdeg
    omega
  have hPk : P.natDegree ≤ k := by
    by_cases hP0 : P = 0
    · simp [hP0]
    · exact le_of_lt ((Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hPdeg)
  have hDdeg : (Q - P).natDegree ≤ k :=
    le_trans (natDegree_sub_le Q P) (max_le (le_of_eq hdeg) hPk)
  -- the agreement set injects into the roots of Q − P
  have hsub : (agreeSet (fun i => P.eval (dom i))
        (fun i => Q.eval (dom i))).card
      ≤ (Q - P).roots.toFinset.card := by
    refine Finset.card_le_card_of_injOn (fun i => dom i) ?_ ?_
    · intro i hi
      have hi' : i ∈ agreeSet (fun i => P.eval (dom i))
          (fun i => Q.eval (dom i)) := Finset.mem_coe.mp hi
      rw [agreeSet, Finset.mem_filter] at hi'
      rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots hD0]
      change (Q - P).eval (dom i) = 0
      rw [eval_sub, sub_eq_zero]
      exact hi'.2.symm
    · exact fun i _ j _ h => dom.injective h
  calc (agreeSet (fun i => P.eval (dom i)) (fun i => Q.eval (dom i))).card
      ≤ (Q - P).roots.toFinset.card := hsub
    _ ≤ Multiset.card (Q - P).roots := Multiset.toFinset_card_le _
    _ ≤ (Q - P).natDegree := Polynomial.card_roots' _
    _ ≤ k := hDdeg

open Classical in
/-- **THE UNCONDITIONAL LADDER CENSUS**: at the boundary radius, with NO farness
hypothesis, the bad-scalar set of the ladder stack `(x^{k+1}, x^k)` is exactly
the negated `(k+1)`-fold subset-sum set of the domain. -/
theorem boundary_slice_ladder_badSet_eq_unconditional (dom : Fin n ↪ F)
    {k : ℕ} (hk : 1 ≤ k) {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (k + 1 : ℕ)) :
    Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
        (fun i => (dom i) ^ (k + 1)) (fun i => (dom i) ^ k) γ)
      = (Finset.univ.powersetCard (k + 1)).image
          (fun S : Finset (Fin n) => -∑ i ∈ S, dom i) := by
  refine boundary_slice_ladder_badSet_eq dom hk hlo hhi ?_
  have h := agreeSet_card_le_of_natDegree_eq dom hk
    (Q := X ^ k) (natDegree_X_pow k)
  simpa using h

open Classical in
/-- Cardinality form of `boundary_slice_ladder_badSet_eq_unconditional`: the
ladder-stack bad-scalar count needs no separate farness hypothesis when the
direction is `X^k`. -/
theorem boundary_slice_ladder_badSet_card_eq_unconditional (dom : Fin n ↪ F)
    {k : ℕ} (hk : 1 ≤ k) {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (k + 1 : ℕ)) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
        (fun i => (dom i) ^ (k + 1)) (fun i => (dom i) ^ k) γ)).card
      = ((Finset.univ.powersetCard (k + 1)).image
          (fun S : Finset (Fin n) => ∑ i ∈ S, dom i)).card := by
  refine boundary_slice_ladder_badSet_card_eq dom hk hlo hhi ?_
  have h := agreeSet_card_le_of_natDegree_eq dom hk
    (Q := X ^ k) (natDegree_X_pow k)
  simpa using h

open Classical in
/-- **THE UNCONDITIONAL MODULAR CENSUS**: at the boundary radius, for every
polynomial stack whose direction has degree exactly `k`, the bad-scalar set is
exactly the modular Wronskian ratio set over `(k+1)`-subsets. -/
theorem boundary_slice_badSet_modular_of_natDegree (dom : Fin n ↪ F)
    {k : ℕ} (hk : 1 ≤ k) {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (k + 1 : ℕ))
    (Q₀ Q₁ : F[X]) (hdeg : Q₁.natDegree = k) :
    Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
        (fun i => Q₀.eval (dom i)) (fun i => Q₁.eval (dom i)) γ)
      = (Finset.univ.powersetCard (k + 1)).image
          (fun S : Finset (Fin n) =>
            -((Q₀ %ₘ ∏ i ∈ S, (X - C (dom i))).coeff k)
              / (Q₁ %ₘ ∏ i ∈ S, (X - C (dom i))).coeff k) :=
  boundary_slice_badSet_modular dom hk hlo hhi Q₀ Q₁
    (agreeSet_card_le_of_natDegree_eq dom hk hdeg)

open Classical in
/-- Cardinality form of `boundary_slice_badSet_modular_of_natDegree`: for a
degree-exact direction polynomial, the bad-scalar count is exactly the modular
ratio image size. -/
theorem boundary_slice_badSet_modular_card_eq_of_natDegree (dom : Fin n ↪ F)
    {k : ℕ} (hk : 1 ≤ k) {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (k + 1 : ℕ))
    (Q₀ Q₁ : F[X]) (hdeg : Q₁.natDegree = k) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
        (fun i => Q₀.eval (dom i)) (fun i => Q₁.eval (dom i)) γ)).card
      = ((Finset.univ.powersetCard (k + 1)).image
          (fun S : Finset (Fin n) =>
            -((Q₀ %ₘ ∏ i ∈ S, (X - C (dom i))).coeff k)
              / (Q₁ %ₘ ∏ i ∈ S, (X - C (dom i))).coeff k)).card :=
  boundary_slice_badSet_modular_card_eq dom hk hlo hhi Q₀ Q₁
    (agreeSet_card_le_of_natDegree_eq dom hk hdeg)

omit [DecidableEq F] in
open Classical in
/-- Coarse counting form of `boundary_slice_badSet_modular_of_natDegree`: a
degree-exact direction polynomial has at most one boundary-slice bad scalar per
`(k+1)`-subset before modular-ratio collisions. -/
theorem boundary_slice_badSet_modular_card_le_choose_of_natDegree (dom : Fin n ↪ F)
    {k : ℕ} (hk : 1 ≤ k) {δ : ℝ≥0}
    (hlo : (k : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (hhi : (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) ≤ (k + 1 : ℕ))
    (Q₀ Q₁ : F[X]) (hdeg : Q₁.natDegree = k) :
    (Finset.univ.filter (fun γ : F => mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
        (fun i => Q₀.eval (dom i)) (fun i => Q₁.eval (dom i)) γ)).card
      ≤ n.choose (k + 1) :=
  boundary_slice_badSet_modular_card_le_choose dom hk hlo hhi Q₀ Q₁
    (agreeSet_card_le_of_natDegree_eq dom hk hdeg)

end ProximityGap.Ownership

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Ownership.agreeSet_card_le_of_natDegree_eq
#print axioms ProximityGap.Ownership.boundary_slice_ladder_badSet_eq_unconditional
#print axioms ProximityGap.Ownership.boundary_slice_ladder_badSet_card_eq_unconditional
#print axioms ProximityGap.Ownership.boundary_slice_badSet_modular_of_natDegree
#print axioms ProximityGap.Ownership.boundary_slice_badSet_modular_card_eq_of_natDegree
#print axioms ProximityGap.Ownership.boundary_slice_badSet_modular_card_le_choose_of_natDegree
