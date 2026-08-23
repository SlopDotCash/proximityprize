/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeBruijnWeightedSquarefree

/-!
# Issue #232 — the ℚ-weighted squarefree grid classification (O107a)

The pqr route of the O105 addendum consumes the two-variable classification at
RATIONAL weights (the fiber differences `W_{ijk} − W_{ij0}` are ℚ-valued even for
ℕ-multiplicities, and positivity is exactly what O105 refuted at three primes).
This file lands it — O100 with ℚ-weights, where the integration is a direct
formula (`a_i := W_{i0} − W_{00}`, `b_j := W_{0j}`; no argmin shift):

    `∑_{i<p,j<q} W i j·ξ^i·η^j = 0   ⟺   ∃ a b : ℕ → ℚ, W i j = a i + b j`.

Same engines as O100 (`slice_of_packet_minpoly` at `Φ_q` over `ℚ⟮ξ⟯`,
`vanishing_combination_const`), with `eq_ratCast` in place of `map_natCast` on
the transport.
-/

namespace RatWeightedSquarefreeGrid

open Polynomial Finset IntermediateField

variable {L : Type*} [Field L] [CharZero L]

/-- Equal `ℚ(ξ)`-valued column sums for ℚ-weights (the O100 step at ℚ). -/
lemma rat_column_sums_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {ξ η : L} (hξ : IsPrimitiveRoot ξ p) (hη : IsPrimitiveRoot η q)
    (W : ℕ → ℕ → ℚ)
    (hsum : ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
      (W i j : L) * ξ ^ i * η ^ j = 0)
    {j j' : ℕ} (hj : j < q) (hj' : j' < q) :
    ∑ i ∈ Finset.range p, (W i j : L) * ξ ^ i
      = ∑ i ∈ Finset.range p, (W i j' : L) * ξ ^ i := by
  classical
  have hξ1 : IsPrimitiveRoot ξ (p ^ 1) := by rwa [pow_one]
  have hη1 : IsPrimitiveRoot η (q ^ 1) := by rwa [pow_one]
  have hmin : minpoly ℚ⟮ξ⟯ η
      = ∑ t ∈ Finset.range q, (X : Polynomial ℚ⟮ξ⟯) ^ (t * 1) := by
    have h := CRTPacketMinpoly.minpoly_adjoin_primitiveRoot_eq_packet
      hp hq hpq one_pos hξ1 hη1
    simpa using h
  set g : ℚ⟮ξ⟯ := IntermediateField.AdjoinSimple.gen ℚ ξ with hg
  have hmapA : ∀ c : ℕ,
      algebraMap ℚ⟮ξ⟯ L (∑ i ∈ Finset.range p, (W i c : ℚ⟮ξ⟯) * g ^ i)
        = ∑ i ∈ Finset.range p, (W i c : L) * ξ ^ i := by
    intro c
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, hg, IntermediateField.AdjoinSimple.algebraMap_gen,
      map_ratCast]
  have hsumA : ∑ c ∈ Finset.range (q * 1),
      (∑ i ∈ Finset.range p, (W i c : ℚ⟮ξ⟯) * g ^ i) • η ^ c = 0 := by
    rw [mul_one]
    have hswap : ∑ c ∈ Finset.range q,
        (∑ i ∈ Finset.range p, (W i c : ℚ⟮ξ⟯) * g ^ i) • η ^ c
        = ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
            (W i j : L) * ξ ^ i * η ^ j := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Algebra.smul_def, hmapA, Finset.sum_mul]
    rw [hswap]
    exact hsum
  have hAeq := CRTDoubleSlice.slice_of_packet_minpoly hmin hsumA hj hj'
    Nat.zero_lt_one
  simp only [mul_one, add_zero] at hAeq
  have hmapped := congrArg (algebraMap ℚ⟮ξ⟯ L) hAeq
  rwa [hmapA, hmapA] at hmapped

/-- The ℚ-weighted modular equation (subtraction is free over ℚ). -/
lemma rat_modular_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {ξ η : L} (hξ : IsPrimitiveRoot ξ p) (hη : IsPrimitiveRoot η q)
    (W : ℕ → ℕ → ℚ)
    (hsum : ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
      (W i j : L) * ξ ^ i * η ^ j = 0) :
    ∀ i < p, ∀ j < q, W i j + W 0 0 = W i 0 + W 0 j := by
  intro i hi j hj
  have hcol := rat_column_sums_eq hp hq hpq hξ hη W hsum hj hq.pos
  have hdiff : ∑ i' ∈ Finset.range p,
      algebraMap ℚ L (W i' j - W i' 0) * ξ ^ i' = 0 := by
    have hterm : ∀ i' ∈ Finset.range p,
        algebraMap ℚ L (W i' j - W i' 0) * ξ ^ i'
          = (W i' j : L) * ξ ^ i' - (W i' 0 : L) * ξ ^ i' := by
      intro i' _
      rw [map_sub, sub_mul, eq_ratCast, eq_ratCast]
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, hcol, sub_self]
  obtain ⟨c, hc⟩ := DeBruijnSquarefreePQ.vanishing_combination_const hp hξ
    (fun i' => W i' j - W i' 0) hdiff
  have h1 := hc i hi
  have h2 := hc 0 hp.pos
  have h3 : W i j - W i 0 = W 0 j - W 0 0 := by rw [h1, ← h2]
  linarith

/-- **The ℚ-weighted squarefree grid classification** (O100 at rational weights,
the fiber-difference engine of the pqr route): vanishing iff the weight matrix is
a sum of a row function and a column function — with the DIRECT integration
`a i = W i 0 − W 0 0`, `b j = W 0 j` (no positivity, exactly what survives the
O105 three-prime refutation). -/
theorem rat_weighted_squarefree_grid {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) {ξ η : L} (hξ : IsPrimitiveRoot ξ p) (hη : IsPrimitiveRoot η q)
    (W : ℕ → ℕ → ℚ) :
    (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
        (W i j : L) * ξ ^ i * η ^ j = 0) ↔
      ∃ a b : ℕ → ℚ, ∀ i < p, ∀ j < q, W i j = a i + b j := by
  constructor
  · intro hsum
    have hmod := rat_modular_eq hp hq hpq hξ hη W hsum
    refine ⟨fun i => W i 0 - W 0 0, fun j => W 0 j, fun i hi j hj => ?_⟩
    have h := hmod i hi j hj
    linarith
  · rintro ⟨a, b, hab⟩
    have hsplit : ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
        (W i j : L) * ξ ^ i * η ^ j
        = (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
            (a i : L) * ξ ^ i * η ^ j)
          + ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
              (b j : L) * ξ ^ i * η ^ j := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hab i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)]
      push_cast
      ring
    have hpart1 : ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
        (a i : L) * ξ ^ i * η ^ j = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [← Finset.mul_sum, hη.geom_sum_eq_zero hq.one_lt, mul_zero]
    have hpart2 : ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
        (b j : L) * ξ ^ i * η ^ j = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ => ?_
      have hterm : ∀ i ∈ Finset.range p,
          (b j : L) * ξ ^ i * η ^ j = (b j : L) * η ^ j * ξ ^ i := by
        intro i _
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
        hξ.geom_sum_eq_zero hp.one_lt, mul_zero]
    rw [hsplit, hpart1, hpart2, add_zero]

end RatWeightedSquarefreeGrid

#print axioms RatWeightedSquarefreeGrid.rat_column_sums_eq
#print axioms RatWeightedSquarefreeGrid.rat_modular_eq
#print axioms RatWeightedSquarefreeGrid.rat_weighted_squarefree_grid
