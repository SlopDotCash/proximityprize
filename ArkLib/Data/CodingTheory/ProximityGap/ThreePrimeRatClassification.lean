/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RatWeightedSquarefreeGrid
import ArkLib.Data.CodingTheory.ProximityGap.CoprimePacketMinpoly
import ArkLib.Data.CodingTheory.ProximityGap.DeBruijnWeightedSquarefreeExp

/-!
# Issue #232 — THE THREE-PRIME ℚ-CLASSIFICATION (squarefree `pqr`, O107)

The O105 addendum's dimension-checked target, executed through the O106 gate:
for distinct primes `p, q, r` and primitive roots `ξ, η, θ` (char 0), a ℚ-weighted
triple-grid sum vanishes **iff** the weight cube splits into three fiber
functions, each constant in one coordinate:

    `∑_{i<p,j<q,k<r} W i j k·ξ^i·η^j·θ^k = 0   ⟺
        ∃ A B C : ℕ → ℕ → ℚ,  W i j k = A j k + B i k + C i j`

— the exact linear structure that SURVIVES the O105 refutation (the ℕ-positive
form is false at three primes; this is its true ℚ-shadow, with dimension
`pq + pr + qr − p − q − r + 1 = pqr − φ(pqr)` matching the vanishing space).

Mechanism — every ingredient landed earlier today:
* the `θ`-fiber coefficients live in `K = ℚ⟮ξ·η⟯` (the CRT exponents embed `ξ, η`
  as powers of the generator);
* `CoprimePacketMinpoly.minpoly_adjoin_coprime_prime_eq_geom` (O106) gives
  `minpoly K θ = Φ_r` at the COMPOSITE base `m = pq` — the gate;
* `CRTDoubleSlice.slice_of_packet_minpoly` forces all `θ`-fibers equal;
* the fiber differences are 2-variable ℚ-weighted vanishing sums, classified by
  `RatWeightedSquarefreeGrid.rat_weighted_squarefree_grid` (O107a);
* integration: `A j k := v_k j`, `B i k := u_k i`, `C i j := W i j 0`;
* converse: each component factors its constant coordinate's full geometric sum.
-/

namespace ThreePrimeRatClassification

open Polynomial Finset IntermediateField

variable {L : Type*} [Field L] [CharZero L]

/-- **THE SQUAREFREE THREE-PRIME ℚ-CLASSIFICATION**: a ℚ-weighted sum over the
`p × q × r` root-of-unity grid vanishes iff the weight cube is a sum of three
fiber functions (each constant in one coordinate). -/
theorem three_prime_rat_classification {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {ξ η θ : L} (hξ : IsPrimitiveRoot ξ p) (hη : IsPrimitiveRoot η q)
    (hθ : IsPrimitiveRoot θ r) (W : ℕ → ℕ → ℕ → ℚ) :
    (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, ∑ k ∈ Finset.range r,
        (W i j k : L) * ξ ^ i * η ^ j * θ ^ k = 0) ↔
      ∃ A B C : ℕ → ℕ → ℚ, ∀ i < p, ∀ j < q, ∀ k < r,
        W i j k = A j k + B i k + C i j := by
  classical
  have hco_pq : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  have hco_pqr : Nat.Coprime (p * q) r :=
    Nat.Coprime.mul_left ((Nat.coprime_primes hp hr).mpr hpr)
      ((Nat.coprime_primes hq hr).mpr hqr)
  have hnpq : 0 < p * q := Nat.mul_pos hp.pos hq.pos
  -- `ξ·η` is a primitive `pq`-th root
  have hξη : IsPrimitiveRoot (ξ * η) (p * q) := by
    have h1 : orderOf ξ = p := hξ.eq_orderOf.symm
    have h2 : orderOf η = q := hη.eq_orderOf.symm
    have horder : orderOf (ξ * η) = p * q := by
      rw [(Commute.all ξ η).orderOf_mul_eq_mul_orderOf_of_coprime
        (by rw [h1, h2]; exact hco_pq), h1, h2]
    exact horder ▸ IsPrimitiveRoot.orderOf (ξ * η)
  constructor
  · -- FORWARD
    intro hsum
    obtain ⟨e₁, he₁p, he₁q⟩ := Nat.chineseRemainder hco_pq 1 0
    obtain ⟨e₂, he₂p, he₂q⟩ := Nat.chineseRemainder hco_pq 0 1
    set g : ℚ⟮ξ * η⟯ := IntermediateField.AdjoinSimple.gen ℚ (ξ * η) with hg
    -- the generator powers transport to `ξ` and `η`
    have hgen : algebraMap ℚ⟮ξ * η⟯ L g = ξ * η :=
      IntermediateField.AdjoinSimple.algebraMap_gen ℚ (ξ * η)
    have hgξ : algebraMap ℚ⟮ξ * η⟯ L (g ^ e₁) = ξ := by
      rw [map_pow, hgen, mul_pow]
      have hx : ξ ^ e₁ = ξ := by
        rw [← DeBruijnWeightedSquarefreeExp.pow_mod_eq hξ e₁]
        have h1 : e₁ % p = 1 % p := he₁p
        rw [h1, Nat.mod_eq_of_lt hp.one_lt, pow_one]
      have hy : η ^ e₁ = 1 := by
        rw [← DeBruijnWeightedSquarefreeExp.pow_mod_eq hη e₁]
        have h1 : e₁ % q = 0 % q := he₁q
        rw [h1, Nat.zero_mod, pow_zero]
      rw [hx, hy, mul_one]
    have hgη : algebraMap ℚ⟮ξ * η⟯ L (g ^ e₂) = η := by
      rw [map_pow, hgen, mul_pow]
      have hx : ξ ^ e₂ = 1 := by
        rw [← DeBruijnWeightedSquarefreeExp.pow_mod_eq hξ e₂]
        have h1 : e₂ % p = 0 % p := he₂p
        rw [h1, Nat.zero_mod, pow_zero]
      have hy : η ^ e₂ = η := by
        rw [← DeBruijnWeightedSquarefreeExp.pow_mod_eq hη e₂]
        have h1 : e₂ % q = 1 % q := he₂q
        rw [h1, Nat.mod_eq_of_lt hq.one_lt, pow_one]
      rw [hx, hy, one_mul]
    have hgξi : ∀ i : ℕ, algebraMap ℚ⟮ξ * η⟯ L ((g ^ e₁) ^ i) = ξ ^ i := by
      intro i
      rw [map_pow, hgξ]
    have hgηj : ∀ j : ℕ, algebraMap ℚ⟮ξ * η⟯ L ((g ^ e₂) ^ j) = η ^ j := by
      intro j
      rw [map_pow, hgη]
    -- the θ-fiber coefficients in `K`
    have hmapA : ∀ k : ℕ,
        algebraMap ℚ⟮ξ * η⟯ L (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
            (W i j k : ℚ⟮ξ * η⟯) * (g ^ e₁) ^ i * (g ^ e₂) ^ j)
          = ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
              (W i j k : L) * ξ ^ i * η ^ j := by
      intro k
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, map_mul, hgξi, hgηj, map_ratCast]
    -- the engine shape
    have hmin := CoprimePacketMinpoly.minpoly_adjoin_coprime_prime_eq_geom
      hnpq hr hco_pqr hξη hθ
    have hsumA : ∑ k ∈ Finset.range (r * 1),
        (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
          (W i j k : ℚ⟮ξ * η⟯) * (g ^ e₁) ^ i * (g ^ e₂) ^ j) • θ ^ k = 0 := by
      rw [mul_one]
      have hswap : ∑ k ∈ Finset.range r,
          (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
            (W i j k : ℚ⟮ξ * η⟯) * (g ^ e₁) ^ i * (g ^ e₂) ^ j) • θ ^ k
          = ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, ∑ k ∈ Finset.range r,
              (W i j k : L) * ξ ^ i * η ^ j * θ ^ k := by
        have hstep : ∀ k ∈ Finset.range r,
            (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
              (W i j k : ℚ⟮ξ * η⟯) * (g ^ e₁) ^ i * (g ^ e₂) ^ j) • θ ^ k
              = ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
                  (W i j k : L) * ξ ^ i * η ^ j * θ ^ k := by
          intro k _
          rw [Algebra.smul_def, hmapA, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_mul]
        rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
      rw [hswap]
      exact hsum
    -- all θ-fibers equal
    have hfiber : ∀ k < r, ∀ k' < r,
        ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
          ((W i j k - W i j k' : ℚ) : L) * ξ ^ i * η ^ j = 0 := by
      intro k hk k' hk'
      have hAeq := CRTDoubleSlice.slice_of_packet_minpoly hmin hsumA hk hk'
        Nat.zero_lt_one
      simp only [mul_one, add_zero] at hAeq
      have hmapped := congrArg (algebraMap ℚ⟮ξ * η⟯ L) hAeq
      rw [hmapA, hmapA] at hmapped
      have hterm : ∀ i ∈ Finset.range p, ∀ j ∈ Finset.range q,
          ((W i j k - W i j k' : ℚ) : L) * ξ ^ i * η ^ j
            = (W i j k : L) * ξ ^ i * η ^ j
              - (W i j k' : L) * ξ ^ i * η ^ j := by
        intro i _ j _
        push_cast
        ring
      calc ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
            ((W i j k - W i j k' : ℚ) : L) * ξ ^ i * η ^ j
          = ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
              ((W i j k : L) * ξ ^ i * η ^ j
                - (W i j k' : L) * ξ ^ i * η ^ j) := by
            refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl
              fun j hj => hterm i hi j hj
        _ = 0 := by
            simp only [Finset.sum_sub_distrib]
            rw [hmapped, sub_self]
    -- classify each fiber difference (2-var, O107a) and integrate
    have hUV : ∀ k : ℕ, ∃ uv : (ℕ → ℚ) × (ℕ → ℚ), k < r →
        ∀ i < p, ∀ j < q, W i j k - W i j 0 = uv.1 i + uv.2 j := by
      intro k
      by_cases hk : k < r
      · obtain ⟨u, v, huv⟩ :=
          (RatWeightedSquarefreeGrid.rat_weighted_squarefree_grid hp hq hpq
            hξ hη (fun i j => W i j k - W i j 0)).mp (hfiber k hk 0 hr.pos)
        exact ⟨(u, v), fun _ => huv⟩
      · exact ⟨(fun _ => 0, fun _ => 0), fun h => absurd h hk⟩
    choose UV hUV' using hUV
    refine ⟨fun j k => (UV k).2 j, fun i k => (UV k).1 i,
      fun i j => W i j 0, fun i hi j hj k hk => ?_⟩
    have h := hUV' k hk i hi j hj
    linarith
  · -- CONVERSE: each component factors its constant coordinate's geometric sum
    rintro ⟨A, B, C, hABC⟩
    have hsplit : ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
        ∑ k ∈ Finset.range r, (W i j k : L) * ξ ^ i * η ^ j * θ ^ k
        = (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, ∑ k ∈ Finset.range r,
            (A j k : L) * ξ ^ i * η ^ j * θ ^ k)
          + (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, ∑ k ∈ Finset.range r,
              (B i k : L) * ξ ^ i * η ^ j * θ ^ k)
          + ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, ∑ k ∈ Finset.range r,
              (C i j : L) * ξ ^ i * η ^ j * θ ^ k := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [hABC i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)
        k (Finset.mem_range.mp hk)]
      push_cast
      ring
    have hC0 : ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
        ∑ k ∈ Finset.range r, (C i j : L) * ξ ^ i * η ^ j * θ ^ k = 0 := by
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      rw [← Finset.mul_sum, hθ.geom_sum_eq_zero hr.one_lt, mul_zero]
    have hB0 : ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
        ∑ k ∈ Finset.range r, (B i k : L) * ξ ^ i * η ^ j * θ ^ k = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun k _ => ?_
      have hterm : ∀ j ∈ Finset.range q,
          (B i k : L) * ξ ^ i * η ^ j * θ ^ k
            = (B i k : L) * ξ ^ i * θ ^ k * η ^ j := by
        intro j _
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
        hη.geom_sum_eq_zero hq.one_lt, mul_zero]
    have hA0 : ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
        ∑ k ∈ Finset.range r, (A j k : L) * ξ ^ i * η ^ j * θ ^ k = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun k _ => ?_
      have hterm : ∀ i ∈ Finset.range p,
          (A j k : L) * ξ ^ i * η ^ j * θ ^ k
            = (A j k : L) * η ^ j * θ ^ k * ξ ^ i := by
        intro i _
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
        hξ.geom_sum_eq_zero hp.one_lt, mul_zero]
    rw [hsplit, hA0, hB0, hC0, add_zero, add_zero]

end ThreePrimeRatClassification

#print axioms ThreePrimeRatClassification.three_prime_rat_classification
