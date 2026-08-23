/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ThreePrimeRatClassification

/-!
# Issue #232 — the ℤ-refinement: Rédei–de Bruijn–Schoenberg at three primes (O108)

O107 classified vanishing ℚ-weighted sums at squarefree `pqr`; O105 refuted the
ℕ-component form.  This file pins the exact boundary: for INTEGER (hence ℕ-)
weights the three fiber components can always be chosen INTEGER-valued —

    `∑ W_{ijk}·ξ^i·η^j·θ^k = 0  ⟺  ∃ A B C : ℕ → ℕ → ℤ,
        W ijk = A j k + B i k + C i j`

— the ℤ-span theorem for vanishing sums of roots of unity (Rédei 1954;
de Bruijn 1953; Schoenberg 1964: the lattice of vanishing sums is spanned over ℤ
by the prime packets) at three-prime moduli, in grid form.  Combined with O105:
the components exist over ℤ and provably NOT over ℕ — the positivity defect of
the three-prime theory is exactly the gap Lam–Leung's span induction measures.

Mechanism: the O107 ℚ-split admits an explicit GAUGE NORMALIZATION with manifestly
integral formulas —

    `C' i j = W i j 0`,  `B' i k = W i 0 k − W i 0 0`,
    `A' j k = W 0 j k − W 0 j 0 − W 0 0 k + W 0 0 0`

— whose correctness is a linear identity in eight instances of the ℚ-split
(`linarith`), transported to ℤ by cast injectivity.  No new analytic content.
-/

namespace ThreePrimeIntClassification

open Finset

variable {L : Type*} [Field L] [CharZero L]

/-- **The ℤ-classification at squarefree `pqr`** (Rédei–de Bruijn–Schoenberg,
three-prime grid form): an integer-weighted sum over the `p × q × r`
root-of-unity grid vanishes iff the weight cube splits into three INTEGER fiber
functions — with explicit gauge-normalized formulas. -/
theorem three_prime_int_classification {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {ξ η θ : L} (hξ : IsPrimitiveRoot ξ p) (hη : IsPrimitiveRoot η q)
    (hθ : IsPrimitiveRoot θ r) (W : ℕ → ℕ → ℕ → ℤ) :
    (∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, ∑ k ∈ Finset.range r,
        (W i j k : L) * ξ ^ i * η ^ j * θ ^ k = 0) ↔
      ∃ A B C : ℕ → ℕ → ℤ, ∀ i < p, ∀ j < q, ∀ k < r,
        W i j k = A j k + B i k + C i j := by
  constructor
  · intro hsum
    -- transport to the ℚ-classification
    have hsumQ : ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
        ∑ k ∈ Finset.range r,
          (((W i j k : ℚ)) : L) * ξ ^ i * η ^ j * θ ^ k = 0 := by
      have hterm : ∀ i ∈ Finset.range p, ∀ j ∈ Finset.range q,
          ∀ k ∈ Finset.range r,
          (((W i j k : ℚ)) : L) * ξ ^ i * η ^ j * θ ^ k
            = (W i j k : L) * ξ ^ i * η ^ j * θ ^ k := by
        intro i _ j _ k _
        push_cast
        ring
      calc ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, ∑ k ∈ Finset.range r,
            (((W i j k : ℚ)) : L) * ξ ^ i * η ^ j * θ ^ k
          = ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, ∑ k ∈ Finset.range r,
              (W i j k : L) * ξ ^ i * η ^ j * θ ^ k := by
            refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl
              fun j hj => Finset.sum_congr rfl fun k hk => hterm i hi j hj k hk
        _ = 0 := hsum
    obtain ⟨A, B, C, hABC⟩ :=
      (ThreePrimeRatClassification.three_prime_rat_classification
        hp hq hr hpq hpr hqr hξ hη hθ (fun i j k => (W i j k : ℚ))).mp hsumQ
    -- the gauge-normalized integral components
    refine ⟨fun j k => W 0 j k - W 0 j 0 - W 0 0 k + W 0 0 0,
      fun i k => W i 0 k - W i 0 0, fun i j => W i j 0,
      fun i hi j hj k hk => ?_⟩
    -- verify over ℚ via eight instances of the split, then cast back
    have h000 := hABC 0 hp.pos 0 hq.pos 0 hr.pos
    have h00k := hABC 0 hp.pos 0 hq.pos k hk
    have h0j0 := hABC 0 hp.pos j hj 0 hr.pos
    have h0jk := hABC 0 hp.pos j hj k hk
    have hi00 := hABC i hi 0 hq.pos 0 hr.pos
    have hi0k := hABC i hi 0 hq.pos k hk
    have hij0 := hABC i hi j hj 0 hr.pos
    have hijk := hABC i hi j hj k hk
    have hQ : (W i j k : ℚ)
        = ((W 0 j k : ℚ) - W 0 j 0 - W 0 0 k + W 0 0 0)
          + ((W i 0 k : ℚ) - W i 0 0) + (W i j 0 : ℚ) := by
      linarith
    exact_mod_cast hQ
  · rintro ⟨A, B, C, hABC⟩
    have hQ : ∀ i < p, ∀ j < q, ∀ k < r,
        ((W i j k : ℚ)) = ((A j k : ℚ)) + ((B i k : ℚ)) + ((C i j : ℚ)) := by
      intro i hi j hj k hk
      exact_mod_cast hABC i hi j hj k hk
    have hvanQ :=
      (ThreePrimeRatClassification.three_prime_rat_classification
        hp hq hr hpq hpr hqr hξ hη hθ (fun i j k => (W i j k : ℚ))).mpr
        ⟨fun j k => (A j k : ℚ), fun i k => (B i k : ℚ),
          fun i j => (C i j : ℚ), hQ⟩
    have hterm : ∀ i ∈ Finset.range p, ∀ j ∈ Finset.range q,
        ∀ k ∈ Finset.range r,
        (W i j k : L) * ξ ^ i * η ^ j * θ ^ k
          = (((W i j k : ℚ)) : L) * ξ ^ i * η ^ j * θ ^ k := by
      intro i _ j _ k _
      push_cast
      ring
    calc ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, ∑ k ∈ Finset.range r,
          (W i j k : L) * ξ ^ i * η ^ j * θ ^ k
        = ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, ∑ k ∈ Finset.range r,
            (((W i j k : ℚ)) : L) * ξ ^ i * η ^ j * θ ^ k := by
          refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl
            fun j hj => Finset.sum_congr rfl fun k hk => hterm i hi j hj k hk
      _ = 0 := hvanQ

/-- **The sharp boundary at three primes** (ℤ yes, ℕ no): every vanishing
ℕ-multiplicity sum at squarefree `pqr` has INTEGER fiber components (this
theorem), while ℕ-valued components are impossible in general
(`ThreePrimePacketRefutation`, O105) — the positivity defect is exactly what
Lam–Leung's span induction measures. -/
theorem nat_weights_int_components {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    {ξ η θ : L} (hξ : IsPrimitiveRoot ξ p) (hη : IsPrimitiveRoot η q)
    (hθ : IsPrimitiveRoot θ r) (w : ℕ → ℕ → ℕ → ℕ)
    (hvan : ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, ∑ k ∈ Finset.range r,
        (w i j k : L) * ξ ^ i * η ^ j * θ ^ k = 0) :
    ∃ A B C : ℕ → ℕ → ℤ, ∀ i < p, ∀ j < q, ∀ k < r,
      (w i j k : ℤ) = A j k + B i k + C i j := by
  have hvanZ : ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q,
      ∑ k ∈ Finset.range r,
        (((w i j k : ℤ)) : L) * ξ ^ i * η ^ j * θ ^ k = 0 := by
    have hterm : ∀ i ∈ Finset.range p, ∀ j ∈ Finset.range q,
        ∀ k ∈ Finset.range r,
        (((w i j k : ℤ)) : L) * ξ ^ i * η ^ j * θ ^ k
          = (w i j k : L) * ξ ^ i * η ^ j * θ ^ k := by
      intro i _ j _ k _
      push_cast
      ring
    calc ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, ∑ k ∈ Finset.range r,
          (((w i j k : ℤ)) : L) * ξ ^ i * η ^ j * θ ^ k
        = ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, ∑ k ∈ Finset.range r,
            (w i j k : L) * ξ ^ i * η ^ j * θ ^ k := by
          refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl
            fun j hj => Finset.sum_congr rfl fun k hk => hterm i hi j hj k hk
      _ = 0 := hvan
  exact (three_prime_int_classification hp hq hr hpq hpr hqr hξ hη hθ
    (fun i j k => (w i j k : ℤ))).mp hvanZ

end ThreePrimeIntClassification

#print axioms ThreePrimeIntClassification.three_prime_int_classification
#print axioms ThreePrimeIntClassification.nat_weights_int_components
