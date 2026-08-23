/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LamLeungSpanTwoPrime

/-!
# Issue #232 — the weighted-route cardinality law + teeth for the weighted
two-prime de Bruijn theorem

The weighted de Bruijn chain (O96 prime powers → O100/O102 squarefree base →
O101 thread-split engine → O103 `debruijn_weighted_two_prime` → O104
`lam_leung_span_two_prime`) closes here with its exponent-surface consequences
and discriminating witnesses:

* `weighted_total_span_two_prime` — the total-span corollary in `i·p + j·q`
  orientation (thin re-export of O104);
* `debruijn_card_two_prime` — **the Lam–Leung cardinality law at `p^a·q^b`,
  weighted route**: a vanishing power sum over exponents `S ⊆ [0, n)` forces
  `|S| = i·p + j·q`, by instantiating the weighted theorem at the indicator
  weight of `S`.  A packet-counting proof of the same law exists on the field
  surface (`DeBruijnTowerWiring.vanishing_card_two_prime`); this derivation is
  independent of the packet machinery, keeping the weighted chain
  self-contained on the exponent surface.

Teeth (fired at `ℂ`, `n = 12 = 2²·3`, genuine multiplicities):
* the converse manufactures the genuinely weighted vanishing
  `2 + ζ₁₂⁴ + ζ₁₂⁶ + ζ₁₂⁸ = 0` (multiplicity `2` at `e = 0`) from the explicit
  packet functions `A = 𝟙{y = 0}` mod `6 = n/2`, `B = 𝟙{z = 0}` mod `4 = n/3`,
  and the concrete identity is then unfolded term-by-term;
* the forward direction refutes the non-decomposable singleton weight `𝟙{e=0}`:
  its vanishing would force `1 = 2i + 3j`, impossible — so `(1 : ℂ) ≠ 0` falls
  out of the weighted de Bruijn structure alone, and the iff genuinely
  discriminates.

Literature pin: de Bruijn (Indag. Math. 1953 §3); Lam–Leung (J. Algebra 224
(2000)), the cardinality form being Lam–Leung Theorem 1 specialized to two
primes.
-/

namespace DeBruijnWeightedCardTwoPrime

open Finset

/-- **The weighted total-span corollary** (`i·p + j·q` orientation): a vanishing
ℕ-weighted power sum at a primitive `p^a·q^b`-th root of unity has total mass in
`ℕ·p + ℕ·q`. -/
theorem weighted_total_span_two_prime {L : Type*} [Field L] [CharZero L]
    {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (ha : 0 < a) (hb : 0 < b)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ a * q ^ b)) (w : ℕ → ℕ)
    (hvan : ∑ e ∈ Finset.range (p ^ a * q ^ b), (w e : L) * ζ ^ e = 0) :
    ∃ i j : ℕ, ∑ e ∈ Finset.range (p ^ a * q ^ b), w e = i * p + j * q := by
  obtain ⟨cA, cB, h⟩ :=
    LamLeungSpanTwoPrime.lam_leung_span_two_prime hp hq hpq ha hb hζ w hvan
  exact ⟨cA, cB, h.trans (by ring)⟩

/-- **The Lam–Leung cardinality law at `p^a·q^b`, weighted route**: a vanishing
power sum over exponents `S ⊆ [0, n)` at a primitive `n`-th root of unity
(char 0) forces `|S| = i·p + j·q` — instantiate the weighted de Bruijn theorem
at the indicator weight of `S`.  Independent of the packet-counting derivation;
the weighted chain is self-contained. -/
theorem debruijn_card_two_prime {L : Type*} [Field L] [CharZero L]
    {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (ha : 0 < a) (hb : 0 < b)
    {ζ : L} (hζ : IsPrimitiveRoot ζ (p ^ a * q ^ b)) {S : Finset ℕ}
    (hS : ∀ e ∈ S, e < p ^ a * q ^ b) (hsum : ∑ e ∈ S, ζ ^ e = 0) :
    ∃ i j : ℕ, S.card = i * p + j * q := by
  classical
  have hsub : S ⊆ Finset.range (p ^ a * q ^ b) :=
    fun e he => Finset.mem_range.mpr (hS e he)
  -- the indicator weight reproduces the subset sum
  have hw : ∑ e ∈ Finset.range (p ^ a * q ^ b),
      ((if e ∈ S then 1 else 0 : ℕ) : L) * ζ ^ e = 0 := by
    calc ∑ e ∈ Finset.range (p ^ a * q ^ b),
        ((if e ∈ S then 1 else 0 : ℕ) : L) * ζ ^ e
        = ∑ e ∈ Finset.range (p ^ a * q ^ b), (if e ∈ S then ζ ^ e else 0) := by
          refine Finset.sum_congr rfl fun e _ => ?_
          by_cases h : e ∈ S <;> simp [h]
      _ = ∑ e ∈ Finset.range (p ^ a * q ^ b) ∩ S, ζ ^ e :=
          Finset.sum_ite_mem _ _ _
      _ = ∑ e ∈ S, ζ ^ e := by rw [Finset.inter_eq_right.mpr hsub]
      _ = 0 := hsum
  obtain ⟨i, j, hij⟩ := weighted_total_span_two_prime hp hq hpq ha hb hζ
    (fun e => if e ∈ S then 1 else 0) hw
  -- the indicator weight totals to the cardinality
  have hcard : ∑ e ∈ Finset.range (p ^ a * q ^ b), (if e ∈ S then 1 else 0)
      = S.card := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub]
    exact (Finset.card_eq_sum_ones S).symm
  rw [hcard] at hij
  exact ⟨i, j, hij⟩

/-! ## Teeth (fired at `ℂ`, `n = 12 = 2²·3`, genuine multiplicities) -/

private lemma exp_twelfth_primitive :
    IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 12))
      (2 ^ 2 * 3 ^ 1) := by
  have h := Complex.isPrimitiveRoot_exp 12 (by norm_num)
  norm_num at h ⊢
  exact h

/-- The converse FIRED on a genuinely weighted decomposition: the explicit packet
functions `A = 𝟙{y = 0}` on residues mod `6 = n/2` and `B = 𝟙{z = 0}` on residues
mod `4 = n/3` produce the weight `w e = 𝟙{6 ∣ e} + 𝟙{4 ∣ e}` — multiplicity `2`
at `e = 0` — and the headline manufactures its vanishing. -/
private lemma weighted_tooth_vanishing :
    ∑ e ∈ Finset.range (2 ^ 2 * 3 ^ 1),
      (((if e % 6 = 0 then 1 else 0) + (if e % 4 = 0 then 1 else 0) : ℕ) : ℂ)
        * Complex.exp (2 * Real.pi * Complex.I / 12) ^ e = 0 := by
  refine (DeBruijnWeightedTwoPrime.debruijn_weighted_two_prime Nat.prime_two
    Nat.prime_three (by norm_num) (by norm_num) (by norm_num)
    exp_twelfth_primitive _).mpr ?_
  exact ⟨fun y => if y = 0 then 1 else 0, fun z => if z = 0 then 1 else 0,
    fun e _ => by norm_num⟩

/-- The concrete identity unfolded from the weighted tooth:
`2 + ζ₁₂⁴ + ζ₁₂⁶ + ζ₁₂⁸ = 0`. -/
example : (2 : ℂ) + Complex.exp (2 * Real.pi * Complex.I / 12) ^ 4
    + Complex.exp (2 * Real.pi * Complex.I / 12) ^ 6
    + Complex.exp (2 * Real.pi * Complex.I / 12) ^ 8 = 0 := by
  have h := weighted_tooth_vanishing
  rw [show (2 ^ 2 * 3 ^ 1 : ℕ) = 12 from by norm_num] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num at h
  linear_combination h

/-- The forward direction FIRED (with teeth): the singleton weight `𝟙{e = 0}` at
`n = 12` cannot vanish — the weighted total-span corollary would force
`1 = 2i + 3j`, which is impossible.  So `(1 : ℂ) ≠ 0` falls out of the weighted
de Bruijn structure alone: the iff genuinely discriminates. -/
example : ¬ (∑ e ∈ Finset.range (2 ^ 2 * 3 ^ 1),
    ((if e = 0 then 1 else 0 : ℕ) : ℂ)
      * Complex.exp (2 * Real.pi * Complex.I / 12) ^ e = 0) := by
  intro hcon
  obtain ⟨i, j, hij⟩ := weighted_total_span_two_prime Nat.prime_two
    Nat.prime_three (by norm_num) (by norm_num) (by norm_num)
    exp_twelfth_primitive (fun e => if e = 0 then 1 else 0) hcon
  have htot : ∑ e ∈ Finset.range (2 ^ 2 * 3 ^ 1),
      (if e = 0 then 1 else 0 : ℕ) = 1 := by decide
  rw [htot] at hij
  omega

end DeBruijnWeightedCardTwoPrime

#print axioms DeBruijnWeightedCardTwoPrime.weighted_total_span_two_prime
#print axioms DeBruijnWeightedCardTwoPrime.debruijn_card_two_prime
#print axioms DeBruijnWeightedCardTwoPrime.weighted_tooth_vanishing
