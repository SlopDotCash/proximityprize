/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedWalkBound
import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# The pairing census: `#{perfect matchings of Fin (2r)} = (2r−1)!!` — closing the K1 counting core (#389)

`NegationClosedWalkBound.zeroSumCount_le_pairings` bounds the zero-sum `2r`-tuple count of `G` by
`(#pairings)·n^r` under the antipodal-pairing residual, where a **pairing** is a fixed-point-free
involution `σ : Perm (Fin (2r))` (`IsPairing`). The remaining unproven step it flagged was the exact
census of pairings. This file proves it:

> `pairings_card_eq_doubleFactorial` :  `#{σ : Perm (Fin (2r)) | IsPairing σ} = (2r−1)!!`,

via the cycle-type conjugacy-class count: a fixed-point-free involution is exactly a permutation with
`cycleType = replicate r 2`, and `Equiv.Perm.card_of_cycleType` evaluates that class to
`(2r)! / (2^r · r!) = (2r−1)!!`. Composing gives the **literal K1 negation-closed walk bound**

> `zeroSumCount_le_doubleFactorial` :  `zeroSumCount G (2r) ≤ (2r−1)!!·n^r`  (under the residual `H`).

This upgrades the K1 counting core from `(#pairings)·n^r` to the closed `(2r−1)!!·n^r`. It is the
combinatorial (counting) half of the energy bound `E_r(μ_n) ≤ (2r−1)!!·n^r`; it is NOT a δ\* / W4
advance (the avg→max gap remains the wall), but it is a genuine, novel, axiom-clean closure of a
named in-tree residual. Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option linter.style.longLine false


open Finset Nat

namespace ArkLib.ProximityGap.NegationClosedWalk

/-- A function is involutive iff its square is the identity permutation. -/
theorem involutive_iff_sq {r : ℕ} (σ : Equiv.Perm (Fin (2 * r))) :
    Function.Involutive σ ↔ σ ^ 2 = 1 := by
  rw [pow_two]
  constructor
  · intro h
    apply Equiv.Perm.ext
    intro x
    rw [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    exact h x
  · intro h x
    have := Equiv.Perm.ext_iff.mp h x
    rwa [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at this

/-- Fixed-point-freeness is full support. -/
theorem fpf_iff_support_univ {r : ℕ} (σ : Equiv.Perm (Fin (2 * r))) :
    (∀ i, σ i ≠ i) ↔ σ.support = Finset.univ := by
  rw [Finset.eq_univ_iff_forall]
  simp only [Equiv.Perm.mem_support]

/-- **A pairing is exactly a permutation with cycle type `replicate r 2`** (all 2-cycles). -/
theorem isPairing_iff_cycleType {r : ℕ} (σ : Equiv.Perm (Fin (2 * r))) :
    IsPairing σ ↔ σ.cycleType = Multiset.replicate r 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · rintro ⟨hinv, hfpf⟩
    have hsq : σ ^ 2 = 1 := (involutive_iff_sq σ).mp hinv
    have hct := Equiv.Perm.cycleType_of_pow_prime_eq_one (p := 2) hsq
    have hsupp : σ.support = Finset.univ := (fpf_iff_support_univ σ).mp hfpf
    have hsum : σ.cycleType.sum = 2 * r := by
      rw [Equiv.Perm.sum_cycleType, hsupp, Finset.card_univ, Fintype.card_fin]
    rw [hct] at hsum ⊢
    have hsum2 : (Multiset.replicate σ.cycleType.card 2).sum = 2 * σ.cycleType.card := by
      rw [Multiset.sum_replicate, smul_eq_mul, Nat.mul_comm]
    rw [hsum2] at hsum
    have hcr : σ.cycleType.card = r := by omega
    rw [hcr]
  · intro hct
    refine ⟨?_, ?_⟩
    · rw [involutive_iff_sq]
      rw [Equiv.Perm.pow_prime_eq_one_iff (p := 2)]
      intro c hc
      rw [hct] at hc
      exact Multiset.eq_of_mem_replicate hc
    · rw [fpf_iff_support_univ]
      have hsum : σ.cycleType.sum = 2 * r := by
        rw [hct, Multiset.sum_replicate, smul_eq_mul, Nat.mul_comm]
      rw [Equiv.Perm.sum_cycleType] at hsum
      have hcard : σ.support.card = Fintype.card (Fin (2 * r)) := by
        rw [hsum, Fintype.card_fin]
      exact (Finset.card_eq_iff_eq_univ _).mp hcard

/-- The pairing-filter equals the cycle-type-`replicate r 2` filter. -/
theorem pairings_eq_cycleType_filter {r : ℕ} :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin (2 * r)) => IsPairing σ))
      = Finset.univ.filter (fun σ : Equiv.Perm (Fin (2 * r)) =>
          σ.cycleType = Multiset.replicate r 2) := by
  ext σ
  simp only [mem_filter, mem_univ, true_and, isPairing_iff_cycleType]

/-- `(2s)! = (2s−1)!! · (2^s · s!)`. -/
theorem two_mul_factorial_eq (s : ℕ) :
    (2 * s)! = (2 * s - 1)‼ * (2 ^ s * s !) := by
  cases s with
  | zero => simp
  | succ k =>
    have e1 : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
    have e2 : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    rw [e2, show (2 * (k + 1))! = ((2 * k + 1) + 1)! by rw [e1],
        Nat.factorial_eq_mul_doubleFactorial (2 * k + 1),
        show ((2 * k + 1) + 1)‼ = (2 * (k + 1))‼ by rw [e1],
        Nat.doubleFactorial_two_mul (k + 1)]
    ring

/-- `(2s)! / (2^s · s!) = (2s−1)!!`. -/
theorem factorial_div_eq_doubleFactorial (s : ℕ) :
    (2 * s)! / (2 ^ s * s !) = (2 * s - 1)‼ := by
  rw [two_mul_factorial_eq s, Nat.mul_div_cancel]
  positivity

/-- **The pairing census.** The number of fixed-point-free involutions (perfect matchings) of
`Fin (2r)` is the double factorial `(2r−1)!!`. Proven via the cycle-type conjugacy class: a pairing
is exactly a permutation with `cycleType = replicate r 2`, counted by `Equiv.Perm.card_of_cycleType`
as `(2r)!/(2^r·r!) = (2r−1)!!`. -/
theorem pairings_card_eq_doubleFactorial (s : ℕ) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin (2 * s)) => IsPairing σ)).card
      = (2 * s - 1)‼ := by
  rw [pairings_eq_cycleType_filter]
  have hset : (Finset.univ.filter (fun σ : Equiv.Perm (Fin (2 * s)) =>
        σ.cycleType = Multiset.replicate s 2))
      = ({g | g.cycleType = Multiset.replicate s 2} : Finset (Equiv.Perm (Fin (2 * s)))) := by
    ext σ; simp [Finset.mem_filter]
  rw [hset]
  have hcard := Equiv.Perm.card_of_cycleType (α := Fin (2 * s)) (Multiset.replicate s 2)
  have hsum : (Multiset.replicate s 2).sum = 2 * s := by
    rw [Multiset.sum_replicate, smul_eq_mul, Nat.mul_comm]
  have hcardα : Fintype.card (Fin (2 * s)) = 2 * s := Fintype.card_fin _
  have hcond : (Multiset.replicate s 2).sum ≤ Fintype.card (Fin (2 * s))
      ∧ ∀ a ∈ Multiset.replicate s 2, 2 ≤ a := by
    refine ⟨by rw [hsum, hcardα], ?_⟩
    intro a ha
    rw [Multiset.eq_of_mem_replicate ha]
  rw [if_pos hcond] at hcard
  have hprod : (Multiset.replicate s 2).prod = 2 ^ s := by
    rw [Multiset.prod_replicate]
  have hcountprod : (∏ n ∈ (Multiset.replicate s 2).toFinset, ((Multiset.replicate s 2).count n)!)
      = s ! := by
    cases s with
    | zero => simp
    | succ k =>
      have htf : (Multiset.replicate (k + 1) 2).toFinset = {2} := by
        rw [Multiset.toFinset_replicate]
        simp
      rw [htf]
      simp only [Finset.prod_singleton]
      rw [Multiset.count_replicate]
      simp
  rw [hcardα, hsum, hprod, hcountprod] at hcard
  rw [hcard]
  simp only [Nat.sub_self, Nat.factorial_zero, one_mul]
  exact factorial_div_eq_doubleFactorial s

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The literal K1 negation-closed walk bound.** Composing the pairing census with
`zeroSumCount_le_pairings`: under the antipodal-pairing residual `H`, the zero-sum `2r`-tuple count
of `G` is at most `(2r−1)!!·n^r`. This is the closed form of the `r`-fold additive-energy bound
`E_r(G) ≤ (2r−1)!!·n^r` (the combinatorial half; the avg→max gap remains the open W4 wall). -/
theorem zeroSumCount_le_doubleFactorial {r : ℕ} (G : Finset F)
    (H : ∀ c ∈ Fintype.piFinset (fun _ : Fin (2 * r) => G), (∑ i, c i = 0) →
        ∃ σ : Equiv.Perm (Fin (2 * r)), IsPairing σ ∧ ∀ i, c (σ i) = - c i) :
    zeroSumCount G (2 * r) ≤ (2 * r - 1)‼ * G.card ^ r := by
  have h := zeroSumCount_le_pairings G H
  rwa [pairings_card_eq_doubleFactorial r] at h

end ArkLib.ProximityGap.NegationClosedWalk

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.NegationClosedWalk.pairings_card_eq_doubleFactorial
#print axioms ArkLib.ProximityGap.NegationClosedWalk.zeroSumCount_le_doubleFactorial
