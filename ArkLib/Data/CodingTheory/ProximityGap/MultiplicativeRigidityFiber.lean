/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Coset rigidity of the power map (Route B: pure fiber counting)

This file formalizes the "Coset Rigidity" lemmas underlying the multiplicative-blowup
argument of the Proximity Gap line of work
(`research/proximity-prize/multiplicative-blowup`, §A).

The core observation is purely group-theoretic: in a finite *cyclic* group `G` of order
`n`, the power map `x ↦ x ^ d` is a group homomorphism (`powMonoidHom d`) whose fibers are
the cosets of its kernel.  Hence every nonempty fiber `{x | x ^ d = c}` has cardinality
equal to that of the kernel, and the kernel — being `{x | x ^ d = 1}` — has cardinality
exactly `Nat.gcd d n`.  Therefore the monomial-agreement set is either empty or has
cardinality exactly `Nat.gcd d n`.

## Route B (fiber counting, no generator)

* `powMonoidHom d : G →* G` is `x ↦ x ^ d` on a commutative group.
* All nonempty fibers of a `MonoidHom` between finite groups are equinumerous
  (`MonoidHom.card_fiber_eq_of_mem_range`).
* The fiber over `1` is the kernel, whose cardinality for a finite cyclic group is
  `Nat.gcd (Nat.card G) d` (`IsCyclic.card_powMonoidHom_ker`).

The only cyclic-specific input is the kernel-cardinality fact; everything else is generic
finite-group fiber counting.

## Main results

* `pow_eq_card_eq_zero_or_gcd` : Lemma 1, the monomial-agreement dichotomy.
* `binomial_agreement_card` : the consumable corollary for `c₁ * x ^ a = c₂ * x ^ b`.
* `binomial_agreement_card_le` : the `≤ a - b` leg of the corollary.
* `binomial_separation` : the rigidity statement in the form the dossier consumes
  (agreement strictly below `k`).

The `d = 0` case is handled honestly: there the agreement set is `univ` (if `c = 1`) or
`∅`, and `Nat.gcd 0 n = n = Fintype.card G`, so the dichotomy statement remains true.

We phrase the corollary over an arbitrary finite cyclic commutative group `G`; the `n`-th
roots of unity `μ_n ⊆ Fˣ` of a field form exactly such a group (a finite subgroup of `Fˣ`
is cyclic), so this is the abstract content of the field-theoretic statement.
-/

open Finset

namespace ProximityGap.MultiplicativeRigidity

open scoped Classical in
/-- **Lemma 1 (monomial agreement / coset rigidity).**

In a finite cyclic commutative group `G` of order `n = Fintype.card G`, for any exponent
`d : ℕ` and target `c : G`, the solution set `{x | x ^ d = c}` is either empty or has
cardinality *exactly* `Nat.gcd d n`.

Proof (Route B): the set is a fiber of `powMonoidHom d`.  Either `c` is not in the range
(empty fiber, card `0`) or it is, in which case the fiber is equinumerous with the fiber
over `1`, i.e. with the kernel `{x | x ^ d = 1}`, whose cardinality is `Nat.gcd d n`. -/
theorem pow_eq_card_eq_zero_or_gcd
    {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] [IsCyclic G] (d : ℕ) (c : G) :
    (Finset.univ.filter fun x : G => x ^ d = c).card = 0 ∨
    (Finset.univ.filter fun x : G => x ^ d = c).card = Nat.gcd d (Fintype.card G) := by
  classical
  by_cases hc : c ∈ Set.range (powMonoidHom d : G →* G)
  · right
    -- `c` is hit, so the fiber over `c` is equinumerous with the fiber over `1` = kernel.
    have h1 : (1 : G) ∈ Set.range (powMonoidHom d : G →* G) := ⟨1, by simp⟩
    have hfib : (Finset.univ.filter fun x : G => (powMonoidHom d : G →* G) x = c).card
        = (Finset.univ.filter fun x : G => (powMonoidHom d : G →* G) x = 1).card :=
      MonoidHom.card_fiber_eq_of_mem_range (powMonoidHom d : G →* G) hc h1
    -- The kernel of `powMonoidHom d` has cardinality `gcd (card G) d` (cyclic-specific input).
    have hker : Nat.card (powMonoidHom d : G →* G).ker = (Nat.card G).gcd d :=
      IsCyclic.card_powMonoidHom_ker G d
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype] at hker
    have e1 : (Finset.univ.filter fun x : G => x ^ d = c)
        = (Finset.univ.filter fun x : G => (powMonoidHom d : G →* G) x = c) := by
      apply Finset.filter_congr; intro x _; simp [powMonoidHom_apply]
    have e2 : (Finset.univ.filter fun x : G => (powMonoidHom d : G →* G) x = 1)
        = (Finset.univ.filter fun x : G => x ∈ (powMonoidHom d : G →* G).ker) := by
      apply Finset.filter_congr; intro x _; simp [MonoidHom.mem_ker]
    rw [e1, hfib, e2, hker, Nat.gcd_comm]
  · left
    -- `c` is not in the range: the solution set is empty.
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro x _ hx
    exact hc ⟨x, by simpa [powMonoidHom_apply] using hx⟩

open scoped Classical in
/-- **Corollary (binomial monomial-agreement bound).**

For a finite cyclic commutative group `G` of order `n`, constants `c₁ c₂ : G` and exponents
`a b : ℕ` with `b < a`, the agreement set `{x | c₁ * x ^ a = c₂ * x ^ b}` is either empty or
has cardinality exactly `Nat.gcd (a - b) n`.

Derived from `pow_eq_card_eq_zero_or_gcd` by dividing by `x ^ b` (`x` is a group element,
hence invertible): the equation is equivalent to `x ^ (a - b) = c₂ * c₁⁻¹`. -/
theorem binomial_agreement_card
    {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] [IsCyclic G]
    (c₁ c₂ : G) (a b : ℕ) (hba : b < a) :
    (Finset.univ.filter fun x : G => c₁ * x ^ a = c₂ * x ^ b).card = 0 ∨
    (Finset.univ.filter fun x : G => c₁ * x ^ a = c₂ * x ^ b).card
      = Nat.gcd (a - b) (Fintype.card G) := by
  classical
  -- `c₁ * x^a = c₂ * x^b  ↔  x^(a-b) = c₂ * c₁⁻¹`, since `x^b` is invertible.
  have key : (Finset.univ.filter fun x : G => c₁ * x ^ a = c₂ * x ^ b)
      = (Finset.univ.filter fun x : G => x ^ (a - b) = c₂ * c₁⁻¹) := by
    apply Finset.filter_congr
    intro x _
    have hab : a = (a - b) + b := (Nat.sub_add_cancel hba.le).symm
    have hsplit : x ^ a = x ^ (a - b) * x ^ b := by rw [← pow_add, ← hab]
    rw [hsplit]
    constructor
    · intro h
      have hx : c₁ * x ^ (a - b) = c₂ := by
        have h' : (c₁ * x ^ (a - b)) * x ^ b = c₂ * x ^ b := by rw [mul_assoc]; exact h
        exact mul_right_cancel h'
      rw [eq_mul_inv_iff_mul_eq, mul_comm, hx]
    · intro h
      have hcoef : c₁ * (c₂ * c₁⁻¹) = c₂ := by
        rw [mul_comm c₂, ← mul_assoc, mul_inv_cancel, one_mul]
      rw [h, ← mul_assoc, hcoef]
  rw [key]
  exact pow_eq_card_eq_zero_or_gcd (a - b) (c₂ * c₁⁻¹)

open scoped Classical in
/-- The `≤ a - b` leg of the binomial corollary: the agreement count is at most `a - b`.

This is immediate from `binomial_agreement_card` since `Nat.gcd (a - b) n ≤ a - b`
whenever `a - b ≠ 0`, which holds because `b < a`. -/
theorem binomial_agreement_card_le
    {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] [IsCyclic G]
    (c₁ c₂ : G) (a b : ℕ) (hba : b < a) :
    (Finset.univ.filter fun x : G => c₁ * x ^ a = c₂ * x ^ b).card ≤ a - b := by
  classical
  rcases binomial_agreement_card c₁ c₂ a b hba with h | h
  · rw [h]; exact Nat.zero_le _
  · rw [h]
    exact Nat.le_of_dvd (Nat.sub_pos_of_lt hba) (Nat.gcd_dvd_left _ _)

open scoped Classical in
/-- **Binomial separation.**

If `0 < b < a ≤ k`, then two distinct monomials `c₁ * X ^ a` and `c₂ * X ^ b` agree on
*strictly fewer* than `k` points of a finite cyclic group `G`.

This is the rigidity statement in the form the multiplicative-blowup dossier consumes: the
agreement count is bounded by `a - b`, and `a - b < k` is pure arithmetic from
`0 < b`, `b < a`, `a ≤ k`.  (The hypothesis `0 < b` is necessary for the *strict* bound:
when `b = 0` one only gets `a - b = a ≤ k`.) -/
theorem binomial_separation
    {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] [IsCyclic G]
    (c₁ c₂ : G) (a b k : ℕ) (hb : 0 < b) (hba : b < a) (hak : a ≤ k) :
    (Finset.univ.filter fun x : G => c₁ * x ^ a = c₂ * x ^ b).card < k := by
  have hcard := binomial_agreement_card_le c₁ c₂ a b hba
  have harith : a - b < k := by omega
  exact lt_of_le_of_lt hcard harith

end ProximityGap.MultiplicativeRigidity
