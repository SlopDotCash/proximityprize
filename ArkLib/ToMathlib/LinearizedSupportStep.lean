/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Frobenius support scaling (inductive engine for q-linearized support)

Over an extension `K` of a finite field `F` with `q = |F|`, the support of `f^q` is the
`q`-scaling of the support of `f`:

* `support_expand_eq` — char-free: `(expand K q f).support = q · (support f)`.
* `support_pow_card` — `(f^q).support = q · (support f)`, via the finite-field freshman's dream
  `f^q = map (iterateFrobenius) (expand q f)` (`map_iterateFrobenius_expand`).

This is the inductive step for the q-linearized support theorem: if `support f ⊆ {q^i}` then
`support (f^q) = q · support f ⊆ {q^{i+1}}`, so the linearized-binomial recursion
`f ↦ f^q - C b · f` preserves support on the `q`-powers (the BKR06 list-size residual).
-/

open Polynomial BigOperators

namespace ArkLib.LinearizedKernel

variable {K : Type*} [Field K]

/-- Support of `expand` scales by `q`: `(expand K q f).support = (· * q) '' support f`. -/
theorem support_expand_eq {q : ℕ} (hq : 0 < q) (f : K[X]) :
    (expand K q f).support = f.support.image (· * q) := by
  classical
  ext m
  simp only [mem_support_iff, Finset.mem_image]
  rw [coeff_expand hq]
  constructor
  · intro hm
    by_cases hdvd : q ∣ m
    · rw [if_pos hdvd] at hm
      exact ⟨m / q, hm, Nat.div_mul_cancel hdvd⟩
    · rw [if_neg hdvd] at hm; exact absurd rfl hm
  · rintro ⟨k, hk, rfl⟩
    rw [if_pos (dvd_mul_left q k), Nat.mul_div_cancel _ hq]
    exact hk

variable {F : Type*} [Field F] [Fintype F] [Algebra F K]

/-- **Frobenius support scaling.** Over an extension `K` of a finite field `F` (`q = |F|`),
`(f^q).support = q · support f`.  Uses `f^q = map (iterateFrobenius) (expand q f)` (the
finite-field freshman's dream), that `map` by the injective iterated Frobenius preserves support,
and `support_expand_eq`. -/
theorem support_pow_card (f : K[X]) :
    (f ^ Fintype.card F).support = f.support.image (· * Fintype.card F) := by
  haveI : CharP F (ringChar F) := ringChar.charP F
  obtain ⟨n, hp, hcard⟩ := FiniteField.card F (ringChar F)
  haveI : Fact (ringChar F).Prime := ⟨hp⟩
  haveI : CharP K (ringChar F) :=
    charP_of_injective_algebraMap (algebraMap F K).injective (ringChar F)
  haveI : ExpChar K (ringChar F) := ExpChar.prime hp
  have hpos : 0 < (ringChar F) ^ (n : ℕ) := pow_pos hp.pos _
  rw [hcard, ← map_iterateFrobenius_expand (ringChar F) f (n : ℕ),
    support_map_of_injective _ (iterateFrobenius K (ringChar F) (n : ℕ)).injective,
    support_expand_eq hpos f]

/-- A polynomial over `K` is **q-power-supported** (`q = |F|`) when every exponent in its support
is a power of `q` — the q-linearized-polynomial support condition.  `∑ a_i X^{q^i}`. -/
def IsQPowSupported (f : K[X]) : Prop := ∀ m ∈ f.support, ∃ i : ℕ, m = Fintype.card F ^ i

/-- Base case: `X` is q-power-supported (support `{1} = {q^0}`). -/
theorem isQPowSupported_X : IsQPowSupported (F := F) (X : K[X]) := by
  intro m hm
  rw [mem_support_iff, coeff_X] at hm
  split_ifs at hm with h
  · exact ⟨0, by rw [pow_zero]; omega⟩
  · exact absurd rfl hm

/-- **Linearized recursion preserves q-power support.** If `P` is q-power-supported then so is
`P^q - C b · P` for any `b`: `support(P^q) = q·support P` lands on the next q-power layer
(`support_pow_card`), and `support(C b · P) ⊆ support P`.  This is the inductive step of the
q-linearized-support theorem; with the recursion identity it gives that subspace polynomials are
q-power-supported. -/
theorem isQPowSupported_kernel {P : K[X]} (b : K) (hP : IsQPowSupported (F := F) P) :
    IsQPowSupported (F := F) (P ^ Fintype.card F - C b * P) := by
  intro m hm
  have hm' : (P ^ Fintype.card F).coeff m ≠ 0 ∨ (C b * P).coeff m ≠ 0 := by
    rw [mem_support_iff, coeff_sub] at hm
    by_contra hcon
    push_neg at hcon
    exact hm (by rw [hcon.1, hcon.2, sub_zero])
  rcases hm' with h | h
  · have hmem : m ∈ (P ^ Fintype.card F).support := mem_support_iff.mpr h
    rw [support_pow_card] at hmem
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hmem
    obtain ⟨i, rfl⟩ := hP k hk
    exact ⟨i + 1, (pow_succ _ _).symm⟩
  · refine hP m (mem_support_iff.mpr ?_)
    rw [coeff_C_mul] at h
    exact fun hc => h (by rw [hc, mul_zero])

end ArkLib.LinearizedKernel

-- Axiom audit.
#print axioms ArkLib.LinearizedKernel.support_expand_eq
#print axioms ArkLib.LinearizedKernel.support_pow_card
#print axioms ArkLib.LinearizedKernel.isQPowSupported_X
#print axioms ArkLib.LinearizedKernel.isQPowSupported_kernel
