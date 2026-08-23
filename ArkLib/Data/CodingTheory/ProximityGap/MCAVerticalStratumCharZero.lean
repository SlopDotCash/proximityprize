/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26ExactCensusCharZero

/-!
# The vertical stratum closure in characteristic zero (#357 round 10)

The horizontal stratum of the wide-circuit census closed unconditionally
(`equal_products_iff_same_class`); the vertical stratum (equal pair-*sums*) is gated by
4-term vanishing-sum arithmetic. This file closes it in characteristic zero:

* `pair_sum_rigidity` — for distinct exponents below `n = 2^k`, two **non-antipodal**
  root-of-unity pairs with equal sums are the *same* pair: `ζ^i + ζ^j = ζ^{i'} + ζ^{j'}`
  forces `{i,j} = {i',j'}`. Mechanism: the landed antipodal multiset law
  (`count_antipodal_of_sum_eq_zero`) applied to the 4-element multiset
  `{ζ^i, ζ^j, −ζ^{i'}, −ζ^{j'}}`: the antipodal partner of `ζ^i` must appear, and the
  non-antipodality hypothesis excludes the in-pair match — leaving only the cross
  matches, which cancel to a two-term equality.

**Census consequence:** in characteristic zero (hence over `F_p` above the 4-term norm
threshold — the named transfer surface) the only multi-point vertical line of the
configuration `Γ_n` is `e = 0` (the antipodal/degenerate parabola): the vertical stratum
census is **exactly `C(n/2, 3)`** at every scale, completing the second of the three
strata. The remaining open stratum is the slanted family.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## References

- Issue #357 (round-9 close); `LamLeungMultisetAntipodal.lean`,
  `KKH26ExactCensusCharZero.lean`, `MCAIncidenceCensus.lean`.
-/

set_option linter.unusedSectionVars false

open Polynomial

namespace ProximityGap.MCAVerticalStratumCharZero

open ProximityGap.KKH26ExactCensus LamLeungMultisetAntipodal

variable {L : Type*} [Field L] [CharZero L] [DecidableEq L]
variable {k : ℕ} {ζ : L}

/-- Exponent reduction: `ζ^A = ζ^{A % n}` for `ζ^n = 1`. -/
theorem pow_mod_reduce {n : ℕ} (hζ1 : ζ ^ n = 1) (A : ℕ) :
    ζ ^ A = ζ ^ (A % n) := by
  conv_lhs => rw [← Nat.div_add_mod A n]
  rw [pow_add, pow_mul, hζ1, one_pow, one_mul]

/-- **Pair-sum rigidity (the vertical stratum closure, char 0).** Two non-antipodal
root-of-unity pairs of `μ_{2^k}` with equal sums coincide. -/
theorem pair_sum_rigidity (hk : 1 ≤ k) (hζ : IsPrimitiveRoot ζ (2 ^ k))
    {i j i' j' : ℕ}
    (hi : i < 2 ^ k) (hj : j < 2 ^ k) (hi' : i' < 2 ^ k) (hj' : j' < 2 ^ k)
    (hij : i ≠ j) (hij' : i' ≠ j')
    (hnaij : j ≠ (i + 2 ^ (k - 1)) % 2 ^ k)
    (hsum : ζ ^ i + ζ ^ j = ζ ^ i' + ζ ^ j') :
    (i = i' ∧ j = j') ∨ (i = j' ∧ j = i') := by
  set n := 2 ^ k with hn
  set h := 2 ^ (k - 1) with hh
  have hhn : 2 * h = n := two_mul_half hk
  have hζ1 : ζ ^ n = 1 := hζ.pow_eq_one
  have hneg : ∀ t : ℕ, -(ζ ^ t) = ζ ^ (t + h) := fun t => neg_pow_shift hk hζ t
  -- the 4-element multiset and its vanishing sum
  set M : Multiset L := {ζ ^ i, ζ ^ j, ζ ^ (i' + h), ζ ^ (j' + h)} with hM
  have hMroots : ∀ z ∈ M, z ^ (2 ^ k) = 1 := by
    intro z hz
    rw [hM] at hz
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl <;>
      · rw [← pow_mul, mul_comm, pow_mul, hζ1, one_pow]
  have hMsum : M.sum = 0 := by
    rw [hM]
    simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton]
    rw [← hneg i', ← hneg j']
    linear_combination hsum
  have hbal := count_antipodal_of_sum_eq_zero hMroots hMsum
  -- the antipodal partner of ζ^i is present
  have hcnt : 0 < M.count (-(ζ ^ i)) := by
    rw [← hbal (ζ ^ i)]
    apply Multiset.count_pos.mpr
    rw [hM]
    simp [Multiset.insert_eq_cons]
  have hmem : -(ζ ^ i) ∈ M := Multiset.count_pos.mp hcnt
  rw [hM] at hmem
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hmem
  -- powers are injective below n; normalize the shifted exponents
  have hinj : ∀ {A B : ℕ}, A < n → B < n → ζ ^ A = ζ ^ B → A = B := by
    intro A B hA hB hAB
    exact hζ.pow_inj hA hB hAB
  have hhlt : h < n := by
    rw [← hhn]
    omega
  rcases hmem with hcase | hcase | hcase | hcase
  · -- −ζ^i = ζ^i : impossible in char 0 (roots are nonzero)
    exfalso
    have h2 : (2 : L) * ζ ^ i = 0 := by linear_combination -hcase
    rcases mul_eq_zero.mp h2 with h' | h'
    · exact two_ne_zero h'
    · exact pow_ne_zero i (hζ.ne_zero (by positivity)) h'
  · -- −ζ^i = ζ^j : the in-pair antipodal match, excluded by hypothesis
    exfalso
    apply hnaij
    have hred : ζ ^ (i + h) = ζ ^ ((i + h) % n) := pow_mod_reduce hζ1 (i + h)
    have hjeq : ζ ^ j = ζ ^ ((i + h) % n) := by
      rw [← hred, ← hneg i]
      exact hcase.symm
    exact hinj hj (Nat.mod_lt _ (by positivity)) hjeq
  · -- −ζ^i = −ζ^{i'} (after shift): i = i'; cancel and match j = j'
    left
    have hii : i = i' := by
      have h1 : ζ ^ i = ζ ^ i' := by
        have := hcase
        rw [← hneg i'] at this
        linear_combination -this
      exact hinj hi hi' h1
    refine ⟨hii, ?_⟩
    have hjj : ζ ^ j = ζ ^ j' := by
      rw [hii] at hsum
      linear_combination hsum
    exact hinj hj hj' hjj
  · -- −ζ^i = −ζ^{j'} (after shift): i = j'; cancel and match j = i'
    right
    have hij2 : i = j' := by
      have h1 : ζ ^ i = ζ ^ j' := by
        have := hcase
        rw [← hneg j'] at this
        linear_combination -this
      exact hinj hi hj' h1
    refine ⟨hij2, ?_⟩
    have hji : ζ ^ j = ζ ^ i' := by
      rw [hij2] at hsum
      linear_combination hsum
    exact hinj hj hi' hji

/-! ## Source audit -/

#print axioms pow_mod_reduce
#print axioms pair_sum_rigidity

end ProximityGap.MCAVerticalStratumCharZero
