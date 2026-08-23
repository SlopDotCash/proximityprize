/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RepCountFiber

/-!
# The rep-count fibre as a polynomial root count (#389 / #444)

The three in-tree fibre/shifted-power reformulations of the Garcia-Voloch rep count
(`repCount_eq_fiber_card`, `repCount_eq_curve`, `repCount_eq_shiftedPower`) all read
`r(c) = #{w in mu_n : (1+w)^n = c^n}` and all flag, **in prose only**, the polynomial
reading "the common-root count of `X^n-1` and `(1+X)^n - c^n`, exactly what a resultant /
Stepanov auxiliary acts on". This file makes that bridge a **theorem**: the fibre injects
into the roots of the single shifted-power polynomial `P_c := (X+1)^n - C (c^n)`, so

> **`repCount_le_shiftedPow_roots`** : `r(c) <= (P_c.roots.toFinset).card`,
> **`repCount_le_natDegree`**       : `r(c) <= n` *as a polynomial root count* (not the
>   trivial `|mu_n|` cardinality bound; the bound is now the degree of an explicit
>   polynomial that the Stepanov counting lemma `card_le_natDegree_of_vanishing` consumes).

This is the structurally-missing link the Stepanov framework's honest "open kernel" note
(`StepanovAuxFramework`) calls for: it hands the rep count to the polynomial-root machinery
through an EXPLICIT, structurally-fixed polynomial whose degree is bounded *independently*
of `r(c)`, so the open work is now purely the auxiliary-multiplicity (Wronskian) input on a
fixed polynomial, not a reformulation. No Weil, no Stepanov auxiliary yet; a clean exact
structural injection. Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

The probe `scripts/probes/probe_shifted_gcd.py` confirms the underlying identity
`r(c) = #fibre = deg gcd(X^n-1, (1+X)^n - c^n) = #roots(gcd)` over thin 2-power `mu_n` at
multiple primes `p >> n^3` (n in {8,16,32}); this file proves the upper-bound direction
(which needs no separability) into the explicit shifted-power polynomial.
-/

open Polynomial Finset

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

variable {F : Type*} [Field F] [DecidableEq F]

/-- The shifted-power polynomial `P_c := (X + 1)^n - C (c^n)` whose `mu_n`-roots are exactly
the rep-count fibre. -/
noncomputable def shiftedPowPoly (n : ℕ) (c : F) : F[X] :=
  (X + C 1) ^ n - C (c ^ n)

/-- For `n >= 1`, `shiftedPowPoly n c` has degree exactly `n` (the `(X+1)^n` head term
dominates the constant `C (c^n)`), hence is nonzero. -/
theorem shiftedPowPoly_natDegree {n : ℕ} (hn : 1 ≤ n) (c : F) :
    (shiftedPowPoly n c).natDegree = n := by
  classical
  unfold shiftedPowPoly
  -- (X + C 1) is monic of degree 1, so (X + C 1)^n is monic of degree n
  have hmonic : ((X + C 1 : F[X]) ^ n).Monic := (monic_X_add_C (1 : F)).pow n
  have hdeg_pow : ((X + C 1 : F[X]) ^ n).natDegree = n := by
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_add_C, mul_one]
  -- the subtracted constant has degree 0 < n
  have hdeg_C : (C (c ^ n) : F[X]).natDegree = 0 := Polynomial.natDegree_C _
  have hlt : (C (c ^ n) : F[X]).natDegree < ((X + C 1 : F[X]) ^ n).natDegree := by
    rw [hdeg_C, hdeg_pow]; omega
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, hdeg_pow]

theorem shiftedPowPoly_ne_zero {n : ℕ} (hn : 1 ≤ n) (c : F) :
    shiftedPowPoly n c ≠ 0 := by
  intro h
  have := shiftedPowPoly_natDegree hn c
  rw [h, Polynomial.natDegree_zero] at this
  omega

/-- A fibre element `w` (with `(1 + w)^n = c^n`) is a root of `shiftedPowPoly n c`. -/
theorem isRoot_shiftedPowPoly_of_fiber {n : ℕ} (c w : F) (hw : (1 + w) ^ n = c ^ n) :
    (shiftedPowPoly n c).IsRoot w := by
  unfold shiftedPowPoly
  simp only [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  rw [add_comm w 1, hw, sub_self]

/-- **The rep-count fibre injects into the roots of the explicit shifted-power polynomial.**
`r(c) <= (shiftedPowPoly n c).roots.toFinset.card`. The fibre `{w in mu_n : (1+w)^n = c^n}`
is a subset of the root set of `P_c = (X+1)^n - C(c^n)`. -/
theorem repCount_le_shiftedPow_roots {n : ℕ} (hn : 1 ≤ n) {G : Finset F}
    (hG : ∀ x : F, x ∈ G ↔ x ≠ 0 ∧ x ^ n = 1) {c : F} (hc : c ≠ 0) :
    repCount G c ≤ (shiftedPowPoly n c).roots.toFinset.card := by
  classical
  have hn0 : n ≠ 0 := by omega
  rw [repCount_eq_fiber_card hn0 hG hc]
  -- every fibre element is a root of the (nonzero) shifted-power polynomial
  apply Finset.card_le_card
  intro w hw
  simp only [Finset.mem_filter] at hw
  obtain ⟨_, hwc⟩ := hw
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (shiftedPowPoly_ne_zero hn c)]
  exact isRoot_shiftedPowPoly_of_fiber c w hwc

/-- **The rep count is bounded by the degree of the explicit shifted-power polynomial.**
`r(c) <= n` realized as a *polynomial root count* of `P_c = (X+1)^n - C(c^n)`. This is the
Stepanov-consumable shape: the bound is the natDegree of a structurally fixed polynomial,
the object `card_le_natDegree_of_vanishing` acts on, NOT the trivial `|mu_n|` cardinality
bound. -/
theorem repCount_le_natDegree {n : ℕ} (hn : 1 ≤ n) {G : Finset F}
    (hG : ∀ x : F, x ∈ G ↔ x ≠ 0 ∧ x ^ n = 1) {c : F} (hc : c ≠ 0) :
    repCount G c ≤ (shiftedPowPoly n c).natDegree := by
  classical
  calc repCount G c
      ≤ (shiftedPowPoly n c).roots.toFinset.card :=
        repCount_le_shiftedPow_roots hn hG hc
    _ ≤ Multiset.card (shiftedPowPoly n c).roots :=
        (shiftedPowPoly n c).roots.toFinset_card_le
    _ ≤ (shiftedPowPoly n c).natDegree :=
        Polynomial.card_roots' (shiftedPowPoly n c)

/-- The explicit `n`-form: `r(c) <= n` via the degree-`n` shifted-power polynomial. -/
theorem repCount_le_n {n : ℕ} (hn : 1 ≤ n) {G : Finset F}
    (hG : ∀ x : F, x ∈ G ↔ x ≠ 0 ∧ x ^ n = 1) {c : F} (hc : c ≠ 0) :
    repCount G c ≤ n := by
  have h := repCount_le_natDegree hn hG hc
  rwa [shiftedPowPoly_natDegree hn c] at h

end ArkLib.ProximityGap.AdditiveEnergyRepBound

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.shiftedPowPoly_natDegree
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.isRoot_shiftedPowPoly_of_fiber
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.repCount_le_shiftedPow_roots
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.repCount_le_natDegree
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.repCount_le_n
