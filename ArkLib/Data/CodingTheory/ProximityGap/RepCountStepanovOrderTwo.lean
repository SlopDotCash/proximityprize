/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RepCountFrobeniusBound
import ArkLib.Data.CodingTheory.ProximityGap.StepanovContradictionEngine

/-!
# AN EXPLICIT ORDER-2 STEPANOV AUXILIARY FOR THE GV OBJECT — `r(c) ≤ (n+1)/2` (#389)

The split deployed-prize regime `n ∣ p−1` (`μ_n ⊂ F_p`, Frobenius trivial) has no
conjugation/Frobenius shortcut, so the `r(c) ≤ 2` bound is unavailable there.  This file gives
the **first rigorous sub-trivial bound for the split case** (indeed for *every* regime, over an
arbitrary field) via an explicit, non-circular Stepanov auxiliary polynomial.

> **`repCount_two_mul_le_of_pow_ne_one`** — for `G = μ_n`, `c ≠ 0` with `c^n ≠ 1` (the
> off-diagonal cosets), `2·r(c) ≤ n+1`, i.e. `r(c) ≤ (n+1)/2`.

**The auxiliary.** `Q(X) = (c − X)^{n+1} + X^{n+1} − c`.  On a rep point `y` (`y^n = 1` and
`(c−y)^n = 1`):

* `Q(y) = (c−y)^n(c−y) + y^n·y − c = (c−y) + y − c = 0`;
* `Q'(y) = −(n+1)(c−y)^n + (n+1)y^n = −(n+1) + (n+1) = 0`.

So `Q` vanishes to order ≥ 2 at every rep point (a double root: `(X−y)² ∣ Q`).  `Q` is nonzero
because `Q(0) = c^{n+1} − c = c(c^n − 1) ≠ 0`, and `deg Q ≤ n+1`.  Feeding `Q`, `M = 2`, and the
rep set to the proven counting engine `stepanov_card_mul_M_le_natDegree` gives
`r(c)·2 ≤ deg Q ≤ n+1`.

This is the genuine Stepanov method — an *explicit* low-degree auxiliary with *proven*
high-order vanishing derived from the subgroup relations (NOT the circular "assume a vanisher
exists" form).  It is the order-2 base case; the sharp Heath-Brown–Konyagin `O(n^{2/3})` bound
requires pushing the vanishing order to `~n^{1/3}` while holding the degree at `~n`, which is the
remaining open construction.  Issue #389.
-/

open Finset Polynomial

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

variable {F : Type*} [Field F] [DecidableEq F]

/-- **THE EXPLICIT ORDER-2 STEPANOV BOUND.**  For `μ_n` over any field, every off-diagonal
coset (`c ≠ 0`, `c^n ≠ 1`) has `2·r(c) ≤ n+1`. -/
theorem repCount_two_mul_le_of_pow_ne_one {G : Finset F} {n : ℕ} (hn : 1 ≤ n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) {c : F} (hc0 : c ≠ 0) (hcn : c ^ n ≠ 1) :
    repCount G c * 2 ≤ n + 1 := by
  classical
  -- The explicit auxiliary `Q = (c − X)^{n+1} + X^{n+1} − c`.
  set Q : F[X] := (C c - X) ^ (n + 1) + X ^ (n + 1) - C c with hQ
  -- `Q ≠ 0`, since `Q(0) = c^{n+1} − c = c(c^n − 1) ≠ 0`.
  have hQ0 : Q ≠ 0 := by
    intro h
    have hev0 : Q.eval 0 = 0 := by rw [h, eval_zero]
    rw [hQ] at hev0
    simp only [eval_sub, eval_add, eval_pow, eval_C, eval_X, sub_zero,
      zero_pow (by omega : n + 1 ≠ 0), add_zero] at hev0
    -- hev0 : c ^ (n+1) - c = 0
    rw [pow_succ] at hev0
    have : c * (c ^ n - 1) = 0 := by linear_combination hev0
    rcases mul_eq_zero.mp this with h1 | h2
    · exact hc0 h1
    · exact hcn (by linear_combination h2)
  -- `deg Q ≤ n + 1`.
  have hdeg : Q.natDegree ≤ n + 1 := by
    rw [hQ]; compute_degree!
  -- Each off-diagonal rep point is a double root of `Q`.
  have hmult : ∀ y ∈ G.filter (fun y => c - y ∈ G), 2 ≤ rootMultiplicity y Q := by
    intro y hy
    rw [Finset.mem_filter] at hy
    obtain ⟨hyG, hcyG⟩ := hy
    have hyn : y ^ n = 1 := (hGmem y).mp hyG
    have hcyn : (c - y) ^ n = 1 := (hGmem (c - y)).mp hcyG
    -- `Q(y) = 0`.
    have hev : Q.eval y = 0 := by
      rw [hQ]
      simp only [eval_sub, eval_add, eval_pow, eval_C, eval_X]
      rw [pow_succ (c - y) n, pow_succ y n, hcyn, hyn]
      ring
    -- `Q'(y) = 0`.
    have hd : Q.derivative.eval y = 0 := by
      rw [hQ]
      simp only [derivative_sub, derivative_add, derivative_pow, derivative_C, derivative_X,
        derivative_one, Nat.add_sub_cancel, mul_one, sub_zero, zero_sub, mul_neg,
        eval_add, eval_sub, eval_neg, eval_mul, eval_pow, eval_C, eval_X, eval_natCast]
      rw [hcyn, hyn]
      ring
    -- A common root of `Q` and `Q'` is a double root: `(X − C y)² ∣ Q`.
    have hr1 : (X - C y) ∣ Q := dvd_iff_isRoot.mpr hev
    obtain ⟨g, hg⟩ := hr1
    have hgy : g.eval y = 0 := by
      have hQd : Q.derivative = g + (X - C y) * g.derivative := by
        rw [hg, derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul]
      rw [hQd] at hd
      simpa [sub_self] using hd
    obtain ⟨g2, hg2⟩ := dvd_iff_isRoot.mpr hgy
    have hdvd : (X - C y) ^ 2 ∣ Q := ⟨g2, by rw [hg, hg2]; ring⟩
    exact (le_rootMultiplicity_iff hQ0).mpr hdvd
  -- Counting: `r(c)·2 ≤ deg Q ≤ n+1`.
  calc repCount G c * 2
      = (G.filter (fun y => c - y ∈ G)).card * 2 := rfl
    _ ≤ Q.natDegree :=
        StepanovContradictionEngine.stepanov_card_mul_M_le_natDegree Q hQ0 _ 2 hmult
    _ ≤ n + 1 := hdeg

/-- The same bound stated as `r(c) ≤ (n+1)/2`. -/
theorem repCount_le_succ_div_two_of_pow_ne_one {G : Finset F} {n : ℕ} (hn : 1 ≤ n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) {c : F} (hc0 : c ≠ 0) (hcn : c ^ n ≠ 1) :
    repCount G c ≤ (n + 1) / 2 := by
  have h := repCount_two_mul_le_of_pow_ne_one hn hGmem hc0 hcn
  omega

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.repCount_two_mul_le_of_pow_ne_one
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.repCount_le_succ_div_two_of_pow_ne_one
