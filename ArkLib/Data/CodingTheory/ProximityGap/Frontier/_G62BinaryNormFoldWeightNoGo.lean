/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G61PureDCGateStrictlyStronger

/-!
# G62: binary cyclotomic norm-folding reverses the weighted kernel-depth gain

For a folded relation polynomial

```text
D(X) = A(X²) + X B(X²),
```

vanishing at `ζ`, multiplication by its `ζ ↦ -ζ` conjugate produces the lower-level
relation

```text
N₂(D)(Y) = A(Y)² - Y B(Y)²,
N₂(D)(ζ²) = 0.
```

This is the most direct 2-power-specific recursion available for characteristic-`p`
wraparound relations. It does preserve vanishing, but it is quantitatively hostile to the
factorial/Bessel endpoint weights used by the exact signed-walk histogram:

* the resonant two-term relation `X-a` folds to `a²-X`;
* its primitive depth changes from `(a+1)/2` to `(a²+1)/2`, so there is no uniform linear
  depth bound under one fold;
* for the dominant exact-probe relation `X-3`, the depth tower is
  `2 -> 5 -> 41 -> 3281`. At the prize moment depth `r=110`, only two folds remain inside
  the histogram before the image exits the support, while the subgroup dimension needs
  `log₂ n` folds;
* the coefficient-factorial denominator reverses by `9!/3! = 60480` on the first fold.

Exact probes at thin cells (`n=8,p=41,r=8`; `n=16,p=3281,r=8`; and
`n=32,p=21523361,r=17`) show the same obstruction for the complete relation census: 53%,
59%, and 66% respectively of the tested source mass is sent beyond the same-depth support,
and termwise source mass exceeds same-depth folded-image mass by factors `2.5e5`, `1.9e6`,
and `3.1e10`. Thus binary norm folding is a valid relation producer but not a contracting
weighted recursion. This file records the algebraic and asymptotic obstruction; it does
not bound the prize object.

Issue #466. Axiom-clean.
-/

set_option autoImplicit false

open Polynomial

namespace ArkLib.ProximityGap.Frontier.G62BinaryNormFoldWeightNoGo

/-- The binary relative norm of `A(Y) + X B(Y)` along `X² = Y`. -/
noncomputable def binaryNormFold {R : Type*} [CommRing R] (A B : R[X]) : R[X] :=
  A ^ 2 - X * B ^ 2

/-- Evaluation of the binary fold at the squared point. -/
theorem eval_binaryNormFold {R : Type*} [CommRing R] (A B : R[X]) (ζ : R) :
    (binaryNormFold A B).eval (ζ ^ 2)
      = (A.eval (ζ ^ 2)) ^ 2 - ζ ^ 2 * (B.eval (ζ ^ 2)) ^ 2 := by
  simp [binaryNormFold]

/-- **The 2-power relation recursion.** If the even/odd decomposition vanishes at `ζ`,
its binary norm fold vanishes at `ζ²`. -/
theorem binaryNormFold_vanishes_of_evenOdd_vanishes
    {R : Type*} [CommRing R] (A B : R[X]) (ζ : R)
    (hvanish : A.eval (ζ ^ 2) + ζ * B.eval (ζ ^ 2) = 0) :
    (binaryNormFold A B).eval (ζ ^ 2) = 0 := by
  rw [eval_binaryNormFold]
  have hA : A.eval (ζ ^ 2) = -ζ * B.eval (ζ ^ 2) := by
    linear_combination hvanish
  rw [hA]
  ring

/-- The two-term resonant relation `X-a` folds to `a²-X`. -/
theorem binaryNormFold_resonant {R : Type*} [CommRing R] (a : R) :
    binaryNormFold (C (-a)) 1 = C (a ^ 2) - X := by
  simp [binaryNormFold]

/-- Primitive signed-walk depth of the odd two-term endpoint `(-a,1)`. -/
def twoTermDepth (a : ℕ) : ℕ := (a + 1) / 2

/-- One binary fold has no coefficient-independent linear depth control. The explicit
choice `a=2C+1` sends depth `C+1` to `2C²+2C+1`, strictly beyond `C(C+1)`. -/
theorem no_uniform_linear_depth_control (C : ℕ) :
    ∃ a : ℕ, Odd a ∧ C * twoTermDepth a < twoTermDepth (a ^ 2) := by
  refine ⟨2 * C + 1, ⟨C, by omega⟩, ?_⟩
  have hsrc : twoTermDepth (2 * C + 1) = C + 1 := by
    unfold twoTermDepth
    omega
  have hsq : (2 * C + 1) ^ 2 + 1 = 2 * (2 * C ^ 2 + 2 * C + 1) := by ring
  have htgt : twoTermDepth ((2 * C + 1) ^ 2) = 2 * C ^ 2 + 2 * C + 1 := by
    unfold twoTermDepth
    rw [hsq]
    omega
  rw [hsrc, htgt]
  nlinarith [sq_nonneg C]

/-- Exact depth tower for the dominant `X-3` relation. -/
theorem resonant_three_depth_tower :
    twoTermDepth 3 = 2 ∧ twoTermDepth 9 = 5 ∧
      twoTermDepth 81 = 41 ∧ twoTermDepth 6561 = 3281 := by
  norm_num [twoTermDepth]

/-- At the nominal prize moment depth `r=110`, the first two norm folds of `X-3` remain
visible, while the third already exits the histogram support. -/
theorem resonant_three_only_two_folds_fit_depth_110 :
    twoTermDepth 81 ≤ 110 ∧ 110 < twoTermDepth 6561 := by
  norm_num [twoTermDepth]

/-- The first norm fold reverses the endpoint factorial weight by exactly
`9!/3! = 60480`. -/
theorem resonant_three_factorial_weight_reversal :
    (9 : ℕ).factorial = 60480 * (3 : ℕ).factorial := by
  norm_num [Nat.factorial]

/-- Honest scope marker: this is a norm-fold route no-go, not a prize closure. -/
def isPrizeClosure : Prop := False

theorem not_prizeClosure : ¬ isPrizeClosure := id

#print axioms binaryNormFold_vanishes_of_evenOdd_vanishes
#print axioms binaryNormFold_resonant
#print axioms no_uniform_linear_depth_control
#print axioms resonant_three_depth_tower
#print axioms resonant_three_only_two_folds_fit_depth_110
#print axioms resonant_three_factorial_weight_reversal
#print axioms not_prizeClosure

end ArkLib.ProximityGap.Frontier.G62BinaryNormFoldWeightNoGo
