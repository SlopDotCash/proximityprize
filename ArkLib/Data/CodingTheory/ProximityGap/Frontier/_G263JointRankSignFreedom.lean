/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# G263: the joint two-rank centered covariance gate is sign-free

After G252–G262 the single surviving CORE face is the DC-subtracted (centered) row-labelled
covariance gate, required (per G214/G225) to hold **independently at rank five and rank six**:
for a weighted kernel `W` on the cyclic quotient `ZMod m` and rank weight `R_r`,

```text
Cov_r(W) = m * ∑_x W x * R_r x − (∑_x W x)(∑_x R_r x)
         = Re ∑_{χ ≠ 1} Ŵ(χ) · conj(R̂_r(χ)).
```

The open hope after G262 and the Fable referee was that the **joint** constraint — one and the
same `W` must satisfy the gate at both ranks — could restrict the adversary enough to give a
sign/positivity/norm certificate the leverage it provably lacks at a single rank (G205 single-depth
sign no-go; G253/G258 single-rank centering no-go).

**This closes that hope.** The map `W ↦ (Cov_5 W, Cov_6 W)` is `ℤ`-linear in `W`, equal to
`(⟨W, f₅⟩, ⟨W, f₆⟩)` with the **centered per-class functionals**
`f_r x = m * R_r x − ∑_y R_r y`, which satisfy `∑_x f_r x = 0`. When `f₅` and `f₆` are linearly
independent (rank two), the nonnegative-integer kernel cone maps onto all four open sign quadrants.
So the joint gate is exactly as unforced as two independent single-rank gates: **no cross-rank
coupling leverage exists.**

We certify this with an exact minimal cell `m = 5`, integer rank weights
`R₅ = (0,1,0,1,2)`, `R₆ = (1,0,2,0,1)` (their centered functionals are rank-two independent, and
independent of the all-ones principal mode), and four explicit nonnegative-integer weighted kernels
— three of them *single-class indicators* — realizing all four sign pairs `(±,±)`.

This is a route no-go on the joint gate, not a sponsor-prime estimate and not prize closure. A
surviving certificate must still use the exact row-labelled phase placement of the sponsor Jacobi
covariance at *each* rank; combining the two ranks supplies no additional sign-forcing structure.
The mechanism is structural (rank-two independence of the two centered functionals), stable across
the surrogate, not a numerical estimate.
-/

namespace ArkLib.ProximityGap.Frontier.G263JointRankSignFreedom

open Finset

/-- Cyclic length of the minimal certifying cell. -/
def m : ℕ := 5

/-- Rank-five weight profile on `Fin m` (integer surrogate). -/
def R5 : Fin m → ℤ := ![0, 1, 0, 1, 2]

/-- Rank-six weight profile on `Fin m` (a genuinely different integer functional). -/
def R6 : Fin m → ℤ := ![1, 0, 2, 0, 1]

/-- Exact integer centered covariance
`Cov(W,R) = m·∑ W·R − (∑ W)(∑ R)`; this is the DC-subtracted gate: only the
nonprincipal (`χ ≠ 1`) Fourier modes survive, because subtracting `(∑W)(∑R)` removes exactly the
principal-frequency product. -/
def centeredCov (W R : Fin m → ℤ) : ℤ :=
  (m : ℤ) * (∑ x, W x * R x) - (∑ x, W x) * (∑ x, R x)

/-- The centered per-class functional `f_R x = m·R x − ∑ R`. Then `Cov(W,R) = ∑ W x · f_R x`. -/
def centeredFunctional (R : Fin m → ℤ) : Fin m → ℤ :=
  fun x => (m : ℤ) * R x - (∑ y, R y)

/-- The covariance is the pairing of `W` against the centered functional of `R`. -/
theorem centeredCov_eq_dot (W R : Fin m → ℤ) :
    centeredCov W R = ∑ x, W x * centeredFunctional R x := by
  unfold centeredCov centeredFunctional
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  ring

/-- **Centering.** Each centered functional sums to zero — the gate sees no principal mode. -/
theorem sum_centeredFunctional_eq_zero (R : Fin m → ℤ) :
    ∑ x, centeredFunctional R x = 0 := by
  unfold centeredFunctional
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ]
  simp only [Fintype.card_fin]
  change (m : ℤ) * (∑ y, R y) - (m : ℤ) * (∑ y, R y) = 0
  ring

/-- Adding a constant offset `c` to the kernel does not change the centered covariance:
principal-frequency inflation is annihilated by centering (matches the Fable constant-offset
lemma). This is why total-mass/positivity bounds carry zero information to the gate. -/
theorem centeredCov_add_const (W R : Fin m → ℤ) (c : ℤ) :
    centeredCov (fun x => W x + c) R = centeredCov W R := by
  rw [centeredCov_eq_dot, centeredCov_eq_dot]
  have hz := sum_centeredFunctional_eq_zero R
  have : ∑ x, (W x + c) * centeredFunctional R x
       = (∑ x, W x * centeredFunctional R x) + c * ∑ x, centeredFunctional R x := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_); ring
  rw [this, hz, mul_zero, add_zero]

/-- The two centered functionals as explicit integer vectors. -/
theorem centeredFunctional_R5 : centeredFunctional R5 = ![-4, 1, -4, 1, 6] := by
  decide

theorem centeredFunctional_R6 : centeredFunctional R6 = ![1, -4, 6, -4, 1] := by
  decide

/-- **Structural cause: rank-two independence.** No nontrivial rational combination
`a·f₅ + b·f₆` vanishes unless `a = b = 0`; equivalently `f₅, f₆` are `ℤ`-linearly independent.
We certify independence by exhibiting two coordinates whose `2×2` minor is a unit-free nonzero
determinant: coordinates `0,1` give `det [[-4,1],[1,-4]] = 15 ≠ 0`. -/
theorem centeredFunctionals_independent :
    centeredFunctional R5 (0 : Fin 5) * centeredFunctional R6 (1 : Fin 5)
      - centeredFunctional R5 (1 : Fin 5) * centeredFunctional R6 (0 : Fin 5) = 15 := by
  decide

/-- Consequence: if `a • f₅ + b • f₆ = 0` pointwise (over `ℚ` or `ℤ`) then `a = b = 0`.
The `2×2` minor being nonzero forces it. -/
theorem centeredFunctionals_lin_indep (a b : ℤ)
    (h : ∀ x, a * centeredFunctional R5 x + b * centeredFunctional R6 x = 0) :
    a = 0 ∧ b = 0 := by
  have h0 := h (0 : Fin 5)
  have h1 := h (1 : Fin 5)
  rw [centeredFunctional_R5, centeredFunctional_R6] at h0 h1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  -- h0 : a*(-4) + b*1 = 0 ; h1 : a*1 + b*(-4) = 0
  constructor <;> omega

/-! ## The four explicit nonnegative-integer weighted kernels realizing every sign quadrant.

Three are single-class indicators (`e_4, e_3, e_2`); the fourth is a two-class kernel `e_0 + e_3`.
All entries are in `{0,1}` — genuine nonnegative-integer, sparse, prize-thin weighted kernels, not
signed vectors. -/

/-- `W₊₊`: indicator of class `4`. -/
def Wpp : Fin m → ℤ := ![0, 0, 0, 0, 1]
/-- `W₊₋`: indicator of class `3`. -/
def Wpm : Fin m → ℤ := ![0, 0, 0, 1, 0]
/-- `W₋₊`: indicator of class `2`. -/
def Wmp : Fin m → ℤ := ![0, 0, 1, 0, 0]
/-- `W₋₋`: two-class kernel `e₀ + e₃`. -/
def Wmm : Fin m → ℤ := ![1, 0, 0, 1, 0]

/-- `(+,+)`: both rank covariances strictly positive. -/
theorem cov_pp : centeredCov Wpp R5 = 6 ∧ centeredCov Wpp R6 = 1 := by
  decide

/-- `(+,−)`: rank five positive, rank six negative. -/
theorem cov_pm : centeredCov Wpm R5 = 1 ∧ centeredCov Wpm R6 = -4 := by
  decide

/-- `(−,+)`: rank five negative, rank six positive. -/
theorem cov_mp : centeredCov Wmp R5 = -4 ∧ centeredCov Wmp R6 = 6 := by
  decide

/-- `(−,−)`: both rank covariances strictly negative. -/
theorem cov_mm : centeredCov Wmm R5 = -3 ∧ centeredCov Wmm R6 = -3 := by
  decide

/-- Each kernel is genuinely nonnegative and integral (a real weighted-kernel profile). -/
theorem kernels_nonneg :
    (∀ x, 0 ≤ Wpp x) ∧ (∀ x, 0 ≤ Wpm x) ∧ (∀ x, 0 ≤ Wmp x) ∧ (∀ x, 0 ≤ Wmm x) := by
  decide

/-- **G263 packaged joint-gate sign-freedom no-go.** With `m = 5` and the two rank weights, there
exist four nonnegative-integer weighted kernels realizing all four joint sign patterns
`(sign Cov₅, sign Cov₆) ∈ {(+,+),(+,−),(−,+),(−,−)}`, while the two centered functionals are
linearly independent (the structural cause). Hence the joint two-rank centered covariance gate is
sign-free: combining rank five and rank six supplies no cross-rank coupling leverage over the
single-rank gate, and only the exact row-labelled sponsor phase placement can decide either sign. -/
theorem joint_rank_sign_freedom :
    -- structural cause: the two centered functionals are independent
    (centeredFunctional R5 (0 : Fin 5) * centeredFunctional R6 (1 : Fin 5)
      - centeredFunctional R5 (1 : Fin 5) * centeredFunctional R6 (0 : Fin 5) ≠ 0)
    -- every witnessing kernel lives in the nonnegative-integer cone
    ∧ (∀ x, 0 ≤ Wpp x) ∧ (∀ x, 0 ≤ Wpm x) ∧ (∀ x, 0 ≤ Wmp x) ∧ (∀ x, 0 ≤ Wmm x)
    -- all four sign quadrants realized by those nonnegative-integer kernels
    ∧ (centeredCov Wpp R5 > 0 ∧ centeredCov Wpp R6 > 0)
    ∧ (centeredCov Wpm R5 > 0 ∧ centeredCov Wpm R6 < 0)
    ∧ (centeredCov Wmp R5 < 0 ∧ centeredCov Wmp R6 > 0)
    ∧ (centeredCov Wmm R5 < 0 ∧ centeredCov Wmm R6 < 0) := by
  obtain ⟨n1, n2, n3, n4⟩ := kernels_nonneg
  refine ⟨?_, n1, n2, n3, n4, ?_, ?_, ?_, ?_⟩
  · rw [centeredFunctionals_independent]; decide
  · obtain ⟨h1, h2⟩ := cov_pp; rw [h1, h2]; exact ⟨by decide, by decide⟩
  · obtain ⟨h1, h2⟩ := cov_pm; rw [h1, h2]; exact ⟨by decide, by decide⟩
  · obtain ⟨h1, h2⟩ := cov_mp; rw [h1, h2]; exact ⟨by decide, by decide⟩
  · obtain ⟨h1, h2⟩ := cov_mm; rw [h1, h2]; exact ⟨by decide, by decide⟩

end ArkLib.ProximityGap.Frontier.G263JointRankSignFreedom
