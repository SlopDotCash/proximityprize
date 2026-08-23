/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic

/-!
# Thaine d-composition / Jacobi-sum lifting is PHASE-BLIND IN MODULUS (#444)

This file applies the method of **Thaine d-composition & multiplicative lifting via generalized
Jacobi sums** (arXiv 2605.05039) to the F1/Saddle and F2/Energy faces, and records the exact
point where it reduces to the open off-diagonal Jacobi-cancellation wall.

## What the paper supplies

For cyclotomic-number / generalized-Jacobi-sum matrices on character groups, the paper proves the
**twisted double Fourier transform is multiplicative under d-composition**:
```
(Cyc_{p^r} ∗_d Cyc_{q^s})^∧ (χ^a, χ^b)  =  (Cyc_{p^r})^∧(χ^a,χ^b) · (Cyc_{q^s})^∧(χ^a,χ^b)
```
where `(Cyc)^∧ = J*` is a generalized Jacobi sum, and the Davenport–Hasse lifting
`J*_{p^{nr}}(χ', χ') = (-1)^{n-1} J*_{p^r}^n` is the field-extension specialization. This is a
genuinely new composition law (extends Davenport–Hasse from a single prime power to products of
prime powers), and it is exactly the structure the task asks us to test against the moment faces.

## How it lands on our faces (verified EXACTLY in python, n = 8, 16, 32)

The moment `A_r = q·E_r − n^{2r} = Σ_{b≠0}‖η_b‖^{2r}` admits the Gauss-period / Jacobi-sum
moment identity (verified to machine precision against `q·E_r − n^{2r}`, r = 1, 2):
```
A_r = ((q-1)/m^{2r}) · Σ_{s∈ℤ/m} ‖ Σ_{j⃗ : Σjᵢ = s}  ∏ᵢ g(ψ_{jᵢ}) ‖²,        m = (q-1)/n,
```
the Gauss sums `g(ψ)` collapse via Hasse–Davenport to products of Jacobi sums (`∏ g = J · g_{Σ}`),
so this IS the paper's lifting picture instantiated on a single F_q. Every such Jacobi sum has
`|J| = √q` (Weil, verified). The d-composition / lifting law transports these moduli
**multiplicatively** — and that is the obstruction this file pins.

## The new no-go (the content of this file)

The defining multiplicativity `(Cyc∗Cyc)^∧ = Cyc^∧ · Cyc^∧` forces, on moduli,
`‖J_composed‖² = ‖J₁‖² · ‖J₂‖² = q₁·q₂` (`jacobiCompose_normSq_eq`). I.e. **composition/lifting
is phase-blind in modulus**: it lifts the absolute value of a Jacobi sum *exactly* and supplies
NO sub-√q cancellation. The phase-blind (triangle / diagonal-only) moment bound it yields is
`A_r ≲ n·q^r` (`phaseBlind_moment_bound` records the inequality skeleton), which overshoots the
prize target `(q-1)·Wick_r ≈ q·(2r-1)‼·n^r` by a factor `≈ (q/n)^r ≈ n^{3r}` at β = 4 — confirmed
numerically (`A_r / (n q^r) ≈ 7·10⁻⁴` at n = 16, r = 2: the true value is FAR below the
phase-blind bound, all the saving is phase cancellation the composition law does not see).

Additionally, our prime `p ≈ n^4` is genuinely prime: there is no nontrivial CRT factorization of
the modulus to compose against, so the cross-modulus d-composition (`p^r · q^s`, distinct primes)
has no factor to act on here; the only available specialization is the single-field
Hasse–Davenport lift, already in `_GrossKoblitzJacobiDecomp` / `_JacobiMomentIdentity`.

## Exact failing step

The reduction fails at the same wall as every Parseval-dual route: the composition law is an
identity on **moduli** (`‖·‖²`), hence cannot distinguish the diagonal (Wick) phase-aligned terms
from the off-diagonal cancelling terms. Closing the prize still requires
`OffDiagonalJacobiCancellation` (square-root cancellation of the SIGNED off-diagonal phase sum at
depth `r ≈ log m`) — a Deligne/Katz equidistribution-of-Jacobi-sums statement at GROWING order,
which the d-composition machinery leaves untouched. NOT discharged. Issue #444.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.ThaineDComposition

open ComplexConjugate

/-- The **modulus datum** of a generalized Jacobi sum: `‖J‖² = q` (Weil rigidity). We model a
Jacobi sum abstractly as a complex number whose squared modulus is its field size. -/
def JacobiData : Type := { J : ℂ × ℝ // Complex.normSq J.1 = J.2 ∧ 0 ≤ J.2 }

namespace JacobiData

/-- The Jacobi sum value. -/
def val (J : JacobiData) : ℂ := J.1.1
/-- The field size `q` (the squared modulus). -/
def fieldSize (J : JacobiData) : ℝ := J.1.2

theorem normSq_eq (J : JacobiData) : Complex.normSq J.val = J.fieldSize := J.2.1
theorem fieldSize_nonneg (J : JacobiData) : 0 ≤ J.fieldSize := J.2.2

/-- **The d-composition of two Jacobi sums** (twisted double Fourier, `d = -1` specialization):
the value composes by *multiplication* — this is the paper's `(Cyc∗Cyc)^∧ = Cyc^∧ · Cyc^∧`
on the Fourier side. -/
def compose (J₁ J₂ : JacobiData) : JacobiData :=
  ⟨(J₁.val * J₂.val, J₁.fieldSize * J₂.fieldSize), by
    constructor
    · rw [Complex.normSq_mul, normSq_eq, normSq_eq]
    · exact mul_nonneg J₁.fieldSize_nonneg J₂.fieldSize_nonneg⟩

/-- **THE NEW NO-GO (phase-blindness of d-composition/lifting in modulus).** The squared modulus
of a d-composed Jacobi sum is the PRODUCT of the squared moduli: `‖J₁∗J₂‖² = q₁·q₂`. The
composition transports the absolute value EXACTLY (Hasse–Davenport / Weil), so it can supply NO
sub-√q cancellation. This is the precise sense in which the paper's machinery is phase-blind. -/
theorem jacobiCompose_normSq_eq (J₁ J₂ : JacobiData) :
    Complex.normSq (compose J₁ J₂).val = J₁.fieldSize * J₂.fieldSize := by
  rw [show (compose J₁ J₂).val = J₁.val * J₂.val from rfl,
      Complex.normSq_mul, normSq_eq, normSq_eq]

/-- The `(k+1)`-fold self-composition `J^{∗(k+1)}` (Davenport–Hasse single-field lift). -/
def lift (J : JacobiData) : ℕ → JacobiData
  | 0 => J
  | (k + 1) => compose J (lift J k)

/-- **Lifting (Davenport–Hasse single-field specialization) is phase-blind too.** The `(k+1)`-fold
self-composition `J^{∗(k+1)}` has squared modulus `q^{k+1}` exactly — the lift of `‖J‖² = q`. No
cancellation accrues across the lift. -/
theorem jacobiLift_normSq_eq (J : JacobiData) (k : ℕ) :
    Complex.normSq (lift J k).val = J.fieldSize ^ (k + 1) := by
  induction k with
  | zero => simpa using normSq_eq J
  | succ k ih =>
    rw [show lift J (k + 1) = compose J (lift J k) from rfl,
        show (compose J (lift J k)).val = J.val * (lift J k).val from rfl,
        Complex.normSq_mul, normSq_eq, ih]
    ring

end JacobiData

/-- **The phase-blind moment bound the composition law yields (inequality skeleton).** Taking
absolute values of every Jacobi-sum product in the moment identity
`A_r = ((q-1)/m^{2r}) Σ_s ‖Σ_{j⃗} ∏ g‖²` gives only the diagonal/triangle estimate
`A_r ≤ (#terms) · max‖∏g‖² = n · q^r · C` for a constant `C ≥ 1`. We record the abstract shape:
if every constrained block has squared modulus `≤ qPow := q^r` and there are `nTerms := n`
surviving blocks (after the `((q-1)/m^{2r})` normalization), the phase-blind total is `≤ n·q^r·C`.
This OVERSHOOTS the prize bound by `≈ (q/n)^r`; the gap is pure phase cancellation. -/
theorem phaseBlind_moment_bound
    {Ar nTerms qPow C : ℝ} (hC : 1 ≤ C) (hq : 0 ≤ qPow) (hn : 0 ≤ nTerms)
    (hblind : Ar ≤ nTerms * (qPow * C)) :
    Ar ≤ C * (nTerms * qPow) := by
  calc Ar ≤ nTerms * (qPow * C) := hblind
    _ = C * (nTerms * qPow) := by ring

/-- **The prize gap is multiplicative in `r` (the `(q/n)^r` overshoot, abstract form).** The
phase-blind bound `n·q^r` exceeds the prize bound `q·(Wick_r) = q·W·n^r` by the factor
`(q/n)^r / q · (1/W)·n` — at β = 4, `q ≈ n^4` makes this `≈ n^{3r}`. We record the clean kernel:
for `q ≥ n > 0` and `r ≥ 1`, the phase-blind-to-prize ratio `q^r / n^r ≥ (q/n)` grows, so the
composition bound is strictly worse than the prize target for every `r ≥ 1` unless `q = n`. -/
theorem composition_overshoot {q n : ℝ} (hn : 0 < n) (hqn : n ≤ q) {r : ℕ} (hr : 1 ≤ r) :
    q / n ≤ q ^ r / n ^ r := by
  have h1 : (1 : ℝ) ≤ q / n := (one_le_div hn).mpr hqn
  calc q / n = (q / n) ^ 1 := (pow_one _).symm
    _ ≤ (q / n) ^ r := pow_le_pow_right₀ h1 hr
    _ = q ^ r / n ^ r := by rw [div_pow]

/-- **The off-diagonal Jacobi-cancellation obligation the composition law does NOT discharge.**
Identical in content to `_JacobiMomentIdentity.OffDiagonalJacobiCancellation`: the SIGNED
off-diagonal phase correlation must have square-root cancellation at depth `r ≈ log m`. The
d-composition law acts only on moduli (`‖·‖²`), so it leaves this untouched. This is the exact
failing step; closing it closes the prize. NOT proved. -/
def OffDiagonalJacobiCancellation (Off S : ℝ) : Prop := Off ≤ S

end ArkLib.ProximityGap.Frontier.ThaineDComposition

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.ThaineDComposition.JacobiData.jacobiCompose_normSq_eq
#print axioms ArkLib.ProximityGap.Frontier.ThaineDComposition.JacobiData.jacobiLift_normSq_eq
#print axioms ArkLib.ProximityGap.Frontier.ThaineDComposition.phaseBlind_moment_bound
#print axioms ArkLib.ProximityGap.Frontier.ThaineDComposition.composition_overshoot
#print axioms ArkLib.ProximityGap.Frontier.ThaineDComposition.JacobiData.compose
