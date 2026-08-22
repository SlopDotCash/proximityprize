/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G136UnitCircleMann

/-!
# G136 (part 3a): the accident tolerance pin — the rung-2 anchor allows at most three

Under the accident law `E₂ = 3n² − 3n + n·A` (part 2, designed; numerics verified), the
rung-2 anchor `q·E₂ ≤ 3·q·n² + n⁴` is equivalent to `q·n·A ≤ 3·q·n + n⁴`, i.e. to
`q·A ≤ 3·q + n³`.  At production (`n³ = 2^90 < q`) this pins the tolerance EXACTLY:

```text
q·A ≤ 3·q + n³  ⟺  A ≤ 3.
```

So the production rung-2 anchor is equivalent (through the accident law) to: **the certified
prime admits at most three accidents** — at most three unit-triple solutions of
`a + b = c + 1` in `μ_{2^30}` beyond the Mann families.  Heuristically the expected number
is `≈ 2^{-68}`; the criterion is a finite arithmetic statement about one prime.

**Honest scope.**  The tolerance arithmetic is unconditional; the accident law (part 2) and
the accident count at the certified primes (the wall) remain open.  CORE remains OPEN.
Issue #466 (G136).
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G136AccidentTolerance

/-- **The tolerance pin.**  When the DC term is below one `q` (production: `n³ = 2^90 < q`),
the anchor slack admits exactly three accidents. -/
theorem accident_tolerance {q A n3 : ℕ} (hq : n3 < q) :
    q * A ≤ 3 * q + n3 ↔ A ≤ 3 := by
  constructor
  · intro h
    by_contra hA
    have h4 : 4 ≤ A := by omega
    have : 4 * q ≤ q * A := by
      calc
        4 * q = q * 4 := Nat.mul_comm 4 q
        _ ≤ q * A := Nat.mul_le_mul_left q h4
    omega
  · intro h
    calc
      q * A ≤ q * 3 := Nat.mul_le_mul_left q h
      _ = 3 * q := Nat.mul_comm q 3
      _ ≤ 3 * q + n3 := Nat.le_add_right _ _

/-- The anchor inequality in accident-law form, both sides scaled by `n`: for `n ≥ 1`,
`q·(3n² − 3n + n·A) ≤ 3·q·n² + n⁴ ⟺ q·A ≤ 3·q + n³`. -/
theorem anchor_iff_tolerance {q A n : ℕ} (hn : 1 ≤ n) :
    q * (3 * n ^ 2 - 3 * n + n * A) ≤ 3 * q * n ^ 2 + n ^ 4
      ↔ q * A ≤ 3 * q + n ^ 3 := by
  have h3n : 3 * n ≤ 3 * n ^ 2 := by
    have hnn : n ≤ n ^ 2 := by
      calc
        n = n * 1 := (Nat.mul_one n).symm
        _ ≤ n * n := Nat.mul_le_mul_left n hn
        _ = n ^ 2 := (sq n).symm
    omega
  -- the subtraction-free key identity
  have hkey : q * (3 * n ^ 2 - 3 * n + n * A) + 3 * q * n
      = 3 * q * n ^ 2 + q * n * A := by
    have h1 : 3 * n ^ 2 - 3 * n + n * A + 3 * n = 3 * n ^ 2 + n * A := by omega
    calc
      q * (3 * n ^ 2 - 3 * n + n * A) + 3 * q * n
          = q * ((3 * n ^ 2 - 3 * n + n * A) + 3 * n) := by ring
      _ = q * (3 * n ^ 2 + n * A) := by rw [h1]
      _ = 3 * q * n ^ 2 + q * n * A := by ring
  constructor
  · intro h
    have hadd := Nat.add_le_add_right h (3 * q * n)
    rw [hkey, Nat.add_assoc] at hadd
    have hqnA : q * n * A ≤ n ^ 4 + 3 * q * n :=
      Nat.le_of_add_le_add_left hadd
    have hdiv : n * (q * A) ≤ n * (3 * q + n ^ 3) := by
      calc
        n * (q * A) = q * n * A := by ring
        _ ≤ n ^ 4 + 3 * q * n := hqnA
        _ = n * (3 * q + n ^ 3) := by ring
    exact Nat.le_of_mul_le_mul_left hdiv (by omega)
  · intro h
    have hmul : n * (q * A) ≤ n * (3 * q + n ^ 3) := Nat.mul_le_mul_left n h
    have hqnA : q * n * A ≤ n ^ 4 + 3 * q * n := by
      calc
        q * n * A = n * (q * A) := by ring
        _ ≤ n * (3 * q + n ^ 3) := hmul
        _ = n ^ 4 + 3 * q * n := by ring
    have hadd : q * (3 * n ^ 2 - 3 * n + n * A) + 3 * q * n
        ≤ (3 * q * n ^ 2 + n ^ 4) + 3 * q * n := by
      rw [hkey]
      calc
        3 * q * n ^ 2 + q * n * A ≤ 3 * q * n ^ 2 + (n ^ 4 + 3 * q * n) :=
          Nat.add_le_add_left hqnA _
        _ = (3 * q * n ^ 2 + n ^ 4) + 3 * q * n := by ring
    exact Nat.le_of_add_le_add_right hadd

/-- Production instantiation: at `n = 2^30`, `q > 2^90`, the anchor-law slack is exactly
three accidents. -/
theorem production_accident_tolerance {q A : ℕ} (hq : 2 ^ 90 < q) :
    q * A ≤ 3 * q + (2 ^ 30) ^ 3 ↔ A ≤ 3 := by
  have h : ((2 : ℕ) ^ 30) ^ 3 = 2 ^ 90 := by norm_num
  rw [h]
  exact accident_tolerance hq

end ArkLib.ProximityGap.Frontier.G136AccidentTolerance

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.G136AccidentTolerance.accident_tolerance
#print axioms ArkLib.ProximityGap.Frontier.G136AccidentTolerance.anchor_iff_tolerance
#print axioms
  ArkLib.ProximityGap.Frontier.G136AccidentTolerance.production_accident_tolerance
