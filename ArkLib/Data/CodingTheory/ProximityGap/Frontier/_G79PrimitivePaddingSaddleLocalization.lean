/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# G79: bounded primitive sectors are absorbed at the saddle

R369 isolates the surviving production-facing conjecture at the single depth
`r = ceil(log q)`.  Its padding calculation gives the envelope

`J_s * (r descFactorial s)^2 * n^(r-s)`

for collisions whose maximally cancelled primitive core has depth `s`.  This file proves the
arithmetic localization behind that calculation.  In the lower half `2s <= r+1`, the last `s`
odd Wick factors already contribute at least `r^s`, while `(r)_s <= r^s`.  Consequently an
orbit budget `J_s <= C*n` costs at most `C*r^s/n^(s-1)` of one Wick budget.

The result is an exact consumer: it does not assert the combinatorial padding envelope or the
orbit-count hypothesis.  In particular, one rotation orbit has linear size, but the union of all
primitive depth-`s` orbits need not.  Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G79PrimitivePaddingSaddleLocalization

open Finset

/-- The last `s` odd factors in the depth-`r` Wick double factorial. -/
def oddWickTail (r s : ℕ) : ℕ :=
  ∏ i ∈ Finset.range s, (2 * (r - i) - 1)

/-- Every one of the last `s` odd Wick factors is at least `r` in the lower half of the
depth range. -/
theorem le_oddWickTail_factor {r s i : ℕ} (hrs : 2 * s ≤ r + 1)
    (hi : i ∈ Finset.range s) :
    r ≤ 2 * (r - i) - 1 := by
  rw [Finset.mem_range] at hi
  omega

/-- **Odd-tail saddle gain.**  In the lower half, the last `s` Wick factors contribute at least
`r^s`. -/
theorem pow_le_oddWickTail {r s : ℕ} (hrs : 2 * s ≤ r + 1) :
    r ^ s ≤ oddWickTail r s := by
  rw [oddWickTail, ← Finset.prod_const, Finset.card_range]
  exact Finset.prod_le_prod' (fun i hi => le_oddWickTail_factor hrs hi)

/-- R369's padded-sector envelope. -/
def padEnvelope (n r J s : ℕ) : ℕ :=
  J * (r.descFactorial s) ^ 2 * n ^ (r - s)

/-- The insertion choices are bounded by `r^(2s)`. -/
theorem padEnvelope_le_pow (n r J s : ℕ) :
    padEnvelope n r J s ≤ J * r ^ (2 * s) * n ^ (r - s) := by
  unfold padEnvelope
  have hfall : r.descFactorial s ≤ r ^ s := Nat.descFactorial_le_pow r s
  have hsq : (r.descFactorial s) ^ 2 ≤ (r ^ s) ^ 2 := Nat.pow_le_pow_left hfall 2
  calc
    J * (r.descFactorial s) ^ 2 * n ^ (r - s)
        ≤ J * (r ^ s) ^ 2 * n ^ (r - s) := by gcongr
    _ = J * r ^ (2 * s) * n ^ (r - s) := by ring

/-- **Exact bounded-sector absorption criterion.**  If a primitive sector has the R369 padding
envelope and its normalized orbit count obeys `J*r^s <= n^s`, then the sector is paid for by its
`s` odd Wick-tail factors (and the remaining `n^(r-s)` free padding mass).

This is the denominator-cleared form of
`W_s / (oddTail*n^r) <= (J/n^s)*r^s`. -/
theorem paddedSector_le_oddTailWick
    {n r J s W : ℕ}
    (hrs : 2 * s ≤ r + 1)
    (hsr : s ≤ r)
    (hW : W ≤ padEnvelope n r J s)
    (hJ : J * r ^ s ≤ n ^ s) :
    W ≤ oddWickTail r s * n ^ r := by
  have hpad := padEnvelope_le_pow n r J s
  have htail := pow_le_oddWickTail hrs
  calc
    W ≤ padEnvelope n r J s := hW
    _ ≤ J * r ^ (2 * s) * n ^ (r - s) := hpad
    _ = (J * r ^ s) * r ^ s * n ^ (r - s) := by ring
    _ ≤ n ^ s * oddWickTail r s * n ^ (r - s) := by gcongr
    _ = oddWickTail r s * n ^ r := by
      rw [← pow_add₀]
      rw [Nat.add_sub_of_le hsr]
      ring

/-- Linear primitive-orbit budgets reduce to the explicit saddle condition
`C*r^s <= n^(s-1)`. -/
theorem paddedSector_le_oddTailWick_of_linear_orbits
    {n r J s W C : ℕ}
    (hn : 0 < n)
    (hrs : 2 * s ≤ r + 1)
    (hsr : s ≤ r)
    (hs : 1 ≤ s)
    (hW : W ≤ padEnvelope n r J s)
    (hJ : J ≤ C * n)
    (hsmall : C * r ^ s ≤ n ^ (s - 1)) :
    W ≤ oddWickTail r s * n ^ r := by
  apply paddedSector_le_oddTailWick hrs hsr hW
  calc
    J * r ^ s ≤ (C * n) * r ^ s := by gcongr
    _ = n * (C * r ^ s) := by ring
    _ ≤ n * n ^ (s - 1) := by gcongr
    _ = n ^ s := by
      obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hs
      simp [pow_succ]

end ArkLib.ProximityGap.Frontier.G79PrimitivePaddingSaddleLocalization

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G79PrimitivePaddingSaddleLocalization.pow_le_oddWickTail
#print axioms
  ArkLib.ProximityGap.Frontier.G79PrimitivePaddingSaddleLocalization.paddedSector_le_oddTailWick
#print axioms
  ArkLib.ProximityGap.Frontier.G79PrimitivePaddingSaddleLocalization.paddedSector_le_oddTailWick_of_linear_orbits
