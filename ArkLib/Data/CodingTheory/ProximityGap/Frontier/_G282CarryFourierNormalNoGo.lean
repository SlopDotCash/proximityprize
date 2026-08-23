/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# G282: primitive carry-Fourier normals do not carry the CORE sign (#466)

G278 decomposed the exact adjacent-rank weighted relation count by integer lift carry

```text
2y + sum(B) - z - sum(A) = k p,       J_r = sum_k J_{r,k},
A_r = p J_r - n^2 C(n,r) C(n,r-1).
```

It proved the involutive symmetry `J_{r,k}=J_{r,-k}` and showed that neither the zero-carry
block nor all nonzero carries certifies the gate. G281 then proved that even perfect Eulerian carry
*shape*, amplified by the complete lawful floor, misses the production gate by `271x` to `> 10^10x`.
Meanwhile G280 proved that a surviving sponsor certificate must carry a genuine odd real sign.

This file tests predeclared arithmetic normals not covered by those two-block/shape no-gos: real
Fourier characters of the carry histogram, aggregated over primitive characters by exact integer
Ramanujan sums. The exact probe of record,
`scripts/probes/g282_carry_fourier_normal_probe.py`, begins with

```text
T2 = sum_k (-1)^k J_k,
T3 = sum_k 2 cos(2 pi k/3) J_k,
T4 = sum_k   cos(  pi k/2) J_k,
T6 = sum_k 2 cos(  pi k/3) J_k.
```

All weights are integers. The probe then checks every primitive-character aggregate
`T_d = sum_k c_d(k) J_k` for conductors `2 ≤ d ≤ 128`, where `c_d` is the integer Ramanujan sum.
On the complete `n=16`, `p<2600` prime window at both live ranks plus four exact `n=32` late cells
(88 cells total), `T2` realizes all four sign quadrants against `A_r` (agreement `47/88`), while
every `T_d`, `3 ≤ d ≤ 128`, remains strictly positive across both gate signs.

The high-conductor tail is not an escape hatch. Every recorded histogram is supported on
`|k| ≤ 6` and satisfies `9 J_0 > sum_k J_k`. For `d ≥ 129` and nonzero `|k| ≤ 6`, put
`q = d / gcd(d,k)`. Then `q ≥ 22`, hence `phi(q) ≥ 8`, and the exact Ramanujan formula gives
`c_d(k) ≥ -phi(d)/8`, while `c_d(0)=phi(d)`. Therefore

```text
T_d ≥ phi(d)/8 * (9 J_0 - sum_k J_k) > 0.
```

Together with the exact finite scan, every primitive Ramanujan carry normal `T_d`, `d ≥ 3`, is
positive on all 88 cells despite both signs of the CORE gate. The only fluctuating conductor is
`d=2`, and it is sign-decoupled.

The abstract theorem below is stronger than the finite census in one direction: on *every* finite
carry space with a negation permutation and symmetric multiplicities, every odd carry weight is
annihilated exactly. More generally, every linear carry statistic equals its negation-evenization.
Therefore a genuinely signed carry certificate cannot come from an odd moment. The exact census
plus the zero-bin-dominance argument excludes the entire primitive Ramanujan family at every
conductor. Any surviving carry refinement must use a non-Ramanujan weight or row-labelled
information; merely increasing conductor cannot help.

FS15-FS18 are fully consumed: they give fixed-depth, almost-all-prime magnitude ladders and the
sharp resultant envelope, but G64 forces the deployed sponsor exceptional by depth six. They
neither select the sponsor prime nor provide the row-labelled sign that these carry normals lack.

Honest scope: abstract annihilation theorem plus four exact calibrated cells. This is a route no-go,
not a sponsor-prime estimate and not prize closure. CORE remains OPEN / ON-BGK.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G282CarryFourierNormalNoGo

open scoped BigOperators

/-- A linear statistic of a finite carry histogram. `J k` is the multiplicity of carry bin `k` and
`a k` its arithmetic weight. -/
def carryPairing {ι : Type*} [Fintype ι] (J a : ι → ℤ) : ℤ := ∑ k, J k * a k

/-- Reindex a carry statistic by any permutation of its bins. -/
theorem carryPairing_reindex {ι : Type*} [Fintype ι] (neg : ι ≃ ι) (J a : ι → ℤ) :
    carryPairing J a = carryPairing (fun k => J (neg k)) (fun k => a (neg k)) := by
  unfold carryPairing
  exact Fintype.sum_equiv neg.symm _ _ (fun k => by simp)

/-- **Odd carry normals vanish.** If negation permutes the carry bins, the histogram is symmetric,
and the weight is odd, then its weighted statistic is exactly zero. This kills every odd carry
moment and every other sign proposed solely through `k ↦ -k`. -/
theorem symmetric_carry_kills_odd {ι : Type*} [Fintype ι] (neg : ι ≃ ι)
    (J a : ι → ℤ) (hJ : ∀ k, J (neg k) = J k) (ha : ∀ k, a (neg k) = -a k) :
    carryPairing J a = 0 := by
  have h := carryPairing_reindex neg J a
  simp_rw [hJ, ha] at h
  unfold carryPairing at h ⊢
  simp only [mul_neg, Finset.sum_neg_distrib] at h
  linarith

/-- Rational version of `carryPairing`, used to state exact evenization. -/
def carryPairingQ {ι : Type*} [Fintype ι] (J a : ι → ℚ) : ℚ := ∑ k, J k * a k

/-- **Every linear carry statistic sees only the negation-even part of its weight.** For a symmetric
histogram, replacing `a(k)` by `(a(k)+a(-k))/2` does not change the statistic. The odd component is
not merely small; it is identically in the kernel. -/
theorem carryPairing_eq_evenized {ι : Type*} [Fintype ι] (neg : ι ≃ ι)
    (J a : ι → ℚ) (hJ : ∀ k, J (neg k) = J k) :
    carryPairingQ J a = carryPairingQ J (fun k => (a k + a (neg k)) / 2) := by
  have hreindex : carryPairingQ J a =
      carryPairingQ (fun k => J (neg k)) (fun k => a (neg k)) := by
    unfold carryPairingQ
    exact Fintype.sum_equiv neg.symm _ _ (fun k => by simp)
  have hreindex' : carryPairingQ J a = carryPairingQ J (fun k => a (neg k)) := by
    simpa only [hJ] using hreindex
  unfold carryPairingQ at hreindex' ⊢
  calc
    ∑ k, J k * a k = (1 / 2 : ℚ) * ((∑ k, J k * a k) + ∑ k, J k * a (neg k)) := by
      rw [← hreindex']
      ring
    _ = ∑ k, J k * ((a k + a (neg k)) / 2) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

/-- **Zero-bin dominance forces positivity for every weight with a one-eighth negative tail.**
This is the abstract inequality used for high-conductor Ramanujan sums. If the distinguished
weight is positive, every other weight is at least minus one eighth of it, all multiplicities are
nonnegative, and the distinguished bin contains more than one ninth of the total mass, then the
weighted statistic is strictly positive. The tail condition is division-free, so no divisibility
assumption on the distinguished weight is hidden. -/
theorem dominant_zero_bin_forces_positive {ι : Type*} [Fintype ι]
    (zero : ι) (J a : ι → ℤ)
    (hapos : 0 < a zero) (hJ : ∀ k, 0 ≤ J k)
    (htail : ∀ k, k ≠ zero → -a zero ≤ 8 * a k)
    (hdominant : ∑ k, J k < 9 * J zero) :
    0 < carryPairing J a := by
  classical
  have hrest : -(a zero) * ∑ k ∈ Finset.univ.erase zero, J k ≤
      ∑ k ∈ Finset.univ.erase zero, J k * (8 * a k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hk0 : k ≠ zero := by simpa using hk
    have := mul_le_mul_of_nonneg_left (htail k hk0) (hJ k)
    nlinarith
  have hsum : (∑ k, J k) = J zero + ∑ k ∈ Finset.univ.erase zero, J k := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ zero)]
    ring
  have hpair : 8 * carryPairing J a =
      8 * J zero * a zero + ∑ k ∈ Finset.univ.erase zero, J k * (8 * a k) := by
    unfold carryPairing
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ zero)]
    calc
      8 * ((∑ k ∈ Finset.univ.erase zero, J k * a k) + J zero * a zero) =
          8 * J zero * a zero + 8 * ∑ k ∈ Finset.univ.erase zero, J k * a k := by ring
      _ = 8 * J zero * a zero + ∑ k ∈ Finset.univ.erase zero, 8 * (J k * a k) := by
        rw [Finset.mul_sum]
      _ = 8 * J zero * a zero + ∑ k ∈ Finset.univ.erase zero, J k * (8 * a k) := by
        apply congrArg (fun x => 8 * J zero * a zero + x)
        apply Finset.sum_congr rfl
        intro k _
        ring
  rw [hsum] at hdominant
  rw [← mul_pos_iff_of_pos_left (by norm_num : (0 : ℤ) < 8)]
  rw [hpair]
  nlinarith

/-! ## Exact calibrated carry-Fourier cells

The values below are recomputed from the canonical G278 integer-lift census. `gate=A_r`;
`T2,T3,T4,T6` are the exact integer carry-character statistics defined in the module docstring. -/

/-- One exact weighted-kernel carry-Fourier cell. -/
structure Cell where
  gate : ℤ
  T2 : ℤ
  T3 : ℤ
  T4 : ℤ
  T6 : ℤ
  deriving DecidableEq, Repr

/-- `(n,p,r)=(16,193,5)`: positive gate but negative parity-carry normal. -/
def p193r5 : Cell :=
  { gate := 3843136, T2 := -163896, T3 := 344054, T4 := 1501916, T6 := 9283734 }

/-- `(16,257,5)`: negative gate and negative parity-carry normal. -/
def p257r5 : Cell :=
  { gate := -1051408, T2 := -88764, T3 := 65288, T4 := 599058, T6 := 5254932 }

/-- `(16,433,5)`: positive gate and positive parity-carry normal. -/
def p433r5 : Cell :=
  { gate := 3425440, T2 := 474180, T3 := 2441678, T4 := 2170622, T6 := 6661278 }

/-- `(16,1553,5)`: negative gate but every tested low-conductor carry normal is positive. -/
def p1553r5 : Cell :=
  { gate := -16213712, T2 := 383316, T3 := 809194, T4 := 516342, T6 := 1581282 }

/-- The fluctuating parity normal `T2` realizes all four sign quadrants against the exact gate. -/
theorem parity_normal_all_four_quadrants :
    (0 < p193r5.gate ∧ p193r5.T2 < 0) ∧
    (p257r5.gate < 0 ∧ p257r5.T2 < 0) ∧
    (0 < p433r5.gate ∧ 0 < p433r5.T2) ∧
    (p1553r5.gate < 0 ∧ 0 < p1553r5.T2) := by
  decide

/-- Positive `T3,T4,T6` do not imply a positive gate: all three are positive at an exact negative
CORE cell. Hence none is a one-sided sign certificate. -/
theorem positive_low_normals_do_not_imply_gate :
    p1553r5.gate < 0 ∧ 0 < p1553r5.T3 ∧ 0 < p1553r5.T4 ∧ 0 < p1553r5.T6 := by
  decide

/-- Packaged G282 no-go: odd carry weights vanish abstractly, parity is sign-decoupled, and the
first other real carry characters can remain positive when the CORE gate is negative. The
all-conductor Ramanujan conclusion additionally uses `dominant_zero_bin_forces_positive` with the
exact support and dominance facts checked by the probe of record. -/
theorem fixed_low_conductor_carry_normals_do_not_pin_sign :
    ((0 < p193r5.gate ∧ p193r5.T2 < 0) ∧
      (p257r5.gate < 0 ∧ p257r5.T2 < 0) ∧
      (0 < p433r5.gate ∧ 0 < p433r5.T2) ∧
      (p1553r5.gate < 0 ∧ 0 < p1553r5.T2)) ∧
    (p1553r5.gate < 0 ∧ 0 < p1553r5.T3 ∧ 0 < p1553r5.T4 ∧ 0 < p1553r5.T6) :=
  ⟨parity_normal_all_four_quadrants, positive_low_normals_do_not_imply_gate⟩

#print axioms symmetric_carry_kills_odd
#print axioms carryPairing_eq_evenized
#print axioms dominant_zero_bin_forces_positive
#print axioms parity_normal_all_four_quadrants
#print axioms positive_low_normals_do_not_imply_gate
#print axioms fixed_low_conductor_carry_normals_do_not_pin_sign

end ArkLib.ProximityGap.Frontier.G282CarryFourierNormalNoGo
