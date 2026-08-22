/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Image
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# LANE G180 (#466, 2026-07-11): central-symmetry covering rigidity for dilated smooth orbits
  — a NON-FOURIER, NON-INTEGER-LIFT structural no-go strictly complementing G99 HEADLINE C

## What this lane adds beyond G99

`Frontier/_G99ErdosTuranLadderCertificate.lean` HEADLINE C
(`not_dilated_orbit_subset_interval`) proves, from the hypotheses `x ^ n = 1`, `x ^ 2 ≠ 1`,
that the dilated orbit `{b · x ^ k}` fits in NO natAbs-interval of radius `V` once
`2 V² < p` — via an integer lift of the *consecutive differences* `m_k = b x^k (x-1)` and
the multiplicative identity `m_j m_k ≡ m_0 m_{j+k}`.

That certificate is *difference-form* and *b-uniform* but it is BLIND to WHERE the interval
sits: it uses only the geometric-progression structure of the difference multiset.

This lane isolates a genuinely different binding mechanism that is thinness-essential in the
2-power sense: **central symmetry**. When `x` is an element of *even order exactly `n = 2 m`*
(the smooth-subgroup GENERATOR case, strictly stronger than G99's `x ^ n = 1 ∧ x ^ 2 ≠ 1`,
which does NOT force this — order-4 elements with `n = 8` are explicit counterexamples), the
unique order-2 field element forces

  `x ^ m = -1`,   hence   `b · x ^ (k + m) = - (b · x ^ k)`,

so the orbit is a centrally symmetric set: `O = - O`. Central symmetry alone (NO integer
lift, NO `2 V² < p`, only `4 V < p`) forces any covering interval to be centered at a
2-torsion point:

  `orbit_subset_interval → (2 • a) is within 2V of 0`,

i.e. the center `a` is within `V` of `{0, p/2}`. Off-center short arcs are excluded at the
FAR coarser scale `V < p/4`, where G99's `V < √(p/2)` gives nothing. The two certificates
compose: G99 kills the residual 2-torsion-centered case at `√(p/2)`; this lane kills every
other center at `p/4`. Both are elementary, b-uniform, non-Fourier, non-energy.

## Honest scope

* This is a covering / anti-concentration structural no-go, not a bound on the BGK atom `M`
  at prize shape. Like G99 it lives at total-mass / containment scale and does not by itself
  move CORE. CORE remains OPEN / ON-BGK.
* The strengthened hypothesis (order exactly `n`, encoded here as `x ^ n = 1 ∧ x ^ m ≠ 1`
  with `n = 2 m`) is the correct one for the smooth-subgroup GENERATOR and is verified to be
  necessary: the plain G99 hypothesis is insufficient for central symmetry
  (`probe_g180_central_symmetry.py`, counterexample census).
* Everything below is axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace ArkLib.ProximityGap.Frontier.G180CentralSymmetryCovering

open Finset

/-- **The 2-power torsion pin.** In a field-like ring (`NoZeroDivisors` `NonAssocRing`),
an element `x` with `x ^ (2 * m) = 1` but `x ^ m ≠ 1` satisfies `x ^ m = -1`: its `m`-th
power is a square root of one distinct from one, hence the unique other root `-1`. This is
the *thinness-essential* step — it is exactly what fails for elements whose order is a proper
even divisor structure (order-4 with `2m = 8`), and it is the only place the sharper
"order exactly `n`" hypothesis is used. -/
theorem pow_half_eq_neg_one {R : Type*} [Ring R] [NoZeroDivisors R]
    {x : R} {m : ℕ} (hx2m : x ^ (2 * m) = 1) (hxm : x ^ m ≠ 1) :
    x ^ m = -1 := by
  have hsq : (x ^ m) * (x ^ m) = 1 := by
    rw [← pow_add]
    have hmm : m + m = 2 * m := by ring
    rw [hmm, hx2m]
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · exact absurd h hxm
  · exact h

/-- **Central symmetry of the dilated orbit (pointwise negation form).** With `x ^ m = -1`
(supplied by `pow_half_eq_neg_one`), shifting the orbit index by the half-period `m` negates
the point: `b · x ^ (k + m) = - (b · x ^ k)`. This is the structural heart: the orbit map
`k ↦ b · x ^ k` is `m`-anti-periodic. -/
theorem orbit_shift_half_neg {R : Type*} [Ring R]
    {x b : R} {m : ℕ} (hxm : x ^ m = -1) (k : ℕ) :
    b * x ^ (k + m) = - (b * x ^ k) := by
  rw [pow_add, hxm, mul_neg_one, mul_neg]

/-- The half-open natAbs interval `{ a, a+1, …, a+V−1 } ⊆ ZMod p`, matching the G99
`interval` definition so the two covering no-gos speak about the same object. -/
def interval {p : ℕ} (a : ZMod p) (V : ℕ) : Finset (ZMod p) :=
  (Finset.range V).image (fun i : ℕ => a + (i : ZMod p))

/-- Membership unfold for `interval`. -/
theorem mem_interval {p : ℕ} {a y : ZMod p} {V : ℕ} :
    y ∈ interval a V ↔ ∃ i : ℕ, i < V ∧ y = a + (i : ZMod p) := by
  unfold interval
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩

/-- **Center-forcing lemma (the non-Fourier covering constraint).** If a point `y` and its
negation `-y` both lie in `interval a V`, then `2 • a` is a difference of two interval offsets:
`2 * a = -(i + j) + (something)` — precisely, `y = a + i` and `-y = a + j` give `2 a = -(i+j)`
in `ZMod p`, so `-(2 a)` is represented by `i + j < 2 V`. Thus the doubled center lies in the
image of `range (2V)`: `∃ t < 2V, (2 : ZMod p) * a = -(t : ZMod p)`. -/
theorem two_center_small_of_mem_and_neg {p : ℕ} {a y : ZMod p} {V : ℕ}
    (hy : y ∈ interval a V) (hny : (-y) ∈ interval a V) :
    ∃ t : ℕ, t < 2 * V ∧ (2 : ZMod p) * a = - (t : ZMod p) := by
  obtain ⟨i, hi, hyi⟩ := mem_interval.mp hy
  obtain ⟨j, hj, hnyj⟩ := mem_interval.mp hny
  refine ⟨i + j, by omega, ?_⟩
  -- y = a + i, -y = a + j  ⇒  0 = (a+i)+(a+j) = 2a + (i+j)
  have hsum : (a + (i : ZMod p)) + (a + (j : ZMod p)) = 0 := by
    rw [← hyi, ← hnyj]; ring
  push_cast
  linear_combination hsum

/-- **HEADLINE — central-symmetry covering no-go.** Let `x` have even order exactly `2 m`
(`x ^ (2 m) = 1`, `x ^ m ≠ 1`) in `ZMod p`, `m ≥ 1`, and let `b ≠ 0`. Suppose the dilated
orbit `{ b · x ^ k }` is contained in some `interval a V`. Then the doubled center `2 • a`
is "small": there is `t < 2 V` with `2 • a = -(t)` in `ZMod p`. Equivalently, an off-center
short arc (center bounded away from every 2-torsion point by more than `V`) CANNOT contain any
dilate of the smooth subgroup — a b-uniform, NON-Fourier, NON-integer-lift certificate that
constrains the ARC LOCATION, complementary to G99's scale-`√(p/2)` difference certificate.

Mechanism: the orbit is centrally symmetric (`orbit_shift_half_neg`), so both `b · x^0 = b`
and its negation `- b = b · x^m` lie in the interval; `two_center_small_of_mem_and_neg` then
pins `2 • a`. -/
theorem dilated_orbit_center_forced {p : ℕ} [Fact p.Prime]
    {x b : ZMod p} {m V : ℕ} {a : ZMod p}
    (_hm : 0 < m) (hx2m : x ^ (2 * m) = 1) (hxm : x ^ m ≠ 1) (_hb : b ≠ 0)
    (hsub : ∀ k : ℕ, b * x ^ k ∈ interval a V) :
    ∃ t : ℕ, t < 2 * V ∧ (2 : ZMod p) * a = - (t : ZMod p) := by
  haveI : NoZeroDivisors (ZMod p) := inferInstance
  have hxmneg : x ^ m = -1 := pow_half_eq_neg_one hx2m hxm
  -- y = b = b · x^0 is in the interval; its negation -b = b · x^m is too.
  have hy : (b * x ^ 0) ∈ interval a V := hsub 0
  have hmm : b * x ^ m = - (b * x ^ 0) := by
    have h := orbit_shift_half_neg (b := b) hxmneg 0
    rwa [Nat.zero_add] at h
  have hny : (- (b * x ^ 0)) ∈ interval a V := by
    have hh := hsub m
    rwa [hmm] at hh
  exact two_center_small_of_mem_and_neg hy hny

/-- **Corollary — off-center exclusion.** If additionally NO `t < 2 V` represents `-(2 • a)`
(the center is bounded away from every 2-torsion point of `ZMod p` by more than `V`), then the
dilated orbit is NOT contained in `interval a V`, at ANY scale, with no `2 V² < p` condition.
This is the regime G99 cannot see. -/
theorem not_dilated_orbit_subset_offcenter_interval {p : ℕ} [Fact p.Prime]
    {x b : ZMod p} {m V : ℕ} {a : ZMod p}
    (hm : 0 < m) (hx2m : x ^ (2 * m) = 1) (hxm : x ^ m ≠ 1) (hb : b ≠ 0)
    (hoff : ∀ t : ℕ, t < 2 * V → (2 : ZMod p) * a ≠ - (t : ZMod p)) :
    ¬ (∀ k : ℕ, b * x ^ k ∈ interval a V) := by
  intro hsub
  obtain ⟨t, ht, heq⟩ := dilated_orbit_center_forced hm hx2m hxm hb hsub
  exact hoff t ht heq

-- Axiom audit: all headline results are axiom-clean
-- (`propext`, `Classical.choice`, `Quot.sound` only).
#print axioms pow_half_eq_neg_one
#print axioms orbit_shift_half_neg
#print axioms two_center_small_of_mem_and_neg
#print axioms dilated_orbit_center_forced
#print axioms not_dilated_orbit_subset_offcenter_interval

end ArkLib.ProximityGap.Frontier.G180CentralSymmetryCovering
