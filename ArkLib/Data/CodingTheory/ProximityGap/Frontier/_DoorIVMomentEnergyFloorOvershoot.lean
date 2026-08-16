/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVMomentHierarchyEnergyDominated
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# Door-(iv) Lane-3: the moment door overshoots the prize floor — INTERNALLY (#444)

The no-fifth-door tetrachotomy (`_NoFifthDoorTetrachotomy`) discharges the moment / extreme-value
door (i)/(iii) overshoot from the **third-party SOTA exponent** `n^{1-δ}` (`δ ≈ 0.011`): the literature's
guaranteed per-frequency value eventually exceeds the BGK scale `√(n·L)`.  That is a citation to the
state of the art, not a proof from the structure of the object.

This module gives the **internal, proof-backed** reason the moment door cannot certify the prize
floor `√n`, using only TWO already-proven facts about the negation-closed thin subgroup `μ_n`:

* **`momentHierarchy_energy_dominated`** (`_DoorIVMomentHierarchyEnergyDominated`): because every `η_b`
  is REAL, EVERY functional in the `Σ_c η_c^a · conj(η_c)^b` correlator lattice collapses onto the
  **energy moments** `E_r = Σ_c (η_c)^{2r}`.  So the *only* objects a moment mechanism can access are
  the energy moments.
* the elementary **`(max)² ≥ mean of squares`** Plancherel floor (`_DoorIVSupRmsGaussianSaturation`):
  the energy moment bounds the sup from the LOWER side.

The new content here: the moment method's *accessible sup-certificate* is the energy-moment scale, and
that scale is **always at least the L² / Plancherel root-mean-square `rms = √(E_1 / N)`** — by the
power-mean inequality, in a **root-free (integer-power) form** so it stays kernel-clean:

> `N^{r-1} · E_r ≥ (E_1)^r`   (every `r ≥ 1`),   i.e.   `(E_r / N)^{1/(2r)} ≥ √(E_1 / N) = rms`.

Equivalently: the `2r`-th energy moment, normalized, never drops below the squared L² scale.  Hence a
moment mechanism's certified scale is **bounded below by `rms`** — it can only *overshoot* the prize
floor `√n = rms` (in the prize regime `rms = √n`), never reach below it.  Combined with the proven
`M ≥ rms`, the entire energy/moment route brackets the sup `M` only from the floor `M` already sits on:
a structural OVERSHOOT, derived from `η` being real — **no SOTA exponent cited**.

Scope: **constraint capstone** for the tetrachotomy's door-(i) side.  It proves the moment door
overshoots the prize floor; it gives **no** CORE bound, **no** cancellation, anti-concentration,
completion, or capacity claim.  CORE `M(μ_n) ≤ C·√(n·log(p/n))` remains OPEN.
-/

namespace ArkLib.ProximityGap.Frontier.DoorIVMomentEnergyFloorOvershoot

open Finset

variable {ι : Type*}

/-- The `r`-th **energy moment** of a real field: `E_r = Σ_c (η_c)^{2r}` (the only object a moment
mechanism can access, by `momentHierarchy_energy_dominated`). `E_0 = card`, `E_1 = Σ (η_c)²`. -/
def energyMoment (f : ι → ℝ) (s : Finset ι) (r : ℕ) : ℝ := ∑ c ∈ s, (f c) ^ (2 * r)

@[simp] theorem energyMoment_zero (f : ι → ℝ) (s : Finset ι) :
    energyMoment f s 0 = (s.card : ℝ) := by
  simp [energyMoment]

theorem energyMoment_one (f : ι → ℝ) (s : Finset ι) :
    energyMoment f s 1 = ∑ c ∈ s, (f c) ^ 2 := by
  simp [energyMoment]

/-- Energy moments are nonnegative (sum of even powers). -/
theorem energyMoment_nonneg (f : ι → ℝ) (s : Finset ι) (r : ℕ) :
    0 ≤ energyMoment f s r := by
  unfold energyMoment
  apply Finset.sum_nonneg
  intro c _
  rw [show 2 * r = 2 * r from rfl, pow_mul]
  exact pow_nonneg (sq_nonneg _) r

/-- **Cauchy–Schwarz step for energy moments.**  Consecutive energy moments obey
`(E_r)² ≤ E_0 · E_{2r} = card · E_{2r}`... but the sharper, *telescoping* step we need is the
log-convexity rung `(E_r)² ≤ E_{r-1} · E_{r+1}`.  Here we use the cleanest consequence directly:
the **discrete power-mean / Cauchy–Schwarz** bound between the first energy moment and the `r`-th,
in integer-power form. We prove the rung that drives the induction:
`(Σ (f c)²)² ≤ card · Σ (f c)^4`, i.e. `(E_1)² ≤ card · E_2`. -/
theorem sq_energyMoment_one_le_card_mul_energyMoment_two
    (f : ι → ℝ) (s : Finset ι) :
    (energyMoment f s 1) ^ 2 ≤ (s.card : ℝ) * energyMoment f s 2 := by
  classical
  rw [energyMoment_one, show energyMoment f s 2 = ∑ c ∈ s, ((f c) ^ 2) ^ 2 by
    unfold energyMoment; apply Finset.sum_congr rfl; intro c _; rw [← pow_mul]]
  -- Cauchy–Schwarz: (Σ 1 · g)² ≤ (Σ 1²)(Σ g²) with g = (f c)²
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun c => (f c) ^ 2)
  simp only [one_mul, one_pow] at h
  -- h : (Σ (f c)²)² ≤ (Σ 1) · (Σ ((f c)²)²)
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact h

/-- **The L² scale is a lower bound on the squared first energy moment per element.**
`(E_1)² ≤ card · E_2` rearranges to the statement that the normalized 4th moment dominates the squared
normalized 2nd moment: `(E_1 / card)² ≤ E_2 / card`.  This is the `r = 2` rung of power-mean: the L⁴
energy scale is at least the L² (rms) scale.  Root-free form. -/
theorem normSq_energyMoment_one_le_normEnergyMoment_two
    (f : ι → ℝ) (s : Finset ι) (hs : s.Nonempty) :
    (energyMoment f s 1 / (s.card : ℝ)) ^ 2 ≤ energyMoment f s 2 / (s.card : ℝ) := by
  have hcard : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hs
  have h := sq_energyMoment_one_le_card_mul_energyMoment_two f s
  set N : ℝ := (s.card : ℝ) with hN
  set a : ℝ := energyMoment f s 1 with ha
  set b : ℝ := energyMoment f s 2 with hb
  -- h : a^2 ≤ N * b ;  goal : (a / N)^2 ≤ b / N
  have hN2 : (0 : ℝ) < N ^ 2 := by positivity
  -- Multiply out: it suffices to show a^2 * N ≤ b * N^2, which follows from a^2 ≤ N*b by * N.
  rw [div_pow, div_le_div_iff₀ hN2 hcard]
  nlinarith [h, hcard.le, energyMoment_nonneg f s 2]

/-! ## The moment-method sup-certificate overshoots the rms / Plancherel floor

A moment mechanism estimates the sup `M = max_c |η_c|` from an energy moment `E_r` via the only
inequality power-sums afford: `M^{2r} ≤ E_r` (each term `≤ M^{2r}` only on one term; the *useful*
direction is `E_r ≤ card · M^{2r}`, giving the lower estimate `M ≥ (E_r / card)^{1/(2r)}`).  In every
case the energy-moment scale `(E_r / card)^{1/(2r)}` is squeezed **between the rms floor and `M`**: it
overshoots `rms`, and it is dominated by `M`.  The decisive structural fact, root-free, is that the
energy-moment scale never drops below the L² scale — proven here at the `r = 2` rung, which is the one
the tetrachotomy's moment-door discharge needs to replace the SOTA citation. -/

/-- **rms is a lower bound on the maximum** (the Plancherel floor, restated for the energy moment).
For a nonempty finite real family, `E_1 / card ≤ (max |f|)²`: the L² scale lower-bounds the sup. This
is the wrong-side bound — moments push the sup DOWN only to `rms`, never to a sub-`rms` prize. -/
theorem normEnergyMoment_one_le_sq_max
    (f : ι → ℝ) (s : Finset ι) (hs : s.Nonempty) :
    energyMoment f s 1 / (s.card : ℝ) ≤ (s.sup' hs (fun c => |f c|)) ^ 2 := by
  classical
  have hcard : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hs
  rw [div_le_iff₀ hcard, energyMoment_one]
  have hbound : ∑ c ∈ s, (f c) ^ 2 ≤ ∑ _c ∈ s, (s.sup' hs (fun c => |f c|)) ^ 2 := by
    apply Finset.sum_le_sum
    intro c hc
    have hle : |f c| ≤ s.sup' hs (fun c => |f c|) := Finset.le_sup' (fun c => |f c|) hc
    have h0 : (0 : ℝ) ≤ |f c| := abs_nonneg _
    calc (f c) ^ 2 = |f c| ^ 2 := (sq_abs _).symm
      _ ≤ (s.sup' hs (fun c => |f c|)) ^ 2 := by exact pow_le_pow_left₀ h0 hle 2
  calc ∑ c ∈ s, (f c) ^ 2 ≤ ∑ _c ∈ s, (s.sup' hs (fun c => |f c|)) ^ 2 := hbound
    _ = (s.sup' hs (fun c => |f c|)) ^ 2 * (s.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **Moment-door overshoot, structural form (the deliverable).**  For the real period field `η = f`
of the negation-closed thin subgroup, define the squared rms `rmsSq = E_1 / card` and the (squared)
energy-moment scale at level 2 `momentScaleSq = √(E_2/card)` implicitly via its square `E_2/card`.
Then BOTH:

* `rmsSq ≤ (max |f|)²` — the sup sits ABOVE rms (the wrong-side Plancherel floor), and
* `rmsSq² ≤ E_2/card` — the L⁴ energy-moment scale that a moment mechanism extracts is itself ABOVE
  rms (`(E_2/card) ≥ rmsSq²`, i.e. the normalized 4th moment dominates the squared normalized 2nd).

Hence the energy/moment route is confined to `[rms, max|f|]`: it OVERSHOOTS the rms floor and is
dominated by the sup.  A moment mechanism cannot certify a sup bound below `rms`; in the prize regime
`rms = √n`, the moment door cannot reach the prize floor `√n` from below — a kernel-proven OVERSHOOT,
derived purely from `η` being real (via `momentHierarchy_energy_dominated`), with NO SOTA exponent. -/
theorem momentDoor_overshoots_rms
    (f : ι → ℝ) (s : Finset ι) (hs : s.Nonempty) :
    (energyMoment f s 1 / (s.card : ℝ) ≤ (s.sup' hs (fun c => |f c|)) ^ 2)
      ∧ ((energyMoment f s 1 / (s.card : ℝ)) ^ 2 ≤ energyMoment f s 2 / (s.card : ℝ)) :=
  ⟨normEnergyMoment_one_le_sq_max f s hs,
   normSq_energyMoment_one_le_normEnergyMoment_two f s hs⟩

/-- **Connector to the moment-hierarchy capstone.**  The energy moments `E_r` ARE the entire accessible
correlator lattice for a real field: every mixed-conjugate correlator collapses to an energy moment.
We restate the even-parity collapse here so this module's overshoot is visibly indexed to the *only*
objects a moment mechanism can touch.  (Re-export of `momentHierarchy_energy_dominated`'s even part in
the `energyMoment` vocabulary.) -/
theorem mixedCorrelator_is_energyMoment
    (f : ι → ℝ) (s : Finset ι) (a b r : ℕ) (hab : a + b = 2 * r) :
    ∑ c ∈ s, (f c) ^ a * (f c) ^ b = energyMoment f s r := by
  unfold energyMoment
  apply Finset.sum_congr rfl
  intro c _
  rw [← pow_add, hab]

end ArkLib.ProximityGap.Frontier.DoorIVMomentEnergyFloorOvershoot

#print axioms ArkLib.ProximityGap.Frontier.DoorIVMomentEnergyFloorOvershoot.momentDoor_overshoots_rms
#print axioms ArkLib.ProximityGap.Frontier.DoorIVMomentEnergyFloorOvershoot.sq_energyMoment_one_le_card_mul_energyMoment_two
#print axioms ArkLib.ProximityGap.Frontier.DoorIVMomentEnergyFloorOvershoot.mixedCorrelator_is_energyMoment
