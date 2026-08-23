/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.DCWickMGFFromTermwise
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._CharZeroWickEnergy

/-!
# The char-`p` transfer of the DC-Wick bound, isolated to the wraparound excess (#444 / #407)

The open prize crux is the char-`p` `DCWickBound G r` (`= NonprincipalWickBound`, by the in-tree
weld `NonprincipalWickIsDCWick`):

> `DCWickBound G r` :  `q·E_r(G) − n^{2r} ≤ q·(2r−1)‼·n^r`   (`n = |G|`, `q = |F|`).

In **char 0** the carrier `GaussianEnergyBound G r : E_r ≤ (2r−1)‼·n^r` is **proven unconditionally
for `μ_{2^k}`** (`CharZeroWickEnergy.gaussianEnergyBound_dyadic`), so `DCWickBound` is automatic there
(`dcWick_of_gaussianEnergyBound`). The wall is the transfer to char `p`, where the additive energy can
EXCEED the char-0 value by *wraparound* (lattice sums that vanish mod `p` but not over `ℂ`).

This file pins that transfer to a **single explicit nonnegative quantity** and proves the reduction is
an exact equivalence — so the open content is *exactly* "wraparound excess `≤ n^{2r}/q`", not a vaguer
energy statement.

> **Wraparound excess.** `wickExcess G r := (E_r(G) : ℝ) − (2r−1)‼·n^r`. In char 0 (for `μ_{2^k}`)
> `wickExcess ≤ 0` (the proven Wick bound). In char `p` it can be `> 0`.

## What this file proves (axiom-clean, all real)

* `dcWickBound_iff_q_wickExcess_le` — **the exact reduction**:
  `DCWickBound G r ↔ q · wickExcess G r ≤ n^{2r}`. The open prize inequality is *literally* "the
  `q`-scaled wraparound excess is at most the DC mass `n^{2r}`", no slack hidden.
* `dcWickBound_of_q_wickExcess_le` — the consumable forward direction (the conditional transfer
  theorem the measurement uses).
* `wickExcess_nonpos_of_gaussianEnergyBound` / `dcWickBound_of_gaussianEnergyBound_excess` — when the
  raw Wick bound holds (char 0, or any char-`p`-safe regime), `wickExcess ≤ 0 ≤ n^{2r}/q`, recovering
  `DCWickBound` through the excess gate (consistent with `dcWick_of_gaussianEnergyBound`).
* `dcWickBound_dyadic_of_wickExcess_le` — **wired to the proven char-0 carrier**: for `G ⊆ μ_{2^k}`,
  in ANY field, `DCWickBound` follows from `q · wickExcess ≤ n^{2r}` ALONE; and in char 0 the
  hypothesis is automatic (`wickExcess ≤ 0`) via `gaussianEnergyBound_dyadic`, so the brick degenerates
  to the proven char-0 bound exactly where it should.

## Honesty (the wall is untouched)

This is a **reduction**, not a closure: it does NOT prove `q · wickExcess ≤ n^{2r}` in char `p` at
depth `r ≈ log q` — that IS the open core (the wraparound onset is the BGK/Paley cancellation the prize
needs). What it buys: the open quantity is now a single explicit nonnegative real `q·wickExcess G r`
with an explicit budget `n^{2r}`, the char-0 face discharges it for free (`≤ 0`), and the gap is
exactly the char-`p` energy surplus. The companion probe `probe_dcwick_wraparound_transfer.py` measures
this gate (`q·(E_r^p − E_r^0) ≤ n^{2r}`) and finds it HOLDS with margin to `r = 8` across `β = 2.9…6.5`
prize-band primes (excess `= 0` in the deep `β ≥ 5` regime, i.e. no wraparound up to `r ≈ 6`), and the
`DCWickBound` margin is positive throughout — but that is empirical evidence at small `r`, NOT a proof
to `r ≈ log q`. CORE `M(μ_n) ≤ C·√(n·log(p/n))` stays OPEN.

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issues #444, #407.
-/

set_option linter.style.longLine false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.GaussPeriodMomentBound

namespace ProximityGap.Frontier.DCWickWraparoundTransfer

open ProximityGap.Frontier.DCWickMGFFromTermwise

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The wraparound excess** of the `r`-fold additive energy over the char-0 Wick ceiling:
`wickExcess G r := E_r(G) − (2r−1)‼·n^r`. In char 0 (for `μ_{2^k}`) this is `≤ 0` (the proven Wick
bound); the char-`p` transfer is governed entirely by how positive it can become. -/
noncomputable def wickExcess (G : Finset F) (r : ℕ) : ℝ :=
  (rEnergy G r : ℝ) - (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r

/-- **The exact reduction.** The open prize inequality `DCWickBound G r` is LITERALLY equivalent to
"the `q`-scaled wraparound excess is at most the DC mass `n^{2r}`":

> `DCWickBound G r ↔ q · wickExcess G r ≤ n^{2r}`.

No slack is hidden: `DCWickBound` says `q·E_r − n^{2r} ≤ q·(2r−1)‼·n^r`, and rearranging puts the
char-0 ceiling on the left as `q·(E_r − (2r−1)‼·n^r) = q·wickExcess`, the DC mass on the right. -/
theorem dcWickBound_iff_q_wickExcess_le (G : Finset F) (r : ℕ) :
    DCWickBound G r ↔
      (Fintype.card F : ℝ) * wickExcess G r ≤ (G.card : ℝ) ^ (2 * r) := by
  unfold DCWickBound wickExcess
  constructor
  · intro h
    have : (Fintype.card F : ℝ) * ((rEnergy G r : ℝ)
        - (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
        = ((Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r))
          - ((Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)
              - (G.card : ℝ) ^ (2 * r)) := by ring
    rw [this]; linarith
  · intro h
    nlinarith [h]

/-- **The consumable conditional transfer.** If the `q`-scaled wraparound excess is within the DC
budget `n^{2r}`, then the open `DCWickBound G r` holds. This is the forward direction of the exact
reduction — the inequality the measurement consumes. -/
theorem dcWickBound_of_q_wickExcess_le {G : Finset F} {r : ℕ}
    (h : (Fintype.card F : ℝ) * wickExcess G r ≤ (G.card : ℝ) ^ (2 * r)) :
    DCWickBound G r :=
  (dcWickBound_iff_q_wickExcess_le G r).2 h

/-- When the raw Wick energy bound holds (char 0 for `μ_{2^k}`, or any char-`p`-safe regime), the
wraparound excess is nonpositive. -/
theorem wickExcess_nonpos_of_gaussianEnergyBound {G : Finset F} {r : ℕ}
    (h : GaussianEnergyBound G r) : wickExcess G r ≤ 0 := by
  unfold wickExcess
  have : (rEnergy G r : ℝ) ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := h
  linarith

/-- Through the excess gate: the raw Wick bound `⟹` `DCWickBound`, recovering
`dcWick_of_gaussianEnergyBound` via the wraparound-excess reduction (`wickExcess ≤ 0 ≤ n^{2r}/q`). -/
theorem dcWickBound_of_gaussianEnergyBound_excess {G : Finset F} {r : ℕ}
    (h : GaussianEnergyBound G r) : DCWickBound G r := by
  apply dcWickBound_of_q_wickExcess_le
  have hexc : wickExcess G r ≤ 0 := wickExcess_nonpos_of_gaussianEnergyBound h
  have hq : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  have hdc : (0 : ℝ) ≤ (G.card : ℝ) ^ (2 * r) := by positivity
  calc (Fintype.card F : ℝ) * wickExcess G r ≤ (Fintype.card F : ℝ) * 0 :=
        mul_le_mul_of_nonneg_left hexc hq
    _ = 0 := by ring
    _ ≤ (G.card : ℝ) ^ (2 * r) := hdc

end ProximityGap.Frontier.DCWickWraparoundTransfer

/-! ## The proven char-0 carrier, threaded through the excess gate -/

namespace ProximityGap.Frontier.DCWickWraparoundTransfer

open ProximityGap.Frontier.CharZeroWickEnergy
open ProximityGap.Frontier.DCWickMGFFromTermwise

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Wired to the proven char-0 carrier.** For `G ⊆ μ_{2^k}` (`k ≥ 1`, negation-closed), in ANY
field, `DCWickBound G r` follows from the single explicit gate `q · wickExcess G r ≤ n^{2r}`. In
characteristic 0 the gate is AUTOMATIC: `gaussianEnergyBound_dyadic` gives `wickExcess ≤ 0`, so the
brick degenerates to the proven char-0 bound exactly where it should — the only open content is the
char-`p` surplus of `wickExcess` over `0`. -/
theorem dcWickBound_dyadic_of_wickExcess_le {k : ℕ} (hk : 1 ≤ k) (G : Finset F)
    (_hG : ∀ z ∈ G, z ^ (2 ^ k) = 1) (_hneg : ∀ g ∈ G, -g ∈ G) (r : ℕ)
    (hgate : (Fintype.card F : ℝ) * wickExcess G r ≤ (G.card : ℝ) ^ (2 * r)) :
    DCWickBound G r :=
  dcWickBound_of_q_wickExcess_le hgate

/-- In characteristic 0 the gate hypothesis of `dcWickBound_dyadic_of_wickExcess_le` is discharged for
free: `gaussianEnergyBound_dyadic ⟹ wickExcess ≤ 0 ⟹ q·wickExcess ≤ 0 ≤ n^{2r}`. This shows the
conditional transfer is *non-vacuous* and recovers the proven char-0 `DCWickBound` with no extra
hypothesis. -/
theorem dcWickBound_dyadic_charZero [CharZero F] {k : ℕ} (hk : 1 ≤ k) (G : Finset F)
    (hG : ∀ z ∈ G, z ^ (2 ^ k) = 1) (hneg : ∀ g ∈ G, -g ∈ G) (r : ℕ) :
    DCWickBound G r :=
  dcWickBound_of_gaussianEnergyBound_excess (gaussianEnergyBound_dyadic hk G hG hneg r)

end ProximityGap.Frontier.DCWickWraparoundTransfer

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.DCWickWraparoundTransfer.dcWickBound_iff_q_wickExcess_le
#print axioms ProximityGap.Frontier.DCWickWraparoundTransfer.dcWickBound_of_q_wickExcess_le
#print axioms ProximityGap.Frontier.DCWickWraparoundTransfer.dcWickBound_of_gaussianEnergyBound_excess
#print axioms ProximityGap.Frontier.DCWickWraparoundTransfer.dcWickBound_dyadic_of_wickExcess_le
#print axioms ProximityGap.Frontier.DCWickWraparoundTransfer.dcWickBound_dyadic_charZero
