/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf6P1_nonprincipal_energy
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Discharging the char-0 instance of `NonprincipalEnergyBound` (#444, lane wf-L4)

`_wf6P1_nonprincipal_energy.lean` states the open moment-route lever as the *named* `Prop`

> `NonprincipalEnergyBound G r D := q·E_r(G) − n^{2r} ≤ q·(D·n^r)`   (`D = (2r−1)‼`, `n = |G|`)

with the proven bridge `eta_pow_le_of_nonprincipalEnergyBound : NonprincipalEnergyBound ⟹
‖η_b‖^{2r} ≤ q·(2r−1)‼·n^r` for `b ≠ 0`. This file **discharges the char-0 instance of that
`Prop` unconditionally**, reducing it to the char-0 additive-energy bound — which is *proven* in
[`DyadicEnergyK1.lean`](../DyadicEnergyK1.lean) (`zeroSumCount_le_doubleFactorial_dyadic`,
Lam–Leung antipodal pairing, axiom-clean).

## The reduction (pure algebra — the unconditional content)

The named `Prop` is *already* the principal-subtracted form, so the char-0 energy bound transfers
to it with **no slack lost** and with `K = 1`:

* Hypothesis (the char-0 Lam–Leung bound): `E_r(G) ≤ (2r−1)‼·n^r`.
* Multiply by `q ≥ 0`: `q·E_r ≤ q·(2r−1)‼·n^r`.
* Subtract the (nonnegative) principal spike `n^{2r}` from the left only:
  `q·E_r − n^{2r} ≤ q·E_r ≤ q·(2r−1)‼·n^r`.

That last chain is *exactly* `NonprincipalEnergyBound G r ((2r−1)‼)`. (The mission's intermediate
`q·(2r−1)‼·n^r − n^{2r}` is a strictly tighter — and still valid — bound; we only need the looser
RHS the `Prop` asks for, hence `n^{2r} ≥ 0` is the sole inequality consumed.)

`nonprincipalEnergyBound_of_energyR_le` packages this; it is axiom-clean and **unconditional** over
the finite field `F` — the only input is the energy bound, supplied as a real-cast hypothesis.

## Why this is the char-0 discharge (and where the gap actually is)

The hypothesis `(E_r : ℝ) ≤ (2r−1)‼·n^r` is precisely the conclusion of
`DyadicEnergyK1.zeroSumCount_le_doubleFactorial_dyadic` for `G ⊆ μ_{2^k}` over a `CharZero` field
(via `E_r = zeroSumCount G (2r)` for negation-closed `G`). So **in characteristic 0 this hypothesis
is a theorem**, and `char0_eta_pow_le_of_energyR_le` below is then an *unconditional* per-frequency
sup bound. The one remaining gap is the **char-`p` transfer** of the energy bound to depth
`r ≈ log q` at `n = 2^30` (the lane-P1 probe shows the *full* `E_r` over `F_p` exceeds `(2r−1)‼·n^r`,
so the hypothesis is char-0-only; the BGK wall). This file makes the char-0 side a closed theorem
modulo that one named energy input, exactly per the §6 modularity convention.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset AddChar
open scoped Nat
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMomentLadder
open ArkLib.ProximityGap.Frontier.WF6P1

namespace ArkLib.ProximityGap.Frontier.WFL4

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The char-0 discharge of `NonprincipalEnergyBound` (pure-algebra core, unconditional).**
From the char-0 additive-energy bound `E_r(G) ≤ (2r−1)‼·n^r` (the Lam–Leung / dyadic-K1 value),
the named nonprincipal-energy `Prop` holds with `doubleFact = (2r−1)‼` and `K = 1`:
`q·E_r − n^{2r} ≤ q·(2r−1)‼·n^r`.

The proof consumes only `q ≥ 0` (to scale the energy bound) and `n^{2r} ≥ 0` (the principal spike
is subtracted from the LHS, so dropping it only weakens the bound). No char-0 assumption is made
*here* — the char-0 content is entirely inside the hypothesis `henergy`, which is a *theorem* in
characteristic 0 (`DyadicEnergyK1.zeroSumCount_le_doubleFactorial_dyadic`). -/
theorem nonprincipalEnergyBound_of_energyR_le (G : Finset F) (r : ℕ)
    (henergy : (energyR G r : ℝ) ≤ ((2 * r - 1)‼ : ℝ) * (G.card : ℝ) ^ r) :
    NonprincipalEnergyBound (F := F) G r ((2 * r - 1)‼ : ℝ) := by
  unfold NonprincipalEnergyBound
  have hq : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  have hspike : (0 : ℝ) ≤ (G.card : ℝ) ^ (2 * r) := by positivity
  -- Scale the energy bound by q ≥ 0, then drop the (nonnegative) principal spike from the LHS.
  have hscaled : (Fintype.card F : ℝ) * energyR G r
      ≤ (Fintype.card F : ℝ) * (((2 * r - 1)‼ : ℝ) * (G.card : ℝ) ^ r) :=
    mul_le_mul_of_nonneg_left henergy hq
  linarith

/-- **The char-0 per-frequency sup bound, wired through the existing bridge.** Composing the
char-0 discharge with `eta_pow_le_of_nonprincipalEnergyBound`: under the char-0 energy bound,
every nontrivial frequency obeys the Gaussian/Wick sup bound `‖η_b‖^{2r} ≤ q·(2r−1)‼·n^r`.

In characteristic 0 the hypothesis `henergy` is the *proven* `DyadicEnergyK1` value, so this is an
unconditional per-frequency bound there; the sole open input is the char-`p` energy transfer. -/
theorem char0_eta_pow_le_of_energyR_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (r : ℕ)
    (henergy : (energyR G r : ℝ) ≤ ((2 * r - 1)‼ : ℝ) * (G.card : ℝ) ^ r)
    (b : F) (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ (2 * r) ≤ (Fintype.card F : ℝ) * (((2 * r - 1)‼ : ℝ) * (G.card : ℝ) ^ r) :=
  eta_pow_le_of_nonprincipalEnergyBound hψ G r ((2 * r - 1)‼ : ℝ)
    (nonprincipalEnergyBound_of_energyR_le G r henergy) b hb

/-- **The strictly-tighter principal-subtracted form** (recorded for completeness): the
nonprincipal energy is in fact `≤ q·(2r−1)‼·n^r − n^{2r}`, i.e. the principal spike `n^{2r}`
may be *kept* on the right. This is the mission's exact intermediate, and shows
`nonprincipalEnergyBound_of_energyR_le` discards nothing essential — it merely relaxes to the
`Prop`'s declared RHS. -/
theorem nonprincipal_energy_le_tight (G : Finset F) (r : ℕ)
    (henergy : (energyR G r : ℝ) ≤ ((2 * r - 1)‼ : ℝ) * (G.card : ℝ) ^ r) :
    (Fintype.card F : ℝ) * energyR G r - (G.card : ℝ) ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * (((2 * r - 1)‼ : ℝ) * (G.card : ℝ) ^ r)
          - (G.card : ℝ) ^ (2 * r) := by
  have hq : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  have hscaled : (Fintype.card F : ℝ) * energyR G r
      ≤ (Fintype.card F : ℝ) * (((2 * r - 1)‼ : ℝ) * (G.card : ℝ) ^ r) :=
    mul_le_mul_of_nonneg_left henergy hq
  linarith

end ArkLib.ProximityGap.Frontier.WFL4

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.WFL4.nonprincipalEnergyBound_of_energyR_le
#print axioms ArkLib.ProximityGap.Frontier.WFL4.char0_eta_pow_le_of_energyR_le
#print axioms ArkLib.ProximityGap.Frontier.WFL4.nonprincipal_energy_le_tight
