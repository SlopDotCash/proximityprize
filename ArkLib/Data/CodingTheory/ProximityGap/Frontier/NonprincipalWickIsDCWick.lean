/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCSubtractedMoment
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.DCWickMGFFromTermwise

/-!
# The nonprincipal even-moment bound IS `DCWickBound` (#444 — moment-route ⟷ DC-Wick weld)

A live measurement round (#444, exact Rust on the *nonprincipal* moment) found that the quantity
actually controlling `M(n) = max_{b≠0}‖η_b‖` is

> `E_r' := (1/q) · ∑_{b≠0} ‖η_b‖^{2r}`,

and that **`E_r' ≤ (2r−1)‼·n^r` holds empirically for all tested `r`** (ratio `≤ 0.06 < 1`, even past
char-0 faithfulness `r > β`) — reconciling the earlier "deep moment FALSE" framing, which had been
measuring the *principal-contaminated* full moment `E_r` (the `b=0`/DC term `n^{2r}/q` is what blows up
once `r > β`, not the nonprincipal spectrum). So "M1's sufficient lemma" (the nonprincipal even-moment
Wick bound) is the live, empirically-validated reduction target.

This file proves, axiom-clean, that this nonprincipal Wick bound is **exactly** the in-tree open crux
`DCWickBound` — no new object. The bridge is purely the already-proven DC-subtracted moment identity
`sum_nonzero_moment` (`∑_{b≠0}‖η_b‖^{2r} = q·E_r − n^{2r}`):

* `NonprincipalWickBound ψ G r` := `∑_{b≠0} ‖η_b‖^{2r} ≤ q·(2r−1)‼·n^r` — the live measurement's
  inequality (the `K = 1` form; `E_r' ≤ (2r−1)‼·n^r` after dividing by `q`).
* `nonprincipalWick_iff_dcWick` — `NonprincipalWickBound ψ G r ↔ DCWickBound G r`. The two are the
  SAME inequality: substitute `∑_{b≠0} = q·E_r − n^{2r}` on the left. So the "moment route" the
  measurement opened and the DC-Wick spine target are one open inequality, not two.
* `eta_pow_le_of_nonprincipalWick` — the consequence the measurement uses: under the nonprincipal Wick
  bound, every `b≠0` period satisfies `‖η_b‖^{2r} ≤ q·(2r−1)‼·n^r`, so `M(n)^{2r} ≤` that — the sup
  transfer (a single nonprincipal term ≤ the nonprincipal sum, capped by the hypothesis).

**Honesty.** This is a definitional weld, not progress on the inequality itself: the open content is
still the char-`p` `∀r` DC-Wick / nonprincipal Wick bound at depth `r ≈ log q` with an ABSOLUTE
constant (the measurement's `K_eff(n)` drifting `0.55 → 0.66` for `n = 16 → 64` is the open
`K^r`-slack the prize needs to pin as `n → 2³⁰`). This file removes a duplication risk — the fleet
should treat the new "nonprincipal moment route" and `DCWickBound` as the same target. CORE
(`M(μ_n) ≤ C·√(n·log(p/n))`) stays OPEN.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCSubtractedMoment

namespace ProximityGap.Frontier.NonprincipalWickIsDCWick

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The nonprincipal even-moment Wick bound** (the live measurement's "M1 sufficient lemma", `K=1`
form): the total non-`DC` even moment is at most the raw Wick ceiling `q·(2r−1)‼·n^r`. Dividing by `q`
this is `E_r' = (1/q)∑_{b≠0}‖η_b‖^{2r} ≤ (2r−1)‼·n^r`, the quantity measured sub-char-0. -/
def NonprincipalWickBound (ψ : AddChar F ℂ) (G : Finset F) (r : ℕ) : Prop :=
  ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r)
    ≤ (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)

/-- **The weld: nonprincipal Wick bound ↔ `DCWickBound`.** The two open inequalities are literally the
same, via the in-tree DC-subtracted moment identity `∑_{b≠0}‖η_b‖^{2r} = q·E_r − n^{2r}`. So the live
"moment route" target and the DC-Wick spine's open crux are one inequality. -/
theorem nonprincipalWick_iff_dcWick {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) :
    NonprincipalWickBound ψ G r ↔ ProximityGap.Frontier.DCWickMGFFromTermwise.DCWickBound G r := by
  unfold NonprincipalWickBound ProximityGap.Frontier.DCWickMGFFromTermwise.DCWickBound
  rw [sum_nonzero_moment hψ G r]

/-- **`GaussianEnergyBound ⟹ NonprincipalWickBound`** (the raw Wick bound implies the nonprincipal
one, since the latter is the DC-weaker object). Routes through the in-tree `dcWick_of_gaussianEnergyBound`. -/
theorem nonprincipalWick_of_gaussianEnergyBound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    {r : ℕ} (h : ArkLib.ProximityGap.GaussPeriodMomentBound.GaussianEnergyBound G r) :
    NonprincipalWickBound ψ G r :=
  (nonprincipalWick_iff_dcWick hψ G r).mpr
    (ProximityGap.Frontier.DCWickMGFFromTermwise.dcWick_of_gaussianEnergyBound h)

/-- **Sup transfer from the nonprincipal Wick bound.** Under `NonprincipalWickBound`, every
non-trivial period satisfies `‖η_b‖^{2r} ≤ q·(2r−1)‼·n^r` (a single nonprincipal term is at most the
nonprincipal sum, which the bound caps at `q·Wick`), hence `M(n)^{2r} = max_{b≠0}‖η_b‖^{2r} ≤` it.
This is the moment→sup step the measurement invokes.

Honest note: under this (DC-weaker, SATISFIABLE-at-the-prize) hypothesis we get the clean `q·Wick`
bound, NOT the strictly-sharper `q·Wick − n^{2r}` of `DCMomentSupBound.eta_pow_le_dc_of_energyBound` —
that sharper form needs the RAW `GaussianEnergyBound` (`E_r ≤ Wick`), which is FALSE at the prize (its
DC term blows up past `r > β`). Trading the `−n^{2r}` sharpening for a satisfiable hypothesis is the
entire point of the nonprincipal/DC route. -/
theorem eta_pow_le_of_nonprincipalWick {ψ : AddChar F ℂ} {G : Finset F} {r : ℕ}
    (h : NonprincipalWickBound ψ G r) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by
  -- single nonprincipal term ≤ the nonprincipal sum ≤ q·Wick (the hypothesis)
  have hterm : ‖eta ψ G b‖ ^ (2 * r) ≤ ∑ b' ∈ univ.erase (0 : F), ‖eta ψ G b'‖ ^ (2 * r) := by
    apply Finset.single_le_sum (f := fun b' => ‖eta ψ G b'‖ ^ (2 * r))
    · intro i _; positivity
    · exact Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b⟩
  exact hterm.trans h

end ProximityGap.Frontier.NonprincipalWickIsDCWick

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.NonprincipalWickIsDCWick.nonprincipalWick_iff_dcWick
#print axioms ProximityGap.Frontier.NonprincipalWickIsDCWick.nonprincipalWick_of_gaussianEnergyBound
#print axioms ProximityGap.Frontier.NonprincipalWickIsDCWick.eta_pow_le_of_nonprincipalWick
