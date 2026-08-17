/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCSubtractedMoment
import ArkLib.Data.CodingTheory.ProximityGap.DCEnergyCorrection

/-!
# Cross-form bridge: DC-subtracted energy ⟺ signed-deep-cancellation (#464)

**The wall has ≥6 kernel-equivalent incarnations.** Several pairwise equivalences are already
in-tree (`_EnergyRatioMonotoneReduction`: `ERM-at-r ⟺ M² ≤ (2r+1)·n`). This file banks a NEW
propositional equivalence between two of those forms whose `↔` was **not** yet an in-tree theorem:

* **Form A′ — DC-subtracted energy** (`DCEnergyCorrection.DCEnergyBound G r`):
  `q·E_r(G) − |G|^{2r} ≤ q·(2r−1)‼·|G|^r`   (the prize hypothesis `A_r ≤ Wick`, cleared of division;
  the canonical DC-subtracted statement, TRUE at the prize where raw `E_r ≤ Wick` is FALSE).

* **Form S — signed-deep-cancellation** (`SignedDeepCancellation`):
  `∑_{b≠0} ‖η_b‖^{2r} ≤ q·(2r−1)‼·|G|^r`   (the explicit sum of `2r`-th powers of the *nonzero* Gauss
  periods is at most the Wick value — i.e. the deep `±1`-relation/`2^μ`-root cancellation sum stays
  Wick-like; this is the form in which the wall reads as "short signed sums of roots of unity vanish
  mod p only at the Gaussian rate").

These two named `Prop`s are about *different objects* — Form A′ is a statement about the additive
energy `E_r = rEnergy G r` (a global combinatorial count, DC-included, then DC-corrected by hand),
Form S is a statement about the *explicit Fourier sum* `∑_{b≠0}‖η_b‖^{2r}` over the nonzero
frequencies. The bridge is **exactly propositional equivalence**, on the nose:

  **`dcEnergyBound_iff_signedDeepCancellation`**  (axiom-clean, primitive `ψ`):
  `DCEnergyBound G r  ↔  SignedDeepCancellation ψ G r`.

**Why this is genuinely new and not a restatement.** The in-tree `DCSubtractedMoment.sum_nonzero_moment`
proves the *identity* `∑_{b≠0}‖η_b‖^{2r} = q·E_r − |G|^{2r}` (an equality of reals), and
`DCEnergyCorrection.eta_pow_le_of_dcEnergyBound` proves the *one-directional* consequence
`Form A′ ⟹ per-frequency bound`. Neither asserts the *bi-conditional between the two thresholded
forms*. This file closes that loop: it shows the two attack surfaces are not merely "morally the same"
but **literally the same `Prop`**, so a proof on either surface is a proof on the other — and, crucially,
it pins which constant (`q·Wick`) is shared. This is the kind of structural fact the dossier calls a
"reduction / equivalence first": it removes the need to ever re-prove the DC bookkeeping when working
on the explicit-sum (signed-cancellation) face.

**Status.** The bridge is PROVEN axiom-clean. The wall itself stays open: *either* form holding at
depth `r ≈ ln q` for the prize `μ_n` is the BGK/Paley √-cancellation. The bridge BANKS structure,
it does not move the wall.

Issue #464 (successor of #444 / #334).
-/

set_option autoImplicit false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy)
open ArkLib.ProximityGap.DCSubtractedMoment (sum_nonzero_moment)
open ArkLib.ProximityGap.DCEnergyCorrection (DCEnergyBound)

namespace ProximityGap.Frontier.AssaultV2.CrossFormBridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Form S — the signed-deep-cancellation form.** The sum of `2r`-th powers of the *nonzero*
(`b ≠ 0`, DC-removed) Gauss periods is at most the Wick value `q·(2r−1)‼·|G|^r`. This is the form in
which the wall reads as a deep `±1`-cancellation of `2^μ`-th roots of unity: `∑_{b≠0}‖η_b‖^{2r}`
counts the signed depth-`r` relations, and "≤ Wick" says they vanish mod `p` only at the Gaussian
rate. Distinct object from `DCEnergyBound` (which is phrased on the energy `E_r`); the bridge below
proves they are the same `Prop`. -/
def SignedDeepCancellation (ψ : AddChar F ℂ) (G : Finset F) (r : ℕ) : Prop :=
  ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r)
    ≤ (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)

/-- **The cross-form bridge (NEW, axiom-clean).** The DC-subtracted *energy* form and the
signed-deep-cancellation *explicit-Fourier-sum* form are propositionally equivalent, sharing the
exact constant `q·(2r−1)‼·|G|^r`:

  `DCEnergyBound G r  ↔  SignedDeepCancellation ψ G r`.

Proof: rewrite the nonzero-frequency power sum to `q·E_r − |G|^{2r}` via the in-tree DC-subtracted
moment identity (`sum_nonzero_moment`), which is *exactly* the left-hand side of `DCEnergyBound`. The
two thresholds are then literally the same inequality. -/
theorem dcEnergyBound_iff_signedDeepCancellation
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) :
    DCEnergyBound G r ↔ SignedDeepCancellation ψ G r := by
  unfold DCEnergyBound SignedDeepCancellation
  rw [sum_nonzero_moment hψ G r]

/-- **Convenience forward consumer.** From the signed-deep-cancellation form one recovers the
DC-subtracted energy bound (the canonical prize hypothesis), hence everything downstream of
`DCEnergyBound` (e.g. `eta_pow_le_of_dcEnergyBound`). This is the practically useful direction: a
proof attempted on the explicit-sum face transports verbatim to the energy face. -/
theorem dcEnergyBound_of_signedDeepCancellation
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {r : ℕ}
    (h : SignedDeepCancellation ψ G r) : DCEnergyBound G r :=
  (dcEnergyBound_iff_signedDeepCancellation hψ G r).mpr h

/-- **Reverse consumer.** From the DC-subtracted energy bound one recovers the signed-cancellation
form. Together with `dcEnergyBound_of_signedDeepCancellation` this records that the two forms are
fully interchangeable as the prize input. -/
theorem signedDeepCancellation_of_dcEnergyBound
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {r : ℕ}
    (h : DCEnergyBound G r) : SignedDeepCancellation ψ G r :=
  (dcEnergyBound_iff_signedDeepCancellation hψ G r).mp h

/-- **The per-frequency consequence, routed through Form S.** Banking the bridge end-to-end: from the
signed-deep-cancellation form, every nonzero Gauss period obeys `‖η_b‖^{2r} ≤ q·(2r−1)‼·|G|^r`. This
is `DCEnergyCorrection.eta_pow_le_of_dcEnergyBound` pulled back across the new equivalence, confirming
the bridge is consumer-compatible with the existing substrate (no re-derivation of the DC bookkeeping
on the explicit-sum face). -/
theorem eta_pow_le_of_signedDeepCancellation
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {r : ℕ}
    (h : SignedDeepCancellation ψ G r) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) :=
  ArkLib.ProximityGap.DCEnergyCorrection.eta_pow_le_of_dcEnergyBound hψ
    (dcEnergyBound_of_signedDeepCancellation hψ h) hb

end ProximityGap.Frontier.AssaultV2.CrossFormBridge

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.AssaultV2.CrossFormBridge.dcEnergyBound_iff_signedDeepCancellation
#print axioms ProximityGap.Frontier.AssaultV2.CrossFormBridge.dcEnergyBound_of_signedDeepCancellation
#print axioms ProximityGap.Frontier.AssaultV2.CrossFormBridge.signedDeepCancellation_of_dcEnergyBound
#print axioms ProximityGap.Frontier.AssaultV2.CrossFormBridge.eta_pow_le_of_signedDeepCancellation
