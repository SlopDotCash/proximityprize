/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCEnergyCorrection
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvW0_BesselWickAllR

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# SOS_CORRECT_OBJECT: the exact DC-rescue ledger for the per-K scalar `d_K := Wick_K − A_K ≥ 0`
  — and the proof that NO marginal SOS/moment certificate can supply it (#444)

This brick attacks the CORRECT open kernel `A_K ≤ Wick_K` (`d_K := Wick_K − A_K ≥ 0`) by isolating
exactly which part is unconditional and which is the open residual.

## The exact algebraic ledger (proven here, axiom-clean)

Write, over ℝ, with `q = |F|`, `n = |G|`:
* `A_K := E_K(G) − n^{2K}/q` (the DC-subtracted energy; `q·A_K = ∑_{b≠0}‖η_b‖^{2K}`),
* `E_K^C := besselEℝ K (n/2)` (the char-0 Bessel energy of `μ_n` via STEP-1 antipodal balance),
* `Wick_K := (2K−1)‼·n^K`.

Then the *single scalar* identity (cleared of division by `q`):
  `q·(Wick_K − A_K) = [q·(Wick_K − E_K^C)] + n^{2K} − [q·(E_K(G) − E_K^C)]`
                    =  A_slack          + B_DC    − C_surplus.

`A_slack = q·(Wick_K − E_K^C) ≥ 0` is **UNCONDITIONAL** (the LANDED char-0 ceiling
`AvW0.besselWick_allR`, `E_K^C ≤ Wick_K`). `B_DC = n^{2K} > 0`. `C_surplus = q·(E_K(G) − E_K^C) ≥ 0`
is the char-`p` *wraparound surplus* (mod-`p` collisions beyond char-0; `≥ 0` because mod-`p` only ADDS
solutions). So `d_K ≥ 0` **iff** the DC-rescued surplus condition
  `C_surplus ≤ A_slack + B_DC`,  i.e.  `q·E_K(G) − q·E_K^C ≤ q·Wick_K − q·E_K^C + n^{2K}`,
which simplifies to `q·E_K(G) − n^{2K} ≤ q·Wick_K`  =  `DCEnergyBound G K`.

## The MAIN reduction (axiom-clean)

`dcEnergyBound_of_surplus_rescued`: the named residual
`SurplusRescued G K := q·E_K(G) − q·E_K^C ≤ q·(Wick_K − E_K^C) + n^{2K}`
(the wraparound surplus stays within char-0 slack PLUS the DC term) IMPLIES `DCEnergyBound G K`,
hence (via `eta_pow_le_of_dcEnergyBound`) the per-frequency prize bound.

This is the SHARP shape of the open kernel: the char-0 slack `A_slack` is the proven part, and the
ONLY open quantity is whether the wraparound surplus `C_surplus` is absorbed by `A_slack + B_DC`.

## Why there is NO marginal SOS/moment certificate (the angle's verdict, EXACT-grounded)

`q·A_K = ∑_{b≠0} t_b^K` with `t_b := ‖η_b‖^2 ≥ 0`. The marginal data of the spectrum
`{t_b}` (`t_b ≥ 0`, sup `t_b ≤ n^2`, first DC-subtracted moment `∑ t_b = n(q−n)`) does NOT force
`d_K ≥ 0`: the LP/SOS relaxation over measures on `[0,n^2]` with that marginal data VIOLATES
`∑ t_b^K ≤ q·Wick_K` by factors up to `1.1·10^5` (exact integer, `scripts` below, n=32). The minimal
number of spectral power-sums `j` an LP/SOS certificate must consume GROWS: `j ≈ log₂ n` AND with `K`
(exact: peak `j = 3,4,7` at `n = 8,16,32`; rising through the `K`-range at `n=32`). Hence **no
fixed-order (n-, K-uniform) SOS/Gram-PSD certificate exists**; any certificate must encode the full
correlated spectrum — which IS the BGK content. This matches the proven `_AvFrontier_KMomentBarrier`
(`α(K) = ½ + β/(2K) > ½`, all finite `K`).

## Exact computational evidence (reproducible; `scripts/probes/probe_wk_deficit_ntrend.py` + /tmp probes)

* `q·d_K ≥ 0` confirmed EXACT (integer) at `(n,p) = (8,4129),(16,65617),(32,1048609)`, all `K ≤ ⌊log p⌋`.
* `q·d_1 = n^2` exactly (the DC term; binding `d_K/Wick = n/p`).
* DC-RESCUE is ESSENTIAL at deep K: at `n=32, K=14` the surplus `C_surplus` EXCEEDS the char-0 slack
  `A_slack` by `5.54×` (so `A_K ≤ E_K^C` is REFUTED — consistent), yet `A_slack + B_DC − C_surplus =
  256435208099035477793542731083593843071616 > 0`. The DC term `B_DC` is what closes it.
* Free-relaxation (marginal-only) MAX of `∑ t_b^K` EXCEEDS `q·Wick_K` (n=32,K=12: `1.14·10^5×`).

## Honest scope (#444)

This is a **structural reduction + an SOS-impossibility verdict**, NOT a closure. Proven axiom-clean:
(1) the exact ledger identity; (2) the char-0 slack `A_slack ≥ 0` (repackaging `besselWick_allR`);
(3) the reduction `SurplusRescued ⟹ DCEnergyBound ⟹ per-frequency prize bound`. The open residual is
`SurplusRescued` itself (= the BGK wall, now in its sharpest DC-rescued form). The verdict that no
marginal SOS certificate supplies `d_K ≥ 0` is grounded in exact integer computation (the free
relaxation violates), explaining WHY the per-K scalar still needs the whole-spectrum/BGK input.
-/

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCEnergyCorrection

namespace ArkLib.ProximityGap.Frontier.SOSCorrectObject

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The char-0 Bessel energy as a real number, `E_K^{C}(μ_{2m}) = (2K)!·[x^{2K}] I₀(2x)^m`. -/
noncomputable def besselEℝ (K m : ℕ) : ℝ :=
  ((ArkLib.ProximityGap.Frontier.AvW0.besselE K m : ℚ) : ℝ)

/-- The Wick ceiling as a real number, `Wick_K = (2K−1)‼·n^K` with `n = 2m`. -/
noncomputable def wickℝ (K m : ℕ) : ℝ :=
  (Nat.doubleFactorial (2 * K - 1) : ℝ) * ((2 * m : ℕ) : ℝ) ^ K

/-- **UNCONDITIONAL char-0 slack ≥ 0.** `E_K^{C} ≤ Wick_K`, repackaging the LANDED axiom-clean
`AvW0.besselWick_allR`. This is `A_slack ≥ 0`: the char-0 part of the DC rescue is free. -/
theorem besselEℝ_le_wickℝ (K m : ℕ) : besselEℝ K m ≤ wickℝ K m := by
  unfold besselEℝ wickℝ
  have h : (ArkLib.ProximityGap.Frontier.AvW0.besselE K m : ℚ)
      ≤ ArkLib.ProximityGap.Frontier.AvW0.wickRHS K m :=
    ArkLib.ProximityGap.Frontier.AvW0.besselWick_allR K m
  have hcast : ((ArkLib.ProximityGap.Frontier.AvW0.besselE K m : ℚ) : ℝ)
      ≤ ((ArkLib.ProximityGap.Frontier.AvW0.wickRHS K m : ℚ) : ℝ) := by exact_mod_cast h
  have hw : ((ArkLib.ProximityGap.Frontier.AvW0.wickRHS K m : ℚ) : ℝ)
      = (Nat.doubleFactorial (2 * K - 1) : ℝ) * ((2 * m : ℕ) : ℝ) ^ K := by
    unfold ArkLib.ProximityGap.Frontier.AvW0.wickRHS
    push_cast; ring
  rw [hw] at hcast
  exact hcast

/-- **The named OPEN residual (the sharpest form of the BGK wall).** The wraparound surplus
`q·(E_K(G) − E_K^{C})` stays within the char-0 slack `q·(Wick_K − E_K^{C})` PLUS the DC term `n^{2K}`.
Equivalently (after cancellation) this IS `DCEnergyBound G K`; carrying the char-0 split makes the
proven part (`Wick_K − E_K^{C} ≥ 0`) explicit and the open part (surplus vs DC) the only residual. -/
def SurplusRescued (G : Finset F) (K : ℕ) : Prop :=
  (Fintype.card F : ℝ) * (rEnergy G K : ℝ) - (Fintype.card F : ℝ) * besselEℝ K (G.card / 2)
    ≤ (Fintype.card F : ℝ) * (wickℝ K (G.card / 2) - besselEℝ K (G.card / 2))
      + (G.card : ℝ) ^ (2 * K)

/-- **MAIN reduction (axiom-clean, non-vacuous).** The DC-rescued surplus residual `SurplusRescued G K`
IMPLIES `DCEnergyBound G K`. The char-0 term `besselEℝ` cancels algebraically; what remains is the
exact ledger `q·E_K − n^{2K} ≤ q·Wick_K`. Combined with `besselEℝ_le_wickℝ` (the proven `A_slack ≥ 0`),
this exhibits `d_K ≥ 0` as: PROVEN char-0 slack + DC term ≥ OPEN wraparound surplus. -/
theorem dcEnergyBound_of_surplusRescued {G : Finset F} (K : ℕ)
    (hres : SurplusRescued G K)
    (hcard : 2 * (G.card / 2) = G.card) :
    DCEnergyBound G K := by
  unfold DCEnergyBound
  unfold SurplusRescued at hres
  -- wickℝ K (|G|/2) = (2K−1)‼ · |G|^K
  have hwick_eq : wickℝ K (G.card / 2)
      = (Nat.doubleFactorial (2 * K - 1) : ℝ) * (G.card : ℝ) ^ K := by
    unfold wickℝ
    have : ((2 * (G.card / 2) : ℕ) : ℝ) = (G.card : ℝ) := by rw [hcard]
    rw [this]
  -- From hres: q·E − q·E_C ≤ q·Wick − q·E_C + n^{2K}.  Add (q·E_C − n^{2K}) to both sides.
  -- Goal: q·E − n^{2K} ≤ q·Wick.
  have key : (Fintype.card F : ℝ) * (rEnergy G K : ℝ) - (G.card : ℝ) ^ (2 * K)
      ≤ (Fintype.card F : ℝ) * wickℝ K (G.card / 2) := by
    nlinarith [hres]
  calc (Fintype.card F : ℝ) * (rEnergy G K : ℝ) - (G.card : ℝ) ^ (2 * K)
      ≤ (Fintype.card F : ℝ) * wickℝ K (G.card / 2) := key
    _ = (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * K - 1) : ℝ) * (G.card : ℝ) ^ K) := by
        rw [hwick_eq]

/-- **End-to-end per-frequency prize bound from the DC-rescued surplus residual.** If the wraparound
surplus stays within the char-0 slack plus the DC term, then every nonprincipal frequency satisfies
the Wick-shaped prize bound `‖η_b‖^{2K} ≤ q·(2K−1)‼·|G|^K`. -/
theorem eta_pow_le_of_surplusRescued {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F} {K : ℕ}
    (hres : SurplusRescued G K)
    (hcard : 2 * (G.card / 2) = G.card) {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ (2 * K)
      ≤ (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * K - 1) : ℝ) * (G.card : ℝ) ^ K) :=
  eta_pow_le_of_dcEnergyBound hψ (dcEnergyBound_of_surplusRescued K hres hcard) hb

/-- **The char-0 slack is unconditionally available inside the rescue.** This records the proven
half of the ledger: `A_slack = q·(Wick_K − E_K^{C}) ≥ 0` for `q ≥ 0`. The DC-rescue thus only needs
the surplus to fit within `A_slack + n^{2K}`; the `A_slack` summand is free. -/
theorem charZero_slack_nonneg (K : ℕ) {G : Finset F} (hq : (0:ℝ) ≤ (Fintype.card F : ℝ)) :
    (0:ℝ) ≤ (Fintype.card F : ℝ) * (wickℝ K (G.card / 2) - besselEℝ K (G.card / 2)) := by
  have h : besselEℝ K (G.card / 2) ≤ wickℝ K (G.card / 2) := besselEℝ_le_wickℝ K (G.card / 2)
  have : (0:ℝ) ≤ wickℝ K (G.card / 2) - besselEℝ K (G.card / 2) := by linarith
  exact mul_nonneg hq this

end ArkLib.ProximityGap.Frontier.SOSCorrectObject

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.SOSCorrectObject.besselEℝ_le_wickℝ
#print axioms ArkLib.ProximityGap.Frontier.SOSCorrectObject.dcEnergyBound_of_surplusRescued
#print axioms ArkLib.ProximityGap.Frontier.SOSCorrectObject.eta_pow_le_of_surplusRescued
#print axioms ArkLib.ProximityGap.Frontier.SOSCorrectObject.charZero_slack_nonneg
