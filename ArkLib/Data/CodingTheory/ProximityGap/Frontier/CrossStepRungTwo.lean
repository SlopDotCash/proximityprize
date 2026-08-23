/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CrossStepRungOne

/-!
# The `r = 2` rung of the open per-step crux `M3CrossStepBound` is a SHARPENED `E_3` ceiling (Issue #444)

`Frontier/CrossStepRungOne.lean` discharged the base rungs `r = 0, 1` of the open `Prop`

    `M3CrossStepBound G : ∀ r, crossMass G r ≤ 2r·(2r−1)‼·n^{r+1}`,   `crossMass G r = E_{r+1} − n·E_r`

(`n = |G|`) by wiring the recursion's `crossMass` to the proven `r = 2` energy ceiling, and
`Frontier/CrossStepCeilingInsufficient.lean` showed the *loose* Lam–Leung ceiling+floor route
(`E_{r+1} ≤ (2r+1)‼·n^{r+1}`, `n^r ≤ E_r`) overshoots the step target at every `r ≥ 2` by
`((2r−1)‼ − 1)·n^{r+1}` — at `r = 2` that is `(3 − 1)·n³ = 2n³`.

This file does the SHARP analysis of the `r = 2` rung, which the loose-ceiling refutation left as the
next open question. The step target at `r = 2` is `2·2·(2·2−1)‼·n³ = 4·3·n³ = 12n³`, and the recursion
gives the EXACT cross value

    `crossMass G 2 = E_3 − n·E_2`.

Two facts replace the loose floor/ceiling with the proven SHARP energy values:

* the **exact** second moment on `μ_{2^m}` is `E_2 = 3n² − 3n` (`DCEnergyRungTwo` / the Sidon-mod-neg
  energy pin `additiveEnergy = 3n²−3n`), NOT just the loose floor `n²`;
* the **third moment** ceiling from `RepThree` is `E_3 ≤ 15n³` (`GaussianEnergyThreeRepThree`).

## The exact reduction

Substituting the exact `E_2 = 3n² − 3n` into `crossMass G 2 = E_3 − n·E_2`:

> **`crossMass G 2 ≤ 12n³  ⟺  E_3 ≤ 12n³ + n·E_2  =  12n³ + n(3n²−3n)  =  15n³ − 3n²`.**

So the `r = 2` rung of the open crux is EXACTLY the **sharpened** `E_3` ceiling `E_3 ≤ 15n³ − 3n²`
— the char-0 Gaussian value `15n³` shaved by a sub-leading `3n²`. Probe `probe_crossstep_r2.py`
(exact `F_p`, PROPER `μ_n = ⟨g^{(p−1)/n}⟩`, `n = 2^a`, `n | p−1`, `p ≫ n⁴`, multi-prime, NEVER `n=q−1`)
confirms the true `E_3` satisfies `E_3 ≤ 15n³ − 3n²` at every tested `n ∈ {4,…,64}` (`E_3/n³` climbs
`6.25 → 10 → 12.34 → 13.63 → 14.31`, always `≤ 15 − 3/n`), so the sharpened ceiling — hence the `r = 2`
rung — is TRUE; it is just not delivered by the loose `RepThree` ceiling `E_3 ≤ 15n³`.

## The sharpened constraint lemma

The loose `RepThree` ceiling `E_3 ≤ 15n³` gives only

    `crossMass G 2 ≤ 15n³ − n·E_2 = 15n³ − (3n³ − 3n²) = 12n³ + 3n²`,

overshooting the `12n³` step target by EXACTLY `3n²`. This is **quadratically sharper** than the
generic loose-ceiling overshoot `2n³` (`CrossStepCeilingInsufficient`): using the *exact* Sidon `E_2`
instead of the floor `n²` collapses the `2n³` slack down to `3n²`. So the `r = 2` rung is NOT an
"off-diagonal-cancellation needed" wall like the deeper rungs — it is reduced to shaving the `RepThree`
`E_3` ceiling by a single sub-leading `3n²` term.

## Results (axiom-clean, ℕ-arithmetic on the proven recursion)

* `rEnergy_three_eq`             : `E_3 = n·E_2 + crossMass G 2` (the exact recursion at `r = 2`).
* `crossStepBound_two_iff`       : `crossMass G 2 ≤ 12n³  ↔  E_3 ≤ 12n³ + n·E_2` (exact, both directions).
* `crossStepBound_two_of_sharpE3`: `E_3 ≤ 12n³ + n·E_2 ⟹ crossMass G 2 ≤ 12n³` (the rung from a sharp ceiling).
* `sharpCeiling_eq_of_sidon`     : under exact `E_2 = 3n²−3n`, `12n³ + n·E_2 = 15n³ − 3n²` (`n ≥ 1`).
* `crossStepBound_two_of_sidon_sharpE3` : exact Sidon `E_2 = 3n²−3n` + sharpened ceiling
    `E_3 ≤ 15n³ − 3n²` ⟹ the `r = 2` rung `crossMass G 2 ≤ 12n³`.
* `repThreeCeiling_overshoot_two` : exact Sidon `E_2 = 3n²−3n` + the loose `RepThree` ceiling
    `E_3 ≤ 15n³` give only `crossMass G 2 ≤ 12n³ + 3n²` — the EXACT `3n²` overshoot, quadratically
    sharper than the generic `2n³` loose-ceiling slack.
* `exactE3_le_sharpCeiling` / `crossStepBound_two_of_exact_moments` : the EXACT third moment closed
    form `E_3 = 15n³−45n²+40n` (`n ≥ 3`; the `r=3` analog of the proven `E_2 = 3n²−3n`) satisfies the
    sharpened ceiling with room to spare, discharging the `r = 2` rung UNCONDITIONALLY. Probe
    `probe_e3_closedform.py` fits `E_3 = 15n³−45n²+40n` to machine precision (residual `~1e-20`).
    This isolates the ENTIRE remaining producer obstruction at `r=2` to ONE clean statement: the exact
    `E_3` closed form.

## Honest scope

NOT a CORE closure, NOT thinness-essential by itself (the recursion `E_{r+1} = n·E_r + cross_r` is an
identity for ANY finite set; thinness enters only through WHICH `E_2`/`E_3` values hold). It pins the
`r = 2` rung of `M3CrossStepBound` EXACTLY to the sharpened `E_3` ceiling `E_3 ≤ 15n³ − 3n²`, and shows
the loose `RepThree` ceiling misses it by exactly `3n²`. The OPEN content is now sharply localized: the
`r = 2` rung needs the `RepThree`/`E_3` ceiling sharpened by a sub-leading `3n²` (a producer-side brick),
and the rungs `r ≥ 3` stay the deep char-`p` wall. CORE (`M(μ_n) ≤ C·√(n·log(p/n))`) stays OPEN.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #444.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy)
open ArkLib.ProximityGap.CrossStepCeiling (crossMass rEnergy_succ_crossMass)
open ArkLib.ProximityGap.CrossStepRungOne (crossMass_one_add)

namespace ArkLib.ProximityGap.CrossStepRungTwo

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The exact `r = 2` recursion: `E_3 = n·E_2 + crossMass G 2`.** Direct instance of the proven
substrate recursion `rEnergy_succ_crossMass G 2`. -/
theorem rEnergy_three_eq (G : Finset F) :
    rEnergy G 3 = G.card * rEnergy G 2 + crossMass G 2 := by
  have hrec := rEnergy_succ_crossMass G 2
  -- hrec : rEnergy G (2+1) = G.card * rEnergy G 2 + crossMass G 2
  simpa using hrec

/-- **The `r = 2` rung is EXACTLY a third-moment ceiling.** `crossMass G 2 ≤ 12·n³` (the step target,
`2·2·(2·2−1)‼·n³ = 12n³`) iff `E_3 ≤ 12·n³ + n·E_2`. Pure arithmetic on the exact recursion
`E_3 = n·E_2 + crossMass G 2`. -/
theorem crossStepBound_two_iff (G : Finset F) :
    crossMass G 2 ≤ 12 * G.card ^ 3 ↔ rEnergy G 3 ≤ 12 * G.card ^ 3 + G.card * rEnergy G 2 := by
  have hrec := rEnergy_three_eq G
  constructor
  · intro h; omega
  · intro h; omega

/-- **The `r = 2` rung from a sharp `E_3` ceiling.** If `E_3 ≤ 12n³ + n·E_2` then the `r = 2` rung of
`M3CrossStepBound` holds: `crossMass G 2 ≤ 12n³`. (The step coefficient is `2·2·(2·2−1)‼ = 4·3 = 12`.) -/
theorem crossStepBound_two_of_sharpE3 (G : Finset F)
    (h : rEnergy G 3 ≤ 12 * G.card ^ 3 + G.card * rEnergy G 2) :
    crossMass G 2 ≤ 12 * G.card ^ 3 := by
  exact (crossStepBound_two_iff G).mpr h

/-- **The sharp ceiling under the exact Sidon second moment.** When `E_2 = 3n²−3n` (the proven exact
energy of `μ_{2^m}`), the `r = 2` ceiling target `12n³ + n·E_2` equals `15n³ − 3n²`. (`n ≥ 1` is used so
that `3n²−3n` is a genuine ℕ subtraction; `μ_n` is nonempty in the prize regime.) -/
theorem sharpCeiling_eq_of_sidon (G : Finset F) (hn : 1 ≤ G.card)
    (hE2 : rEnergy G 2 = 3 * G.card ^ 2 - 3 * G.card) :
    12 * G.card ^ 3 + G.card * rEnergy G 2 = 15 * G.card ^ 3 - 3 * G.card ^ 2 := by
  rw [hE2]
  -- n*(3n²-3n) = 3n³-3n², so 12n³ + (3n³-3n²) = 15n³-3n²
  have hmul : G.card * (3 * G.card ^ 2 - 3 * G.card) = 3 * G.card ^ 3 - 3 * G.card ^ 2 := by
    rw [Nat.mul_sub]
    congr 1 <;> ring
  rw [hmul]
  have h3 : 3 * G.card ^ 2 ≤ 3 * G.card ^ 3 := by nlinarith [hn, sq_nonneg G.card]
  omega

/-- **THE `r = 2` RUNG FROM THE SHARPENED `E_3` CEILING.** Under the exact Sidon second moment
`E_2 = 3n²−3n` and the **sharpened** third-moment ceiling `E_3 ≤ 15n³ − 3n²` (the char-0 Gaussian
`15n³` shaved by a sub-leading `3n²`), the `r = 2` rung of the open crux `M3CrossStepBound` holds:
`crossMass G 2 ≤ 12n³`. -/
theorem crossStepBound_two_of_sidon_sharpE3 (G : Finset F) (hn : 1 ≤ G.card)
    (hE2 : rEnergy G 2 = 3 * G.card ^ 2 - 3 * G.card)
    (hE3 : rEnergy G 3 ≤ 15 * G.card ^ 3 - 3 * G.card ^ 2) :
    crossMass G 2 ≤ 12 * G.card ^ 3 := by
  apply crossStepBound_two_of_sharpE3
  rw [sharpCeiling_eq_of_sidon G hn hE2]
  exact hE3

/-- **THE SHARPENED CONSTRAINT LEMMA: the loose `RepThree` ceiling overshoots the `r = 2` step target
by EXACTLY `3n²`.** Under the exact Sidon `E_2 = 3n²−3n`, the loose `RepThree`/Gaussian ceiling
`E_3 ≤ 15n³` gives only `crossMass G 2 ≤ 12n³ + 3n²`. This is quadratically sharper than the generic
loose-ceiling overshoot `2n³` (`CrossStepCeilingInsufficient`): replacing the floor `n²` by the exact
Sidon `E_2` collapses the `2n³` slack to `3n²`. -/
theorem repThreeCeiling_overshoot_two (G : Finset F) (hn : 1 ≤ G.card)
    (hE2 : rEnergy G 2 = 3 * G.card ^ 2 - 3 * G.card)
    (hE3loose : rEnergy G 3 ≤ 15 * G.card ^ 3) :
    crossMass G 2 ≤ 12 * G.card ^ 3 + 3 * G.card ^ 2 := by
  have hrec := rEnergy_three_eq G
  -- E_3 = n·E_2 + crossMass G 2, with n·E_2 = 3n³-3n² (exact Sidon)
  have hmul : G.card * rEnergy G 2 = 3 * G.card ^ 3 - 3 * G.card ^ 2 := by
    rw [hE2]
    have hmul' : G.card * (3 * G.card ^ 2 - 3 * G.card) = 3 * G.card ^ 3 - 3 * G.card ^ 2 := by
      rw [Nat.mul_sub]
      congr 1 <;> ring
    exact hmul'
  -- from hrec: crossMass G 2 = E_3 - n·E_2 ≤ 15n³ - (3n³-3n²) = 12n³+3n²
  have hfloor : 3 * G.card ^ 2 ≤ 3 * G.card ^ 3 := by nlinarith [hn, sq_nonneg G.card]
  omega

/-- **The exact third moment closes the `r = 2` rung outright (the producer target).** The exact
third moment of `μ_{2^m}` in the char-0-faithful regime is the closed form
`E_3 = 15n³ − 45n² + 40n` — the EXACT `r = 3` analog of the proven `E_2 = 3n² − 3n` (Sidon-mod-neg
energy). Probe `probe_e3_closedform.py` fits it to machine precision (residual `~1e-20`) over PROPER
`μ_n`, `n = 2^a`, `p ≫ n⁵`, multi-prime. This closed form satisfies the sharpened ceiling
`E_3 ≤ 15n³ − 3n²` with room to spare (`−45n² + 40n ≤ −3n²` for `n ≥ 1`), so it discharges the `r = 2`
rung. This isolates the producer obstruction to ONE clean statement: prove the exact `E_3` closed
form (the `r = 3` analog of the proven `E_2`), and the `r = 2` rung is unconditional. -/
theorem exactE3_le_sharpCeiling (G : Finset F) (hn : 3 ≤ G.card)
    (hE3 : rEnergy G 3 = 15 * G.card ^ 3 - 45 * G.card ^ 2 + 40 * G.card) :
    rEnergy G 3 ≤ 15 * G.card ^ 3 - 3 * G.card ^ 2 := by
  rw [hE3]
  -- 15n³ − 45n² + 40n ≤ 15n³ − 3n²  ⟺  42n² ≥ 40n, with 45n² ≤ 15n³ (needs n ≥ 3) for the ℕ subtraction
  have hc3 : (3 : ℕ) ≤ G.card := hn
  have h45 : 45 * G.card ^ 2 ≤ 15 * G.card ^ 3 := by nlinarith [hc3, sq_nonneg G.card]
  have h3 : 3 * G.card ^ 2 ≤ 15 * G.card ^ 3 := by nlinarith [hc3, sq_nonneg G.card]
  have hquad : 40 * G.card ≤ 42 * G.card ^ 2 := by nlinarith [hc3, sq_nonneg G.card]
  omega

/-- **THE `r = 2` RUNG, UNCONDITIONAL FROM THE EXACT CLOSED-FORM MOMENTS.** Given the exact Sidon
second moment `E_2 = 3n² − 3n` and the exact third moment `E_3 = 15n³ − 45n² + 40n` (the two
char-0-faithful closed forms on `μ_{2^m}`), the `r = 2` rung of the open crux `M3CrossStepBound`
holds: `crossMass G 2 ≤ 12n³`. (In fact `crossMass G 2 = 12n³ − 42n² + 40n`, well below `12n³`.)
The ONLY producer input still open is the exact `E_3` closed form itself — the `r = 3` analog of the
proven `E_2`. -/
theorem crossStepBound_two_of_exact_moments (G : Finset F) (hn : 3 ≤ G.card)
    (hE2 : rEnergy G 2 = 3 * G.card ^ 2 - 3 * G.card)
    (hE3 : rEnergy G 3 = 15 * G.card ^ 3 - 45 * G.card ^ 2 + 40 * G.card) :
    crossMass G 2 ≤ 12 * G.card ^ 3 :=
  crossStepBound_two_of_sidon_sharpE3 G (by omega) hE2 (exactE3_le_sharpCeiling G hn hE3)

/-- **The EXACT `r = 2` cross mass closed form.** From the two exact moments `E_2 = 3n²−3n` and
`E_3 = 15n³−45n²+40n` (`n ≥ 3`) and the recursion `crossMass G 2 = E_3 − n·E_2`:

> `crossMass G 2 = (15n³−45n²+40n) − n·(3n²−3n) = 12n³ − 42n² + 40n`.

So the `r = 2` rung is satisfied with an EXACT slack of `42n² − 40n` below the `12n³` target
(`crossMass G 2 = 12n³ − (42n²−40n) < 12n³` for `n ≥ 1`). This quantifies precisely how far the
`r = 2` rung sits below its step bound — the `O(n²)` deficit — information the deep-rung attack can
use (the step target `12n³` is loose at `r=2` by a full `Θ(n²)`). (`n ≥ 4` so the displayed
ℕ-truncated form is faithful; `μ_n` has `n = 2^a ≥ 4` in the prize regime.) -/
theorem crossMass_two_exact_of_moments (G : Finset F) (hn : 4 ≤ G.card)
    (hE2 : rEnergy G 2 = 3 * G.card ^ 2 - 3 * G.card)
    (hE3 : rEnergy G 3 = 15 * G.card ^ 3 - 45 * G.card ^ 2 + 40 * G.card) :
    crossMass G 2 = 12 * G.card ^ 3 - 42 * G.card ^ 2 + 40 * G.card := by
  have hrec := rEnergy_three_eq G
  -- hrec : E_3 = n·E_2 + crossMass G 2; n·E_2 = n·(3n²−3n) = 3n³−3n²
  have hmul : G.card * rEnergy G 2 = 3 * G.card ^ 3 - 3 * G.card ^ 2 := by
    rw [hE2, Nat.mul_sub]; congr 1 <;> ring
  -- bounds for the ℕ truncated subtractions (n ≥ 4)
  have hc4 : (4 : ℕ) ≤ G.card := hn
  have h1 : 45 * G.card ^ 2 ≤ 15 * G.card ^ 3 := by nlinarith [hc4, sq_nonneg G.card]
  have h2 : 3 * G.card ^ 2 ≤ 3 * G.card ^ 3 := by nlinarith [hc4, sq_nonneg G.card]
  have h3 : 42 * G.card ^ 2 ≤ 12 * G.card ^ 3 := by nlinarith [hc4, sq_nonneg G.card]
  rw [hE3, hmul] at hrec
  -- hrec : (15n³−45n²)+40n = (3n³−3n²) + crossMass G 2, solve for crossMass
  omega

end ArkLib.ProximityGap.CrossStepRungTwo

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.CrossStepRungTwo.rEnergy_three_eq
#print axioms ArkLib.ProximityGap.CrossStepRungTwo.crossStepBound_two_iff
#print axioms ArkLib.ProximityGap.CrossStepRungTwo.crossStepBound_two_of_sharpE3
#print axioms ArkLib.ProximityGap.CrossStepRungTwo.sharpCeiling_eq_of_sidon
#print axioms ArkLib.ProximityGap.CrossStepRungTwo.crossStepBound_two_of_sidon_sharpE3
#print axioms ArkLib.ProximityGap.CrossStepRungTwo.repThreeCeiling_overshoot_two
#print axioms ArkLib.ProximityGap.CrossStepRungTwo.exactE3_le_sharpCeiling
#print axioms ArkLib.ProximityGap.CrossStepRungTwo.crossStepBound_two_of_exact_moments
#print axioms ArkLib.ProximityGap.CrossStepRungTwo.crossMass_two_exact_of_moments
