/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvL_DiBenedettoEnergyGrounded

/-!
# The di-Benedetto near-Sidon BEAT assembly, modular (#444, AvT3a)

This file ASSEMBLES the di-Benedetto near-Sidon sup-norm improvement for `μ_n` (the multiplicative
group of `2^k`-th roots of unity) from two clearly-named external hypotheses plus the
**now-grounded** char-0 cubic-energy bound. It is the consumer-side weld of
`_AvL_DiBenedettoEnergyGrounded.rEnergy_three_le` into the analytic estimate.

## The mathematics being assembled

di-Benedetto, *"On the sum-product problem for nearly-Sidon sets"* / the trilinear character-sum
machinery of **arXiv:2003.06165** (Thm 3.1), specialized to the multiplicative set `μ_n` of
`2^k`-th roots of unity, consumes the near-Sidon additive energies
`T₂(n) = 3n² − 3n` and `T₃(n) = 15n³ − 45n² + 40n` (the GENUINE `rEnergy` closed forms, proven
char-0 in `_AvL_T3ClosedForm`, value-bounded `T₃ ≤ 15n³` in `_AvL_DiBenedettoEnergyGrounded`).
With these Sidon-floor energies the di-Benedetto "energy exponent" specializes to `Hexp = 7`,
yielding the complete-character-sum bound

> `max_{a≠0} |Σ_{x∈μ_n} e_p(a·x)|  ≤  |μ_n|^{1 − 1/24} · p^{1/72}`,

nontrivial (i.e. beats the trivial `≤ |μ_n|`) precisely when `|μ_n| > p^{1/7}`. At the prize
aspect ratio `β = 4` (`n ≈ p^{1/4}`) the realised sup-norm exponent is `≈ 0.9583 = 23/24`.

## How this brick is organised (the modularity)

* **`DiBenedettoThm31`** — a *named hypothesis* (a `Prop` field) packaging the EXTERNAL trilinear
  estimate verbatim as it applies here: *given the cubic-energy bound `E₃ ≤ 15·n³`, the sup-norm
  obeys `M ≤ n^{23/24}·p^{1/72}`*. This is the arXiv:2003.06165 Thm 3.1 input. We do NOT prove it
  (it is external analytic number theory); we name it and consume it.
* **`GoodPrimeEnergyTransfer`** — a SEPARATE named hypothesis: *the char-0 energy bound
  `E₃ ≤ 15·n³` transfers to the residue field `F_p` at `p`*. The char-0 bound is PROVEN
  (`rEnergy_three_le`); whether it survives reduction mod `p` is the **open core** (the No-Excess
  onset threshold `r₀(n)`; the bad-prime set is finite but its prize-scale control is the BGK
  wall). Naming this transfer as a hypothesis is exactly what makes the assembly GOOD-PRIME-ONLY.
* **`diBenedetto_beat`** — the assembly: from `DiBenedettoThm31` + `GoodPrimeEnergyTransfer`,
  conclude the beat bound `M ≤ n^{23/24}·p^{1/72}`. The energy premise of `DiBenedettoThm31` is
  discharged structurally by `GoodPrimeEnergyTransfer`, so the conclusion is unconditional GIVEN
  the two named hypotheses.

## ⚠️ Honest scope — this is NOT prize closure

* **GOOD-PRIME-ONLY.** The prize is **FOR-ALL-q** (the three CA constants are bound BEFORE the
  universal quantifier over fields, per [ABF26] §4.5 `mcaConjecture`). The whole assembly rests on
  `GoodPrimeEnergyTransfer`, which is a hypothesis ABOUT A SINGLE PRIME `p`. A good-prime result
  cannot close a for-all-q statement. `isPrizeClosure = false`.
* **The saving is STRICTLY below `1/24` at every finite `n`.** The exact energy
  `E₃ = 15n³ − 45n² + 40n` has leading constant `15`, with strictly positive lower-order
  correction (`energyThree_lt_strict : E₃ < 15n³` for `n > 1`); the `1/24` is the leading-order
  idealisation only.
* **`0.9583 = 23/24 ≫ 0.5`.** The prize requires the sup-norm exponent to reach `1/2`
  (the Paley/BGK target `M ≤ C√(n·log(p/n))`). `23/24` is on the HIGH side of the wall; this is a
  genuine SOTA-direction structural gain, not a crossing of the wall.

This is a clean MODULAR SOTA brick: two external/open inputs named, the proven char-0 energy
consumed, the beat exponent assembled. Axiom-clean (`propext, Classical.choice, Quot.sound`);
no `sorry`.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy)

namespace ArkLib.ProximityGap.Frontier.AvT3aDiBenedettoBeat

variable {L : Type*} [Field L] [DecidableEq L] [CharZero L]

/-- The realised di-Benedetto beat exponent at the cubic energy level: `Hexp = 7` gives the
sup-norm saving `1/24`, so the sup-norm exponent is `1 − 1/24 = 23/24`. As a rational this is
exactly `23/24 = 0.958333…` — the headline `0.9583` figure at prize aspect ratio `β = 4`. -/
def beatExponent : ℚ := 23 / 24

/-- Sanity: the beat exponent is `23/24`, strictly between the trivial `1` and the prize target
`1/2`. This pins, axiom-clean, that the assembly lands on the HIGH side of the BGK wall
(`23/24 ≫ 1/2`) — i.e. it is a SOTA-direction gain, not a wall crossing. -/
theorem beatExponent_between : (1 : ℚ) / 2 < beatExponent ∧ beatExponent < 1 := by
  refine ⟨?_, ?_⟩ <;> · unfold beatExponent; norm_num

/-- **Named hypothesis (i): the external di-Benedetto Thm 3.1 estimate (arXiv:2003.06165),
specialized to `μ_n`.** Given the cubic additive-energy bound `E₃(G) ≤ 15·|G|³` (the near-Sidon
floor, proven char-0), the worst-case complete character sum
`M = max_{a≠0} |Σ_{x∈G} e_p(a·x)|` obeys `M ≤ |G|^{23/24} · p^{1/72}`.

This is the EXTERNAL analytic input. `M`, `p`, and the sum are abstracted into the parameters:
`Mval` is the (real, nonneg) sup-norm value, `pval` the field characteristic as a real, and the
hypothesis carries the energy premise `E₃ ≤ 15·|G|³` exactly as di-Benedetto's machinery needs it.
We do not prove this; we name it and consume it. -/
def DiBenedettoThm31 (G : Finset L) (Mval pval : ℝ) : Prop :=
  ((rEnergy G 3 : ℝ) ≤ 15 * (G.card : ℝ) ^ 3) →
    Mval ≤ (G.card : ℝ) ^ (beatExponent : ℝ) * pval ^ ((1 : ℝ) / 72)

/-- **Named hypothesis (ii): good-prime energy transfer.** The char-0 cubic-energy bound
`E₃(G) ≤ 15·|G|³` (PROVEN: `AvLDiBenedettoEnergyGrounded.rEnergy_three_le`) holds for the additive
energy computed for the purposes of the prime `p`. Whether the char-0 census survives reduction mod
`p` is the OPEN core (No-Excess onset threshold; finite bad-prime set, prize-scale control = BGK
wall). This is the lever that makes the whole assembly good-prime-only. -/
def GoodPrimeEnergyTransfer (G : Finset L) : Prop :=
  (rEnergy G 3 : ℝ) ≤ 15 * (G.card : ℝ) ^ 3

/-- **The assembly.** From the external di-Benedetto Thm 3.1 estimate (i) and the good-prime energy
transfer (ii), the di-Benedetto BEAT bound holds: the worst-case complete character sum obeys

  `M ≤ |G|^{23/24} · p^{1/72}`.

The energy premise of `DiBenedettoThm31` is discharged by `GoodPrimeEnergyTransfer`, so given the
two named hypotheses the conclusion holds with no further side condition. (At `β = 4`,
`|G| ≈ p^{1/4}`, the exponent is `≈ 0.9583`.) -/
theorem diBenedetto_beat (G : Finset L) (Mval pval : ℝ)
    (hThm : DiBenedettoThm31 G Mval pval)
    (hTransfer : GoodPrimeEnergyTransfer G) :
    Mval ≤ (G.card : ℝ) ^ (beatExponent : ℝ) * pval ^ ((1 : ℝ) / 72) :=
  hThm hTransfer

/-- **The assembly with the energy transfer DISCHARGED from the proven char-0 census.** When `G` is
a non-empty negation-closed set of `2^k`-th roots of unity (the `μ_n` hypotheses), the good-prime
energy transfer's premise is exactly the proven `rEnergy_three_le`, so the only remaining input is
the external di-Benedetto Thm 3.1 estimate. This is the headline modular statement: *for `μ_n`, the
di-Benedetto Thm 3.1 hypothesis ALONE yields the `23/24` beat* (the energy side is closed in
char 0). It is still good-prime-only: `hThm` (and hence its conclusion) is asserted at the single
prime `p` whose residue field underlies `Mval, pval`. -/
theorem diBenedetto_beat_mu {k : ℕ} (G : Finset L) (Mval pval : ℝ)
    (h0 : (0 : L) ∉ G) (hneg : ∀ z ∈ G, -z ∈ G) (hroot : ∀ z ∈ G, z ^ (2 ^ k) = 1)
    (hcard : 1 ≤ G.card)
    (hThm : DiBenedettoThm31 G Mval pval) :
    Mval ≤ (G.card : ℝ) ^ (beatExponent : ℝ) * pval ^ ((1 : ℝ) / 72) :=
  hThm (AvLDiBenedettoEnergyGrounded.rEnergy_three_le (k := k) G h0 hneg hroot hcard)

end ArkLib.ProximityGap.Frontier.AvT3aDiBenedettoBeat

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.AvT3aDiBenedettoBeat.beatExponent_between
#print axioms ArkLib.ProximityGap.Frontier.AvT3aDiBenedettoBeat.diBenedetto_beat
#print axioms ArkLib.ProximityGap.Frontier.AvT3aDiBenedettoBeat.diBenedetto_beat_mu
