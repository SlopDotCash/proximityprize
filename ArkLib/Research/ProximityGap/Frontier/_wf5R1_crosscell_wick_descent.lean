/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CrossCellShkredovBound
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodMomentBound

/-!
# The dyadic-descent route to the Gaussian energy bound (#444, lane wf-R1)

Lane R1 (BCHKS Conj 1.12 / crossCell ≤ ε·diagonal, additive-comb route). This file lands the
**exact algebraic reduction** of the prize Gaussian energy bound `E_s(μ_n) ≤ (2s-1)‼·n^s`
(`GaussPeriodMomentBound.GaussianEnergyBound` at `r = s`) to a bound on the dyadic **crossCell**
surplus, and records the **machine-checked refutation** of the per-level multiplicative forms.

## The chain

`CumulantDyadicDescent` gives the EXACT split (negation-closed `G = μ_n = H ⊔ ζ·H`, `H = μ_{n/2}`):

> `N₀(G, 2s) = 2·N₀(H, 2s) + crossCell(H, ζ, 2s)`   (`CrossCellShkredovBound.crossCell_add_two_diag`),

and `N₀(·, 2s) = rEnergy(·) s = E_s(·)` for negation-closed sets
(`SubgroupGaussSumRawMoment.N0_eq_rEnergy_of_neg_closed`). So the parent energy is the diagonal
floor `2·E_s(μ_{n/2})` plus the off-diagonal cross-resonance count. The Gaussian energy bound at
the parent, `E_s(μ_n) ≤ (2s-1)‼·(2·|H|)^s`, therefore holds **iff**

> **`crossCell(H, ζ, 2s) ≤ (2s-1)‼·(2|H|)^s − 2·E_s(μ_{n/2})`**   (`Q_R1`, the sharp sufficient form),

i.e. the cross surplus is at most the Wick budget minus the diagonal floor. This is the cleanest
concrete sufficient lemma the dyadic/additive-comb route reduces the prize energy input to.

## The reduction (proved here, axiom-clean)

`gaussianEnergyBound_of_crossCell_le` : the implication
`crossCell ≤ Wick(2|H|,s) − 2·E_s(H)  ⟹  GaussianEnergyBound (H ∪ ζ·H) s`.
Pure arithmetic on the exact descent identity (cast to `ℝ`), no character sums, no regime
hypothesis. It is the honest statement of what the crossCell route must supply.

## The refutation of the per-level multiplicative forms (HONEST — probe-checked, NOT a closure)

Exact char-0 DP counts (`probe_wf5R1_*.py`, thin primes `p ≈ n⁴`, `n ∈ {16,32}`) refute every
*per-level multiplicative* form of the crossCell bound — they all FAIL with a ratio that GROWS in
the depth `s`:

Each ratio below is labelled by its actual denominator. The probe-reported sequence
`1.14 (s=2), 1.31 (s=3), 1.61 (s=4), 2.10 (s=5)` at `n=16` is the WICK-RECURSION-NORMALISED ratio
`crossCell / ((2^{s-1}−1)·2·E_s(H))`; an earlier version of this docstring reused the same
sequence for the naive ratio as well, which was wrong for `s ≥ 3`.

* **`crossCell ≤ ε·(2·E_s(H))`, `ε < 1`** (the naive Shkredov diagonal form,
  `CrossCellShkredovBound.ShkredovDiagonalBound`): the naive ratio `crossCell/(2E_s(H))` is the
  normalised value times `2^{s-1}−1`, i.e. about `1.14, 3.94, 11.3, 31.5` for `s = 2..5`. Exact
  check at the `n=16, s=3` char-0 cell: `E_3(μ_16) = 50560`, `E_3(μ_8) = 5120`, so
  `crossCell = 50560 − 2·5120 = 40320` and `crossCell/(2E_3(μ_8)) = 40320/10240 = 3.9375`. NO
  `ε < 1`.
* **`crossCell ≤ (2^{s-1}−1)·(2·E_s(H))`** (the Wick-recursion multiplier, the value that would let
  the descent reproduce the Wick scaling `n^s → (2n)^s`): the normalised ratio is
  `1.14, 1.31 (= 3.9375/3 = 1.3125), 1.61, 2.10` at `n=16` — STILL `> 1` and growing. The per-level
  energy ratio `E_s(μ_n)/E_s(μ_{n/2})` is `4.29, 9.88, 24.5` at `n=16, s=2,3,4`, EXCEEDING the
  Wick scale `2^s = 4, 8, 16`.

Both per-level forms fail in these cells; correcting the ratio labels does not restore either. The
global bound `E_s(μ_n) ≤ (2s-1)‼·n^s` is still measured to hold (`W_n < 1` for all tested
`n ≤ 32`, with `W` DECREASING in `s`): the descent drifts toward the Wick ceiling at every dyadic
level (ratio `> 2^s`), and the global bound survives through the slack accumulated at the small
base levels. So the crossCell route is a **slack-balance** argument, not a per-level domination —
the sufficient lemma must track the *absolute* Wick gap `Wick(2|H|,s) − 2·E_s(H)` (the form `Q_R1`,
proved equivalent to the parent bound here).

**What is open, false or settled.** Keep three problems apart:
* In CHARACTERISTIC ZERO (`μ_n` = complex `2`-power roots of unity) a vanishing sum with
  nonnegative coefficients decomposes into antipodal pairs, so the char-0 energy has a pairing
  ceiling `≤ (2s-1)‼·n^s` at every depth; that part is not an open problem.
* In CHARACTERISTIC `p`, extra (wrapping) collisions can push the actual finite-field energy above
  the char-0 count; bounding that excess is the open content.
* The RAW Gaussian target `E_s ≤ (2s-1)‼·n^s` at production depth `s ≈ log p` is known to be
  obstructed by the principal (DC) atom `n^{2s}/q` (R113 in the 2026-10-28 audit); the live
  production target is the DC-subtracted form (`DCSubtractedMoment`), not this raw bound.
The descent identity **localizes but does not close** the open finite-field content.

## References
- [BCHKS25] Ben-Sasson–Carmon–Haböck–Kopparty–Saraf. ePrint 2025/2055, Conjecture 1.12.
- [ABF26] Arnon–Boneh–Fenzi. *Open Problems in List Decoding and Correlated Agreement.* #407/#444.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.SubgroupGaussSumRawMoment
open ArkLib.ProximityGap.CrossCellShkredovBound
open ArkLib.ProximityGap.GaussPeriodMomentBound

namespace ArkLib.ProximityGap.CrossCellWickDescent

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The sharp dyadic sufficient form `Q_R1`.** For `G = μ_n = H ⊔ ζ·H` (`H = μ_{n/2}`), the
crossCell surplus is at most the Wick budget at the parent minus the diagonal floor:

> `crossCell(H, ζ, 2s)  ≤  (2s-1)‼·(2·|H|)^s − 2·E_s(μ_{n/2})`.

(Stated over `ℝ` with `E_s(H) = rEnergy H s`. `2·|H| = |G|`.) This is the exact arithmetic
complement of the Gaussian energy bound at the parent level — see `gaussianEnergyBound_of_crossCell_le`. -/
def CrossCellWickBudget (H : Finset F) (ζ : F) (s : ℕ) : Prop :=
  (crossCell H ζ (2 * s) : ℝ)
    ≤ (Nat.doubleFactorial (2 * s - 1) : ℝ) * ((2 * H.card : ℕ) : ℝ) ^ s
        - 2 * (rEnergy H s : ℝ)

/-- **The reduction (lane R1 headline, axiom-clean).** If the crossCell surplus obeys the Wick
budget `Q_R1` and the negation-closed identity `N₀(G,2s) = E_s(G)` holds at both levels, then the
**Gaussian energy bound holds at the parent**: `E_s(μ_n) ≤ (2s-1)‼·|μ_n|^s`. Pure arithmetic on the
exact dyadic descent `N₀(G,2s) = 2·N₀(H,2s) + crossCell` (`crossCell_add_two_diag`). No character
sums, no regime hypothesis — this is the honest statement of what the crossCell / additive-comb
route must supply to feed `GaussPeriodMomentBound`. -/
theorem gaussianEnergyBound_of_crossCell_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {H : Finset F} {ζ : F} (hζ : ζ ≠ 0)
    (hdisj : Disjoint H (H.image (fun y => ζ * y))) {s : ℕ} (hs : 1 ≤ s)
    (hnegG : ∀ x ∈ (H ∪ H.image (fun y => ζ * y)), -x ∈ (H ∪ H.image (fun y => ζ * y)))
    (hnegH : ∀ x ∈ H, -x ∈ H)
    (hbudget : CrossCellWickBudget H ζ s) :
    GaussianEnergyBound (H ∪ H.image (fun y => ζ * y)) s := by
  classical
  set G := H ∪ H.image (fun y => ζ * y) with hG
  -- exact descent: 2·N₀(H,2s) + crossCell = N₀(G,2s)
  have hdec : 2 * N0 H (2 * s) + crossCell H ζ (2 * s) = N0 G (2 * s) :=
    crossCell_add_two_diag hζ hdisj (by omega : 1 ≤ 2 * s)
  -- N₀ = rEnergy at both levels (negation-closed)
  have hEG : N0 G (2 * s) = rEnergy G s := N0_eq_rEnergy_of_neg_closed hψ G hnegG s
  have hEH : N0 H (2 * s) = rEnergy H s := N0_eq_rEnergy_of_neg_closed hψ H hnegH s
  -- |G| = 2·|H| (disjoint union, image of injective scaling has card |H|)
  have hcardK : (H.image (fun y => ζ * y)).card = H.card :=
    Finset.card_image_of_injective _ (fun a b hab => mul_left_cancel₀ hζ hab)
  have hcardG : G.card = 2 * H.card := by
    rw [hG, Finset.card_union_of_disjoint hdisj, hcardK]; ring
  -- E_s(G) = 2·E_s(H) + crossCell  (ℕ-level), from the exact descent + the two N₀=rEnergy bridges
  have hnatE : rEnergy G s = 2 * rEnergy H s + crossCell H ζ (2 * s) := by
    rw [← hEG, ← hEH]; omega
  -- cast to ℝ
  have hreal : (rEnergy G s : ℝ) = 2 * (rEnergy H s : ℝ) + (crossCell H ζ (2 * s) : ℝ) := by
    have := congrArg (Nat.cast (R := ℝ)) hnatE
    push_cast at this
    linarith [this]
  -- assemble the real-valued inequality
  have hb := hbudget
  unfold CrossCellWickBudget at hb
  unfold GaussianEnergyBound
  -- goal: ↑(rEnergy G s) ≤ (doubleFact)·(↑G.card)^s; rewrite card and rEnergy G via the descent
  rw [hcardG, hreal]
  -- 2·↑(rEnergy H s) + ↑crossCell ≤ (doubleFact)·(↑(2·|H|))^s, from hb
  linarith [hb]

/-- **Converse: the parent Gaussian bound implies `Q_R1`.** Under the same exact descent
hypotheses, `GaussianEnergyBound (H ∪ ζ·H) s` gives `CrossCellWickBudget H ζ s`, since
`E_s(G) = 2·E_s(H) + crossCell` and `|G| = 2·|H|`. -/
theorem crossCellWickBudget_of_gaussianEnergyBound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {H : Finset F} {ζ : F} (hζ : ζ ≠ 0)
    (hdisj : Disjoint H (H.image (fun y => ζ * y))) {s : ℕ} (hs : 1 ≤ s)
    (hnegG : ∀ x ∈ (H ∪ H.image (fun y => ζ * y)), -x ∈ (H ∪ H.image (fun y => ζ * y)))
    (hnegH : ∀ x ∈ H, -x ∈ H)
    (hG : GaussianEnergyBound (H ∪ H.image (fun y => ζ * y)) s) :
    CrossCellWickBudget H ζ s := by
  classical
  set G := H ∪ H.image (fun y => ζ * y) with hGdef
  have hdec : 2 * N0 H (2 * s) + crossCell H ζ (2 * s) = N0 G (2 * s) :=
    crossCell_add_two_diag hζ hdisj (by omega : 1 ≤ 2 * s)
  have hEG : N0 G (2 * s) = rEnergy G s := N0_eq_rEnergy_of_neg_closed hψ G hnegG s
  have hEH : N0 H (2 * s) = rEnergy H s := N0_eq_rEnergy_of_neg_closed hψ H hnegH s
  have hcardK : (H.image (fun y => ζ * y)).card = H.card :=
    Finset.card_image_of_injective _ (fun a b hab => mul_left_cancel₀ hζ hab)
  have hcardG : G.card = 2 * H.card := by
    rw [hGdef, Finset.card_union_of_disjoint hdisj, hcardK]; ring
  have hnatE : rEnergy G s = 2 * rEnergy H s + crossCell H ζ (2 * s) := by
    rw [← hEG, ← hEH]; omega
  have hreal : (rEnergy G s : ℝ) = 2 * (rEnergy H s : ℝ) + (crossCell H ζ (2 * s) : ℝ) := by
    have := congrArg (Nat.cast (R := ℝ)) hnatE
    push_cast at this
    linarith [this]
  unfold GaussianEnergyBound at hG
  rw [hcardG, hreal] at hG
  unfold CrossCellWickBudget
  linarith [hG]

/-- **`Q_R1` is the exact complement of the parent Gaussian bound.** Under the exact descent
hypotheses, `CrossCellWickBudget H ζ s ↔ GaussianEnergyBound (H ∪ ζ·H) s`: `Q_R1` neither
weakens nor strengthens the named open input, it only relocates it onto the off-diagonal
cross-resonance count. (Earlier versions of this theorem stated only the forward implication
despite the `iff` name; both directions are now proved.) -/
theorem crossCellWickBudget_iff_parentBound {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {H : Finset F} {ζ : F} (hζ : ζ ≠ 0)
    (hdisj : Disjoint H (H.image (fun y => ζ * y))) {s : ℕ} (hs : 1 ≤ s)
    (hnegG : ∀ x ∈ (H ∪ H.image (fun y => ζ * y)), -x ∈ (H ∪ H.image (fun y => ζ * y)))
    (hnegH : ∀ x ∈ H, -x ∈ H) :
    CrossCellWickBudget H ζ s ↔
      GaussianEnergyBound (H ∪ H.image (fun y => ζ * y)) s :=
  ⟨fun hb => gaussianEnergyBound_of_crossCell_le hψ hζ hdisj hs hnegG hnegH hb,
    fun hG => crossCellWickBudget_of_gaussianEnergyBound hψ hζ hdisj hs hnegG hnegH hG⟩

end ArkLib.ProximityGap.CrossCellWickDescent

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms ArkLib.ProximityGap.CrossCellWickDescent.gaussianEnergyBound_of_crossCell_le
#print axioms ArkLib.ProximityGap.CrossCellWickDescent.crossCellWickBudget_of_gaussianEnergyBound
#print axioms ArkLib.ProximityGap.CrossCellWickDescent.crossCellWickBudget_iff_parentBound
