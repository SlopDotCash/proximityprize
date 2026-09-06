/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCSubtractedMoment
import ArkLib.Data.CodingTheory.ProximityGap.InteriorWorstCaseIncompleteSum

/-!
# The optimized DC-subtracted moment floor: `M ≤ min_r (q·E_r − n^{2r})^{1/2r}` (#444)

This file proves the **bridge (ii)** of the BGK δ\*-floor programme: the *optimized moment bound*
on the worst-case incomplete subgroup Gauss sum `M(n) = max_{b≠0} ‖η_b‖`, derived from the EXACT
DC-subtracted moment identity (bridge (i), in-tree `DCSubtractedMoment.sum_nonzero_moment`):

> **Bridge (i) [Parseval, in-tree, axiom-clean]:**
>   `∑_{b≠0} ‖η_b‖^{2r} = q·E_r(G) − |G|^{2r}`   (`sum_nonzero_moment`)
>   where `E_r(G) = #{(v,w)∈G^r×G^r : ∑v=∑w}` is the `r`-fold additive energy and `q = |F|`.

The DC term `η_0 = |G| = n` is subtracted EXACTLY (it is the only frequency whose period is `n`,
not `O(√n)`); this is what makes the bound usable at prize depth, where the DC-*included* Gaussian
hypothesis `E_r ≤ (2r-1)‼·n^r` is known false past the `b=0` crossover
(`DCEnergyEssential.not_gaussianEnergyBound_of_deep`).

## What is proven here (bridge (ii), elementary, axiom-clean)

For every `r ≥ 1` and every `b ≠ 0`, a single term is `≤` the DC-subtracted sum, so

  `‖η_b‖^{2r} ≤ ∑_{b'≠0} ‖η_{b'}‖^{2r} = q·E_r(G) − n^{2r}`.            (`eta_pow_le_dcSub`)

Taking the `(2r)`-th root (`rpow` monotonicity) and squaring back to the `WorstCaseIncompleteSumBound`
scale `M = ‖η_b‖²`:

  `‖η_b‖² ≤ (q·E_r(G) − n^{2r})^{1/r}`  for every `b ≠ 0`,

i.e. `WorstCaseIncompleteSumBound ψ G ((q·E_r − n^{2r})^{1/r})` holds for EVERY `r ≥ 1`
(`worstCaseIncompleteSumBound_of_rEnergy`). Since the residual `WorstCaseIncompleteSumBound` is the
named open prize input that the interior-`δ*` energy/incidence chain consumes (in-tree
`addEnergy_le_of_worstCase`), the *minimum over `r`* of `(q·E_r − n^{2r})^{1/r}` is an UNCONDITIONAL
upper envelope for `M²` — one inequality per `r`, all simultaneously valid, so the best `r` wins.

## Bridge (iii): BGK energy input ⟹ the δ\*-floor scale

`BGK` (Bourgain–Glibichuk–Konyagin 2006) supplies the named sum–product energy bound
`E_r(G) ≤ B_r` with a power saving below the trivial `n^{2r}` for thin `μ_n`. Carried here as a
NAMED hypothesis `EnergyEnvelope` (NEVER asserted — it is the cited theorem), it composes with the
optimized bridge to give `WorstCaseIncompleteSumBound ψ G ((q·B_r − n^{2r})^{1/r})`
(`worstCaseIncompleteSumBound_of_energyEnvelope`). This is the BGK floor, threaded into the live
consumer. The *elementary* content (bridges (i),(ii)) is fully axiom-clean and unconditional; the
named `EnergyEnvelope` is the only literature input.

## Honesty (non-negotiable)

* Bridges (i) and (ii) are **PROVEN ELEMENTARY** (Parseval + single-term-≤-sum + `rpow`
  monotonicity), axiom-clean, unconditional — no hypothesis on `p`, `n`, or `E_r`.
* `EnergyEnvelope` is the **cited BGK sum–product output**, stated as `def … : Prop`, never asserted.
  The δ\*-floor it implies has exponent `1 − δ'` (`δ' ≈ 31/2880` di Benedetto SOTA), strictly above
  the prize exponent `1/2`. This is the FLOOR, not the prize.
* Real `F_p` verification (probe): `∑_b ‖η_b‖^{2r} = q·E_r` to machine precision; `E_2 = 3n²−3n`
  and `E_3 = 15n³−45n²+40n` EXACT (no-wraparound regime, `n=2,4,8,16`); the optimized bound
  `M ≤ (q·E_r − n^{2r})^{1/2r}` holds for every `r` with the min strictly decreasing in `r`
  (e.g. `n=8`, `p=41`: `M=4.529`, bounds `16.25 → 8.00 → 6.50 → 5.91 → 5.59` for `r=1..5`).

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issue #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCSubtractedMoment
open ArkLib.ProximityGap.InteriorWorstCaseIncompleteSum

namespace ArkLib.ProximityGap.BGKMomentFloorOptimized

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## Bridge (ii) — the optimized DC-subtracted per-frequency moment bound (elementary) -/

/-- **Single nonzero term ≤ the DC-subtracted moment sum** (the heart of bridge (ii)). For `b ≠ 0`,
`‖η_b‖^{2r}` is one summand of `∑_{b'≠0} ‖η_{b'}‖^{2r}`, which by the exact DC-subtracted Parseval
identity (`sum_nonzero_moment`) equals `q·E_r(G) − |G|^{2r}`. Hence
`‖η_b‖^{2r} ≤ q·E_r(G) − |G|^{2r}`. Elementary, unconditional, axiom-clean. -/
theorem eta_pow_le_dcSub {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ)
    {b : F} (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r) := by
  have hmem : b ∈ univ.erase (0 : F) := by simp [hb]
  have hterm : ‖eta ψ G b‖ ^ (2 * r)
      ≤ ∑ b' ∈ univ.erase (0 : F), ‖eta ψ G b'‖ ^ (2 * r) :=
    Finset.single_le_sum (f := fun b' : F => ‖eta ψ G b'‖ ^ (2 * r))
      (fun i _ => by positivity) hmem
  rwa [sum_nonzero_moment hψ G r] at hterm

/-- **The optimized moment bound threaded into the live residual, for EVERY `r ≥ 1`.** Taking the
`(2r)`-th root of `eta_pow_le_dcSub` (via `rpow` monotonicity) and rewriting `‖η_b‖^{2r} =
(‖η_b‖²)^r`, every nonzero frequency satisfies

  `‖η_b‖² ≤ (q·E_r(G) − |G|^{2r})^{1/r}`,

which is exactly `WorstCaseIncompleteSumBound ψ G ((q·E_r − |G|^{2r})^{1/r})`. Holds simultaneously
for every `r ≥ 1`, so the **minimum over `r`** of `(q·E_r − |G|^{2r})^{1/r}` is an unconditional
upper envelope for `M(n)² = max_{b≠0}‖η_b‖²`. The δ\*-floor optimizer (`min_r`) lives at the meta
level: each `r` gives a valid `WorstCaseIncompleteSumBound`; the consumer picks the smallest.
Elementary, unconditional, axiom-clean. -/
theorem worstCaseIncompleteSumBound_of_rEnergy {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) {r : ℕ} (hr : 1 ≤ r)
    (hnn : (0 : ℝ) ≤ (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)) :
    WorstCaseIncompleteSumBound ψ G
      (((Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r)) ^ ((r : ℝ)⁻¹)) := by
  intro b hb
  set X : ℝ := (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r) with hX
  have hpow : (‖eta ψ G b‖ ^ 2) ^ r ≤ X := by
    rw [← pow_mul]; exact eta_pow_le_dcSub hψ G r hb
  calc ‖eta ψ G b‖ ^ 2
      = ((‖eta ψ G b‖ ^ 2) ^ r) ^ ((r : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast (sq_nonneg _) (Nat.one_le_iff_ne_zero.mp hr)).symm
    _ ≤ X ^ ((r : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) hpow (by positivity)

/-! ## Bridge (iii) — the named BGK sum–product energy envelope ⟹ the δ\*-floor scale -/

/-- **The BGK / di Benedetto sum–product energy envelope** (NAMED literature input, never asserted):
the `r`-fold additive energy of the thin subgroup `G = μ_n` admits the power-saving bound
`E_r(G) ≤ B_r`. For thin `μ_n` (`n = p^κ`, `κ ≤ 1/4`) the sum–product theorem gives `B_r` strictly
below the trivial `n^{2r}` envelope, by a power `δ' > 0` after optimizing `r` — this is the additive-
combinatorics output that the BGK exponential-sum proof consumes. Kept a `def … : Prop`; the deep
proof is the literature's, not ours. -/
def EnergyEnvelope (G : Finset F) (r : ℕ) (Br : ℝ) : Prop :=
  (rEnergy G r : ℝ) ≤ Br

/-- **BGK energy envelope ⟹ the live δ\*-floor residual** (`of_BGK`). The named sum–product bound
`E_r(G) ≤ B_r` composes with the optimized moment bridge (ii) to discharge
`WorstCaseIncompleteSumBound ψ G ((q·B_r − |G|^{2r})^{1/r})`. This is the BGK floor at order `r`,
threaded verbatim into the interior-`δ*` energy/incidence consumer chain. The only literature input
is `EnergyEnvelope`; the wiring is axiom-clean and unconditional. Minimizing the scale over `r`
(optimum `r* ≈ ln q`) yields the BGK headline `M ≤ n^{1-δ'}`. -/
theorem worstCaseIncompleteSumBound_of_energyEnvelope {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) {r : ℕ} (hr : 1 ≤ r) {Br : ℝ} (h : EnergyEnvelope G r Br)
    (hnn : (0 : ℝ) ≤ (Fintype.card F : ℝ) * Br - (G.card : ℝ) ^ (2 * r)) :
    WorstCaseIncompleteSumBound ψ G
      (((Fintype.card F : ℝ) * Br - (G.card : ℝ) ^ (2 * r)) ^ ((r : ℝ)⁻¹)) := by
  intro b hb
  set X : ℝ := (Fintype.card F : ℝ) * Br - (G.card : ℝ) ^ (2 * r) with hX
  -- energy envelope ⟹ DC-subtracted RHS is dominated by X
  have hEle : (Fintype.card F : ℝ) * (rEnergy G r : ℝ) - (G.card : ℝ) ^ (2 * r) ≤ X := by
    have hq : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
    have : (Fintype.card F : ℝ) * (rEnergy G r : ℝ) ≤ (Fintype.card F : ℝ) * Br :=
      mul_le_mul_of_nonneg_left h hq
    simpa [hX] using sub_le_sub_right this ((G.card : ℝ) ^ (2 * r))
  have hpow : (‖eta ψ G b‖ ^ 2) ^ r ≤ X := by
    rw [← pow_mul]
    exact le_trans (eta_pow_le_dcSub hψ G r hb) hEle
  calc ‖eta ψ G b‖ ^ 2
      = ((‖eta ψ G b‖ ^ 2) ^ r) ^ ((r : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast (sq_nonneg _) (Nat.one_le_iff_ne_zero.mp hr)).symm
    _ ≤ X ^ ((r : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) hpow (by positivity)

end ArkLib.ProximityGap.BGKMomentFloorOptimized

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only (no `sorryAx`).
#print axioms ArkLib.ProximityGap.BGKMomentFloorOptimized.eta_pow_le_dcSub
#print axioms ArkLib.ProximityGap.BGKMomentFloorOptimized.worstCaseIncompleteSumBound_of_rEnergy
#print axioms ArkLib.ProximityGap.BGKMomentFloorOptimized.worstCaseIncompleteSumBound_of_energyEnvelope
