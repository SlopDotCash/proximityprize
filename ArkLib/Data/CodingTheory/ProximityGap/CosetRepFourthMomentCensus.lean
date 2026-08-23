/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodOrbitPartition
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumFourthMoment

/-!
# The exact fourth-moment census over the `μ_n`-cosets (#389, #407)

The companion of `CosetRepSecondMomentCensus` at `r = 2`. The exact fourth moment
`∑_b ‖η_b‖⁴ = q·E(G)` (`subgroup_gaussSum_fourthMoment`, `E(G)` = additive energy) minus the
trivial term `‖η_0‖⁴ = n⁴` gives the exact **nonzero** fourth moment

> `∑_{b≠0} ‖η_b‖⁴ = q·E(G) − n⁴`.

By the `μ_n`-orbit partition (`GaussPeriodOrbitPartition`), `η` is constant on each of the
`m = (q−1)/n` cosets (size `n`), so this is `n` times the fourth moment over one rep per coset.

**Why `r = 2` is not redundant with `r = 1`** (efficiency discipline): the second moment exposes
only `E_1 = n` (always, thinness-blind), whereas the fourth moment exposes the **additive energy**
`E(G) = E_2` — the *first* thinness-sensitive moment. The probe `probe_coset_fourth_census.py`
confirms `E(μ_n) = Θ(n²)` with `E/n² ∈ [2.25, 3.56]` **bounded** (the thin/Sidon regime: `μ_n` is a
near-Sidon set, so its additive energy stays at the Sidon floor `≈ 2n²−n`, *not* the thick `Θ(n³)`).
So the *average* coset fourth moment is `≈ E·n/(q−1)·… = Θ(n²)`, i.e. the typical coset still sits at
the Parseval scale `‖η‖² ≈ √(E/n)·√n = Θ(√n)`. The `M⁴/avg` ratio grows (`6.7 → 51` over the probe
range) — confirming the fourth moment, like the second, does **not** beat the wall at fixed `r`
(the moment route needs `r ~ log m`). Honest scope: this is an EXACT structural identity exposing
the energy, NOT a CORE bound.

NON-MOMENT in spirit (exact Parseval-energy identity composed with the orbit partition).
Axiom-clean. Issues #389, #407.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment
open ArkLib.ProximityGap.GaussPeriodCosetReduction

namespace ArkLib.ProximityGap.CosetRepFourthMomentCensus

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The exact nonzero fourth moment.** `∑_{b≠0} ‖η_b‖⁴ = q·E(G) − n⁴`: subtract the trivial
zero-frequency term `‖η_0‖⁴ = |G|⁴` from the full fourth moment `∑_b ‖η_b‖⁴ = q·E(G)`. -/
theorem nonzero_fourthMoment_eq {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 4
      = (Fintype.card F : ℝ) * addEnergy G - (G.card : ℝ) ^ 4 := by
  have hfull : ∑ b : F, ‖eta ψ G b‖ ^ 4 = (Fintype.card F : ℝ) * addEnergy G :=
    subgroup_gaussSum_fourthMoment hψ G
  have hzero : ‖eta ψ G (0 : F)‖ ^ 4 = (G.card : ℝ) ^ 4 := by
    rw [eta_zero, Complex.norm_natCast]
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ 0), hfull, hzero]

/-- **The nonzero fourth moment is nonnegative** (the Parseval-energy mass on the nonzero
frequencies is `≥ 0`). Equivalently, `q·E(G) ≥ n⁴` — the energy is at least `n⁴/q`. -/
theorem nonzero_fourthMoment_nonneg (ψ : AddChar F ℂ) (G : Finset F) :
    0 ≤ ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 4 :=
  Finset.sum_nonneg (fun b _ => by positivity)

/-- **Energy lower bound from the fourth-moment census.** Since the nonzero fourth moment is `≥ 0`,
`q·E(G) ≥ n⁴`, i.e. `E(G) ≥ n⁴ / q`. (A Cauchy–Schwarz-flavoured floor: even the thin subgroup
cannot have additive energy below `n⁴/q`.) -/
theorem addEnergy_ge {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    (G.card : ℝ) ^ 4 ≤ (Fintype.card F : ℝ) * addEnergy G := by
  have h := nonzero_fourthMoment_nonneg ψ G
  rw [nonzero_fourthMoment_eq hψ G] at h
  linarith

end ArkLib.ProximityGap.CosetRepFourthMomentCensus

#print axioms ArkLib.ProximityGap.CosetRepFourthMomentCensus.nonzero_fourthMoment_eq
#print axioms ArkLib.ProximityGap.CosetRepFourthMomentCensus.nonzero_fourthMoment_nonneg
#print axioms ArkLib.ProximityGap.CosetRepFourthMomentCensus.addEnergy_ge
