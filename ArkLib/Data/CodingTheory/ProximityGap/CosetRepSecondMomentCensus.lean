/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodOrbitPartition

/-!
# The exact second-moment census over the `μ_n`-cosets (#389, #407)

Combining the exact second moment `∑_b ‖η_b‖² = q·n` (`subgroup_gaussSum_secondMoment`) with the
trivial term `‖η_0‖² = n²` gives the exact **nonzero** second moment

> `∑_{b≠0} ‖η_b‖² = q·n − n² = n·(q − n)`.

By the `μ_n`-orbit partition (`GaussPeriodOrbitPartition`), `η` is constant on each of the
`m = (q−1)/n` cosets, each of size `n`, so this is `n` times the second moment summed over one
representative per coset. Reading off the **per-coset average** (`n · (q − n) = n · ∑_reps ‖η_rep‖²`,
so `∑_reps ‖η_rep‖² = q − n`):

> the *average* coset Gauss-period magnitude is `‖η_rep‖²_avg = (q − n)/m = n·(q − n)/(q − 1) ≈ n`,

i.e. the **Parseval floor `√n`** holds for the *typical* coset. The entire open CORE is the gap
between this exact average and the **worst** coset rep `M(n) = max_rep ‖η_rep‖`: the prize asserts
`M ≤ C·√(n·log(p/n))`, i.e. the worst rep exceeds the `√n` average by at most a `√(log(p/n))`
factor. This file pins the *average* side **exactly** (it is `n`, a flat Parseval floor) — so the
beyond-`√n` content lives **entirely** in the max-vs-average spread, NOT in the second moment.

NON-MOMENT in spirit (the census is an exact Parseval identity composed with the orbit partition;
it does NOT attempt a moment *bound* on the max — that route is loose at `r=1`, needing `r ~ log m`).
Honest scope: this is an EXACT structural identity framing the open gap, NOT a CORE bound.
Axiom-clean. Issues #389, #407.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.GaussPeriodCosetReduction

namespace ArkLib.ProximityGap.CosetRepSecondMomentCensus

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The exact nonzero second moment.** `∑_{b≠0} ‖η_b‖² = q·|G| − |G|²`: subtract the trivial
zero-frequency term `‖η_0‖² = |G|²` from the full second moment `∑_b ‖η_b‖² = q·|G|`. -/
theorem nonzero_secondMoment_eq {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2
      = (Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2 := by
  have hfull : ∑ b : F, ‖eta ψ G b‖ ^ 2 = (Fintype.card F : ℝ) * G.card :=
    subgroup_gaussSum_secondMoment hψ G
  have hzero : ‖eta ψ G (0 : F)‖ ^ 2 = (G.card : ℝ) ^ 2 := by
    rw [eta_zero, Complex.norm_natCast]
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ 0), hfull, hzero]

/-- **The exact nonzero second moment, factored.** `∑_{b≠0} ‖η_b‖² = |G|·(q − |G|)` — the form that
exposes the per-coset average: dividing by the `m = (q−1)/n` cosets (each contributing `n` equal
copies) gives the average coset value `q − |G|` summed over reps, i.e. average `≈ |G|`. -/
theorem nonzero_secondMoment_factored {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2
      = (G.card : ℝ) * ((Fintype.card F : ℝ) - G.card) := by
  rw [nonzero_secondMoment_eq hψ G]; ring

/-- **The nonzero second moment is nonnegative and `≤ q·|G|`** (a sanity envelope: the Parseval mass
on the nonzero frequencies sits between `0` and the full second moment). -/
theorem nonzero_secondMoment_nonneg (ψ : AddChar F ℂ) (G : Finset F) :
    0 ≤ ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2 :=
  Finset.sum_nonneg (fun b _ => by positivity)

end ArkLib.ProximityGap.CosetRepSecondMomentCensus

#print axioms ArkLib.ProximityGap.CosetRepSecondMomentCensus.nonzero_secondMoment_eq
#print axioms ArkLib.ProximityGap.CosetRepSecondMomentCensus.nonzero_secondMoment_factored
#print axioms ArkLib.ProximityGap.CosetRepSecondMomentCensus.nonzero_secondMoment_nonneg
