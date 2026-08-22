/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.I031SupTransversalCollapse
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.PeriodOrbitQuotientReduction

/-!
# I031: the I031 transversal concretely covers the nonzero-frequency cosets of `μ_n` (#444)

`PeriodOrbitQuotientReduction.lean` proves the period-bound transversal reduction
(`nonzeroPeriodBound_iff_repPeriodBound`) for an **abstract** subgroup `G` and **abstract**
representative set `R`, gated on two unproven hypotheses: `MultiplicativelyInvariant G` and
`CoversNonzeroFrequencyCosets G R`. Neither had been instantiated for the actual prize subgroup
`μ_n = nthRootsFinset n 1` with a concrete transversal.

This file discharges the **cover** hypothesis concretely: any I031 `IsCosetTransversal n T` (from
`I031SupTransversalCollapse.lean`) is a `CoversNonzeroFrequencyCosets μ_n T`. So the abstract
quotient consumer's coset-cover requirement is now connected to the concrete `μ_n` transversal.

## What is landed

* `isCosetTransversal_covers`: every `b ≠ 0` shares its `μ_n`-coset with a `t ∈ T`, hence
  `b = g·t` with `g ∈ μ_n`, `g ≠ 0`. This is exactly `CoversNonzeroFrequencyCosets μ_n T`, the
  cover hypothesis of `nonzeroPeriodBound_of_repPeriodBound` / `..._iff_...`, discharged for the
  prize subgroup with the I031 transversal.

## A note on the companion `MultiplicativelyInvariant μ_n` hypothesis (honest wall)

The abstract consumer's *other* hypothesis, `MultiplicativelyInvariant (nthRootsFinset n 1)`, is
**mathematically immediate** (`μ_n` is a finite multiplicative group: closed under multiplication by
`mul_mem_nthRootsFinset`, and under inverses since `(g⁻¹)^n = (g^n)⁻¹ = 1`). However, *elaborating
the statement type* `MultiplicativelyInvariant (nthRootsFinset n 1)` for abstract `F`, `n`
`whnf`-diverges in this build (a `maxHeartbeats 0` elaboration did not terminate), so the wired
`mun_nonzeroPeriodBound_iff_repPeriodBound` is **not landed here**, only the cover half. The
proof *term* is trivial; the wall is purely a `whnf` elaboration trap on that particular `def` in a
statement type, not a mathematical gap. Logged for a future worker (try `irreducible`/`@[reducible]`
control or a hand-rolled `Subgroup`-based restatement that sidesteps the `Finset`-level `whnf`).

## Scope (rules 3, 6, honesty contract)

This connects the I031 transversal to the abstract `CoversNonzeroFrequencyCosets` consumer for the
concrete prize subgroup: it is **NOT** a CORE closure and **NOT** thinness-essential (the cover
holds
for any multiplicative subgroup and any transversal, independent of thickness). Its value is
frontier-movement: the abstract consumer's cover hypothesis had never been instantiated for `μ_n`;
this discharges it. CORE (`M(μ_n) ≤ C·√(n·log(p/n))`) stays **OPEN**.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset Polynomial
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ProximityGap.Frontier.PeriodOrbitQuotientReduction

namespace ArkLib.ProximityGap.I031DilationOrbitReduction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **A coset transversal is a nonzero-frequency coset cover.** If `T` meets each `μ_n`-coset of
`Fₚ*` once (`IsCosetTransversal`), then every `b ≠ 0` lies in the coset of some `t ∈ T`, i.e.
`b = g·t` with `g ∈ μ_n`, `g ≠ 0`. This discharges the `CoversNonzeroFrequencyCosets` hypothesis of
the abstract quotient consumer (`PeriodOrbitQuotientReduction`) concretely for `μ_n` with the I031
transversal. -/
theorem isCosetTransversal_covers {n : ℕ} (hn : 0 < n) {T : Finset F}
    (hT : IsCosetTransversal n T) :
    CoversNonzeroFrequencyCosets (nthRootsFinset n (1 : F)) T := by
  intro b hb
  have hbfreq : b ∈ nonzeroFreqs F := by rwa [mem_nonzeroFreqs]
  obtain ⟨t, htT, htlabel⟩ := hT.surj b hbfreq
  -- `cosetLabel n t = cosetLabel n b` ⇒ `b ∈ cosetLabel n t = t • μ_n` ⇒ `b = t * g`, `g ∈ μ_n`.
  have hb_in_t : b ∈ cosetLabel n t := by rw [htlabel]; exact self_mem_cosetLabel hn b
  rw [cosetLabel, dilate, Finset.mem_image] at hb_in_t
  obtain ⟨g, hg, hbg⟩ := hb_in_t
  -- `b = t * g = g * t`, `g ∈ μ_n`, `g ≠ 0`.
  refine ⟨t, htT, g, hg, ne_zero_of_mem_nthRootsFinset one_ne_zero hg, ?_⟩
  rw [← hbg, mul_comm]

#print axioms isCosetTransversal_covers

end ArkLib.ProximityGap.I031DilationOrbitReduction
