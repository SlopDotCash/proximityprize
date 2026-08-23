/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAGSFieldUniversal

/-!
# Issue #141 — the field-universal GS prize, reduced to a single combinatorial input

This file is a thin naming layer over the canonical surface in
`GrandChallenge141UniformResolved`, which defines the genuine field-universal prize
(`epsMCAgsPrizeUniversalConjecture`), isolates the open core (`UniversalGSListMassBound`), and
proves the reduction (`epsMCAgsPrizeUniversalConjecture_of_UniversalGSListMassBound`).

Earlier this file carried its **own** copy of `epsMCAgsPrizeUniversalConjecture` and an identical
open-core hypothesis under the name `CapacityListCoveringBound`; that duplicate declaration of
`epsMCAgsPrizeUniversalConjecture` made the two modules un-co-importable (it broke `lake build
ArkLib`). The duplication is removed: `CapacityListCoveringBound` is now a definitional alias of the
canonical `UniversalGSListMassBound`, and the reduction below delegates to the canonical proof.

## The open core (unchanged)

The prize is field-universal: the constants `c₁,c₂,c₃` are quantified **before** the field, so the
bound `(1/q)·(2^m)^{c₁}/(ρ^{c₂}·η^{c₃})` vanishes as `q → ∞`. The genuinely-open content is exactly
`UniversalGSListMassBound` — the beyond-Johnson Reed–Solomon list-decoding mass bound up to capacity
`δ ≤ 1 − ρ − η` (no in-tree or mathlib proof exists). Nothing here asserts it; it is the explicit
hypothesis of the reduction.

## References
- [ABF26] §1 Grand MCA Challenge; §4.5 `conj:mca-conjecture`. Tracking: Issue #141.
-/

namespace ProximityGap

open NNReal Code
open scoped ProbabilityTheory BigOperators NNReal

namespace MCAGS

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The Reed–Solomon code at ABF26 prize rate `ρ = prizeRates j` over the evaluation `domain`. -/
noncomputable def prizeCode (domain : ι ↪ F) (j : Fin 4) : Set (ι → F) :=
  (ReedSolomon.code (domain := domain)
      ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))

/-- **The clean combinatorial open input.** A definitional alias of the canonical
`UniversalGSListMassBound`: a *uniformly polynomial* Guruswami–Sudan list size together with the
pivot-covering and faithfulness data, valid up to capacity `δ ≤ 1 − ρ − η`. This is the
beyond-Johnson Reed–Solomon list-decoding mass bound — the genuinely open research input. It is not
asserted here; it is the explicit hypothesis of
`epsMCAgsPrizeUniversal_of_capacityListCovering`. -/
abbrev CapacityListCoveringBound (m : ℕ) : Prop := UniversalGSListMassBound m

/-- **The reduction (axiom-clean): the field-universal prize follows from the combinatorial bound.**
A thin wrapper over the canonical `epsMCAgsPrizeUniversalConjecture_of_UniversalGSListMassBound`:
from a faithful, pivot-covering family of uniformly-polynomial GS list size up to capacity, the
GS-exposed error meets the prize bound by the proven bridge
`epsMCAgs_le_listSize_div_of_pivotCovering`, pinning the open ABF26 prize to exactly
`CapacityListCoveringBound` with no `axiom` and no `sorry`. -/
theorem epsMCAgsPrizeUniversal_of_capacityListCovering (m : ℕ)
    (h : CapacityListCoveringBound m) :
    epsMCAgsPrizeUniversalConjecture m :=
  epsMCAgsPrizeUniversalConjecture_of_UniversalGSListMassBound m h

/-! ## Source audit -/

#print axioms ProximityGap.MCAGS.epsMCAgsPrizeUniversal_of_capacityListCovering

end MCAGS

end ProximityGap
