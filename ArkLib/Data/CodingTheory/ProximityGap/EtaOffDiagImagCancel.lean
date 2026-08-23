/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.EtaNormSqRealShiftForm
import ArkLib.Data.CodingTheory.ProximityGap.EtaInvolutionFixedPointReal

/-!
# Off-diagonal imaginary cancellation for the inversion shift-spectrum (#444, #389)

This is the next consumer of the completed inversion-orbit structure.  The real-shift form proves
that the total nontrivial difference-set shift spectrum has zero imaginary sum:

`∑_{ζ ∈ μ_n \ {1}} Im η_{b(ζ-1)} = 0`.

For even `n`, the inversion involution has the fixed point `ζ = -1`, and the fixed-point theorem
`eta_negTwoB_isReal` proves that this singleton contributes zero imaginary part.  Therefore, in
odd characteristic (`-1 ≠ 1`), deleting both fixed points `1` and `-1` leaves an exactly
imaginary-cancelling off-diagonal spectrum:

`∑_{ζ ∈ μ_n \ {1,-1}} Im η_{b(ζ-1)} = 0`.

Honest scope: exact bookkeeping identity only, not a bound.  It packages the shift spectrum as
"real singleton + conjugate off-diagonal pairs"; bounding the remaining real cosine sum is still the
open BGK/Paley cancellation problem.  No CORE/capacity claim.
-/

open Finset AddChar Polynomial
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.EtaNormSqRealShiftForm
open ArkLib.ProximityGap.EtaInvolutionFixedPointReal

namespace ArkLib.ProximityGap.EtaOffDiagImagCancel

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

set_option linter.unusedFintypeInType false in
/-- **Off-diagonal imaginary cancellation after deleting the inversion fixed point.**  For even
`n` and odd characteristic (`-1 ≠ 1`), the fixed point `ζ = -1` contributes zero imaginary part, so
removing it from the already-real nontrivial shift-sum leaves zero total imaginary part on the
off-diagonal spectrum `μ_n \ {1,-1}`. -/
theorem sum_im_offDiag_shift_eq_zero {ψ : AddChar F ℂ} {n : ℕ} (hn : 0 < n) (hne : Even n)
    (hneg : (-1 : F) ≠ 1) (b : F) :
    ∑ ζ ∈ ((nthRootsFinset n (1 : F)).erase 1).erase (-1),
        (eta ψ (nthRootsFinset n (1 : F)) (b * (ζ - 1))).im = 0 := by
  classical
  set G := nthRootsFinset n (1 : F) with hG
  have hmemG : (-1 : F) ∈ G := by
    simpa [hG] using neg_one_mem_nthRootsFinset (F := F) hn hne
  have hmemErase : (-1 : F) ∈ G.erase 1 := by
    simp [hmemG, hneg]
  have htotal :
      ∑ ζ ∈ G.erase 1, (eta ψ G (b * (ζ - 1))).im = 0 := by
    simpa [hG] using sum_im_shift_eq_zero (ψ := ψ) (F := F) hn b
  have hfixedArg : b * ((-1 : F) - 1) = -2 * b := by ring
  have hfixed : (eta ψ G (b * ((-1 : F) - 1))).im = 0 := by
    simpa [hG, hfixedArg] using eta_negTwoB_isReal (ψ := ψ) (F := F) hn hne b
  rw [← Finset.sum_erase_add _ _ hmemErase] at htotal
  rwa [hfixed, add_zero] at htotal

#print axioms ArkLib.ProximityGap.EtaOffDiagImagCancel.sum_im_offDiag_shift_eq_zero

end ArkLib.ProximityGap.EtaOffDiagImagCancel
