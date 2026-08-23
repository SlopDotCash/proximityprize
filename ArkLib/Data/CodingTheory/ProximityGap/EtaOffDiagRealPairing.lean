/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.EtaShiftRealPartPairing
import ArkLib.Data.CodingTheory.ProximityGap.EtaOffDiagImagCancel

/-!
# Off-diagonal real-part pairing for the inversion shift-spectrum (#444, #389)

`EtaShiftRealPartPairing` proves that inversion preserves each real shift-period term and that the
whole nontrivial real-shift sum is invariant under the reindex `ζ ↦ ζ⁻¹`.  `EtaOffDiagImagCancel`
then deletes the two inversion fixed points `1` and `-1` and proves exact imaginary cancellation on
the remaining off-diagonal spectrum.

This file records the matching **real-part** bookkeeping on that same off-diagonal spectrum
`μ_n \ {1,-1}`:

* `offDiag_shiftSum_re_inv_invariant` — the real off-diagonal sum is unchanged by the inversion
  reindex.
* `two_mul_offDiag_shiftSum_re_eq_paired_sum` — twice the off-diagonal real sum is the sum of the
  two equal inversion-paired real contributions at every off-diagonal point.

Honest scope: exact orbit bookkeeping only, not a bound.  This removes the fixed-point singleton
from the real-pairing identity and leaves the open content exactly where it belongs: bounding the
remaining real cosine aggregate on one representative from each inversion pair.  No CORE claim.
-/

open Finset AddChar Polynomial
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.AdditiveEnergyKernel (inv_mem_nthRootsFinset)

namespace ArkLib.ProximityGap.EtaOffDiagRealPairing

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The off-diagonal real-shift sum is invariant under inversion.**  After deleting the two
inversion fixed points `1` and `-1`, the reindex `ζ ↦ ζ⁻¹` still permutes the spectrum and
preserves each real part. -/
theorem offDiag_shiftSum_re_inv_invariant {ψ : AddChar F ℂ} {n : ℕ} (hn : 0 < n) (b : F) :
    ∑ ζ ∈ ((nthRootsFinset n (1 : F)).erase 1).erase (-1),
        (eta ψ (nthRootsFinset n (1 : F)) (b * (ζ - 1))).re
      = ∑ ζ ∈ ((nthRootsFinset n (1 : F)).erase 1).erase (-1),
        (eta ψ (nthRootsFinset n (1 : F)) (b * (ζ⁻¹ - 1))).re := by
  classical
  refine Finset.sum_nbij' (fun ζ => ζ⁻¹) (fun ζ => ζ⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro ζ hζ
    rw [Finset.mem_erase] at hζ ⊢
    rw [Finset.mem_erase] at hζ
    refine ⟨?_, ?_⟩
    · intro h
      have hneg : ζ = (-1 : F) := by
        simpa using congrArg Inv.inv h
      exact hζ.1 hneg
    · rw [Finset.mem_erase]
      refine ⟨?_, inv_mem_nthRootsFinset hn hζ.2.2⟩
      intro h
      exact hζ.2.1 (by simpa using (inv_eq_one.mp h))
  · intro ζ hζ
    rw [Finset.mem_erase] at hζ ⊢
    rw [Finset.mem_erase] at hζ
    refine ⟨?_, ?_⟩
    · intro h
      have hneg : ζ = (-1 : F) := by
        simpa using congrArg Inv.inv h
      exact hζ.1 hneg
    · rw [Finset.mem_erase]
      refine ⟨?_, inv_mem_nthRootsFinset hn hζ.2.2⟩
      intro h
      exact hζ.2.1 (by simpa using (inv_eq_one.mp h))
  · intro ζ hζ
    rw [Finset.mem_erase] at hζ
    have hζmem : ζ ∈ nthRootsFinset n (1 : F) := Finset.mem_of_mem_erase hζ.2
    have hζ0 : ζ ≠ 0 := ne_zero_of_mem_nthRootsFinset one_ne_zero hζmem
    simp [inv_inv]
  · intro ζ hζ
    rw [Finset.mem_erase] at hζ
    have hζmem : ζ ∈ nthRootsFinset n (1 : F) := Finset.mem_of_mem_erase hζ.2
    have hζ0 : ζ ≠ 0 := ne_zero_of_mem_nthRootsFinset one_ne_zero hζmem
    simp [inv_inv]
  · intro ζ hζ
    rw [Finset.mem_erase] at hζ
    have hζmem : ζ ∈ nthRootsFinset n (1 : F) := Finset.mem_of_mem_erase hζ.2
    have hζ0 : ζ ≠ 0 := ne_zero_of_mem_nthRootsFinset one_ne_zero hζmem
    simp only [inv_inv]

/-- **Paired off-diagonal real aggregate.**  Twice the off-diagonal real sum equals the sum of
the forward and inverse-shift real contributions.  This is the lossless algebraic form consumed by
any future half-orbit bound; it is still only bookkeeping, not cancellation. -/
theorem two_mul_offDiag_shiftSum_re_eq_paired_sum {ψ : AddChar F ℂ} {n : ℕ} (hn : 0 < n) (b : F) :
    2 * (∑ ζ ∈ ((nthRootsFinset n (1 : F)).erase 1).erase (-1),
        (eta ψ (nthRootsFinset n (1 : F)) (b * (ζ - 1))).re)
      = ∑ ζ ∈ ((nthRootsFinset n (1 : F)).erase 1).erase (-1),
        ((eta ψ (nthRootsFinset n (1 : F)) (b * (ζ - 1))).re
          + (eta ψ (nthRootsFinset n (1 : F)) (b * (ζ⁻¹ - 1))).re) := by
  classical
  rw [Finset.sum_add_distrib]
  rw [← offDiag_shiftSum_re_inv_invariant (ψ := ψ) hn b]
  ring

#print axioms ArkLib.ProximityGap.EtaOffDiagRealPairing.offDiag_shiftSum_re_inv_invariant
#print axioms ArkLib.ProximityGap.EtaOffDiagRealPairing.two_mul_offDiag_shiftSum_re_eq_paired_sum

end ArkLib.ProximityGap.EtaOffDiagRealPairing
