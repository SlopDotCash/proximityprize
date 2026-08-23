/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodCosetReduction

/-!
# I031 orbit-quotient reduction for Gaussian periods (#444)

The I031 lead from the issue-444 sweep is not generic chaining on all nonzero frequencies.
The exact period invariance says

`η_{u b} = η_b` for every `u ∈ G`,

so the index set is the multiplicative quotient `Fˣ / G`.  This file packages the
axiom-clean finite statement consumed by probes and future entropy arguments:
if `R` contains one representative of every nonzero `G`-orbit, then the set of
period norms over all nonzero frequencies is exactly the set of period norms over
`R`.

This proves only the deterministic quotient collapse.  It does **not** prove the
remaining I031 transfer step from the deterministic period process to a Gaussian
comparison process.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.GaussPeriodCosetReduction

namespace ArkLib.ProximityGap.Frontier.I031OrbitQuotient

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A finite set `R` of representatives for the nonzero multiplicative `G`-orbits. -/
def CoversNonzeroOrbits (G R : Finset F) : Prop :=
  ∀ b : F, b ≠ 0 → ∃ u ∈ G, ∃ r ∈ R, b = u * r

/-- **Exact quotient collapse of the period-norm spectrum.**

If `R` contains one representative of every nonzero `G`-orbit and all representatives
are nonzero, then the period norms over all nonzero frequencies are exactly the period
norms over `R`.
-/
theorem eta_norm_nonzero_image_eq_rep_image {ψ : AddChar F ℂ} {G R : Finset F}
    (hbij : ∀ u ∈ G, G.image (fun y => u * y) = G) (h0 : (0 : F) ∉ G)
    (hcover : CoversNonzeroOrbits G R) (hRsub : ∀ r ∈ R, r ≠ 0) :
    ((Finset.univ.erase (0 : F)).image fun b => ‖eta ψ G b‖)
      = (R.image fun r => ‖eta ψ G r‖) := by
  classical
  ext z
  constructor
  · intro hz
    rcases Finset.mem_image.mp hz with ⟨b, hb, hz⟩
    have hb0 : b ≠ 0 := (Finset.mem_erase.mp hb).1
    rcases hcover b hb0 with ⟨u, hu, r, hr, hbr⟩
    refine Finset.mem_image.mpr ⟨r, hr, ?_⟩
    rw [← hz, hbr, eta_mul_left hbij h0 hu r]
  · intro hz
    rcases Finset.mem_image.mp hz with ⟨r, hr, hz⟩
    exact Finset.mem_image.mpr
      ⟨r, Finset.mem_erase.mpr ⟨hRsub r hr, Finset.mem_univ r⟩, hz⟩

/-- **Max form of the quotient collapse.**

The maximum period norm over all nonzero frequencies equals the maximum over any
nonzero representative set meeting every orbit.
-/
theorem eta_norm_nonzero_max_eq_rep_max {ψ : AddChar F ℂ} {G R : Finset F}
    (hbij : ∀ u ∈ G, G.image (fun y => u * y) = G) (h0 : (0 : F) ∉ G)
    (hcover : CoversNonzeroOrbits G R) (hRsub : ∀ r ∈ R, r ≠ 0)
    (hNZ : (Finset.univ.erase (0 : F)).Nonempty) (hRne : R.Nonempty) :
    (((Finset.univ.erase (0 : F)).image fun b => ‖eta ψ G b‖).max' (hNZ.image _))
      = ((R.image fun r => ‖eta ψ G r‖).max' (hRne.image _)) := by
  classical
  let S : Finset ℝ := (Finset.univ.erase (0 : F)).image fun b => ‖eta ψ G b‖
  let T : Finset ℝ := R.image fun r => ‖eta ψ G r‖
  have hSne : S.Nonempty := by
    simpa [S] using hNZ.image (fun b => ‖eta ψ G b‖)
  have hTne : T.Nonempty := by
    simpa [T] using hRne.image (fun r => ‖eta ψ G r‖)
  have hST : S = T := eta_norm_nonzero_image_eq_rep_image hbij h0 hcover hRsub
  change S.max' hSne = T.max' hTne
  apply le_antisymm
  · refine Finset.max'_le S hSne (T.max' hTne) ?_
    intro y hy
    exact Finset.le_max' T y (hST ▸ hy)
  · refine Finset.max'_le T hTne (S.max' hSne) ?_
    intro y hy
    exact Finset.le_max' S y (hST.symm ▸ hy)

end ArkLib.ProximityGap.Frontier.I031OrbitQuotient

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.I031OrbitQuotient.eta_norm_nonzero_image_eq_rep_image
#print axioms ArkLib.ProximityGap.Frontier.I031OrbitQuotient.eta_norm_nonzero_max_eq_rep_max
