/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumCosetInv

/-!
# Period orbit quotient reduction (#444 / I031)

The I031 chaining handle uses the elementary fact that the subgroup Gauss period

`η_b = ∑_{x∈G} ψ(b*x)`

is constant on multiplicative `G`-cosets of nonzero frequencies. The core invariance is already
proved in `SubgroupGaussSumCosetInv.eta_smul_invariant`. This Frontier file packages the consumer
form needed by the quotient-chaining route:

if a finite set `R` covers the nonzero frequency cosets, then a period bound checked only on `R`
extends to every nonzero frequency. Thus the relevant index set has size `(q-1)/|G|` once a
transversal is supplied; the remaining I031 content is the deterministic-to-Gaussian sup comparison,
not this quotient step.
-/

set_option autoImplicit false

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumCosetInv

namespace ProximityGap.Frontier.PeriodOrbitQuotientReduction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `R` covers the nonzero multiplicative `G`-cosets of the frequency line: every `b ≠ 0`
can be written as `g*r` with `g ∈ G`, `g ≠ 0`, and `r ∈ R`. -/
def CoversNonzeroFrequencyCosets (G R : Finset F) : Prop :=
  ∀ b : F, b ≠ 0 → ∃ r ∈ R, ∃ g ∈ G, g ≠ 0 ∧ b = g * r

/-- Multiplication by every nonzero element of `G` preserves `G`, in both directions. -/
def MultiplicativelyInvariant (G : Finset F) : Prop :=
  ∀ g ∈ G, g ≠ 0 →
    (∀ x ∈ G, g * x ∈ G) ∧ (∀ x ∈ G, g⁻¹ * x ∈ G)

/-- Period bounds on all nonzero frequencies. -/
def NonzeroPeriodBound (ψ : AddChar F ℂ) (G : Finset F) (T : ℝ) : Prop :=
  ∀ b : F, b ≠ 0 → ‖eta ψ G b‖ ≤ T

/-- Period bounds checked only on a chosen representative set. -/
def RepPeriodBound (ψ : AddChar F ℂ) (G R : Finset F) (T : ℝ) : Prop :=
  ∀ r ∈ R, ‖eta ψ G r‖ ≤ T

/-- Every nonzero frequency has a representative with the same Gauss period. -/
theorem exists_rep_eta_eq {ψ : AddChar F ℂ} {G R : Finset F}
    (hG : MultiplicativelyInvariant G) (hcover : CoversNonzeroFrequencyCosets G R) {b : F}
    (hb : b ≠ 0) :
    ∃ r ∈ R, eta ψ G b = eta ψ G r := by
  rcases hcover b hb with ⟨r, hr, g, hg, hg0, hbgr⟩
  rcases hG g hg hg0 with ⟨hleft, hleftInv⟩
  refine ⟨r, hr, ?_⟩
  rw [hbgr]
  exact eta_smul_invariant G hleft hleftInv hg0

/-- **Quotient consumer.** If `R` covers the nonzero frequency cosets and the subgroup is invariant
under its nonzero multipliers, then bounding the periods on `R` bounds every nonzero period. -/
theorem nonzeroPeriodBound_of_repPeriodBound {ψ : AddChar F ℂ} {G R : Finset F} {T : ℝ}
    (hG : MultiplicativelyInvariant G) (hcover : CoversNonzeroFrequencyCosets G R)
    (hR : RepPeriodBound ψ G R T) :
    NonzeroPeriodBound ψ G T := by
  intro b hb
  rcases exists_rep_eta_eq (ψ := ψ) hG hcover hb with ⟨r, hr, heta⟩
  rw [heta]
  exact hR r hr

/-- The reverse implication is immediate when all representatives are nonzero. -/
theorem repPeriodBound_of_nonzeroPeriodBound {ψ : AddChar F ℂ} {G R : Finset F} {T : ℝ}
    (hRnz : ∀ r ∈ R, r ≠ 0) (h : NonzeroPeriodBound ψ G T) :
    RepPeriodBound ψ G R T := by
  intro r hr
  exact h r (hRnz r hr)

/-- Equivalence between the full nonzero-frequency bound and the representative bound, once `R`
is a nonzero coset cover. -/
theorem nonzeroPeriodBound_iff_repPeriodBound {ψ : AddChar F ℂ} {G R : Finset F} {T : ℝ}
    (hG : MultiplicativelyInvariant G) (hcover : CoversNonzeroFrequencyCosets G R)
    (hRnz : ∀ r ∈ R, r ≠ 0) :
    NonzeroPeriodBound ψ G T ↔ RepPeriodBound ψ G R T :=
  ⟨repPeriodBound_of_nonzeroPeriodBound hRnz,
    nonzeroPeriodBound_of_repPeriodBound hG hcover⟩

/-- The period-norm image over all nonzero frequencies is contained in the period-norm image over
any representative cover. -/
theorem nonzeroPeriodNorm_image_subset_repPeriodNorm_image {ψ : AddChar F ℂ} {G R : Finset F}
    (hG : MultiplicativelyInvariant G) (hcover : CoversNonzeroFrequencyCosets G R) :
    ((Finset.univ.erase (0 : F)).image fun b => ‖eta ψ G b‖)
      ⊆ (R.image fun r => ‖eta ψ G r‖) := by
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨b, hbmem, rfl⟩
  have hb : b ≠ 0 := (Finset.mem_erase.mp hbmem).1
  rcases exists_rep_eta_eq (ψ := ψ) hG hcover hb with ⟨r, hr, heta⟩
  exact Finset.mem_image.mpr ⟨r, hr, by rw [heta]⟩

/-- The representative period-norm image is contained in the nonzero-frequency image when every
representative is nonzero. -/
theorem repPeriodNorm_image_subset_nonzeroPeriodNorm_image {ψ : AddChar F ℂ} {G R : Finset F}
    (hRnz : ∀ r ∈ R, r ≠ 0) :
    (R.image fun r => ‖eta ψ G r‖)
      ⊆ ((Finset.univ.erase (0 : F)).image fun b => ‖eta ψ G b‖) := by
  intro z hz
  rcases Finset.mem_image.mp hz with ⟨r, hr, rfl⟩
  exact Finset.mem_image.mpr
    ⟨r, Finset.mem_erase.mpr ⟨hRnz r hr, Finset.mem_univ r⟩, rfl⟩

/-- **Exact quotient collapse of the period-norm spectrum.** Under a nonzero representative cover,
the set of period magnitudes seen on all nonzero frequencies is exactly the set seen on `R`. -/
theorem nonzeroPeriodNorm_image_eq_repPeriodNorm_image {ψ : AddChar F ℂ} {G R : Finset F}
    (hG : MultiplicativelyInvariant G) (hcover : CoversNonzeroFrequencyCosets G R)
    (hRnz : ∀ r ∈ R, r ≠ 0) :
    ((Finset.univ.erase (0 : F)).image fun b => ‖eta ψ G b‖)
      = (R.image fun r => ‖eta ψ G r‖) := by
  exact Finset.Subset.antisymm
    (nonzeroPeriodNorm_image_subset_repPeriodNorm_image (ψ := ψ) hG hcover)
    (repPeriodNorm_image_subset_nonzeroPeriodNorm_image (ψ := ψ) hRnz)

end ProximityGap.Frontier.PeriodOrbitQuotientReduction

#print axioms ProximityGap.Frontier.PeriodOrbitQuotientReduction.exists_rep_eta_eq
#print axioms
  ProximityGap.Frontier.PeriodOrbitQuotientReduction.nonzeroPeriodBound_of_repPeriodBound
#print axioms
  ProximityGap.Frontier.PeriodOrbitQuotientReduction.repPeriodBound_of_nonzeroPeriodBound
#print axioms
  ProximityGap.Frontier.PeriodOrbitQuotientReduction.nonzeroPeriodBound_iff_repPeriodBound
#print axioms
  ProximityGap.Frontier.PeriodOrbitQuotientReduction.nonzeroPeriodNorm_image_subset_repPeriodNorm_image
#print axioms
  ProximityGap.Frontier.PeriodOrbitQuotientReduction.repPeriodNorm_image_subset_nonzeroPeriodNorm_image
#print axioms
  ProximityGap.Frontier.PeriodOrbitQuotientReduction.nonzeroPeriodNorm_image_eq_repPeriodNorm_image
