/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.CodingTheory.ProximityGap.Basic

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ProximityPrize.Compatibility.UniformProbability
import ArkLib.Data.Probability.Notation
import Mathlib.Probability.Distributions.Uniform

/-!
# Proximity gap fundamental definitions

Define the fundamental definitions for proximity gap properties of generic codes and
module codes over (scalar) rings.

## Main Definitions

### Proximity Gap Definitions
- `proximityMeasure`: Counts vectors close to linear combinations with code `C`
- `proximityGap`: Proximity gap property at distance `d` with cardinality bound
- `δ_ε_proximityGap`: Generic `(δ, ε)`-proximity gap for any collection of sets

### Correlated Agreement Definitions
- `jointAgreement`: Words collectively agree with code `C` on the same coordinate set
- `jointAgreement_iff_jointProximity`: Equivalence between agreement and proximity formulations
- `δ_ε_correlatedAgreementAffineLines`: Correlated agreement for affine lines (2 words)
- `δ_ε_correlatedAgreementCurves`: Correlated agreement for parametrised curves (k words)
- `δ_ε_correlatedAgreementAffineSpaces`: Correlated agreement for affine subspaces (k+1 words)

## Extensions
- weighted correlated agreement
- mutual correlated agreement: a numeric `ε_mca(C, δ)` (ABF26 Definition 4.3) is now
  available in `Errors.lean`. The WHIR proximity-generator version
  (`hasMutualCorrAgreement`) in `ProofSystem/Whir/MutualCorrAgreement.lean` has a
  predicate-level one-way bridge `proximityCondition_imp_mcaEvent_affineLine`; the
  full numeric re-expression remains open (tracked as ABF26-D4.3 follow-up).
- generalize the CA definitions using proximity generator?

## References

- [BCIKS20] Eli Ben-Sasson, Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.
  Proximity gaps for Reed–Solomon codes. In 2020 IEEE 61st Annual Symposium on Foundations of
  Computer Science (FOCS), 2020. Full paper: https://eprint.iacr.org/2020/654, version 20210703:203025.

- [DG25] Benjamin E. Diamond and Angus Gruen. “Proximity Gaps in Interleaved Codes”. In: IACR
  Communications in Cryptology 1.4 (Jan. 13, 2025). issn: 3006-5496. doi: 10.62056/a0ljbkrz.

-/

namespace ProximityGap

open NNReal Finset Function Code Affine
open scoped ProbabilityTheory BigOperators LinearCode Affine

universe u v w k l

section CoreSecurityDefinitions

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type k} {ι : Type l} [Fintype κ] [Fintype ι] [Nonempty ι]
-- κ => row indices, ι => column indices
variable {F : Type v} [Ring F] [Fintype F]
-- variable {M : Type} [Fintype M] -- Message space type
variable {A : Type w} [Fintype A] [DecidableEq A] [AddCommMonoid A] [Module F A] -- Alphabet type
variable (C : Set (ι → A))

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  {F : Type} [Ring F] [Fintype F] [SampleableType F]
  {k : ℕ}

omit [DecidableEq ι] in
/-- Convert the affine-line correlated-agreement predicate into the concrete
`Code.jointProximity` witness used by downstream soundness adapters. -/
theorem jointProximity_of_δ_ε_correlatedAgreementAffineLines
    {A : Type 0} [AddCommMonoid A] [Module F A] [Fintype A] [DecidableEq A]
    {C : Set (ι → A)} {δ ε : ℝ≥0} {u : WordStack (A := A) (κ := Fin 2) (ι := ι)}
    (h_ca : δ_ε_correlatedAgreementAffineLines (F := F) C δ ε)
    (h_prob : Pr_{let z ← $ᵖ F}[δᵣ(u 0 + z • u 1, C) ≤ δ] > ε) :
    jointProximity (C := C) (u := u) δ := by
  rw [← jointAgreement_iff_jointProximity]
  apply h_ca u
  rwa [← ProximityPrize.Compatibility.pmf_uniform_probability_eq_native]

section MultilinearCA

variable {F : Type} [CommRing F] [Fintype F] [SampleableType F]

omit [DecidableEq ι] in
/-- Convert the multilinear correlated-agreement predicate into the concrete
`Code.jointProximity` witness used by downstream soundness adapters. -/
theorem jointProximity_of_δ_ε_multilinearCorrelatedAgreement
    {A : Type 0} [AddCommMonoid A] [Module F A] [Fintype A] [DecidableEq A]
    {C : Set (ι → A)} {ϑ : ℕ} {δ ε : ℝ≥0}
    {u : WordStack (A := A) (κ := Fin (2 ^ ϑ)) (ι := ι)}
    (h_ca : δ_ε_multilinearCorrelatedAgreement (F := F) C ϑ δ ε)
    (h_prob :
      Pr_{let r ← $ᵖ (Fin ϑ → F)}[δᵣ(r |⨂| u, C) ≤ δ] > (ϑ : ℝ≥0) * ε) :
    jointProximity (C := C) (u := u) δ := by
  rw [← jointAgreement_iff_jointProximity]
  apply h_ca u
  rwa [← ProximityPrize.Compatibility.pmf_uniform_probability_eq_native]

end MultilinearCA

omit [DecidableEq ι] in
/-- Convert the polynomial-curves correlated-agreement predicate into the concrete
`Code.jointProximity` witness used by downstream soundness adapters. -/
theorem jointProximity_of_δ_ε_correlatedAgreementCurves
    {A : Type 0} [AddCommMonoid A] [Module F A] [Fintype A] [DecidableEq A]
    {C : Set (ι → A)} {δ ε : ℝ≥0} {u : WordStack (A := A) (κ := Fin (k + 1)) (ι := ι)}
    (h_ca : δ_ε_correlatedAgreementCurves (F := F) (k := k) C δ ε)
    (h_prob :
      Pr_{let r ← $ᵖ F}[δᵣ(∑ i : Fin (k + 1), (r ^ (i : ℕ)) • u i, C) ≤ δ]
        > k * ε) :
    jointProximity (C := C) (u := u) δ := by
  rw [← jointAgreement_iff_jointProximity]
  apply h_ca u
  rwa [← ProximityPrize.Compatibility.pmf_uniform_probability_eq_native]

omit [Fintype F] [SampleableType F] in
/-- Convert the affine-spaces correlated-agreement predicate into the concrete
`Code.jointProximity` witness used by downstream soundness adapters.

This is only the predicate/proximity-form bridge: callers must still supply the probability
trigger required by `δ_ε_correlatedAgreementAffineSpaces`. -/
theorem jointProximity_of_δ_ε_correlatedAgreementAffineSpaces
    {A : Type 0} [AddCommGroup A] [Module F A] [Fintype A] [DecidableEq A]
    {C : Set (ι → A)} {δ ε : ℝ≥0} {u : WordStack (A := A) (κ := Fin (k + 1)) (ι := ι)}
    (h_ca : δ_ε_correlatedAgreementAffineSpaces (F := F) (k := k) C δ ε)
    (h_prob :
      Pr_{let y ← $ᵖ ↥(Affine.affineSubspaceAtOrigin (F := F) (u 0) (Fin.tail u))}[
        δᵣ(y.1, C) ≤ δ] > ε) :
    jointProximity (C := C) (u := u) δ := by
  rw [← jointAgreement_iff_jointProximity]
  apply h_ca u
  rwa [← ProximityPrize.Compatibility.pmf_uniform_probability_eq_native]

end CoreSecurityDefinitions

namespace WeightedAgreement

open NNReal Finset Function
open scoped BigOperators

section

variable {ι : Type} [Fintype ι] [Nonempty ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable (μ : ι → Set.Icc (0 : ℚ) 1)

end

end WeightedAgreement

end ProximityGap
