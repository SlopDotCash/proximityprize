/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (R196 small-index branch consumer)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R188QuarterMGFTowerConsumer

/-!
# R196 (#466): small-index branch for the product-MGF route

R196's exact census shows the coarse large-index spike envelope is not meant
for tiny quotient sizes `M = (p-1)/n < 32`: many such cases violate the
`exp(max/4)/M` spike-ratio target.  But the direct quarter-MGF bound itself
remains below `2` on the finite census.

This file records the deterministic proof shape:

```text
SmallIndexBaseCase ∨ LargeIndexEnvelope
  ⟹ DyadicQuarterMGFBound.
```

The small-index branch is where finite certificates live; the large-index
branch is where the R189/R194/R195 envelope machinery applies.  This avoids
forcing a large-index asymptotic inequality onto degenerate tiny coset counts.
-/

open Finset
open Real

namespace ArkLib.ProximityGap.Frontier.R196SmallIndexBranchConsumer

open ArkLib.ProximityGap.Frontier.R188QuarterMGFTowerConsumer

/-- Direct finite-certificate branch for small quotient index.  It is just the
quarter-MGF bound, named to distinguish finite base certificates from the
large-index envelope proof. -/
def SmallIndexQuarterMGFCertificate {ι : Type*}
    (s : Finset ι) (t : ι → ℝ) : Prop :=
  DyadicQuarterMGFBound s t

/-- Large-index envelope branch.  Also definitionally the same final bound,
but named separately because its proof is expected to factor through
bulk/spike, logarithmic max, and covariance slack inputs. -/
def LargeIndexQuarterMGFEnvelope {ι : Type*}
    (s : Finset ι) (t : ι → ℝ) : Prop :=
  DyadicQuarterMGFBound s t

/-- If either the finite small-index certificate or the large-index envelope
is available, the quarter-MGF residual is available. -/
theorem quarterMGF_of_small_or_large {ι : Type*}
    (s : Finset ι) (t : ι → ℝ)
    (h : SmallIndexQuarterMGFCertificate s t ∨ LargeIndexQuarterMGFEnvelope s t) :
    DyadicQuarterMGFBound s t := by
  rcases h with hsmall | hlarge
  · exact hsmall
  · exact hlarge

/-- Product-MGF route with the small/large branch exposed directly.  This feeds
the R188 tower consumer: if both child sides are covered by either finite
base certificates or the large-index envelope, then the parent has the R168
tail MGF residual. -/
theorem dyadicTailMGF_of_child_small_or_large {ι : Type*}
    (s : Finset ι) (parent left right : ι → ℝ)
    (hparent : ∀ i ∈ s, parent i ≤ left i + right i)
    (hLeft : SmallIndexQuarterMGFCertificate s left ∨ LargeIndexQuarterMGFEnvelope s left)
    (hRight : SmallIndexQuarterMGFCertificate s right ∨ LargeIndexQuarterMGFEnvelope s right) :
    ArkLib.ProximityGap.Frontier.R168DyadicTailEnvelopeConsumer.DyadicTailMGFBound s parent := by
  exact dyadicTailMGF_of_child_quarterMGF s parent left right hparent
    (quarterMGF_of_small_or_large s left hLeft)
    (quarterMGF_of_small_or_large s right hRight)

end ArkLib.ProximityGap.Frontier.R196SmallIndexBranchConsumer

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R196SmallIndexBranchConsumer.quarterMGF_of_small_or_large
#print axioms ArkLib.ProximityGap.Frontier.R196SmallIndexBranchConsumer.dyadicTailMGF_of_child_small_or_large
