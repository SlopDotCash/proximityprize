/-
Copyright (c) 2024 - 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.DG25.ReedSolomon

/-!
# DG25 tensor proximity gap — contrapositive forms

The DP24 Binary Basefold soundness analysis (Proposition 4.21, fiberwise-far case) consumes
the DG25 tensor-style proximity gap in *contrapositive* form: from a word stack that is FAR
from the interleaved code, conclude that the random tensor (multilinear) combination is close
to the base code with probability at most `ϑ · ε / |F|`.

`δ_ε_multilinearCorrelatedAgreement_Nat` is stated in the forward (correlated-agreement)
direction; this file packages the contrapositive once, plus its Reed–Solomon specialization
through `reedSolomon_multilinearCorrelatedAgreement_Nat` (Corollary 3.7, `ε = n`), so that the
Binius `Prop421Case2FiberwiseFarResidual` discharge can consume a single lemma whose
hypotheses are exactly the Lemma 4.22 far-lift output.
-/

noncomputable section

open Code LinearCode InterleavedCode ReedSolomon ProximityGap ProbabilityTheory
open NNReal Finset

namespace ProximityGap

section Generic

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [CommRing F] [Fintype F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommMonoid A] [Module F A]

omit [Fintype A] in
/-- **Contrapositive of the tensor correlated-agreement property.**

If `C` has the `(ϑ, e, ε)` multilinear correlated-agreement property and the stack `u` is NOT
jointly `e`-proximate to the interleaved code, then the random multilinear combination is
`e`-close to `C` with probability at most `ϑ · ε / |F|`. -/
lemma multilinearCorrelatedAgreement_contrapositive
    {C : Set (ι → A)} {ϑ e ε : ℕ}
    (hCA : δ_ε_multilinearCorrelatedAgreement_Nat (F := F) (A := A) (C := C) ϑ e ε)
    (u : WordStack A (Fin (2 ^ ϑ)) ι)
    (h_far : ¬ jointProximityNat (C := C) (u := u) e) :
    Pr_{let r ← $ᵖ (Fin ϑ → F)}[ Δ₀(r |⨂| u, C) ≤ e ]
      ≤ (ϑ : ℝ≥0) * ε / (Fintype.card F : ℝ≥0) :=
  le_of_not_gt fun h_gt => h_far (hCA u h_gt)

end Generic

section ReedSolomon

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {A : Type} [Field A] [Fintype A] [DecidableEq A]
variable {α : ι ↪ A} {k : ℕ}

set_option maxHeartbeats 800000 in
/-- **Corollary 3.7, contrapositive form (Reed–Solomon, unique decoding).**

For an RS code within unique decoding radius `e`, any stack that is NOT jointly `e`-proximate
to the interleaved code has its random tensor combination `e`-close to the code with
probability at most `ϑ · n / |A|`. This is the exact probabilistic input to DP24
Proposition 4.21, Case 2 (with `n = |S^{(i+ϑ)}|` and `ϑ = steps`). -/
lemma reedSolomon_tensor_far_vanish_prob_le
    [NeZero k] [Nontrivial (ReedSolomon.code α k)]
    (hk : k ≤ Fintype.card ι) {e : ℕ}
    (he : e ≤ Code.uniqueDecodingRadius (C := (ReedSolomon.code α k : Set (ι → A))))
    {ϑ : ℕ} (hϑ : ϑ > 0)
    (u : WordStack A (Fin (2 ^ ϑ)) ι)
    (h_far : ¬ jointProximityNat (C := (ReedSolomon.code α k : Set (ι → A))) (u := u) e) :
    Pr_{let r ← $ᵖ (Fin ϑ → A)}[ Δ₀(r |⨂| u, (ReedSolomon.code α k : Set (ι → A))) ≤ e ]
      ≤ (ϑ : ℝ≥0) * (Fintype.card ι) / (Fintype.card A : ℝ≥0) :=
  multilinearCorrelatedAgreement_contrapositive
    (reedSolomon_multilinearCorrelatedAgreement_Nat (α := α) (k := k) hk he ϑ hϑ) u h_far

end ReedSolomon

end ProximityGap

#print axioms ProximityGap.multilinearCorrelatedAgreement_contrapositive
#print axioms ProximityGap.reedSolomon_tensor_far_vanish_prob_le
