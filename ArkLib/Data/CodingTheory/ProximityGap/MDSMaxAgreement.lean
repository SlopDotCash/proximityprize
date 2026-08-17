/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ProximityGap.MCAGS

open scoped NNReal
open Polynomial

namespace ArkLib.MDS

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Hypothesis 30: The maximal agreement of any vector with an MDS code is at least k.
    This implies the maximum agreement can never be k-1.
    For Reed-Solomon codes, this follows from polynomial interpolation.
-/
def rs_max_agreement_ge_k (domain : ι ↪ F) (k : ℕ) (_hk : k ≤ Fintype.card ι) (v : ι → F) :
    Prop :=
    ∃ c ∈ (ReedSolomon.code domain k : Set (ι → F)),
      (Finset.univ.filter (fun i => c i = v i)).card ≥ k

end ArkLib.MDS
