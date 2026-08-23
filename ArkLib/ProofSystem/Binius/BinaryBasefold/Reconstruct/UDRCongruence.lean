/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Binius.BinaryBasefold.Code

/-!
# UDR-closeness congruence under domain-index equality

This file provides `UDRClose_of_fin_eq`: transporting unique-decoding-radius closeness
(`UDRClose`) of an oracle function `f` at domain index `i` to an oracle function `g` at
domain index `j`, given a propositional equality `i = j` of the (dependent) `Fin r` indices
and a heterogeneous equality `HEq f g`.

Since the domain index `i : Fin r` controls the type `OracleFunction … i` of the oracle
function, the natural statement uses `HEq f g`; once `i = j` is substituted the two oracle
functions live in the same type and `HEq` collapses to equality, after which `UDRClose` is
preserved by the proof-irrelevant membership bounds `h_i`, `h_j`.

This congruence is consumed by the query-phase soundness layer (`QueryPhasePrelims`) and by
the final-sumcheck step proofs.
-/

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix

noncomputable section

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 : ℕ} [NeZero ℓ] [NeZero 𝓡]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}

/-- **UDR-closeness congruence under domain-index equality.**

If the domain indices `i, j : Fin r` are equal and the oracle functions `f, g` are
heterogeneously equal, then closeness of `f` (at `i`) transports to closeness of `g`
(at `j`). The membership bounds `h_i : i ≤ ℓ` and `h_j : j ≤ ℓ` are implicit and only
enter `UDRClose` through proof-irrelevant positions. -/
theorem UDRClose_of_fin_eq
    {i j : Fin r} {h_i : i ≤ ℓ} {h_j : j ≤ ℓ}
    {f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i}
    {g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j}
    (hij : i = j) (hfg : HEq f g)
    (hf_close : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i h_i f) :
    UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) j h_j g := by
  cases hij
  cases hfg
  exact hf_close

end

end Binius.BinaryBasefold
