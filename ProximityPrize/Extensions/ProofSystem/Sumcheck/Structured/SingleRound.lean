/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.ProofSystem.Sumcheck.Structured.SingleRound

/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ProximityPrize.Extensions.ProofSystem.Sumcheck.Structured
import ArkLib.ProofSystem.Sumcheck.Structured.RoundLemmas

/-!
# Structured (Witness-Mode) Sumcheck — Single-Round Primitives

This file collects single-round primitives for the structured (witness-mode) sumcheck:

- `getSumcheckRoundPoly` — derive the univariate `g_i(X)` sent by the prover from
  the multiquadratic round polynomial `H_i(X_i, ..., X_{ℓ-1})` by summing over the
  remaining boolean-hypercube directions.
- `pSpecSumcheckRound` — the two-message protocol spec for one round
  (`P_to_V : L⦃≤ d⦄[X]`, `V_to_P : L`; `d` defaults to 2), with `OracleInterface` /
  `SampleableType` instances.
- `roundPrvState`, `getRoundProverFinalOutput`, `roundOracleProver`, `roundOracleVerifier`,
  `roundOracleReduction` — the per-round prover / verifier / reduction, generic in a protocol
  `Context : Type` and external oracle statements `OStmtIn : ιₛᵢ → Type`. The outer protocol
  iterates these via `seqCompose`.
- `roundKnowledgeError` — the `2 / |L|` Schwartz–Zippel round error.

These were originally housed in `Binius.BinaryBasefold.Prelude`,
`RingSwitching.Spec`, and `RingSwitching.SumcheckPhase`. They are fully
generic (no binary-tower or ring-switching dependencies) and have been promoted here so
that future ring-switching protocols (Hachi, Galois-ring PCS) can reuse them without
depending on `Binius.*`. `RingSwitching.SumcheckPhase` retains thin `@[reducible]`
wrappers that specialize `Context` and `OStmtIn` back to the ring-switching types.
-/

namespace Sumcheck.Structured

open OracleSpec OracleComp ProtocolSpec Finset Polynomial MvPolynomial

noncomputable section

section RoundPoly

variable {L : Type} [CommRing L] (ℓ : ℕ) [NeZero ℓ] (D : SumcheckDomain L ℓ)

/-- Degree bound for the prover's round polynomial over an **arbitrary** summation set `S`.
This is the heterogeneous generalisation of `Spec.SingleRound.sumcheck_roundPoly_degreeLE`, which
fixes `S` to a uniform cube `(univ.map D) ^ᶠ (n - i)`. The per-round / hyperprism sumcheck sums over
heterogeneous cubes `(SumcheckDomain.drop …).cube`, so the degree bound must not depend on the shape
of `S` — and indeed it doesn't: each summand has degree `≤ deg` in the free variable, and a finite
sum preserves that. -/
theorem roundPoly_degreeLE_finset {R : Type*} [CommSemiring R] {n deg : ℕ} (i : Fin (n + 1))
    {challenges : Fin i.castSucc → R} {poly : R[X Fin (n + 1)]}
    (hp : poly ∈ R⦃≤ deg⦄[X Fin (n + 1)]) (S : Finset (Fin (n - i) → R)) :
    ∑ x ∈ S, poly ⸨X ⦃i⦄, challenges, x⸩' (by simp; omega) ∈ R⦃≤ deg⦄[X] := by
  refine mem_degreeLE.mpr ((degree_sum_le S _).trans (Finset.sup_le fun x _ => ?_))
  refine degree_map_le.trans (natDegree_le_iff_degree_le.mp ?_)
  rw [natDegree_finSuccEquivNth]
  exact degreeOf_le_iff.mpr fun m a ↦ hp a i

/-- The authoritative round polynomial keeps variable `0` as its indeterminate.
Its evaluation is the remaining cube sum with that prefix variable fixed. -/
theorem getSumcheckRoundPoly_eval_eq_sum_cons {d : ℕ} (i : Fin ℓ)
    (h : ↥L⦃≤ d⦄[X Fin (ℓ - ↑i.castSucc)]) (r : L) :
    (getSumcheckRoundPoly ℓ D (i := i) h).val.eval r =
      ∑ x ∈ (D.drop (↑i.castSucc + 1)).cube,
        MvPolynomial.eval (Fin.cons r x ∘ Fin.cast (by
          have := i.isLt; simp only [Fin.val_castSucc]; omega)) h.val := by
  simp only [getSumcheckRoundPoly, Polynomial.eval_finsetSum]
  exact Finset.sum_congr rfl fun x _ => MvPolynomial.eval_evalExcept_first _ x h.val r

/-- The two-point round check delegates to the canonical uniform-domain identity. -/
theorem getSumcheckRoundPoly_sum_eq {𝓑 : Fin 2 ↪ L} (i : Fin ℓ)
    (h : ↥L⦃≤ 2⦄[X Fin (ℓ - ↑i.castSucc)]) :
    (getSumcheckRoundPoly ℓ (SumcheckDomain.uniform 𝓑 ℓ) (i := i) h).val.eval (𝓑 0) +
      (getSumcheckRoundPoly ℓ (SumcheckDomain.uniform 𝓑 ℓ) (i := i) h).val.eval (𝓑 1) =
        ∑ x ∈ (Finset.univ.map 𝓑) ^ᶠ (ℓ - ↑i.castSucc), MvPolynomial.eval x h.val :=
  eval_add_eval_getSumcheckRoundPoly ℓ 𝓑 i h

end RoundPoly

section ProtocolSpec

variable (L : Type) [Semiring L]

variable [Fintype L] [DecidableEq L] [SampleableType L]

end ProtocolSpec

/-! ## Single round of the structured sumcheck

The per-round prover/verifier/reduction (one round; the outer protocol iterates them via
`seqCompose`). Generic in:
- the underlying carrier `L` (anything `CommRing`),
- the protocol context `Context : Type` (Binius RingSwitching plugs in
  `RingSwitchingBaseContext κ L K ℓ`; Hachi will plug in its own),
- the external oracle statements `OStmtIn : ιₛᵢ → Type` (Binius plugs in
  `aOStmtIn.OStmtIn`).

The state machine has three states per round:
- `0`: before any messages — input statement + oracle product + witness.
- `1`: after P sends `h_i(X)` — adds the univariate.
- `2`: after V samples `r'_i` — adds the challenge.

The error bound `roundKnowledgeError` is the standard `2 / |L|`
Schwartz–Zippel bound; it doesn't depend on `Context` or `OStmtIn`. -/

section SingleRound

variable {L : Type} [CommRing L] [DecidableEq L] (ℓ : ℕ) [NeZero ℓ] (D : SumcheckDomain L ℓ)
variable (Context : Type) {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
  [Oₛᵢ : ∀ j, OracleInterface (OStmtIn j)]
-- Round-polynomial degree bound. `d = 2` for the `H = P · t` case (Binius, ring-switching);
-- `d = 2b+1` for Hachi's degree-`2b` smallness combinator. Threaded explicitly (Lean `variable`
-- has no default), so callers pass `(d := 2)` / `(d := 2b+1)`.
variable (d : ℕ)

end SingleRound

section RoundError

variable (L : Type) [Fintype L] (ℓ : ℕ)

end RoundError

end

end Sumcheck.Structured

#print axioms Sumcheck.Structured.getSumcheckRoundPoly_eval_eq_sum_cons
#print axioms Sumcheck.Structured.getSumcheckRoundPoly_sum_eq
