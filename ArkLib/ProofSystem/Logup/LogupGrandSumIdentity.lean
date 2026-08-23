/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Logup.Common
import ArkLib.ProofSystem.Logup.Sumcheck.SumcheckPolynomial
import ArkLib.Data.MvPolynomial.SchwartzZippelCounting

/-!
# LogUp grand-sum logarithmic-derivative identity + Schwartz-Zippel soundness (issue #13)

The completeness core (the sum-of-reciprocals multiset-inclusion identity, honest-oracle and
count forms + the honest-Q vanishing) and the soundness core (the SZ probability bound for the
LogUp check polynomial via prob_eval_zero_le_div). The OracleVerifier.soundness Prop bridges
remain sibling-owned run-unfolding plumbing.
-/

/-!
# Issue #13 scratch: LogUp Protocol 2 completeness/soundness — extractable math

SCRATCH-FIRST, HAND-VERIFIED. This file is NOT part of the ArkLib build and edits no shared file.
It extracts and closes the *genuine mathematics* underlying the LogUp Protocol-2 security residuals,
distinguishing it cleanly from the protocol-plumbing walls (run-unfolding, the external
`Sumcheck.Spec` import, and the generic `append` composition keystone) that the named residuals
`SubPhaseSoundnessResidual` / `SubPhaseCompletenessResidual` actually bottom out in.

## What this file proves (fully, against confirmed in-tree API)

`section GrandSumIdentity` — **the LogUp logarithmic-derivative grand-sum identity**, i.e. the
completeness rational-function identity the issue asks for:

    ∑_u  m(u) / (x + t(u))  =  ∑_i ∑_u  1 / (x + f_i(u))

with `m` the honest multiplicity oracle from paper eq. (14). This is the precise statement that the
honest prover's sum-of-reciprocals over the table equals the sum-of-reciprocals over the lookup
columns whenever the lookup relation holds. It is proven by chaining the two already-proven halves
in `Logup/Common.lean`:

* `table_sum_normalizedMultiplicity_eq_lookup_sum`  (table side → per-value counts),
* `lookupMultiplicity_sum_div_eq_column_sum`        (per-value counts → column side).

`section PerRowVanishing` — **the per-row algebraic mechanism**: on every hypercube row, the honest
helper functions make the Protocol-2 batched check polynomial `Q` collapse to `∑_k h_k(u)` (the
domain-identity term vanishes). This is the row-local fact behind the embedded sumcheck claim.
Proven by re-exposing the in-tree `qOnHypercube_honest_helpers`.

`section SZSoundness` — **the Schwartz–Zippel soundness reduction** for the LogUp `Q` polynomial.
The cleared-denominator check polynomial `logupQPolynomial` has individual degree `≤ M + 3` in every
variable (proven in-tree: `logupQPolynomial_degreeOf`). We reduce the soundness bound — the
probability that a *nonzero* `Q` vanishes at a uniformly random point of `(S)^n` — to ArkLib's
`prob_eval_zero_le_div` (the probability form of `schwartz_zippel_counting`). The single arithmetic
step `totalDegree ≤ n * (M + 3)` from the per-variable `degreeOf` bound is isolated as the explicit
named hypothesis `hTotalDeg` (we could not confirm the exact mathlib lemma name with the package
source unavailable; it is the standard `MvPolynomial.totalDegree ≤ ∑ᵢ degreeOf i`).

## Honesty note — the named residuals are NOT closed here

`SubPhaseSoundnessResidual` / `SubPhaseCompletenessResidual` are statements about
`OracleVerifier.soundness` / `OracleReduction.completeness` of the outer and embedded-sumcheck
sub-verifiers, threaded through the generic `OracleVerifier.append_soundness` /
`OracleReduction.append_completeness`. Closing them requires (a) unfolding `Reduction.run` of the
outer phase (the verifier-side `simulateQ_outerVerify_eq` exists; the prover-side run composition
does not), (b) the external `Sumcheck.Spec` plain soundness/completeness theorem at the lifted shape
(outside `Logup/**`), and (c) the generic `Prover.appendRunRightResidual` keystone in
`Append.lean` (a ~200-line heterogeneous `Fin.induction`, shared with #25). Those are protocol
plumbing, not extractable algebra, and are not addressed here. What IS extractable algebra — the
grand-sum identity, the per-row vanishing, and the SZ degree/probability reduction — is below.
-/

open scoped NNReal ENNReal BigOperators
open ProbabilityTheory

namespace Logup

namespace Issue13Scratch

/-! ## The LogUp grand-sum logarithmic-derivative identity (completeness core) -/

section GrandSumIdentity

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n M : ℕ}

/-- **LogUp grand-sum identity, count form.** For every challenge `x`, the honest-multiplicity-
weighted sum of table reciprocals equals the multiplicity-weighted sum of per-value reciprocals,
which equals the sum of all column reciprocals. This is exactly the chain of the two in-tree halves;
it is the algebraic heart of LogUp completeness.

`normalizedMultiplicityValue oStmt u = (lookupCount t(u)) / (tableCount t(u))` (paper eq. 14), and
`honestMultiplicity oStmt` is the oracle with `evalOnHypercube _ u = normalizedMultiplicityValue _ u`
by `rfl`. -/
theorem grandSum_identity
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (hInput : (((stmt, oStmt), ()) ∈ inputRelation F n M))
    (hM : 0 < M) (xChallenge : F) :
    (∑ u : Hypercube n,
        normalizedMultiplicityValue oStmt u /
          (xChallenge + evalOnHypercube (tableOracle oStmt) u)) =
      ∑ i : Fin M, ∑ u : Hypercube n,
        (1 : F) / (xChallenge + evalOnHypercube (columnOracle oStmt i) u) := by
  rw [table_sum_normalizedMultiplicity_eq_lookup_sum stmt oStmt hInput hM xChallenge]
  exact lookupMultiplicity_sum_div_eq_column_sum oStmt xChallenge

/-- **LogUp grand-sum identity, honest-oracle form.** The same identity, but written with the honest
multiplicity *oracle* `m = honestMultiplicity oStmt` on the left, matching the paper's
`∑_u m(u)/(x+t(u)) = ∑_i ∑_u 1/(x+f_i(u))`.

The left-hand summand is definitionally the count-form summand because
`evalOnHypercube (honestMultiplicity oStmt) u = normalizedMultiplicityValue oStmt u` by `rfl`. -/
theorem grandSum_identity_honest
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (hInput : (((stmt, oStmt), ()) ∈ inputRelation F n M))
    (hM : 0 < M) (xChallenge : F) :
    (∑ u : Hypercube n,
        evalOnHypercube (honestMultiplicity oStmt) u /
          (xChallenge + evalOnHypercube (tableOracle oStmt) u)) =
      ∑ i : Fin M, ∑ u : Hypercube n,
        (1 : F) / (xChallenge + evalOnHypercube (columnOracle oStmt i) u) := by
  -- `evalOnHypercube (honestMultiplicity oStmt) u = normalizedMultiplicityValue oStmt u`:
  -- `honestMultiplicity oStmt = ⟨normalizedMultiplicityValue oStmt⟩` and `evalOnHypercube p u = p u`
  -- with the `LagrangeOracle` `CoeFun` projecting `.values`. We unfold both definitions.
  have hpt : ∀ u : Hypercube n,
      evalOnHypercube (honestMultiplicity oStmt) u = normalizedMultiplicityValue oStmt u := by
    intro u
    simp [honestMultiplicity, evalOnHypercube]
  simp only [hpt]
  exact grandSum_identity stmt oStmt hInput hM xChallenge

/-- **Degenerate completeness sanity check.** With no columns (`M = 0`) the honest multiplicity is
identically `0`, so both sides of the grand-sum identity are `0`. This makes the `0 < M` hypothesis
of the main identity visibly tight (the table-count division only normalizes when columns exist) and
confirms the no-column boundary handled by `honestMultiplicity_eval_zero_no_columns`. -/
theorem grandSum_identity_no_columns
    (oStmt : ∀ i, OStmtIn F n 0 i) (xChallenge : F) :
    (∑ u : Hypercube n,
        evalOnHypercube (honestMultiplicity oStmt) u /
          (xChallenge + evalOnHypercube (tableOracle oStmt) u)) =
      ∑ i : Fin 0, ∑ u : Hypercube n,
        (1 : F) / (xChallenge + evalOnHypercube (columnOracle oStmt i) u) := by
  simp [honestMultiplicity_eval_zero_no_columns]

end GrandSumIdentity

/-! ## Per-row vanishing of the batched check polynomial under honest helpers -/

section PerRowVanishing

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n M K : ℕ}

/-- **Honest per-row collapse.** On any hypercube row `u`, evaluating the batched Protocol-2
expression `Q` at the honest helper oracles `h_k(u) = Σ_i m_i(u)/φ_i(u)` collapses the domain-
identity term to `0`, leaving `Q(u) = Σ_k h_k(u)`. This is the row-local algebra that the embedded
sumcheck reduces `∑_u Q(u) = ∑_u ∑_k h_k(u)` to. Re-exposes the in-tree
`qOnHypercube_honest_helpers`; the only hypothesis is pole-freeness of the denominators on this row
(supplied by the outer pole-rejection guard, whose failure probability is the proven
`probEvent_pole_le`). -/
theorem qOnHypercube_honest_collapse
    (groups : PartialSumGroups M K) (oStmt : ∀ i, OStmtIn F n M i)
    (multiplicity : MultilinearOracle F n) (xChallenge : F) (zChallenge : Fin n → F)
    (batchingScalars : Fin K → F) (u : Hypercube n)
    (hden : ∀ k : Fin K, ∀ i ∈ groups k, termPhi oStmt xChallenge i u ≠ 0) :
    qOnHypercube groups oStmt multiplicity
        (fun k => helperOracle groups oStmt multiplicity xChallenge k)
        xChallenge zChallenge batchingScalars u =
      ∑ k : Fin K, evalOnHypercube (helperOracle groups oStmt multiplicity xChallenge k) u :=
  qOnHypercube_honest_helpers groups oStmt multiplicity xChallenge zChallenge batchingScalars u hden

/-- **Final-point honest collapse.** The verifier's final check value `Q(...)` at the sumcheck point
`r`, with the claimed helper evaluations equal to the algebraic helper values and pole-free
denominators, equals `Σ_k helpers(k)`. Re-exposes `qAtPoint_eq_sum_helpers`: this is the soundness-
side companion (the cleared check the honest evaluations must satisfy). -/
theorem qAtPoint_honest_collapse
    (groups : PartialSumGroups M K) (xChallenge : F) (zChallenge rChallenge : Fin n → F)
    (batchingScalars : Fin K → F) (evals : PointEvaluations F M K)
    (hhelper : ∀ k : Fin K, evals.helpers k = helperValueAtPoint groups xChallenge evals k)
    (hden : ∀ k : Fin K, ∀ i ∈ groups k, termPhiAtPoint xChallenge evals i ≠ 0) :
    qAtPoint groups xChallenge zChallenge rChallenge batchingScalars evals =
      ∑ k : Fin K, evals.helpers k :=
  qAtPoint_eq_sum_helpers groups xChallenge zChallenge rChallenge batchingScalars evals hhelper hden

end PerRowVanishing

/-! ## Schwartz–Zippel soundness reduction for the LogUp Q polynomial -/

section SZSoundness

variable {F : Type} [Field F] [DecidableEq F] {n M : ℕ}
variable (params : ProtocolParams M)

/-- **SZ soundness bound for LogUp, reduced to the in-tree degree bound + ArkLib's
`prob_eval_zero_le_div`.**

Soundness of the LogUp algebraic check rests on Schwartz–Zippel: if the cleared-denominator check
polynomial `Q = logupQPolynomial …` is *nonzero* (the dishonest case), then a uniformly random
challenge point makes `Q` vanish with probability at most `totalDegree(Q) / |S|` per the SZ counting
lemma. Since every individual degree of `Q` is `≤ M + 3` (in-tree `logupQPolynomial_degreeOf`), the
total degree is `≤ n * (M + 3)`, giving the bound `n*(M+3) / |S|`.

We discharge everything via the confirmed ArkLib substrate `prob_eval_zero_le_div`
(`Data/MvPolynomial/SchwartzZippelCounting.lean`), supplying:
* `hQ_ne` : the dishonest-case nonvanishing of `Q` (the soundness premise),
* `hTotalDeg` : `Q.totalDegree ≤ n * (M + 3)` — the ONE arithmetic step from the per-variable
  `degreeOf ≤ M + 3` bound that we cannot name precisely with mathlib source unavailable. It is the
  standard `MvPolynomial.totalDegree_le` ⇐ `∑ᵢ degreeOf i` fact, here `∑_{i:Fin n} (M+3) = n*(M+3)`.
* the per-coordinate sampling domains `S` with at least `m` elements each.

This is the genuine SZ soundness content; only `hTotalDeg` remains as a named (purely arithmetic)
residual. -/
theorem logup_SZ_soundness
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i)
    (hQ_ne : logupQPolynomial F n M params stmt oStmt ≠ 0)
    (hTotalDeg : (logupQPolynomial F n M params stmt oStmt).totalDegree ≤ n * (M + 3))
    (S : Fin n → Set F) [∀ i, Fintype ↥(S i)] [∀ i, Nonempty ↥(S i)]
    (m : ℕ) (hm_pos : 0 < m) (hm : ∀ i, m ≤ (S i).toFinset.card) :
    Pr_{ let x ←$ᵖ (∀ i, ↥(S i)) }[
        MvPolynomial.eval (fun i => (↑(x i) : F)) (logupQPolynomial F n M params stmt oStmt) = 0 ]
      ≤ ((n * (M + 3) : ℕ) : ℝ≥0∞) / m :=
  prob_eval_zero_le_div
    (logupQPolynomial F n M params stmt oStmt) hQ_ne (n * (M + 3)) m hTotalDeg hm_pos hm

/-- **The per-variable degree bound is fully in-tree** (recorded here so the only genuine residual in
`logup_SZ_soundness` is the `totalDegree` aggregation `hTotalDeg`, not the degree analysis itself).
Every variable's individual degree in `Q` is `≤ M + 3`. -/
theorem logupQPolynomial_degreeOf_le
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (i : Fin n) :
    MvPolynomial.degreeOf i (logupQPolynomial F n M params stmt oStmt) ≤ M + 3 :=
  logupQPolynomial_degreeOf F n M params stmt oStmt i

end SZSoundness

end Issue13Scratch

end Logup
