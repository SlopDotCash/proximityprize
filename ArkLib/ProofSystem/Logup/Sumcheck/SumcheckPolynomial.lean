/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.MvPolynomial.Degrees
import ArkLib.ProofSystem.Logup.Common

/-!
# LogUp Sumcheck Polynomial

Constructs `logupQPolynomial`, an `MvPolynomial (Fin n) F` whose restriction to the signed
hypercube agrees with `qOnHypercube` from `Common.lean`, and proves its individual degree is
at most `M + 3`. Depends only on `Common.lean` and Mathlib — no ArkLib Sumcheck types.
-/

namespace Logup

open scoped BigOperators

section SumcheckPolynomial

variable (F : Type) [Field F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- The `{±1}` Lagrange basis polynomial for one hypercube row. -/
private noncomputable def signedBasisPolynomial (u : Hypercube n) :
    MvPolynomial (Fin n) F :=
  MvPolynomial.C (((2 : F) ^ n)⁻¹) *
    ∏ j : Fin n, (1 + MvPolynomial.C (bitToSign F (u j)) * MvPolynomial.X j)

/-- Multilinear extension of a function on the signed hypercube `{±1}ⁿ`. -/
private noncomputable def signedMLEPolynomial (values : Hypercube n → F) :
    MvPolynomial (Fin n) F :=
  ∑ u : Hypercube n, MvPolynomial.C (values u) * signedBasisPolynomial F n u

/-- The polynomial whose value at `r` is `L_H(r, z)`. -/
private noncomputable def lagrangeKernelPolynomial (z : Fin n → F) :
    MvPolynomial (Fin n) F :=
  MvPolynomial.C (((2 : F) ^ n)⁻¹) *
    ∏ j : Fin n, (1 + MvPolynomial.C (z j) * MvPolynomial.X j)

private theorem signedBasisPolynomial_eval (u : Hypercube n) (r : Fin n → F) :
    MvPolynomial.eval r (signedBasisPolynomial F n u) = lagrangeKernel F u r := by
  simp [signedBasisPolynomial, lagrangeKernel, lagrangeKernelAtPoint, signPoint]

private theorem signedMLEPolynomial_eval (values : Hypercube n → F) (r : Fin n → F) :
    MvPolynomial.eval r (signedMLEPolynomial F n values) =
      ∑ u : Hypercube n, values u * lagrangeKernel F u r := by
  simp [signedMLEPolynomial, signedBasisPolynomial_eval]

private theorem lagrangeKernelPolynomial_eval (z r : Fin n → F) :
    MvPolynomial.eval r (lagrangeKernelPolynomial F n z) =
      lagrangeKernelAtPoint F r z := by
  simp [lagrangeKernelPolynomial, lagrangeKernelAtPoint, mul_comm]

private theorem two_ne_zero_of_signsDistinct (hSigns : (-1 : F) ≠ 1) : (2 : F) ≠ 0 := by
  intro htwo
  apply hSigns
  have hsum : (1 : F) + 1 = 0 := by
    rw [← htwo]
    norm_num
  calc
    (-1 : F) = 1 := by
      rw [← sub_eq_zero]
      calc
        (-1 : F) - 1 = -((1 : F) + 1) := by ring
        _ = 0 := by rw [hsum]; ring

private theorem signFactor_same (b : Fin 2) :
    1 + bitToSign F b * bitToSign F b = (2 : F) := by
  fin_cases b <;> simp [bitToSign] <;> ring

private theorem signFactor_diff {a b : Fin 2} (hab : a ≠ b) :
    1 + bitToSign F a * bitToSign F b = (0 : F) := by
  fin_cases a <;> fin_cases b <;> simp [bitToSign] at hab ⊢

/-- The Lagrange kernel is a delta function on hypercube sign points: `L_H(v, signPoint u)`
is `1` when `v = u` and `0` otherwise. Exported (non-`private`) for the outer-verifier
run characterization in `Logup/Security/OuterRun.lean`. -/
theorem lagrangeKernel_signPoint
    (hSigns : (-1 : F) ≠ 1) (u v : Hypercube n) :
    lagrangeKernel F v (signPoint F u) = if v = u then 1 else 0 := by
  classical
  by_cases hvu : v = u
  · subst v
    simp only [lagrangeKernel, lagrangeKernelAtPoint, signPoint]
    have hprod :
        (∏ j : Fin n, (1 + bitToSign F (u j) * bitToSign F (u j))) = (2 : F) ^ n := by
      calc
        (∏ j : Fin n, (1 + bitToSign F (u j) * bitToSign F (u j))) =
            ∏ _j : Fin n, (2 : F) := by
              apply Finset.prod_congr rfl
              intro j _
              exact signFactor_same F (u j)
        _ = (2 : F) ^ (Finset.univ : Finset (Fin n)).card := by
              rw [Finset.prod_const]
        _ = (2 : F) ^ n := by simp
    rw [hprod]
    have hpow : (2 : F) ^ n ≠ 0 :=
      pow_ne_zero n (two_ne_zero_of_signsDistinct F hSigns)
    field_simp [hpow]
    simp
  · simp only [lagrangeKernel, lagrangeKernelAtPoint, signPoint]
    have hex : ∃ j : Fin n, v j ≠ u j := by
      by_contra h
      apply hvu
      funext j
      by_contra hj
      exact h ⟨j, hj⟩
    rcases hex with ⟨j, hj⟩
    have hprod :
        (∏ j : Fin n, (1 + bitToSign F (v j) * bitToSign F (u j))) = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ j) (signFactor_diff F hj)
    rw [hprod]
    simp [hvu]

private theorem signedMLEPolynomial_eval_signPoint
    (hSigns : (-1 : F) ≠ 1) (values : Hypercube n → F) (u : Hypercube n) :
    MvPolynomial.eval (signPoint F u) (signedMLEPolynomial F n values) = values u := by
  classical
  rw [signedMLEPolynomial_eval]
  rw [Finset.sum_eq_single u]
  · simp [lagrangeKernel_signPoint F n hSigns]
  · intro v _ hv
    simp [lagrangeKernel_signPoint F n hSigns, hv]
  · intro h
    exact False.elim (h (Finset.mem_univ u))

private theorem signedLinearFactor_degreeOf (a : F) (i j : Fin n) :
    MvPolynomial.degreeOf i (1 + MvPolynomial.C a * MvPolynomial.X j) ≤
      if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst i
    simp only [↓reduceIte]
    have hone :
        MvPolynomial.degreeOf j (1 : MvPolynomial (Fin n) F) ≤ 1 := by
      simp
    have hmul :
        MvPolynomial.degreeOf j (MvPolynomial.C a * MvPolynomial.X j) ≤ 1 := by
      calc
        _ ≤ MvPolynomial.degreeOf j (MvPolynomial.C a) +
            MvPolynomial.degreeOf j (MvPolynomial.X j) := by
          exact MvPolynomial.degreeOf_mul_le j _ _
        _ ≤ 0 + 1 := by
          gcongr
          · exact (MvPolynomial.degreeOf_C (R := F) a j).le
          · exact MvPolynomial.degreeOf_X_le (R := F) j j
        _ = 1 := by omega
    exact (MvPolynomial.degreeOf_add_le j _ _).trans (max_le hone hmul)
  · simp only [hij, ↓reduceIte]
    have hone :
        MvPolynomial.degreeOf i (1 : MvPolynomial (Fin n) F) ≤ 0 := by
      simp
    have hmul :
        MvPolynomial.degreeOf i (MvPolynomial.C a * MvPolynomial.X j) ≤ 0 := by
      calc
        _ ≤ MvPolynomial.degreeOf i (MvPolynomial.C a) +
            MvPolynomial.degreeOf i (MvPolynomial.X j) := by
          exact MvPolynomial.degreeOf_mul_le i _ _
        _ ≤ 0 + 0 := by
          gcongr
          · exact (MvPolynomial.degreeOf_C (R := F) a i).le
          · exact (MvPolynomial.degreeOf_X_of_ne (R := F) (i := i) (j := j) hij).le
        _ = 0 := by omega
    exact (MvPolynomial.degreeOf_add_le i _ _).trans (max_le hone hmul)

private theorem signedBasisPolynomial_degreeOf (u : Hypercube n) (i : Fin n) :
    MvPolynomial.degreeOf i (signedBasisPolynomial F n u) ≤ 1 := by
  calc
    _ ≤ MvPolynomial.degreeOf i (MvPolynomial.C (((2 : F) ^ n)⁻¹)) +
        MvPolynomial.degreeOf i
          (∏ j : Fin n, (1 + MvPolynomial.C (bitToSign F (u j)) * MvPolynomial.X j)) := by
      exact MvPolynomial.degreeOf_mul_le i _ _
    _ ≤ 0 +
        MvPolynomial.degreeOf i
          (∏ j : Fin n, (1 + MvPolynomial.C (bitToSign F (u j)) * MvPolynomial.X j)) := by
      gcongr
      exact (MvPolynomial.degreeOf_C (R := F) (((2 : F) ^ n)⁻¹) i).le
    _ =
        MvPolynomial.degreeOf i
          (∏ j : Fin n, (1 + MvPolynomial.C (bitToSign F (u j)) * MvPolynomial.X j)) := by
      simp
    _ ≤ ∑ j : Fin n,
        MvPolynomial.degreeOf i (1 + MvPolynomial.C (bitToSign F (u j)) * MvPolynomial.X j) := by
      exact MvPolynomial.degreeOf_prod_le i _ _
    _ ≤ ∑ j : Fin n, if i = j then 1 else 0 := by
      apply Finset.sum_le_sum
      intro j _
      exact signedLinearFactor_degreeOf F n (bitToSign F (u j)) i j
    _ = 1 := by
      norm_num

private theorem signedMLEPolynomial_degreeOf (values : Hypercube n → F) (i : Fin n) :
    MvPolynomial.degreeOf i (signedMLEPolynomial F n values) ≤ 1 := by
  classical
  calc
    _ ≤ (Finset.univ : Finset (Hypercube n)).sup
        fun u => MvPolynomial.degreeOf i
          (MvPolynomial.C (values u) * signedBasisPolynomial F n u) := by
      exact MvPolynomial.degreeOf_sum_le i _ _
    _ ≤ 1 := by
      apply Finset.sup_le
      intro u _
      calc
        MvPolynomial.degreeOf i (MvPolynomial.C (values u) * signedBasisPolynomial F n u)
            ≤ MvPolynomial.degreeOf i (MvPolynomial.C (values u)) +
              MvPolynomial.degreeOf i (signedBasisPolynomial F n u) := by
          exact MvPolynomial.degreeOf_mul_le i _ _
        _ ≤ 0 + 1 := by
          gcongr
          · exact (MvPolynomial.degreeOf_C (R := F) (values u) i).le
          · exact signedBasisPolynomial_degreeOf F n u i
        _ = 1 := by omega

private theorem lagrangeKernelPolynomial_degreeOf (z : Fin n → F) (i : Fin n) :
    MvPolynomial.degreeOf i (lagrangeKernelPolynomial F n z) ≤ 1 := by
  calc
    _ ≤ MvPolynomial.degreeOf i (MvPolynomial.C (((2 : F) ^ n)⁻¹)) +
        MvPolynomial.degreeOf i
          (∏ j : Fin n, (1 + MvPolynomial.C (z j) * MvPolynomial.X j)) := by
      exact MvPolynomial.degreeOf_mul_le i _ _
    _ ≤ 0 +
        MvPolynomial.degreeOf i
          (∏ j : Fin n, (1 + MvPolynomial.C (z j) * MvPolynomial.X j)) := by
      gcongr
      exact (MvPolynomial.degreeOf_C (R := F) (((2 : F) ^ n)⁻¹) i).le
    _ =
        MvPolynomial.degreeOf i
          (∏ j : Fin n, (1 + MvPolynomial.C (z j) * MvPolynomial.X j)) := by
      simp
    _ ≤ ∑ j : Fin n,
        MvPolynomial.degreeOf i (1 + MvPolynomial.C (z j) * MvPolynomial.X j) := by
      exact MvPolynomial.degreeOf_prod_le i _ _
    _ ≤ ∑ j : Fin n, if i = j then 1 else 0 := by
      apply Finset.sum_le_sum
      intro j _
      exact signedLinearFactor_degreeOf F n (z j) i j
    _ = 1 := by
      norm_num

/-- Polynomial extension of one retained Lagrange-form multilinear oracle. -/
private noncomputable def multilinearOraclePolynomial (oracle : MultilinearOracle F n) :
    MvPolynomial (Fin n) F :=
  signedMLEPolynomial F n fun u => evalOnHypercube oracle u

private theorem multilinearOraclePolynomial_eval (oracle : MultilinearOracle F n)
    (r : Fin n → F) :
    MvPolynomial.eval r (multilinearOraclePolynomial F n oracle) =
      lagrangeOracleEval oracle r := by
  simp [multilinearOraclePolynomial, signedMLEPolynomial_eval, lagrangeOracleEval,
    evalOnHypercube]

private theorem multilinearOraclePolynomial_eval_signPoint
    (hSigns : (-1 : F) ≠ 1) (oracle : MultilinearOracle F n) (u : Hypercube n) :
    MvPolynomial.eval (signPoint F u) (multilinearOraclePolynomial F n oracle) =
      evalOnHypercube oracle u := by
  simpa [multilinearOraclePolynomial, evalOnHypercube] using
    signedMLEPolynomial_eval_signPoint F n hSigns (fun u => evalOnHypercube oracle u) u

private noncomputable def inputOraclePolynomial
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (idx : InputOracleIdx M) :
    MvPolynomial (Fin n) F :=
  match idx with
  | .table => multilinearOraclePolynomial F n (oStmt (.input .table))
  | .column i => multilinearOraclePolynomial F n (oStmt (.input (.column i)))

private noncomputable def multiplicityPolynomial
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) :
    MvPolynomial (Fin n) F :=
  multilinearOraclePolynomial F n (oStmt .multiplicity)

private noncomputable def helperPolynomial
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (k : Fin params.numGroups) :
    MvPolynomial (Fin n) F :=
  multilinearOraclePolynomial F n ((oStmt .helpers) k)

private noncomputable def termPhiPolynomial
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (i : TermIdx M) :
    MvPolynomial (Fin n) F :=
  MvPolynomial.C stmt.xChallenge + inputOraclePolynomial F n M params oStmt (termToInput i)

private noncomputable def termNumeratorPolynomial
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (i : TermIdx M) :
    MvPolynomial (Fin n) F :=
  match termToInput i with
  | .table => multiplicityPolynomial F n M params oStmt
  | .column _ => MvPolynomial.C (-1)

private noncomputable def domainIdentityPolynomial
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (k : Fin params.numGroups) :
    MvPolynomial (Fin n) F :=
  helperPolynomial F n M params oStmt k *
      (∏ i ∈ canonicalGroups params k, termPhiPolynomial F n M params stmt oStmt i) -
    ∑ i ∈ canonicalGroups params k,
      termNumeratorPolynomial F n M params oStmt i *
        ∏ j ∈ (canonicalGroups params k).erase i,
          termPhiPolynomial F n M params stmt oStmt j

private theorem inputOraclePolynomial_eval
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (idx : InputOracleIdx M)
    (r : Fin n → F) :
    MvPolynomial.eval r (inputOraclePolynomial F n M params oStmt idx) =
      match idx with
      | .table => lagrangeOracleEval (oStmt (.input .table)) r
      | .column i => lagrangeOracleEval (oStmt (.input (.column i))) r := by
  cases idx with
  | table =>
      simpa [inputOraclePolynomial] using
        multilinearOraclePolynomial_eval F n (oStmt (.input .table)) r
  | column i =>
      simpa [inputOraclePolynomial] using
        multilinearOraclePolynomial_eval F n (oStmt (.input (.column i))) r

private theorem inputOraclePolynomial_eval_signPoint
    (hSigns : (-1 : F) ≠ 1)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (idx : InputOracleIdx M)
    (u : Hypercube n) :
    MvPolynomial.eval (signPoint F u) (inputOraclePolynomial F n M params oStmt idx) =
      match idx with
      | .table => evalOnHypercube (oStmt (.input .table)) u
      | .column i => evalOnHypercube (oStmt (.input (.column i))) u := by
  cases idx with
  | table =>
      simpa [inputOraclePolynomial] using
        multilinearOraclePolynomial_eval_signPoint F n hSigns (oStmt (.input .table)) u
  | column i =>
      simpa [inputOraclePolynomial] using
        multilinearOraclePolynomial_eval_signPoint F n hSigns (oStmt (.input (.column i))) u

private theorem multiplicityPolynomial_eval
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (r : Fin n → F) :
    MvPolynomial.eval r (multiplicityPolynomial F n M params oStmt) =
      lagrangeOracleEval (oStmt .multiplicity) r :=
  multilinearOraclePolynomial_eval F n (oStmt .multiplicity) r

private theorem multiplicityPolynomial_eval_signPoint
    (hSigns : (-1 : F) ≠ 1)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (u : Hypercube n) :
    MvPolynomial.eval (signPoint F u) (multiplicityPolynomial F n M params oStmt) =
      evalOnHypercube (oStmt .multiplicity) u :=
  multilinearOraclePolynomial_eval_signPoint F n hSigns (oStmt .multiplicity) u

private theorem helperPolynomial_eval
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (k : Fin params.numGroups)
    (r : Fin n → F) :
    MvPolynomial.eval r (helperPolynomial F n M params oStmt k) =
      lagrangeOracleEval ((oStmt .helpers) k) r :=
  multilinearOraclePolynomial_eval F n ((oStmt .helpers) k) r

private theorem helperPolynomial_eval_signPoint
    (hSigns : (-1 : F) ≠ 1)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (k : Fin params.numGroups)
    (u : Hypercube n) :
    MvPolynomial.eval (signPoint F u) (helperPolynomial F n M params oStmt k) =
      evalOnHypercube ((oStmt .helpers) k) u :=
  multilinearOraclePolynomial_eval_signPoint F n hSigns ((oStmt .helpers) k) u

private theorem termPhiPolynomial_eval_eq_termPhi
    (hSigns : (-1 : F) ≠ 1)
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i)
    (u : Hypercube n) (i : TermIdx M) :
    MvPolynomial.eval (signPoint F u) (termPhiPolynomial F n M params stmt oStmt i) =
      termPhi (fun i => oStmt (.input i)) stmt.xChallenge i u := by
  unfold termPhiPolynomial termPhi phi
  cases hidx : termToInput i with
  | table =>
      simp [inputOraclePolynomial_eval_signPoint, hSigns]
  | column j =>
      simp [inputOraclePolynomial_eval_signPoint, hSigns]

private theorem termNumeratorPolynomial_eval_eq_termNumerator
    (hSigns : (-1 : F) ≠ 1)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i)
    (u : Hypercube n) (i : TermIdx M) :
    MvPolynomial.eval (signPoint F u) (termNumeratorPolynomial F n M params oStmt i) =
      termNumerator (oStmt .multiplicity) i u := by
  unfold termNumeratorPolynomial termNumerator numerator
  cases hidx : termToInput i with
  | table =>
      simp [multiplicityPolynomial_eval_signPoint, hSigns]
  | column j =>
      simp

private theorem domainIdentityPolynomial_eval_eq_domainIdentityTerm
    (hSigns : (-1 : F) ≠ 1)
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i)
    (u : Hypercube n) (k : Fin params.numGroups) :
    MvPolynomial.eval (signPoint F u) (domainIdentityPolynomial F n M params stmt oStmt k) =
      domainIdentityTerm (canonicalGroups params) (fun i => oStmt (.input i))
        (oStmt .multiplicity) (oStmt .helpers) stmt.xChallenge k u := by
  unfold domainIdentityPolynomial domainIdentityTerm denominatorProduct
  simp [helperPolynomial_eval_signPoint, hSigns,
    termPhiPolynomial_eval_eq_termPhi F n M params hSigns stmt oStmt u,
    termNumeratorPolynomial_eval_eq_termNumerator F n M params hSigns oStmt u]

private theorem termPhiPolynomial_eval_eq_termPhiAtPoint
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i)
    (r : Fin n → F) (evals : PointEvaluations F M params.numGroups)
    (htable : evals.table = lagrangeOracleEval (oStmt (.input .table)) r)
    (hcolumns : ∀ i : Fin M, evals.columns i =
      lagrangeOracleEval (oStmt (.input (.column i))) r)
    (i : TermIdx M) :
    MvPolynomial.eval r (termPhiPolynomial F n M params stmt oStmt i) =
      termPhiAtPoint stmt.xChallenge evals i := by
  unfold termPhiPolynomial termPhiAtPoint phiAtPoint
  cases hidx : termToInput i with
  | table =>
      simp [inputOraclePolynomial_eval, htable]
  | column j =>
      simp [inputOraclePolynomial_eval, hcolumns j]

private theorem termNumeratorPolynomial_eval_eq_termNumeratorAtPoint
    (oStmt : ∀ i, OStmtAfterOuter F n M params i)
    (r : Fin n → F) (evals : PointEvaluations F M params.numGroups)
    (hmultiplicity : evals.multiplicity = lagrangeOracleEval (oStmt .multiplicity) r)
    (i : TermIdx M) :
    MvPolynomial.eval r (termNumeratorPolynomial F n M params oStmt i) =
      termNumeratorAtPoint evals i := by
  unfold termNumeratorPolynomial termNumeratorAtPoint numeratorAtPoint
  cases hidx : termToInput i with
  | table =>
      simp [multiplicityPolynomial_eval, hmultiplicity]
  | column j =>
      simp

private theorem domainIdentityPolynomial_eval_eq_domainIdentityAtPoint
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i)
    (r : Fin n → F) (evals : PointEvaluations F M params.numGroups)
    (hmultiplicity : evals.multiplicity = lagrangeOracleEval (oStmt .multiplicity) r)
    (htable : evals.table = lagrangeOracleEval (oStmt (.input .table)) r)
    (hcolumns : ∀ i : Fin M, evals.columns i =
      lagrangeOracleEval (oStmt (.input (.column i))) r)
    (hhelpers : ∀ k : Fin params.numGroups, evals.helpers k =
      lagrangeOracleEval ((oStmt .helpers) k) r)
    (k : Fin params.numGroups) :
    MvPolynomial.eval r (domainIdentityPolynomial F n M params stmt oStmt k) =
      domainIdentityAtPoint (canonicalGroups params) stmt.xChallenge evals k := by
  unfold domainIdentityPolynomial domainIdentityAtPoint
  simp [helperPolynomial_eval, hhelpers k,
    termPhiPolynomial_eval_eq_termPhiAtPoint F n M params stmt oStmt r evals htable hcolumns,
    termNumeratorPolynomial_eval_eq_termNumeratorAtPoint F n M params oStmt r evals
      hmultiplicity]

private theorem multilinearOraclePolynomial_degreeOf (oracle : MultilinearOracle F n)
    (i : Fin n) :
    MvPolynomial.degreeOf i (multilinearOraclePolynomial F n oracle) ≤ 1 := by
  simpa [multilinearOraclePolynomial] using
    signedMLEPolynomial_degreeOf F n (fun u => evalOnHypercube oracle u) i

private theorem inputOraclePolynomial_degreeOf
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (idx : InputOracleIdx M)
    (i : Fin n) :
    MvPolynomial.degreeOf i (inputOraclePolynomial F n M params oStmt idx) ≤ 1 := by
  cases idx with
  | table =>
      simpa [inputOraclePolynomial] using
        multilinearOraclePolynomial_degreeOf F n (oStmt (.input .table)) i
  | column j =>
      simpa [inputOraclePolynomial] using
        multilinearOraclePolynomial_degreeOf F n (oStmt (.input (.column j))) i

private theorem multiplicityPolynomial_degreeOf
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (i : Fin n) :
    MvPolynomial.degreeOf i (multiplicityPolynomial F n M params oStmt) ≤ 1 :=
  multilinearOraclePolynomial_degreeOf F n (oStmt .multiplicity) i

private theorem helperPolynomial_degreeOf
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (k : Fin params.numGroups)
    (i : Fin n) :
    MvPolynomial.degreeOf i (helperPolynomial F n M params oStmt k) ≤ 1 :=
  multilinearOraclePolynomial_degreeOf F n ((oStmt .helpers) k) i

private theorem termPhiPolynomial_degreeOf
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (j : TermIdx M) (i : Fin n) :
    MvPolynomial.degreeOf i (termPhiPolynomial F n M params stmt oStmt j) ≤ 1 := by
  calc
    _ ≤ max (MvPolynomial.degreeOf i (MvPolynomial.C stmt.xChallenge))
        (MvPolynomial.degreeOf i (inputOraclePolynomial F n M params oStmt (termToInput j))) := by
      exact MvPolynomial.degreeOf_add_le i _ _
    _ ≤ max 0 1 := by
      gcongr
      · exact (MvPolynomial.degreeOf_C (R := F) stmt.xChallenge i).le
      · exact inputOraclePolynomial_degreeOf F n M params oStmt (termToInput j) i
    _ = 1 := by
      omega

private theorem termNumeratorPolynomial_degreeOf
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (j : TermIdx M) (i : Fin n) :
    MvPolynomial.degreeOf i (termNumeratorPolynomial F n M params oStmt j) ≤ 1 := by
  unfold termNumeratorPolynomial
  cases h : termToInput j with
  | table =>
      simpa [h, multiplicityPolynomial] using
        multiplicityPolynomial_degreeOf F n M params oStmt i
  | column c =>
      exact (MvPolynomial.degreeOf_C (R := F) (-1 : F) i).le.trans (by omega)

private theorem finset_card_termIdx_le (s : Finset (TermIdx M)) :
    s.card ≤ M + 1 := by
  simpa [TermIdx] using Finset.card_le_univ (s := s)

private theorem termPhiPolynomial_prod_degreeOf
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (s : Finset (TermIdx M))
    (i : Fin n) :
    MvPolynomial.degreeOf i
        (∏ j ∈ s, termPhiPolynomial F n M params stmt oStmt j) ≤ M + 1 := by
  calc
    _ ≤ ∑ j ∈ s,
        MvPolynomial.degreeOf i (termPhiPolynomial F n M params stmt oStmt j) := by
      exact MvPolynomial.degreeOf_prod_le i _ _
    _ ≤ ∑ _j ∈ s, 1 := by
      apply Finset.sum_le_sum
      intro j _
      exact termPhiPolynomial_degreeOf F n M params stmt oStmt j i
    _ = s.card := by
      simp
    _ ≤ M + 1 := finset_card_termIdx_le M s

private theorem domainIdentityPolynomial_degreeOf
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (k : Fin params.numGroups)
    (i : Fin n) :
    MvPolynomial.degreeOf i (domainIdentityPolynomial F n M params stmt oStmt k) ≤ M + 2 := by
  unfold domainIdentityPolynomial
  have hProd :
      MvPolynomial.degreeOf i
        (∏ j ∈ canonicalGroups params k, termPhiPolynomial F n M params stmt oStmt j) ≤
          M + 1 :=
    termPhiPolynomial_prod_degreeOf F n M params stmt oStmt (canonicalGroups params k) i
  have hLeft :
      MvPolynomial.degreeOf i
        (helperPolynomial F n M params oStmt k *
          (∏ j ∈ canonicalGroups params k, termPhiPolynomial F n M params stmt oStmt j)) ≤
        M + 2 := by
    calc
      _ ≤ MvPolynomial.degreeOf i (helperPolynomial F n M params oStmt k) +
          MvPolynomial.degreeOf i
            (∏ j ∈ canonicalGroups params k,
              termPhiPolynomial F n M params stmt oStmt j) := by
        exact MvPolynomial.degreeOf_mul_le i _ _
      _ ≤ 1 + (M + 1) := by
        gcongr
        exact helperPolynomial_degreeOf F n M params oStmt k i
      _ = M + 2 := by
        omega
  have hRight :
      MvPolynomial.degreeOf i
        (∑ j ∈ canonicalGroups params k,
          termNumeratorPolynomial F n M params oStmt j *
            ∏ l ∈ (canonicalGroups params k).erase j,
              termPhiPolynomial F n M params stmt oStmt l) ≤
        M + 2 := by
    calc
      _ ≤ (canonicalGroups params k).sup fun j =>
          MvPolynomial.degreeOf i
            (termNumeratorPolynomial F n M params oStmt j *
              ∏ l ∈ (canonicalGroups params k).erase j,
                termPhiPolynomial F n M params stmt oStmt l) := by
        exact MvPolynomial.degreeOf_sum_le i _ _
      _ ≤ M + 2 := by
        apply Finset.sup_le
        intro j _
        have hEraseProd :
            MvPolynomial.degreeOf i
              (∏ l ∈ (canonicalGroups params k).erase j,
                termPhiPolynomial F n M params stmt oStmt l) ≤ M + 1 :=
          termPhiPolynomial_prod_degreeOf F n M params stmt oStmt
            ((canonicalGroups params k).erase j) i
        calc
          _ ≤ MvPolynomial.degreeOf i (termNumeratorPolynomial F n M params oStmt j) +
              MvPolynomial.degreeOf i
                (∏ l ∈ (canonicalGroups params k).erase j,
                  termPhiPolynomial F n M params stmt oStmt l) := by
            exact MvPolynomial.degreeOf_mul_le i _ _
          _ ≤ 1 + (M + 1) := by
            gcongr
            exact termNumeratorPolynomial_degreeOf F n M params oStmt j i
          _ = M + 2 := by
            omega
  exact (MvPolynomial.degreeOf_sub_le i _ _).trans (max_le hLeft hRight)

/-- The concrete multivariate LogUp sumcheck polynomial before packaging with its degree proof. -/
noncomputable def logupQPolynomial
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) :
    MvPolynomial (Fin n) F :=
  ∑ k : Fin params.numGroups, (
    helperPolynomial F n M params oStmt k +
      lagrangeKernelPolynomial F n stmt.zChallenge *
        MvPolynomial.C (stmt.batchingScalars k) *
          domainIdentityPolynomial F n M params stmt oStmt k)

/-- On the signed hypercube, the concrete `Q` polynomial is exactly the row expression from
LogUp's outer algebra. -/
theorem logupQPolynomial_eval_signPoint_eq_qOnHypercube
    (hSigns : (-1 : F) ≠ 1)
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i)
    (u : Hypercube n) :
    MvPolynomial.eval (signPoint F u) (logupQPolynomial F n M params stmt oStmt) =
      qOnHypercube (canonicalGroups params) (fun i => oStmt (.input i)) (oStmt .multiplicity)
        (oStmt .helpers) stmt.xChallenge stmt.zChallenge stmt.batchingScalars u := by
  simp [logupQPolynomial, qOnHypercube, helperPolynomial_eval_signPoint, hSigns,
    lagrangeKernelPolynomial_eval, lagrangeKernelAtPoint, lagrangeKernel, signPoint,
    domainIdentityPolynomial_eval_eq_domainIdentityTerm F n M params hSigns stmt oStmt u]

/-- Evaluating the concrete LogUp sumcheck polynomial at the final verifier point recovers the
value reconstructed by LogUp's final oracle-query check. -/
theorem logupQPolynomial_eval_eq_qAtPoint
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i)
    (r : Fin n → F) (evals : PointEvaluations F M params.numGroups)
    (hmultiplicity : evals.multiplicity = lagrangeOracleEval (oStmt .multiplicity) r)
    (htable : evals.table = lagrangeOracleEval (oStmt (.input .table)) r)
    (hcolumns : ∀ i : Fin M, evals.columns i =
      lagrangeOracleEval (oStmt (.input (.column i))) r)
    (hhelpers : ∀ k : Fin params.numGroups, evals.helpers k =
      lagrangeOracleEval ((oStmt .helpers) k) r) :
    MvPolynomial.eval r (logupQPolynomial F n M params stmt oStmt) =
      qAtPoint (canonicalGroups params) stmt.xChallenge stmt.zChallenge r
        stmt.batchingScalars evals := by
  simp [logupQPolynomial, qAtPoint, helperPolynomial_eval, hhelpers, lagrangeKernelPolynomial_eval,
    domainIdentityPolynomial_eval_eq_domainIdentityAtPoint F n M params stmt oStmt r evals
      hmultiplicity htable hcolumns hhelpers]

theorem logupQPolynomial_degreeOf
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) (i : Fin n) :
    MvPolynomial.degreeOf i (logupQPolynomial F n M params stmt oStmt) ≤ M + 3 := by
  classical
  unfold logupQPolynomial
  calc
    _ ≤ (Finset.univ : Finset (Fin params.numGroups)).sup fun k =>
        MvPolynomial.degreeOf i
          (helperPolynomial F n M params oStmt k +
            lagrangeKernelPolynomial F n stmt.zChallenge *
              MvPolynomial.C (stmt.batchingScalars k) *
                domainIdentityPolynomial F n M params stmt oStmt k) := by
      exact MvPolynomial.degreeOf_sum_le i _ _
    _ ≤ M + 3 := by
      apply Finset.sup_le
      intro k _
      have hHelper : MvPolynomial.degreeOf i (helperPolynomial F n M params oStmt k) ≤ M + 3 :=
        (helperPolynomial_degreeOf F n M params oStmt k i).trans (by omega)
      have hProduct :
          MvPolynomial.degreeOf i
            (lagrangeKernelPolynomial F n stmt.zChallenge *
              MvPolynomial.C (stmt.batchingScalars k) *
                domainIdentityPolynomial F n M params stmt oStmt k) ≤ M + 3 := by
        calc
          _ ≤ MvPolynomial.degreeOf i
                (lagrangeKernelPolynomial F n stmt.zChallenge *
                  MvPolynomial.C (stmt.batchingScalars k)) +
              MvPolynomial.degreeOf i
                (domainIdentityPolynomial F n M params stmt oStmt k) := by
            exact MvPolynomial.degreeOf_mul_le i _ _
          _ ≤ (MvPolynomial.degreeOf i (lagrangeKernelPolynomial F n stmt.zChallenge) +
                MvPolynomial.degreeOf i (MvPolynomial.C (stmt.batchingScalars k))) +
              MvPolynomial.degreeOf i
                (domainIdentityPolynomial F n M params stmt oStmt k) := by
            gcongr
            exact MvPolynomial.degreeOf_mul_le i _ _
          _ ≤ (1 + 0) + (M + 2) := by
            gcongr
            · exact lagrangeKernelPolynomial_degreeOf F n stmt.zChallenge i
            · exact (MvPolynomial.degreeOf_C (R := F) (stmt.batchingScalars k) i).le
            · exact domainIdentityPolynomial_degreeOf F n M params stmt oStmt k i
          _ = M + 3 := by
            omega
      exact (MvPolynomial.degreeOf_add_le i _ _).trans (max_le hHelper hProduct)

end SumcheckPolynomial

end Logup
