/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Sumcheck.SumcheckPolynomial
import ArkLib.ProofSystem.Sumcheck.Spec.General

/-!
# LogUp Sumcheck Bridge

Packages `logupQPolynomial` from `SumcheckPolynomial.lean` into ArkLib's Sumcheck interface
types, then connects it to the generic Sumcheck relation, verifier, reduction, and context lift.
-/

namespace Logup

open scoped BigOperators

section SumcheckInterface

variable (F : Type) [Field F] [Fintype F] [DecidableEq F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- Individual-degree bound for LogUp's embedded sumcheck polynomial. -/
def logupSumcheckDegree (_params : ProtocolParams M) : ℕ :=
  M + 3

/-- The concrete ArkLib Sumcheck transcript shape for LogUp's embedded sumcheck. -/
abbrev logupSumcheckPSpec : ProtocolSpec (Fin.vsum (fun _ : Fin n => 2)) :=
  Sumcheck.Spec.pSpec F (logupSumcheckDegree M params) n

/-- The generic sumcheck input statement used by LogUp: target `0`, no prior challenges. -/
abbrev LogupSumcheckStmtIn (_params : ProtocolParams M) : Type :=
  Sumcheck.Spec.StatementRound F n 0

/-- The generic sumcheck output statement: the final claim at verifier point `r`. -/
abbrev LogupSumcheckStmtOut (_params : ProtocolParams M) : Type :=
  Sumcheck.Spec.StatementRound F n (.last n)

/-- The generic sumcheck oracle statement: LogUp's bounded-degree `Q` polynomial. -/
abbrev LogupSumcheckOracleStatement : Unit → Type :=
  Sumcheck.Spec.OracleStatement F n (logupSumcheckDegree M params)

/-- LogUp enters the embedded sumcheck with the zero-sum claim. -/
def logupInitialSumcheckStatement : LogupSumcheckStmtIn F n M params where
  target := 0
  challenges := fun i => Fin.elim0 i

/-- Package `logupQPolynomial` with its degree certificate into ArkLib's oracle statement type. -/
noncomputable def logupSumcheckPolynomial
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) :
    LogupSumcheckOracleStatement F n M params () := by
  classical
  exact ⟨logupQPolynomial F n M params stmt oStmt, by
    rw [MvPolynomial.mem_restrictDegree_iff_degreeOf_le]
    intro i
    exact logupQPolynomial_degreeOf F n M params stmt oStmt i⟩

/-- Package the LogUp `Q` polynomial as the single oracle statement expected by Sumcheck. -/
noncomputable def logupSumcheckOracleStmt
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) :
    ∀ i, LogupSumcheckOracleStatement F n M params i :=
  fun _ => logupSumcheckPolynomial F n M params stmt oStmt

/-- The row-wise claim that `logupQPolynomial` agrees with `qOnHypercube` on `H`. -/
def logupSumcheckPolynomialRowsAgree
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) : Prop :=
  ∀ u : Hypercube n,
    MvPolynomial.eval (signPoint F u) (logupSumcheckPolynomial F n M params stmt oStmt).1 =
      qOnHypercube (canonicalGroups params) (fun i => oStmt (.input i)) (oStmt .multiplicity)
        (oStmt .helpers) stmt.xChallenge stmt.zChallenge stmt.batchingScalars u

omit [Fintype F] [DecidableEq F] in
theorem logupSumcheckPolynomialRowsAgree_of_signsDistinct
    (hSigns : (-1 : F) ≠ 1)
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) :
    logupSumcheckPolynomialRowsAgree F n M params stmt oStmt := by
  intro u
  simpa [logupSumcheckPolynomial] using
    logupQPolynomial_eval_signPoint_eq_qOnHypercube
      (F := F) (n := n) (M := M) (params := params) hSigns stmt oStmt u

/-- The LogUp zero-sum claim that is fed to the generic sumcheck. -/
noncomputable def logupOuterSumcheckClaim
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) : F :=
  ∑ u : Hypercube n,
    qOnHypercube (canonicalGroups params) (fun i => oStmt (.input i)) (oStmt .multiplicity)
      (oStmt .helpers) stmt.xChallenge stmt.zChallenge stmt.batchingScalars u

theorem logupOuterSumcheckClaim_honestHelpers_eq_sum_helpers
    (stmtIn : StmtIn F n M)
    (oStmtIn : ∀ i, OStmtIn F n M i)
    (stmt : StmtAfterOuter F n M params)
    (hInput : (((stmtIn, oStmtIn), ()) ∈ inputRelation F n M))
    (htable : ∀ u : Hypercube n,
      stmt.xChallenge + evalOnHypercube (tableOracle oStmtIn) u ≠ 0) :
    logupOuterSumcheckClaim F n M params stmt
      (fun
        | .input i => oStmtIn i
        | .multiplicity => honestMultiplicity oStmtIn
        | .helpers => honestHelpers params oStmtIn stmt.xChallenge) =
      ∑ u : Hypercube n,
        ∑ k : Fin params.numGroups,
          evalOnHypercube (honestHelpers params oStmtIn stmt.xChallenge k) u := by
  unfold logupOuterSumcheckClaim
  apply Finset.sum_congr rfl
  intro u _
  have hden :
      ∀ k : Fin params.numGroups, ∀ i ∈ canonicalGroups params k,
        termPhi oStmtIn stmt.xChallenge i u ≠ 0 := by
    intro _ i _
    exact termPhi_ne_zero_of_inputRelation_of_table
      stmtIn oStmtIn stmt.xChallenge hInput htable i u
  simpa [honestHelpers] using
    qOnHypercube_honest_helpers (groups := canonicalGroups params)
      oStmtIn (honestMultiplicity oStmtIn) stmt.xChallenge stmt.zChallenge
      stmt.batchingScalars u hden

omit [Fintype F] [DecidableEq F] in
theorem canonicalGroups_sum_partition (f : TermIdx M → F) :
    (∑ k : Fin params.numGroups, ∑ i ∈ canonicalGroups params k, f i) =
      ∑ i : TermIdx M, f i := by
  classical
  simp only [canonicalGroups]
  rw [Finset.sum_sigma' (s := (Finset.univ : Finset (Fin params.numGroups)))
    (t := fun k => params.group k) (f := fun _ i => f i)]
  refine Finset.sum_bij (s := (Finset.univ.sigma fun k => params.group k))
    (t := (Finset.univ : Finset (TermIdx M))) (i := fun x _ => x.2) ?_ ?_ ?_ ?_
  · intro x _
    exact Finset.mem_univ x.2
  · intro x hx y hy hxy
    rcases x with ⟨kx, ix⟩
    rcases y with ⟨ky, iy⟩
    change ix = iy at hxy
    have hfst : kx = ky := by
      apply params.group_eq_of_mem (i := ix)
      · exact (Finset.mem_sigma.mp hx).2
      · rw [hxy]
        exact (Finset.mem_sigma.mp hy).2
    cases hfst
    cases hxy
    rfl
  · intro i _
    rcases params.exists_mem_group i with ⟨k, hk⟩
    exact ⟨Sigma.mk k i, Finset.mem_sigma.mpr ⟨Finset.mem_univ k, hk⟩, rfl⟩
  · intro x _
    rfl

omit [Fintype F] in
theorem honest_helper_sum_eq_sum_terms
    (oStmt : ∀ i, OStmtIn F n M i) (xChallenge : F) (u : Hypercube n) :
    (∑ k : Fin params.numGroups,
        evalOnHypercube (honestHelpers params oStmt xChallenge k) u) =
      ∑ i : TermIdx M,
        termNumerator (honestMultiplicity oStmt) i u / termPhi oStmt xChallenge i u := by
  simpa [honestHelpers, helperOracle, helperValue, evalOnHypercube] using
    canonicalGroups_sum_partition (params := params)
      (f := fun i : TermIdx M =>
        termNumerator (honestMultiplicity oStmt) i u / termPhi oStmt xChallenge i u)

omit [Fintype F] in
theorem sum_terms_eq_table_add_columns
    (oStmt : ∀ i, OStmtIn F n M i) (xChallenge : F) (u : Hypercube n) :
    (∑ i : TermIdx M,
        termNumerator (honestMultiplicity oStmt) i u / termPhi oStmt xChallenge i u) =
      evalOnHypercube (honestMultiplicity oStmt) u /
        (xChallenge + evalOnHypercube (tableOracle oStmt) u) +
        ∑ i : Fin M,
          (-1 : F) / (xChallenge + evalOnHypercube (columnOracle oStmt i) u) := by
  change (∑ i : Fin (M + 1),
        termNumerator (honestMultiplicity oStmt) i u / termPhi oStmt xChallenge i u) = _
  rw [Fin.sum_univ_succ]
  congr 1

omit [Fintype F] in
theorem sum_terms_zero_no_columns
    (oStmt : ∀ i, OStmtIn F n 0 i) (xChallenge : F) (u : Hypercube n) :
    (∑ i : TermIdx 0,
        termNumerator (honestMultiplicity oStmt) i u / termPhi oStmt xChallenge i u) = 0 := by
  rw [sum_terms_eq_table_add_columns (F := F) (n := n) (M := 0) oStmt xChallenge u]
  simp [honestMultiplicity_eval_zero_no_columns]

omit [Fintype F] in
theorem honest_helper_sum_zero_no_columns
    (params : ProtocolParams 0) (oStmt : ∀ i, OStmtIn F n 0 i) (xChallenge : F) :
    (∑ u : Hypercube n,
      ∑ k : Fin params.numGroups,
        evalOnHypercube (honestHelpers params oStmt xChallenge k) u) = 0 := by
  apply Finset.sum_eq_zero
  intro u _
  rw [honest_helper_sum_eq_sum_terms
    (F := F) (n := n) (M := 0) (params := params) oStmt xChallenge u]
  exact sum_terms_zero_no_columns (F := F) (n := n) oStmt xChallenge u

theorem honest_helper_sum_zero_of_inputRelation
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (hInput : (((stmt, oStmt), ()) ∈ inputRelation F n M))
    (hM : 0 < M) (xChallenge : F) :
    (∑ u : Hypercube n,
      ∑ k : Fin params.numGroups,
        evalOnHypercube (honestHelpers params oStmt xChallenge k) u) = 0 := by
  have hhelpers_eq_terms :
      (∑ u : Hypercube n,
        ∑ k : Fin params.numGroups,
          evalOnHypercube (honestHelpers params oStmt xChallenge k) u) =
        ∑ u : Hypercube n,
          ∑ i : TermIdx M,
            termNumerator (honestMultiplicity oStmt) i u /
              termPhi oStmt xChallenge i u := by
    apply Finset.sum_congr rfl
    intro u _
    exact honest_helper_sum_eq_sum_terms
      (F := F) (n := n) (M := M) (params := params) oStmt xChallenge u
  have hterms_split :
      (∑ u : Hypercube n,
          ∑ i : TermIdx M,
            termNumerator (honestMultiplicity oStmt) i u /
              termPhi oStmt xChallenge i u) =
        (∑ u : Hypercube n,
          evalOnHypercube (honestMultiplicity oStmt) u /
            (xChallenge + evalOnHypercube (tableOracle oStmt) u)) +
        ∑ u : Hypercube n,
          ∑ i : Fin M,
            (-1 : F) /
              (xChallenge + evalOnHypercube (columnOracle oStmt i) u) := by
    simp_rw [sum_terms_eq_table_add_columns
      (F := F) (n := n) (M := M) oStmt xChallenge]
    rw [Finset.sum_add_distrib]
  have hcolumns_neg :
      (∑ u : Hypercube n,
          ∑ i : Fin M,
            (-1 : F) /
              (xChallenge + evalOnHypercube (columnOracle oStmt i) u)) =
        - ∑ i : Fin M,
            ∑ u : Hypercube n,
              (1 : F) /
                (xChallenge + evalOnHypercube (columnOracle oStmt i) u) := by
    rw [Finset.sum_comm]
    simp_rw [neg_div]
    simp_rw [Finset.sum_neg_distrib]
  calc
    (∑ u : Hypercube n,
      ∑ k : Fin params.numGroups,
        evalOnHypercube (honestHelpers params oStmt xChallenge k) u)
        = ∑ u : Hypercube n,
            ∑ i : TermIdx M,
              termNumerator (honestMultiplicity oStmt) i u /
                termPhi oStmt xChallenge i u := hhelpers_eq_terms
    _ = (∑ u : Hypercube n,
          evalOnHypercube (honestMultiplicity oStmt) u /
            (xChallenge + evalOnHypercube (tableOracle oStmt) u)) +
        ∑ u : Hypercube n,
          ∑ i : Fin M,
            (-1 : F) /
              (xChallenge + evalOnHypercube (columnOracle oStmt i) u) := hterms_split
    _ = (∑ a : F, (lookupMultiplicityCount oStmt a : F) / (xChallenge + a)) +
        ∑ u : Hypercube n,
          ∑ i : Fin M,
            (-1 : F) /
              (xChallenge + evalOnHypercube (columnOracle oStmt i) u) := by
          change
            (∑ u : Hypercube n,
              normalizedMultiplicityValue oStmt u /
                (xChallenge + evalOnHypercube (tableOracle oStmt) u)) +
              ∑ u : Hypercube n,
                ∑ i : Fin M,
                  (-1 : F) /
                    (xChallenge + evalOnHypercube (columnOracle oStmt i) u) =
              (∑ a : F, (lookupMultiplicityCount oStmt a : F) / (xChallenge + a)) +
              ∑ u : Hypercube n,
                ∑ i : Fin M,
                  (-1 : F) /
                    (xChallenge + evalOnHypercube (columnOracle oStmt i) u)
          rw [table_sum_normalizedMultiplicity_eq_lookup_sum stmt oStmt hInput hM]
    _ = (∑ i : Fin M,
          ∑ u : Hypercube n,
            (1 : F) /
              (xChallenge + evalOnHypercube (columnOracle oStmt i) u)) +
        ∑ u : Hypercube n,
          ∑ i : Fin M,
            (-1 : F) /
              (xChallenge + evalOnHypercube (columnOracle oStmt i) u) := by
          rw [lookupMultiplicity_sum_div_eq_column_sum]
    _ = 0 := by
          rw [hcolumns_neg]
          exact add_neg_cancel _

theorem honest_helper_sum_zero_of_inputRelation_all
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (hInput : (((stmt, oStmt), ()) ∈ inputRelation F n M))
    (xChallenge : F) :
    (∑ u : Hypercube n,
      ∑ k : Fin params.numGroups,
        evalOnHypercube (honestHelpers params oStmt xChallenge k) u) = 0 := by
  by_cases hM : 0 < M
  · exact honest_helper_sum_zero_of_inputRelation
      (F := F) (n := n) (M := M) (params := params) stmt oStmt hInput hM xChallenge
  · have hM0 : M = 0 := by omega
    subst M
    exact honest_helper_sum_zero_no_columns
      (F := F) (n := n) params oStmt xChallenge

/-- Semantic agreement between final oracle-query answers and the retained LogUp oracles. -/
def logupPointEvaluationsAgree
    (r : Fin n → F)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i)
    (evals : PointEvaluations F M params.numGroups) : Prop :=
  evals.multiplicity = lagrangeOracleEval (oStmt .multiplicity) r ∧
    evals.table = lagrangeOracleEval (oStmt (.input .table)) r ∧
    (∀ i : Fin M, evals.columns i = lagrangeOracleEval (oStmt (.input (.column i))) r) ∧
      ∀ k : Fin params.numGroups, evals.helpers k = lagrangeOracleEval ((oStmt .helpers) k) r

omit [Fintype F] [DecidableEq F] in
theorem logupPointEvaluationsAgree.multiplicity
    {r : Fin n → F} {oStmt : ∀ i, OStmtAfterOuter F n M params i}
    {evals : PointEvaluations F M params.numGroups}
    (h : logupPointEvaluationsAgree F n M params r oStmt evals) :
    evals.multiplicity = lagrangeOracleEval (oStmt .multiplicity) r :=
  h.1

omit [Fintype F] [DecidableEq F] in
theorem logupPointEvaluationsAgree.table
    {r : Fin n → F} {oStmt : ∀ i, OStmtAfterOuter F n M params i}
    {evals : PointEvaluations F M params.numGroups}
    (h : logupPointEvaluationsAgree F n M params r oStmt evals) :
    evals.table = lagrangeOracleEval (oStmt (.input .table)) r :=
  h.2.1

omit [Fintype F] [DecidableEq F] in
theorem logupPointEvaluationsAgree.column
    {r : Fin n → F} {oStmt : ∀ i, OStmtAfterOuter F n M params i}
    {evals : PointEvaluations F M params.numGroups}
    (h : logupPointEvaluationsAgree F n M params r oStmt evals) (i : Fin M) :
    evals.columns i = lagrangeOracleEval (oStmt (.input (.column i))) r :=
  h.2.2.1 i

omit [Fintype F] [DecidableEq F] in
theorem logupPointEvaluationsAgree.helper
    {r : Fin n → F} {oStmt : ∀ i, OStmtAfterOuter F n M params i}
    {evals : PointEvaluations F M params.numGroups}
    (h : logupPointEvaluationsAgree F n M params r oStmt evals)
    (k : Fin params.numGroups) :
    evals.helpers k = lagrangeOracleEval ((oStmt .helpers) k) r :=
  h.2.2.2 k

omit [Fintype F] [DecidableEq F] in
theorem termPhiAtPoint_zero_of_logupPointEvaluationsAgree
    {r : Fin n → F} {oStmt : ∀ i, OStmtAfterOuter F n M params i}
    {evals : PointEvaluations F M params.numGroups}
    (h : logupPointEvaluationsAgree F n M params r oStmt evals)
    (xChallenge : F) :
    termPhiAtPoint xChallenge evals (0 : TermIdx M) =
      xChallenge + lagrangeOracleEval (oStmt (.input .table)) r := by
  simp [h.2.1]

omit [Fintype F] [DecidableEq F] in
theorem termPhiAtPoint_succ_of_logupPointEvaluationsAgree
    {r : Fin n → F} {oStmt : ∀ i, OStmtAfterOuter F n M params i}
    {evals : PointEvaluations F M params.numGroups}
    (h : logupPointEvaluationsAgree F n M params r oStmt evals)
    (xChallenge : F) (i : Fin M) :
    termPhiAtPoint xChallenge evals ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ =
      xChallenge + lagrangeOracleEval (oStmt (.input (.column i))) r := by
  simp [h.2.2.1 i]

omit [Fintype F] [DecidableEq F] in
theorem termNumeratorAtPoint_zero_of_logupPointEvaluationsAgree
    {r : Fin n → F} {oStmt : ∀ i, OStmtAfterOuter F n M params i}
    {evals : PointEvaluations F M params.numGroups}
    (h : logupPointEvaluationsAgree F n M params r oStmt evals) :
    termNumeratorAtPoint evals (0 : TermIdx M) = lagrangeOracleEval (oStmt .multiplicity) r := by
  simp [h.1]

end SumcheckInterface

section SumcheckBridge

variable (F : Type) [Field F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- The `{±1}` sumcheck domain, packaged in the form expected by `Sumcheck.Spec`. -/
def signDomain (hSigns : (-1 : F) ≠ 1) : Fin 2 ↪ F where
  toFun := bitToSign F
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b
    · rfl
    · exact absurd h hSigns
    · exact absurd h.symm hSigns
    · rfl

private theorem sum_piFinset_map_univ_eq_sum_hypercube
    (D : Fin 2 ↪ F) (f : (Fin n → F) → F) :
    (∑ x ∈ Fintype.piFinset fun _ : Fin n => Finset.univ.map D, f x) =
      ∑ u : Hypercube n, f (fun j => D (u j)) := by
  classical
  symm
  refine Finset.sum_nbij (s := (Finset.univ : Finset (Hypercube n)))
    (t := Fintype.piFinset fun _ : Fin n => Finset.univ.map D)
    (i := fun u j => D (u j)) ?hi ?hinj ?hsurj ?hfg
  · intro u _
    rw [Fintype.mem_piFinset]
    intro j
    exact Finset.mem_map.mpr ⟨u j, Finset.mem_univ _, rfl⟩
  · intro u _ v _ huv
    funext j
    exact D.injective (congr_fun huv j)
  · intro x hx
    have hx_coord : ∀ j : Fin n, ∃ b : Fin 2, D b = x j := by
      intro j
      have hxj := (Fintype.mem_piFinset.mp hx) j
      rcases Finset.mem_map.mp hxj with ⟨b, _, hb⟩
      exact ⟨b, hb⟩
    let u : Hypercube n := fun j => Classical.choose (hx_coord j)
    refine ⟨u, Finset.mem_univ _, ?_⟩
    funext j
    exact Classical.choose_spec (hx_coord j)
  · intro u _
    rfl


/-- The initial generic Sumcheck relation induced by a LogUp outer transcript. -/
def logupSumcheckRelationInput (hSigns : (-1 : F) ≠ 1)
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) : Prop :=
  ((logupInitialSumcheckStatement F n M params, logupSumcheckOracleStmt F n M params stmt oStmt),
      ()) ∈
    Sumcheck.Spec.relationRound F n (logupSumcheckDegree M params) (signDomain F hSigns) 0

/-- If the polynomial bridge agrees on the hypercube and LogUp's outer algebra proves a zero sum,
then the generic Sumcheck input relation is exactly the claim sent to Sumcheck. -/
theorem logupSumcheckRelationInput_of_rowsAgree
    {hSigns : (-1 : F) ≠ 1}
    {stmt : StmtAfterOuter F n M params}
    {oStmt : ∀ i, OStmtAfterOuter F n M params i}
    (hRows : logupSumcheckPolynomialRowsAgree F n M params stmt oStmt)
    (hZero : logupOuterSumcheckClaim F n M params stmt oStmt = 0) :
    logupSumcheckRelationInput F n M params hSigns stmt oStmt := by
  unfold logupSumcheckRelationInput Sumcheck.Spec.relationRound
  simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.sub_zero, logupInitialSumcheckStatement,
    Set.mem_setOf_eq, Fin.elim0_append, logupSumcheckOracleStmt]
  change
    (∑ x ∈ Fintype.piFinset fun _ : Fin n => Finset.univ.map (signDomain F hSigns),
      MvPolynomial.eval ((x ∘ Fin.cast (by omega)) ∘ Fin.cast (by omega))
        (logupSumcheckPolynomial F n M params stmt oStmt).val) = 0
  rw [sum_piFinset_map_univ_eq_sum_hypercube
    (F := F) (n := n) (D := signDomain F hSigns)
    (f := fun x =>
      MvPolynomial.eval ((x ∘ Fin.cast (by omega)) ∘ Fin.cast (by omega))
        (logupSumcheckPolynomial F n M params stmt oStmt).val)]
  calc
    (∑ u : Hypercube n,
        MvPolynomial.eval
          ((((fun j => (signDomain F hSigns) (u j)) ∘ Fin.cast (by omega)) ∘
              Fin.cast (by omega)))
          (logupSumcheckPolynomial F n M params stmt oStmt).val)
        =
      logupOuterSumcheckClaim F n M params stmt oStmt := by
        rw [logupOuterSumcheckClaim]
        apply Finset.sum_congr rfl
        intro u _
        simpa [signDomain, signPoint] using hRows u
    _ = 0 := hZero

/-- The obligations needed to replace the current abstract embedded sumcheck by ArkLib's generic
sumcheck plus LogUp's final oracle-query check. -/
structure LogupSumcheckBridge
    (stmt : StmtAfterOuter F n M params)
    (oStmt : ∀ i, OStmtAfterOuter F n M params i) where
  claimZero : logupOuterSumcheckClaim F n M params stmt oStmt = 0

theorem LogupSumcheckBridge.of_honestHelpers
    [Fintype F] [DecidableEq F]
    (stmtIn : StmtIn F n M)
    (oStmtIn : ∀ i, OStmtIn F n M i)
    (stmt : StmtAfterOuter F n M params)
    (hInput : (((stmtIn, oStmtIn), ()) ∈ inputRelation F n M))
    (htable : ∀ u : Hypercube n,
      stmt.xChallenge + evalOnHypercube (tableOracle oStmtIn) u ≠ 0)
    (hHelpers :
      (∑ u : Hypercube n,
        ∑ k : Fin params.numGroups,
          evalOnHypercube (honestHelpers params oStmtIn stmt.xChallenge k) u) = 0) :
    LogupSumcheckBridge F n M params stmt
      (fun
        | .input i => oStmtIn i
        | .multiplicity => honestMultiplicity oStmtIn
        | .helpers => honestHelpers params oStmtIn stmt.xChallenge) where
  claimZero := by
    rw [logupOuterSumcheckClaim_honestHelpers_eq_sum_helpers
      (F := F) (n := n) (M := M) (params := params)
      stmtIn oStmtIn stmt hInput htable]
    exact hHelpers

theorem LogupSumcheckBridge.of_honest
    [Fintype F] [DecidableEq F]
    (stmtIn : StmtIn F n M)
    (oStmtIn : ∀ i, OStmtIn F n M i)
    (stmt : StmtAfterOuter F n M params)
    (hInput : (((stmtIn, oStmtIn), ()) ∈ inputRelation F n M))
    (htable : ∀ u : Hypercube n,
      stmt.xChallenge + evalOnHypercube (tableOracle oStmtIn) u ≠ 0) :
    LogupSumcheckBridge F n M params stmt
      (fun
        | .input i => oStmtIn i
        | .multiplicity => honestMultiplicity oStmtIn
        | .helpers => honestHelpers params oStmtIn stmt.xChallenge) :=
  LogupSumcheckBridge.of_honestHelpers
    (F := F) (n := n) (M := M) (params := params)
    stmtIn oStmtIn stmt hInput htable
    (honest_helper_sum_zero_of_inputRelation_all
      (F := F) (n := n) (M := M) (params := params)
      stmtIn oStmtIn hInput stmt.xChallenge)

theorem LogupSumcheckBridge.relationInput
    {hSigns : (-1 : F) ≠ 1}
    {stmt : StmtAfterOuter F n M params}
    {oStmt : ∀ i, OStmtAfterOuter F n M params i}
    (bridge : LogupSumcheckBridge F n M params stmt oStmt) :
    logupSumcheckRelationInput F n M params hSigns stmt oStmt :=
  logupSumcheckRelationInput_of_rowsAgree (F := F) (n := n) (M := M) (params := params)
    (logupSumcheckPolynomialRowsAgree_of_signsDistinct
      (F := F) (n := n) (M := M) (params := params) hSigns stmt oStmt)
    bridge.claimZero

theorem logupSumcheckRelationInput_of_honest
    [Fintype F] [DecidableEq F]
    {hSigns : (-1 : F) ≠ 1}
    (stmtIn : StmtIn F n M)
    (oStmtIn : ∀ i, OStmtIn F n M i)
    (stmt : StmtAfterOuter F n M params)
    (hInput : (((stmtIn, oStmtIn), ()) ∈ inputRelation F n M))
    (htable : ∀ u : Hypercube n,
      stmt.xChallenge + evalOnHypercube (tableOracle oStmtIn) u ≠ 0) :
    logupSumcheckRelationInput F n M params hSigns stmt
      (fun
        | .input i => oStmtIn i
        | .multiplicity => honestMultiplicity oStmtIn
        | .helpers => honestHelpers params oStmtIn stmt.xChallenge) :=
  (LogupSumcheckBridge.of_honest
    (F := F) (n := n) (M := M) (params := params)
    stmtIn oStmtIn stmt hInput htable).relationInput

theorem logupSumcheckPolynomial_finalEval
    {stmt : StmtAfterOuter F n M params}
    {oStmt : ∀ i, OStmtAfterOuter F n M params i}
    (r : Fin n → F) (evals : PointEvaluations F M params.numGroups)
    (hAgree : logupPointEvaluationsAgree F n M params r oStmt evals) :
    MvPolynomial.eval r (logupSumcheckPolynomial F n M params stmt oStmt).1 =
      qAtPoint (canonicalGroups params) stmt.xChallenge stmt.zChallenge r
        stmt.batchingScalars evals := by
  exact logupQPolynomial_eval_eq_qAtPoint (F := F) (n := n) (M := M) (params := params)
    stmt oStmt r evals hAgree.multiplicity hAgree.table hAgree.column hAgree.helper

theorem logupSumcheckOutputTarget_eq_eval
    {hSigns : (-1 : F) ≠ 1}
    {out : LogupSumcheckStmtOut F n M params}
    {oStmt : ∀ i, LogupSumcheckOracleStatement F n M params i}
    (hRel :
      ((out, oStmt), ()) ∈
        Sumcheck.Spec.relationRound F n (logupSumcheckDegree M params)
          (signDomain F hSigns) (.last n)) :
    out.target = MvPolynomial.eval out.challenges (oStmt ()).1 := by
  unfold Sumcheck.Spec.relationRound at hRel
  rw [← hRel]
  have hzero : n - ↑(Fin.last n : Fin (n + 1)) = 0 := by simp
  letI : IsEmpty (Fin (n - ↑(Fin.last n : Fin (n + 1)))) := by
    rw [hzero]
    infer_instance
  rw [Fintype.piFinset_of_isEmpty]
  let x0 : Fin (n - ↑(Fin.last n : Fin (n + 1))) → F := fun i => isEmptyElim i
  rw [Finset.sum_eq_single x0]
  · have hpoint :
        Fin.append out.challenges x0 ∘
            Fin.cast (Sumcheck.Spec.relationRound._proof_1 n (Fin.last n)) =
          out.challenges := by
      rw [Fin.append_right_nil out.challenges x0 hzero]
      ext i
      simp
    rw [hpoint]
    rfl
  · intro y _ hy
    exfalso
    apply hy
    funext i
    exact isEmptyElim i
  · intro hx
    exact False.elim (hx (@Finset.mem_univ _ Unique.fintype x0))

theorem LogupSumcheckBridge.finalQueryCheck
    {stmt : StmtAfterOuter F n M params}
    {oStmt : ∀ i, OStmtAfterOuter F n M params i}
    (out : LogupSumcheckStmtOut F n M params)
    (evals : PointEvaluations F M params.numGroups)
    (hAgree :
      logupPointEvaluationsAgree F n M params out.challenges oStmt evals)
    (hTarget :
      out.target =
        MvPolynomial.eval out.challenges
          (logupSumcheckPolynomial F n M params stmt oStmt).1) :
    Logup.finalQueryCheck (canonicalGroups params) stmt.xChallenge stmt.zChallenge out.challenges
      stmt.batchingScalars evals out.target := by
  change
    qAtPoint (canonicalGroups params) stmt.xChallenge stmt.zChallenge out.challenges
      stmt.batchingScalars evals = out.target
  rw [hTarget]
  exact (logupSumcheckPolynomial_finalEval (F := F) (n := n) (M := M) (params := params)
    (stmt := stmt) (oStmt := oStmt) out.challenges evals hAgree).symm

theorem LogupSumcheckBridge.finalQueryCheck_of_relation
    {hSigns : (-1 : F) ≠ 1}
    {stmt : StmtAfterOuter F n M params}
    {oStmt : ∀ i, OStmtAfterOuter F n M params i}
    (out : LogupSumcheckStmtOut F n M params)
    (evals : PointEvaluations F M params.numGroups)
    (hAgree :
      logupPointEvaluationsAgree F n M params out.challenges oStmt evals)
    (hRel :
      ((out, logupSumcheckOracleStmt F n M params stmt oStmt), ()) ∈
        Sumcheck.Spec.relationRound F n (logupSumcheckDegree M params)
          (signDomain F hSigns) (.last n)) :
    Logup.finalQueryCheck (canonicalGroups params) stmt.xChallenge stmt.zChallenge out.challenges
      stmt.batchingScalars evals out.target := by
  apply LogupSumcheckBridge.finalQueryCheck (F := F) (n := n) (M := M) (params := params)
    out evals hAgree
  simpa [logupSumcheckOracleStmt] using
    logupSumcheckOutputTarget_eq_eval (F := F) (n := n) (M := M) (params := params)
      (hSigns := hSigns) (out := out)
      (oStmt := logupSumcheckOracleStmt F n M params stmt oStmt) hRel


end SumcheckBridge

section ConcreteSumcheckReduction

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] (n M : ℕ)
variable (params : ProtocolParams M)

/-- The existing generic Sumcheck oracle verifier specialized to LogUp's domain and degree bound. -/
noncomputable def logupConcreteSumcheckOracleVerifier [SampleableType F]
    (hSigns : (-1 : F) ≠ 1) :
    OracleVerifier oSpec (LogupSumcheckStmtIn F n M params)
      (LogupSumcheckOracleStatement F n M params)
      (LogupSumcheckStmtOut F n M params)
      (LogupSumcheckOracleStatement F n M params)
      (logupSumcheckPSpec F n M params) :=
  Sumcheck.Spec.oracleVerifier F (logupSumcheckDegree M params)
    (signDomain F hSigns) n oSpec

/-- The existing generic Sumcheck oracle reduction specialized to LogUp's domain and degree
bound. -/
noncomputable def logupConcreteSumcheckOracleReduction [SampleableType F]
    (hSigns : (-1 : F) ≠ 1) :
    OracleReduction oSpec (LogupSumcheckStmtIn F n M params)
      (LogupSumcheckOracleStatement F n M params) Unit
      (LogupSumcheckStmtOut F n M params)
      (LogupSumcheckOracleStatement F n M params) Unit
      (logupSumcheckPSpec F n M params) :=
  Sumcheck.Spec.oracleReduction F (logupSumcheckDegree M params)
    (signDomain F hSigns) n oSpec

end ConcreteSumcheckReduction

section SumcheckLift

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)] (n M : ℕ)
variable (params : ProtocolParams M)

/-- Context lens from LogUp's retained outer state to ArkLib's generic Sumcheck state.

The projection builds the generic zero-sum claim and its single polynomial oracle. The lift drops
the generic Sumcheck output because the top-level LogUp protocol returns only success/failure.
-/
noncomputable def logupSumcheckContextLens :
    OracleContext.Lens
      (StmtAfterOuter F n M params) StmtOut
      (LogupSumcheckStmtIn F n M params) (LogupSumcheckStmtOut F n M params)
      (OStmtAfterOuter F n M params) OStmtOut
      (LogupSumcheckOracleStatement F n M params)
      (LogupSumcheckOracleStatement F n M params)
      Unit Unit Unit Unit where
  stmt :=
    ⟨fun ctx =>
        (logupInitialSumcheckStatement F n M params,
          logupSumcheckOracleStmt F n M params ctx.1 ctx.2),
      fun _ _ => ((), fun i => Fin.elim0 i)⟩
  wit :=
    ⟨fun _ => (),
      fun _ _ => ()⟩

/-- Oracle-routing lens from LogUp's retained outer state to ArkLib's generic Sumcheck state,
instantiating the new `OracleStatement.OracleLens` API (#433).

The LogUp embedded sumcheck is a *virtual* oracle reduction: the inner generic-Sumcheck oracle is
the single batched polynomial `Q` (indexed by `Unit`), whereas the outer oracle family
`OStmtAfterOuter` is the LogUp lookup oracles (table, columns, multiplicity, helpers). The
value-level transport is exactly `logupSumcheckContextLens.stmt` (reused verbatim via `toLens`, so
all soundness / completeness machinery keeps applying), and the routing data is:

- `projStmt` / `liftStmt`: the non-oracle projection (enter the sumcheck with the zero-sum claim and
  no prior challenges) and lift (the top-level LogUp protocol returns only `Unit`), matching
  `logupSumcheckContextLens.stmt`'s statement shape.
- `simOStmt`: answers each inner `Q`-evaluation query at a point `r : Fin n → F` by honestly
  querying the *outer* LogUp oracles at `r` (the table, columns, multiplicity, and helper oracles),
  assembling their point evaluations into `PointEvaluations`, and returning
  `qAtPoint … r …` — the verifier's final check value `Q(L_H(r,z), m(r), φᵢ(r), hₖ(r))` from paper
  equation (19). This is the value the honest `Q` polynomial takes (cf. `finalEval`), reading
  `x, z, λ` from the outer non-oracle statement via `ReaderT`.
- `embedOStmt` / `hEqOStmt`: the full LogUp protocol leaves no output oracle statements
  (`OutputOracleIdx = Fin 0`), so the output-side embedding is the (vacuous) empty embedding. -/
noncomputable def logupSumcheckOracleLens [Fintype F] [DecidableEq F] [SampleableType F] :
    OracleStatement.OracleLens oSpec
      (StmtAfterOuter F n M params) StmtOut
      (LogupSumcheckStmtIn F n M params) (LogupSumcheckStmtOut F n M params)
      (OStmtAfterOuter F n M params) OStmtOut
      (LogupSumcheckOracleStatement F n M params)
      (LogupSumcheckOracleStatement F n M params)
      (logupSumcheckPSpec F n M params) where
  toLens := (logupSumcheckContextLens F n M params).stmt
  projStmt := fun _ => logupInitialSumcheckStatement F n M params
  liftStmt := fun _ _ => ()
  simOStmt := fun q =>
    match q with
    | ⟨(), r⟩ => ReaderT.mk fun stmt => do
        let m : F ← query (spec := [OStmtAfterOuter F n M params]ₒ)
          (⟨.multiplicity, r⟩ : [OStmtAfterOuter F n M params]ₒ.Domain)
        let t : F ← query (spec := [OStmtAfterOuter F n M params]ₒ)
          (⟨.input .table, r⟩ : [OStmtAfterOuter F n M params]ₒ.Domain)
        let colList : List F ← (List.finRange M).mapM (fun i =>
          (query (spec := [OStmtAfterOuter F n M params]ₒ)
            (⟨.input (.column i), r⟩ : [OStmtAfterOuter F n M params]ₒ.Domain) :
            OracleComp (oSpec + [OStmtAfterOuter F n M params]ₒ) F))
        let helperList : List F ← (List.finRange params.numGroups).mapM
          (fun (k : Fin params.numGroups) =>
            (query (spec := [OStmtAfterOuter F n M params]ₒ)
              (show [OStmtAfterOuter F n M params]ₒ.Domain from ⟨.helpers, ⟨k, r⟩⟩) :
              OracleComp (oSpec + [OStmtAfterOuter F n M params]ₒ) F))
        let evals : PointEvaluations F M params.numGroups :=
          { multiplicity := m
            table := t
            columns := fun i => colList.getD i.val 0
            helpers := fun k => helperList.getD k.val 0 }
        pure (show F from
          qAtPoint (canonicalGroups params) stmt.xChallenge stmt.zChallenge r
            stmt.batchingScalars evals)
  embedOStmt := Function.Embedding.ofIsEmpty
  hEqOStmt := fun i => Fin.elim0 i

/-- The embedded LogUp sumcheck phase, obtained by lifting ArkLib's generic Sumcheck reduction
through the LogUp-to-Sumcheck context lens.

Migrated to the new `OracleReduction.liftContext` signature (#433): the value-level context lens
`logupSumcheckContextLens` drives the prover, threaded alongside the oracle-routing
`stmtLens := logupSumcheckOracleLens` (carrying the `simOStmt` / `embedOStmt` data). -/
noncomputable def sumcheckOracleReduction [SampleableType F] :
    OracleReduction oSpec (StmtAfterOuter F n M params) (OStmtAfterOuter F n M params) Unit
      (StmtOut) (OStmtOut) Unit
      (logupSumcheckPSpec F n M params) :=
  (logupConcreteSumcheckOracleReduction oSpec F n M params
      (Fact.out : (-1 : F) ≠ 1)).liftContext
    (logupSumcheckContextLens.{0} F n M params)
    (logupSumcheckOracleLens.{0} oSpec F n M params)

end SumcheckLift

end Logup
