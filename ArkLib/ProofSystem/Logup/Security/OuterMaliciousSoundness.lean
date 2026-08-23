/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.OuterVerifierSupport
import ArkLib.ProofSystem.Logup.Security.OuterMaliciousClaim
import ArkLib.ProofSystem.Logup.Security.Soundness
import ArkLib.ProofSystem.Logup.Security.MarginalBridgeProof
import ArkLib.ProofSystem.Logup.Security.LogupSoundnessPointwise

open OracleComp OracleSpec ProtocolSpec
open scoped BigOperators NNReal ENNReal

/-!
# Outer malicious soundness: readback, transcript claim, and the claim-based state function

The run-level wiring of `hOuter@midLanguage` (design: issue #13 comment `4668149886`):
full verifier readback (with the pole guard), the transcript claim, acceptance ⟺ claim-vanishing,
and the complete claim-based RBR `StateFunction` whose `toFun_full` is proven. Axiom-clean.
-/

namespace Logup


variable {ι : Type} {oSpec : OracleSpec ι}
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
variable {n M : ℕ} {params : ProtocolParams M}

/-- **Full-field readback for the compiled outer verifier.** Every surviving output reads its
entire statement off the transcript — the challenge fields are the round-1/round-3 draws and the
output oracles are the input oracles plus the round-0/round-2 prover messages. -/
theorem outer_toVerifier_verify_support_full
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (transcript : FullTranscript (outerPSpec F n params))
    (res : StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i))
    (hres : some res ∈ support
      (((outerVerifier oSpec F n M params).toVerifier.verify
        (stmt, oStmt) transcript).run)) :
    (∀ u : Hypercube n,
      chalX F n M params (transcript.challenges)
        + evalOnHypercube (tableOracle oStmt) u ≠ 0) ∧
    res.1.xChallenge = chalX F n M params (transcript.challenges) ∧
    res.1.zChallenge = (chalBatch F n M params (transcript.challenges)).1 ∧
    res.1.batchingScalars = (chalBatch F n M params (transcript.challenges)).2 ∧
    (∀ i, res.2 (.input i) = oStmt i) ∧
    res.2 .multiplicity = transcript.messages ⟨0, rfl⟩ ∧
    res.2 .helpers = transcript.messages ⟨2, rfl⟩ := by
  classical
  simp only [OracleVerifier.toVerifier] at hres
  rw [simulateQ_outerVerify_eq (oSpec := oSpec) (F := F) (n := n) (M := M) (params := params)
    (stmt := stmt) (oStmt := oStmt) (chal := transcript.challenges)
    (msgs := transcript.messages)] at hres
  by_cases hacc : ∀ u : Hypercube n,
      chalX F n M params transcript.challenges + evalOnHypercube (tableOracle oStmt) u ≠ 0
  · rw [if_pos hacc] at hres
    simp only [OptionT.run_pure, pure_bind, support_pure,
      Set.mem_singleton_iff, Option.some.injEq] at hres
    subst hres
    exact ⟨hacc, rfl, rfl, rfl, fun i => rfl, rfl, rfl⟩
  · rw [if_neg hacc] at hres
    simp only [OptionT.run_failure, failure_bind] at hres
    simp at hres






variable {ι : Type} {oSpec : OracleSpec ι}
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
variable {n M : ℕ} {params : ProtocolParams M}

/-- The after-outer mid-claim read directly off a full outer transcript: the batched hypercube
sum at the transcript's challenges and prover messages, against the input oracles. -/
noncomputable def transcriptClaim (oStmt : ∀ i, OStmtIn F n M i)
    (transcript : FullTranscript (outerPSpec F n params)) : F :=
  ∑ u : Hypercube n,
    qOnHypercube (canonicalGroups params) oStmt
      (transcript.messages ⟨0, rfl⟩) (transcript.messages ⟨2, rfl⟩)
      (chalX F n M params (transcript.challenges))
      (chalBatch F n M params (transcript.challenges)).1
      (chalBatch F n M params (transcript.challenges)).2 u

/-- **Accepted outputs land in `midLanguage` iff the transcript claim vanishes.** Combining the
full readback with the definition of `logupOuterSumcheckClaim`. -/
theorem outer_accept_mem_midLanguage_iff
    (stmt : StmtIn F n M) (oStmt : ∀ i, OStmtIn F n M i)
    (transcript : FullTranscript (outerPSpec F n params))
    (res : StmtAfterOuter F n M params × (∀ i, OStmtAfterOuter F n M params i))
    (hres : some res ∈ support
      (((outerVerifier oSpec F n M params).toVerifier.verify
        (stmt, oStmt) transcript).run)) :
    res ∈ midLanguage F n M params ↔ transcriptClaim oStmt transcript = 0 := by
  obtain ⟨-, hx, hz, hb, hin, hm, hh⟩ :=
    outer_toVerifier_verify_support_full stmt oStmt transcript res hres
  unfold midLanguage
  rw [Set.mem_setOf_eq]
  unfold logupOuterSumcheckClaim transcriptClaim
  constructor <;> intro h <;> rw [← h] <;>
    exact Finset.sum_congr rfl (fun u _ => by rw [hx, hz, hb, hm, hh, funext hin])


section MalSoundDefs

variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
variable (n M : ℕ) (params : ProtocolParams M)

/-- The mid-claim assembled from the four outer-transcript entries. -/
noncomputable def entriesClaim (oStmt : ∀ i, OStmtIn F n M i)
    (mult : MultilinearOracle F n) (x : F)
    (helpers : HelperMessages F n params.numGroups)
    (zb : BatchingChallenge F n params.numGroups) : F :=
  ∑ u : Hypercube n,
    qOnHypercube (canonicalGroups params) oStmt mult helpers x zb.1 zb.2 u

/-- The claim-based RBR state for the outer phase at `midLanguage`. -/
def outerMidState (m : Fin 5) (stmt : StmtIn F n M × (∀ i, OStmtIn F n M i))
    (tr : (outerPSpec F n params).Transcript m) : Prop :=
  stmt ∈ (inputRelation F n M).language ∨
    (∃ h4 : 3 < m.val,
      (∀ u : Hypercube n,
        (show F from tr ⟨1, by omega⟩)
          + evalOnHypercube (tableOracle stmt.2) u ≠ 0) ∧
      entriesClaim F n M params stmt.2
        (show MultilinearOracle F n from tr ⟨0, by omega⟩)
        (show F from tr ⟨1, by omega⟩)
        (show HelperMessages F n params.numGroups from tr ⟨2, by omega⟩)
        (show BatchingChallenge F n params.numGroups from tr ⟨3, h4⟩) = 0) ∨
    (∃ h1 : 1 < m.val, m.val ≤ 3 ∧
      (show F from tr ⟨1, h1⟩) ∈
        outerBadChallenges params stmt.2
          (show MultilinearOracle F n from tr ⟨0, by omega⟩))








end MalSoundDefs

section MalSoundSF

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ) (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

local instance instInhabitedFieldMalSoundSF : Inhabited F := ⟨0⟩

/-- **The claim-based outer state function at `midLanguage`.** -/
noncomputable def outerMidStateFunction :
    ((outerVerifier oSpec F n M params).toVerifier).StateFunction init impl
      (inputRelation F n M).language (midLanguage F n M params) where
  toFun := outerMidState F n M params
  toFun_empty := fun stmt => by
    unfold outerMidState
    constructor
    · exact fun h => Or.inl h
    · rintro (h | ⟨h, -⟩ | ⟨h, -⟩)
      · exact h
      · exact absurd h (by omega)
      · exact absurd h (by omega)
  toFun_next := fun m hdir stmt tr hno msg => by
    fin_cases m
    · -- round 0
      unfold outerMidState at hno ⊢
      rintro (h | ⟨h, -⟩ | ⟨h, -⟩)
      · exact hno (Or.inl h)
      · exact absurd h (by norm_num)
      · exact absurd h (by norm_num)
    · exact absurd hdir (by exact fun h => by cases h)
    · -- round 2: entries 0/1 preserved by concat
      unfold outerMidState at hno ⊢
      rintro (h | ⟨h, -⟩ | ⟨h, -, hmem⟩)
      · exact hno (Or.inl h)
      · exact absurd h (by norm_num)
      · exact hno (Or.inr (Or.inr ⟨by norm_num, by norm_num, hmem⟩))
    · exact absurd hdir (by exact fun h => by cases h)
  toFun_full := fun stmt tr hno => by
    classical
    refine probEvent_eq_zero ?_
    intro x hx hmem
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, mem_support_bind_iff] at hx
    obtain ⟨s, -, hx⟩ := hx
    have hx' := _root_.support_simulateQ_run'_subset impl _ s hx
    have hguard :=
      (outer_toVerifier_verify_support_full stmt.1 stmt.2 tr x hx').1
    have hiff := outer_accept_mem_midLanguage_iff stmt.1 stmt.2 tr x hx'
    -- so the state at the last round is true — contradiction
    refine hno ?_
    unfold outerMidState
    exact Or.inr (Or.inl ⟨by norm_num, hguard, hiff.mp hmem⟩)





end MalSoundSF

section Flips

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ) (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

local instance instInhabitedFieldFlips : Inhabited F := ⟨0⟩

/-- Generic uniform-draw membership bound over any fintype challenge: a tsum of uniform masses
weighted by event probabilities supported inside a finite set is at most `#mem / #C`. -/
theorem tsum_uniform_mem_le {C : Type} [Fintype C] [Nonempty C] [SampleableType C]
    [DecidableEq C]
    (mem : Finset C) (g : C → ℝ≥0∞)
    (hg : ∀ c, c ∉ mem → g c = 0) (hgle : ∀ c, g c ≤ Pr[= c | ($ᵗ C)]) :
    (∑' c : C, g c) ≤ (mem.card : ℝ≥0∞) / (Fintype.card C : ℝ≥0∞) := by
  classical
  have hmass : ∀ c : C, Pr[= c | ($ᵗ C)] = (Fintype.card C : ℝ≥0∞)⁻¹ := by
    intro c
    rw [probOutput_uniformSample]
  calc (∑' c : C, g c)
      ≤ ∑' c : C, (if c ∈ mem then (Fintype.card C : ℝ≥0∞)⁻¹ else 0) := by
        refine ENNReal.tsum_le_tsum (fun c => ?_)
        by_cases hc : c ∈ mem
        · rw [if_pos hc]
          exact le_trans (hgle c) (le_of_eq (hmass c))
        · rw [if_neg hc, hg c hc]
    _ = ∑ c : C, (if c ∈ mem then (Fintype.card C : ℝ≥0∞)⁻¹ else 0) := tsum_fintype _
    _ = (mem.card : ℝ≥0∞) * (Fintype.card C : ℝ≥0∞)⁻¹ := by
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    _ = _ := by rw [div_eq_mul_inv]


/-- Instance-free finite-support tsum bound: if `g` vanishes off `mem` and is pointwise at most
`q`, its tsum is at most `|mem| · q`. -/
theorem tsum_le_card_mul_of_support_subset {C : Type} (mem : Finset C) (g : C → ℝ≥0∞)
    (q : ℝ≥0∞) (hg : ∀ c, c ∉ mem → g c = 0) (hgle : ∀ c, g c ≤ q) :
    (∑' c : C, g c) ≤ (mem.card : ℝ≥0∞) * q := by
  classical
  calc (∑' c : C, g c) = ∑ c ∈ mem, g c := tsum_eq_sum hg
    _ ≤ ∑ _c ∈ mem, q := Finset.sum_le_sum (fun c _ => hgle c)
    _ = (mem.card : ℝ≥0∞) * q := by rw [Finset.sum_const, nsmul_eq_mul]

end Flips



#print axioms Logup.tsum_uniform_mem_le



section RbrMain

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ) (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

local instance instInhabitedFieldRbrMain : Inhabited F := ⟨0⟩

/-- The per-round RBR error of the claim-based outer state: the bad-challenge mass at round 1,
the `(z, λ)` Schwartz–Zippel mass at round 3. -/
noncomputable def outerMidRbrError : (outerPSpec F n params).ChallengeIdx → ℝ≥0 :=
  fun i => if i.1.val = 1
    then (((M + 1) * 2 ^ n - 1 : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0)
    else ((n + 1 : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0)

/-- **Outer RBR soundness at `midLanguage`.** -/
theorem outerVerifier_rbrSoundness_mid :
    ((outerVerifier oSpec F n M params).toVerifier).rbrSoundness init impl
      (inputRelation F n M).language (midLanguage F n M params)
      (outerMidRbrError F n M params) := by
  classical
  refine ⟨outerMidStateFunction oSpec F n M params init impl, ?_⟩
  intro stmtIn hStmtIn WitIn WitOut witIn prover i
  have hBad : ¬ (((stmtIn.1, stmtIn.2), ()) ∈ inputRelation F n M) := by
    intro h
    exact hStmtIn ((Set.mem_language_iff _ _).mpr ⟨(), h⟩)
  rcases i with ⟨⟨iv, hiv⟩, hdir⟩
  interval_cases iv
  · exact absurd hdir (by exact fun h => by cases h)
  · -- round 1: the bad-challenge flip
    have herr : outerMidRbrError F n M params ⟨⟨1, hiv⟩, hdir⟩
        = (((M + 1) * 2 ^ n - 1 : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0) := by
      unfold outerMidRbrError; norm_num
    rw [herr]
    refine le_trans (probEvent_bind_le_of_forall_support init _ _ _ (fun s _ => ?_)) le_rfl
    rw [simulateQ_bind, StateT.run'_bind_lib]
    refine probEvent_bind_le_of_forall_support _ _ _ _ (fun rk _ => ?_)
    obtain ⟨⟨t, pst⟩, s'⟩ := rk
    rw [liftComp_eq_liftM]
    rw [ChallengeCoherence.probEvent_run'_simulateQ_addLift_getChallenge_bind impl s'
      ⟨⟨1, hiv⟩, hdir⟩ (fun c => pure (t, c)) _]
    haveI : SampleableType ((outerPSpec F n params).Challenge ⟨⟨1, hiv⟩, hdir⟩) :=
      (inferInstance : SampleableType F)
    haveI : DecidableEq ((outerPSpec F n params).Challenge ⟨⟨1, hiv⟩, hdir⟩) :=
      (inferInstance : DecidableEq F)
    haveI : Fintype ((outerPSpec F n params).Challenge ⟨⟨1, hiv⟩, hdir⟩) :=
      (inferInstance : Fintype F)
    simp only [probOutput_uniformSample]
    refine le_trans (tsum_le_card_mul_of_support_subset
      (Finset.univ.filter (fun c : (outerPSpec F n params).Challenge ⟨⟨1, hiv⟩, hdir⟩ =>
        (show F from c) ∈ outerBadChallenges params stmtIn.2
          (show MultilinearOracle F n from t ⟨0, by norm_num⟩)))
      _ ((Fintype.card ((outerPSpec F n params).Challenge ⟨⟨1, hiv⟩, hdir⟩) : ℝ≥0∞))⁻¹
      ?hg ?hgle) ?_
    case hg =>
      intro c hc
      rw [mul_eq_zero]
      right
      rw [simulateQ_pure]
      refine probEvent_eq_zero ?_
      rintro x hx ⟨hno, hyes⟩
      simp only [StateT.run'_eq, StateT.run_pure, _root_.map_pure, support_pure,
        Set.mem_singleton_iff] at hx
      subst hx
      unfold outerMidStateFunction outerMidState at hyes
      obtain h | ⟨h, -⟩ | ⟨h1, hle, hmem⟩ := hyes
      · exact hStmtIn h
      · exact absurd h (by norm_num)
      · exact hc (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩)
    case hgle =>
      intro c
      calc (Fintype.card ((outerPSpec F n params).Challenge ⟨⟨1, hiv⟩, hdir⟩) : ℝ≥0∞)⁻¹
            * _ ≤ (Fintype.card ((outerPSpec F n params).Challenge ⟨⟨1, hiv⟩, hdir⟩) : ℝ≥0∞)⁻¹
            * 1 := by gcongr; exact probEvent_le_one
        _ = _ := mul_one _
    · -- card bound: |bad| ≤ (M+1)·2ⁿ − 1; identify card C = card F
      have hcardC : Fintype.card ((outerPSpec F n params).Challenge ⟨⟨1, hiv⟩, hdir⟩)
          = Fintype.card F := Fintype.card_congr (Equiv.cast rfl)
      have hfle : (Finset.univ.filter (fun c : (outerPSpec F n params).Challenge ⟨⟨1, hiv⟩, hdir⟩ =>
          (show F from c) ∈ outerBadChallenges params stmtIn.2
            (show MultilinearOracle F n from t ⟨0, by norm_num⟩))).card
          ≤ (M + 1) * 2 ^ n - 1 := by
        refine le_trans (Finset.card_le_card_of_injOn (fun c => show F from c)
          (fun c hc => (Finset.mem_filter.mp hc).2) (fun a _ b _ h => h)) ?_
        exact outerBadChallenges_card_le params stmtIn.1 stmtIn.2 hBad _
      rw [hcardC, ← div_eq_mul_inv]
      rw [ENNReal.coe_div (by exact_mod_cast Fintype.card_ne_zero), ENNReal.coe_natCast,
        ENNReal.coe_natCast]
      gcongr
  · exact absurd hdir (by exact fun h => by cases h)
  · -- round 3: the (z, λ) Schwartz–Zippel flip
    have herr : outerMidRbrError F n M params ⟨⟨3, hiv⟩, hdir⟩
        = ((n + 1 : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0) := by
      unfold outerMidRbrError; norm_num
    rw [herr]
    refine le_trans (probEvent_bind_le_of_forall_support init _ _ _ (fun s _ => ?_)) le_rfl
    rw [simulateQ_bind, StateT.run'_bind_lib]
    refine probEvent_bind_le_of_forall_support _ _ _ _ (fun rk _ => ?_)
    obtain ⟨⟨t, pst⟩, s'⟩ := rk
    rw [liftComp_eq_liftM]
    rw [ChallengeCoherence.probEvent_run'_simulateQ_addLift_getChallenge_bind impl s'
      ⟨⟨3, hiv⟩, hdir⟩ (fun c => pure (t, c)) _]
    haveI : SampleableType ((outerPSpec F n params).Challenge ⟨⟨3, hiv⟩, hdir⟩) :=
      (inferInstance : SampleableType (BatchingChallenge F n params.numGroups))
    haveI : DecidableEq ((outerPSpec F n params).Challenge ⟨⟨3, hiv⟩, hdir⟩) :=
      (inferInstance : DecidableEq (BatchingChallenge F n params.numGroups))
    haveI : Fintype ((outerPSpec F n params).Challenge ⟨⟨3, hiv⟩, hdir⟩) :=
      (inferInstance : Fintype (BatchingChallenge F n params.numGroups))
    simp only [probOutput_uniformSample]
    set mult : MultilinearOracle F n := show MultilinearOracle F n from t ⟨0, by norm_num⟩
      with hmult
    set x : F := show F from t ⟨1, by norm_num⟩ with hxdef
    set helpers : HelperMessages F n params.numGroups :=
      show HelperMessages F n params.numGroups from t ⟨2, by norm_num⟩ with hhelp
    by_cases hguard : ∀ u : Hypercube n,
        x + evalOnHypercube (tableOracle stmtIn.2) u ≠ 0
    case neg =>
      refine le_trans (le_of_eq ?_) (zero_le _)
      rw [ENNReal.tsum_eq_zero]
      intro c
      rw [mul_eq_zero]
      right
      rw [simulateQ_pure]
      refine probEvent_eq_zero ?_
      rintro y hy ⟨hno, hyes⟩
      simp only [StateT.run'_eq, StateT.run_pure, _root_.map_pure, support_pure,
        Set.mem_singleton_iff] at hy
      subst hy
      unfold outerMidStateFunction outerMidState at hyes
      obtain h | ⟨h4x, hg, -⟩ | ⟨h1x, h3, -⟩ := hyes
      · exact hStmtIn h
      · exact hguard hg
      · exact absurd h3 (by norm_num)
    case pos =>
      by_cases hxbad : x ∈ outerBadChallenges params stmtIn.2 mult
      case pos =>
        refine le_trans (le_of_eq ?_) (zero_le _)
        rw [ENNReal.tsum_eq_zero]
        intro c
        rw [mul_eq_zero]
        right
        rw [simulateQ_pure]
        refine probEvent_eq_zero ?_
        rintro y hy ⟨hno, -⟩
        simp only [StateT.run'_eq, StateT.run_pure, _root_.map_pure, support_pure,
          Set.mem_singleton_iff] at hy
        subst hy
        refine hno ?_
        unfold outerMidStateFunction outerMidState
        exact Or.inr (Or.inr ⟨by norm_num, by norm_num, hxbad⟩)
      case neg =>
        have hNot := claim_not_identicallyZero params stmtIn.1 stmtIn.2 hBad mult x
          hguard hxbad helpers
        have hcount := card_filter_claimZero_mul_card_le (F := F)
          (Fact.out : (-1 : F) ≠ 1) (canonicalGroups params) stmtIn.2 mult helpers x hNot
        set Z : Finset ((outerPSpec F n params).Challenge ⟨⟨3, hiv⟩, hdir⟩) :=
          Finset.univ.filter
            (fun c : (outerPSpec F n params).Challenge ⟨⟨3, hiv⟩, hdir⟩ =>
              (∑ u : Hypercube n, qOnHypercube (canonicalGroups params) stmtIn.2 mult helpers
                x (show BatchingChallenge F n params.numGroups from c).1
                (show BatchingChallenge F n params.numGroups from c).2 u) = 0) with hZ
        refine le_trans (tsum_le_card_mul_of_support_subset Z _
          ((Fintype.card ((outerPSpec F n params).Challenge ⟨⟨3, hiv⟩, hdir⟩) : ℝ≥0∞))⁻¹
          ?hg3 ?hgle3) ?_
        case hg3 =>
          intro c hc
          rw [mul_eq_zero]
          right
          rw [simulateQ_pure]
          refine probEvent_eq_zero ?_
          rintro y hy ⟨hno, hyes⟩
          simp only [StateT.run'_eq, StateT.run_pure, _root_.map_pure, support_pure,
            Set.mem_singleton_iff] at hy
          subst hy
          unfold outerMidStateFunction outerMidState at hyes
          obtain h | ⟨h4x, hgx, hclaim⟩ | ⟨h1x, h3, -⟩ := hyes
          · exact hStmtIn h
          · refine hc ?_
            rw [hZ]
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hclaim⟩
          · exact absurd h3 (by norm_num)
        case hgle3 =>
          intro c
          calc (Fintype.card ((outerPSpec F n params).Challenge ⟨⟨3, hiv⟩, hdir⟩) : ℝ≥0∞)⁻¹
                * _ ≤ (Fintype.card
                  ((outerPSpec F n params).Challenge ⟨⟨3, hiv⟩, hdir⟩) : ℝ≥0∞)⁻¹ * 1 := by
                gcongr; exact probEvent_le_one
            _ = _ := mul_one _
        · -- counting: |Z|·q ≤ (n+1)·q^(n+K) ⟹ |Z|/q^(n+K) ≤ (n+1)/q
          have hcardC : Fintype.card
              ((outerPSpec F n params).Challenge ⟨⟨3, hiv⟩, hdir⟩)
              = Fintype.card F ^ (n + params.numGroups) := by
            calc Fintype.card ((outerPSpec F n params).Challenge ⟨⟨3, hiv⟩, hdir⟩)
                = Fintype.card ((Fin n → F) × (Fin params.numGroups → F)) :=
                  Fintype.card_congr (Equiv.cast rfl)
              _ = Fintype.card F ^ (n + params.numGroups) := by
                  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fun,
                    Fintype.card_fin, Fintype.card_fin, ← pow_add]
          have hcfle : Z.card ≤ (Finset.univ.filter
                (fun p : (Fin n → F) × (Fin params.numGroups → F) =>
                  (∑ u : Hypercube n, qOnHypercube (canonicalGroups params) stmtIn.2 mult helpers
                    x p.1 p.2 u) = 0)).card := by
            rw [hZ]
            exact Finset.card_le_card_of_injOn
              (fun c => show BatchingChallenge F n params.numGroups from c)
              (fun c hc => Finset.mem_filter.mpr
                ⟨Finset.mem_univ _, (Finset.mem_filter.mp hc).2⟩)
              (fun a _ b _ h => h)
          have hZq : (Z.card * Fintype.card F : ℕ)
              ≤ (n + 1) * Fintype.card F ^ (n + params.numGroups) :=
            le_trans (Nat.mul_le_mul_right _ hcfle) hcount
          rw [hcardC, ← div_eq_mul_inv, Nat.cast_pow]
          have hq0 : (0 : ℝ≥0) < (Fintype.card F : ℝ≥0) := by
            exact_mod_cast Fintype.card_pos
          have hnn : (Z.card : ℝ≥0) / ((Fintype.card F : ℝ≥0) ^ (n + params.numGroups))
              ≤ ((n + 1 : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0) := by
            rw [div_le_div_iff₀ (by positivity) hq0]
            calc (Z.card : ℝ≥0) * (Fintype.card F : ℝ≥0)
                = ((Z.card * Fintype.card F : ℕ) : ℝ≥0) := by push_cast; ring
              _ ≤ (((n + 1) * Fintype.card F ^ (n + params.numGroups) : ℕ) : ℝ≥0) := by
                  exact_mod_cast hZq
              _ = ((n + 1 : ℕ) : ℝ≥0) * ((Fintype.card F : ℝ≥0) ^ (n + params.numGroups)) := by
                  push_cast; ring
          calc (Z.card : ℝ≥0∞) / ((Fintype.card F : ℝ≥0∞) ^ (n + params.numGroups))
              = (((Z.card : ℝ≥0) / ((Fintype.card F : ℝ≥0) ^ (n + params.numGroups)) : ℝ≥0)
                  : ℝ≥0∞) := by
                rw [ENNReal.coe_div (by positivity), ENNReal.coe_pow, ENNReal.coe_natCast,
                  ENNReal.coe_natCast]
            _ ≤ ((((n + 1 : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0) : ℝ≥0) : ℝ≥0∞) := by
                exact_mod_cast hnn

end RbrMain







section MidCapstone

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ) (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

local instance instInhabitedFieldMidCap : Inhabited F := ⟨0⟩

omit [Field F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)] [SampleableType F] in
/-- The total claim-based RBR error: the bad-challenge mass plus the `(z,λ)` SZ mass. -/
theorem sum_outerMidRbrError [Field F] :
    ∑ i : (outerPSpec F n params).ChallengeIdx, outerMidRbrError F n M params i
      = (((M + 1) * 2 ^ n - 1 : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0)
        + ((n + 1 : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0) := by
  classical
  have hsub : ∑ i ∈ Finset.univ.filter
        (fun i : Fin 4 => (outerPSpec F n params).dir i = Direction.V_to_P),
        (if i.val = 1
          then (((M + 1) * 2 ^ n - 1 : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0)
          else ((n + 1 : ℕ) : ℝ≥0) / (Fintype.card F : ℝ≥0))
      = ∑ i : (outerPSpec F n params).ChallengeIdx, outerMidRbrError F n M params i := by
    refine Finset.sum_subtype _ (fun x => ?_) _
    simp [ProtocolSpec.ChallengeIdx]
  have hfilter : Finset.univ.filter
      (fun i : Fin 4 => (outerPSpec F n params).dir i = Direction.V_to_P)
      = ({⟨1, by norm_num⟩, ⟨3, by norm_num⟩} : Finset (Fin 4)) := by
    ext i
    fin_cases i
    · exact iff_of_false (fun h => nomatch (Finset.mem_filter.mp h).2) (by decide)
    · exact iff_of_true (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩) (by decide)
    · exact iff_of_false (fun h => nomatch (Finset.mem_filter.mp h).2) (by decide)
    · exact iff_of_true (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩) (by decide)
  rw [← hsub, hfilter, Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num

/-- **`hOuter@midLanguage` DISCHARGED.** The outer LogUp verifier is sound from the input
language into `midLanguage` with the paper-shaped `outerSoundnessError`, for any
state-preserving, non-failing, value-blind implementation, over a field larger than the
hypercube and with at least as many groups as variables. -/
theorem outerVerifier_soundness_mid
    (hpole : 2 ^ n < Fintype.card F) (hnK : n ≤ params.numGroups)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    (outerVerifier oSpec F n M params).soundness init impl
      (inputRelation F n M).language (midLanguage F n M params)
      (outerSoundnessError F n M params) := by
  show ((outerVerifier oSpec F n M params).toVerifier).soundness init impl
    (inputRelation F n M).language (midLanguage F n M params)
    (outerSoundnessError F n M params)
  have hRbr := outerVerifier_rbrSoundness_mid oSpec F n M params init impl
  have hbr : Verifier.MarginalBridge init impl
      (inputRelation F n M).language (midLanguage F n M params)
      ((outerVerifier oSpec F n M params).toVerifier)
      (outerMidRbrError F n M params) :=
    Verifier.marginalBridge_holds himplSP himplNF himplVB
  have h := Verifier.rbrSoundness_imp_soundness_of_marginal init impl hRbr hbr
  have hle : (∑ i : (outerPSpec F n params).ChallengeIdx, outerMidRbrError F n M params i)
      ≤ outerSoundnessError F n M params := by
    rw [sum_outerMidRbrError]
    unfold outerSoundnessError
    rw [card_hypercube]
    have h2n : (0 : ℝ≥0) < ((Fintype.card F - 2 ^ n : ℕ) : ℝ≥0) := by
      exact_mod_cast Nat.sub_pos_of_lt hpole
    refine add_le_add ?_ ?_
    · first
      | (gcongr
         · exact h2n
         · exact_mod_cast Nat.sub_le _ _)
      | (gcongr
         exact_mod_cast Nat.sub_le _ _)
      | gcongr
    · first
      | (gcongr
         exact_mod_cast Nat.succ_le_succ hnK)
      | gcongr
  exact Verifier.soundness.mono_error init impl h hle

/-- **Issue #13 LogUp soundness — END-TO-END.** The full LogUp verifier is sound with the
paper error, with every protocol obligation discharged; only standard runtime side
conditions on the shared-oracle implementation remain as hypotheses. -/
theorem logup_soundness_end_to_end [oSpec.Fintype] [oSpec.Inhabited]
    (sumcheckSoundnessError : ℝ≥0) (hn : 0 < n)
    (hpole : 2 ^ n < Fintype.card F) (hnK : n ≤ params.numGroups)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    (logupVerifier oSpec F n M params).soundness init impl
      (inputRelation F n M).language outputRelation.language
      (logupSoundnessError F n M params sumcheckSoundnessError) :=
  logup_soundness_pointwiseSumcheck oSpec F n M params sumcheckSoundnessError hn
    (outerVerifier_soundness_mid oSpec F n M params init impl hpole hnK
      himplSP himplNF himplVB)
    himplSP himplNF himplVB

end MidCapstone




end Logup

#print axioms Logup.outer_toVerifier_verify_support_full
#print axioms Logup.outer_accept_mem_midLanguage_iff
#print axioms Logup.outerMidStateFunction
#print axioms Logup.tsum_uniform_mem_le
#print axioms Logup.outerVerifier_rbrSoundness_mid
#print axioms Logup.sum_outerMidRbrError
#print axioms Logup.outerVerifier_soundness_mid
#print axioms Logup.logup_soundness_end_to_end
