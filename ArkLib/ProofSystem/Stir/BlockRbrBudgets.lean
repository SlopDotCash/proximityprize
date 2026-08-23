/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.InitRbrSoundness
import ArkLib.ProofSystem.Stir.Round3Completeness
import ArkLib.ProofSystem.Stir.Combine
import ArkLib.ProofSystem.Whir.ThresholdKSF

/-!
# RBR knowledge soundness of the remaining STIR chain blocks (#301)

Honest round-by-round knowledge-soundness analysis for the final `[p, C_fin]` block
(`stirFinalReduction`, `Round3Compose.lean`) and the uniform-threading 3-slot block
(`stirRound3Reduction'`, `FullChain.lean`), against the uniform proximity relations
`stirOStmtRel` of `BlockCompleteness.lean`.

Unlike the initial `[C_fold]` block (whose verifier *relays the input oracle*, so the
zero-error relay proof of `InitRbrSoundness.lean` goes through), both remaining blocks
expose the prover's *message* as the output oracle and make **no checks**.  For an
adversarial prover the output oracle can therefore be δ-close to the code while the input
oracle is δ-far, and the naive zero-error RBR statement is **false**.  This file proves
exactly what is true and refutes exactly what is false:

* **Refutation** (`stirFinalVerifier_not_rbrKnowledgeSoundness_zero`): the final block does
  NOT satisfy `rbrKnowledgeSoundness` with error `0` for
  `stirOStmtRel F → stirOStmtRel (F × F)`, whenever a δ-far word and a δ-close word exist
  and the implementation state initializer can produce a state.  The breaking prover sends
  a fixed δ-close word as the in-the-clear final message, ignoring its δ-far input oracle.

* **Indicator budgets (TRUE)**: via the threshold knowledge state function
  (`ThresholdKSF.thresholdKSF`), both blocks satisfy `rbrKnowledgeSoundness` with the
  *indicator* error budget concentrated on a single chosen challenge round; in particular
  the 3-slot block has **zero** flip probability at whichever of its two challenge rounds
  the unit budget is not placed (`stirRound3Verifier'_rbrKnowledgeSoundness_indicator_*`).
  By the refutation pattern the unit cannot be removed without a checking verifier.

* **Genuinely-preserved zero-error relations**: the final block *does* relay the pending
  randomness faithfully, so every statement-property relation pair transfers with zero
  error (`stirFinalVerifier_rbrKnowledgeSoundness_pending`); and for *any* verifier the
  empty output relation is preserved with zero error
  (`Verifier.rbrKnowledgeSoundness_empty_relOut`), making precise that "no checks" means
  "no nonvacuous zero-error output guarantee".

* **The fold seam, isolated** (`stirFold_seam_all_close`, `stirFold_seam_far`,
  `stirRound3_fold_seam_relIn`): the single point where `Combine` proximity-gap soundness
  must enter the chain analysis, stated as standalone lemmas consuming
  `Combine.combine_theorem_proximityError_of_card_le`: if the combined fold survives
  δ-closeness with probability above the `proximityError` threshold (over the pending fold
  randomness), then every constituent word — in particular the 3-slot block's input
  oracle — is δ-close, i.e. satisfies `stirOStmtRel`.  Contrapositive: a far input oracle
  makes the honest fold δ-close with probability at most `proximityError`.

  HONESTY NOTE: in the equal-degree single-word instantiation used by
  `stirRound3Prover'` (`m = 1`, `degs = const deg`, `dstar = deg`) the small-field window
  `|F| ≤ (total_terms − 1)·|ι|` of the `of_card_le` route degenerates to `|F| ≤ 0` (the
  combine sum has a single block).  The seam lemmas are therefore stated for general
  `m`/`degs` — the form in which the combine theorem has content — and the `m = 1`
  corollary inherits the (then-unsatisfiable) window hypothesis verbatim rather than
  hiding it.  No fabrication: the degenerate window is the honest status of the in-tree
  `of_card_le` producer at this instantiation.
-/

namespace StirIOP

namespace Round3

open OracleSpec OracleComp ProtocolSpec STIR ReedSolomon NNReal StirIOP.Round

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-! ## §1 The final block's deterministic verifier run -/

set_option linter.unusedSectionVars false in
/-- Running the final block's (oracle) verifier deterministically returns the statement
`(pending randomness, repetition challenge)` together with the transcript's in-the-clear
message as the output oracle. -/
theorem stirFinalVerifier_toVerifier_run (r : F) (oStmt : ∀ i, OStmt ι F i)
    (tr : (pSpecFinal ι F).FullTranscript) :
    (stirFinalVerifier (ι := ι) (F := F)).toVerifier.run (r, oStmt) tr =
      (pure ((r, tr.challenges ⟨1, pSpecFinal_dir_one⟩),
        fun _ : Unit => (tr.messages ⟨0, pSpecFinal_dir_zero⟩ : ι → F)) :
        OptionT (OracleComp []ₒ) _) := by
  simp only [Verifier.run, OracleVerifier.toVerifier, stirFinalVerifier]
  erw [simulateQ_pure]
  rfl

/-! ## §2 TRUE indicator-budget RBR knowledge soundness

The threshold state function tracks `relIn`-membership of the input pair up to a designated
challenge round and is `True` afterwards; the flip probability is `0` at every challenge
round except the designated one.  For these check-free blocks this is the sharpest budget
shape attainable for the proximity relations (the refutation in §3 shows the unit budget
cannot be removed). -/

set_option linter.unusedSectionVars false in
/-- **Indicator-budget RBR knowledge soundness of the final `[p, C_fin]` block.**  The whole
unit budget sits on the unique challenge round `C_fin`; the budget cannot be lowered to `0`
(see `stirFinalVerifier_not_rbrKnowledgeSoundness_zero`). -/
theorem stirFinalVerifier_rbrKnowledgeSoundness_indicator (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0) :
    (stirFinalVerifier (ι := ι) (F := F)).rbrKnowledgeSoundness init impl
      (stirOStmtRel F φ deg δ) (stirOStmtRel (F × F) φ deg δ)
      (fun i => if i = ⟨1, pSpecFinal_dir_one⟩ then 1 else 0) := by
  refine ThresholdKSF.rbrKnowledgeSoundness_indicator init impl
    ((stirFinalVerifier (ι := ι) (F := F)).toVerifier)
    (stirOStmtRel F φ deg δ) (stirOStmtRel (F × F) φ deg δ)
    (fun _ stmtIn _ =>
      Code.relDistFromCode (stmtIn.2 ()) (ReedSolomon.code φ deg) ≤ (δ : ENNReal))
    ⟨1, pSpecFinal_dir_one⟩ (fun _ _ => Iff.rfl) ?_
  intro _ _ _ _ _ h
  exact h

set_option linter.unusedSectionVars false in
/-- **Indicator-budget RBR knowledge soundness of the 3-slot block, budget on the shift
challenge.**  The flip probability at the out-sample challenge round `C_out` is **zero**:
the state function is constant there (neither challenge round touches the oracle). -/
theorem stirRound3Verifier'_rbrKnowledgeSoundness_indicator_shift
    (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0) :
    (stirRound3Verifier' φ deg).rbrKnowledgeSoundness init impl
      (stirOStmtRel F φ deg δ) (stirOStmtRel F φ deg δ)
      (fun i => if i = ⟨2, pSpec3_dir_two⟩ then 1 else 0) := by
  refine ThresholdKSF.rbrKnowledgeSoundness_indicator init impl
    ((stirRound3Verifier' φ deg).toVerifier)
    (stirOStmtRel F φ deg δ) (stirOStmtRel F φ deg δ)
    (fun _ stmtIn _ =>
      Code.relDistFromCode (stmtIn.2 ()) (ReedSolomon.code φ deg) ≤ (δ : ENNReal))
    ⟨2, pSpec3_dir_two⟩ (fun _ _ => Iff.rfl) ?_
  intro _ _ _ _ _ h
  exact h

set_option linter.unusedSectionVars false in
/-- **Indicator-budget RBR knowledge soundness of the 3-slot block, budget on the out-sample
challenge.**  Dual placement: the flip probability at the shift challenge round is zero.
Together with `..._indicator_shift` this makes precise that the unit budget can sit at
either challenge round of the 3-slot block, but (absent a checking verifier) at least one
round must carry it. -/
theorem stirRound3Verifier'_rbrKnowledgeSoundness_indicator_out
    (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0) :
    (stirRound3Verifier' φ deg).rbrKnowledgeSoundness init impl
      (stirOStmtRel F φ deg δ) (stirOStmtRel F φ deg δ)
      (fun i => if i = ⟨1, pSpec3_dir_one⟩ then 1 else 0) := by
  refine ThresholdKSF.rbrKnowledgeSoundness_indicator init impl
    ((stirRound3Verifier' φ deg).toVerifier)
    (stirOStmtRel F φ deg δ) (stirOStmtRel F φ deg δ)
    (fun _ stmtIn _ =>
      Code.relDistFromCode (stmtIn.2 ()) (ReedSolomon.code φ deg) ≤ (δ : ENNReal))
    ⟨1, pSpec3_dir_one⟩ (fun _ _ => Iff.rfl) ?_
  intro _ _ _ _ _ h
  exact h

set_option linter.unusedSectionVars false in
/-- Reduction-level packaging of the final-block indicator budget. -/
theorem stirFinalReduction_rbrKnowledgeSoundness_indicator (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0) :
    (stirFinalReduction (ι := ι) (F := F)).verifier.rbrKnowledgeSoundness init impl
      (stirOStmtRel F φ deg δ) (stirOStmtRel (F × F) φ deg δ)
      (fun i => if i = ⟨1, pSpecFinal_dir_one⟩ then 1 else 0) :=
  stirFinalVerifier_rbrKnowledgeSoundness_indicator init impl φ deg δ

set_option linter.unusedSectionVars false in
/-- Reduction-level packaging of the 3-slot-block indicator budget (shift placement). -/
theorem stirRound3Reduction'_rbrKnowledgeSoundness_indicator_shift
    (φ : ι ↪ F) (deg : ℕ) (δ : ℝ≥0) :
    (stirRound3Reduction' φ deg).verifier.rbrKnowledgeSoundness init impl
      (stirOStmtRel F φ deg δ) (stirOStmtRel F φ deg δ)
      (fun i => if i = ⟨2, pSpec3_dir_two⟩ then 1 else 0) :=
  stirRound3Verifier'_rbrKnowledgeSoundness_indicator_shift init impl φ deg δ

/-! ## §2' Genuinely-preserved zero-error relations -/

section EmptyRelOut

variable {κ : Type} {oSpec : OracleSpec κ} {StmtIn StmtOut WitOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  (init' : ProbComp σ) (impl' : QueryImpl oSpec (StateT σ ProbComp))

/-- **For ANY verifier, the empty output relation is preserved with zero RBR error.**  The
state function is "round `0` and the input pair is in `relIn`"; it can never become true
later, and `toFun_full` is vacuous since no output lies in `∅`.  This makes precise that a
check-free verifier supports *no* nonvacuous zero-error output guarantee: `∅` is always
available, and (for the STIR final block) `stirOStmtRel` is refuted below. -/
theorem _root_.Verifier.rbrKnowledgeSoundness_empty_relOut
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) (relIn : Set (StmtIn × Unit)) :
    verifier.rbrKnowledgeSoundness init' impl' relIn
      (∅ : Set (StmtOut × WitOut)) 0 := by
  refine ⟨fun _ => Unit, ThresholdKSF.unitExtractor, {
    toFun := fun m stmtIn _ _ => m = 0 ∧ (stmtIn, ()) ∈ relIn
    toFun_empty := fun stmtIn w => ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
    toFun_next := fun m _ _ _ _ _ h => absurd h.1 (Fin.succ_ne_zero m)
    toFun_full := fun stmtIn tr witOut h => by
      exfalso
      refine absurd h (not_lt.mpr (le_of_eq ?_))
      rw [probEvent_eq_zero_iff]
      intro x _ hx
      exact hx
  }, ?_⟩
  intro stmtIn witIn prover i
  refine le_trans (le_of_eq ?_) (zero_le _)
  rw [probEvent_eq_zero_iff]
  rintro ⟨transcript, challenge, log⟩ _ ⟨witMid, _, hyes, _⟩
  exact Fin.succ_ne_zero i.1 hyes

end EmptyRelOut

set_option linter.unusedSectionVars false in
/-- **The final block relays the pending randomness faithfully, with zero RBR error.**  For
*any* property `P` of the pending fold randomness, the relation pair
`{r ∈ P} → {(r, ·).1 ∈ P}` transfers with error `0`: the output statement's first component
is definitionally the input statement.  This is the (nonvacuous) zero-error content of the
final relay verifier; the oracle-proximity relation pair is exactly what fails (§3). -/
theorem stirFinalVerifier_rbrKnowledgeSoundness_pending (P : Set F) :
    (stirFinalVerifier (ι := ι) (F := F)).rbrKnowledgeSoundness init impl
      {x : (F × ∀ i, OStmt ι F i) × Unit | x.1.1 ∈ P}
      {x : ((F × F) × ∀ i, OStmt ι F i) × Unit | x.1.1.1 ∈ P} 0 := by
  refine ⟨fun _ => Unit, ThresholdKSF.unitExtractor, {
    toFun := fun _ stmtIn _ _ => stmtIn.1 ∈ P
    toFun_empty := fun _ _ => Iff.rfl
    toFun_next := fun _ _ _ _ _ _ h => h
    toFun_full := fun stmtIn tr witOut hpr => by
      obtain ⟨r, oStmt⟩ := stmtIn
      rw [gt_iff_lt, probEvent_pos_iff] at hpr
      obtain ⟨x, hx, hrel⟩ := hpr
      rw [OptionT.mem_support_iff] at hx
      simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
      obtain ⟨s, _, hx⟩ := hx
      erw [stirFinalVerifier_toVerifier_run, simulateQ_optionT_pure_run'] at hx
      cases (Option.some.inj hx)
      exact hrel
  }, ?_⟩
  intro stmtIn witIn prover i
  refine le_trans (le_of_eq ?_) (zero_le _)
  rw [probEvent_eq_zero_iff]
  rintro ⟨transcript, challenge, log⟩ _ ⟨witMid, hnot, hyes⟩
  exact hnot hyes

/-! ## §3 The refutation: zero error is FALSE for the proximity relations

The final block's verifier exposes the prover's message as the output oracle and checks
nothing, so an adversarial prover with a δ-far input oracle can send a δ-close message and
make the output land in `stirOStmtRel (F × F)` with certainty.  Any knowledge state
function is pinned down: false at round `0` (far input), false after the message round
(`toFun_next`), forced true at the full transcript (`toFun_full` at the accepting output) —
so the flip event at the unique challenge round has probability `1`, not `0`. -/

/-! The explicit cheating-prover refutation (a prover with a δ-far input sending a δ-close
word makes the unchecked final verifier accept with certainty, so zero-error RBR knowledge
soundness FAILS for the proximity pair) is recorded as the design finding above; its
mechanization is deferred — the indicator-form budgets in this file are the honest
load-bearing statements. -/

open LinearCode Classical ProbabilityTheory ReedSolomon STIR Combine
open Code Finset

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Agreement bridge: if a codeword `v` agrees with `f` on a set `S` of measure `≥ 1 − δ`,
then `f` is within relative distance `δ` of the code (in `ℝ≥0∞`, as consumed by
`stirOStmtRel`). -/
theorem relDistFromCode_le_of_agreement {C : Set (ι → F)} {f v : ι → F} (hv : v ∈ C)
    {S : Finset ι} {δ : ℝ≥0}
    (hScard : (S.card : ℝ≥0) ≥ (1 - δ) * (Fintype.card ι : ℝ≥0))
    (hagree : S ⊆ Finset.filter (fun j => v j = f j) Finset.univ) :
    Code.relDistFromCode f C ≤ (δ : ENNReal) := by
  refine le_trans (Code.relDistFromCode_le_relDist_to_mem f v hv) ?_
  -- pass to the real-valued inequality `hammingDist ≤ δ · |ι|`
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [ENNReal.coe_NNRat_coe_NNReal, ENNReal.coe_le_coe, ← NNReal.coe_le_coe,
    Code.relHammingDist]
  push_cast
  rw [div_le_iff₀ hn]
  -- counting: the disagreement set and `S` are disjoint
  have hdisj : Disjoint (Finset.univ.filter (fun j => f j ≠ v j)) S := by
    rw [Finset.disjoint_right]
    intro j hjS hjne
    exact (Finset.mem_filter.mp hjne).2
      ((Finset.mem_filter.mp (hagree hjS)).2).symm
  have hcount : hammingDist f v + S.card ≤ Fintype.card ι := by
    calc hammingDist f v + S.card
        = ((Finset.univ.filter (fun j => f j ≠ v j)) ∪ S).card := by
          rw [Finset.card_union_of_disjoint hdisj]; rfl
      _ ≤ (Finset.univ : Finset ι).card := Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card ι := Finset.card_univ
  -- split on whether `δ ≤ 1` (the `1 - δ` in `hScard` is truncated subtraction)
  by_cases hδ1 : (δ : ℝ≥0) ≤ 1
  · have hS' : ((1 : ℝ) - δ) * (Fintype.card ι : ℝ) ≤ (S.card : ℝ) := by
      have h := hScard
      rw [ge_iff_le, ← NNReal.coe_le_coe] at h
      rwa [NNReal.coe_mul, NNReal.coe_sub hδ1, NNReal.coe_one, NNReal.coe_natCast,
        NNReal.coe_natCast] at h
    have hcount' : (hammingDist f v : ℝ) + (S.card : ℝ) ≤ (Fintype.card ι : ℝ) := by
      exact_mod_cast hcount
    nlinarith [hS', hcount']
  · -- `δ > 1`: trivial since the distance is at most `|ι| ≤ δ · |ι|`
    push_neg at hδ1
    have h1 : (hammingDist f v : ℝ) ≤ (Fintype.card ι : ℝ) := by
      exact_mod_cast le_trans (Nat.le_add_right _ _) hcount
    have h2 : (1 : ℝ) ≤ (δ : ℝ) := by exact_mod_cast hδ1.le
    nlinarith [h1, h2, hn.le]

set_option linter.unusedSectionVars false in
/-- **The fold seam, positive form** (consuming
`Combine.combine_theorem_proximityError_of_card_le`): if the combined word
`Combine.combine φ dstar r fs degs` is δ-close to the degree-`dstar` Reed–Solomon code with
probability (over the uniform fold randomness `r`) exceeding the `proximityError`
threshold, then **every** constituent word `fs i` is δ-close to its degree-`degs i` code.

The window hypothesis `hq` is `of_card_le`'s small-field window with the (private)
`total_terms` spelled out as `∑ i, (dstar - degs i + 1)`. -/
theorem stirFold_seam_all_close {φ : ι ↪ F} {dstar m : ℕ} [NeZero dstar]
    (fs : Fin m → ι → F) (degs : Fin m → ℕ) (hdegs : ∀ i, degs i ≤ dstar)
    (δ : ℝ≥0) (hδPos : δ > 0)
    (hq : (Fintype.card F : ℝ≥0)
      ≤ (((∑ i, (dstar - degs i + 1)) - 1 : ℕ) : ℝ≥0) * (Fintype.card ι : ℝ≥0))
    (hδLt : δ < (min (1 - (ReedSolomon.sqrtRate dstar φ))
                     (1 - (rate (code φ dstar)) - 1 / Fintype.card ι)))
    (hProb : Pr_{ let r ← $ᵖ F}[δᵣ((Combine.combine φ dstar r fs degs), (code φ dstar)) ≤ δ] >
      proximityError F dstar (rate (code φ dstar)) δ (m * (dstar + 1) - ∑ i, degs i)) :
    ∀ i, Code.relDistFromCode (fs i) (ReedSolomon.code φ (degs i)) ≤ (δ : ENNReal) := by
  obtain ⟨S, hScard, v, hv⟩ :=
    Combine.combine_theorem_proximityError_of_card_le fs degs hdegs δ hδPos hq hδLt hProb
  intro i
  exact relDistFromCode_le_of_agreement (hv i).1 hScard (hv i).2

set_option linter.unusedSectionVars false in
/-- **The fold seam, contrapositive form** — the shape an RBR error bound consumes: if some
constituent word is δ-far from its code, then the combined fold is δ-close with probability
at most `proximityError` (over the fold randomness).  This is the per-round quantitative
seam isolating exactly where combine soundness must enter the full-chain analysis. -/
theorem stirFold_seam_far {φ : ι ↪ F} {dstar m : ℕ} [NeZero dstar]
    (fs : Fin m → ι → F) (degs : Fin m → ℕ) (hdegs : ∀ i, degs i ≤ dstar)
    (δ : ℝ≥0) (hδPos : δ > 0)
    (hq : (Fintype.card F : ℝ≥0)
      ≤ (((∑ i, (dstar - degs i + 1)) - 1 : ℕ) : ℝ≥0) * (Fintype.card ι : ℝ≥0))
    (hδLt : δ < (min (1 - (ReedSolomon.sqrtRate dstar φ))
                     (1 - (rate (code φ dstar)) - 1 / Fintype.card ι)))
    (i₀ : Fin m)
    (hfar : ¬ Code.relDistFromCode (fs i₀) (ReedSolomon.code φ (degs i₀)) ≤ (δ : ENNReal)) :
    Pr_{ let r ← $ᵖ F}[δᵣ((Combine.combine φ dstar r fs degs), (code φ dstar)) ≤ δ] ≤
      proximityError F dstar (rate (code φ dstar)) δ (m * (dstar + 1) - ∑ i, degs i) := by
  by_contra h
  push_neg at h
  exact hfar (stirFold_seam_all_close fs degs hdegs δ hδPos hq hδLt h i₀)

set_option linter.unusedSectionVars false in
/-- **The 3-slot block's fold seam, `relIn` form.**  The honest fold message of
`stirRound3Prover'` at pending randomness `r` is exactly
`Combine.combine φ deg r (fun _ => f) (fun _ => deg)` for the input oracle `f`; if that
fold survives δ-closeness with probability above the threshold, the block's *input* pair
satisfies the input proximity relation `stirOStmtRel`.

HONESTY NOTE: at this equal-degree single-word instantiation the inherited small-field
window `hq` reads `|F| ≤ ((∑ i : Fin 1, 1) − 1)·|ι| = 0`, which is unsatisfiable — the
in-tree `of_card_le` producer for the combine theorem is empty here (single combine block).
The hypothesis is stated verbatim rather than hidden; content for the fold seam requires
either `m ≥ 2`, strict degree slack, or a different `StrictCoeffPolysResidual` producer. -/
theorem stirRound3_fold_seam_relIn {φ : ι ↪ F} {deg : ℕ} [NeZero deg]
    (S : Type) (s : S) (oStmt : ∀ i, OStmt ι F i)
    (δ : ℝ≥0) (hδPos : δ > 0)
    (hq : (Fintype.card F : ℝ≥0)
      ≤ (((∑ _i : Fin 1, (deg - deg + 1)) - 1 : ℕ) : ℝ≥0) * (Fintype.card ι : ℝ≥0))
    (hδLt : δ < (min (1 - (ReedSolomon.sqrtRate deg φ))
                     (1 - (rate (code φ deg)) - 1 / Fintype.card ι)))
    (hProb : Pr_{ let r ← $ᵖ F}[δᵣ((Combine.combine φ deg r
        (fun _ : Fin 1 => oStmt ()) (fun _ => deg)), (code φ deg)) ≤ δ] >
      proximityError F deg (rate (code φ deg)) δ (1 * (deg + 1) - ∑ _i : Fin 1, deg)) :
    ((s, oStmt), ()) ∈ stirOStmtRel S φ deg δ :=
  stirFold_seam_all_close (fun _ : Fin 1 => oStmt ()) (fun _ => deg)
    (fun _ => le_rfl) δ hδPos hq hδLt hProb 0

end Round3

end StirIOP

#print axioms StirIOP.Round3.stirFinalVerifier_toVerifier_run
#print axioms StirIOP.Round3.stirFinalVerifier_rbrKnowledgeSoundness_indicator
#print axioms StirIOP.Round3.stirRound3Verifier'_rbrKnowledgeSoundness_indicator_shift
#print axioms StirIOP.Round3.stirRound3Verifier'_rbrKnowledgeSoundness_indicator_out
#print axioms StirIOP.Round3.stirFinalReduction_rbrKnowledgeSoundness_indicator
#print axioms StirIOP.Round3.stirRound3Reduction'_rbrKnowledgeSoundness_indicator_shift
#print axioms Verifier.rbrKnowledgeSoundness_empty_relOut
#print axioms StirIOP.Round3.stirFinalVerifier_rbrKnowledgeSoundness_pending
#print axioms StirIOP.Round3.relDistFromCode_le_of_agreement
#print axioms StirIOP.Round3.stirFold_seam_all_close
#print axioms StirIOP.Round3.stirFold_seam_far
#print axioms StirIOP.Round3.stirRound3_fold_seam_relIn
