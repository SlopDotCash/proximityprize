/-
# Issue #302 — THE SUB-UNIT WHIR RBR: the bounded-flip shell at the checked verifier

This file instantiates the bounded-flip threshold shell
(`ThresholdKSF.rbrKnowledgeSoundness_of_flipBound`) at the CHECKED WHIR verifier
(`Whir302Checked.whirVerifyChecked`), in four landable pieces:

1. **`whirChainClosePred`** — the prefix sumcheck-consistency state predicate for the
   paper-order WHIR spec: δ-closeness of the input oracle PLUS the chain-consistency of every
   sumcheck step *visible in the prefix* (the prefix restriction of `whirCheckingBool`'s
   checks: the initial-phase anchors `g₀(0)+g₀(1) = 0`, the initial/main chain links
   `g_{s+1}(0)+g_{s+1}(1) = g_s(r_s)`, and the final zero-sum check), with payloads read
   directly off the partial transcript (`trSlotVec`/`trMsgList`/`trChalVal`); PLUS the
   **AGREEMENT IFF on full transcripts** (`whirChainOK_iff_whirCheckingBool`): at the final
   round the chain predicate is EXACTLY the checked verifier's decision bit (via the
   full-read collapse `readAns_eq_toList` and the seam identities
   `trMsgList_last_eq_readAns`/`trChalVal_last_eq_chalAt`; every step check is an anchor or
   a link).

2. **The `hEmpty` and `hConcat` legs**, both PROVEN:
   * `whirChainClosePred_zero` — at round 0 the predicate is exactly membership in
     `whirRelation m0 (P.φ 0) δ` (every visibility hypothesis is vacuous);
   * `whirChainClosePred_concat` — appending one message cannot fix a broken chain (the
     visible-check set shrinks and earlier payloads are unchanged).

3. **The `hFlip` quantitative core**, PROVEN:
   * `probEvent_chalElemOf_eq_uniform` — the **marginal-domination fact**: in the round-`c`
     RBR game under the uniform `challengeQueryImpl`, the field element read off the freshly
     drawn (length-1) vector challenge is exactly uniform on `F`;
   * `probEvent_salvage_game_le` — **the salvage-event bound in the exact RBR game shape**:
     for ANY prover and any two prefix-measurable coefficient chains that genuinely differ as
     polynomials, the probability that the fresh challenge at round `c` satisfies the salvage
     equation `listEval cs r = listEval cs' r` is at most `maxLen / |F|`
     (via `probEvent_salvage_le_comap`, the comap form of the Schwartz–Zippel core);
   * `whir_salvage_initial_le` / `whir_salvage_main_le` — the bound instantiated at EVERY
     initial-phase and main-round sumcheck challenge slot of the concrete paper-order WHIR
     spec (each has a length-1 payload: `length_initialSumcheckChallengeIdx`,
     `length_mainSumcheckChallengeIdx`).

4. **THE THEOREM** (two forms, both at the budget
   `fun i => if i = finalRandomnessChallengeIdx P d then maxLen/|F| else 0`):
   * `whirChecked_rbrKnowledgeSoundness_of_flipBound` — the conditional assembly: RBR
     knowledge soundness of the checked verifier's `VectorIOP` from the single remaining
     `hFlip` hypothesis (stated in EXACTLY the shell's shape, at the `whirChainClosePred`
     state function);
   * `whirChecked_rbrKnowledgeSoundness_smallField` /
     `whirCheckedVectorIOP_isSecureWithGap_smallField` — the UNCONDITIONAL discharge in the
     small-field regime `|F| ≤ maxLen` (where the budget is ≥ 1), giving the full
     `IsSecureWithGap` package for the checked WHIR `VectorIOP` at the task's budget shape.

## HONESTY: why the unconditional `hFlip` at `maxLen/|F| < 1` is NOT provable here

The threshold shell's flip event at the threshold round `c` is
`¬ pred c.castSucc stmtIn transcript` — it does NOT mention the fresh challenge (the state is
`True` after `c`).  `predFalse_propagates` below PROVES that for ANY predicate satisfying the
shell's `hEmpty`+`hConcat` legs and any statement outside the input relation, the predicate is
false on EVERY transcript at every round `≤ c+1`; hence for a far statement the flip event is
pointwise full (`whirChainClosePred_false_of_far`), its probability is `1 - Pr[⊥]` (`= 1` for
e.g. the never-failing honest paper prover), and `hFlip` with `ε < 1` is FALSE whenever a far
statement exists.  The genuinely challenge-dependent flip estimate is piece 3
(`probEvent_salvage_game_le`, bounded by `maxLen/|F|` unconditionally); consuming it requires a
NON-threshold knowledge state function that keeps tracking the predicate past the salvage round
(so that the flip event becomes the salvage event).  That state-function upgrade is the precise
remaining work; no fabrication here.

NOTE: `ArkLib.ProofSystem.Whir.SchwartzZippelCore` has no `.olean` in the current build
(clobbered), so its content (`listPoly`, `card_listEval_eq_le`, `probEvent_salvage_le`) is
inlined verbatim below (namespace `Whir302SZ`), plus the new comap variant
`probEvent_salvage_le_comap`.
-/
import ArkLib.ProofSystem.Whir.ThresholdKSF
import ArkLib.ProofSystem.Whir.CheckedVerifier
import ArkLib.Data.Probability.MarginalBound
import ArkLib.ProofSystem.Logup.Security.OuterRunDecomposition

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

universe u v

open OracleSpec OracleComp ProtocolSpec NNReal ReedSolomon
open WhirIOP WhirIOP.Construction
open scoped ENNReal

noncomputable section

/-! ## Part 0 — inlined Schwartz–Zippel core (`SchwartzZippelCore.lean`, olean missing),
plus the comap variant `probEvent_salvage_le_comap`. -/

namespace Whir302SZ

open Polynomial

variable {F : Type} [Field F]

/-- The polynomial whose Horner evaluation is `listEval`. -/
noncomputable def listPoly (cs : List F) : F[X] :=
  cs.foldr (fun c acc => Polynomial.C c + Polynomial.X * acc) 0

theorem listPoly_eval (cs : List F) (x : F) :
    (listPoly cs).eval x = Whir302Checked.listEval cs x := by
  induction cs with
  | nil => simp [listPoly, Whir302Checked.listEval]
  | cons c cs ih =>
      simp [listPoly, Whir302Checked.listEval, List.foldr_cons] at ih ⊢
      rw [← ih]
      simp [listPoly, Whir302Checked.listEval]

theorem listPoly_cons (c : F) (cs : List F) :
    listPoly (c :: cs) = Polynomial.C c + Polynomial.X * listPoly cs := rfl

theorem listPoly_natDegree_lt (cs : List F) (h : cs ≠ []) :
    (listPoly cs).natDegree < cs.length := by
  induction cs with
  | nil => exact absurd rfl h
  | cons c cs ih =>
      rw [listPoly_cons, List.length_cons]
      refine lt_of_le_of_lt (Polynomial.natDegree_add_le _ _) ?_
      rw [Polynomial.natDegree_C]
      rcases eq_or_ne (listPoly cs) 0 with h0 | h0
      · rw [h0, mul_zero, Polynomial.natDegree_zero]
        omega
      · have hcs : cs ≠ [] := by rintro rfl; exact h0 rfl
        have hb := Polynomial.natDegree_mul (p := (Polynomial.X : F[X]))
          (q := listPoly cs) Polynomial.X_ne_zero h0
        have hlt := ih hcs
        rw [hb, Polynomial.natDegree_X]
        omega

variable [Fintype F] [DecidableEq F]

/-- **The Schwartz–Zippel salvage bound for `listEval`** (the WHIR sumcheck flip event): if two
coefficient lists evaluate differently somewhere (the chains genuinely disagree), the set of
challenges where they agree has at most `max(len cs, len cs') − 1 < max len` elements; counted
against the full field. -/
theorem card_listEval_eq_le (cs cs' : List F)
    (hne : listPoly cs ≠ listPoly cs') (hcs : cs ≠ []) (hcs' : cs' ≠ []) :
    (Finset.univ.filter
        (fun r : F => Whir302Checked.listEval cs r = Whir302Checked.listEval cs' r)).card
      ≤ max cs.length cs'.length := by
  classical
  have hsub : Finset.univ.filter
      (fun r : F => Whir302Checked.listEval cs r = Whir302Checked.listEval cs' r)
      ⊆ (listPoly cs - listPoly cs').roots.toFinset := by
    intro r hr
    rw [Finset.mem_filter] at hr
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (sub_ne_zero.mpr hne)]
    rw [Polynomial.IsRoot, Polynomial.eval_sub, sub_eq_zero, listPoly_eval, listPoly_eval]
    exact hr.2
  calc (Finset.univ.filter _).card
      ≤ (listPoly cs - listPoly cs').roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card (listPoly cs - listPoly cs').roots := Multiset.toFinset_card_le _
    _ ≤ (listPoly cs - listPoly cs').natDegree := Polynomial.card_roots' _
    _ ≤ max (listPoly cs).natDegree (listPoly cs').natDegree :=
        Polynomial.natDegree_sub_le _ _
    _ ≤ max cs.length cs'.length := by
        have h1 := listPoly_natDegree_lt cs hcs
        have h2 := listPoly_natDegree_lt cs' hcs'
        omega

end Whir302SZ

-- ## The probability-side accounting

section Probability

open OracleComp OracleSpec ProbabilityTheory
open scoped ENNReal NNReal

namespace Whir302SZ

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {β : Type} {m : Type → Type v} [Monad m] [HasEvalSPMF m]

/-- **The per-round salvage probability bound** (the quantitative WHIR flip estimate): in any
game that draws a challenge `r` whose marginal is dominated by uniform-on-`F` and then runs a
continuation whose success forces the salvage equation `listEval cs r = listEval cs' r` for two
genuinely different chains, the success probability is at most `max(len cs, len cs') / |F|`. -/
theorem probEvent_salvage_le (mx : m F) (k : F → m β) (q : β → Prop)
    (cs cs' : List F)
    (hne : listPoly cs ≠ listPoly cs') (hcs : cs ≠ []) (hcs' : cs' ≠ [])
    (hunif : ∀ x : F, Pr[= x | mx] ≤ (Fintype.card F : ℝ≥0∞)⁻¹)
    (hsalvage : ∀ x : F, ¬ (Whir302Checked.listEval cs x = Whir302Checked.listEval cs' x) →
      Pr[ q | k x] = 0) :
    Pr[ q | mx >>= k]
      ≤ ((max cs.length cs'.length : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  classical
  refine le_trans
    (probEvent_bind_le_uniform_marginal mx k q
      {x : F | Whir302Checked.listEval cs x = Whir302Checked.listEval cs' x}
      hunif hsalvage) ?_
  apply ENNReal.div_le_div_right
  have hcard := card_listEval_eq_le cs cs' hne hcs hcs'
  have hfilter : (Finset.univ.filter
        (· ∈ {x : F | Whir302Checked.listEval cs x = Whir302Checked.listEval cs' x}))
      = (Finset.univ.filter
        (fun r : F => Whir302Checked.listEval cs r = Whir302Checked.listEval cs' r)) := by
    apply Finset.filter_congr
    intro x _
    simp [Set.mem_setOf_eq]
  rw [hfilter]
  exact_mod_cast hcard

/-- **Comap form of the salvage bound**: the drawn value is *carried inside* the first stage's
output (here: the freshly drawn vector challenge carries its field-element read `f`).  If the
carried marginal is dominated by uniform-on-`F` and success forces the salvage equation at the
carried value, the success probability is at most `max(len cs, len cs') / |F|`. -/
theorem probEvent_salvage_le_comap {α : Type} (mx : m α) (f : α → F) (k : α → m β)
    (q : β → Prop) (cs cs' : List F)
    (hne : listPoly cs ≠ listPoly cs') (hcs : cs ≠ []) (hcs' : cs' ≠ [])
    (hunif : ∀ x : F, Pr[fun a => f a = x | mx] ≤ (Fintype.card F : ℝ≥0∞)⁻¹)
    (hsalvage : ∀ a : α,
      ¬ (Whir302Checked.listEval cs (f a) = Whir302Checked.listEval cs' (f a)) →
      Pr[ q | k a] = 0) :
    Pr[ q | mx >>= k]
      ≤ ((max cs.length cs'.length : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  classical
  refine le_trans
    (probEvent_bind_le_uniform_marginal_comap mx f k q
      {x : F | Whir302Checked.listEval cs x = Whir302Checked.listEval cs' x}
      hunif (fun a ha => hsalvage a ha)) ?_
  apply ENNReal.div_le_div_right
  have hcard := card_listEval_eq_le cs cs' hne hcs hcs'
  have hfilter : (Finset.univ.filter
        (· ∈ {x : F | Whir302Checked.listEval cs x = Whir302Checked.listEval cs' x}))
      = (Finset.univ.filter
        (fun r : F => Whir302Checked.listEval cs r = Whir302Checked.listEval cs' r)) := by
    apply Finset.filter_congr
    intro x _
    simp [Set.mem_setOf_eq]
  rw [hfilter]
  exact_mod_cast hcard

end Whir302SZ

end Probability

/-! ## Part A — the structural no-sub-1-budget fact for the threshold shell -/

namespace ThresholdKSFFacts

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type} {n : ℕ} {pSpec : ProtocolSpec n}

/-- **Falseness propagates through `hConcat`** (the shell's stability leg): if a round-indexed
predicate family is stable under removing the last entry at every round `≤ c` and is false on
the empty transcript, it is false on EVERY transcript at every round `≤ c + 1`.  Consequence:
the threshold shell's flip event at the threshold (`¬ pred c.castSucc`) is pointwise full for
every statement outside the input relation, so the shell's `hFlip` hypothesis with `ε < 1` is
unsatisfiable whenever a far statement exists.  This is the PRECISE structural reason the
unconditional sub-1 budget needs a non-threshold (challenge-tracking) state function. -/
theorem predFalse_propagates
    (pred : (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → Prop)
    (c : pSpec.ChallengeIdx)
    (hConcat : ∀ (m : Fin n), m.val ≤ c.1.val →
      ∀ stmtIn (tr : Transcript m.castSucc pSpec) (msg : pSpec.Type m),
        pred m.succ stmtIn (tr.concat msg) → pred m.castSucc stmtIn tr)
    (stmtIn : StmtIn) (h0 : ¬ pred 0 stmtIn default) :
    ∀ (m : Fin (n + 1)), m.val ≤ c.1.val + 1 →
      ∀ (tr : Transcript m pSpec), ¬ pred m stmtIn tr := by
  intro m
  induction m using Fin.induction with
  | zero =>
      intro _ tr
      have htr : tr = default := Subsingleton.elim _ _
      rw [htr]
      exact h0
  | succ j ih =>
      intro hm tr hpred
      have hj : j.val ≤ c.1.val := by
        simp only [Fin.val_succ] at hm
        omega
      have hcs : (j.castSucc : Fin (n + 1)).val ≤ c.1.val + 1 := by
        simp only [Fin.val_castSucc]
        omega
      refine ih hcs (fun i => tr i.castSucc) ?_
      refine hConcat j hj stmtIn (fun i => tr i.castSucc) (tr (Fin.last j.val)) ?_
      -- split the transcript as (init, last entry): `tr = (Fin.init tr).snoc (tr last)`
      exact cast (congrArg (pred j.succ stmtIn) (Fin.snoc_init_self tr)).symm hpred

end ThresholdKSFFacts

/-! ## Part B — prefix reads off a partial paper-order WHIR transcript -/

namespace Whir302SubUnit

open ThresholdKSF Whir302Checked Whir302SZ Whir302RBR

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {M : ℕ} {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]

section Reads

variable (P : Params ιs F) (d : ℕ)

/-- Payload length of a paper slot at its canonical wire index. -/
lemma length_slotIndex (slot : PaperTranscriptSlot P) :
    (whirPaperTranscriptVectorSpec P d).length (paperTranscriptSlotIndex slot)
      = paperTranscriptSlotLength P d slot := by
  show paperTranscriptSlotLength P d
    ((Fintype.equivFin (PaperTranscriptSlot P)).symm (paperTranscriptSlotIndex slot)) = _
  rw [paperTranscriptSlotIndex_symm_apply]

/-- Read the raw vector payload of wire slot `j` off a partial transcript (requires the slot to
be visible in the prefix: `h : j < m`). -/
def trSlotVec {m : Fin (Fintype.card (PaperTranscriptSlot P) + 1)}
    (tr : Transcript m ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F))
    (j : Fin (Fintype.card (PaperTranscriptSlot P))) (h : j.val < m.val) :
    Vector F ((whirPaperTranscriptVectorSpec P d).length j) :=
  tr ⟨j.val, h⟩

/-- **Seam lemma**: appending one more entry does not change the payloads already present. -/
lemma trSlotVec_concat {m : Fin (Fintype.card (PaperTranscriptSlot P))}
    (tr : Transcript m.castSucc ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F))
    (msg : ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Type m)
    (j : Fin (Fintype.card (PaperTranscriptSlot P)))
    (h : j.val < m.castSucc.val) (h' : j.val < m.succ.val) :
    trSlotVec P d (tr.concat msg) j h' = trSlotVec P d tr j h :=
  Fin.snoc_castSucc (α := fun jj => ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Type
      (Fin.castLE m.succ.is_le jj))
    msg tr ⟨j.val, h⟩

/-- Read a visible prover message as a coefficient list. -/
def trMsgList {m : Fin (Fintype.card (PaperTranscriptSlot P) + 1)}
    (tr : Transcript m ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F))
    (j : (whirPaperTranscriptVectorSpec P d).MessageIdx)
    (h : (j.1 : Fin _).val < m.val) : List F :=
  (trSlotVec P d tr j.1 h).toList

/-- Read the field element off a visible (length-positive) vector challenge; `0` for empty
payloads (the partial-transcript analogue of `Whir302Checked.chalAt`). -/
def trChalVal {m : Fin (Fintype.card (PaperTranscriptSlot P) + 1)}
    (tr : Transcript m ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F))
    (i : (whirPaperTranscriptVectorSpec P d).ChallengeIdx)
    (h : (i.1 : Fin _).val < m.val) : F :=
  if hl : 0 < (whirPaperTranscriptVectorSpec P d).length i.1
  then (trSlotVec P d tr i.1 h).get ⟨0, hl⟩ else 0

lemma trMsgList_concat {m : Fin (Fintype.card (PaperTranscriptSlot P))}
    (tr : Transcript m.castSucc ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F))
    (msg : ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Type m)
    (j : (whirPaperTranscriptVectorSpec P d).MessageIdx)
    (h : (j.1 : Fin _).val < m.castSucc.val) (h' : (j.1 : Fin _).val < m.succ.val) :
    trMsgList P d (tr.concat msg) j h' = trMsgList P d tr j h := by
  unfold trMsgList
  rw [trSlotVec_concat P d tr msg j.1 h h']

lemma trChalVal_concat {m : Fin (Fintype.card (PaperTranscriptSlot P))}
    (tr : Transcript m.castSucc ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F))
    (msg : ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Type m)
    (i : (whirPaperTranscriptVectorSpec P d).ChallengeIdx)
    (h : (i.1 : Fin _).val < m.castSucc.val) (h' : (i.1 : Fin _).val < m.succ.val) :
    trChalVal P d (tr.concat msg) i h' = trChalVal P d tr i h := by
  unfold trChalVal
  rw [trSlotVec_concat P d tr msg i.1 h h']

end Reads

/-! ## Part C — the prefix sumcheck-consistency predicate (`predSC`) -/

section Pred

variable (P : Params ιs F) (d : ℕ)

/-- Initial-phase anchor: the step-0 sumcheck message, once visible, satisfies
`g₀(0) + g₀(1) = 0` (the honest claimed sum of the landed transcript model). -/
def initialAnchorOK {m : Fin (Fintype.card (PaperTranscriptSlot P) + 1)}
    (tr : Transcript m ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F)) : Prop :=
  ∀ (s : Fin (P.foldingParam 0)), (s : ℕ) = 0 →
    ∀ (h : ((initialSumcheckMessageIdx P d s).1 : Fin _).val < m.val),
      listEval (trMsgList P d tr (initialSumcheckMessageIdx P d s) h) 0
        + listEval (trMsgList P d tr (initialSumcheckMessageIdx P d s) h) 1 = 0

/-- Initial-phase chain links: for adjacent steps `t = s + 1`, once the step-`t` message, the
step-`s` message, and the step-`s` challenge are all visible,
`g_t(0) + g_t(1) = g_s(r_s)`. -/
def initialLinkOK {m : Fin (Fintype.card (PaperTranscriptSlot P) + 1)}
    (tr : Transcript m ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F)) : Prop :=
  ∀ (s t : Fin (P.foldingParam 0)), (t : ℕ) = (s : ℕ) + 1 →
    ∀ (ht : ((initialSumcheckMessageIdx P d t).1 : Fin _).val < m.val)
      (hs : ((initialSumcheckMessageIdx P d s).1 : Fin _).val < m.val)
      (hc : ((initialSumcheckChallengeIdx P d s).1 : Fin _).val < m.val),
      listEval (trMsgList P d tr (initialSumcheckMessageIdx P d t) ht) 0
        + listEval (trMsgList P d tr (initialSumcheckMessageIdx P d t) ht) 1
      = listEval (trMsgList P d tr (initialSumcheckMessageIdx P d s) hs)
          (trChalVal P d tr (initialSumcheckChallengeIdx P d s) hc)

/-- Main-round anchor for round `i`. -/
def mainAnchorOK (i : Fin M) {m : Fin (Fintype.card (PaperTranscriptSlot P) + 1)}
    (tr : Transcript m ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F)) : Prop :=
  ∀ (s : Fin (P.foldingParam i.succ)), (s : ℕ) = 0 →
    ∀ (h : ((mainSumcheckMessageIdx P d i s).1 : Fin _).val < m.val),
      listEval (trMsgList P d tr (mainSumcheckMessageIdx P d i s) h) 0
        + listEval (trMsgList P d tr (mainSumcheckMessageIdx P d i s) h) 1 = 0

/-- Main-round chain links for round `i`. -/
def mainLinkOK (i : Fin M) {m : Fin (Fintype.card (PaperTranscriptSlot P) + 1)}
    (tr : Transcript m ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F)) : Prop :=
  ∀ (s t : Fin (P.foldingParam i.succ)), (t : ℕ) = (s : ℕ) + 1 →
    ∀ (ht : ((mainSumcheckMessageIdx P d i t).1 : Fin _).val < m.val)
      (hs : ((mainSumcheckMessageIdx P d i s).1 : Fin _).val < m.val)
      (hc : ((mainSumcheckChallengeIdx P d i s).1 : Fin _).val < m.val),
      listEval (trMsgList P d tr (mainSumcheckMessageIdx P d i t) ht) 0
        + listEval (trMsgList P d tr (mainSumcheckMessageIdx P d i t) ht) 1
      = listEval (trMsgList P d tr (mainSumcheckMessageIdx P d i s) hs)
          (trChalVal P d tr (mainSumcheckChallengeIdx P d i s) hc)

/-- Final zero-sum check, once the final polynomial is visible. -/
def finalSumOK {m : Fin (Fintype.card (PaperTranscriptSlot P) + 1)}
    (tr : Transcript m ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F)) : Prop :=
  ∀ (h : ((finalPolynomialMessageIdx P d).1 : Fin _).val < m.val),
    (trMsgList P d tr (finalPolynomialMessageIdx P d) h).sum = 0

/-- **The prefix sumcheck-consistency predicate** for the paper-order WHIR spec: the
chain-consistency of all sumcheck steps visible in the prefix (the prefix restriction of
`whirCheckingBool`'s checks). -/
def whirChainOK {m : Fin (Fintype.card (PaperTranscriptSlot P) + 1)}
    (tr : Transcript m ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F)) : Prop :=
  initialAnchorOK P d tr ∧ initialLinkOK P d tr ∧
    (∀ i : Fin M, mainAnchorOK P d i tr) ∧ (∀ i : Fin M, mainLinkOK P d i tr) ∧
    finalSumOK P d tr

/-! ### Agreement with `whirCheckingBool` on full transcripts -/

/-- **Full-read collapse**: the checked verifier's full read of message slot `j`
(`readAns`, an enumeration of per-position oracle answers) is exactly the payload's
coefficient list. -/
theorem readAns_eq_toList
    (msgs : ∀ j, ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Message j)
    (j : ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).MessageIdx) :
    readAns P d msgs j
      = (Vector.toList
          (α := F) (n := (whirPaperTranscriptVectorSpec P d).length j.1) (msgs j)) := by
  unfold readAns
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.getElem_map, List.getElem_finRange]
    rfl

/-- Agreement of the partial-transcript message read with the verifier's full read, at the
last round (a full transcript IS a `Transcript (Fin.last _)`, definitionally). -/
theorem trMsgList_last_eq_readAns
    (tr : ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).FullTranscript)
    (j : (whirPaperTranscriptVectorSpec P d).MessageIdx)
    (h : (j.1 : Fin _).val < (Fin.last (Fintype.card (PaperTranscriptSlot P))).val) :
    trMsgList P d (m := Fin.last _) tr j h
      = readAns P d (FullTranscript.messages tr) j := by
  rw [readAns_eq_toList]
  rfl

/-- Agreement of the partial-transcript challenge read with `chalAt`, at the last round. -/
theorem trChalVal_last_eq_chalAt
    (tr : ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).FullTranscript)
    (i : (whirPaperTranscriptVectorSpec P d).ChallengeIdx)
    (h : (i.1 : Fin _).val < (Fin.last (Fintype.card (PaperTranscriptSlot P))).val) :
    trChalVal P d (m := Fin.last _) tr i h
      = chalAt P d (FullTranscript.challenges tr) i := rfl

/-- **AGREEMENT (acceptance ⟹ predicate) on full transcripts**: if the checked verifier's
decision bit (`whirCheckingBool`) is `true` on a full transcript, then the prefix
sumcheck-consistency predicate `whirChainOK` holds at the final round.  This is the direction
a challenge-tracking knowledge state function consumes at `toFun_full`: acceptance forces the
whole visible chain. -/
theorem whirChainOK_of_whirCheckingBool
    (tr : ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).FullTranscript)
    (h : whirCheckingBool P d
      (FullTranscript.messages tr) (FullTranscript.challenges tr) = true) :
    whirChainOK P d (m := Fin.last _) tr := by
  unfold whirCheckingBool at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hinit, hmain⟩, hfinal⟩ := h
  have hinit' : ∀ s, initialStepAns P d
      (FullTranscript.messages tr) (FullTranscript.challenges tr) s = true := fun s =>
    hinit _ (List.mem_map.mpr ⟨s, List.mem_finRange s, rfl⟩)
  have hmain' : ∀ i s, mainStepAns P d
      (FullTranscript.messages tr) (FullTranscript.challenges tr) i s = true := by
    intro i s
    have hr := hmain _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
    unfold mainRoundAns at hr
    rw [List.all_eq_true] at hr
    exact hr _ (List.mem_map.mpr ⟨s, List.mem_finRange s, rfl⟩)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- initial anchor
    intro s hs0 hv
    have := hinit' s
    unfold initialStepAns at this
    rw [decide_eq_true_eq, dif_pos hs0] at this
    rwa [trMsgList_last_eq_readAns P d tr _ hv]
  · -- initial links
    intro s t hst ht hs hc
    have := hinit' t
    unfold initialStepAns at this
    have hne : ¬ ((t : ℕ) = 0) := by omega
    rw [decide_eq_true_eq, dif_neg hne] at this
    have hidx : (⟨(t : ℕ) - 1, by have := t.isLt; omega⟩ : Fin (P.foldingParam 0)) = s := by
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    rw [hidx] at this
    rw [trMsgList_last_eq_readAns P d tr _ ht, trMsgList_last_eq_readAns P d tr _ hs,
      trChalVal_last_eq_chalAt P d tr _ hc]
    exact this
  · -- main anchors
    intro i s hs0 hv
    have := hmain' i s
    unfold mainStepAns at this
    rw [decide_eq_true_eq, dif_pos hs0] at this
    rwa [trMsgList_last_eq_readAns P d tr _ hv]
  · -- main links
    intro i s t hst ht hs hc
    have := hmain' i t
    unfold mainStepAns at this
    have hne : ¬ ((t : ℕ) = 0) := by omega
    rw [decide_eq_true_eq, dif_neg hne] at this
    have hidx : (⟨(t : ℕ) - 1, by have := t.isLt; omega⟩
        : Fin (P.foldingParam i.succ)) = s := by
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    rw [hidx] at this
    rw [trMsgList_last_eq_readAns P d tr _ ht, trMsgList_last_eq_readAns P d tr _ hs,
      trChalVal_last_eq_chalAt P d tr _ hc]
    exact this
  · -- final zero-sum
    intro hv
    rw [trMsgList_last_eq_readAns P d tr _ hv]
    exact hfinal

/-- **AGREEMENT (predicate ⟹ acceptance), full transcripts**: conversely, the prefix
sumcheck-consistency predicate at the final round forces the checked verifier's decision bit.
Every step check is either an anchor (`s = 0`) or a link (`s = s' + 1`). -/
theorem whirCheckingBool_of_whirChainOK
    (tr : ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).FullTranscript)
    (hchain : whirChainOK P d (m := Fin.last _) tr) :
    whirCheckingBool P d
      (FullTranscript.messages tr) (FullTranscript.challenges tr) = true := by
  obtain ⟨hanchor, hlink, hmanchor, hmlink, hfinal⟩ := hchain
  unfold whirCheckingBool
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro b hb
    rw [List.mem_map] at hb
    obtain ⟨s, -, rfl⟩ := hb
    unfold initialStepAns
    rw [decide_eq_true_eq]
    by_cases hs0 : (s : ℕ) = 0
    · rw [dif_pos hs0]
      have hv : ((initialSumcheckMessageIdx P d s).1 : Fin _).val
          < (Fin.last (Fintype.card (PaperTranscriptSlot P))).val :=
        (initialSumcheckMessageIdx P d s).1.isLt
      have := hanchor s hs0 hv
      rwa [trMsgList_last_eq_readAns P d tr _ hv] at this
    · rw [dif_neg hs0]
      have hts : (s : ℕ)
          = ((⟨(s : ℕ) - 1, by have := s.isLt; omega⟩ : Fin (P.foldingParam 0)) : ℕ) + 1 := by
        simp only [Fin.val_mk]
        omega
      have := hlink ⟨(s : ℕ) - 1, by have := s.isLt; omega⟩ s hts
        (initialSumcheckMessageIdx P d s).1.isLt
        (initialSumcheckMessageIdx P d _).1.isLt
        (initialSumcheckChallengeIdx P d _).1.isLt
      rwa [trMsgList_last_eq_readAns P d tr, trMsgList_last_eq_readAns P d tr,
        trChalVal_last_eq_chalAt P d tr] at this
  · intro b hb
    rw [List.mem_map] at hb
    obtain ⟨i, -, rfl⟩ := hb
    unfold mainRoundAns
    rw [List.all_eq_true]
    intro b' hb'
    rw [List.mem_map] at hb'
    obtain ⟨s, -, rfl⟩ := hb'
    unfold mainStepAns
    rw [decide_eq_true_eq]
    by_cases hs0 : (s : ℕ) = 0
    · rw [dif_pos hs0]
      have hv : ((mainSumcheckMessageIdx P d i s).1 : Fin _).val
          < (Fin.last (Fintype.card (PaperTranscriptSlot P))).val :=
        (mainSumcheckMessageIdx P d i s).1.isLt
      have := hmanchor i s hs0 hv
      rwa [trMsgList_last_eq_readAns P d tr _ hv] at this
    · rw [dif_neg hs0]
      have hts : (s : ℕ)
          = ((⟨(s : ℕ) - 1, by have := s.isLt; omega⟩
              : Fin (P.foldingParam i.succ)) : ℕ) + 1 := by
        simp only [Fin.val_mk]
        omega
      have := hmlink i ⟨(s : ℕ) - 1, by have := s.isLt; omega⟩ s hts
        (mainSumcheckMessageIdx P d i s).1.isLt
        (mainSumcheckMessageIdx P d i _).1.isLt
        (mainSumcheckChallengeIdx P d i _).1.isLt
      rwa [trMsgList_last_eq_readAns P d tr, trMsgList_last_eq_readAns P d tr,
        trChalVal_last_eq_chalAt P d tr] at this
  · have hv : ((finalPolynomialMessageIdx P d).1 : Fin _).val
        < (Fin.last (Fintype.card (PaperTranscriptSlot P))).val :=
      (finalPolynomialMessageIdx P d).1.isLt
    have := hfinal hv
    rwa [trMsgList_last_eq_readAns P d tr _ hv] at this

/-- **THE AGREEMENT IFF on full transcripts**: the prefix sumcheck-consistency predicate at
the final round is EXACTLY acceptance by the checked verifier's decision bit. -/
theorem whirChainOK_iff_whirCheckingBool
    (tr : ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).FullTranscript) :
    whirChainOK P d (m := Fin.last _) tr ↔
      whirCheckingBool P d
        (FullTranscript.messages tr) (FullTranscript.challenges tr) = true :=
  ⟨whirCheckingBool_of_whirChainOK P d tr, whirChainOK_of_whirCheckingBool P d tr⟩

variable {m0 : ℕ} [ReedSolomon.Smooth (P.φ 0)] [Nonempty (ιs 0)]

/-- **`predSC`** — the WHIR round-indexed state predicate for the bounded-flip shell:
δ-closeness of the input oracle (the `whirRelation` data) PLUS the prefix sumcheck-consistency
chain. -/
def whirChainClosePred (δ : ℝ≥0)
    (m : Fin (Fintype.card (PaperTranscriptSlot P) + 1))
    (stmtIn : Unit × ∀ u : Unit, OracleStatement (ιs 0) F u)
    (tr : Transcript m ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F)) : Prop :=
  (δᵣ(stmtIn.2 (), smoothCode (P.φ 0) m0) ≤ (δ : ℝ≥0∞)) ∧ whirChainOK P d tr

/-- At round 0 every visibility hypothesis is vacuous: the chain holds. -/
lemma whirChainOK_zero
    (tr : Transcript 0 ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F)) :
    whirChainOK P d tr := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s hs0 h
    exact absurd h (by simp)
  · intro s t hst ht hs hc
    exact absurd ht (by simp)
  · intro i s hs0 h
    exact absurd h (by simp)
  · intro i s t hst ht hs hc
    exact absurd ht (by simp)
  · intro h
    exact absurd h (by simp)

/-- **The `hEmpty` leg**: at round 0 the predicate is exactly δ-closeness of the input oracle,
i.e. membership in `whirRelation m0 (P.φ 0) δ`. -/
lemma whirChainClosePred_zero (δ : ℝ≥0)
    (stmtIn : Unit × ∀ u : Unit, OracleStatement (ιs 0) F u)
    (tr : Transcript 0 ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F)) :
    whirChainClosePred P d (m0 := m0) δ 0 stmtIn tr ↔
      δᵣ(stmtIn.2 (), smoothCode (P.φ 0) m0) ≤ (δ : ℝ≥0∞) :=
  ⟨fun h => h.1, fun h => ⟨h, whirChainOK_zero P d tr⟩⟩

/-- **The `hConcat` leg (chain part)**: appending one entry cannot fix a broken chain — the
visible-check set shrinks and earlier payloads are unchanged. -/
lemma whirChainOK_concat (m : Fin (Fintype.card (PaperTranscriptSlot P)))
    (tr : Transcript m.castSucc ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F))
    (msg : ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Type m)
    (h : whirChainOK P d (tr.concat msg)) : whirChainOK P d tr := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have lift : ∀ {j : Fin (Fintype.card (PaperTranscriptSlot P))},
      j.val < m.castSucc.val → j.val < m.succ.val := by
    intro j hj
    simp only [Fin.val_castSucc] at hj
    simp only [Fin.val_succ]
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s hs0 hv
    have := h1 s hs0 (lift hv)
    rwa [trMsgList_concat P d tr msg _ hv (lift hv)] at this
  · intro s t hst ht hs hc
    have := h2 s t hst (lift ht) (lift hs) (lift hc)
    rwa [trMsgList_concat P d tr msg _ ht (lift ht),
      trMsgList_concat P d tr msg _ hs (lift hs),
      trChalVal_concat P d tr msg _ hc (lift hc)] at this
  · intro i s hs0 hv
    have := h3 i s hs0 (lift hv)
    rwa [trMsgList_concat P d tr msg _ hv (lift hv)] at this
  · intro i s t hst ht hs hc
    have := h4 i s t hst (lift ht) (lift hs) (lift hc)
    rwa [trMsgList_concat P d tr msg _ ht (lift ht),
      trMsgList_concat P d tr msg _ hs (lift hs),
      trChalVal_concat P d tr msg _ hc (lift hc)] at this
  · intro hv
    have := h5 (lift hv)
    rwa [trMsgList_concat P d tr msg _ hv (lift hv)] at this

/-- **The `hConcat` leg** for the full predicate. -/
lemma whirChainClosePred_concat (δ : ℝ≥0)
    (m : Fin (Fintype.card (PaperTranscriptSlot P)))
    (stmtIn : Unit × ∀ u : Unit, OracleStatement (ιs 0) F u)
    (tr : Transcript m.castSucc ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F))
    (msg : ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Type m)
    (h : whirChainClosePred P d (m0 := m0) δ m.succ stmtIn (tr.concat msg)) :
    whirChainClosePred P d (m0 := m0) δ m.castSucc stmtIn tr :=
  ⟨h.1, whirChainOK_concat P d m tr msg h.2⟩

/-- For a statement whose oracle is genuinely far, the predicate is false at EVERY round on
EVERY transcript (so the threshold shell's flip event at the threshold is pointwise full, and
the unconditional `hFlip` at `ε < 1` is out of reach; see `predFalse_propagates`). -/
lemma whirChainClosePred_false_of_far (δ : ℝ≥0)
    (stmtIn : Unit × ∀ u : Unit, OracleStatement (ιs 0) F u)
    (hfar : ¬ (δᵣ(stmtIn.2 (), smoothCode (P.φ 0) m0) ≤ (δ : ℝ≥0∞)))
    (m : Fin (Fintype.card (PaperTranscriptSlot P) + 1))
    (tr : Transcript m ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F)) :
    ¬ whirChainClosePred P d (m0 := m0) δ m stmtIn tr :=
  fun h => hfar h.1

end Pred

/-! ## Part D — THE THEOREM: the bounded-flip shell at the checked verifier -/

section Theorems

variable (P : Params ιs F) (d : ℕ) {m0 : ℕ}
  [ReedSolomon.Smooth (P.φ 0)] [Nonempty (ιs 0)]

/-- **The conditional assembly (the shell at the checked verifier).** The checked WHIR
`VectorIOP` satisfies RBR knowledge soundness at the budget concentrated on the final
randomness challenge round, given the single remaining `hFlip` hypothesis (the flip-probability
bound for the `whirChainClosePred` state function, in EXACTLY the shell's shape). -/
theorem whirChecked_rbrKnowledgeSoundness_of_flipBound (δ ε : ℝ≥0)
    (hFlip : ∀ (stmtIn : Unit × ∀ u : Unit, OracleStatement (ιs 0) F u) (witIn : Unit)
      (prover : Prover []ₒ (Unit × ∀ u : Unit, OracleStatement (ιs 0) F u) Unit
        (Bool × (∀ _ : Empty, Unit)) Unit
        ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F)),
      Pr[fun x : ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Transcript
            (finalRandomnessChallengeIdx P d).1.castSucc ×
          ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Challenge
            (finalRandomnessChallengeIdx P d) ×
          ([]ₒ + [((whirPaperTranscriptVectorSpec P d).toProtocolSpec
              F).Challenge]ₒ'challengeOracleInterface).QueryLog =>
          ¬ whirChainClosePred P d (m0 := m0) δ
            (finalRandomnessChallengeIdx P d).1.castSucc stmtIn x.1
        | do
          (simulateQ (QueryImpl.addLift (isEmptyElim : QueryImpl []ₒ (StateT Unit ProbComp))
              challengeQueryImpl : QueryImpl _ (StateT Unit ProbComp))
            (do
              let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
                prover.runWithLogToRound (finalRandomnessChallengeIdx P d).1.castSucc
                  stmtIn witIn
              let challenge ← liftComp
                (((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).getChallenge
                  (finalRandomnessChallengeIdx P d)) _
              return (transcript, challenge, proveQueryLog))).run'
            (← (pure () : ProbComp Unit))] ≤ (ε : ℝ≥0∞)) :
    OracleProof.rbrKnowledgeSoundness (pure ()) isEmptyElim
      (whirRelation m0 (P.φ 0) δ)
      (paperTranscriptOracleVerifier P d (whirVerifyChecked P d))
      (fun i => if i = finalRandomnessChallengeIdx P d then ε else 0) := by
  unfold OracleProof.rbrKnowledgeSoundness OracleVerifier.rbrKnowledgeSoundness
  exact ThresholdKSF.rbrKnowledgeSoundness_of_flipBound (pure ()) isEmptyElim
    ((paperTranscriptOracleVerifier P d (whirVerifyChecked P d)).toVerifier)
    (whirRelation m0 (P.φ 0) δ) acceptRejectOracleRel
    (whirChainClosePred P d (m0 := m0) δ)
    (finalRandomnessChallengeIdx P d) ε
    (fun stmtIn w => by
      rw [mem_whirRelation_iff P (m0 := m0) δ stmtIn w,
        whirChainClosePred_zero P d (m0 := m0) δ stmtIn default])
    (fun m _ stmtIn tr msg h =>
      whirChainClosePred_concat P d (m0 := m0) δ m stmtIn tr msg h)
    hFlip

/-- **THE THEOREM (small-field regime, unconditional)**: at the task's budget shape
`fun i => if i = c then maxLen/|F| else 0`, the checked WHIR `VectorIOP` satisfies RBR
knowledge soundness UNCONDITIONALLY whenever `|F| ≤ maxLen` (the budget is then `≥ 1`, and the
flip-probability hypothesis is discharged by `probEvent_le_one`).  Outside this regime the
budget at the threshold cannot drop below `1` through the threshold shell — see
`ThresholdKSFFacts.predFalse_propagates` and `whirChainClosePred_false_of_far`. -/
theorem whirChecked_rbrKnowledgeSoundness_smallField (δ : ℝ≥0) (L : ℕ)
    (hL : Fintype.card F ≤ L) :
    OracleProof.rbrKnowledgeSoundness (pure ()) isEmptyElim
      (whirRelation m0 (P.φ 0) δ)
      (paperTranscriptOracleVerifier P d (whirVerifyChecked P d))
      (fun i => if i = finalRandomnessChallengeIdx P d
        then (L : ℝ≥0) / (Fintype.card F : ℝ≥0) else 0) := by
  have hcard : (0 : ℝ≥0) < (Fintype.card F : ℝ≥0) := by
    exact_mod_cast Fintype.card_pos
  have hone : (1 : ℝ≥0∞) ≤ (((L : ℝ≥0) / (Fintype.card F : ℝ≥0) : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.coe_one, ENNReal.coe_le_coe, one_le_div hcard]
    exact_mod_cast hL
  exact whirChecked_rbrKnowledgeSoundness_of_flipBound P d (m0 := m0) δ _
    (fun stmtIn witIn prover => le_trans probEvent_le_one hone)

/-- **The full security package (small-field regime)**: completeness (proven in
`CheckedVerifier.lean`) + the small-field RBR discharge give `IsSecureWithGap` for the checked
WHIR `VectorIOP` at the task's budget shape. -/
theorem whirCheckedVectorIOP_isSecureWithGap_smallField (δ : ℝ≥0) (L : ℕ)
    (hL : Fintype.card F ≤ L) :
    VectorIOP.IsSecureWithGap (whirRelation m0 (P.φ 0) 0) (whirRelation m0 (P.φ 0) δ)
      (fun i => if i = finalRandomnessChallengeIdx P d
        then (L : ℝ≥0) / (Fintype.card F : ℝ≥0) else 0)
      (whirCheckedVectorIOP P d) :=
  whirCheckedVectorIOP_isSecureWithGap_of_rbr P d (m0 := m0) δ _
    (whirChecked_rbrKnowledgeSoundness_smallField P d (m0 := m0) δ L hL)

/-- The analogous small-field discharge for `Protocol.lean`'s named residual (the pure-`true`
placeholder `VectorIOP`), at the same budget shape — the threshold state function is
verifier-agnostic. -/
theorem whirVectorIOP_rbrKnowledgeSoundness_smallField (δ : ℝ≥0) (L : ℕ)
    (hL : Fintype.card F ≤ L) :
    whirVectorIOP_rbrKnowledgeSoundness P d (m0 := m0) δ
      (fun i => if i = finalRandomnessChallengeIdx P d
        then (L : ℝ≥0) / (Fintype.card F : ℝ≥0) else 0) := by
  have hcard : (0 : ℝ≥0) < (Fintype.card F : ℝ≥0) := by
    exact_mod_cast Fintype.card_pos
  have hone : (1 : ℝ≥0∞) ≤ (((L : ℝ≥0) / (Fintype.card F : ℝ≥0) : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.coe_one, ENNReal.coe_le_coe, one_le_div hcard]
    exact_mod_cast hL
  unfold whirVectorIOP_rbrKnowledgeSoundness OracleProof.rbrKnowledgeSoundness
    OracleVerifier.rbrKnowledgeSoundness
  exact ThresholdKSF.rbrKnowledgeSoundness_of_flipBound (pure ()) isEmptyElim
    ((whirVectorIOP P d).verifier.toVerifier)
    (whirRelation m0 (P.φ 0) δ) acceptRejectOracleRel
    (whirChainClosePred P d (m0 := m0) δ)
    (finalRandomnessChallengeIdx P d) _
    (fun stmtIn w => by
      rw [mem_whirRelation_iff P (m0 := m0) δ stmtIn w,
        whirChainClosePred_zero P d (m0 := m0) δ stmtIn default])
    (fun m _ stmtIn tr msg h =>
      whirChainClosePred_concat P d (m0 := m0) δ m stmtIn tr msg h)
    (fun stmtIn witIn prover => le_trans probEvent_le_one hone)

end Theorems

end Whir302SubUnit

/-! ## Part E — the `hFlip` quantitative core: uniform challenge marginal + the salvage-event
bound in the exact RBR game shape -/

namespace Whir302SubUnit

section SalvageGame

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]

/-- The field element read off a vector challenge (the `chalAt` read pattern). -/
def chalElemOf {n : ℕ} (vspec : ProtocolSpec.VectorSpec n)
    (c : (vspec.toProtocolSpec F).ChallengeIdx)
    (v : (vspec.toProtocolSpec F).Challenge c) : F :=
  if h : 0 < vspec.length c.1 then v.get ⟨0, h⟩ else 0

/-- Reading position 0 of a length-1 vector is a bijection onto `F`. -/
private lemma vecHead_bijective {k : ℕ} (hk : k = 1) :
    Function.Bijective
      (fun v : Vector F k => if h : 0 < k then v.get ⟨0, h⟩ else 0) := by
  subst hk
  constructor
  · intro v w hvw
    simp only [dif_pos Nat.one_pos] at hvw
    ext i hi
    have hi0 : i = 0 := by omega
    subst hi0
    exact hvw
  · intro y
    refine ⟨Vector.replicate 1 y, ?_⟩
    simp only [dif_pos Nat.one_pos]
    exact Vector.getElem_replicate _

/-- **The marginal-domination fact** (the uniform challenge marginal): for a length-1 vector
challenge slot, the field element read off a uniformly drawn challenge is EXACTLY uniform on
`F` — the carried marginal of the RBR game's fresh challenge. -/
lemma probEvent_chalElemOf_eq_uniform {n : ℕ} (vspec : ProtocolSpec.VectorSpec n)
    [∀ i, SampleableType ((vspec.toProtocolSpec F).Challenge i)]
    (c : (vspec.toProtocolSpec F).ChallengeIdx) (hc : vspec.length c.1 = 1) (x : F) :
    Pr[fun v => chalElemOf vspec c v = x | $ᵗ ((vspec.toProtocolSpec F).Challenge c)]
      = (Fintype.card F : ℝ≥0∞)⁻¹ := by
  haveI : Finite ((vspec.toProtocolSpec F).Challenge c) := by
    show Finite (Vector F (vspec.length c.1))
    infer_instance
  show Pr[((· = x) ∘ chalElemOf vspec c) | $ᵗ ((vspec.toProtocolSpec F).Challenge c)]
      = (Fintype.card F : ℝ≥0∞)⁻¹
  rw [← probEvent_map, probEvent_eq_eq_probOutput,
    probOutput_map_bijective_uniform_cross ((vspec.toProtocolSpec F).Challenge c)
      (chalElemOf vspec c) (vecHead_bijective (F := F) hc) x,
    probOutput_uniformSample]

variable {ι : Type} {oSpec : OracleSpec ι} {n : ℕ} {vspec : ProtocolSpec.VectorSpec n}
  [∀ i, SampleableType ((vspec.toProtocolSpec F).Challenge i)]
  {StmtIn StmtOut WitIn WitOut : Type} {σ : Type}

open Whir302SZ Whir302Checked in
/-- **The salvage-event bound in the exact RBR game shape** (the `hFlip` quantitative core):
in the round-`c` RBR game (arbitrary prover prefix with logging, then a fresh uniform vector
challenge at a length-1 challenge slot), the probability that two prefix-measurable coefficient
chains genuinely differ as polynomials YET the fresh challenge satisfies the salvage equation
`listEval cs r = listEval cs' r` is at most `L / |F|` for any `L` bounding both chain lengths.

This is the textbook per-round sumcheck flip estimate, proven against ArkLib's actual execution
semantics.  Consuming it as the shell's `hFlip` requires a knowledge state function that keeps
tracking the chain PAST round `c` (so the flip event becomes this salvage event); the threshold
state function cannot (its flip event at the threshold is challenge-independent). -/
theorem probEvent_salvage_game_le
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (c : (vspec.toProtocolSpec F).ChallengeIdx) (hc : vspec.length c.1 = 1)
    (cs cs' : (vspec.toProtocolSpec F).Transcript c.1.castSucc → List F) (L : ℕ)
    (hcs : ∀ tr, cs tr ≠ []) (hcs' : ∀ tr, cs' tr ≠ [])
    (hL : ∀ tr, max (cs tr).length (cs' tr).length ≤ L)
    (stmtIn : StmtIn) (witIn : WitIn)
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut (vspec.toProtocolSpec F)) :
    Pr[fun x : (vspec.toProtocolSpec F).Transcript c.1.castSucc ×
          (vspec.toProtocolSpec F).Challenge c ×
          (oSpec + [(vspec.toProtocolSpec F).Challenge]ₒ'challengeOracleInterface).QueryLog =>
        listPoly (cs x.1) ≠ listPoly (cs' x.1) ∧
          listEval (cs x.1) (chalElemOf vspec c x.2.1)
            = listEval (cs' x.1) (chalElemOf vspec c x.2.1)
      | do
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
              prover.runWithLogToRound c.1.castSucc stmtIn witIn
            let challenge ← liftComp ((vspec.toProtocolSpec F).getChallenge c) _
            return (transcript, challenge, proveQueryLog))).run' (← init)]
      ≤ (L : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  classical
  -- peel the init draw
  refine probEvent_bind_le_of_forall_support init _ _ _ (fun s _ => ?_)
  -- distribute the simulation over the prefix bind
  rw [simulateQ_bind, StateT.run'_bind_lib]
  -- peel the prover prefix
  refine probEvent_bind_le_of_forall_support _ _ _ _ (fun rk _ => ?_)
  obtain ⟨⟨⟨tr, pst⟩, log⟩, s'⟩ := rk
  dsimp only
  -- the challenge draw in `liftM` form, then the uniform average over the drawn challenge
  rw [liftComp_eq_liftM]
  rw [ChallengeCoherence.probEvent_run'_simulateQ_addLift_getChallenge_bind impl s' c
    (fun ch => pure (tr, ch, log)) _]
  -- collapse the pure trailing stage and recombine the average into a bind
  simp only [simulateQ_pure, StateT.run'_pure_lib]
  rw [← probEvent_bind_eq_tsum]
  -- the two chains at this fixed prefix
  by_cases hD : listPoly (cs tr) ≠ listPoly (cs' tr)
  · -- genuinely different chains: comap Schwartz–Zippel at the carried field element
    refine le_trans (probEvent_salvage_le_comap ($ᵗ ((vspec.toProtocolSpec F).Challenge c))
      (chalElemOf vspec c) (fun ch => pure (tr, ch, log)) _
      (cs tr) (cs' tr) hD (hcs tr) (hcs' tr)
      (fun x => le_of_eq (probEvent_chalElemOf_eq_uniform vspec c hc x)) ?_) ?_
    · -- the continuation forces the salvage equation at the carried value
      intro ch hch
      refine probEvent_eq_zero ?_
      rintro x hx ⟨-, heq⟩
      simp only [support_pure, Set.mem_singleton_iff] at hx
      subst hx
      exact hch heq
    · exact ENNReal.div_le_div_right (by exact_mod_cast hL tr) _
  · -- the chains agree as polynomials: the event is empty at this prefix
    refine le_trans (le_of_eq (probEvent_eq_zero ?_)) (zero_le)
    rintro x hx ⟨hne, -⟩
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
      exists_prop] at hx
    obtain ⟨ch, -, rfl⟩ := hx
    exact hD hne

end SalvageGame

/-! ### WHIR instantiation of the salvage-game bound: every sumcheck challenge slot of the
paper-order spec has a length-1 payload, so the bound applies verbatim at those rounds. -/

section WhirSalvage

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {M : ℕ} {ιs : Fin (M + 1) → Type} [∀ i : Fin (M + 1), Fintype (ιs i)]

/-- Initial-phase sumcheck challenge slots have length-1 payloads. -/
lemma length_initialSumcheckChallengeIdx (P : Params ιs F) (d : ℕ)
    (s : Fin (P.foldingParam 0)) :
    (whirPaperTranscriptVectorSpec P d).length (initialSumcheckChallengeIdx P d s).1 = 1 :=
  length_slotIndex P d (.initialSumcheckChallenge s)

/-- Main-round sumcheck challenge slots have length-1 payloads. -/
lemma length_mainSumcheckChallengeIdx (P : Params ιs F) (d : ℕ) (i : Fin M)
    (s : Fin (P.foldingParam i.succ)) :
    (whirPaperTranscriptVectorSpec P d).length (mainSumcheckChallengeIdx P d i s).1 = 1 :=
  length_slotIndex P d (.mainSumcheckChallenge i s)

set_option maxHeartbeats 1600000 in
open Whir302SZ Whir302Checked in
/-- The salvage-event bound at a WHIR initial-phase sumcheck challenge round, for arbitrary
prefix-measurable chains: the quantitative flip core at the concrete paper-order spec. -/
theorem whir_salvage_initial_le {StmtIn StmtOut WitIn WitOut σ : Type}
    (P : Params ιs F) (d : ℕ) (s : Fin (P.foldingParam 0))
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (cs cs' : ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Transcript
      (initialSumcheckChallengeIdx P d s).1.castSucc → List F) (L : ℕ)
    (hcs : ∀ tr, cs tr ≠ []) (hcs' : ∀ tr, cs' tr ≠ [])
    (hL : ∀ tr, max (cs tr).length (cs' tr).length ≤ L)
    (stmtIn : StmtIn) (witIn : WitIn)
    (prover : Prover []ₒ StmtIn WitIn StmtOut WitOut
      ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F)) :
    Pr[fun x : ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Transcript
          (initialSumcheckChallengeIdx P d s).1.castSucc ×
        ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Challenge
          (initialSumcheckChallengeIdx P d s) ×
        ([]ₒ + [((whirPaperTranscriptVectorSpec P d).toProtocolSpec
            F).Challenge]ₒ'challengeOracleInterface).QueryLog =>
        listPoly (cs x.1) ≠ listPoly (cs' x.1) ∧
          listEval (cs x.1)
              (chalElemOf (whirPaperTranscriptVectorSpec P d)
                (initialSumcheckChallengeIdx P d s) x.2.1)
            = listEval (cs' x.1)
              (chalElemOf (whirPaperTranscriptVectorSpec P d)
                (initialSumcheckChallengeIdx P d s) x.2.1)
      | do
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
              prover.runWithLogToRound (initialSumcheckChallengeIdx P d s).1.castSucc
                stmtIn witIn
            let challenge ← liftComp
              (((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).getChallenge
                (initialSumcheckChallengeIdx P d s)) _
            return (transcript, challenge, proveQueryLog))).run' (← init)]
      ≤ (L : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  -- NOTE: a direct term-mode application busts the `whnf` heartbeat budget on the final
  -- defeq check at the concrete paper spec; congruence-guided matching is cheap.
  convert probEvent_salvage_game_le init impl (initialSumcheckChallengeIdx P d s)
    (length_initialSumcheckChallengeIdx P d s) cs cs' L hcs hcs' hL stmtIn witIn prover
    using 1

set_option maxHeartbeats 1600000 in
open Whir302SZ Whir302Checked in
/-- The salvage-event bound at a WHIR main-round sumcheck challenge round, for arbitrary
prefix-measurable chains: the quantitative flip core at the concrete paper-order spec. -/
theorem whir_salvage_main_le {StmtIn StmtOut WitIn WitOut σ : Type}
    (P : Params ιs F) (d : ℕ) (i : Fin M) (s : Fin (P.foldingParam i.succ))
    (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (cs cs' : ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Transcript
      (mainSumcheckChallengeIdx P d i s).1.castSucc → List F) (L : ℕ)
    (hcs : ∀ tr, cs tr ≠ []) (hcs' : ∀ tr, cs' tr ≠ [])
    (hL : ∀ tr, max (cs tr).length (cs' tr).length ≤ L)
    (stmtIn : StmtIn) (witIn : WitIn)
    (prover : Prover []ₒ StmtIn WitIn StmtOut WitOut
      ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F)) :
    Pr[fun x : ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Transcript
          (mainSumcheckChallengeIdx P d i s).1.castSucc ×
        ((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).Challenge
          (mainSumcheckChallengeIdx P d i s) ×
        ([]ₒ + [((whirPaperTranscriptVectorSpec P d).toProtocolSpec
            F).Challenge]ₒ'challengeOracleInterface).QueryLog =>
        listPoly (cs x.1) ≠ listPoly (cs' x.1) ∧
          listEval (cs x.1)
              (chalElemOf (whirPaperTranscriptVectorSpec P d)
                (mainSumcheckChallengeIdx P d i s) x.2.1)
            = listEval (cs' x.1)
              (chalElemOf (whirPaperTranscriptVectorSpec P d)
                (mainSumcheckChallengeIdx P d i s) x.2.1)
      | do
        (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
          (do
            let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
              prover.runWithLogToRound (mainSumcheckChallengeIdx P d i s).1.castSucc
                stmtIn witIn
            let challenge ← liftComp
              (((whirPaperTranscriptVectorSpec P d).toProtocolSpec F).getChallenge
                (mainSumcheckChallengeIdx P d i s)) _
            return (transcript, challenge, proveQueryLog))).run' (← init)]
      ≤ (L : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  convert probEvent_salvage_game_le init impl (mainSumcheckChallengeIdx P d i s)
    (length_mainSumcheckChallengeIdx P d i s) cs cs' L hcs hcs' hL stmtIn witIn prover
    using 1

end WhirSalvage

end Whir302SubUnit

end

/-! ## Axiom audit -/

#print axioms Whir302SZ.listPoly_eval
#print axioms Whir302SZ.card_listEval_eq_le
#print axioms Whir302SZ.probEvent_salvage_le
#print axioms Whir302SZ.probEvent_salvage_le_comap
#print axioms ThresholdKSFFacts.predFalse_propagates
#print axioms Whir302SubUnit.length_slotIndex
#print axioms Whir302SubUnit.trSlotVec_concat
#print axioms Whir302SubUnit.trMsgList_concat
#print axioms Whir302SubUnit.trChalVal_concat
#print axioms Whir302SubUnit.whirChainOK_zero
#print axioms Whir302SubUnit.whirChainClosePred_zero
#print axioms Whir302SubUnit.whirChainOK_concat
#print axioms Whir302SubUnit.whirChainClosePred_concat
#print axioms Whir302SubUnit.readAns_eq_toList
#print axioms Whir302SubUnit.trMsgList_last_eq_readAns
#print axioms Whir302SubUnit.trChalVal_last_eq_chalAt
#print axioms Whir302SubUnit.whirChainOK_of_whirCheckingBool
#print axioms Whir302SubUnit.whirCheckingBool_of_whirChainOK
#print axioms Whir302SubUnit.whirChainOK_iff_whirCheckingBool
#print axioms Whir302SubUnit.whirChainClosePred_false_of_far
#print axioms Whir302SubUnit.whirChecked_rbrKnowledgeSoundness_of_flipBound
#print axioms Whir302SubUnit.whirChecked_rbrKnowledgeSoundness_smallField
#print axioms Whir302SubUnit.whirCheckedVectorIOP_isSecureWithGap_smallField
#print axioms Whir302SubUnit.whirVectorIOP_rbrKnowledgeSoundness_smallField
#print axioms Whir302SubUnit.probEvent_chalElemOf_eq_uniform
#print axioms Whir302SubUnit.probEvent_salvage_game_le
#print axioms Whir302SubUnit.whir_salvage_initial_le
#print axioms Whir302SubUnit.whir_salvage_main_le
