/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.FriCompleteFinalRound
import ProximityPrize.Extensions.ProofSystem.Fri.Spec.Completeness
import ArkLib.OracleReduction.Composition.Sequential.AppendOracleAdapters
import ArkLib.OracleReduction.Composition.Sequential.SeqComposePerfectCompletenessChallengeThreaded

/-!
# FRI: folding-phase perfect completeness — toward discharging the Brick D residual

This module assembles the FRI folding-phase completeness from the per-round legs
(`foldRoundPerfectCompletenessResidual_holds`, `finalFoldRoundPerfectCompletenessResidual_holds`)
via the n-ary challenge-seam `seqCompose` keystone
(`OracleReduction.seqCompose_perfectCompleteness_challenge_threaded`).

Assembly plan (see the campaign notes): (i) `perfectCompleteness` is monotone in the output
relation (`perfectCompleteness_mono_relOut` below); (ii) the round relations chain through the
`j`-indexed family `foldChainRel` (the canonical witness-proximity clause of
`FoldPhase.inputRelation`, generic in the round index); (iii) each round's output relation
entails the next round's input relation (forgetting the folding-consistency clause);
(iv–vi) the keystone application and the final binary challenge-seam append.
-/

namespace Fri.Spec.Completeness

open OracleSpec OracleComp ProtocolSpec NNReal Domain Finset

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {n : ℕ} {k : ℕ} {s : Fin (k + 1) → ℕ+} {d : ℕ+}
variable {ω : SmoothCosetFftDomain n F}
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-- **`perfectCompleteness` is monotone in the output relation** (for plain reductions).
If every output in `relOut` is also in `relOut'`, perfect completeness w.r.t. `relOut`
implies perfect completeness w.r.t. `relOut'`. Candidate for upstreaming to
`OracleReduction/Security/Basic.lean`. -/
theorem _root_.Reduction.perfectCompleteness_mono_relOut
    {ι : Type} {oSpec : OracleSpec ι}
    {σ' : Type} {init' : ProbComp σ'} {impl' : QueryImpl oSpec (StateT σ' ProbComp)}
    {StmtIn WitIn StmtOut WitOut : Type} {m : ℕ} {pSpec : ProtocolSpec m}
    [∀ j, SampleableType (pSpec.Challenge j)]
    {R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec}
    {relIn : Set (StmtIn × WitIn)} {relOut relOut' : Set (StmtOut × WitOut)}
    (hsub : relOut ⊆ relOut')
    (h : R.perfectCompleteness init' impl' relIn relOut) :
    R.perfectCompleteness init' impl' relIn relOut' := by
  intro stmtIn witIn hmem
  refine le_trans (h stmtIn witIn hmem) ?_
  refine prEvent_mono _ _ _ ?_
  rintro ⟨⟨_, prvOut, witOut⟩, stmtOut⟩ ⟨hrel, hagree⟩
  exact ⟨hsub hrel, hagree⟩

/-- **Oracle-level output-relation monotonicity for `perfectCompleteness`.** Definitionally the
`toReduction` statement of `Reduction.perfectCompleteness_mono_relOut`. -/
theorem _root_.OracleReduction.perfectCompleteness_mono_relOut
    {ι : Type} {oSpec : OracleSpec ι}
    {σ' : Type} {init' : ProbComp σ'} {impl' : QueryImpl oSpec (StateT σ' ProbComp)}
    {StmtIn WitIn StmtOut WitOut : Type}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [∀ j, OracleInterface (OStmtIn j)]
    {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [∀ j, OracleInterface (OStmtOut j)]
    {m : ℕ} {pSpec : ProtocolSpec m}
    [∀ j, OracleInterface (pSpec.Message j)]
    [∀ j, SampleableType (pSpec.Challenge j)]
    {R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec}
    {relIn : Set ((StmtIn × ∀ j, OStmtIn j) × WitIn)}
    {relOut relOut' : Set ((StmtOut × ∀ j, OStmtOut j) × WitOut)}
    (hsub : relOut ⊆ relOut')
    (h : R.perfectCompleteness init' impl' relIn relOut) :
    R.perfectCompleteness init' impl' relIn relOut' :=
  Reduction.perfectCompleteness_mono_relOut hsub h

/-! ### The j-indexed round-chaining relation -/

/-- The canonical round-chaining relation: the latest oracle is within relative Hamming distance
`δ` of its witness polynomial. The older exact-witness/positive-radius definition is preserved in
the migration audit; canonical FRI admits proximity inputs and does not require `0 < δ`. -/
def foldChainRel (j : Fin (k + 1)) (_cond : ∑ i, (s i).1 ≤ n) (δ : ℝ≥0) :
    Set
      ((Statement F j × (∀ j', OracleStatement s ω j j')) × Witness F s d j.castSucc) :=
  fun ⟨⟨_, ostmt⟩, w⟩ =>
    Code.relHammingDist (ostmt (Fin.last j.val)) (fun x => w.1.eval x.1) ≤ δ

/-- Historical exact-chain data, retained separately from the canonical proximity relation.
It records a positive radius, Reed–Solomon proximity and exact witness evaluation. -/
def Compatibility.exactFoldChainRel (j : Fin (k + 1)) (_cond : ∑ i, (s i).1 ≤ n) (δ : ℝ≥0) :
    Set
      ((Statement F j × (∀ j', OracleStatement s ω j j')) × Witness F s d j.castSucc) :=
  fun ⟨⟨_, ostmt⟩, w⟩ =>
    let N := ∑ j' ∈ finRangeTo (k + 1) (Fin.last j.val).val, (s j').1
    let dom := ω.subdomain N
    let f : Fin (2 ^ (n - N)) → F :=
      fun idx => ostmt (Fin.last j.val)
        ⟨dom idx, Finset.mem_image.mpr ⟨idx, Finset.mem_univ _, rfl⟩⟩
    (0 < δ ∧
      δᵣ(f, (_root_.ReedSolomon.code (↑dom : Fin (2 ^ (n - N)) ↪ F)
        (2 ^ ((∑ j', (s j').1) - N) * d.1) : Set _)) ≤ ↑δ) ∧
    (∀ (idx : Fin (2 ^ (n - N))), f idx = w.1.eval (dom idx : F))


/-- Exact-chain data imply the canonical witness-proximity relation. No converse is asserted. -/
lemma Compatibility.exactFoldChainRel_subset_foldChainRel
    (j : Fin (k + 1)) (cond : ∑ i, (s i).1 ≤ n) (δ : ℝ≥0) :
    Compatibility.exactFoldChainRel (s := s) (d := d) (ω := ω) j cond δ ⊆
      foldChainRel (s := s) (d := d) j cond δ := by
  rintro ⟨⟨stmt, oracles⟩, wit⟩ h
  have heval := h.2
  have horacle : oracles (Fin.last j.val) = fun x => wit.1.eval x.1 := by
    funext x
    obtain ⟨idx, _, hidx⟩ := Finset.mem_image.mp x.property
    have hx : x = ⟨(ω.subdomain
        (∑ j' ∈ finRangeTo (k + 1) (Fin.last j.val).val, (s j').1)) idx,
        Finset.mem_image.mpr ⟨idx, Finset.mem_univ _, rfl⟩⟩ := Subtype.ext hidx.symm
    rw [hx]
    exact heval idx
  change Code.relHammingDist (oracles (Fin.last j.val)) (fun x => wit.1.eval x.1) ≤ δ
  rw [horacle]
  unfold Code.relHammingDist
  erw [hammingDist_self]
  simp

/-- `FoldPhase.inputRelation` at round `i` is the chaining relation at `i.castSucc`. -/
lemma inputRelation_eq_foldChainRel (i : Fin k) (cond : ∑ i, (s i).1 ≤ n) (δ : ℝ≥0) :
    FoldPhase.inputRelation s (ω := ω) d i cond δ
      = foldChainRel (s := s) (d := d) i.castSucc cond δ := rfl

/-- `FoldPhase.outputRelation` at round `i` entails the chaining relation at `i.succ`
(forget the folding-consistency clause). -/
lemma outputRelation_subset_foldChainRel (i : Fin k) (cond : ∑ i, (s i).1 ≤ n) (δ : ℝ≥0) :
    FoldPhase.outputRelation s (ω := ω) d i cond δ
      ⊆ foldChainRel (s := s) (d := d) i.succ cond δ := by
  exact fun _ h => h

/-! ### n-ary composition of the non-final folding rounds -/

set_option maxHeartbeats 2000000 in
/-- **Perfect completeness of the composed non-final folding rounds.** The `seqCompose` of the
`k` fold rounds is perfectly complete from the round-`0` chaining relation to the round-`k`
chaining relation: each leg is the discharged per-round residual
(`foldRoundPerfectCompletenessResidual_holds`), weakened into the chain by
`outputRelation_subset_foldChainRel`, composed by the n-ary challenge-seam keystone. -/
theorem seqComposeFoldRounds_perfectCompleteness
    (cond : ∑ i, (s i).1 ≤ n) (δ : ℝ≥0) (hInit : NeverFail init) :
    (OracleReduction.seqCompose
        (fun j => Statement F j) (fun j => OracleStatement s ω j)
        (fun (j : Fin (k + 1)) => Witness F s d j.castSucc)
        (fun i => FoldPhase.foldOracleReduction s (ω := ω) d i)).perfectCompleteness
      init impl
      (foldChainRel (s := s) (d := d) 0 cond δ)
      (foldChainRel (s := s) (d := d) (Fin.last k) cond δ) := by
  refine OracleReduction.seqCompose_perfectCompleteness_challenge_threaded
    (fun j => Statement F j) (fun j => OracleStatement s ω j)
    (fun (j : Fin (k + 1)) => Witness F s d j.castSucc)
    (fun i => FoldPhase.foldOracleReduction s (ω := ω) d i)
    (fun j => foldChainRel (s := s) (d := d) j cond δ)
    (fun i => ⟨by omega, rfl⟩)
    hInit
    (by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])
    (fun t => t.elim)
    (fun t => t.elim)
    (fun i => OracleReduction.perfectCompleteness_mono_relOut
      (outputRelation_subset_foldChainRel (s := s) (d := d) i cond δ)
      (foldRoundPerfectCompletenessResidual_holds init impl hInit i cond δ))

/-! ### Bridges into the stated FRI relations -/

/-- The chaining relation at the last index is the final round's input relation. -/
lemma foldChainRel_last_eq_finalInput (cond : ∑ i, (s i).1 ≤ n) (δ : ℝ≥0) :
    foldChainRel (s := s) (d := d) (ω := ω) (Fin.last k) cond δ
      = FinalFoldPhase.inputRelation s (ω := ω) d cond δ := rfl

/-- The composed-protocol input relation is the chaining relation at round `0`. -/
lemma generalInputRelation_eq_foldChainRel
    (dom_size_cond : (2 ^ (∑ i, (s i).1)) * d ≤ 2 ^ n) (δ : ℝ≥0) :
    Fri.Spec.inputRelation k s d dom_size_cond δ
      = foldChainRel (s := s) (d := d) (ω := ω) 0 (round_bound dom_size_cond) δ := by
  cases k with
  | zero => rfl
  | succ k' => rfl

/-! ### Brick D — folding phase: residual discharged -/

/-- Statement-level sampleability of the appended fold+final challenge spec (instance search
does not find the canonical append instance through the `pSpecFold` redex on its own). -/
noncomputable local instance instFoldPlusFinalChallengeSampleable :
    ∀ i, SampleableType ((pSpecFold k s (ω := ω) ++ₚ FinalFoldPhase.pSpec F).Challenge i) :=
  fun i => instSampleableTypeChallengeAppend i

set_option maxHeartbeats 4000000 in
/-- **Perfect completeness of the full FRI folding phase** (`k` fold rounds + final round),
from the round-`0` chaining relation to the final-round output relation. -/
theorem reductionFold_perfectCompleteness
    (dom_size_cond : (2 ^ (∑ i, (s i).1)) * d ≤ 2 ^ n)
    (hInit : NeverFail init) (δ : ℝ≥0) :
    (reductionFold k s d (ω := ω)).perfectCompleteness init impl
      (foldChainRel (s := s) (d := d) 0 (round_bound dom_size_cond) δ)
      (FinalFoldPhase.outputRelation s (ω := ω) d (round_bound dom_size_cond) δ) := by
  haveI : ∀ j, Fintype ((pSpecFold k s (ω := ω)).Challenge j) :=
    seqComposeChallenge_fintype _
  haveI : ∀ j, Inhabited ((pSpecFold k s (ω := ω)).Challenge j) :=
    seqComposeChallenge_inhabited _
  haveI : ∀ j, Fintype (((pSpecFold k s (ω := ω)) ++ₚ (FinalFoldPhase.pSpec F)).Challenge j) :=
    appendChallenge_fintype _ _
  haveI : ∀ j, Inhabited
      (((pSpecFold k s (ω := ω)) ++ₚ (FinalFoldPhase.pSpec F)).Challenge j) :=
    appendChallenge_inhabited _ _
  have h2' : (FinalFoldPhase.finalFoldOracleReduction (k := k) s d
        (ω := ω)).perfectCompleteness init impl
      (foldChainRel (s := s) (d := d) (Fin.last k) (round_bound dom_size_cond) δ)
      (FinalFoldPhase.outputRelation s (ω := ω) d (round_bound dom_size_cond) δ) := by
    rw [foldChainRel_last_eq_finalInput]
    exact finalFoldRoundPerfectCompletenessResidual_holds init impl hInit
      (round_bound dom_size_cond) δ
  have hDir : ((pSpecFold k s (ω := ω)) ++ₚ (FinalFoldPhase.pSpec F)).dir
      (⟨Fin.vsum fun (_ : Fin k) => 2, by omega⟩ :
        Fin ((Fin.vsum fun (_ : Fin k) => 2) + 2)) = .V_to_P := by
    rw [show (⟨Fin.vsum fun (_ : Fin k) => 2, by omega⟩ :
          Fin ((Fin.vsum fun (_ : Fin k) => 2) + 2))
        = Fin.natAdd (Fin.vsum fun (_ : Fin k) => 2) ⟨0, by omega⟩ from by ext; simp]
    rw [Prover.append_dir_natAdd]
    rfl
  have happ := OracleReduction.append_perfectCompleteness_challenge _ _
    (seqComposeFoldRounds_perfectCompleteness init impl (round_bound dom_size_cond) δ hInit)
    h2' (by omega) hDir rfl
    (fun t => t.elim) (fun t => t.elim) hInit
  exact happ

set_option maxHeartbeats 4000000 in
/-- **Brick D — folding-phase perfect completeness (residual DISCHARGED).** The hypotheses of
the residual are themselves the discharged per-round residual theorems, so this instance is
fully unconditional (given `hInit`). -/
theorem foldPhasePerfectCompletenessStatement_holds
    (dom_size_cond : (2 ^ (∑ i, (s i).1)) * d ≤ 2 ^ n)
    (hInit : NeverFail init) (δ : ℝ≥0) :
    foldPhasePerfectCompletenessStatement (k := k) (s := s) (d := d) (ω := ω) init impl
      dom_size_cond hInit δ
      (fun i => foldRoundPerfectCompletenessResidual_holds init impl hInit i
        (round_bound dom_size_cond) δ)
      (finalFoldRoundPerfectCompletenessResidual_holds init impl hInit
        (round_bound dom_size_cond) δ) := by
  unfold foldPhasePerfectCompletenessStatement
  rw [generalInputRelation_eq_foldChainRel]
  exact reductionFold_perfectCompleteness init impl dom_size_cond hInit δ

end Fri.Spec.Completeness

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Reduction.perfectCompleteness_mono_relOut
#print axioms OracleReduction.perfectCompleteness_mono_relOut
#print axioms Fri.Spec.Completeness.seqComposeFoldRounds_perfectCompleteness
#print axioms Fri.Spec.Completeness.reductionFold_perfectCompleteness
#print axioms Fri.Spec.Completeness.foldPhasePerfectCompletenessStatement_holds

#print axioms Fri.Spec.Completeness.Compatibility.exactFoldChainRel_subset_foldChainRel
