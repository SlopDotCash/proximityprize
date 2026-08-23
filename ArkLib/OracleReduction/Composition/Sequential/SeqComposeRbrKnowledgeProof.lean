/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.General
import ArkLib.OracleReduction.Composition.Sequential.AppendToVerifierKeystone
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeFailingDetEmpty
import ArkLib.OracleReduction.Composition.Sequential.SeqComposeMsgCompleteness

/-!
# n-ary `seqCompose` round-by-round knowledge soundness (failing-deterministic components)

This file proves the n-ary sequential-composition rbr **knowledge**-soundness theorem at both the
`Verifier` and `OracleVerifier` levels, discharging the pass-through hypothesis of
`OracleVerifier.seqCompose_rbrKnowledgeSoundness` (`General.lean`) for chains of
*failing-deterministic* verifiers (the RingSwitching/sumcheck shape
`⟨fun s tr => OptionT.mk (pure (verify? s tr))⟩`, witnesses supplied by
`OracleVerifier.toVerifier_eq_failingDet_of_collapse` and the composition combinators).

The induction (on the number of components `m`) merges the two proven templates:

* the error-bookkeeping mechanics of `ArkLib.SeqComposeRbrSoundness.seqCompose_rbrSoundness_of_append`
  (`ProofSystem/Sumcheck/Spec/SeqComposeRbrSoundness.lean`) — base case `Verifier.id` + vanishing
  composed error, successor case `seqCompose_succ` + the combinatorial bridge
  `seqComposeError_eq_append` reconciling the `Sum.elim`-routed binary error with the
  `seqComposeChallengeIdxToSigma`-indexed composed error;
* the seam-hypothesis derivations of `Reduction.seqCompose_perfectCompleteness_threaded`
  (`SeqComposePerfectCompletenessThreaded.lean`) — the `Nat.eq_zero_or_pos` split into the
  **message seam** (nonempty `P_to_V`-leading tail, handled by the proven
  `Verifier.append_rbrKnowledgeSoundness_failingDet_subsingleton` keystone, with seam direction
  derived via `ProtocolSpec.seqCompose_appendValid` + `Prover.append_dir_natAdd`) and the
  **empty seam** (single trailing component, handled by the residual-free
  `Verifier.append_rbrKnowledgeSoundness_failingDet_empty` keystone).

The `OracleVerifier` level is obtained from the `Verifier` level by the n-ary verifier fusion
`(OracleVerifier.seqCompose …).toVerifier = Verifier.seqCompose …` (re-derived here from the proven
binary `OracleReduction.oracleVerifier_append_toVerifier`, mirroring
`OracleVerifier.seqCompose_toVerifier_of_binary_for_rbr`), since
`OracleVerifier.rbrKnowledgeSoundness` is definitionally `toVerifier`-level.

The combinatorial bridge `seqComposeError_eq_append` is re-derived publicly here (it is `private`
in `General.lean`, which is swarm-contended and so not edited).

No `sorry`, no `admit`, no new axioms: the only hypotheses are the per-component data
(failing-determinism witnesses, per-component rbr knowledge soundness, `P_to_V`-leading
nonemptiness) and the stateless-regime side conditions (`Subsingleton σ`, reachable lossless
`init`) consumed by the proven binary keystones.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped ENNReal NNReal

namespace ArkLib.SeqComposeRbrKnowledge

/-! ## The combinatorial error bridge (public re-derivation)

`General.lean` proves the analogous bridge as a `private` lemma `seqComposeError_eq_append`; we
re-derive it here (publicly) so the n-ary induction below can use it, following the public copy in
`ArkLib/ProofSystem/Sumcheck/Spec/SeqComposeRbrSoundness.lean` (which a file under
`OracleReduction/` must not import). -/

section ErrorBridge

variable {m : ℕ} {n : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}

/-- `seqComposeChallengeIdxToSigma` along the `inl` embedding of a head challenge index lands in
the first component with the original index. -/
private theorem idxToSigma_inl (s : (pSpec 0).ChallengeIdx) :
    seqComposeChallengeIdxToSigma (pSpec := pSpec)
      (ChallengeIdx.inl (pSpec₁ := pSpec 0)
        (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec i.succ)) s)
      = ⟨0, s⟩ := by
  have hsplit : (Fin.splitSum (n := n)
      (ChallengeIdx.inl (pSpec₁ := pSpec 0)
        (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec i.succ)) s).1) = ⟨0, s.1⟩ := by
    rw [Fin.splitSum_succ]; erw [Fin.dappend_left]
  have hfst : (seqComposeChallengeIdxToSigma (pSpec := pSpec)
      (ChallengeIdx.inl (pSpec₁ := pSpec 0)
        (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec i.succ)) s)).fst = (0 : Fin (m + 1)) :=
    congrArg Sigma.fst hsplit
  refine Sigma.ext hfst ?_
  rw [Subtype.heq_iff_coe_heq (by rw [hfst]) (by rw [hfst])]
  have hval : ((seqComposeChallengeIdxToSigma (pSpec := pSpec)
      (ChallengeIdx.inl (pSpec₁ := pSpec 0)
        (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec i.succ)) s)).snd.1)
      = (Fin.splitSum (n := n)
          (ChallengeIdx.inl (pSpec₁ := pSpec 0)
            (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec i.succ)) s).1).snd := rfl
  rw [hval]
  exact (Sigma.ext_iff.mp hsplit).2

/-- `seqComposeChallengeIdxToSigma` along the `inr` embedding of a tail challenge index: the first
component is shifted by `Fin.succ` and the tail index recovered by the tail's
`seqComposeChallengeIdxToSigma`. -/
private theorem idxToSigma_inr
    (s : (ProtocolSpec.seqCompose (fun i => pSpec i.succ)).ChallengeIdx) :
    seqComposeChallengeIdxToSigma (pSpec := pSpec)
      (ChallengeIdx.inr (pSpec₁ := pSpec 0)
        (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec i.succ)) s)
      = ⟨(seqComposeChallengeIdxToSigma (pSpec := fun i => pSpec i.succ) s).fst.succ,
          (seqComposeChallengeIdxToSigma (pSpec := fun i => pSpec i.succ) s).snd⟩ := by
  have hsplit : (Fin.splitSum (n := n)
      (ChallengeIdx.inr (pSpec₁ := pSpec 0)
        (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec i.succ)) s).1)
      = ⟨(Fin.splitSum (n := fun i => n i.succ) s.1).fst.succ,
          (Fin.splitSum (n := fun i => n i.succ) s.1).snd⟩ := by
    rw [Fin.splitSum_succ]; erw [Fin.dappend_right]
  have hfst : (seqComposeChallengeIdxToSigma (pSpec := pSpec)
      (ChallengeIdx.inr (pSpec₁ := pSpec 0)
        (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec i.succ)) s)).fst =
        (seqComposeChallengeIdxToSigma (pSpec := fun i => pSpec i.succ) s).fst.succ :=
    congrArg Sigma.fst hsplit
  refine Sigma.ext hfst ?_
  rw [Subtype.heq_iff_coe_heq (by rw [hfst]) (by rw [hfst])]
  have hval : ((seqComposeChallengeIdxToSigma (pSpec := pSpec)
      (ChallengeIdx.inr (pSpec₁ := pSpec 0)
        (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec i.succ)) s)).snd.1)
      = (Fin.splitSum (n := n)
          (ChallengeIdx.inr (pSpec₁ := pSpec 0)
            (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec i.succ)) s).1).snd := rfl
  rw [hval]
  exact (Sigma.ext_iff.mp hsplit).2

/-- **The composed RBR error, indexed via `seqComposeChallengeIdxToSigma` over the global
challenge index, equals the appended-form error built from the head error and the tail's
`seqCompose` error transported by `ChallengeIdx.sumEquiv.symm`.** This is the combinatorial bridge
identifying the two indexings of the composed protocol's challenges (a public re-derivation of
`General.lean`'s private `seqComposeError_eq_append`). -/
theorem seqComposeError_eq_append (f : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0)
    (a : (pSpec 0 ++ₚ ProtocolSpec.seqCompose (fun i => pSpec i.succ)).ChallengeIdx) :
    f (seqComposeChallengeIdxToSigma (pSpec := pSpec) a).fst
        (seqComposeChallengeIdxToSigma (pSpec := pSpec) a).snd =
      (Sum.elim (f 0)
          (fun k => f (seqComposeChallengeIdxToSigma (pSpec := fun i => pSpec i.succ) k).fst.succ
            (seqComposeChallengeIdxToSigma (pSpec := fun i => pSpec i.succ) k).snd) ∘
        ⇑ChallengeIdx.sumEquiv.symm) a := by
  set g : ((i : Fin (m + 1)) × (pSpec i).ChallengeIdx) → ℝ≥0 := fun x => f x.fst x.snd with hg
  rw [Function.comp_apply]
  rw [show a = ChallengeIdx.sumEquiv (ChallengeIdx.sumEquiv.symm a) from
    (Equiv.apply_symm_apply _ _).symm]
  rw [Equiv.symm_apply_apply]
  rcases ChallengeIdx.sumEquiv.symm a with s | s
  · simp only [Sum.elim_inl, ChallengeIdx.sumEquiv, Equiv.coe_fn_mk]
    exact congrArg g (idxToSigma_inl s)
  · simp only [Sum.elim_inr, ChallengeIdx.sumEquiv, Equiv.coe_fn_mk]
    exact congrArg g (idxToSigma_inr s)

end ErrorBridge

end ArkLib.SeqComposeRbrKnowledge

/-! ## n-ary verifier fusion

The `toVerifier` of an `OracleVerifier.seqCompose` is the `Verifier.seqCompose` of the
`toVerifier`s, by induction from the proven binary verifier-fusion keystone
`OracleReduction.oracleVerifier_append_toVerifier`. (Mirrors
`OracleVerifier.seqCompose_toVerifier_of_binary_for_rbr` from the sumcheck assembly, which lives
under `ProofSystem/` and so cannot be imported here.) -/

namespace OracleVerifier

variable {ι : Type} {oSpec : OracleSpec ι}

set_option linter.unusedVariables false in
/-- Local copy of the binary verifier-fusion law (the `OracleVerifier.append`/`toVerifier`
commutation), ∀-quantified over seams so that a single witness feeds every level of the
`seqCompose` induction. -/
def BinaryVerifierFusionForRbrKnowledge (oSpec : OracleSpec ι) : Prop :=
  ∀ {Stmt₁ : Type} {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [Oₛ₁ : ∀ i, OracleInterface.{0, 0} (OStmt₁ i)]
    {Stmt₂ : Type} {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type} [Oₛ₂ : ∀ i, OracleInterface.{0, 0} (OStmt₂ i)]
    {Stmt₃ : Type} {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type} [Oₛ₃ : ∀ i, OracleInterface.{0, 0} (OStmt₃ i)]
    {p q : ℕ} {pSpec₁ : ProtocolSpec p} {pSpec₂ : ProtocolSpec q}
    [Oₘ₁ : ∀ i, OracleInterface.{0, 0} (pSpec₁.Message i)]
    [Oₘ₂ : ∀ i, OracleInterface.{0, 0} (pSpec₂.Message i)]
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    [c₁ : OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂),
    (OracleVerifier.append (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁ V₂).toVerifier
      = Verifier.append V₁.toVerifier V₂.toVerifier

/-- The binary verifier-fusion law follows from the proven append verifier-fusion keystone. -/
theorem binaryVerifierFusionForRbrKnowledge_holds (oSpec : OracleSpec ι) :
    BinaryVerifierFusionForRbrKnowledge oSpec := by
  intro Stmt₁ ιₛ₁ OStmt₁ Oₛ₁ Stmt₂ ιₛ₂ OStmt₂ Oₛ₂ Stmt₃ ιₛ₃ OStmt₃ Oₛ₃
    p q pSpec₁ pSpec₂ Oₘ₁ Oₘ₂ V₁ c₁ V₂
  exact OracleReduction.oracleVerifier_append_toVerifier
    (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁ V₂

/-- The n-ary verifier fusion used by the rbr knowledge-soundness `seqCompose` assembly, derived
from the binary fusion law by induction on the number of components. -/
theorem seqCompose_toVerifier_of_binary_for_rbrKnowledge
    (hBinaryFusion : BinaryVerifierFusionForRbrKnowledge oSpec)
    {m : ℕ}
    (Stmt : Fin (m + 1) → Type)
    {ιₛ : Fin (m + 1) → Type} (OStmt : (i : Fin (m + 1)) → ιₛ i → Type)
    (Oₛ : ∀ i, ∀ j, OracleInterface.{0, 0} (OStmt i j))
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (Oₘ : ∀ i, ∀ j, OracleInterface.{0, 0} ((pSpec i).Message j))
    (V : (i : Fin m) →
      OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ) (OStmt i.succ)
        (pSpec i))
    (coh : ∀ i, OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ i.castSucc) (Oₛ₂ := Oₛ i.succ)
      (Oₘ₁ := Oₘ i) (V i)) :
    (OracleVerifier.seqCompose (Oₛ := Oₛ) (Oₘ := Oₘ) Stmt OStmt V (coh := coh)).toVerifier =
      Verifier.seqCompose (fun i => Stmt i × (∀ j, OStmt i j)) (fun i => (V i).toVerifier) := by
  induction m with
  | zero =>
    show (OracleVerifier.seqCompose Stmt OStmt V).toVerifier = Verifier.id
    rw [OracleVerifier.seqCompose_zero Stmt OStmt V]
    exact OracleVerifier.id_toVerifier
  | succ m ih =>
    letI tailCoh :
        ∀ i, OracleVerifier.Append.AppendCoherent (Oₛ₁ := (fun i => Oₛ (Fin.succ i)) i.castSucc)
          (Oₛ₂ := (fun i => Oₛ (Fin.succ i)) i.succ) (Oₘ₁ := (fun i => Oₘ (Fin.succ i)) i)
          (V (Fin.succ i)) := fun i => coh i.succ
    letI headCoh :
        OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ 0) (Oₛ₂ := Oₛ 1) (Oₘ₁ := Oₘ 0) (V 0) :=
      coh 0
    have ihTail := ih (Stmt ∘ Fin.succ) (fun i => OStmt (Fin.succ i)) (fun i => Oₛ (Fin.succ i))
      (fun i => Oₘ (Fin.succ i)) (fun i => V (Fin.succ i)) tailCoh
    have hHead := hBinaryFusion (Oₛ₁ := Oₛ 0) (Oₛ₂ := Oₛ 1) (Oₛ₃ := Oₛ (Fin.last (m + 1)))
      (Oₘ₁ := Oₘ 0)
      (V 0) (c₁ := headCoh)
      (OracleVerifier.seqCompose (Stmt ∘ Fin.succ) (fun i => OStmt (Fin.succ i))
        (Oₛ := fun i => Oₛ (Fin.succ i)) (Oₘ := fun i => Oₘ (Fin.succ i))
        (fun i => V (Fin.succ i)) (coh := tailCoh))
    rw [OracleVerifier.seqCompose_succ Stmt OStmt (Oₛ := Oₛ) (Oₘ := Oₘ) V (coh := coh),
        Verifier.seqCompose_succ (fun i => Stmt i × (∀ j, OStmt i j)) (fun i => (V i).toVerifier)]
    exact hHead.trans (congrArg (Verifier.append (V 0).toVerifier) ihTail)

end OracleVerifier

/-! ## The n-ary `Verifier.seqCompose` rbr knowledge-soundness theorem (failing-det components) -/

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι}
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

set_option maxHeartbeats 1000000 in
-- The induction creates large dependent Fin goals in the successor case.
/-- **n-ary `Verifier.seqCompose` rbr knowledge soundness for failing-deterministic components
(`Subsingleton σ`).** Every component verifier is failing-deterministic
(`V i = ⟨fun s tr => OptionT.mk (pure (verify? i s tr))⟩`), `P_to_V`-leading and nonempty
(`hValid`), and rbr knowledge-sound (`h`); then the sequential composition is rbr knowledge-sound
with the `seqComposeChallengeIdxToSigma`-indexed composed error — exactly the shape consumed by the
pass-through `Verifier.seqCompose_rbrKnowledgeSoundness` (`General.lean`).

Induction on the number of components: the base case is `Verifier.id_rbrKnowledgeSoundness` (the
composed error vanishes on the empty challenge-index type); the successor case unfolds via
`seqCompose_succ` and splits by `Nat.eq_zero_or_pos` on the tail length into the **message seam**
(proven keystone `append_rbrKnowledgeSoundness_failingDet_subsingleton`, seam direction from
`ProtocolSpec.seqCompose_appendValid` + `Prover.append_dir_natAdd`) and the **empty seam**
(residual-free keystone `append_rbrKnowledgeSoundness_failingDet_empty`); the `Sum.elim`-routed
binary error is reconciled with the composed error by `seqComposeError_eq_append`. -/
theorem seqCompose_rbrKnowledgeSoundness_failingDet
    [Subsingleton σ] {m : ℕ}
    (Stmt : Fin (m + 1) → Type) (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i, ∀ j, SampleableType ((pSpec i).Challenge j)]
    [∀ i, Inhabited (Stmt i)]
    (V : (i : Fin m) → Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (verify? : ∀ i : Fin m,
      Stmt i.castSucc → (pSpec i).FullTranscript → Option (Stmt i.succ))
    (hVerify : ∀ i, V i = ⟨fun s tr => OptionT.mk (pure (verify? i s tr))⟩)
    (rel : (i : Fin (m + 1)) → Set (Stmt i × Wit i))
    (rbrKnowledgeError : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0)
    (hValid : ∀ i, ∃ h : 0 < n i, (pSpec i).dir ⟨0, h⟩ = .P_to_V)
    (hNEW : ∀ i, Nonempty (Wit i))
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (h : ∀ i, (V i).rbrKnowledgeSoundness init impl (rel i.castSucc) (rel i.succ)
      (rbrKnowledgeError i)) :
    (Verifier.seqCompose Stmt V).rbrKnowledgeSoundness init impl (rel 0) (rel (Fin.last m))
      (fun combinedIdx =>
        letI ij := seqComposeChallengeIdxToSigma combinedIdx
        rbrKnowledgeError ij.1 ij.2) := by
  induction m with
  | zero =>
    rw [Verifier.seqCompose_zero]
    have hzero :
        (fun combinedIdx : (ProtocolSpec.seqCompose pSpec).ChallengeIdx =>
          letI ij := seqComposeChallengeIdxToSigma combinedIdx
          rbrKnowledgeError ij.1 ij.2) = 0 := by
      funext combinedIdx
      exact (seqComposeChallengeIdxToSigma combinedIdx).1.elim0
    rw [hzero]
    have hrel : rel (Fin.last 0) = rel 0 := by congr 1
    rw [hrel]
    exact Verifier.id_rbrKnowledgeSoundness init impl
  | succ m ih =>
    -- unfold the seqCompose into a binary append of the head with the tail's seqCompose,
    -- and expose the head's failing-deterministic shape
    rw [Verifier.seqCompose_succ]
    have h0 := h 0
    rw [hVerify 0] at h0
    rw [hVerify 0]
    -- the tail's composed rbr knowledge soundness (the inductive hypothesis)
    haveI : ∀ i : Fin (m + 1), Inhabited ((Stmt ∘ Fin.succ) i) :=
      fun i => inferInstanceAs (Inhabited (Stmt i.succ))
    have hTail := ih (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => V (Fin.succ i))
      (fun i => verify? (Fin.succ i)) (fun i => hVerify (Fin.succ i))
      (fun i => rel (Fin.succ i)) (fun i => rbrKnowledgeError (Fin.succ i))
      (fun i => hValid (Fin.succ i)) (fun i => hNEW (Fin.succ i)) (fun i => h (Fin.succ i))
    -- reconcile the Sum.elim-routed error with the seqComposeChallengeIdxToSigma-indexed error
    have herr :
        (fun combinedIdx : (ProtocolSpec.seqCompose pSpec).ChallengeIdx =>
          letI ij := seqComposeChallengeIdxToSigma (pSpec := pSpec) combinedIdx
          rbrKnowledgeError ij.1 ij.2)
        = (Sum.elim (rbrKnowledgeError 0)
            (fun combinedIdx =>
              letI ij := seqComposeChallengeIdxToSigma (pSpec := fun i => pSpec i.succ)
                combinedIdx
              rbrKnowledgeError (Fin.succ ij.1) ij.2) ∘ ⇑ChallengeIdx.sumEquiv.symm) :=
      funext (fun a => ArkLib.SeqComposeRbrKnowledge.seqComposeError_eq_append
        (pSpec := pSpec) rbrKnowledgeError a)
    rw [herr]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · -- empty trailing seam (`m = 0`): the tail `seqCompose` is 0-round; the residual-free
      -- failing-det empty keystone applies with no direction/state-regime hypotheses
      subst hm
      exact Verifier.append_rbrKnowledgeSoundness_failingDet_empty (verify? 0)
        (Verifier.seqCompose (Stmt ∘ Fin.succ) (fun i => V (Fin.succ i)))
        hInit (hNEW (Fin.succ 0)) h0 hTail
    · -- message seam: the tail is nonempty and starts with a `P_to_V` message
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
      have hn : 0 < Fin.vsum (fun i => n (Fin.succ i)) := by
        rw [Fin.vsum_succ]
        have := (hValid (Fin.succ 0)).1
        omega
      obtain ⟨hpos, hdir⟩ :=
        (ProtocolSpec.seqCompose_appendValid (pSpec := fun i => pSpec (Fin.succ i))
          (fun i => hValid (Fin.succ i))).resolve_left (by omega)
      have hDir : ((pSpec 0) ++ₚ (ProtocolSpec.seqCompose (fun i => pSpec (Fin.succ i)))).dir
          (⟨n 0, by omega⟩ : Fin (n 0 + Fin.vsum (fun i => n (Fin.succ i)))) = .P_to_V := by
        rw [show (⟨n 0, by omega⟩ : Fin (n 0 + Fin.vsum (fun i => n (Fin.succ i))))
              = Fin.natAdd (n 0) ⟨0, hpos⟩ from by ext; simp]
        rw [Prover.append_dir_natAdd]
        exact hdir
      exact Verifier.append_rbrKnowledgeSoundness_failingDet_subsingleton (verify? 0)
        (Verifier.seqCompose (Stmt ∘ Fin.succ) (fun i => V (Fin.succ i)))
        hInit hInitNF (hNEW (Fin.succ 0)) hpos hDir hdir h0 hTail

end Verifier

/-! ## The n-ary `OracleVerifier.seqCompose` rbr knowledge-soundness theorem -/

namespace OracleVerifier

variable {ι : Type} {oSpec : OracleSpec ι}
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

set_option maxHeartbeats 1000000 in
/-- **n-ary `OracleVerifier.seqCompose` rbr knowledge soundness for failing-deterministic
components (`Subsingleton σ`).** Discharges the pass-through hypothesis
`hSeqComposeRbrKnowledgeSoundness` of `OracleVerifier.seqCompose_rbrKnowledgeSoundness`
(`General.lean`) for chains whose component verifiers compile to *failing*-deterministic
`toVerifier`s (`hFD`, the shape produced by `OracleVerifier.toVerifier_eq_failingDet_of_collapse`
and the failing-det composition combinators).

Proof: `OracleVerifier.rbrKnowledgeSoundness` is definitionally `toVerifier`-level; the n-ary
verifier fusion `seqCompose_toVerifier_of_binary_for_rbrKnowledge` rewrites the composed
`toVerifier` into the `Verifier.seqCompose` of the component `toVerifier`s, and the `Verifier`-level
n-ary theorem applies with the failing-determinism witnesses extracted from `hFD` by choice. -/
theorem seqCompose_rbrKnowledgeSoundness_failingDet
    [Subsingleton σ] {m : ℕ}
    (Stmt : Fin (m + 1) → Type)
    {ιₛ : Fin (m + 1) → Type} (OStmt : (i : Fin (m + 1)) → ιₛ i → Type)
    [Oₛ : ∀ i, ∀ j, OracleInterface.{0, 0} (OStmt i j)]
    (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface.{0, 0} ((pSpec i).Message j)]
    [∀ i, ∀ j, SampleableType ((pSpec i).Challenge j)]
    [∀ i, Inhabited (Stmt i × ∀ j, OStmt i j)]
    (V : (i : Fin m) →
      OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ) (OStmt i.succ)
        (pSpec i))
    [coh : ∀ i, OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ i.castSucc) (Oₛ₂ := Oₛ i.succ)
      (Oₘ₁ := Oₘ i) (V i)]
    (rel : ∀ i, Set ((Stmt i × ∀ j, OStmt i j) × Wit i))
    (rbrKnowledgeError : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0)
    (hFD : ∀ i, ∃ v? : (Stmt i.castSucc × ∀ j, OStmt i.castSucc j) → (pSpec i).FullTranscript →
        Option (Stmt i.succ × ∀ j, OStmt i.succ j),
      (V i).toVerifier = ⟨fun p tr => OptionT.mk (pure (v? p tr))⟩)
    (hValid : ∀ i, ∃ h : 0 < n i, (pSpec i).dir ⟨0, h⟩ = .P_to_V)
    (hNEW : ∀ i, Nonempty (Wit i))
    (hInit : ∃ s, s ∈ support init) (hInitNF : Pr[⊥ | init] = 0)
    (h : ∀ i, (V i).rbrKnowledgeSoundness init impl (rel i.castSucc) (rel i.succ)
      (rbrKnowledgeError i)) :
    (OracleVerifier.seqCompose Stmt OStmt V).rbrKnowledgeSoundness
      init impl (rel 0) (rel (Fin.last m))
      (fun combinedIdx =>
        letI ij := seqComposeChallengeIdxToSigma combinedIdx
        rbrKnowledgeError ij.1 ij.2) := by
  show (OracleVerifier.seqCompose Stmt OStmt V).toVerifier.rbrKnowledgeSoundness
    init impl (rel 0) (rel (Fin.last m)) _
  rw [seqCompose_toVerifier_of_binary_for_rbrKnowledge
    (binaryVerifierFusionForRbrKnowledge_holds oSpec) Stmt OStmt Oₛ Oₘ V coh]
  exact Verifier.seqCompose_rbrKnowledgeSoundness_failingDet
    (fun i => Stmt i × (∀ j, OStmt i j)) Wit (fun i => (V i).toVerifier)
    (fun i => Classical.choose (hFD i)) (fun i => Classical.choose_spec (hFD i))
    rel rbrKnowledgeError hValid hNEW hInit hInitNF h

end OracleVerifier

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ArkLib.SeqComposeRbrKnowledge.seqComposeError_eq_append
#print axioms OracleVerifier.binaryVerifierFusionForRbrKnowledge_holds
#print axioms OracleVerifier.seqCompose_toVerifier_of_binary_for_rbrKnowledge
#print axioms Verifier.seqCompose_rbrKnowledgeSoundness_failingDet
#print axioms OracleVerifier.seqCompose_rbrKnowledgeSoundness_failingDet
