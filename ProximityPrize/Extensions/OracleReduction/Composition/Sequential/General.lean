/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.OracleReduction.Composition.Sequential.General

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ProximityPrize.Extensions.OracleReduction.Composition.Sequential.Append

/-!
  # Sequential Composition of Many Oracle Reductions

  This file defines the sequential composition of an arbitrary `m + 1` number of oracle reductions.
  This is defined by iterating the composition of two reductions, as defined in `Append.lean`.

  The security properties of the general sequential composition of reductions are then inherited
  from the case of composing two reductions.
-/

open ProtocolSpec OracleComp

universe u v

variable {ι : Type} {oSpec : OracleSpec ι}

section Composition

namespace Prover

end Prover

namespace Verifier

end Verifier

namespace Reduction

end Reduction

namespace OracleProver

end OracleProver

namespace OracleVerifier

/-- If every component preserves the input oracle values extensionally, sequential composition
preserves them too. This applies to both embedded and virtual output representations. -/
theorem seqCompose_materializeOutput_eq_input {m : ℕ}
    (Stmt : Fin (m + 1) → Type) {ιₛ : Type} (OStmt : ιₛ → Type)
    [Oₛ : ∀ j, OracleInterface (OStmt j)]
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)]
    (V : (i : Fin m) → OracleVerifier oSpec (Stmt i.castSucc) OStmt
      (Stmt i.succ) OStmt (pSpec i))
    (hV : ∀ i chals inputs messages, (V i).materializeOutput chals inputs messages = inputs)
    (chals : (ProtocolSpec.seqCompose pSpec).Challenges)
    (inputs : ∀ i, OStmt i) (messages : (ProtocolSpec.seqCompose pSpec).Messages) :
    (OracleVerifier.seqCompose Stmt (fun _ => OStmt) V).materializeOutput
      chals inputs messages = inputs := by
  induction m with
  | zero => rfl
  | succ m ih =>
    let tail := ProtocolSpec.seqCompose (fun i : Fin m => pSpec i.succ)
    let c₁ := Challenges.fst (pSpec₁ := pSpec 0) (pSpec₂ := tail) chals
    let c₂ := Challenges.snd (pSpec₁ := pSpec 0) (pSpec₂ := tail) chals
    let m₁ := Messages.fst (pSpec₁ := pSpec 0) (pSpec₂ := tail) messages
    let m₂ := Messages.snd (pSpec₁ := pSpec 0) (pSpec₂ := tail) messages
    change (OracleVerifier.seqCompose (Stmt ∘ Fin.succ) (fun _ => OStmt)
      (fun i => V (Fin.succ i))).materializeOutput c₂
        ((V 0).materializeOutput c₁ inputs m₁) m₂ = inputs
    rw [hV 0]
    exact ih (Stmt ∘ Fin.succ) (fun i => V (Fin.succ i))
      (fun i => hV (Fin.succ i)) c₂ m₂

end OracleVerifier

namespace OracleReduction

end OracleReduction

end Composition

variable {m : ℕ}
    {Stmt : Fin (m + 1) → Type}
    {ιₛ : Fin (m + 1) → Type} {OStmt : (i : Fin (m + 1)) → ιₛ i → Type}
    [Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j)]
    {Wit : Fin (m + 1) → Type}
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)]
    [∀ i, ∀ j, SampleableType ((pSpec i).Challenge j)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

-- section Execution

-- end Execution

section Security

open scoped NNReal

namespace Reduction

omit Oₘ in
theorem seqCompose_completeness
    (rel : (i : Fin (m + 1)) → Set (Stmt i × Wit i))
    (R : ∀ i, Reduction oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ)
      (pSpec i))
    (completenessError : Fin m → ℝ≥0)
    (h : ∀ i, (R i).completeness init impl (rel i.castSucc) (rel i.succ) (completenessError i))
    (hSeqComposeCompleteness :
      (Reduction.seqCompose Stmt Wit R).completeness init impl (rel 0) (rel (Fin.last m))
        (∑ i, completenessError i)) :
      (Reduction.seqCompose Stmt Wit R).completeness init impl (rel 0) (rel (Fin.last m))
        (∑ i, completenessError i) :=
  hSeqComposeCompleteness

omit Oₘ in
theorem seqCompose_perfectCompleteness
    (rel : (i : Fin (m + 1)) → Set (Stmt i × Wit i))
    (R : ∀ i, Reduction oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ)
      (pSpec i))
    (h : ∀ i, (R i).perfectCompleteness init impl (rel i.castSucc) (rel i.succ))
    (hSeqComposePerfectCompleteness :
      (Reduction.seqCompose Stmt Wit R).perfectCompleteness
        init impl (rel 0) (rel (Fin.last m))) :
      (Reduction.seqCompose Stmt Wit R).perfectCompleteness
        init impl (rel 0) (rel (Fin.last m)) :=
  hSeqComposePerfectCompleteness

set_option maxHeartbeats 1000000 in
-- The induction proof creates large dependent Fin goals in the successor case.
/-- **Brick (issue #25): n-ary `seqCompose` perfect completeness reduces to the binary `append`
keystone.** By induction on `m`: base case `Reduction.id_perfectCompleteness`; step unfolds via
`seqCompose_succ` and discharges the binary `append` with `hAppend` + the IH. Feeding the eventual
unconditional binary `reduction_append_perfectCompleteness` as `hAppend` closes the n-ary statement.
Modeled on the proven `seqCompose'_appendCoherent` induction. -/
theorem seqCompose_perfectCompleteness_of_append {m : ℕ}
    (Stmt : Fin (m + 1) → Type) (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i, ∀ j, SampleableType ((pSpec i).Challenge j)]
    (R : (i : Fin m) →
      Reduction oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ) (pSpec i))
    (rel : (i : Fin (m + 1)) → Set (Stmt i × Wit i))
    (hAppend : ∀ {S₁ W₁ S₂ W₂ S₃ W₃ : Type} {k₁ k₂ : ℕ}
        {p₁ : ProtocolSpec k₁} {p₂ : ProtocolSpec k₂}
        [∀ j, SampleableType (p₁.Challenge j)] [∀ j, SampleableType (p₂.Challenge j)]
        (R₁ : Reduction oSpec S₁ W₁ S₂ W₂ p₁) (R₂ : Reduction oSpec S₂ W₂ S₃ W₃ p₂)
        {r₁ : Set (S₁ × W₁)} {r₂ : Set (S₂ × W₂)} {r₃ : Set (S₃ × W₃)},
        R₁.perfectCompleteness init impl r₁ r₂ → R₂.perfectCompleteness init impl r₂ r₃ →
        (R₁.append R₂).perfectCompleteness init impl r₁ r₃)
    (h : ∀ i, (R i).perfectCompleteness init impl (rel i.castSucc) (rel i.succ)) :
    (seqCompose Stmt Wit R).perfectCompleteness init impl (rel 0) (rel (Fin.last m)) := by
  induction m with
  | zero =>
    rw [seqCompose_zero]
    exact Reduction.id_perfectCompleteness (init := init) (impl := impl) (rel := rel 0)
  | succ m ih =>
    change ((R 0).append
        (seqCompose (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => R (Fin.succ i))))
      |>.perfectCompleteness init impl (rel 0) (rel (Fin.succ (Fin.last m)))
    exact hAppend (R 0) _ (h 0)
      (ih (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => R (Fin.succ i))
        (fun i => rel (Fin.succ i)) (fun i => h (Fin.succ i)))

set_option maxHeartbeats 1000000 in
-- The induction proof creates large dependent Fin goals in the successor case.
/-- **Brick (issue #25): n-ary `seqCompose` completeness reduces to the binary `append` keystone.**
Error-bearing analogue of `seqCompose_perfectCompleteness_of_append`: base case
`Reduction.id_perfectCompleteness` (= completeness with error `0`) and `∑ (i : Fin 0) = 0`;
step splits the error with `Fin.sum_univ_succ` into `completenessError 0 + ∑ tail` and applies
`hAppend`. -/
theorem seqCompose_completeness_of_append {m : ℕ}
    (Stmt : Fin (m + 1) → Type) (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i, ∀ j, SampleableType ((pSpec i).Challenge j)]
    (R : (i : Fin m) →
      Reduction oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ) (pSpec i))
    (rel : (i : Fin (m + 1)) → Set (Stmt i × Wit i))
    (completenessError : Fin m → ℝ≥0)
    (hAppend : ∀ {S₁ W₁ S₂ W₂ S₃ W₃ : Type} {k₁ k₂ : ℕ}
        {p₁ : ProtocolSpec k₁} {p₂ : ProtocolSpec k₂}
        [∀ j, SampleableType (p₁.Challenge j)] [∀ j, SampleableType (p₂.Challenge j)]
        (R₁ : Reduction oSpec S₁ W₁ S₂ W₂ p₁) (R₂ : Reduction oSpec S₂ W₂ S₃ W₃ p₂)
        {r₁ : Set (S₁ × W₁)} {r₂ : Set (S₂ × W₂)} {r₃ : Set (S₃ × W₃)} {e₁ e₂ : ℝ≥0},
        R₁.completeness init impl r₁ r₂ e₁ → R₂.completeness init impl r₂ r₃ e₂ →
        (R₁.append R₂).completeness init impl r₁ r₃ (e₁ + e₂))
    (h : ∀ i, (R i).completeness init impl (rel i.castSucc) (rel i.succ) (completenessError i)) :
    (seqCompose Stmt Wit R).completeness init impl (rel 0) (rel (Fin.last m))
      (∑ i, completenessError i) := by
  induction m with
  | zero =>
    rw [seqCompose_zero, Fin.sum_univ_zero]
    exact Reduction.id_perfectCompleteness (init := init) (impl := impl) (rel := rel 0)
  | succ m ih =>
    rw [Fin.sum_univ_succ]
    change ((R 0).append
        (seqCompose (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => R (Fin.succ i))))
      |>.completeness init impl (rel 0) (rel (Fin.succ (Fin.last m)))
        (completenessError 0 + ∑ i, completenessError (Fin.succ i))
    exact hAppend (R 0) _ (h 0)
      (ih (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => R (Fin.succ i))
        (fun i => rel (Fin.succ i)) (fun i => completenessError (Fin.succ i))
        (fun i => h (Fin.succ i)))

end Reduction

namespace Verifier

/-- Reduction of `seqComposeChallengeIdxToSigma` along the `inl` embedding of a challenge index of
    the head protocol `pSpec 0`: it lands in the first component (`Fin 0`) with the original
    index. -/
private theorem seqComposeIdx_inl {m : ℕ} {n : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (s : (pSpec 0).ChallengeIdx) :
    seqComposeChallengeIdxToSigma (pSpec := pSpec)
      (ChallengeIdx.inl (pSpec₁ := pSpec 0) (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec i.succ)) s)
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

/-- Reduction of `seqComposeChallengeIdxToSigma` along the `inr` embedding of a challenge index of
    the tail protocol: the first component is shifted by `Fin.succ` and the tail index is recovered
    by `seqComposeChallengeIdxToSigma` on the tail. -/
private theorem seqComposeIdx_inr {m : ℕ} {n : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (s : (ProtocolSpec.seqCompose (fun i => pSpec i.succ)).ChallengeIdx) :
    seqComposeChallengeIdxToSigma (pSpec := pSpec)
      (ChallengeIdx.inr (pSpec₁ := pSpec 0) (pSpec₂ := ProtocolSpec.seqCompose (fun i => pSpec i.succ)) s)
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

/-- The RBR error of a sequential composition, expressed via `seqComposeChallengeIdxToSigma` over
    the *global* challenge index, equals the appended-form error built from the head error and the
    tail's `seqCompose` error transported by `ChallengeIdx.sumEquiv.symm`. This is the combinatorial
    bridge identifying the two indexings of the composed protocol's challenges, used to discharge
    the challenge-index transport goals left by `convert append_rbr…`. -/
private theorem seqComposeError_eq_append {m : ℕ} {n : Fin (m + 1) → ℕ}
    {pSpec : ∀ i, ProtocolSpec (n i)} (f : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0)
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
    exact congrArg g (seqComposeIdx_inl s)
  · simp only [Sum.elim_inr, ChallengeIdx.sumEquiv, Equiv.coe_fn_mk]
    exact congrArg g (seqComposeIdx_inr s)

end Verifier

namespace OracleReduction

theorem seqCompose_completeness
    (rel : (i : Fin (m + 1)) → Set ((Stmt i × ∀ j, OStmt i j) × Wit i))
    (R : ∀ i, OracleReduction oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Wit i.castSucc)
      (Stmt i.succ) (OStmt i.succ) (Wit i.succ) (pSpec i))

    (completenessError : Fin m → ℝ≥0)
    (h : ∀ i, (R i).completeness init impl (rel i.castSucc) (rel i.succ) (completenessError i))
    (hSeqComposeCompleteness :
      (OracleReduction.seqCompose Stmt OStmt Wit R).completeness
        init impl (rel 0) (rel (Fin.last m)) (∑ i, completenessError i)) :
      (OracleReduction.seqCompose Stmt OStmt Wit R).completeness
        init impl (rel 0) (rel (Fin.last m)) (∑ i, completenessError i) :=
  hSeqComposeCompleteness

theorem seqCompose_perfectCompleteness
    (rel : (i : Fin (m + 1)) → Set ((Stmt i × ∀ j, OStmt i j) × Wit i))
    (R : ∀ i, OracleReduction oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Wit i.castSucc)
      (Stmt i.succ) (OStmt i.succ) (Wit i.succ) (pSpec i))

    (h : ∀ i, (R i).perfectCompleteness init impl (rel i.castSucc) (rel i.succ))
    (hSeqComposePerfectCompleteness :
      (OracleReduction.seqCompose Stmt OStmt Wit R).perfectCompleteness
        init impl (rel 0) (rel (Fin.last m))) :
      (OracleReduction.seqCompose Stmt OStmt Wit R).perfectCompleteness
        init impl (rel 0) (rel (Fin.last m)) :=
  hSeqComposePerfectCompleteness

end OracleReduction

namespace OracleVerifier

end OracleVerifier

/-! ## Source audit for current n-ary sequential-composition residual fronts -/

#print axioms Reduction.seqCompose_completeness
#print axioms Reduction.seqCompose_perfectCompleteness
#print axioms Verifier.seqCompose_soundness
#print axioms Verifier.seqCompose_knowledgeSoundness
#print axioms Verifier.seqComposeError_eq_append
#print axioms Verifier.seqCompose_rbrSoundness
#print axioms Verifier.seqCompose_rbrKnowledgeSoundness
#print axioms OracleReduction.seqCompose_completeness
#print axioms OracleReduction.seqCompose_perfectCompleteness
#print axioms OracleVerifier.seqCompose_soundness
#print axioms OracleVerifier.seqCompose_knowledgeSoundness
#print axioms OracleVerifier.seqCompose_rbrSoundness
#print axioms OracleVerifier.seqCompose_rbrKnowledgeSoundness

end Security

-- The new structural output theorem is independent of the inherited RBR proof debt above.
#print axioms OracleVerifier.seqCompose_materializeOutput_eq_input
