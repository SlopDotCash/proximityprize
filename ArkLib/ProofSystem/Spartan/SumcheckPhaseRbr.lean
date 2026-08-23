/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.LiftContext.OracleReduction
import ArkLib.ProofSystem.Sumcheck.Spec.General

/-!
# Round-by-round soundness transport for lifted sum-check phases (issue #114)

Spartan's two sum-check phases are `liftContext`s of the generic multi-round sum-check oracle
reduction. This module provides the *generic* machinery to transport the inner sum-check's
round-by-round soundness through such a lift **honestly** — i.e. with outer languages that are
genuinely implied by / imply the inner sum-check claim, rather than the (false) "cube-sum implies
R1CS satisfiability" implication that the `Extractor.Lens.IsKnowledgeSound` route would demand
(see the design note in `FirstSumcheckComplete.lean`).

Contents:

* `Verifier.rbrSoundness_mono_langOut` — round-by-round soundness is antitone in the output
  language: shrinking `langOut` preserves rbr soundness (the same state function works, since
  `toFun_full` only gets easier). This lets us state phase lemmas with *concrete* output languages
  once they are contained in the canonically-transported one.

* `Statement.Lens.pullbackIsSound` — for any statement lens and inner languages, the lens is
  `IsSound` from the pullback input language `lens.proj ⁻¹' innerLangIn` to the *transported*
  output language

    `{y | ∀ stmtIn innerOut, compat stmtIn innerOut → lens.lift stmtIn innerOut = y →
          innerOut ∈ innerLangOut}`

  (the largest output language for which `lift_sound` can hold). Both fields hold by construction;
  this is the canonical honest instantiation of the lens-soundness interface.

* `OracleVerifier.liftContext_rbrSoundness_pullback` — the combination: a lifted oracle verifier
  inherits rbr soundness from the inner one, from the pullback input language to any output
  language contained in the transported one, via the proven
  `OracleVerifier.liftContext_rbr_soundness` + the two pieces above.

* `OracleVerifier.seqCompose'_embed_inl` / `Sumcheck.Spec.oracleVerifier_embed` /
  `Sumcheck.Spec.mem_support_oracleVerifier_run_oStmt` — the **oracle pass-through facts** for the
  concrete sum-check verifier: the sequentially-composed sum-check oracle verifier routes its
  single output oracle from its single input oracle (`embed () = .inl ()`, by induction over the
  rounds using `append_embed_eq`), hence any reachable verifier output carries the *unchanged*
  input polynomial oracle. This is what pins the inner output oracle in the transported output
  language to the (projected) virtual polynomial, making the concrete Spartan phase output
  languages (`ℱ(r_x) = t'`-shaped) provably contained in the transported ones.

The Spartan-specific phase lemmas consuming this machinery live in `FirstSumcheckComplete.lean`
and `SecondSumcheckComplete.lean`. The generic pieces are candidates for upstreaming into
`OracleReduction/LiftContext/` and `OracleReduction/Composition/Sequential/` respectively; they
are kept here for now to limit rebuild churn of the framework cone.
-/

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

universe u

section RbrSoundnessMono

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn StmtOut : Type} {n : ℕ}
  {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **Round-by-round soundness is antitone in the output language.** If a verifier is rbr-sound
into `langOut`, it is rbr-sound into any `langOut' ⊆ langOut`, with the same error: the same state
function works, since shrinking the output language only weakens the `toFun_full` obligation
(`Pr[· ∈ langOut'] ≤ Pr[· ∈ langOut] = 0`). -/
theorem Verifier.rbrSoundness_mono_langOut
    {langIn : Set StmtIn} {langOut langOut' : Set StmtOut}
    {V : Verifier oSpec StmtIn StmtOut pSpec}
    {err : pSpec.ChallengeIdx → ℝ≥0}
    (hsub : langOut' ⊆ langOut)
    (h : V.rbrSoundness init impl langIn langOut err) :
    V.rbrSoundness init impl langIn langOut' err := by
  obtain ⟨stF, hbound⟩ := h
  refine ⟨⟨stF.toFun, stF.toFun_empty, stF.toFun_next, fun stmt tr hneg => ?_⟩, hbound⟩
  have h0 := stF.toFun_full stmt tr hneg
  exact le_antisymm
    (le_trans (probEvent_mono fun x _ hx => hsub hx) (le_of_eq h0)) (zero_le _)

end RbrSoundnessMono

section PullbackIsSound

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}

/-- The **transported output language** of a statement lens: the largest output language `L` for
which `lift_sound` (compatible inner outputs outside `innerLangOut` lift outside `L`) can hold.
Concrete phase output languages are proven sound by showing containment in this one. -/
def Statement.Lens.transportedLangOut
    (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (innerLangOut : Set InnerStmtOut)
    (compat : OuterStmtIn → InnerStmtOut → Prop) : Set OuterStmtOut :=
  {y | ∀ stmtIn innerOut, compat stmtIn innerOut → lens.lift stmtIn innerOut = y →
        innerOut ∈ innerLangOut}

/-- **Canonical (pullback) lens-soundness instance.** Any statement lens is `IsSound` from the
pullback input language `lens.proj ⁻¹' innerLangIn` to the transported output language
`lens.transportedLangOut innerLangOut compat`: both fields hold by construction. This is the honest
instantiation of `Statement.Lens.IsSound` for `liftContext`ed phases whose claims live on the
*inner* protocol (e.g. sum-check claims), avoiding any false outer-relation implication. -/
@[reducible] def Statement.Lens.pullbackIsSound
    (lens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (innerLangIn : Set InnerStmtIn) (innerLangOut : Set InnerStmtOut)
    (compat : OuterStmtIn → InnerStmtOut → Prop) :
    lens.IsSound (lens.proj ⁻¹' innerLangIn)
      (lens.transportedLangOut innerLangOut compat)
      innerLangIn innerLangOut compat where
  proj_sound := fun _ h => h
  lift_sound := fun stmtIn innerOut hc hno hmem =>
    hno (hmem stmtIn innerOut hc rfl)

end PullbackIsSound

section LiftContextPullback

variable {ι : Type} {oSpec : OracleSpec ι}
  {OuterStmtIn OuterStmtOut : Type}
  {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type} [∀ i, OracleInterface (OuterOStmtIn i)]
  {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type} [∀ i, OracleInterface (OuterOStmtOut i)]
  {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type} [∀ i, OracleInterface (InnerOStmtIn i)]
  {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type} [∀ i, OracleInterface (InnerOStmtOut i)]
  {InnerStmtIn InnerStmtOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, OracleInterface (pSpec.Message i)] [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  [Inhabited InnerStmtOut] [∀ i, Inhabited (InnerOStmtOut i)]

/-- **Pullback rbr-soundness transport through `OracleVerifier.liftContext`.** A lifted oracle
verifier inherits the inner verifier's round-by-round soundness — from the pullback of the inner
input language along the lens projection, to any outer output language contained in the
transported one — with the same per-round errors.

This is the honest soundness-transport interface for `liftContext`ed phases: the input/output
languages carry the *inner* (e.g. sum-check) claim, transported through the lens, rather than any
unrelated outer relation. -/
theorem OracleVerifier.liftContext_rbrSoundness_pullback
    {innerLangIn : Set (InnerStmtIn × ∀ i, InnerOStmtIn i)}
    {innerLangOut : Set (InnerStmtOut × ∀ i, InnerOStmtOut i)}
    {outerLangOut : Set (OuterStmtOut × ∀ i, OuterOStmtOut i)}
    {rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0}
    {lens : OracleStatement.OracleLens oSpec OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                                OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut pSpec}
    (V : OracleVerifier oSpec InnerStmtIn InnerOStmtIn InnerStmtOut InnerOStmtOut pSpec)
    [coh : OracleVerifier.LiftContextCoherent lens V]
    (hOut : outerLangOut ⊆
      lens.toLens.transportedLangOut innerLangOut (V.toVerifier.compatStatement lens.toLens))
    (h : V.rbrSoundness init impl innerLangIn innerLangOut rbrSoundnessError) :
    (V.liftContext lens).rbrSoundness init impl
      (lens.toLens.proj ⁻¹' innerLangIn) outerLangOut rbrSoundnessError := by
  have h1 := V.liftContext_rbr_soundness (lens := lens)
    (lensSound := lens.toLens.pullbackIsSound innerLangIn innerLangOut
      (V.toVerifier.compatStatement lens.toLens)) h
  unfold OracleVerifier.rbrSoundness at h1 ⊢
  exact Verifier.rbrSoundness_mono_langOut hOut h1

end LiftContextPullback

section SeqComposeEmbed

variable {ι : Type} {oSpec : OracleSpec ι}

/-- If every component oracle verifier routes its output oracles from its *input* oracles
(`embed` lands in `Sum.inl`), then so does their sequential composition `seqCompose'`.
Induction over the number of rounds via `append_embed_eq`. -/
theorem OracleVerifier.seqCompose'_embed_inl {m : ℕ}
    (Stmt : Fin (m + 1) → Type)
    {ιₛ : Fin (m + 1) → Type} (OStmt : (i : Fin (m + 1)) → ιₛ i → Type)
    (Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j))
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    (Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j))
    (V : (i : Fin m) →
      OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ) (OStmt i.succ)
        (pSpec i))
    (coh : ∀ i, OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ i.castSucc) (Oₛ₂ := Oₛ i.succ)
      (Oₘ₁ := Oₘ i) (V i))
    (hV : ∀ i (a : ιₛ i.succ), ∃ b : ιₛ i.castSucc, (V i).embed a = Sum.inl b)
    (a : ιₛ (Fin.last m)) :
    ∃ b : ιₛ 0, (OracleVerifier.seqCompose' Stmt OStmt Oₛ Oₘ V coh).embed a = Sum.inl b := by
  induction m with
  | zero => exact ⟨a, rfl⟩
  | succ m ih =>
    obtain ⟨b₁, hb₁⟩ := ih (Stmt ∘ Fin.succ) (fun i => OStmt (Fin.succ i))
      (fun i => Oₛ (Fin.succ i)) (fun i => Oₘ (Fin.succ i)) (fun i => V (Fin.succ i))
      (fun i => coh i.succ) (fun i a => hV i.succ a) a
    obtain ⟨b₂, hb₂⟩ := hV 0 b₁
    refine ⟨b₂, ?_⟩
    show (OracleVerifier.append (V 0)
      (OracleVerifier.seqCompose' (Stmt ∘ Fin.succ) (fun i => OStmt (Fin.succ i))
        (fun i => Oₛ (Fin.succ i)) (fun i => Oₘ (Fin.succ i)) (fun i => V (Fin.succ i))
        (fun i => coh i.succ))).embed a = Sum.inl b₂
    rw [OracleVerifier.Append.append_embed_eq, hb₁]
    show Sum.map id _ ((V 0).embed b₁) = Sum.inl b₂
    rw [hb₂]
    rfl

end SeqComposeEmbed

namespace Sumcheck.Spec

open Sumcheck.Spec

variable {R : Type} [CommSemiring R] [DecidableEq R] [SampleableType R]
  {deg : ℕ} {m : ℕ} {D : Fin m ↪ R} {n : ℕ}
  {ι : Type} {oSpec : OracleSpec ι}

omit [SampleableType R] in
/-- **The composed sum-check oracle verifier passes its polynomial oracle through:** its single
output oracle is routed from its single input oracle (`embed () = .inl ()`), for any number of
rounds. Each single round is a `liftContext` whose `embedOStmt` is `Function.Embedding.inl`; the
composition preserves this by `seqCompose'_embed_inl`. -/
theorem oracleVerifier_embed (a : Unit) :
    (oracleVerifier R deg D n oSpec).embed a = Sum.inl () := by
  obtain ⟨b, hb⟩ := OracleVerifier.seqCompose'_embed_inl
    (StatementRound R n) (fun _ => OracleStatement R n deg)
    (fun _ _ => inferInstance) (fun _ _ => inferInstance)
    (SingleRound.oracleVerifier R n deg D oSpec)
    (fun i => inferInstance)
    (fun _ a => ⟨a, rfl⟩) a
  exact hb

/-- **Reachable outputs of the (plain-verifier view of the) sum-check oracle verifier carry the
unchanged input polynomial oracle.** Any statement in the support of
`(oracleVerifier …).toVerifier.run (stmt, oStmt) tr` has second (oracle) component equal to
`oStmt`. This pins the inner output oracle in lens-transported output languages to the projected
virtual polynomial. -/
theorem mem_support_oracleVerifier_run_oStmt
    {stmt : StatementRound R n 0} {oStmt : ∀ i, OracleStatement R n deg i}
    {tr : FullTranscript (pSpec R deg n)}
    {out : StatementRound R n (Fin.last n) × ∀ i, OracleStatement R n deg i}
    (h : out ∈ support ((oracleVerifier R deg D n oSpec).toVerifier.run (stmt, oStmt) tr)) :
    out.2 = oStmt := by
  classical
  -- Unfold the `toVerifier` run to a bind whose second component is the pure `embed`-routing.
  rw [Verifier.run, OracleVerifier.toVerifier] at h
  simp only [OptionT.mem_support_iff, OptionT.run_bind, Option.elimM] at h
  rw [mem_support_bind_iff] at h
  obtain ⟨a, _, ha⟩ := h
  cases a with
  | none => simp at ha
  | some stmtOut =>
    simp only [Option.elim_some, OptionT.run_pure, support_pure, Set.mem_singleton_iff,
      Option.some_inj] at ha
    -- `out = (stmtOut, routing)`; collapse the routing to `oStmt` via the `embed` lemma.
    subst ha
    funext i
    change OracleVerifier.mkVerifierOStmtOut
        (oracleVerifier R deg D n oSpec).embed
        (oracleVerifier R deg D n oSpec).hEq oStmt tr i = oStmt i
    have he : (oracleVerifier R deg D n oSpec).embed i = Sum.inl () :=
      oracleVerifier_embed (R := R) (deg := deg) (D := D) (n := n) (oSpec := oSpec) i
    unfold OracleVerifier.mkVerifierOStmtOut
    split
    next j h' =>
      cases i
      have hj : j = () := by
        have hsum : (Sum.inl () : Unit ⊕ (pSpec R deg n).MessageIdx) = Sum.inl j := by
          simpa only [he] using h'
        exact (Sum.inl.inj hsum).symm
      cases hj
      simp only [eqRec_eq_cast, cast_cast, cast_eq]
    next j h' =>
      rw [he] at h'
      exact absurd h' (by simp)

end Sumcheck.Spec
