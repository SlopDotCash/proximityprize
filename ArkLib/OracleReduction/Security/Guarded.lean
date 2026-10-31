/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann, Pablo Martín Vinuelas, Alexander Hicks
-/

import ArkLib.OracleReduction.Composition.Sequential.Append
import ArkLib.ToVCVio.Simulation

/-!
# Guarded verifiers

A **guarded** verifier either returns a deterministic verdict or aborts:
`if check stmt tr then pure (out stmt tr) else failure`, where `failure` is native to the
verifier monad `OptionT (OracleComp _)`. It is the faithful model of a verifier that rejects at
runtime, and purity is its special case with the trivially-true check.

This file holds the notion itself, independent of any particular security definition, so that
completeness, round-by-round and coordinate-wise special soundness arguments can all share it.

## Contents

* `Verifier.IsGuardedWith` / `Verifier.IsGuarded`: the guard predicate, with a `Bool`-valued
  check; `IsGuarded.of_isPure` is the pure case.
* `Verifier.GuardedForm`: guardedness with its check and verdict map as **data**, the guarded
  mirror of `Verifier.PureForm`. `GuardedForm.isGuarded` forgets back to the class, and
  `PureForm.toGuardedForm` is the data form of `IsGuarded.of_isPure`, and `GuardedForm.ofEq`
  transports guardedness data along an equality of verifiers.
* `Verifier.GuardedForm.append`: closure of guardedness data under `Verifier.append`, with
  composite check `check₁ s tr.fst && check₂ (out₁ s tr.fst) tr.snd`; `Verifier.IsGuarded.append`
  is the forgetful corollary.
* `Verifier.append_run_guardedLeft`: running an appended verifier whose left factor is guarded.
* `Verifier.GuardedForm.prEvent_pos_of_check`: a guarded verifier whose guard passes outputs its
  verdict with positive probability.
The oracle-query adapter preserves native output-oracle routing through
`OracleVerifier.mkVerifierOStmtOut`.

Adapted from ArkLib PRs #1294–#1296, reviewed head
`9b0b5c962d97a9a0a9388c0bcc7e70d503e9ddd9`.
-/

set_option autoImplicit false

open OracleComp OracleSpec ProtocolSpec

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {StmtIn StmtOut : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}

/-- A deterministic verdict carried as data, without choosing it from `IsPure`. -/
structure PureForm (V : Verifier oSpec StmtIn StmtOut pSpec) where
  /-- The deterministic output statement. -/
  verify : StmtIn → FullTranscript pSpec → StmtOut
  /-- The verifier returns exactly that output. -/
  verify_eq : ∀ stmt tr, V.verify stmt tr = pure (verify stmt tr)

/-- Forget a deterministic verdict witness to the purity class. -/
theorem PureForm.isPure {V : Verifier oSpec StmtIn StmtOut pSpec} (P : V.PureForm) :
    V.IsPure := ⟨P.verify, P.verify_eq⟩

/-- A verifier is **guarded with** a `Bool`-valued `check` and a deterministic output map `out` if
its verdict is `pure (out stmt tr)` when the check passes and `failure` otherwise. This is the
faithful model of a verifier that rejects at runtime (the check is `Bool`-valued; decidable-`Prop`
consumers use `decide`). -/
def IsGuardedWith (V : Verifier oSpec StmtIn StmtOut pSpec)
    (check : StmtIn → FullTranscript pSpec → Bool)
    (out : StmtIn → FullTranscript pSpec → StmtOut) : Prop :=
  ∀ stmt tr, V.verify stmt tr = if check stmt tr then pure (out stmt tr) else failure

/-- A verifier is **guarded** if it is guarded with *some* check and output map. Purity is the
special case `check := fun _ _ => true` (`IsGuarded.of_isPure`). -/
class IsGuarded (V : Verifier oSpec StmtIn StmtOut pSpec) : Prop where
  is_guarded : ∃ check out, V.IsGuardedWith check out

/-- Every pure verifier is guarded, with the trivially-true check. -/
theorem IsGuarded.of_isPure (V : Verifier oSpec StmtIn StmtOut pSpec) (h : V.IsPure) :
    V.IsGuarded := by
  obtain ⟨f, hf⟩ := h.is_pure
  exact ⟨fun _ _ => true, f, fun stmt tr => by simp [hf stmt tr]⟩

/-- Every pure verifier is guarded automatically: the instance form of `IsGuarded.of_isPure`. -/
instance (V : Verifier oSpec StmtIn StmtOut pSpec) [h : V.IsPure] : V.IsGuarded :=
  IsGuarded.of_isPure V h

/-- A **guardedness witness carrying check and output map as data**: the bundled form of
`Verifier.IsGuardedWith`, and the guarded mirror of `Verifier.PureForm`.

As for purity, the `IsGuarded` *class* only asserts that some `(check, out)` pair exists, so
reading `out` off it costs `Classical.choice`. Consumers that must *name* the verdict map, such as
composed extractors and escape events, carry this data instead. -/
structure GuardedForm (V : Verifier oSpec StmtIn StmtOut pSpec) where
  /-- The runtime guard. -/
  check : StmtIn → FullTranscript pSpec → Bool
  /-- The verdict where the guard passes. -/
  out : StmtIn → FullTranscript pSpec → StmtOut
  /-- The verifier is guarded with exactly these. -/
  verify_eq : V.IsGuardedWith check out

/-- Forget the data: a `Verifier.GuardedForm` yields the `Verifier.IsGuarded` class. -/
theorem GuardedForm.isGuarded {V : Verifier oSpec StmtIn StmtOut pSpec} (G : V.GuardedForm) :
    V.IsGuarded :=
  ⟨G.check, G.out, G.verify_eq⟩

/-- Every pure form is a guarded form, at the trivially-true check: the data form of
`Verifier.IsGuarded.of_isPure`. Lossless, and computable — the verdict function carries over. -/
def PureForm.toGuardedForm {V : Verifier oSpec StmtIn StmtOut pSpec} (P : V.PureForm) :
    V.GuardedForm where
  check := fun _ _ => true
  out := P.verify
  verify_eq := fun stmt tr => by rw [P.verify_eq stmt tr]; simp

/-- Transport a guarded form along an equality of verifiers. The check and verdict map are kept
as they are; only the run equation is rewritten. This is how a guarded form built for one
presentation of a verifier serves another, such as the `Verifier.append` of two converted oracle
verifiers serving the converted `OracleVerifier.append` (`OracleVerifier.append_toVerifier`). -/
def GuardedForm.ofEq {V V' : Verifier oSpec StmtIn StmtOut pSpec} (h : V = V')
    (G : V.GuardedForm) : V'.GuardedForm where
  check := G.check
  out := G.out
  verify_eq := h ▸ G.verify_eq

section GuardedFormAppend

variable {Stmt₁ Stmt₂ Stmt₃ : Type} {m k : ℕ}
  {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec k}

/-- Deterministic verdict data composes at the actual intermediate statement. -/
def PureForm.append {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁}
    {V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂} (P₁ : V₁.PureForm) (P₂ : V₂.PureForm) :
    (V₁.append V₂).PureForm where
  verify stmt tr := P₂.verify (P₁.verify stmt tr.fst) tr.snd
  verify_eq stmt tr := by
    simp only [Verifier.append, P₁.verify_eq, pure_bind, P₂.verify_eq]

/-- **Guardedness data composes computably**: the composed guard runs the left check on the
transcript prefix and, if it passes, the right check on the suffix from the statement the left
verifier outputs at the seam; the composed verdict is the right verdict there. The guarded mirror of
`Verifier.PureForm.append`, and transcript-level in the same way — the seam is `tr.fst`/`tr.snd`,
with no challenge-tree path machinery.

`verify_eq` normalizes `Verifier.append`'s bind under the two `if`-splits, mirroring
`Verifier.PureForm.append`; `Verifier.IsGuarded.append` is proved from it by forgetting the
data. -/
def GuardedForm.append {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁}
    {V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂} (G₁ : V₁.GuardedForm) (G₂ : V₂.GuardedForm) :
    (V₁.append V₂).GuardedForm where
  check := fun stmt tr => G₁.check stmt tr.fst && G₂.check (G₁.out stmt tr.fst) tr.snd
  out := fun stmt tr => G₂.out (G₁.out stmt tr.fst) tr.snd
  verify_eq := fun stmt tr => by
    simp only [Verifier.append]
    rw [G₁.verify_eq stmt tr.fst]
    by_cases hc₁ : G₁.check stmt tr.fst = true
    · rw [ite_eq_left hc₁, pure_bind, G₂.verify_eq (G₁.out stmt tr.fst) tr.snd]
      by_cases hc₂ : G₂.check (G₁.out stmt tr.fst) tr.snd = true <;> simp [hc₁, hc₂]
    · rw [ite_eq_right hc₁]
      simp [hc₁]

/-- Guardedness is closed under `Verifier.append`: forget the data of `GuardedForm.append`. -/
theorem IsGuarded.append (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂) (h₁ : V₁.IsGuarded) (h₂ : V₂.IsGuarded) :
    (V₁.append V₂).IsGuarded :=
  (GuardedForm.append ⟨_, _, h₁.is_guarded.choose_spec.choose_spec⟩
    ⟨_, _, h₂.is_guarded.choose_spec.choose_spec⟩).isGuarded

/-- Running an appended verifier whose left factor is **guarded**: the composed run is the right
verifier's at the left verdict where the left check passes, and `failure` where it does not. -/
theorem append_run_guardedLeft
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (check₁ : Stmt₁ → pSpec₁.FullTranscript → Bool)
    (out₁ : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hV₁ : V₁.IsGuardedWith check₁ out₁)
    (stmt : Stmt₁) (tr₁ : pSpec₁.FullTranscript) (tr₂ : pSpec₂.FullTranscript) :
      (V₁.append V₂).run stmt (tr₁ ++ₜ tr₂) =
        if check₁ stmt tr₁ then V₂.run (out₁ stmt tr₁) tr₂ else failure := by
  simp only [Verifier.run, Verifier.append, FullTranscript.append_fst,
    FullTranscript.append_snd, hV₁ stmt tr₁]
  by_cases hc : check₁ stmt tr₁ <;> simp [hc]

/-- A rejected first phase aborts the composite, regardless of the second verifier. -/
theorem GuardedForm.append_run_of_reject
    {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁} (G₁ : V₁.GuardedForm)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (stmt : Stmt₁) (tr₁ : pSpec₁.FullTranscript) (tr₂ : pSpec₂.FullTranscript)
    (h : G₁.check stmt tr₁ = false) :
    (V₁.append V₂).run stmt (tr₁ ++ₜ tr₂) = failure := by
  rw [append_run_guardedLeft V₁ V₂ G₁.check G₁.out G₁.verify_eq, h]
  rfl

end GuardedFormAppend

/-- A guarded verifier whose guard passes outputs its verdict with positive probability, because
`init` has a possible outcome. The converse direction is
`Verifier.GuardedForm.check_and_of_prEvent_pos`. -/
theorem GuardedForm.prEvent_pos_of_check {σ : Type} {init : ProbComp σ}
    {impl : QueryImpl oSpec (StateT σ ProbComp)} {V : Verifier oSpec StmtIn StmtOut pSpec}
    (G : V.GuardedForm)
    {stmt : StmtIn} {tr : FullTranscript pSpec} {p : StmtOut → Prop}
    (hc : G.check stmt tr = true) (hp : p (G.out stmt tr)) :
    Pr{let s ← OptionT.mk do
      (simulateQ impl (V.run stmt tr)).run' (← init)}[p s] > 0 := by
  have hrun : (V.run stmt tr : OracleComp oSpec (Option StmtOut)) =
      pure (some (G.out stmt tr)) := by
    simp only [Verifier.run, G.verify_eq stmt tr, hc, ite_true]
    rfl
  rw [gt_iff_lt, OptionT.prEvent_mk_pos_iff]
  obtain ⟨s, hs⟩ := OracleComp.support_nonempty init
  refine ⟨G.out stmt tr, ?_, hp⟩
  rw [hrun]
  simp only [simulateQ_pure, support_bind, Set.mem_iUnion, exists_prop]
  exact ⟨s, hs, by simp [StateT.run'_eq, StateT.run_pure]⟩

end Verifier

namespace Verifier.GuardedForm

variable {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
    {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}
    {n : ℕ} {pSpec : ProtocolSpec n}
    [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]
    [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]

set_option backward.isDefEq.respectTransparency false in
/-- The guard and verdict of a **query-guard-return** oracle verifier as data. If the verifier
makes one query `q` to the prover's messages, guards on the answer and the challenges, and returns
a statement built from them, then its induced verifier is guarded: the guard is `check` at the
transcript's answer and challenges, and the verdict is `accept` there, with the materialized output
oracles. The run equation follows from native oracle-query simulation. -/
def ofQueryGuard
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (q : [pSpec.Message]ₒ.Domain)
    (check : StmtIn → [pSpec.Message]ₒ.Range q → pSpec.Challenges → Prop)
    [hcheck : ∀ s a c, Decidable (check s a c)]
    (accept : StmtIn → [pSpec.Message]ₒ.Range q → pSpec.Challenges → StmtOut)
    (hV : ∀ stmt chals, verifier.verify stmt chals = do
      let a ← query (spec := [pSpec.Message]ₒ) q
      guard (check stmt a chals)
      return accept stmt a chals) :
    verifier.toVerifier.GuardedForm where
  check s tr := @decide _
    (hcheck s.1 (OracleInterface.answer (tr.messages q.1) q.2) tr.challenges)
  out s tr := (accept s.1 (OracleInterface.answer (tr.messages q.1) q.2) tr.challenges,
    OracleVerifier.mkVerifierOStmtOut verifier.embed verifier.hEq s.2 tr)
  verify_eq s tr := by
    apply OptionT.ext
    simp only [OracleVerifier.toVerifier, hV, guard, OptionT.run_bind]
    erw [simulateQ_bind]
    erw [OptionT.simulateQ_simOracle2_liftM_query_T2]
    simp only [pure_bind]
    by_cases hc : check s.1 (OracleInterface.answer (tr.messages q.1) q.2) tr.challenges <;>
      simp [hc, OptionT.run, OptionT.mk, OptionT.bind, simulateQ_pure,
        OracleVerifier.mkVerifierOStmtOut] <;> rfl

end Verifier.GuardedForm

#print axioms Verifier.PureForm.isPure
#print axioms Verifier.PureForm.append
#print axioms Verifier.IsGuarded.of_isPure
#print axioms Verifier.GuardedForm.isGuarded
#print axioms Verifier.PureForm.toGuardedForm
#print axioms Verifier.GuardedForm.ofEq
#print axioms Verifier.GuardedForm.append
#print axioms Verifier.IsGuarded.append
#print axioms Verifier.append_run_guardedLeft
#print axioms Verifier.GuardedForm.append_run_of_reject
#print axioms Verifier.GuardedForm.prEvent_pos_of_check
#print axioms Verifier.GuardedForm.ofQueryGuard
