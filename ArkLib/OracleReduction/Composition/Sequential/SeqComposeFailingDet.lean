/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeFailingDet
import ArkLib.OracleReduction.Composition.Sequential.General

/-!
# Failing-determinism is preserved by sequential composition (issue #29)

The failing-deterministic rbr knowledge-soundness append keystones
(`Verifier.append_rbrKnowledgeSoundness_failingDet_subsingleton` and its OracleVerifier lift)
consume a determinism witness `hVerify : V.toVerifier = ⟨fun p tr => OptionT.mk (pure (v? p tr))⟩`.
For *composite* verifiers built by `OracleVerifier.seqCompose` this witness must be assembled from
the per-round witnesses. This file provides that assembly:

- `Verifier.IsFailingDet`: the existential failing-determinism predicate (some partial verdict
  function `v? : Stmt₁ → FullTranscript → Option Stmt₂` realizes the verifier);
- closure lemmas: pure (total-deterministic) verifiers are failing-deterministic
  (`IsFailingDet.of_pure`), the identity verifier is (`id_isFailingDet`), and the binary append of
  two failing-deterministic verifiers is (`IsFailingDet.append`, via the proven
  `append_failingDet_failingDet` combinator);
- the n-ary witness: `OracleVerifier.seqCompose_toVerifier_isFailingDet` — a `seqCompose` of oracle
  verifiers whose every compiled `toVerifier` is failing-deterministic compiles to a
  failing-deterministic `toVerifier`. Proved by induction, with each step fusing the seam by the
  proven `OracleReduction.oracleVerifier_append_toVerifier` keystone.
-/

open OracleComp OracleSpec ProtocolSpec

namespace Verifier

-- Pinned at `OracleSpec.{0,0}`: the `OracleVerifier.toVerifier` compilation (and the proven
-- failing-det append combinators) all live at universe 0, and so do all security consumers.
variable {ι : Type} {oSpec : OracleSpec.{0,0} ι}

/-- **Failing-determinism (existential form).** A verifier is *failing-deterministic* when some
partial verdict function `v? : Stmt₁ → FullTranscript → Option Stmt₂` realizes it: it makes no
oracle queries and either deterministically outputs a next statement (`some`) or rejects (`none`).
This is the witness shape consumed (after `obtain`) as `hVerify` by the failing-deterministic rbr
knowledge-soundness append keystones. -/
def IsFailingDet {Stmt₁ Stmt₂ : Type} {k : ℕ} {pSpec : ProtocolSpec k}
    (V : Verifier oSpec Stmt₁ Stmt₂ pSpec) : Prop :=
  ∃ v? : Stmt₁ → pSpec.FullTranscript → Option Stmt₂,
    V = ⟨fun s tr => OptionT.mk (pure (v? s tr))⟩

/-- A *total*-deterministic verifier is failing-deterministic (with the always-`some` verdict):
`OptionT`'s `pure x` is definitionally `OptionT.mk (pure (some x))`. -/
theorem IsFailingDet.of_pure {Stmt₁ Stmt₂ : Type} {k : ℕ} {pSpec : ProtocolSpec k}
    {V : Verifier oSpec Stmt₁ Stmt₂ pSpec} (v : Stmt₁ → pSpec.FullTranscript → Stmt₂)
    (hV : V = ⟨fun s tr => pure (v s tr)⟩) : V.IsFailingDet := by
  subst hV
  exact ⟨fun s tr => some (v s tr), rfl⟩

/-- The identity verifier is failing-deterministic (it returns its statement, never failing). -/
theorem id_isFailingDet {Stmt : Type} :
    (Verifier.id : Verifier oSpec Stmt Stmt !p[]).IsFailingDet :=
  IsFailingDet.of_pure (fun s _ => s) rfl

/-- **Failing-determinism is closed under binary append**, with the composed verdict given by
`Option.bind` (run the first verdict; on success feed the intermediate statement to the second). -/
theorem IsFailingDet.append {Stmt₁ Stmt₂ Stmt₃ : Type}
    {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁} {V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂}
    (h₁ : V₁.IsFailingDet) (h₂ : V₂.IsFailingDet) :
    (V₁.append V₂).IsFailingDet := by
  obtain ⟨v₁?, rfl⟩ := h₁
  obtain ⟨v₂?, rfl⟩ := h₂
  refine ⟨fun s tr => (v₁? s tr.fst).bind fun s₂ => v₂? s₂ tr.snd, ?_⟩
  simpa only using append_failingDet_failingDet v₁? v₂?

end Verifier

namespace OracleVerifier

variable {ι : Type} {oSpec : OracleSpec.{0,0} ι}

/-- Auxiliary (explicit-instance) form of `seqCompose_toVerifier_isFailingDet`, phrased on
`seqCompose'` so that the induction can specialize the interface/coherence arguments. -/
theorem seqCompose'_toVerifier_isFailingDet {m : ℕ}
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
    (h : ∀ i, (V i).toVerifier.IsFailingDet) :
    (OracleVerifier.seqCompose' Stmt OStmt Oₛ Oₘ V coh).toVerifier.IsFailingDet := by
  induction m with
  | zero =>
    rw [show (OracleVerifier.seqCompose' Stmt OStmt Oₛ Oₘ V coh).toVerifier
          = (@OracleVerifier.id ι oSpec (Stmt 0) (ιₛ 0) (OStmt 0) (Oₛ 0)).toVerifier from rfl,
      OracleVerifier.id_toVerifier]
    exact Verifier.id_isFailingDet
  | succ m ih =>
    letI : OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ 0) (Oₛ₂ := Oₛ 1) (Oₘ₁ := Oₘ 0) (V 0) :=
      coh 0
    change (OracleVerifier.append (V 0)
        (OracleVerifier.seqCompose' (Stmt ∘ Fin.succ) (fun i => OStmt (Fin.succ i))
          (fun i => Oₛ (Fin.succ i)) (fun i => Oₘ (Fin.succ i)) (fun i => V (Fin.succ i))
          (fun i => coh i.succ))).toVerifier.IsFailingDet
    rw [OracleReduction.oracleVerifier_append_toVerifier]
    exact (h 0).append (ih (Stmt ∘ Fin.succ) (fun i => OStmt (Fin.succ i))
      (fun i => Oₛ (Fin.succ i)) (fun i => Oₘ (Fin.succ i)) (fun i => V (Fin.succ i))
      (fun i => coh i.succ) (fun i => h i.succ))

/-- **The n-ary failing-determinism witness.** A `seqCompose` of oracle verifiers whose every
compiled `toVerifier` is failing-deterministic compiles to a failing-deterministic `toVerifier`.
Destructuring the conclusion yields the `hVerify` witness consumed by the failing-deterministic
rbr knowledge-soundness append keystones at composite seams. -/
theorem seqCompose_toVerifier_isFailingDet {m : ℕ}
    (Stmt : Fin (m + 1) → Type)
    {ιₛ : Fin (m + 1) → Type} (OStmt : (i : Fin (m + 1)) → ιₛ i → Type)
    [Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j)]
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)]
    (V : (i : Fin m) →
      OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ) (OStmt i.succ)
        (pSpec i))
    [coh : ∀ i, OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ i.castSucc) (Oₛ₂ := Oₛ i.succ)
      (Oₘ₁ := Oₘ i) (V i)]
    (h : ∀ i, (V i).toVerifier.IsFailingDet) :
    (OracleVerifier.seqCompose Stmt OStmt V).toVerifier.IsFailingDet :=
  seqCompose'_toVerifier_isFailingDet Stmt OStmt Oₛ Oₘ V coh h

end OracleVerifier

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms Verifier.IsFailingDet.of_pure
#print axioms Verifier.id_isFailingDet
#print axioms Verifier.IsFailingDet.append
#print axioms OracleVerifier.seqCompose'_toVerifier_isFailingDet
#print axioms OracleVerifier.seqCompose_toVerifier_isFailingDet
