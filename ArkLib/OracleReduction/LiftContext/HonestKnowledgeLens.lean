/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.LiftContext.Lens

/-!
# The honest knowledge-soundness lens: pullback-in / transported-out relations

The corrected per-phase relation contract for `liftContext` round-by-round *knowledge* soundness
(#114's rbr-KS leaves). For any statement lens with trivial (`Unit`) witnesses, the
`Extractor.Lens.IsKnowledgeSound` instance is provable **by construction** when the outer relations
are the lens-transported inner relations:

* `pullbackRelIn` — the outer input claim *is* the inner claim, read through `proj`;
* `transportedRelOut` — the largest outer output relation for which `proj_knowledgeSound` holds
  (every compatible inner statement lifting to the given outer output satisfies the inner
  relation).

This is the knowledge-soundness analogue of `Statement.Lens.pullbackIsSound`. It replaces the
**false-as-stated** per-phase contracts of the Spartan sum-check leaves
(`firstSumcheck_rbrKnowledgeSoundness` / `secondSumcheck_rbrKnowledgeSoundness`, whose
`lift_knowledgeSound` field demands "inner cube-sum identity at one fixed `τ` ⟹ outer R1CS
satisfiability" — false because the Schwartz–Zippel randomness over `τ` lives in the *preceding*
`firstChallenge`/`RandomQuery` phase, not in the sum-check phase). With the transported contracts
the per-leaf rbr-KS follows from `Verifier.liftContext_rbr_knowledgeSoundness` and the generic
sum-check rbr-KS, and R1CS satisfiability re-enters the global chain at the `firstChallenge`
phase's lens (Schwartz–Zippel, error `deg/|R|`).

Both fields hold definitionally — no probabilistic or algebraic content; `#print axioms` reports
no axioms at all.
-/

open OracleComp

namespace Extractor.Lens.Honest

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}

/-- **Pullback input relation** (`Unit` witnesses): the outer input claim is the inner input claim
read through the lens projection. -/
def pullbackRelIn (stmtLens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (innerRelIn : Set (InnerStmtIn × Unit)) : Set (OuterStmtIn × Unit) :=
  { x | (stmtLens.proj x.1, x.2) ∈ innerRelIn }

/-- **Transported output relation** (`Unit` witnesses): the largest outer output relation for which
`proj_knowledgeSound` holds — every compatible inner output statement lifting to the given outer
output satisfies the inner output relation. -/
def transportedRelOut (stmtLens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (innerRelOut : Set (InnerStmtOut × Unit))
    (compatStmt : OuterStmtIn → InnerStmtOut → Prop) : Set (OuterStmtOut × Unit) :=
  { y | ∀ sIn sOut, compatStmt sIn sOut → stmtLens.lift sIn sOut = y.1 →
          (sOut, ()) ∈ innerRelOut }

/-- **The honest knowledge-soundness lens instance.** For trivial (`Unit`) witnesses, the
pullback-in / transported-out relations make `Extractor.Lens.IsKnowledgeSound` true by
construction — both fields are definitional, with no false cross-phase implication. -/
@[reducible] def honestLensKS
    (stmtLens : Statement.Lens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (innerRelIn : Set (InnerStmtIn × Unit)) (innerRelOut : Set (InnerStmtOut × Unit))
    (compatStmt : OuterStmtIn → InnerStmtOut → Prop) :
    Extractor.Lens.IsKnowledgeSound
      (pullbackRelIn stmtLens innerRelIn)
      innerRelIn
      (transportedRelOut stmtLens innerRelOut compatStmt)
      innerRelOut
      compatStmt (fun _ _ => True)
      ⟨stmtLens, Witness.InvLens.trivial⟩ where
  proj_knowledgeSound := by
    rintro outerStmtIn innerStmtOut ⟨⟩ hCompat hLift
    exact hLift outerStmtIn innerStmtOut hCompat rfl
  lift_knowledgeSound := by
    rintro outerStmtIn ⟨⟩ ⟨⟩ _hCompat hRelIn
    exact hRelIn

end Extractor.Lens.Honest
