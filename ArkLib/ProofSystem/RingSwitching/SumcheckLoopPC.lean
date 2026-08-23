/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.RingSwitching.SumcheckPhase

/-!
# Sumcheck-loop perfect completeness (issue #29)

`sumcheckLoopOracleReduction_perfectCompleteness` lives in its own file because its elaboration is
dominated by a single `whnf`-heavy definitional check (the `seqCompose`/`toReduction` bridge against
the keystone conclusion); isolating it keeps `SumcheckPhase` fast to (re)build and makes this one
declaration cheap to iterate on / profile.
-/

namespace RingSwitching.SumcheckPhase

open OracleSpec OracleComp ProtocolSpec Polynomial MvPolynomial Sumcheck.Structured

variable (κ : ℕ) [NeZero κ]
variable (L : Type) [CommRing L] [Nontrivial L] [Fintype L] [DecidableEq L] [SampleableType L]
variable (K : Type) [CommRing K] [Fintype K] [DecidableEq K]
variable [Algebra K L]
variable (P : RingSwitchingProfile K L κ)
variable (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
variable (h_l : ℓ = ℓ' + κ)
variable (aOStmtIn : AbstractOStmtIn L ℓ')
variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl []ₒ (StateT σ ProbComp)}


-- The keystone application unifies the concrete `sumcheckLoopOracleReduction` (a `@[reducible]`
-- `OracleReduction.seqCompose`) against the keystone conclusion, whose `OracleReduction`-level
-- `perfectCompleteness` unfolds through `.toReduction` of the full ring-switching seqCompose — this
-- defeq is `whnf`-heavy (slow but terminating), hence the raised heartbeat budget.
set_option maxHeartbeats 40000000 in
/-- **Sumcheck-loop perfect completeness (issue #29, phase 1).** The `seqCompose` of the `ℓ'`
per-round oracle reductions (`sumcheckLoopOracleReduction = OracleReduction.seqCompose …
iteratedSumcheckOracleReduction`) is perfectly complete from `0` to `Fin.last ℓ'`.

Pure pass-through to the proven oracle-level n-ary keystone
`OracleReduction.seqCompose_perfectCompleteness_threaded`, fed with:
- the per-round reductions `iteratedSumcheckOracleReduction i` and the relation family
  `fun i => sumcheckRoundRelation … i` (so `rel 0`/`rel (Fin.last ℓ')` are the loop endpoints and
  the per-round seam `rel i.castSucc → rel i.succ` is exactly the `_proved` residual shape);
- `hValid`: every round's protocol `pSpecSumcheckRound L = ⟨![P_to_V, V_to_P], …⟩` is nonempty and
  opens with a `P_to_V` prover message (by `rfl`);
- `hImplSupp` over the empty oracle spec `[]ₒ` (vacuous);
- the per-round completeness `h i = iteratedSumcheckOracleReduction_perfectCompleteness_proved`.
The per-round challenge `Fintype`/`Inhabited` are supplied locally (the challenge type at index `1`
is the field `L`). -/
theorem sumcheckLoopOracleReduction_perfectCompleteness [IsDomain L]
    (hInit : NeverFail init) :
    OracleReduction.perfectCompleteness
      (oracleReduction := sumcheckLoopOracleReduction κ L K P ℓ ℓ' aOStmtIn)
      (relIn := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn 0)
      (relOut := sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn (Fin.last ℓ'))
      (init := init) (impl := impl) := by
  classical
  haveI : Nonempty L := ⟨0⟩
  -- per-round challenge finiteness/inhabitedness: the challenge type at index `1` is the field `L`
  -- (index `0` is a `P_to_V` message, so its `ChallengeIdx` proof is absurd).
  -- The per-round challenge type (at index `1`) is the field `L`; index `0` is a `P_to_V` message
  -- so its `ChallengeIdx` proof is absurd. We supply `SampleableType`/`Fintype`/`Inhabited`
  -- explicitly (via the explicit-args keystone form), avoiding the `(fun _ => p) i`-redex instance
  -- mismatch for the literal per-round protocol `fun _ => pSpecSumcheckRound L`.
  -- Pre-align the goal to the delegate's exact conclusion shape (`seqCompose … |>.perfectCompleteness
  -- … (rel 0) (rel (Fin.last ℓ'))`): `sumcheckLoopOracleReduction` is `@[reducible]` so this `show`
  -- is a single delta step, and `(fun i => …) 0` is a β step — pinning every implicit of
  -- `perfectCompleteness` syntactically. Without it, `refine`-driven unification of those implicits
  -- against the folded definition whnf-normalizes the protocol type families (pathologically slow).
  show OracleReduction.perfectCompleteness
    (oracleReduction := OracleReduction.seqCompose (m := ℓ') (oSpec := []ₒ)
      (Stmt := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P))
      (OStmt := fun _ => aOStmtIn.OStmtIn)
      (Wit := fun i => SumcheckWitness L ℓ' i)
      (R := fun (i : Fin ℓ') => iteratedSumcheckOracleReduction κ L K P ℓ ℓ' aOStmtIn i))
    (relIn := (fun i => sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i) 0)
    (relOut := (fun i => sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i) (Fin.last ℓ'))
    (init := init) (impl := impl)
  have H := OracleReduction.seqCompose_pc_oracle_msg' (init := init) (impl := impl)
    (Stmt := Statement (L := L) (ℓ := ℓ') (RingSwitchingBaseContext κ L K ℓ P))
    (OStmt := fun _ => aOStmtIn.OStmtIn)
    -- `Oₛ`/`Oₘ` supplied explicitly with β-reduced target types: instance *search* against the
    -- literal-lambda redexes `(fun _ => …) i` whnf-loops (the docstring's warning) — this avoids it.
    (Oₛ := fun _ j => (inferInstance : OracleInterface (aOStmtIn.OStmtIn j)))
    (Oₘ := fun _ j => (inferInstance : OracleInterface ((pSpecSumcheckRound L).Message j)))
    (Wit := fun i => SumcheckWitness L ℓ' i)
    (R := fun i => iteratedSumcheckOracleReduction κ L K P ℓ ℓ' aOStmtIn i)
    (coh := fun i => instIteratedSumcheckOracleReductionAppendCoherent
      (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (aOStmtIn := aOStmtIn) i)
    (rel := fun i => sumcheckRoundRelation κ L K P ℓ ℓ' h_l aOStmtIn i)
    (fun _ _ => inferInstance)
    (fun _ j => by
      rcases j with ⟨⟨v, hv⟩, hj⟩
      interval_cases v
      · exact absurd hj (by simp [pSpecSumcheckRound, Sumcheck.Structured.pSpecSumcheckRound])
      · simpa only [pSpecSumcheckRound, Sumcheck.Structured.pSpecSumcheckRound,
          ProtocolSpec.Challenge, Matrix.cons_val_one, Matrix.cons_val_fin_one] using
          (inferInstance : Fintype L))
    (fun _ j => by
      rcases j with ⟨⟨v, hv⟩, hj⟩
      interval_cases v
      · exact absurd hj (by simp [pSpecSumcheckRound, Sumcheck.Structured.pSpecSumcheckRound])
      · simpa only [pSpecSumcheckRound, Sumcheck.Structured.pSpecSumcheckRound,
          ProtocolSpec.Challenge, Matrix.cons_val_one, Matrix.cons_val_fin_one] using
          (⟨(0 : L)⟩ : Inhabited L))
    (fun _ => ⟨by norm_num, rfl⟩)
    hInit
    (by simp only [Set.fmap_eq_image, IsEmpty.forall_iff, implies_true])
    (fun i => iteratedSumcheckOracleReduction_perfectCompleteness_proved
      (κ := κ) (L := L) (K := K) (P := P) (ℓ := ℓ) (ℓ' := ℓ') (h_l := h_l)
      (aOStmtIn := aOStmtIn) (init := init) (impl := impl) hInit i)
  exact H
end RingSwitching.SumcheckPhase
