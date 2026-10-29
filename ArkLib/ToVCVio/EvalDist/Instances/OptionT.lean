/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import VCVio.EvalDist.Instances.OptionT
import VCVio.EvalDist.Monad.Map
import VCVio.OracleComp.ProbComp

/-!
# Additions to VCV-io's `EvalDist.Instances.OptionT`
-/

/-- Bridge lemma: when two `OptionT ProbComp` computations have underlying `run`s related by
    an `Option.map` of a function `f`, their probability events of `P` and `P ∘ f` agree. -/
lemma OptionT.probEvent_eq_of_run_map_eq {α β : Type}
    (mx : OptionT ProbComp α) (my : OptionT ProbComp β) (f : β → α) (P : α → Prop)
    (h : mx.run = (Option.map f) <$> my.run) :
    Pr{let x ← mx}[P x] = Pr{let y ← my}[P (f y)] := by
  have hmx : mx = f <$> my := by
    change mx.run = (f <$> my).run
    rw [OptionT.run_map]; exact h
  rw [hmx, prEvent_map]

/-- **Cross-type `probEvent` congruence.** When two computations of *propositionally-equal* value
types have heterogeneously-equal discrete `evalDist`s and corresponding events (transported along
the type
equality), their probability events agree. The seam-transfer proofs produce exactly this shape: the
appended and recast experiments live over equal-but-not-defeq transcript types, with `evalDist`s
related through that type equality. Proved by `subst`ing the type equality (turning the `HEq`s into
`Eq`s) and using that native event probability depends only on the discrete evaluation measure and event-set. -/
lemma probEvent_congr_heq {m : Type → Type _} [Monad m] [LawfulMonad m]
    [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α β : Type} (h : α = β)
    (mx : m α) (my : m β) (P : α → Prop) (Q : β → Prop)
    (hd : HEq (@evalDist m _ α ⊤ mx) (@evalDist m _ β ⊤ my))
    (hPQ : ∀ x, P x ↔ Q (h ▸ x)) :
    Pr{let x ← mx}[P x] = Pr{let y ← my}[Q y] := by
  subst h
  let : MeasurableSpace α := ⊤
  have hde : 𝒟[mx] = 𝒟[my] := eq_of_heq hd
  rw [prEvent_eq_evalDist_of_discrete, prEvent_eq_evalDist_of_discrete, hde]
  congr 1
  exact Set.ext fun x => hPQ x
