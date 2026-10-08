/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import VCVio.EvalDist.Instances.OptionT

/-!
# Additions to VCV-io's `EvalDist.Instances.OptionT`
-/

-- `OptionT.probEvent_eq_of_run_map_eq` is supplied by the upstream import.

/-- **Cross-type `probEvent` congruence.** When two computations of *propositionally-equal* value
types have heterogeneously-equal `evalSPMF`s and corresponding events (transported along the type
equality), their probability events agree. The seam-transfer proofs produce exactly this shape: the
appended and recast experiments live over equal-but-not-defeq transcript types, with `evalSPMF`s
related through that type equality. Proved by `subst`ing the type equality (turning the `HEq`s into
`Eq`s) and using that `probEvent` depends only on `evalSPMF` and the event-set. -/
lemma probEvent_congr_heq {m : Type → Type _} [Monad m] [MonadLiftT m SPMF] {α β : Type} (h : α = β)
    (mx : m α) (my : m β) (P : α → Prop) (Q : β → Prop)
    (hd : HEq (𝒮[mx]) (𝒮[my])) (hPQ : ∀ x, P x ↔ Q (h ▸ x)) :
    Pr[P | mx] = Pr[Q | my] := by
  subst h
  have hde : (𝒮[mx]) = (𝒮[my]) := eq_of_heq hd
  unfold probEvent
  rw [hde]
  congr 1
  exact congrArg (Set.image some) (Set.ext fun x => hPQ x)
