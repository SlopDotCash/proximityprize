/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import VCVio.OracleComp.SimSemantics.SimulateQ

/-!
# `simulateQ` over `mapM` in `OptionT (OracleComp _)`

If every step of a monadic `mapM` resolves to `pure (some _)` under `simulateQ`, then the
entire `mapM` resolves to `pure (some _)` of the pointwise mapped result.

These lemmas are generic — independent of any specific oracle, target monad, or proof system.
They sit alongside the existing `simulateQ_optionT_*` family in
`VCVio/OracleComp/SimSemantics/SimulateQ.lean` (`simulateQ_optionT_bind'`,
`simulateQ_optionT_bind''`, `simulateQ_optionT_lift`, `simulateQ_option_elim`,
`simulateQ_option_elimM`) and are intended to be upstreamed to that file.

They are used by oracle-verifier equivalence proofs in ArkLib (e.g. for sum-check) where the
verifier collects a vector of oracle evaluations via `mapM` and each oracle answer is pure
under `simulateQ`.
-/

universe u

open OracleComp

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {r : Type → Type*}
  [Monad r] [LawfulMonad r] (impl : QueryImpl spec r)

/-- `simulateQ` over `OptionT.map` when the underlying computation is already pure after
simulation. -/
lemma simulateQ_optionT_map_of_pure
    {α β : Type} (mx : OptionT (OracleComp spec) α) (f : α → β) (x : α)
    (hmx : simulateQ impl mx.run =
      (pure (some x) : r (Option α))) :
    simulateQ impl (f <$> mx).run =
    (pure (some (f x)) : r (Option β)) := by
  rw [OptionT.run_map, simulateQ_map]
  rw [hmx]
  simp

/-- `simulateQ` over `List.mapM` in `OptionT`: when each step is pure under `simulateQ`,
the whole `mapM` is pure of the pointwise mapped list. -/
lemma simulateQ_optionT_list_mapM_pure
    {α β : Type} (f : α → OptionT (OracleComp spec) β) (g : α → β) (l : List α)
    (hfg : ∀ x, simulateQ impl (f x : OracleComp spec (Option β)) =
      (pure (some (g x)) : r (Option β))) :
    simulateQ impl ((l.mapM f : OptionT (OracleComp spec) (List β)) :
      OracleComp spec (Option (List β))) =
    (pure (some (l.map g)) : r (Option (List β))) := by
  induction l with
  | nil => exact simulateQ_pure impl (some [])
  | cons a rest ih =>
    change simulateQ impl ((a :: rest).mapM f : OptionT (OracleComp spec) (List β)).run = _
    rw [List.mapM_cons, OptionT.run_bind, Option.elimM, simulateQ_bind]
    -- After rewrite: Option.elimM (simulateQ impl (f a).run) (pure none) (fun r => ...) = ...
    -- Substitute the first step via `hfg a`.
    have h₁ : (f a : OracleComp spec (Option β)) = (f a).run := rfl
    rw [← h₁, hfg a]
    simp only [pure_bind, Option.elim_some]
    -- Now peel the inner bind for `let rs ← rest.mapM f; pure (r :: rs)`.
    rw [OptionT.run_bind, Option.elimM, simulateQ_bind]
    have h₂ : (rest.mapM f : OracleComp spec (Option (List β))) =
        (rest.mapM f : OptionT (OracleComp spec) (List β)).run := rfl
    rw [← h₂, ih]
    simp only [pure_bind, Option.elim_some]
    -- The final step is `pure (g a :: rest.map g)` in OptionT.
    change simulateQ impl ((pure (g a :: rest.map g) : OptionT (OracleComp spec) (List β)).run) = _
    exact simulateQ_pure impl (some (g a :: rest.map g))

/-- `simulateQ` over `Vector.mapM` in `OptionT`: when each step is pure under `simulateQ`,
the whole `mapM` is pure of the pointwise mapped vector. -/
lemma simulateQ_optionT_mapM_pure
    {n : ℕ} {α β : Type} (f : α → OptionT (OracleComp spec) β) (g : α → β) (xs : Vector α n)
    (hfg : ∀ x, simulateQ impl (f x : OracleComp spec (Option β)) =
      (pure (some (g x)) : r (Option β))) :
    simulateQ impl ((xs.mapM f : OptionT (OracleComp spec) (Vector β n)) :
      OracleComp spec (Option (Vector β n))) =
    (pure (some (xs.map g)) : r (Option (Vector β n))) := by
  -- Step 1: OptionT-level chain `toArray <$> xs.mapM f = List.toArray <$> xs.toList.mapM f`.
  have h_vl :
      (Vector.toArray <$> xs.mapM f : OptionT (OracleComp spec) (Array β)) =
        List.toArray <$> xs.toList.mapM f :=
    (Vector.toArray_mapM (xs := xs) (f := f)).trans Array.mapM_eq_mapM_toList
  -- Step 2: At the OracleComp (run) level, push `<$>` into `Option.map <$>` via `OptionT.run_map`.
  have h_run :
      Option.map Vector.toArray <$>
        ((xs.mapM f : OptionT (OracleComp spec) (Vector β n)) :
          OracleComp spec (Option (Vector β n))) =
      Option.map List.toArray <$>
        ((xs.toList.mapM f : OptionT (OracleComp spec) (List β)) :
          OracleComp spec (Option (List β))) := by
    have h : (Vector.toArray <$> xs.mapM f : OptionT (OracleComp spec) (Array β)).run =
        (List.toArray <$> xs.toList.mapM f : OptionT (OracleComp spec) (Array β)).run :=
      congrArg OptionT.run h_vl
    rw [OptionT.run_map, OptionT.run_map] at h
    exact h
  -- Step 3: Apply `simulateQ` to both sides; push it through `<$>` via `simulateQ_map`.
  have h_sim := congrArg (simulateQ impl) h_run
  rw [simulateQ_map, simulateQ_map] at h_sim
  -- Step 4: Reduce the list-side via the list lemma.
  rw [simulateQ_optionT_list_mapM_pure impl f g xs.toList hfg] at h_sim
  -- Step 5: Massage the RHS so both sides have the form `Option.map Vector.toArray <$> _`.
  have h_simp_rhs :
      (Option.map List.toArray <$>
          (pure (some (xs.toList.map g)) :
            r (Option (List β)))) =
      Option.map Vector.toArray <$>
        (pure (some (xs.map g)) : r (Option (Vector β n))) := by
    rw [map_pure, map_pure]
    congr 1
    simp only [Option.map_some, Option.some.injEq]
    rw [← Vector.toList_map]; exact Array.toArray_toList
  rw [h_simp_rhs] at h_sim
  -- Step 6: Invert `Option.map Vector.toArray <$> _` via injectivity (`map_inj_right`).
  have h_inj : ∀ {x y : Option (Vector β n)},
      Option.map Vector.toArray x = Option.map Vector.toArray y → x = y := by
    intro x y hxy
    rcases x with _ | x <;> rcases y with _ | y <;>
      simp only [Option.map_none, Option.map_some, Option.some.injEq, reduceCtorEq] at hxy
    · rfl
    · exact congrArg some (Vector.toArray_inj.mp hxy)
  exact (map_inj_right h_inj).mp h_sim

end OracleComp
