/-
Copyright (c) 2026 VCVio Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.OracleComp.QueryTracking.RandomOracle.FreshQuery

/-! # Public finite-key and cache transports for expected-query bounds

Adapted from VCVio `e417e35ac452c3994173eda268a8eee0d26115d2`.
-/

open OracleSpec OracleComp
namespace OracleComp
variable {D α : Type} {R : D → Type}

/-- A finite set containing every key that can occur on any response branch of a program. -/
noncomputable def possibleQueryKeys [DecidableEq D] [∀ d, Finite (R d)]
    (oa : OracleComp (ofFn R) α) : Finset D := by
  classical
  letI : ∀ d, Fintype (R d) := fun d => Fintype.ofFinite (R d)
  exact OracleComp.construct (C := fun _ => Finset D)
    (fun _ => ∅) (fun t _ rest => insert t (Finset.univ.biUnion rest)) oa

@[simp] theorem possibleQueryKeys_pure [DecidableEq D] [∀ d, Finite (R d)] (a : α) :
    possibleQueryKeys (pure a : OracleComp (ofFn R) α) = ∅ := rfl

@[simp] theorem possibleQueryKeys_query_bind [DecidableEq D] [∀ d, Finite (R d)]
    (t : D) (k : R t → OracleComp (ofFn R) α) :
    possibleQueryKeys (liftM ((ofFn R).query t) >>= k) =
      insert t (Set.Finite.toFinset
        (Set.finite_iUnion fun u => (possibleQueryKeys (k u)).finite_toSet)) := by
  classical
  ext q
  simp [possibleQueryKeys]

/-- Every query is in the finite key support determined by the program syntax. -/
theorem allQueriesSatisfy_possibleQueryKeys [DecidableEq D] [∀ d, Finite (R d)]
    (oa : OracleComp (ofFn R) α) : AllQueriesSatisfy oa (· ∈ possibleQueryKeys oa) := by
  classical
  induction oa using OracleComp.inductionOn with
  | pure a => exact allQueriesSatisfy_pure _ _
  | query_bind t k ih =>
      rw [allQueriesSatisfy_query_bind_iff]
      refine ⟨by simp, fun u => ?_⟩
      have mono : ∀ (ob : OracleComp (ofFn R) α) (P Q : D → Prop),
          AllQueriesSatisfy ob P → (∀ d, P d → Q d) → AllQueriesSatisfy ob Q := by
        intro ob P Q h hpq
        induction ob using OracleComp.inductionOn with
        | pure a => exact allQueriesSatisfy_pure _ _
        | query_bind d rest ihr =>
            exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr
              ⟨hpq d ((allQueriesSatisfy_query_bind_iff _ _ _).mp h).1,
                fun v => ihr v (((allQueriesSatisfy_query_bind_iff _ _ _).mp h).2 v)⟩
      apply mono _ _ _ (ih u)
      intro d hd
      simp only [possibleQueryKeys_query_bind, Finset.mem_insert, Set.Finite.mem_toFinset,
        Set.mem_iUnion, Finset.mem_coe]
      exact Or.inr ⟨u, hd⟩


/-- Restrict a cached answer assignment to a finite key set. -/
def restrictCache (S : Finset D) (c : (ofFn R).QueryCache) :
    (ofFn (fun d : S => R d.val)).QueryCache :=
  QueryCache.ofFn (fun d => c d.val)

/-- Restriction commutes with updating a key in the retained set. -/
theorem restrictCache_update [DecidableEq D] (S : Finset D) (c : (ofFn R).QueryCache)
    (t : S) (u : R t.val) :
    restrictCache S (c.cacheQuery t.val u) = (restrictCache S c).cacheQuery t u := by
  apply QueryCache.ext
  intro q
  by_cases hq : q = t
  · subst q
    simp [restrictCache]
  · have hv : q.val ≠ t.val := fun h => hq (Subtype.ext h)
    simp [restrictCache, QueryCache.cacheQuery_of_ne _ _ hq,
      QueryCache.cacheQuery_of_ne _ _ hv]


/-- Extend a finite answer table with fixed arbitrary answers outside its key set. -/
noncomputable def extendTable [∀ d, Nonempty (R d)] (S : Finset D)
    (g : (d : S) → R d.val) : ∀ d, R d := by
  classical
  exact fun d => if h : d ∈ S then g ⟨d, h⟩ else Classical.arbitrary (R d)

@[simp] theorem extendTable_subtype [∀ d, Nonempty (R d)] (S : Finset D)
    (g : (d : S) → R d.val) (d : S) : extendTable S g d.val = g d := by
  simp [extendTable, d.property]

/-- Updating a retained answer cell commutes with extension to all keys. -/
theorem extendTable_update [DecidableEq D] [∀ d, Nonempty (R d)] (S : Finset D)
    (g : (d : S) → R d.val) (t : S) (u : R t.val) :
    extendTable S (Function.update g t u) = Function.update (extendTable S g) t.val u := by
  classical
  funext q
  by_cases hq : q = t.val
  · subst q
    simp
  · by_cases hs : q ∈ S
    · have hsub : (⟨q, hs⟩ : S) ≠ t := fun h => hq (congrArg Subtype.val h)
      simp [extendTable, hs, Function.update_of_ne hq, Function.update_of_ne hsub]
    · simp [extendTable, hs, Function.update_of_ne hq]


end OracleComp
