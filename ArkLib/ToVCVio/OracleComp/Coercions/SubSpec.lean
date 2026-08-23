/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import VCVio.OracleComp.Coercions.Add

/-!
# Additions to VCV-io's `OracleComp.Coercions.SubSpec`
-/

namespace OracleComp

universe u v w

lemma mem_support_of_mem_support_liftComp
    {ι τ α : Type} {spec : OracleSpec ι} {superSpec : OracleSpec τ}
    [MonadLiftT (OracleQuery spec) (OracleQuery superSpec)]
    (oa : OracleComp spec α) (x : α) :
    x ∈ support (oa.liftComp superSpec) → x ∈ support oa := by
  intro hx
  induction oa using OracleComp.inductionOn generalizing x with
  | pure y =>
      simpa using hx
  | query_bind q oa ih =>
      rw [OracleComp.liftComp_bind, mem_support_bind_iff] at hx
      rw [mem_support_bind_iff]
      obtain ⟨u, _hu, hx⟩ := hx
      exact ⟨u, OracleComp.mem_support_query q u, ih u x hx⟩

lemma liftComp_bind_pure
    {ι τ α β : Type} {spec : OracleSpec ι} {superSpec : OracleSpec τ}
    [MonadLiftT (OracleQuery spec) (OracleQuery superSpec)]
    (oa : OracleComp spec α) (f : α → β) :
    OracleComp.liftComp (do let a ← oa; pure (f a)) superSpec =
      f <$> OracleComp.liftComp oa superSpec := by
  change (f <$> oa).liftComp superSpec = f <$> oa.liftComp superSpec
  exact OracleComp.liftComp_map superSpec oa f

lemma bind_liftComp_map
    {ι τ α β γ : Type} {spec : OracleSpec ι} {superSpec : OracleSpec τ}
    [MonadLiftT (OracleQuery spec) (OracleQuery superSpec)]
    (oa : OracleComp spec α) (f : α → β) (body : β → OracleComp superSpec γ) :
    (do
      let b ← f <$> OracleComp.liftComp oa superSpec
      body b) =
    (do
      let a ← OracleComp.liftComp oa superSpec
      body (f a)) := by
  simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]

/-- Lifting an `OracleComp` from `(spec₁ + spec₂)` through the right-associated extension
`spec₁ + (spec₂ + spec₃)` and then across the add-association `SubSpec` agrees with the direct
lift into the left-associated extension `(spec₁ + spec₂) + spec₃`. -/
lemma liftComp_add_assoc_right
    {ι₁ : Type u} {ι₂ : Type v} {ι₃ : Type w}
    {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {spec₃ : OracleSpec ι₃}
    {α : Type u}
    (oa : OracleComp (spec₁ + spec₂) α) :
    liftComp (liftComp oa (spec₁ + (spec₂ + spec₃))) ((spec₁ + spec₂) + spec₃) =
      liftComp oa ((spec₁ + spec₂) + spec₃) := by
  induction oa using OracleComp.inductionOn with
  | pure _ => rfl
  | query_bind t oa ih =>
      rcases t with t | t
      · simp only [OracleComp.liftComp_bind, OracleComp.liftComp_query, bind_map_left]
        refine bind_congr ?_
        intro x
        exact ih x
      · simp only [OracleComp.liftComp_bind, OracleComp.liftComp_query, bind_map_left]
        refine bind_congr ?_
        intro x
        exact ih x

/-- `OptionT` version of `liftComp_add_assoc_right`. This is the coherence needed when a
transitive `OptionT (OracleComp _)` lift passes through `spec₁ + (spec₂ + spec₃)` before landing in
the left-associated target `(spec₁ + spec₂) + spec₃`, while another path lifts directly. -/
lemma liftM_OptionT_add_assoc_right
    {ι₁ : Type u} {ι₂ : Type v} {ι₃ : Type w}
    {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {spec₃ : OracleSpec ι₃}
    {α : Type u}
    (oa : OptionT (OracleComp (spec₁ + spec₂)) α) :
    (liftM (liftM oa : OptionT (OracleComp (spec₁ + (spec₂ + spec₃))) α) :
      OptionT (OracleComp ((spec₁ + spec₂) + spec₃)) α) =
    OptionT.mk (OracleComp.liftComp oa.run ((spec₁ + spec₂) + spec₃)) := by
  apply OptionT.ext
  dsimp only [liftM, MonadLiftT.monadLift, MonadLift.monadLift]
  exact liftComp_add_assoc_right (oa := oa.run)

#print axioms OracleComp.liftComp_add_assoc_right
#print axioms OracleComp.liftM_OptionT_add_assoc_right

end OracleComp
