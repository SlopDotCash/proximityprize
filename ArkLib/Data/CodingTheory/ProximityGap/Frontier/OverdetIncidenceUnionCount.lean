/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Module.Submodule.Basic
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf2NH_overdet_single_gamma

/-!
# Over-determined far-line incidence is a UNION OF PER-WITNESS SINGLETONS (#407, δ* count face)

## The honest gap this file fills

The δ* prize object is the **far-line incidence count** `I = #{γ : ∃ far witness S,
u₀ + γ·u₁ explainable on S}` (`B1IncidenceBridge.farIncidence`,
`WorstCaseFarIncidenceBounded`).  The in-tree scope notes
(`_RThinRealizabilityCodim.realizability_bounds_set_not_count`,
`B1IncidenceBridge.worstCaseIncidence_is_the_open_object`) are emphatic that this **count** is the
genuine open object, and that no per-set/value bound supplies it — the gap is precisely the
*union over witnesses* of the per-witness γ-sets.

The per-witness piece is already proved, field-size-free, in
`_wf2NH_overdet_single_gamma.lean`:

> `incidence_subsingleton_of_not_mem` : in the over-determined / far regime (`b ∉ W`), the
> γ-set `{γ : a + γ•b ∈ W}` of a SINGLE witness is a **subsingleton** (≤ 1 γ).

This file supplies the elementary but missing **counting bridge**: a finite filter of γ defined by
"`∃ S in the witness family, the per-witness predicate holds`" is the *union* of per-witness γ-sets,
so when each per-witness γ-set is a subsingleton the whole incidence is bounded by the **number of
witnesses** — a `p`-INDEPENDENT combinatorial (subset) count.  This is exactly the structural reason
the over-determined incidence is a combinatorial count (the p-independence half of the orchestrator's
δ*-decoupling caveat #1), now machine-checked at the union-bound level.

## What is and is NOT proved here

- **PROVED:** `card_filter_exists_subsingleton_le` — if for every `S ∈ T` the set
  `{γ : Q S γ}` is a `Subsingleton`, then `#{γ ∈ univ : ∃ S ∈ T, Q S γ} ≤ #T`.  This is the
  union-of-singletons bound, uniform in the (finite) field — no `p`-dependence enters.
- **PROVED:** `card_filter_exists_subsingleton_le'` — the `Fintype`-indexed convenience form.
- **NOT proved (honest):** that the relevant `Q S` (membership of `u₀ + γ•u₁` in `RS[S]`) actually
  *is* a subsingleton for the deployed far witnesses (that is the in-tree
  `incidence_subsingleton_of_not_mem`, which needs the far hypothesis `b ∉ W` per witness), and that
  `#{far witnesses}` matches the closed-form `(n/2−1)²` / `n` (the B1 count law).  This file is the
  pure counting bridge; composing it with those gives the p-independent incidence bound.  It does
  NOT close CORE: the prize core is the *decay-vs-budget* threshold asymptotics (caveat #2), a
  separate question.

All results axiom-clean (`{propext, Classical.choice, Quot.sound}`).
-/

namespace ProximityGap.Frontier.OverdetIncidenceUnionCount

open Finset

/-- **The union-of-per-witness-singletons counting bound.**
Let `T : Finset σ` be a finite witness family and `Q : σ → F → Prop` a per-witness predicate over a
finite type `F`.  If for *every* witness `S ∈ T` the per-witness solution set `{γ : Q S γ}` is a
`Subsingleton` (at most one `γ`), then the number of `γ` satisfying *some* witness is at most the
number of witnesses:

`#{γ : ∃ S ∈ T, Q S γ} ≤ #T`.

This is the elementary union bound `|⋃_{S∈T} A_S| ≤ Σ_{S∈T} |A_S| ≤ #T` specialised to
singleton/empty `A_S`.  It is uniform in the finite type `F` — no field-size (`p`) dependence — which
is exactly why the over-determined far-line incidence is a `p`-independent combinatorial count. -/
theorem card_filter_exists_subsingleton_le
    {F : Type*} [Fintype F] [DecidableEq F] {σ : Type*} [DecidableEq σ]
    (T : Finset σ) (Q : σ → F → Prop) [DecidablePred (fun γ : F => ∃ S ∈ T, Q S γ)]
    [∀ S, DecidablePred (Q S)]
    (hsub : ∀ S ∈ T, {γ : F | Q S γ}.Subsingleton) :
    (Finset.univ.filter (fun γ : F => ∃ S ∈ T, Q S γ)).card ≤ T.card := by
  classical
  -- The γ-filter is contained in the bUnion over S of the per-witness γ-sets.
  have hsub_set :
      (Finset.univ.filter (fun γ : F => ∃ S ∈ T, Q S γ))
        ⊆ T.biUnion (fun S => Finset.univ.filter (fun γ : F => Q S γ)) := by
    intro γ hγ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ
    obtain ⟨S, hST, hQ⟩ := hγ
    refine Finset.mem_biUnion.mpr ⟨S, hST, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hQ
  calc
    (Finset.univ.filter (fun γ : F => ∃ S ∈ T, Q S γ)).card
        ≤ (T.biUnion (fun S => Finset.univ.filter (fun γ : F => Q S γ))).card :=
          Finset.card_le_card hsub_set
    _ ≤ ∑ S ∈ T, (Finset.univ.filter (fun γ : F => Q S γ)).card :=
          Finset.card_biUnion_le
    _ ≤ ∑ _S ∈ T, 1 :=
          Finset.sum_le_sum (fun S hS => by
            -- each per-witness γ-set has card ≤ 1 because it is a subsingleton.
            rw [Finset.card_le_one]
            intro a ha b hb
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
            exact hsub S hS ha hb)
    _ = T.card := by simp

/-- **Fintype-indexed convenience form.**  Same union bound with the witness family ranging over a
whole finite index type `σ` (so the witness count is `Fintype.card σ`). -/
theorem card_filter_exists_subsingleton_le'
    {F : Type*} [Fintype F] [DecidableEq F] {σ : Type*} [Fintype σ] [DecidableEq σ]
    (Q : σ → F → Prop) [DecidablePred (fun γ : F => ∃ S, Q S γ)]
    [∀ S, DecidablePred (Q S)]
    (hsub : ∀ S, {γ : F | Q S γ}.Subsingleton) :
    (Finset.univ.filter (fun γ : F => ∃ S, Q S γ)).card ≤ Fintype.card σ := by
  classical
  have := card_filter_exists_subsingleton_le (F := F) (Finset.univ : Finset σ) Q
    (by intro S _; exact hsub S)
  simpa using this

/-- **Specialisation to the affine-submodule (over-determination) per-witness predicate.**
Take the witness family `T` and let each witness `S ∈ T` carry a submodule `W S` of a fixed
`F`-vector space `V`, with deployed vectors `a S, b S : V`.  Define the per-witness predicate
`Q S γ := a S + γ • b S ∈ W S` (the "line through `a S` in direction `b S` lands in the witness
codeword space").  If every deployed witness is **far** (`b S ∉ W S`, the over-determined regime),
then by `incidence_subsingleton_of_not_mem` each per-witness γ-set is a subsingleton, and the union
count gives

`#{γ : ∃ S ∈ T, a S + γ•b S ∈ W S} ≤ #T`,

i.e. the far-line incidence is bounded by the witness count, **uniformly in the field** (`p`-indep).
This is the abstract content of "over-determined far incidence = combinatorial count". -/
theorem farIncidence_affine_le_witnesses
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {V : Type*} [AddCommGroup V] [Module F V]
    {σ : Type*} [DecidableEq σ]
    (T : Finset σ) (W : σ → Submodule F V) (a b : σ → V)
    [DecidablePred (fun γ : F => ∃ S ∈ T, a S + γ • b S ∈ W S)]
    [∀ S, DecidablePred (fun γ : F => a S + γ • b S ∈ W S)]
    (hfar : ∀ S ∈ T, b S ∉ W S) :
    (Finset.univ.filter (fun γ : F => ∃ S ∈ T, a S + γ • b S ∈ W S)).card ≤ T.card := by
  classical
  refine card_filter_exists_subsingleton_le (F := F) T
    (fun S γ => a S + γ • b S ∈ W S) ?_
  intro S hS
  -- the per-witness solution set is exactly the subsingleton from the proved dichotomy.
  have hsub :
      {γ : F | a S + γ • b S ∈ W S}.Subsingleton :=
    ProximityGap.Frontier.wf2NH.incidence_subsingleton_of_not_mem (a := a S) (b := b S)
      (hfar S hS)
  exact hsub

/-- **The exact in-tree `farIncidence` shape, bounded by the large-witness count.**
This matches the deployed `B1IncidenceBridge.farIncidence` filter *verbatim*: `γ` is bad iff there
exists a witness set `S` of size `≥ (1−δ)·n` and a codeword `w ∈ C` agreeing with the line
`u₀ + γ·u₁` on all of `S`.  We range the witness family over a finite index type `σ` carrying the
sets `wit : σ → Finset ι` and the size predicate `big : σ → Prop`.  Given the **per-witness pinning
hypothesis** — for each big witness `S`, at most one `γ` admits an agreeing codeword — the whole
far incidence is `≤ #(big witnesses)`, a combinatorial (subset) count uniform in `F`.

HONEST: the per-witness pinning hypothesis `hpin` is exactly the hard over-determination content
(`incidence_subsingleton_of_not_mem` once the agreement system is read as submodule membership); it
is kept an explicit input, NOT discharged here.  This lemma is the type-checked statement that *if*
each far witness pins `γ`, the open `WorstCaseFarIncidenceBounded` reduces to bounding the
(p-independent) big-witness count — the precise remaining obligation, not a fake closure. -/
theorem farIncidence_shape_le_bigWitnesses
    {F : Type*} [Fintype F] [DecidableEq F]
    {ι : Type*} {A : Type*} [SMul F A] [Add A]
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (C : Set (ι → A)) (u₀ u₁ : ι → A)
    (wit : σ → Finset ι) (big : σ → Prop) [DecidablePred big]
    (hcover : ∀ {S : Finset ι} {γ : F},
        (∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i) → (∃ j : σ, big j ∧ wit j = S))
    [DecidablePred (fun γ : F => ∃ S : Finset ι,
        (∃ j : σ, big j ∧ wit j = S) ∧ ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i)]
    [∀ j : σ, DecidablePred (fun γ : F => ∃ w ∈ C, ∀ i ∈ wit j, w i = u₀ i + γ • u₁ i)]
    (hpin : ∀ j : σ, big j →
        {γ : F | ∃ w ∈ C, ∀ i ∈ wit j, w i = u₀ i + γ • u₁ i}.Subsingleton) :
    (Finset.univ.filter (fun γ : F => ∃ S : Finset ι,
        (∃ j : σ, big j ∧ wit j = S) ∧ ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i)).card
      ≤ (Finset.univ.filter big).card := by
  classical
  set bigW : Finset σ := Finset.univ.filter big with hbigW
  -- the γ-filter is contained in the bUnion over big witnesses j of the per-witness γ-sets.
  set perWit : σ → Finset F :=
    fun j => Finset.univ.filter (fun γ : F => ∃ w ∈ C, ∀ i ∈ wit j, w i = u₀ i + γ • u₁ i)
    with hperWit
  calc
    (Finset.univ.filter (fun γ : F => ∃ S : Finset ι,
        (∃ j : σ, big j ∧ wit j = S) ∧ ∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i)).card
        ≤ (bigW.biUnion perWit).card := by
          apply Finset.card_le_card
          intro γ hγ
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hγ
          obtain ⟨S, ⟨j, hbj, hjS⟩, hagree⟩ := hγ
          refine Finset.mem_biUnion.mpr ⟨j, ?_, ?_⟩
          · simp only [hbigW, Finset.mem_filter, Finset.mem_univ, true_and]; exact hbj
          · simp only [hperWit, Finset.mem_filter, Finset.mem_univ, true_and]
            subst hjS; exact hagree
    _ ≤ ∑ j ∈ bigW, (perWit j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ bigW, 1 :=
          Finset.sum_le_sum (fun j hj => by
            simp only [hbigW, Finset.mem_filter, Finset.mem_univ, true_and] at hj
            rw [hperWit, Finset.card_le_one]
            intro a ha b hb
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
            exact hpin j hj ha hb)
    _ = bigW.card := by simp
    _ = (Finset.univ.filter big).card := by rw [hbigW]

end ProximityGap.Frontier.OverdetIncidenceUnionCount

/-! ## Axiom audit -/
#print axioms
  ProximityGap.Frontier.OverdetIncidenceUnionCount.card_filter_exists_subsingleton_le
#print axioms
  ProximityGap.Frontier.OverdetIncidenceUnionCount.card_filter_exists_subsingleton_le'
#print axioms
  ProximityGap.Frontier.OverdetIncidenceUnionCount.farIncidence_affine_le_witnesses
#print axioms
  ProximityGap.Frontier.OverdetIncidenceUnionCount.farIncidence_shape_le_bigWitnesses
