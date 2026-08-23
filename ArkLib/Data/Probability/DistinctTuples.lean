/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.Probability.Combinatorial
import ArkLib.Data.Probability.UniformPushforward

/-!
# Uniform distinct tuples and the subset-sampling bridge

The distribution bridge between the two natural ways to sample a size-`n` evaluation domain
from a finite alphabet `α`:

* an **injective `n`-tuple** (an embedding `Fin n ↪ α`, the "`n` distinct points in order"
  sample space used by the [AGL24] §3 analysis), sampled uniformly
  (`uniformDistinctTuples`); and
* a **size-`n` subset** (`Probability.SizeSubset α n`), sampled uniformly
  (`Probability.uniformSizeSubsetOfLe`, the sample space of the in-tree random Reed-Solomon
  front doors).

The bridge is the pushforward identity `map_uniformDistinctTuples_ofEmbedding`: the image map
`SizeSubset.ofEmbedding` (an injective tuple to its underlying set) is a **balanced surjection**
— every size-`n` subset has exactly `n!` ordered enumerations (`card_fiber_ofEmbedding`, via the
fiber equivalence `fiberEquivOfEmbedding` with the bijective enumerations of the subset) — so
the uniform tuple distribution pushes forward to the uniform subset distribution
(`ArkLib.Probability.map_uniformOfFintype_of_fiber_card_eq`).  `Pr`-transport corollaries
(`Pr_uniformSizeSubsetOfLe_eq_Pr_uniformDistinctTuples`, and the plain-function variant through
`uniformDistinctTuplesFun`) restate the bridge in the repo's probability notation.

This is wiring step (b) of the [AGL24] Theorem 1.1 campaign (issue #346): it moves the
random-RS bad-domain probability from the subset sample space onto the distinct-tuple sample
space where the reduced-intersection-matrix machinery lives.
-/

namespace ProbabilityTheory

open scoped ProbabilityTheory

/-- `Pr`-transport along a pushforward: sampling from `p.map g` and testing `P` is sampling
from `p` and testing `P ∘ g`. -/
lemma Pr_map {A B : Type} (p : PMF A) (g : A → B) (P : B → Prop) :
    Pr_{ let b ← p.map g }[P b] = Pr_{ let a ← p }[P (g a)] := by
  show ((p.map g).bind fun b => PMF.pure (P b)) True
      = (p.bind fun a => PMF.pure (P (g a))) True
  rw [PMF.bind_map]
  rfl

end ProbabilityTheory

namespace Probability

open scoped ProbabilityTheory

variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}

namespace SizeSubset

/-- The size-`n` subset cut out by an injective `n`-tuple: the image of the embedding. -/
def ofEmbedding (f : Fin n ↪ α) : SizeSubset α n :=
  ⟨Finset.univ.map f, by simp⟩

omit [Fintype α] [DecidableEq α] in
@[simp]
theorem coe_ofEmbedding (f : Fin n ↪ α) :
    ((ofEmbedding f : SizeSubset α n) : Finset α) = Finset.univ.map f := rfl

/-- The fiber of `ofEmbedding` over a size-`n` subset `s` is exactly the set of bijective
enumerations of `s`: an embedding with image `s` is the same data as an equivalence
`Fin n ≃ s`. -/
noncomputable def fiberEquivOfEmbedding (s : SizeSubset α n) :
    {f : Fin n ↪ α // ofEmbedding f = s} ≃ (Fin n ≃ ((s : Finset α) : Type _)) where
  toFun fp :=
    Equiv.ofBijective
      (fun i => ⟨fp.1 i, by
        have hval : (Finset.univ.map fp.1) = (s : Finset α) := congrArg Subtype.val fp.2
        rw [← hval]
        exact Finset.mem_map_of_mem _ (Finset.mem_univ i)⟩)
      (by
        refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, by simp⟩
        intro i j hij
        exact fp.1.injective (congrArg Subtype.val hij))
  invFun e :=
    ⟨e.toEmbedding.trans (Function.Embedding.subtype _), by
      apply Subtype.ext
      ext a
      simp only [coe_ofEmbedding, Finset.mem_map, Finset.mem_univ, true_and,
        Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
        Function.Embedding.coe_subtype]
      constructor
      · rintro ⟨i, rfl⟩
        exact (e i).2
      · intro ha
        exact ⟨e.symm ⟨a, ha⟩, by simp⟩⟩
  left_inv fp := by
    apply Subtype.ext
    apply DFunLike.ext
    intro i
    rfl
  right_inv e := by
    apply Equiv.ext
    intro i
    apply Subtype.ext
    rfl

/-- **Every size-`n` subset has exactly `n!` ordered enumerations**: the fiber of the image map
`ofEmbedding` over any `s : SizeSubset α n` has cardinality `n!`. -/
theorem card_fiber_ofEmbedding (s : SizeSubset α n) :
    (Finset.univ.filter (fun f : Fin n ↪ α => ofEmbedding f = s)).card = n.factorial := by
  rw [← Fintype.card_subtype, Fintype.card_congr (fiberEquivOfEmbedding s)]
  have hcard : Fintype.card (Fin n) = Fintype.card ((s : Finset α) : Type _) := by simp
  rw [Fintype.card_equiv (Fintype.equivOfCardEq hcard), Fintype.card_fin]

omit [Fintype α] [DecidableEq α] in
/-- The image map from injective `n`-tuples onto size-`n` subsets is surjective. -/
theorem ofEmbedding_surjective :
    Function.Surjective (ofEmbedding : (Fin n ↪ α) → SizeSubset α n) := by
  intro s
  have hcard : Fintype.card (Fin n) = Fintype.card ((s : Finset α) : Type _) := by simp
  obtain ⟨f, hf⟩ := (fiberEquivOfEmbedding s).symm (Fintype.equivOfCardEq hcard)
  exact ⟨f, hf⟩

end SizeSubset

/-- The uniform distribution on injective `n`-tuples (embeddings `Fin n ↪ α`) of a finite
alphabet, for `n ≤ |α|`.  This is the "`n` distinct evaluation points, in order" sample space
of the [AGL24] §3 analysis. -/
noncomputable def uniformDistinctTuples (α : Type*) [Fintype α] [DecidableEq α] (n : ℕ)
    (h : n ≤ Fintype.card α) : PMF (Fin n ↪ α) :=
  letI : Nonempty (Fin n ↪ α) :=
    Function.Embedding.nonempty_of_card_le (by simpa using h)
  PMF.uniformOfFintype (Fin n ↪ α)

/-- **The distinct-tuple ↔ subset distribution bridge.**  The image map `ofEmbedding` pushes
the uniform distinct-tuple distribution forward to the uniform size-`n` subset distribution:
it is a balanced surjection with all fibers of size `n!`. -/
theorem map_uniformDistinctTuples_ofEmbedding (h : n ≤ Fintype.card α) :
    (uniformDistinctTuples α n h).map SizeSubset.ofEmbedding = uniformSizeSubsetOfLe α n h := by
  letI : Nonempty (Fin n ↪ α) :=
    Function.Embedding.nonempty_of_card_le (by simpa using h)
  letI : Nonempty (SizeSubset α n) := SizeSubset.nonempty_of_le h
  have huni : uniformDistinctTuples α n h = PMF.uniformOfFintype (Fin n ↪ α) := rfl
  have hmap : (uniformDistinctTuples α n h).map SizeSubset.ofEmbedding
      = PMF.uniformOfFintype (SizeSubset α n) := by
    rw [huni]
    exact ArkLib.Probability.map_uniformOfFintype_of_fiber_card_eq
      SizeSubset.ofEmbedding SizeSubset.ofEmbedding_surjective
      (fun s₁ s₂ => by
        rw [SizeSubset.card_fiber_ofEmbedding, SizeSubset.card_fiber_ofEmbedding])
  ext s
  rw [hmap, PMF.uniformOfFintype_apply, uniformSizeSubsetOfLe_apply h s]
  congr 1
  rw [Fintype.card_eq_nat_card]
  exact_mod_cast SizeSubset.card

section PrTransport

variable {β : Type} [Fintype β] [DecidableEq β]

/-- `Pr`-form of the bridge: any event over a uniformly sampled size-`n` subset has the same
probability as the corresponding event over a uniformly sampled injective `n`-tuple, read
through the image map. -/
theorem Pr_uniformSizeSubsetOfLe_eq_Pr_uniformDistinctTuples
    {n : ℕ} (h : n ≤ Fintype.card β) (P : SizeSubset β n → Prop) :
    Pr_{ let L ← uniformSizeSubsetOfLe β n h }[P L]
      = Pr_{ let f ← uniformDistinctTuples β n h }[P (SizeSubset.ofEmbedding f)] := by
  rw [← map_uniformDistinctTuples_ofEmbedding h, ProbabilityTheory.Pr_map]

end PrTransport

/-- The uniform distinct-tuple distribution pushed onto plain functions `Fin n → α`: the
evaluation-point distribution `D : PMF (ι → F)` consumed by the [AGL24] Lemma 3.1 interface
(`AGL24.RIMFullRankFailureProbResidual`). -/
noncomputable def uniformDistinctTuplesFun (α : Type*) [Fintype α] [DecidableEq α] (n : ℕ)
    (h : n ≤ Fintype.card α) : PMF (Fin n → α) :=
  PMF.map (DFunLike.coe : (Fin n ↪ α) → (Fin n → α)) (uniformDistinctTuples α n h)

/-- `Pr`-transport from the function-valued distinct-tuple distribution back to embeddings. -/
theorem Pr_uniformDistinctTuplesFun_eq {β : Type} [Fintype β] [DecidableEq β]
    {n : ℕ} (h : n ≤ Fintype.card β) (Q : (Fin n → β) → Prop) :
    Pr_{ let x ← uniformDistinctTuplesFun β n h }[Q x]
      = Pr_{ let f ← uniformDistinctTuples β n h }[Q ⇑f] := by
  have h0 : uniformDistinctTuplesFun β n h
      = PMF.map (DFunLike.coe : (Fin n ↪ β) → (Fin n → β)) (uniformDistinctTuples β n h) := rfl
  rw [h0, ProbabilityTheory.Pr_map]

end Probability

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProbabilityTheory.Pr_map
#print axioms Probability.SizeSubset.ofEmbedding
#print axioms Probability.SizeSubset.fiberEquivOfEmbedding
#print axioms Probability.SizeSubset.card_fiber_ofEmbedding
#print axioms Probability.SizeSubset.ofEmbedding_surjective
#print axioms Probability.uniformDistinctTuples
#print axioms Probability.map_uniformDistinctTuples_ofEmbedding
#print axioms Probability.Pr_uniformSizeSubsetOfLe_eq_Pr_uniformDistinctTuples
#print axioms Probability.uniformDistinctTuplesFun
#print axioms Probability.Pr_uniformDistinctTuplesFun_eq
