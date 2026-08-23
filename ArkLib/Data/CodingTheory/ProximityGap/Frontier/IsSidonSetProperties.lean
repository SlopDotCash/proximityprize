/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.REnergySwapFloorSidonIff

/-!
# Structural properties of plain Sidon (`B_2`) sets (#444, #389, §0)

Reusable closure properties of `SubgroupGaussSumMoment.IsSidonSet` (the plain `B_2` condition
introduced for the swap-floor sharpness, `REnergySwapFloorSidonSharp`).  These are the elementary
hereditary facts the depth-`ℓ` `B_h`-Sidon ladder (§0) leans on:

* **`IsSidonSet.subset`** — a subset of a Sidon set is Sidon (Sidon is hereditary).
* **`isSidonSet_empty`**, **`isSidonSet_singleton`** — the trivial base cases.
* **`IsSidonSet.translate`** — Sidon is invariant under translation `G ↦ G + t` (the coincidence
  relation `a+b = c+d` is translation-equivariant).
* **`IsSidonSet.scale`** — Sidon is invariant under nonzero dilation `G ↦ tG`.
* **`IsSidonSet.affine`** — Sidon is invariant under affine maps `x ↦ u + t*x`, `t ≠ 0`.
* **`isSidonSet_map_affine_iff`** — affine images preserve and reflect Sidon exactly.

Axiom-clean (`propext, Classical.choice, Quot.sound`).  No CORE closure, no char-p transfer, no
capacity / beyond-Johnson / growth-law claim.  Issues #444, #389.
-/

open Finset

namespace ArkLib.ProximityGap.SubgroupGaussSumMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Sidon is hereditary:** a subset of a Sidon set is Sidon. -/
theorem IsSidonSet.subset {G H : Finset F} (hG : IsSidonSet G) (hHG : H ⊆ G) :
    IsSidonSet H := by
  intro a ha b hb c hc d hd hsum
  exact hG a (hHG ha) b (hHG hb) c (hHG hc) d (hHG hd) hsum

/-- The empty set is Sidon (vacuously). -/
theorem isSidonSet_empty : IsSidonSet (∅ : Finset F) := by
  intro a ha; exact absurd ha (Finset.notMem_empty a)

/-- A singleton is Sidon. -/
theorem isSidonSet_singleton (x : F) : IsSidonSet ({x} : Finset F) := by
  intro a ha b hb c hc d hd _
  rw [Finset.mem_singleton] at ha hb hc hd
  subst ha hb hc hd
  exact Or.inl ⟨rfl, rfl⟩

/-- **Translation invariance:** if `G` is Sidon then so is its translate `G.map (+t)`.
The coincidence relation `a + b = c + d` is preserved under shifting each element by `t`
(both sides gain `2t`). -/
theorem IsSidonSet.translate {G : Finset F} (hG : IsSidonSet G) (t : F) :
    IsSidonSet (G.map (addLeftEmbedding t)) := by
  intro a ha b hb c hc d hd hsum
  simp only [Finset.mem_map, addLeftEmbedding_apply] at ha hb hc hd
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  obtain ⟨c', hc', rfl⟩ := hc
  obtain ⟨d', hd', rfl⟩ := hd
  -- (t+a')+(t+b') = (t+c')+(t+d')  ⟹  a'+b' = c'+d'
  have hsum' : a' + b' = c' + d' := by
    have : t + a' + (t + b') = t + c' + (t + d') := hsum
    linear_combination this
  rcases hG a' ha' b' hb' c' hc' d' hd' hsum' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by rw [h1], by rw [h2]⟩
  · exact Or.inr ⟨by rw [h1], by rw [h2]⟩

/-- The embedding `x ↦ t * x` for a nonzero scalar `t`. -/
def mulLeftEmbeddingOfNe (t : F) (ht : t ≠ 0) : F ↪ F where
  toFun := fun x => t * x
  inj' := by
    intro x y hxy
    exact mul_left_cancel₀ ht hxy

/-- **Nonzero-dilation invariance:** if `G` is Sidon then so is its nonzero scalar multiple.
The coincidence relation `a + b = c + d` is preserved under multiplying each element by `t ≠ 0`,
and cancellation by `t` recovers the original Sidon coincidence. -/
theorem IsSidonSet.scale {G : Finset F} (hG : IsSidonSet G) {t : F} (ht : t ≠ 0) :
    IsSidonSet (G.map (mulLeftEmbeddingOfNe t ht)) := by
  intro a ha b hb c hc d hd hsum
  simp only [Finset.mem_map] at ha hb hc hd
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  obtain ⟨c', hc', rfl⟩ := hc
  obtain ⟨d', hd', rfl⟩ := hd
  change t * a' + t * b' = t * c' + t * d' at hsum
  have hsum' : a' + b' = c' + d' := by
    apply mul_left_cancel₀ ht
    calc
      t * (a' + b') = t * a' + t * b' := by ring
      _ = t * c' + t * d' := hsum
      _ = t * (c' + d') := by ring
  rcases hG a' ha' b' hb' c' hc' d' hd' hsum' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by rw [h1], by rw [h2]⟩
  · exact Or.inr ⟨by rw [h1], by rw [h2]⟩

/-- The embedding `x ↦ u + t * x` for a nonzero scalar `t`. -/
def affineEmbeddingOfNe (u t : F) (ht : t ≠ 0) : F ↪ F where
  toFun := fun x => u + t * x
  inj' := by
    intro x y hxy
    apply mul_left_cancel₀ ht
    exact add_left_cancel hxy

/-- **Affine invariance:** if `G` is Sidon then so is its affine image `u + tG`, for
`t ≠ 0`.  This packages the translation and dilation closures into the exact affine closure
needed by the `B₂`/Sidon structural toolkit; it is purely algebraic and makes no CORE or
capacity claim. -/
theorem IsSidonSet.affine {G : Finset F} (hG : IsSidonSet G) (u : F) {t : F} (ht : t ≠ 0) :
    IsSidonSet (G.map (affineEmbeddingOfNe u t ht)) := by
  intro a ha b hb c hc d hd hsum
  simp only [Finset.mem_map] at ha hb hc hd
  obtain ⟨a', ha', rfl⟩ := ha
  obtain ⟨b', hb', rfl⟩ := hb
  obtain ⟨c', hc', rfl⟩ := hc
  obtain ⟨d', hd', rfl⟩ := hd
  change u + t * a' + (u + t * b') = u + t * c' + (u + t * d') at hsum
  have hsum' : a' + b' = c' + d' := by
    apply mul_left_cancel₀ ht
    calc
      t * (a' + b') = (u + t * a' + (u + t * b')) - (u + u) := by ring
      _ = (u + t * c' + (u + t * d')) - (u + u) := by rw [hsum]
      _ = t * (c' + d') := by ring
  rcases hG a' ha' b' hb' c' hc' d' hd' hsum' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨by rw [h1], by rw [h2]⟩
  · exact Or.inr ⟨by rw [h1], by rw [h2]⟩

/-- **Affine images preserve and reflect Sidon exactly.**  A nonzero affine map is injective and
transports the equation `a+b=c+d` bijectively up to the same additive/scalar normalization, so
passing to `u + tG` loses no `B₂`/Sidon information. -/
theorem isSidonSet_map_affine_iff (G : Finset F) (u : F) {t : F} (ht : t ≠ 0) :
    IsSidonSet (G.map (affineEmbeddingOfNe u t ht)) ↔ IsSidonSet G := by
  constructor
  · intro hImage a ha b hb c hc d hd hsum
    have ha' : u + t * a ∈ G.map (affineEmbeddingOfNe u t ht) := by
      exact Finset.mem_map.mpr ⟨a, ha, rfl⟩
    have hb' : u + t * b ∈ G.map (affineEmbeddingOfNe u t ht) := by
      exact Finset.mem_map.mpr ⟨b, hb, rfl⟩
    have hc' : u + t * c ∈ G.map (affineEmbeddingOfNe u t ht) := by
      exact Finset.mem_map.mpr ⟨c, hc, rfl⟩
    have hd' : u + t * d ∈ G.map (affineEmbeddingOfNe u t ht) := by
      exact Finset.mem_map.mpr ⟨d, hd, rfl⟩
    have hsum' : u + t * a + (u + t * b) = u + t * c + (u + t * d) := by
      calc
        u + t * a + (u + t * b) = u + u + t * (a + b) := by ring
        _ = u + u + t * (c + d) := by rw [hsum]
        _ = u + t * c + (u + t * d) := by ring
    rcases hImage (u + t * a) ha' (u + t * b) hb' (u + t * c) hc' (u + t * d) hd' hsum' with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨mul_left_cancel₀ ht (add_left_cancel h1),
          mul_left_cancel₀ ht (add_left_cancel h2)⟩
    · exact Or.inr ⟨mul_left_cancel₀ ht (add_left_cancel h1),
          mul_left_cancel₀ ht (add_left_cancel h2)⟩
  · intro hG
    exact hG.affine u ht

end ArkLib.ProximityGap.SubgroupGaussSumMoment

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only (no sorryAx).
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.IsSidonSet.subset
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.IsSidonSet.translate
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.IsSidonSet.scale
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.IsSidonSet.affine
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMoment.isSidonSet_map_affine_iff
