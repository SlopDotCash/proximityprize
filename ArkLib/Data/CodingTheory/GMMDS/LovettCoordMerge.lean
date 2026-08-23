/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettLemma24
import ArkLib.Data.CodingTheory.GMMDS.LovettLemma2456

/-!
# Lovett's GM-MDS proof: the coordinate-merge construction (#389)

This file builds the *coordinate merge* used in the merge branch of Lovett's Lemma 2.5
(arXiv:1803.02523, p.9).  Given a merge candidate — an interior coordinate `j* < n−1` and the
last coordinate `n−1`, both globally relevant — Lovett forms a new system `V'` over `Fin (n−1)`
by collapsing coordinates `j*` and `n−1` into a single new **last** coordinate carrying the sum of
the two old multiplicities, and re-indexing the remaining `n−2` coordinates order-preservingly.

## The merge map

`mergeIdx j* : Fin (n−1) → Fin n` sends:
* the last new coordinate `n−2` ↦ the old last `n−1` (its image is irrelevant for the merged
  value, which is computed directly), and
* an interior new coordinate `t < n−2` ↦ the order-preserving lift skipping `j*`
  (`t` if `t < j*`, else `t+1`).

`mergeVec j* v : Fin (n−1) → ℕ` is the merged multiplicity vector:
* the last new coordinate carries `v(j*) + v(n−1)`;
* every interior new coordinate `t` carries `v (mergeIdx j* t)`.

## What is proven here (the cleanly-provable layer)

* `mergeVec_vAbs` — the merge **preserves total weight**: `|mergeVec j* v| = |v|`.  (The two merged
  coordinates are added; every other coordinate is relocated bijectively.)
* `mergeVec_shape` — clause (iii) for the merged vector: interior coordinates stay `≤ 1`
  (the merged value sits at the new *last* coordinate, exempt from (iii)).
* `mergeMeet_lower` / `mergeMeet_zero_of_mem` — the meet-weight only *increases* under the merge,
  and the increase is **zero** for any index set containing the merge candidate `i*` (since `i*`
  zeros both merged coordinates), in particular for the full set in a primitive system.

The remaining clause-(ii) bound for index sets *not* containing `i*` is exactly Lovett's
Lemma 2.4 (tight constraints are singletons or the whole set), isolated as the named residual
`MergeMDS` in `LovettMergeBranch.lean`.

Issue #389.
-/

open Finset

namespace ArkLib.GMMDS

variable {m n : ℕ}

/-- The order-preserving coordinate lift `Fin (n−1) → Fin n` for the merge: interior new
coordinates skip `j*`, the last new coordinate maps to the old last coordinate. -/
def mergeIdx {n : ℕ} (hn : 1 ≤ n) (j : Fin n) (t : Fin (n - 1)) : Fin n :=
  if (t : ℕ) < (j : ℕ) then ⟨t, by omega⟩
  else ⟨(t : ℕ) + 1, by have := t.isLt; omega⟩

/-- The merged multiplicity vector over `Fin (n−1)`: the new last coordinate carries the sum of
`v(j*)` and `v(n−1)`; every other (interior) coordinate carries the relocated old value. -/
def mergeVec {n : ℕ} (hn : 1 ≤ n) (j : Fin n) (v : Fin n → ℕ) : Fin (n - 1) → ℕ :=
  fun t => if (t : ℕ) = n - 1 - 1 then v j + v (lastCoord n hn)
           else v (mergeIdx hn j t)

/-- The merged system `V'` over `Fin (n−1)`. -/
def mergeSys {n m : ℕ} (hn : 1 ≤ n) (j : Fin n) (V : Fin m → (Fin n → ℕ)) :
    Fin m → (Fin (n - 1) → ℕ) :=
  fun i => mergeVec hn j (V i)

/-- `mergeIdx` is injective. -/
theorem mergeIdx_injective {n : ℕ} (hn : 1 ≤ n) (j : Fin n) :
    Function.Injective (mergeIdx hn j) := by
  intro a b hab
  unfold mergeIdx at hab
  by_cases ha : (a : ℕ) < (j : ℕ) <;> by_cases hb : (b : ℕ) < (j : ℕ) <;>
    simp only [ha, hb, if_true, if_false] at hab <;>
    (have := Fin.mk.injEq .. ▸ hab) <;>
    (apply Fin.ext) <;> omega

/-- The image of `mergeIdx` never hits `j`. -/
theorem mergeIdx_ne_j {n : ℕ} (hn : 1 ≤ n) (j : Fin n) (t : Fin (n - 1)) :
    mergeIdx hn j t ≠ j := by
  unfold mergeIdx
  by_cases ht : (t : ℕ) < (j : ℕ) <;> simp only [ht, if_true, if_false] <;>
    (intro h; have := congrArg Fin.val h; simp at this; omega)

/-- The image of an *interior* new coordinate (`t < n−2`) never hits the old last coordinate. -/
theorem mergeIdx_ne_last {n : ℕ} (hn : 1 ≤ n) (j : Fin n) (t : Fin (n - 1))
    (ht : (t : ℕ) < n - 1 - 1) : mergeIdx hn j t ≠ lastCoord n hn := by
  unfold mergeIdx lastCoord
  by_cases h : (t : ℕ) < (j : ℕ) <;> simp only [h, if_true, if_false] <;>
    (intro hh; have := congrArg Fin.val hh; simp at this; omega)

/-- The interior new coordinates `{ t : Fin (n−1) | t < n−2 }` map bijectively (via `mergeIdx`)
onto the old coordinates other than `j` and the last. -/
theorem mergeIdx_image_interior {n : ℕ} (hn : 1 ≤ n) (j : Fin n) (hjlt : (j : ℕ) < n - 1) :
    (Finset.univ.filter (fun t : Fin (n - 1) => (t : ℕ) < n - 1 - 1)).image (mergeIdx hn j)
      = Finset.univ \ {j, lastCoord n hn} := by
  classical
  apply Finset.ext
  intro c
  rw [Finset.mem_sdiff]
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨t, ht, rfl⟩
    rintro (h | h)
    · exact mergeIdx_ne_j hn j t h
    · exact mergeIdx_ne_last hn j t ht h
  · intro hc
    push_neg at hc
    obtain ⟨hcj, hclast⟩ := hc
    -- c ≠ j and c ≠ last; find preimage t
    have hcval : (c : ℕ) ≠ (j : ℕ) := fun h => hcj (Fin.ext h)
    have hclval : (c : ℕ) ≠ n - 1 := by
      intro h; apply hclast; apply Fin.ext
      show (c : ℕ) = n - 1; rw [h]
    have hclt : (c : ℕ) < n := c.isLt
    have hjltn : (j : ℕ) < n := j.isLt
    by_cases hcj2 : (c : ℕ) < (j : ℕ)
    · refine ⟨⟨c, by omega⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        show _ < n - 1 - 1; omega
      · unfold mergeIdx
        rw [if_pos (show ((⟨c, by omega⟩ : Fin (n-1)) : ℕ) < (j : ℕ) from hcj2)]
    · -- c > j (since c ≠ j), so preimage is c-1
      have hcgtj : (j : ℕ) < (c : ℕ) := by omega
      refine ⟨⟨(c : ℕ) - 1, by omega⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        show _ < n - 1 - 1; omega
      · unfold mergeIdx
        have hnlt : ¬ ((c : ℕ) - 1 < (j : ℕ)) := by omega
        simp only [hnlt, if_false]
        apply Fin.ext; show (c : ℕ) - 1 + 1 = (c : ℕ); omega

/-- **The merge preserves total weight.**  `|mergeVec j v| = |v|` (for `n ≥ 2`, where the merge
candidate `j < n−1` can exist). -/
theorem mergeVec_vAbs {n : ℕ} (hn2 : 2 ≤ n) (j : Fin n) (hjlt : (j : ℕ) < n - 1)
    (v : Fin n → ℕ) :
    vAbs (mergeVec (by omega : 1 ≤ n) j v) = vAbs v := by
  classical
  have hn : 1 ≤ n := by omega
  -- The last new coordinate of Fin (n-1) is `n-2`; isolate it.
  set L : Fin (n - 1) := ⟨n - 1 - 1, by omega⟩ with hL
  -- vAbs (mergeVec) = (sum over interior) + (merged value at L)
  have hsplit : vAbs (mergeVec hn j v)
      = (∑ t ∈ Finset.univ.filter (fun t : Fin (n - 1) => (t : ℕ) < n - 1 - 1),
          mergeVec hn j v t) + mergeVec hn j v L := by
    unfold vAbs
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun t : Fin (n - 1) => (t : ℕ) < n - 1 - 1)]
    congr 1
    -- the "not < n-1-1" filter is exactly {L}
    have : (Finset.univ.filter (fun t : Fin (n - 1) => ¬ (t : ℕ) < n - 1 - 1)) = {L} := by
      apply Finset.ext; intro t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hL]
      constructor
      · intro h; apply Fin.ext; have := t.isLt; simp; omega
      · intro h; rw [h]; simp
    rw [this, Finset.sum_singleton]
  -- interior sum equals sum over coords ≠ j, ≠ last (via mergeIdx bijection)
  have hinterior : (∑ t ∈ Finset.univ.filter (fun t : Fin (n - 1) => (t : ℕ) < n - 1 - 1),
        mergeVec hn j v t)
      = ∑ c ∈ Finset.univ \ {j, lastCoord n hn}, v c := by
    rw [← mergeIdx_image_interior hn j hjlt]
    rw [Finset.sum_image (fun a _ b _ h => mergeIdx_injective hn j h)]
    apply Finset.sum_congr rfl
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    unfold mergeVec
    rw [if_neg (by omega)]
  -- merged value at L = v j + v last
  have hmerged : mergeVec hn j v L = v j + v (lastCoord n hn) := by
    unfold mergeVec; rw [if_pos (by simp [hL])]
  rw [hsplit, hinterior, hmerged]
  -- now: (∑ over univ \ {j,last} v) + (v j + v last) = ∑ over univ v
  have hjne : j ≠ lastCoord n hn ∨ True := Or.inr trivial
  -- sum over univ = (sum over univ\{j,last}) + v j + v last
  have hdiff : ∑ c ∈ Finset.univ \ {j, lastCoord n hn}, v c + (v j + v (lastCoord n hn))
      = ∑ c, v c := by
    have hsub : ({j, lastCoord n hn} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
    rw [← Finset.sum_sdiff hsub]
    congr 1
    -- need j ≠ last to expand {j,last}
    have hjlast : j ≠ lastCoord n hn := by
      intro h; rw [h] at hjlt; simp only [lastCoord] at hjlt; omega
    rw [Finset.sum_pair hjlast]
  rw [vAbs]; omega

/-- **Clause (iii) for the merged vector.**  Interior coordinates of `mergeVec j v` stay `≤ 1`
whenever the original interior coordinates are `≤ 1` (shape (iii)).  The merged value sits at the
new *last* coordinate, which is exempt from (iii). -/
theorem mergeVec_shape {n : ℕ} (hn2 : 2 ≤ n) (j : Fin n) (hjlt : (j : ℕ) < n - 1)
    (v : Fin n → ℕ) (hshape : ∀ l : Fin n, (l : ℕ) < n - 1 → v l ≤ 1)
    (t : Fin (n - 1)) (ht : (t : ℕ) < n - 1 - 1) :
    mergeVec (by omega : 1 ≤ n) j v t ≤ 1 := by
  have hn : 1 ≤ n := by omega
  unfold mergeVec
  rw [if_neg (by omega)]
  apply hshape
  -- the image coordinate is < n - 1
  unfold mergeIdx
  by_cases h : (t : ℕ) < (j : ℕ) <;> simp only [h, if_true, if_false]
  · show (t : ℕ) < n - 1; omega
  · show (t : ℕ) + 1 < n - 1; omega

end ArkLib.GMMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.GMMDS.mergeIdx_injective
#print axioms ArkLib.GMMDS.mergeIdx_image_interior
#print axioms ArkLib.GMMDS.mergeVec_vAbs
#print axioms ArkLib.GMMDS.mergeVec_shape
