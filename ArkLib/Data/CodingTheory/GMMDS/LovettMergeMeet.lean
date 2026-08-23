/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettCoordMerge

/-!
# Lovett's GM-MDS proof: the merge-meet monotonicity bricks (#389)

The clause-(ii) verification for the merged system `mergeSys j V` (over `Fin (n−1)`) in the merge
branch of Lovett's Lemma 2.5 (arXiv:1803.02523, p.9) hinges on understanding how the
coordinate-wise meet `⋀_{i∈I}` behaves under the coordinate merge.  This file isolates the two
*unconditionally true* facts about that meet, which are the combinatorial heart of the clause-(ii)
inequality:

* `mergeMeet_interior` — at an **interior** new coordinate `t < n−2`, the merged meet equals the
  relocated original meet: `(⋀_I mergeVec v_i) t = (⋀_I v_i) (mergeIdx t)`.  (The merge is a plain
  reindexing away from the merged coordinate.)
* `mergeMeet_last_ge` — at the **new last** coordinate `L = n−2`, the merged meet is *at least* the
  sum of the two old meets it absorbs: `(⋀_I mergeVec v_i) L ≥ (⋀_I v_i) j + (⋀_I v_i) last`.  This
  is the (super-additive) `inf(aᵢ + bᵢ) ≥ inf aᵢ + inf bᵢ` inequality at the merged coordinate.
* `mergeMeet_last_zero_of_mem` — if some `i* ∈ I` has `v_{i*}(j) = v_{i*}(last) = 0` (the merge
  candidate), the new-last merged-meet value is exactly `0`.  This is the case that makes the merge
  *lossless* on the meet: the `+1` produced by merging two coordinates is fully absorbed, so
  clause (ii) is preserved for any index set containing the merge candidate — in particular for the
  full set `I = univ` in a primitive system.

These three facts pin the only obstruction to `IsVStar (mergeSys j V) k` clause (ii) for index
sets `I` with `1 < |I| < m` **not** containing the merge candidate: there the merged meet can
strictly exceed the original by `1`, and the inequality survives iff `I` was *non-tight*
(`not_tightConstraint_le`).  That `1 < |I| < m` tight sets cannot occur is exactly Lovett's
Lemma 2.4, which (as the PDF proof shows) is **not** a standalone combinatorial fact: it is proven
only within the minimal-counterexample by replacing the `I`-block with its meet (a system of the
*same* induction measure `d` but fewer vectors) and transferring independence via the equal-span /
equal-cardinality counting lemma.  See the report attached to this brick for the precise
architectural prerequisite (an `m`-aware induction hypothesis, absent from the current `(n,k,d)`
frame).

Issue #389.
-/

open Finset

namespace ArkLib.GMMDS

variable {m n : ℕ}

/-- At an **interior** new coordinate `t < n−2`, the merged meet is the relocated original meet. -/
theorem mergeMeet_interior {n m : ℕ} (hn : 1 ≤ n) (j : Fin n)
    (V : Fin m → (Fin n → ℕ)) (I : Finset (Fin m)) (hI : I.Nonempty)
    (t : Fin (n - 1)) (ht : (t : ℕ) < n - 1 - 1) :
    vMeet (mergeSys hn j V) I hI t = vMeet V I hI (mergeIdx hn j t) := by
  unfold vMeet
  have hfun : (fun i => mergeSys hn j V i t) = (fun i => V i (mergeIdx hn j t)) := by
    funext i
    show mergeSys hn j V i t = V i (mergeIdx hn j t)
    unfold mergeSys mergeVec
    rw [if_neg (by omega)]
  rw [hfun]

/-- At the **new last** coordinate `L = n−2`, every merged value is `v_i(j) + v_i(last)`. -/
theorem mergeMeet_last_eq {n m : ℕ} (hn : 1 ≤ n) (j : Fin n)
    (V : Fin m → (Fin n → ℕ)) (I : Finset (Fin m)) (hI : I.Nonempty)
    (L : Fin (n - 1)) (hL : (L : ℕ) = n - 1 - 1) :
    vMeet (mergeSys hn j V) I hI L
      = I.inf' hI (fun i => V i j + V i (lastCoord n hn)) := by
  unfold vMeet
  have hfun : (fun i => mergeSys hn j V i L) = (fun i => V i j + V i (lastCoord n hn)) := by
    funext i
    show mergeSys hn j V i L = V i j + V i (lastCoord n hn)
    unfold mergeSys mergeVec
    rw [if_pos hL]
  rw [hfun]

/-- **Super-additivity of the meet at the merged coordinate.**  At the new last coordinate the
merged meet is *at least* the sum of the two old meets it absorbs:
`(⋀_I mergeVec v_i) L ≥ (⋀_I v_i) j + (⋀_I v_i) last`. -/
theorem mergeMeet_last_ge {n m : ℕ} (hn : 1 ≤ n) (j : Fin n)
    (V : Fin m → (Fin n → ℕ)) (I : Finset (Fin m)) (hI : I.Nonempty)
    (L : Fin (n - 1)) (hL : (L : ℕ) = n - 1 - 1) :
    vMeet V I hI j + vMeet V I hI (lastCoord n hn) ≤ vMeet (mergeSys hn j V) I hI L := by
  rw [mergeMeet_last_eq hn j V I hI L hL]
  unfold vMeet
  -- inf of sums ≥ sum of infs
  refine Finset.le_inf' hI _ (fun i hi => ?_)
  exact Nat.add_le_add (Finset.inf'_le _ hi) (Finset.inf'_le _ hi)

/-- **The merge is lossless on the meet when the candidate is present.**  If some `i* ∈ I` has
`v_{i*}(j) = 0` and `v_{i*}(last) = 0` (the merge candidate), the new-last merged-meet value is
exactly `0`.  In particular, for the full set `I = univ` in a primitive system the `+1` from
merging is fully absorbed and clause (ii) is preserved at `I = univ`. -/
theorem mergeMeet_last_zero_of_mem {n m : ℕ} (hn : 1 ≤ n) (j : Fin n)
    (V : Fin m → (Fin n → ℕ)) (I : Finset (Fin m)) (hI : I.Nonempty)
    (L : Fin (n - 1)) (hL : (L : ℕ) = n - 1 - 1)
    {i₀ : Fin m} (hi₀ : i₀ ∈ I) (hj0 : V i₀ j = 0) (hlast0 : V i₀ (lastCoord n hn) = 0) :
    vMeet (mergeSys hn j V) I hI L = 0 := by
  rw [mergeMeet_last_eq hn j V I hI L hL]
  refine Nat.le_zero.mp ?_
  have := Finset.inf'_le (fun i => V i j + V i (lastCoord n hn)) hi₀
  rw [hj0, hlast0] at this
  simpa using this

/-- **Interior-meet weight equals the relocated original meet weight.**  The sum of the merged-meet
over the interior new coordinates equals the sum of the original meet over the old coordinates
other than `j` and `last`. -/
theorem mergeMeet_interior_sum {n m : ℕ} (hn : 1 ≤ n) (j : Fin n) (hjlt : (j : ℕ) < n - 1)
    (V : Fin m → (Fin n → ℕ)) (I : Finset (Fin m)) (hI : I.Nonempty) :
    (∑ t ∈ Finset.univ.filter (fun t : Fin (n - 1) => (t : ℕ) < n - 1 - 1),
        vMeet (mergeSys hn j V) I hI t)
      = ∑ c ∈ Finset.univ \ {j, lastCoord n hn}, vMeet V I hI c := by
  classical
  rw [← mergeIdx_image_interior hn j hjlt]
  rw [Finset.sum_image (fun a _ b _ h => mergeIdx_injective hn j h)]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
  exact mergeMeet_interior hn j V I hI t ht

/-- The new-last coordinate `L = n−2` of `Fin (n−1)`, as a `Finset` complement of the interior. -/
private theorem not_interior_eq_last {n : ℕ} (hn2 : 2 ≤ n)
    (L : Fin (n - 1)) (hL : (L : ℕ) = n - 1 - 1) :
    (Finset.univ.filter (fun t : Fin (n - 1) => ¬ (t : ℕ) < n - 1 - 1)) = {L} := by
  apply Finset.ext; intro t
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h; apply Fin.ext; have := t.isLt; rw [hL]; omega
  · intro h; rw [h, hL]; simp

/-- **Splitting the merged-meet weight into interior + new-last.** -/
theorem mergeMeet_vAbs_split {n m : ℕ} (hn2 : 2 ≤ n) (j : Fin n) (hjlt : (j : ℕ) < n - 1)
    (V : Fin m → (Fin n → ℕ)) (I : Finset (Fin m)) (hI : I.Nonempty) :
    vAbs (vMeet (mergeSys (by omega : 1 ≤ n) j V) I hI)
      = (∑ c ∈ Finset.univ \ {j, lastCoord n (by omega)}, vMeet V I hI c)
        + vMeet (mergeSys (by omega : 1 ≤ n) j V) I hI ⟨n - 1 - 1, by omega⟩ := by
  classical
  have hn : 1 ≤ n := by omega
  set L : Fin (n - 1) := ⟨n - 1 - 1, by omega⟩ with hLdef
  have hLval : (L : ℕ) = n - 1 - 1 := rfl
  unfold vAbs
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun t : Fin (n - 1) => (t : ℕ) < n - 1 - 1)]
  rw [not_interior_eq_last hn2 L hLval, Finset.sum_singleton]
  rw [mergeMeet_interior_sum hn j hjlt V I hI]

/-- **The merge does not decrease the meet weight.**  `|⋀_I v_i| ≤ |⋀_I mergeVec v_i|`: interior
coordinates are relocated bijectively (equal contribution), and the merged coordinate is
super-additive (`mergeMeet_last_ge`). -/
theorem vAbs_vMeet_le_mergeMeet {n m : ℕ} (hn2 : 2 ≤ n) (j : Fin n) (hjlt : (j : ℕ) < n - 1)
    (V : Fin m → (Fin n → ℕ)) (I : Finset (Fin m)) (hI : I.Nonempty) :
    vAbs (vMeet V I hI) ≤ vAbs (vMeet (mergeSys (by omega : 1 ≤ n) j V) I hI) := by
  classical
  have hn : 1 ≤ n := by omega
  rw [mergeMeet_vAbs_split hn2 j hjlt V I hI]
  -- |⋀ V| = (sum over univ\{j,last}) + (⋀ V j + ⋀ V last)
  have hsplitV : vAbs (vMeet V I hI)
      = (∑ c ∈ Finset.univ \ {j, lastCoord n hn}, vMeet V I hI c)
        + (vMeet V I hI j + vMeet V I hI (lastCoord n hn)) := by
    unfold vAbs
    have hsub : ({j, lastCoord n hn} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
    have hjlast : j ≠ lastCoord n hn := by
      intro h; rw [h] at hjlt; simp only [lastCoord] at hjlt; omega
    rw [← Finset.sum_sdiff hsub, Finset.sum_pair hjlast]
  rw [hsplitV]
  have hge := mergeMeet_last_ge (by omega : 1 ≤ n) j V I hI ⟨n - 1 - 1, by omega⟩ rfl
  omega

/-- **The merge is lossless on the meet weight when the candidate is in `I`.**  If some `i* ∈ I`
zeros both merged coordinates (`v_{i*}(j) = v_{i*}(last) = 0`), then `|⋀_I mergeVec v_i| = |⋀_I v_i|`
— the merge adds nothing to the meet weight. -/
theorem mergeMeet_vAbs_eq_of_mem {n m : ℕ} (hn2 : 2 ≤ n) (j : Fin n) (hjlt : (j : ℕ) < n - 1)
    (V : Fin m → (Fin n → ℕ)) (I : Finset (Fin m)) (hI : I.Nonempty)
    {i₀ : Fin m} (hi₀ : i₀ ∈ I) (hj0 : V i₀ j = 0)
    (hlast0 : V i₀ (lastCoord n (by omega)) = 0) :
    vAbs (vMeet (mergeSys (by omega : 1 ≤ n) j V) I hI) = vAbs (vMeet V I hI) := by
  classical
  have hn : 1 ≤ n := by omega
  rw [mergeMeet_vAbs_split hn2 j hjlt V I hI]
  -- new-last meet is 0
  have hlast := mergeMeet_last_zero_of_mem (by omega : 1 ≤ n) j V I hI ⟨n - 1 - 1, by omega⟩
    rfl hi₀ hj0 hlast0
  -- the j and last original meets are also 0 (i₀ zeros them ⟹ inf is 0)
  have hmeetj : vMeet V I hI j = 0 := by
    unfold vMeet; refine Nat.le_zero.mp ?_
    have := Finset.inf'_le (fun i => V i j) hi₀; rw [hj0] at this; simpa using this
  have hmeetlast : vMeet V I hI (lastCoord n hn) = 0 := by
    unfold vMeet; refine Nat.le_zero.mp ?_
    have := Finset.inf'_le (fun i => V i (lastCoord n hn)) hi₀
    rw [hlast0] at this; simpa using this
  rw [hlast, add_zero]
  -- |⋀ V| = (sum over univ\{j,last}) + (⋀ V j + ⋀ V last) = sum, since both are 0
  unfold vAbs
  have hsub : ({j, lastCoord n hn} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
  have hjlast : j ≠ lastCoord n hn := by
    intro h; rw [h] at hjlt; simp only [lastCoord] at hjlt; omega
  rw [← Finset.sum_sdiff hsub, Finset.sum_pair hjlast, hmeetj, hmeetlast, add_zero, add_zero]

/-- **Clause (ii) for the merged system at `I = univ` in a primitive system.**  Since the meet
weight is unchanged (the full meet zeros every coordinate, primitivity) and the per-vector weights
are preserved (`mergeVec_vAbs`), the MDS inequality for the full set transports verbatim. -/
theorem mergeSys_mds_univ {n m : ℕ} (hn2 : 2 ≤ n) (j : Fin n) (hjlt : (j : ℕ) < n - 1)
    {V : Fin m → (Fin n → ℕ)} {k : ℕ} (hV : IsVStar V k)
    (hne : (Finset.univ : Finset (Fin m)).Nonempty)
    {i₀ : Fin m} (hj0 : V i₀ j = 0) (hlast0 : V i₀ (lastCoord n (by omega)) = 0) :
    (∑ i, (k - vAbs (mergeSys (by omega : 1 ≤ n) j V i)))
        + vAbs (vMeet (mergeSys (by omega : 1 ≤ n) j V) Finset.univ hne) ≤ k := by
  classical
  have hn : 1 ≤ n := by omega
  -- per-vector weights preserved
  have hwt : ∀ i, vAbs (mergeSys hn j V i) = vAbs (V i) := by
    intro i; rw [mergeSys, mergeVec_vAbs hn2 j hjlt]
  rw [Finset.sum_congr rfl (fun i _ => by rw [hwt i])]
  -- meet weight unchanged (candidate i₀ ∈ univ)
  rw [mergeMeet_vAbs_eq_of_mem hn2 j hjlt V Finset.univ hne (Finset.mem_univ i₀) hj0 hlast0]
  exact hV.mds Finset.univ hne

end ArkLib.GMMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.GMMDS.mergeMeet_interior
#print axioms ArkLib.GMMDS.mergeMeet_last_ge
#print axioms ArkLib.GMMDS.mergeMeet_last_zero_of_mem
#print axioms ArkLib.GMMDS.mergeMeet_interior_sum
#print axioms ArkLib.GMMDS.vAbs_vMeet_le_mergeMeet
#print axioms ArkLib.GMMDS.mergeMeet_vAbs_eq_of_mem
#print axioms ArkLib.GMMDS.mergeSys_mds_univ
