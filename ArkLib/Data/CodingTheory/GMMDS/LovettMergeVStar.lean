/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettMergeMeet
import ArkLib.Data.CodingTheory.GMMDS.LovettMergeBranch
import ArkLib.Data.CodingTheory.GMMDS.LovettBlockDecomp

/-!
# Lovett's GM-MDS proof: the merged system is again `V*(k)` (#389)

This file assembles **clause (ii)** of `IsVStar` for the coordinate-merged system `mergeSys j V`
(over `Fin (n−1)`), completing the proof that `mergeSys j V` is a `V*(k)` system whenever `V` is
(in the merge branch of Lovett's Lemma 2.5, arXiv:1803.02523, p.9).

`mergeSys_weight_shape` (in `LovettMergeBranch`) already gives clauses (i) and (iii), and
`mergeSys_mds_univ` (in `LovettMergeMeet`) gives clause (ii) for `I = univ`.  The remaining work is
the MDS inequality for a *general* nonempty index set `I`.

## The clause-(ii) argument

For a nonempty `I ⊆ Fin m`:

* The per-vector weight is preserved (`mergeVec_vAbs`), so the sum term `Σ_{i∈I}(k − |mergeVec vᵢ|)`
  equals `Σ_{i∈I}(k − |vᵢ|)`.

* The merged-meet weight `|⋀_I mergeVec vᵢ|` decomposes (`mergeMeet_vAbs_split`) into the interior
  part — equal to the relocated original meet over `univ \ {j, last}` — plus the value at the new
  last coordinate `L`.  That value is `inf_{i∈I}(vᵢ j + vᵢ last)`; since `j` is an *interior*
  coordinate, shape (iii) forces `vᵢ j ≤ 1`, hence `(⋀_I mergeVec)(L) ≤ 1 + ⋀_I(last)`
  (`mergeMeet_last_le`).  Therefore the merged-meet weight exceeds the original by at most `1`
  (`mergeMeet_vAbs_le_succ`).

The `+1` is absorbed by a case split:

* If the merge candidate `i₀ ∈ I` (`vᵢ₀ j = vᵢ₀ last = 0`), the merge is *lossless*
  (`mergeMeet_vAbs_eq_of_mem`) and the inequality transports verbatim from `hV.mds`.
* If `i₀ ∉ I`, the candidate is absent.  Then either `I` is **non-tight** — whence
  `not_tightConstraint_le` gives a unit of slack to absorb the `+1` — or `I` is **tight**, in which
  case Lovett's Lemma 2.4 (`tight_card_eq_one_or_m`, available inside the minimal counterexample)
  forces `|I| ∈ {1, m}`.  A singleton set merges losslessly (its meet is the vector itself, weight
  preserved); `|I| = m` means `I = univ`, which *contains* `i₀`, contradicting `i₀ ∉ I`.

The capstone `mergeSys_isVStar` packages clauses (i)–(iii).

Issue #389.
-/

open Finset

namespace ArkLib.GMMDS

variable {F : Type*} [Field F] {m n : ℕ}

/-- **Upper bound on the merged meet at the new last coordinate.**  Since `j` is an interior
coordinate (`j < n−1`), shape (iii) bounds `vᵢ j ≤ 1`, so the merged-meet value
`inf_{i∈I}(vᵢ j + vᵢ last)` is at most `1 + ⋀_I(last)`. -/
theorem mergeMeet_last_le {n m : ℕ} (hn2 : 2 ≤ n) (j : Fin n) (hjlt : (j : ℕ) < n - 1)
    {V : Fin m → (Fin n → ℕ)} {k : ℕ} (hV : IsVStar V k)
    (I : Finset (Fin m)) (hI : I.Nonempty)
    (L : Fin (n - 1)) (hL : (L : ℕ) = n - 1 - 1) :
    vMeet (mergeSys (by omega : 1 ≤ n) j V) I hI L ≤ vMeet V I hI (lastCoord n (by omega)) + 1 := by
  have hn : 1 ≤ n := by omega
  rw [mergeMeet_last_eq hn j V I hI L hL]
  -- pick i₁ achieving inf of vᵢ last; then inf'(sum) ≤ vᵢ₁ j + vᵢ₁ last ≤ 1 + meet(last).
  obtain ⟨i₀, hi₀⟩ := hI
  classical
  obtain ⟨i₁, hi₁mem, hi₁eq⟩ := Finset.exists_mem_eq_inf' ⟨i₀, hi₀⟩ (fun i => V i (lastCoord n hn))
  have hshape : V i₁ j ≤ 1 := hV.shape i₁ j hjlt
  calc I.inf' ⟨i₀, hi₀⟩ (fun i => V i j + V i (lastCoord n hn))
      ≤ V i₁ j + V i₁ (lastCoord n hn) := Finset.inf'_le _ hi₁mem
    _ ≤ 1 + V i₁ (lastCoord n hn) := by omega
    _ = vMeet V I ⟨i₀, hi₀⟩ (lastCoord n hn) + 1 := by
        unfold vMeet; rw [← hi₁eq]; omega

/-- **The merge increases the meet weight by at most 1.**  Interior coordinates relocate bijectively
(equal contribution), and the merged coordinate adds at most `1` over the original last-coordinate
meet (`mergeMeet_last_le`, using shape (iii) at the interior coordinate `j`). -/
theorem mergeMeet_vAbs_le_succ {n m : ℕ} (hn2 : 2 ≤ n) (j : Fin n) (hjlt : (j : ℕ) < n - 1)
    {V : Fin m → (Fin n → ℕ)} {k : ℕ} (hV : IsVStar V k) (I : Finset (Fin m)) (hI : I.Nonempty) :
    vAbs (vMeet (mergeSys (by omega : 1 ≤ n) j V) I hI) ≤ vAbs (vMeet V I hI) + 1 := by
  classical
  have hn : 1 ≤ n := by omega
  rw [mergeMeet_vAbs_split hn2 j hjlt V I hI]
  have hsplitV : vAbs (vMeet V I hI)
      = (∑ c ∈ Finset.univ \ {j, lastCoord n hn}, vMeet V I hI c)
        + (vMeet V I hI j + vMeet V I hI (lastCoord n hn)) := by
    unfold vAbs
    have hsub : ({j, lastCoord n hn} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
    have hjlast : j ≠ lastCoord n hn := by
      intro h; rw [h] at hjlt; simp only [lastCoord] at hjlt; omega
    rw [← Finset.sum_sdiff hsub, Finset.sum_pair hjlast]
  rw [hsplitV]
  have hlast := mergeMeet_last_le hn2 j hjlt hV I hI ⟨n - 1 - 1, by omega⟩ rfl
  omega

/-- **Clause (ii) for the merged system, lossless case.**  When the merge candidate `i₀ ∈ I` is
present, the merged meet weight is unchanged and the per-vector weights are preserved, so the MDS
inequality transports verbatim from `hV.mds I`. -/
theorem mergeSys_mds_of_mem {n m : ℕ} (hn2 : 2 ≤ n) (j : Fin n) (hjlt : (j : ℕ) < n - 1)
    {V : Fin m → (Fin n → ℕ)} {k : ℕ} (hV : IsVStar V k)
    (I : Finset (Fin m)) (hI : I.Nonempty)
    {i₀ : Fin m} (hi₀ : i₀ ∈ I) (hj0 : V i₀ j = 0) (hlast0 : V i₀ (lastCoord n (by omega)) = 0) :
    (∑ i ∈ I, (k - vAbs (mergeSys (by omega : 1 ≤ n) j V i)))
        + vAbs (vMeet (mergeSys (by omega : 1 ≤ n) j V) I hI) ≤ k := by
  have hn : 1 ≤ n := by omega
  have hwt : ∀ i, vAbs (mergeSys hn j V i) = vAbs (V i) := by
    intro i; rw [mergeSys, mergeVec_vAbs hn2 j hjlt]
  rw [Finset.sum_congr rfl (fun i _ => by rw [hwt i])]
  rw [mergeMeet_vAbs_eq_of_mem hn2 j hjlt V I hI hi₀ hj0 hlast0]
  exact hV.mds I hI

/-- **Clause (ii) for the merged system at a singleton.**  A singleton merges losslessly: its meet
is the vector itself, whose weight is preserved by `mergeVec_vAbs`. -/
theorem mergeSys_mds_singleton {n m : ℕ} (hn2 : 2 ≤ n) (j : Fin n) (hjlt : (j : ℕ) < n - 1)
    {V : Fin m → (Fin n → ℕ)} {k : ℕ} (hV : IsVStar V k) (i : Fin m) :
    (∑ i' ∈ ({i} : Finset (Fin m)), (k - vAbs (mergeSys (by omega : 1 ≤ n) j V i')))
        + vAbs (vMeet (mergeSys (by omega : 1 ≤ n) j V) {i} (Finset.singleton_nonempty i)) ≤ k := by
  classical
  have hn : 1 ≤ n := by omega
  rw [Finset.sum_singleton]
  -- the singleton meet of the merged system is the merged vector itself
  have hmeet : vMeet (mergeSys hn j V) {i} (Finset.singleton_nonempty i) = mergeSys hn j V i := by
    funext t; unfold vMeet; simp [Finset.inf'_singleton]
  rw [hmeet, mergeSys, mergeVec_vAbs hn2 j hjlt]
  -- k - |vᵢ| + |vᵢ| = k  (since |vᵢ| ≤ k)
  have hle : vAbs (V i) ≤ k := le_trans (hV.weight_le i) (Nat.sub_le k 1)
  omega

/-- **Clause (ii) for the merged system — general nonempty index set.**  Inside a minimal
counterexample (`hcex`, with the `d`- and `m`-IHs), the MDS inequality holds for `mergeSys j V` at
every nonempty `I`.  The merge candidate `i₀` (zeroing the interior `j` and the last coordinate) is
the engine for the absent-candidate non-tight slack and the tight-set classification. -/
theorem mergeSys_mds_general {n m : ℕ} (hn2 : 2 ≤ n) (j : Fin n) (hjlt : (j : ℕ) < n - 1)
    {V : Fin m → (Fin n → ℕ)} {k : ℕ} (hk : 1 ≤ k) (hV : IsVStar V k)
    {i₀ : Fin m} (hj0 : V i₀ j = 0) (hlast0 : V i₀ (lastCoord n (by omega)) = 0)
    (hcex : ¬ LovettHolds F V k)
    (IHd : ∀ {m' : ℕ} (V' : Fin m' → (Fin n → ℕ)),
      lovettD V' k < lovettD V k → IsVStar V' k → LovettHolds F V' k)
    (IHm : ∀ {m' : ℕ} (V' : Fin m' → (Fin n → ℕ)),
      lovettD V' k = lovettD V k → m' < m → IsVStar V' k → LovettHolds F V' k)
    (I : Finset (Fin m)) (hI : I.Nonempty) :
    (∑ i ∈ I, (k - vAbs (mergeSys (by omega : 1 ≤ n) j V i)))
        + vAbs (vMeet (mergeSys (by omega : 1 ≤ n) j V) I hI) ≤ k := by
  classical
  have hn : 1 ≤ n := by omega
  by_cases hmem : i₀ ∈ I
  · exact mergeSys_mds_of_mem hn2 j hjlt hV I hI hmem hj0 hlast0
  · -- candidate absent: split on tightness of I
    -- per-vector weights are preserved
    have hwt : ∀ i, vAbs (mergeSys hn j V i) = vAbs (V i) := by
      intro i; rw [mergeSys, mergeVec_vAbs hn2 j hjlt]
    rw [Finset.sum_congr rfl (fun i _ => by rw [hwt i])]
    by_cases htight : tightConstraint V k I hI
    · -- tight: |I| ∈ {1, m}
      rcases tight_card_eq_one_or_m hI hk hV htight hcex IHd IHm with h1 | hm
      · -- singleton
        obtain ⟨i, hieq⟩ := Finset.card_eq_one.mp h1
        subst hieq
        have := mergeSys_mds_singleton hn2 j hjlt hV i
        rwa [Finset.sum_singleton, hwt i] at this
      · -- |I| = m  ⟹  I = univ  ⟹  i₀ ∈ I, contradiction
        exfalso
        have huniv : I = Finset.univ := by
          apply Finset.eq_univ_of_card
          rw [hm, Fintype.card_fin]
        exact hmem (huniv ▸ Finset.mem_univ i₀)
    · -- non-tight: slack absorbs the +1
      have hslack := not_tightConstraint_le hV hI htight
      have hmeet := mergeMeet_vAbs_le_succ hn2 j hjlt hV I hI
      omega

/-- **The merged system is again `V*(k)`.**  Inside a minimal counterexample (with the `d`- and
`m`-IHs and the merge candidate `i₀`), `mergeSys j V` satisfies all three `V*(k)` clauses: weight
(i) and shape (iii) automatically (`mergeSys_weight_shape`), and the MDS clause (ii) at every
nonempty index set (`mergeSys_mds_general`). -/
theorem mergeSys_isVStar {n m : ℕ} (hn2 : 2 ≤ n) (j : Fin n) (hjlt : (j : ℕ) < n - 1)
    {V : Fin m → (Fin n → ℕ)} {k : ℕ} (hk : 1 ≤ k) (hV : IsVStar V k)
    {i₀ : Fin m} (hj0 : V i₀ j = 0) (hlast0 : V i₀ (lastCoord n (by omega)) = 0)
    (hcex : ¬ LovettHolds F V k)
    (IHd : ∀ {m' : ℕ} (V' : Fin m' → (Fin n → ℕ)),
      lovettD V' k < lovettD V k → IsVStar V' k → LovettHolds F V' k)
    (IHm : ∀ {m' : ℕ} (V' : Fin m' → (Fin n → ℕ)),
      lovettD V' k = lovettD V k → m' < m → IsVStar V' k → LovettHolds F V' k) :
    IsVStar (mergeSys (by omega : 1 ≤ n) j V) k := by
  obtain ⟨hwt, hshape⟩ := mergeSys_weight_shape hn2 j hjlt hV
  refine ⟨?_, ?_, ?_⟩
  · -- (i): weight ≤ k - 1
    exact hwt
  · -- (ii): the MDS inequality at every nonempty I
    intro I hI
    exact mergeSys_mds_general (F := F) hn2 j hjlt hk hV hj0 hlast0 hcex IHd IHm I hI
  · -- (iii): shape
    exact hshape

end ArkLib.GMMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.GMMDS.mergeMeet_last_le
#print axioms ArkLib.GMMDS.mergeMeet_vAbs_le_succ
#print axioms ArkLib.GMMDS.mergeSys_mds_general
#print axioms ArkLib.GMMDS.mergeSys_isVStar
