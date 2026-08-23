/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettCombinatorial
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Lovett's GM-MDS proof: `V*(k)` preservation under coordinate reduction (#389, layer 7)

The combinatorial input to Lemma 2.2 (arXiv:1803.02523): if every vector of a `V*(k)` system
has `vᵢ(j) ≥ 1`, then lowering coordinate `j` by one in every vector yields a `V*(k−1)`
system.  Composed with `pFam_family_indep_of_reduced` (layer 5) this is the full Lemma 2.2
reduction.

Issue #389.
-/

open Finset

namespace ArkLib.GMMDS

variable {m n : ℕ}

/-- Lowering one coordinate `≥ 1` by one drops the weight by one. -/
theorem vAbs_update_pred (f : Fin n → ℕ) (j : Fin n) (h : 1 ≤ f j) :
    vAbs (Function.update f j (f j - 1)) = vAbs f - 1 := by
  classical
  rw [vAbs, vAbs, Finset.sum_update_of_mem (Finset.mem_univ j),
    ← Finset.add_sum_erase _ f (Finset.mem_univ j), Finset.erase_eq]
  omega

/-- `inf'` of `(g i − 1)` is `(inf' g) − 1` when every `g i ≥ 1`. -/
theorem inf'_pred {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (g : ι → ℕ)
    (hg : ∀ i ∈ s, 1 ≤ g i) :
    s.inf' hs (fun i => g i - 1) = s.inf' hs g - 1 := by
  refine le_antisymm ?_ ?_
  · obtain ⟨i₀, hi₀, hi₀eq⟩ := Finset.exists_mem_eq_inf' hs g
    rw [hi₀eq]
    exact Finset.inf'_le _ hi₀
  · refine Finset.le_inf' _ _ (fun i hi => ?_)
    have h1 := Finset.inf'_le g hi
    have h2 := hg i hi
    omega

/-- The meet of the reduced system equals the reduced meet (shared coordinate `j`). -/
theorem vMeet_reduce (V : Fin m → (Fin n → ℕ)) (I : Finset (Fin m)) (hI : I.Nonempty)
    {j : Fin n} (h : ∀ i ∈ I, 1 ≤ V i j) :
    vMeet (fun i => Function.update (V i) j (V i j - 1)) I hI
      = Function.update (vMeet V I hI) j (vMeet V I hI j - 1) := by
  classical
  funext l
  by_cases hl : l = j
  · rw [hl, Function.update_self]
    show I.inf' hI (fun i => Function.update (V i) j (V i j - 1) j)
      = I.inf' hI (fun i => V i j) - 1
    have hfun : (fun i => Function.update (V i) j (V i j - 1) j)
        = (fun i => V i j - 1) := by funext i; rw [Function.update_self]
    rw [hfun]
    exact inf'_pred I hI (fun i => V i j) h
  · rw [Function.update_of_ne hl]
    show I.inf' hI (fun i => Function.update (V i) j (V i j - 1) l) = I.inf' hI (fun i => V i l)
    have hfun : (fun i => Function.update (V i) j (V i j - 1) l) = (fun i => V i l) := by
      funext i; rw [Function.update_of_ne hl]
    rw [hfun]

/-- **`V*(k)` preservation under coordinate reduction** (Lemma 2.2 combinatorial input). -/
theorem isVStar_reduce {V : Fin m → (Fin n → ℕ)} {k : ℕ} (hk : 1 ≤ k)
    (hV : IsVStar V k) {j : Fin n} (hj : ∀ i, 1 ≤ V i j) :
    IsVStar (fun i => Function.update (V i) j (V i j - 1)) (k - 1) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [vAbs_update_pred _ _ (hj i)]
    have := hV.weight_le i; omega
  · intro I hI
    have hmeet_ge : 1 ≤ vMeet V I hI j := Finset.le_inf' _ _ (fun i _ => hj i)
    have hmeet : vAbs (vMeet (fun i => Function.update (V i) j (V i j - 1)) I hI)
        = vAbs (vMeet V I hI) - 1 := by
      rw [vMeet_reduce V I hI (fun i _ => hj i)]
      exact vAbs_update_pred _ _ hmeet_ge
    have hsumeq : (∑ i ∈ I, ((k - 1) - vAbs (Function.update (V i) j (V i j - 1))))
        = ∑ i ∈ I, (k - vAbs (V i)) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [vAbs_update_pred _ _ (hj i)]
      have hle := hV.weight_le i
      have hge : 1 ≤ vAbs (V i) := by
        rw [vAbs]
        exact le_trans (hj i)
          (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
      omega
    have horig := hV.mds I hI
    have hmeet_abs_ge : 1 ≤ vAbs (vMeet V I hI) := by
      rw [vAbs]
      exact le_trans hmeet_ge
        (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
    rw [hsumeq, hmeet]; omega
  · intro i l hl
    by_cases hlj : l = j
    · rw [hlj, Function.update_self]
      have hjlt : (j : ℕ) < n - 1 := by rw [← hlj]; exact hl
      have hs := hV.shape i j hjlt
      have := hj i
      omega
    · rw [Function.update_of_ne hlj]; exact hV.shape i l hl

end ArkLib.GMMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.GMMDS.isVStar_reduce
