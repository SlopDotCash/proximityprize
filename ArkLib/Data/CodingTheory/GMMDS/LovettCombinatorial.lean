/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Lovett's GM-MDS proof: the combinatorial core (#389)

Formalizing Shachar Lovett, *MDS matrices over small fields: A proof of the GM-MDS
conjecture* (arXiv:1803.02523).  This file sets up the combinatorial framework — the
multiplicity-vector system `V = (v₁,…,v_m) ⊆ ℕⁿ`, the property `V*(k)` (Definitions 1.4 /
1.6), the coordinate-wise meet `⋀`, and the first structural lemma — which underlie the
minimal-counterexample induction proving Theorem 1.7 (the algebraic GM-MDS conjecture).

This is layer 1 (the purely combinatorial part) of discharging the in-tree residual
`AGL24.GMMDSDualZeroPatternTheorem`.  The algebraic core (linear independence of the
polynomial families `P(k,V)` over the rational function field `F(a)`, via Lemmas 2.2–2.6)
builds on this.

## Results

* `vAbs` — the weight `|v| = Σⱼ v(j)`.
* `vMeet` — the coordinate-wise meet `⋀_{i∈I} vᵢ` over a nonempty index set.
* `IsVStar` — Lovett's property `V*(k)` (Def 1.6): bounded weight, the MDS-condition
  inequality (ii), and the `{0,1}`-except-last shape (iii).
* `not_le_of_isVStar` (**Lemma 2.1**): no two distinct system vectors are comparable.

Issue #389.
-/

open Finset

namespace ArkLib.GMMDS

variable {m n : ℕ}

/-- The weight `|v| = Σⱼ v(j)` of a multiplicity vector. -/
def vAbs (v : Fin n → ℕ) : ℕ := ∑ j, v j

/-- The coordinate-wise meet `⋀_{i∈I} vᵢ` of a nonempty family of vectors. -/
noncomputable def vMeet (V : Fin m → (Fin n → ℕ)) (I : Finset (Fin m))
    (hI : I.Nonempty) : Fin n → ℕ :=
  fun j => I.inf' hI (fun i => V i j)

/-- **Lovett's property `V*(k)`** (Definition 1.6).  A multiplicity-vector system
`V = (v₁,…,v_m) ⊆ ℕⁿ` satisfies `V*(k)` when:
* (i) every weight is `≤ k−1`;
* (ii) for every nonempty `I`, `Σ_{i∈I}(k − |vᵢ|) + |⋀_{i∈I} vᵢ| ≤ k` (the MDS condition);
* (iii) every coordinate except the last is in `{0,1}`. -/
structure IsVStar (V : Fin m → (Fin n → ℕ)) (k : ℕ) : Prop where
  weight_le : ∀ i, vAbs (V i) ≤ k - 1
  mds : ∀ (I : Finset (Fin m)) (hI : I.Nonempty),
    (∑ i ∈ I, (k - vAbs (V i))) + vAbs (vMeet V I hI) ≤ k
  shape : ∀ i, ∀ j : Fin n, (j : ℕ) < n - 1 → V i j ≤ 1

/-- If `v ≤ w` coordinate-wise then the pair-meet is `v`, so `|⋀| = |v|`. -/
theorem vAbs_meet_pair_of_le {V : Fin m → (Fin n → ℕ)} {i j : Fin m}
    (hle : ∀ l, V i l ≤ V j l) :
    vAbs (vMeet V {i, j} ⟨i, Finset.mem_insert_self i {j}⟩) = vAbs (V i) := by
  classical
  rw [vAbs, vAbs]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  show ({i, j} : Finset (Fin m)).inf' ⟨i, Finset.mem_insert_self i {j}⟩
      (fun i' => V i' l) = V i l
  refine le_antisymm (Finset.inf'_le _ (Finset.mem_insert_self i {j})) ?_
  refine Finset.le_inf' _ _ (fun i' hi' => ?_)
  rcases Finset.mem_insert.mp hi' with h | h
  · subst h; exact le_refl _
  · rw [Finset.mem_singleton.mp h]; exact hle l

/-- **Lemma 2.1.**  In a system satisfying `V*(k)` (only (i),(ii) are used), no two
*distinct* vectors are coordinate-wise comparable: there are no `i ≠ j` with `vᵢ ≤ vⱼ`. -/
theorem not_le_of_isVStar {V : Fin m → (Fin n → ℕ)} {k : ℕ} (hk : 1 ≤ k)
    (hV : IsVStar V k) {i j : Fin m} (hij : i ≠ j) : ¬ (∀ l, V i l ≤ V j l) := by
  classical
  intro hle
  -- (ii) at I = {i, j}
  have hpair : ({i, j} : Finset (Fin m)).Nonempty := ⟨i, Finset.mem_insert_self i {j}⟩
  have h2 := hV.mds {i, j} hpair
  -- the pair sum is (k - |vᵢ|) + (k - |vⱼ|)
  have hsum : (∑ i' ∈ ({i, j} : Finset (Fin m)), (k - vAbs (V i')))
      = (k - vAbs (V i)) + (k - vAbs (V j)) := by
    rw [Finset.sum_insert (by simp [hij]), Finset.sum_singleton]
  -- |⋀| = |vᵢ|
  have hmeet : vAbs (vMeet V {i, j} hpair) = vAbs (V i) :=
    vAbs_meet_pair_of_le hle
  rw [hsum, hmeet] at h2
  have hi := hV.weight_le i
  have hj := hV.weight_le j
  -- 2k - |vⱼ| ≤ k  with |vⱼ| ≤ k-1  ⟹  contradiction (k ≥ 1 forced)
  omega

end ArkLib.GMMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.GMMDS.not_le_of_isVStar
