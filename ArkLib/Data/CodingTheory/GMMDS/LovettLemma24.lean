/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettCombinatorial

/-!
# Lovett's GM-MDS proof: tight constraints and primitivity combinatorics (#389)

Combinatorial scaffolding for Lovett's Lemmas 2.4–2.6 (arXiv:1803.02523).  This file collects
the *purely combinatorial* facts about a `V*(k)` system that the (algebraic) Lemmas 2.4–2.6
build on, kept separate from the algebraic substitution arguments:

* `tightConstraint` — Definition 2.3: `I` is tight when property (ii) holds with equality.
* `singleton_tight` — a singleton is always tight (Lovett's remark after Def 2.3).
* `vMeet_univ_eq_zero` — in a *primitive* system (`∀ j, ∃ i, vᵢ(j) = 0`) the meet over **all**
  indices is the zero vector (this is Lovett's Lemma 2.2 conclusion, the standing hypothesis of
  §2 once the reducible branch is removed by the master frame).
* `last_coord_meet_zero` — the last coordinate of the full meet is `0`, used in Lemma 2.5 to
  locate a vector with `vᵢ(n−1) = 0`.

Issue #389.
-/

open Finset

namespace ArkLib.GMMDS

variable {m n : ℕ}

/-- **Definition 2.3 (tight constraint).**  `I` is *tight* for `V` (at level `k`) when the MDS
inequality (ii) holds with equality:
`Σ_{i∈I}(k − |vᵢ|) + |⋀_{i∈I} vᵢ| = k`. -/
def tightConstraint (V : Fin m → (Fin n → ℕ)) (k : ℕ) (I : Finset (Fin m))
    (hI : I.Nonempty) : Prop :=
  (∑ i ∈ I, (k - vAbs (V i))) + vAbs (vMeet V I hI) = k

/-- A singleton index set `{i}` is always a tight constraint: the sum is `k − |vᵢ|` and the meet
is `vᵢ`, so the total is `k`. -/
theorem singleton_tight (V : Fin m → (Fin n → ℕ)) {k : ℕ} (i : Fin m)
    (hk : vAbs (V i) ≤ k) :
    tightConstraint V k {i} (Finset.singleton_nonempty i) := by
  classical
  unfold tightConstraint
  rw [Finset.sum_singleton]
  have hmeet : vAbs (vMeet V {i} (Finset.singleton_nonempty i)) = vAbs (V i) := by
    unfold vAbs vMeet
    refine Finset.sum_congr rfl (fun l _ => ?_)
    simp [Finset.inf'_singleton]
  rw [hmeet]; omega

/-- In a system where coordinate `j` is *globally hit by a zero* (`∃ i, V i j = 0`), the meet over
**all** indices vanishes at `j`. -/
theorem meet_univ_coord_zero {V : Fin m → (Fin n → ℕ)} (hne : (Finset.univ : Finset (Fin m)).Nonempty)
    {j : Fin n} (hj : ∃ i, V i j = 0) :
    vMeet V Finset.univ hne j = 0 := by
  classical
  obtain ⟨i, hi⟩ := hj
  unfold vMeet
  refine Nat.le_zero.mp ?_
  rw [← hi]
  exact Finset.inf'_le (fun i => V i j) (Finset.mem_univ i)

/-- **Primitivity ⟹ full meet is zero** (Lovett's Lemma 2.2 conclusion).  If every coordinate is
hit by a zero of some vector, the coordinate-wise meet over all indices is the zero vector. -/
theorem vMeet_univ_eq_zero {V : Fin m → (Fin n → ℕ)} (hne : (Finset.univ : Finset (Fin m)).Nonempty)
    (hprim : ∀ j : Fin n, ∃ i, V i j = 0) :
    vMeet V Finset.univ hne = (fun _ => 0) := by
  funext j
  exact meet_univ_coord_zero hne (hprim j)

/-- The full meet has weight zero in a primitive system. -/
theorem vAbs_vMeet_univ_eq_zero {V : Fin m → (Fin n → ℕ)}
    (hne : (Finset.univ : Finset (Fin m)).Nonempty)
    (hprim : ∀ j : Fin n, ∃ i, V i j = 0) :
    vAbs (vMeet V Finset.univ hne) = 0 := by
  rw [vMeet_univ_eq_zero hne hprim]; simp [vAbs]

/-- **Slack form of the MDS condition.**  In a `V*(k)` system, a *non-tight* index set `I`
satisfies the strict inequality, i.e. over `ℕ` the MDS quantity is `≤ k − 1`:
`Σ_{i∈I}(k − |vᵢ|) + |⋀_{i∈I} vᵢ| ≤ k − 1`.

This is the precise "slack absorbs the merge" inequality used in the `|I| < m` branch of Lemma
2.5's clause (ii): a non-tight set has at least one unit of slack to absorb the `+1` produced by
merging two coordinates. -/
theorem not_tightConstraint_le {V : Fin m → (Fin n → ℕ)} {k : ℕ} (hV : IsVStar V k)
    {I : Finset (Fin m)} (hI : I.Nonempty) (hnt : ¬ tightConstraint V k I hI) :
    (∑ i ∈ I, (k - vAbs (V i))) + vAbs (vMeet V I hI) ≤ k - 1 := by
  have hle := hV.mds I hI
  unfold tightConstraint at hnt
  omega

/-- **Tight ⟹ no slack.**  The contrapositive companion: if the MDS quantity has slack
(`≤ k − 1`), then `I` is not tight.  (Trivial, but convenient for the dichotomy bookkeeping.) -/
theorem not_tightConstraint_of_le {V : Fin m → (Fin n → ℕ)} {k : ℕ}
    {I : Finset (Fin m)} (hI : I.Nonempty)
    (hle : (∑ i ∈ I, (k - vAbs (V i))) + vAbs (vMeet V I hI) ≤ k - 1) (hk : 1 ≤ k) :
    ¬ tightConstraint V k I hI := by
  unfold tightConstraint
  omega

/-- **Primitivity ⟹ the full-set meet is tight-at-last with value `0`.**  In a primitive system
the last coordinate of the full meet vanishes (`meet_univ_coord_zero` with the last coordinate),
the precise fact used in the `|I| = m` branch of Lemma 2.5's clause (ii) — there the merge of the
last two coordinates of the meet contributes nothing, since both are `0`. -/
theorem meet_univ_last_zero {V : Fin m → (Fin n → ℕ)}
    (hne : (Finset.univ : Finset (Fin m)).Nonempty) {j : Fin n}
    (hj : ∃ i, V i j = 0) : vMeet V Finset.univ hne j = 0 :=
  meet_univ_coord_zero hne hj

end ArkLib.GMMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.GMMDS.singleton_tight
#print axioms ArkLib.GMMDS.vMeet_univ_eq_zero
#print axioms ArkLib.GMMDS.not_tightConstraint_le
#print axioms ArkLib.GMMDS.not_tightConstraint_of_le
