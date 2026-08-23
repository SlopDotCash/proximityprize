/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettLemma2456
import ArkLib.Data.CodingTheory.GMMDS.LovettLemma24

/-!
# Lovett's GM-MDS proof: the combinatorial opening of Lemma 2.5 (#389)

The opening moves of Lovett's Lemma 2.5 (arXiv:1803.02523, p.9), kept separate from the
algebraic merge/substitution argument:

* `exists_last_coord_zero` — Lemma 2.2 (`vMeet_univ_eq_zero`) locates an index `i*` whose last
  coordinate vanishes, `vᵢ*(n−1) = 0`.
* `exists_inner_zero_of_ne_oneVec` — if such a vector is **not** the witness `(1,…,1,0)`, then by
  the `{0,1}`-shape (iii) it has a *strictly interior* zero: `∃ j* < n−1, vᵢ*(j*) = 0`.  This is
  the bad coordinate `j*` Lovett merges with the last coordinate.

Together these say: **either** some vector is the witness `(1,…,1,0)` (Lemma 2.5's conclusion),
**or** there is an index `i*` and a coordinate `j* < n−1` with both `vᵢ*(j*) = 0` and
`vᵢ*(n−1) = 0` — the precondition for the merge construction (the remaining algebraic residual
`LovettMerge`).

Issue #389.
-/

open Finset

namespace ArkLib.GMMDS

variable {F : Type*} [Field F] {n m : ℕ}

/-- **Lemma 2.2 corollary for Lemma 2.5.**  In a primitive system, some vector has its last
coordinate equal to `0`. -/
theorem exists_last_coord_zero {V : Fin m → (Fin n → ℕ)} (hn : 1 ≤ n)
    (hprim : ∀ j : Fin n, ∃ i, V i j = 0) :
    ∃ i, V i (lastCoord n hn) = 0 := hprim _

/-- **The shape dichotomy of Lemma 2.5.**  If a vector `vᵢ` has `vᵢ(n−1) = 0` and is **not** the
all-ones-except-last witness `(1,…,1,0)`, then (using shape (iii): every interior coordinate is
`0` or `1`) it must have an interior zero `vᵢ(j*) = 0` for some `j* < n−1`.  Otherwise every
interior coordinate would be exactly `1` and the last would be `0`, making `vᵢ = (1,…,1,0)`. -/
theorem exists_inner_zero_of_ne_oneVec {V : Fin m → (Fin n → ℕ)} {k : ℕ} (hn : 1 ≤ n)
    (hV : IsVStar V k) {i : Fin m} (hlast : V i (lastCoord n hn) = 0)
    (hne : V i ≠ oneVec n hn) :
    ∃ j : Fin n, (j : ℕ) < n - 1 ∧ V i j = 0 := by
  by_contra hcon
  push Not at hcon
  apply hne
  funext j
  by_cases hj : (j : ℕ) < n - 1
  · have h1 := hV.shape i j hj
    have h2 := hcon j hj
    simp only [oneVec, if_pos hj]; omega
  · have hjl : j = lastCoord n hn := by
      apply Fin.ext; simp only [lastCoord]; omega
    rw [hjl, hlast]
    simp only [oneVec, lastCoord]
    rw [if_neg (by omega : ¬ ((n - 1 : ℕ) < n - 1))]

/-- **The Lemma 2.5 alternative** (combinatorial form).  In a primitive `V*(k)` system with
`m ≥ 1`: **either** the structured witness exists (some `vᵢ₀ = (1,…,1,0)`), **or** there is an
index `i*` and an interior coordinate `j* < n−1` with `vᵢ*(j*) = 0` **and** `vᵢ*(n−1) = 0`.
The second alternative is the precondition of Lovett's merge construction; ruling it out (the
algebraic substitution-divisibility argument) is the remaining residual `LovettMerge`. -/
theorem witness_or_mergeCandidate {V : Fin m → (Fin n → ℕ)} {k : ℕ} (hn : 1 ≤ n)
    (hV : IsVStar V k) (hprim : ∀ j : Fin n, ∃ i, V i j = 0) :
    (∃ i₀, V i₀ = oneVec n hn) ∨
      (∃ (i : Fin m) (j : Fin n), (j : ℕ) < n - 1 ∧ V i j = 0 ∧ V i (lastCoord n hn) = 0) := by
  obtain ⟨i, hlast⟩ := exists_last_coord_zero hn hprim
  by_cases hwit : V i = oneVec n hn
  · exact Or.inl ⟨i, hwit⟩
  · obtain ⟨j, hjlt, hj0⟩ := exists_inner_zero_of_ne_oneVec hn hV hlast hwit
    exact Or.inr ⟨i, j, hjlt, hj0, hlast⟩

end ArkLib.GMMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.GMMDS.exists_last_coord_zero
#print axioms ArkLib.GMMDS.exists_inner_zero_of_ne_oneVec
#print axioms ArkLib.GMMDS.witness_or_mergeCandidate
