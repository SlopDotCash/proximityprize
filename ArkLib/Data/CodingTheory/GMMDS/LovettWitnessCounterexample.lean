/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GMMDS.LovettLemma2456
import ArkLib.Data.CodingTheory.GMMDS.LovettLemma24

/-!
# Lovett's GM-MDS proof: the witness counterexample (REPAIR DONE) (#389)

The in-tree residual `LovettWitnessExists` (`LovettLemma2456.lean`) packages the combinatorial
core of Lovett's §2 (Lemmas 2.4–2.6, arXiv:1803.02523).  An earlier version of `LovettWitness`
demanded *every primitive `V*(k)` system contains an index `i₀` with `V i₀ = (1,…,1,0)` **and**
`n = k`*.  **The `n = k` conjunct was not derivable** and made the residual false.  This file
exhibits the explicit counterexample that diagnosed it:

`n = 2`, `k = 3`, `m = 2`, `V = (v₀, v₁)` with `v₀ = (1,0)` and `v₁ = (0,2)`.

* `cexV_isVStar` — `V` satisfies `V*(3)`.
* `cexV_primitive` — `V` is primitive (`∀ j, ∃ i, V i j = 0`).
* `cexV_not_reducible` — `V` is **not** reducible (no coordinate is `≥ 1` everywhere), so the
  minimal-counterexample master frame routes it to the *primitive* step, where the witness is
  demanded.
* `cexV_n_ne_k` — here `n = 2 ≠ 3 = k`, so the old `n = k` demand was genuinely false.

The deeper fact is that `P(3, V)` is *linearly independent* — its coefficient determinant over
`F(a)` is `(a₁ − a₂)²`, the polynomials being `{x − a₁, (x − a₁)x, (x − a₂)²}`.  So this is **not**
a counterexample to Theorem 1.7: it is a genuine independent primitive `V*(k)` system with `n < k`.

**Repair (DONE).**  `LovettWitness` now drops `n = k`, keeping only Lemma 2.5
(`∃ i₀, V i₀ = (1,…,1,0)`).  `lovettHolds_of_witness` (in `LovettNLtK.lean`) splits on `n = k`
vs `n < k`: the `n = k` branch is the one-vector separation (`lovettHolds_of_witness_nEqK`); the
`n < k` branch is the genuine algebraic Lemma 2.6 / final contradiction proven as a *direct*
independence statement (`lovettHolds_nLtK`: raise `vᵢ₀`, transfer via the block-span identity, the
`d`-IH, and the separated factor `p = ∏_{j<n−1}(x − aⱼ)`).  Accordingly this file now records
`cexV_has_witness`: the *repaired* `LovettWitness` is **satisfiable** on this system (routed
through the `n < k` branch), not a false demand.

Issue #389.
-/

open Finset

namespace ArkLib.GMMDS

/-- The counterexample system: `v₀ = (1,0)`, `v₁ = (0,2)` in `ℕ²`. -/
def cexV : Fin 2 → (Fin 2 → ℕ) := ![![1, 0], ![0, 2]]

/-- `V` is primitive: coordinate `0` is zeroed by `v₁`, coordinate `1` by `v₀`. -/
theorem cexV_primitive : ∀ j : Fin 2, ∃ i, cexV i j = 0 := by
  decide

/-- `V` is **not** reducible: no coordinate is `≥ 1` in *every* vector. -/
theorem cexV_not_reducible : ¬ ∃ j : Fin 2, ∀ i, 1 ≤ cexV i j := by
  decide

theorem cexV_vAbs0 : vAbs (cexV 0) = 1 := by rw [vAbs]; decide
theorem cexV_vAbs1 : vAbs (cexV 1) = 2 := by rw [vAbs]; decide

/-- The weight of the meet over a nonempty `J` equals the meet weight; computed per-subset. -/
private theorem cexV_meet_singleton (i : Fin 2) :
    vAbs (vMeet cexV {i} (Finset.singleton_nonempty i)) = vAbs (cexV i) := by
  unfold vAbs vMeet
  refine Finset.sum_congr rfl (fun l _ => ?_)
  simp [Finset.inf'_singleton]

/-- The meet over the whole index set `{0,1}` is the zero vector (primitivity). -/
private theorem cexV_meet_pair (hJ : ({0, 1} : Finset (Fin 2)).Nonempty) :
    vAbs (vMeet cexV {0, 1} hJ) = 0 := by
  rw [vAbs]
  have hz : ∀ l, vMeet cexV {0, 1} hJ l = 0 := by
    intro l
    obtain ⟨i, hi⟩ := cexV_primitive l
    refine Nat.le_zero.mp ?_
    rw [← hi]
    refine Finset.inf'_le (fun i => cexV i l) ?_
    fin_cases i <;> decide
  simp [hz]

/-- Every nonempty `I ⊆ Fin 2` is `{0}`, `{1}`, or `{0,1}`. -/
private theorem cexV_subset_cases (I : Finset (Fin 2)) (hI : I.Nonempty) :
    I = {0} ∨ I = {1} ∨ I = {0, 1} := by
  classical
  obtain ⟨w, hw⟩ := hI
  by_cases h0 : (0 : Fin 2) ∈ I <;> by_cases h1 : (1 : Fin 2) ∈ I
  · right; right
    have hIeq : I = Finset.univ := by
      rw [Finset.eq_univ_iff_forall]
      intro x; fin_cases x <;> assumption
    rw [hIeq]; decide
  · left
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨h0, fun x hx => ?_⟩
    fin_cases x
    · rfl
    · exact absurd hx h1
  · right; left
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨h1, fun x hx => ?_⟩
    fin_cases x
    · exact absurd hx h0
    · rfl
  · exfalso; fin_cases w <;> simp_all

/-- `V` satisfies Lovett's property `V*(3)`. -/
theorem cexV_isVStar : IsVStar cexV 3 := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · -- (i) weights ≤ k − 1 = 2
    intro i
    fin_cases i
    · show vAbs (cexV 0) ≤ 3 - 1; rw [cexV_vAbs0]; omega
    · show vAbs (cexV 1) ≤ 3 - 1; rw [cexV_vAbs1]
  · -- (ii) MDS inequality for every nonempty I
    intro I hI
    rcases cexV_subset_cases I hI with rfl | rfl | rfl
    · rw [Finset.sum_singleton, cexV_meet_singleton, cexV_vAbs0]
    · rw [Finset.sum_singleton, cexV_meet_singleton, cexV_vAbs1]
    · rw [show (∑ i ∈ ({0, 1} : Finset (Fin 2)), (3 - vAbs (cexV i)))
            = (3 - vAbs (cexV 0)) + (3 - vAbs (cexV 1)) by
          rw [Finset.sum_insert (by decide), Finset.sum_singleton],
        cexV_meet_pair, cexV_vAbs0, cexV_vAbs1]
  · -- (iii) coordinate `0` (the only one `< n − 1 = 1`) is in `{0,1}`
    intro i l hl
    have hl0 : l = 0 := by
      have : (l : ℕ) = 0 := by omega
      exact Fin.ext (by simpa using this)
    subst hl0
    fin_cases i <;> decide

/-- `cexV 0 = (1,0) = oneVec 2`. -/
theorem cexV_zero_eq_oneVec : cexV 0 = oneVec 2 (by norm_num) := by
  funext j; fin_cases j <;> rfl

/-- **The *repaired* `LovettWitness F V 3` holds.**  After dropping the false `n = k` conjunct,
`LovettWitness` is exactly Lemma 2.5 (`∃ i₀, V i₀ = (1,…,1,0)`), and the counterexample system
*does* contain such a vector (`v₀ = (1,0)`).  So the repaired residual is **satisfiable** here —
confirming the repair routes this system through the genuine `n < k` branch
(`ArkLib.GMMDS.lovettHolds_nLtK`) rather than a vacuous/false demand. -/
theorem cexV_has_witness (F : Type*) [Field F] : LovettWitness F cexV 3 :=
  ⟨by norm_num, 0, cexV_zero_eq_oneVec⟩

/-- **The old `n = k` conjunct is genuinely false here.**  This is *why* the previous
`LovettWitness` definition (which bundled `n = k`) was an unprovable, false residual: the
counterexample has `n = 2 ≠ 3 = k`. -/
theorem cexV_n_ne_k : (2 : ℕ) ≠ 3 := by norm_num

end ArkLib.GMMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.GMMDS.cexV_isVStar
#print axioms ArkLib.GMMDS.cexV_has_witness
