/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.AntipodalVanishingCountLower

/-!
# §6.5 — the GRADED lower half of Lam–Leung: `C(n/2, j) ≤ #{vanishing subsets of size 2j}` (#444)

This refines `AntipodalVanishingCountLower.lean` (which proved the *total* lower bound
`2^{n/2} ≤ V_1(μ_n)`) to a **per-size** (graded) lower bound: choosing exactly `j` of the `p = n/2`
antipodal pairs `{x, -x}` gives a vanishing subset of size `2j`, and there are exactly `C(p, j)` such
size-`2j` pair-unions, all distinct, so

> **`C(n/2, j) ≤ #{ S ⊆ μ_n : |S| = 2j ∧ Σ_{x∈S} x = 0 }`**.

Summed over `j` this recovers the total `2^{n/2} ≤ V_1`; the graded version additionally pins the
**even-size concentration** of the vanishing family (all pair-unions have even size `2j`).

Probe receipt: `scripts/probes/probe_graded_vanishing_lower.py` (exact, n = 4..12): the graded bound
holds at every grade, and is **TIGHT** (equality) at every grade for n ≤ 10 and at all but the
middle grade for n = 12 (where extra non-pair vanishers appear, V=24 > C(6,3)=20).  This matches the
prize-regime tightness: at `n = 2^a` Lam–Leung gives the matching upper `Z(t) = (1+t²)^{n/2}`.

## What is proved (axiom-clean)

- `gradedPairUnion_card` — the size-`2j` pair-unions are counted by `C(p, j)` (the `j`-subsets of the
  `p` pairs, each contributing both members ⟹ size `2j`).
- `card_le_gradedVanishing` — the headline: `C(p, j) ≤ #{ vanishing subsets of size 2j }`.

Reuses `AntipodalVanishingCountLower.sum_pairUnion_eq_zero` / `pairUnion` for the vanishing direction.

## Scope / honesty (rule 3, rule 6)

CHAR-0, NOT thinness-essential, NOT a CORE closure — the graded LOWER half of Lam–Leung.  It refines
the §6.5 supply profile (even-size concentration + per-grade binomial floor) but does not bound
`M(μ_n)`.  CORE stays OPEN.

Issue #444, §6.5 (graded lower half).
-/

set_option linter.unusedVariables false

namespace ArkLib.ProximityGap.GradedAntipodalVanishingLower

open Finset BigOperators
open ArkLib.ProximityGap.AntipodalVanishingCountLower

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-! ### Size of a pair-union: choosing `j` disjoint 2-element pairs gives a set of size `2j`. -/

/-- A union of `j` chosen pairs (each a 2-element set, pairwise disjoint) has card `2j`. -/
theorem pairUnion_card_eq_two_mul {p : ℕ} (pair : Fin p → Finset G)
    (hdisj : ∀ i j, i ≠ j → Disjoint (pair i) (pair j))
    (hcard : ∀ i, (pair i).card = 2)
    (T : Finset (Fin p)) :
    (pairUnion pair T).card = 2 * T.card := by
  unfold pairUnion
  rw [Finset.card_biUnion]
  · rw [Finset.sum_congr rfl (fun i _ => hcard i)]
    rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  · intro i _ j _ hij; exact hdisj i j hij

/-! ### The graded pair-union count is `C(p, j)`. -/

/-- The number of size-`2j` pair-unions equals `C(p, j)`: the pair-union map restricted to the
`j`-subsets of the `p` pairs is injective (it is injective on all of `Finset (Fin p)`), and its image
is exactly the size-`2j` pair-unions. -/
theorem gradedPairUnion_card {p : ℕ} (pair : Fin p → Finset G)
    (hdisj : ∀ i j, i ≠ j → Disjoint (pair i) (pair j))
    (hcard : ∀ i, (pair i).card = 2)
    (hne : ∀ i, (pair i).Nonempty)
    (j : ℕ) :
    ((Finset.univ.powersetCard j : Finset (Finset (Fin p))).image (pairUnion pair)).card
      = Nat.choose p j := by
  rw [Finset.card_image_of_injOn]
  · rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  · intro T₁ _ T₂ _ h
    exact pairUnion_injective pair hdisj hne h

/-! ### The headline graded lower bound. -/

variable [Fintype G]

/-- **`C(p, j) ≤ #{ vanishing subsets of size 2j }`.**  Each size-`2j` pair-union is a union of `j`
antipodal pairs, hence (a) has card `2j` and (b) vanishes (`sum_pairUnion_eq_zero`, `σ = neg`,
`f = id`).  There are `C(p, j)` distinct such unions, so the size-`2j` vanishing family has at least
`C(p, j)` members.  With `p = n/2` this is the graded lower half of Lam–Leung over `μ_n`. -/
theorem card_le_gradedVanishing {p : ℕ} (pair : Fin p → Finset G)
    (hdisj : ∀ i j, i ≠ j → Disjoint (pair i) (pair j))
    (hcard : ∀ i, (pair i).card = 2)
    (hne : ∀ i, (pair i).Nonempty)
    (σ : G → G)
    (hmap : ∀ i, ∀ x ∈ pair i, σ x ∈ pair i)
    (hinv : ∀ i, ∀ x ∈ pair i, σ (σ x) = x)
    (hnofix : ∀ i, ∀ x ∈ pair i, σ x ≠ x)
    (hanti : ∀ x : G, σ x = - x)
    (j : ℕ) :
    Nat.choose p j ≤
      (Finset.univ.filter
        (fun S : Finset G => S.card = 2 * j ∧ ∑ x ∈ S, x = 0)).card := by
  have hsub :
      ((Finset.univ.powersetCard j : Finset (Finset (Fin p))).image (pairUnion pair))
        ⊆ (Finset.univ.filter
            (fun S : Finset G => S.card = 2 * j ∧ ∑ x ∈ S, x = 0)) := by
    intro S hS
    simp only [Finset.mem_image, Finset.mem_powersetCard] at hS
    obtain ⟨T, ⟨_, hTcard⟩, rfl⟩ := hS
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · -- size is 2 * |T| = 2 * j
      rw [pairUnion_card_eq_two_mul pair hdisj hcard T, hTcard]
    · -- vanishes
      refine sum_pairUnion_eq_zero (pairUnion pair T) σ ?_ ?_ ?_ id ?_
      · intro x hx
        simp only [pairUnion, Finset.mem_biUnion] at hx ⊢
        obtain ⟨i, hiT, hxi⟩ := hx
        exact ⟨i, hiT, hmap i x hxi⟩
      · intro x hx
        simp only [pairUnion, Finset.mem_biUnion] at hx
        obtain ⟨i, hiT, hxi⟩ := hx
        exact hinv i x hxi
      · intro x hx
        simp only [pairUnion, Finset.mem_biUnion] at hx
        obtain ⟨i, hiT, hxi⟩ := hx
        exact hnofix i x hxi
      · intro x hx
        simp only [id_eq]; exact hanti x
  calc Nat.choose p j
      = ((Finset.univ.powersetCard j :
            Finset (Finset (Fin p))).image (pairUnion pair)).card :=
        (gradedPairUnion_card pair hdisj hcard hne j).symm
    _ ≤ _ := Finset.card_le_card hsub

/-! ### Non-vacuity witness (the graded bound is real).

`p = 1`, `j = 1` over `ZMod 5` with the single negation pair `{1, 4}` (size 2, `1+4=0`): the bound
gives `C(1,1) = 1 ≤ #{ size-2 vanishing subsets of ZMod 5 }`, discharged by `decide`. -/

/-- Concrete witness: `C(1,1) = 1 ≤ #{ size-2 vanishing subsets of ZMod 5 }`. -/
example :
    Nat.choose 1 1 ≤
      (Finset.univ.filter
        (fun S : Finset (ZMod 5) => S.card = 2 * 1 ∧ ∑ x ∈ S, x = 0)).card := by
  refine card_le_gradedVanishing
    (fun _ => ({1, 4} : Finset (ZMod 5)))
    ?_ ?_ ?_ (fun x => -x) ?_ ?_ ?_ (fun x => rfl) 1
  · intro i j hij; exact absurd (Subsingleton.elim i j) hij
  · intro i; simp only; decide
  · intro i; refine ⟨(1 : ZMod 5), ?_⟩; simp only; decide
  · intro i x hx; simp only at hx ⊢; fin_cases hx <;> decide
  · intro i x hx; simp only at hx ⊢; fin_cases hx <;> decide
  · intro i x hx; simp only at hx ⊢; fin_cases hx <;> decide

end ArkLib.ProximityGap.GradedAntipodalVanishingLower

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.GradedAntipodalVanishingLower.gradedPairUnion_card
#print axioms ArkLib.ProximityGap.GradedAntipodalVanishingLower.card_le_gradedVanishing
