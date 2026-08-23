/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.SubspaceDesign
import ArkLib.Data.CodingTheory.ListDecoding.FPRUNEPotential
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# FPRUNE good-coordinate existence (Chen–Zhang 2025 / arXiv 2512.08017, Lemma 3.4 existence half)

The polynomial list-decoding bound for subspace-design codes is proven via the `FPRUNE`
algorithm, which recursively samples a **good** coordinate `i` — one that strictly drops the
weighted dimension `wt_η(ℋ) := dim ℋ + η` by a factor `(1 - η')` — until the ambient space
collapses to `{0}`. For the recursion to be well-defined (and to terminate), at each positive
dimension there must *exist* such a good coordinate.

The combinatorial heart that the in-tree FPRUNE potential bricks consume — `fprune_one_step`
(Lemma 3.4 inequality) and `fprune_expectation_lower_of_branch` (Lemma 3.5 assembly,
`ListDecoding/FPRUNEPotential.lean`) — currently **take the nonempty good-coordinate set
`J.Nonempty` as a hypothesis**. This file discharges that existence obligation directly from
the subspace-design coordinate-dimension budget (`IsSubspaceDesign`, ABF26 Definition 2.16 /
CZ25 Definition 6):

* `good_filter_nonempty_of_weight_budget` — the abstract averaging principle: a finite family
  of reals with average below a threshold has a member below the threshold.
* `card_good_ge_of_weight_budget` — the quantitative count form: at least `n·(1 - B/θ)`
  coordinates are good, the mass bound FPRUNE's sampling step consumes.
* `good_coord_exists_of_design` — the FPRUNE good set `{i | dim ℋ_i + η ≤ (1-η')(r+η)}` is
  nonempty, because the design budget forces `∑_i (dim ℋ_i + η) ≤ (r·τ(r) + η)·n`, which lies
  below `(1-η')(r+η)·n` exactly when `r·τ(r) + η < (1-η')(r+η)` (the capacity regime).
* `fprune_one_step_of_design` — plugs that nonempty good-coordinate set into
  `fprune_one_step`, eliminating the raw `J.Nonempty` hypothesis for the design-instantiated
  one-step potential inequality.
* `card_good_coord_ge_of_design` — the quantitative design-code count: `≥ n·(1 - (r·τ(r)+η)/θ)`
  good coordinates, the FPRUNE sampling mass (positive in the capacity regime).
* `exists_good_coord_dim_lt_of_design` — packages a good coordinate together with the **strict
  dimension drop** `dim ℋ_i < r` (using `0 < η'`), the well-foundedness datum the FPRUNE
  recursion needs to make progress.

Here `ℋ_i := ℋ ⊓ ker(eval_i)` is the subspace of `ℋ` whose codewords vanish at position `i`,
matching `IsSubspaceDesign`. Everything is axiom-clean (`[propext, Classical.choice,
Quot.sound]`).

## References

- [CZ25] Chen–Zhang. Thm B.5 / Lemmas 3.4–3.5 (subspace-design route to capacity list decoding),
  arXiv 2512.08017.
- [ABF26] Arnon-Boneh-Fenzi. *Open Problems in List Decoding and Correlated Agreement*, §2.5.
-/

set_option linter.unusedSectionVars false

open Finset
open scoped NNReal

namespace CodingTheory.ListDecoding

/-- **Abstract good-coordinate existence (averaging / Markov).** If a finite family of reals
`a : ι → ℝ` satisfies a weight budget `∑ i, a i ≤ n·B` with `B < θ`, then the good set
`{i | a i ≤ θ}` is nonempty: were every coordinate `> θ`, the sum would exceed `n·θ > n·B`,
contradicting the budget. -/
theorem good_filter_nonempty_of_weight_budget {ι : Type*} [Fintype ι] [Nonempty ι]
    (a : ι → ℝ) (θ B : ℝ)
    (hbudget : ∑ i, a i ≤ (Fintype.card ι : ℝ) * B) (hB : B < θ) :
    (univ.filter (fun i => a i ≤ θ)).Nonempty := by
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hempty
  have hall : ∀ i, θ < a i := fun i => not_le.mp (hempty (Finset.mem_univ i))
  have hcardpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsum_gt : (Fintype.card ι : ℝ) * θ < ∑ i, a i := by
    have h : ∑ _i : ι, θ < ∑ i, a i :=
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => hall i)
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h
  have hcontra : (Fintype.card ι : ℝ) * θ < (Fintype.card ι : ℝ) * B :=
    lt_of_lt_of_le hsum_gt hbudget
  have h2 : (Fintype.card ι : ℝ) * B < (Fintype.card ι : ℝ) * θ :=
    mul_lt_mul_of_pos_left hB hcardpos
  linarith [hcontra, h2]

/-- **Quantitative good-coordinate count (averaging / Markov, count form).** With nonnegative
weights `a` and budget `∑ a ≤ n·B`, at least `n - n·B/θ = n·(1 - B/θ)` coordinates are good
(`a i ≤ θ`). This is the quantitative companion to `good_filter_nonempty_of_weight_budget`: it
is the count FPRUNE's sampling step needs, since the good coordinates must carry enough weight
for the recursion's probability distribution. (Each bad coordinate has `a i > θ`, so the bad
set contributes `≥ #bad · θ` to the budget `≤ n·B`, giving `#bad ≤ n·B/θ`.) -/
theorem card_good_ge_of_weight_budget {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (θ B : ℝ) (hθ : 0 < θ)
    (hbudget : ∑ i, a i ≤ (Fintype.card ι : ℝ) * B) :
    (Fintype.card ι : ℝ) - (Fintype.card ι : ℝ) * B / θ ≤
      ((univ.filter (fun i => a i ≤ θ)).card : ℝ) := by
  classical
  have hsplit :
      ((univ.filter (fun i => a i ≤ θ)).card : ℝ)
        + ((univ.filter (fun i => ¬ a i ≤ θ)).card : ℝ)
        = (Fintype.card ι : ℝ) := by
    rw [← Nat.cast_add, Finset.card_filter_add_card_filter_not, Finset.card_univ]
  have hbad_weight : ((univ.filter (fun i => ¬ a i ≤ θ)).card : ℝ) * θ
      ≤ ∑ i ∈ univ.filter (fun i => ¬ a i ≤ θ), a i := by
    have h := Finset.card_nsmul_le_sum (univ.filter (fun i => ¬ a i ≤ θ)) a θ
      (fun i hi => le_of_lt (not_le.mp (Finset.mem_filter.mp hi).2))
    simpa [nsmul_eq_mul] using h
  have hbad_le_total : ∑ i ∈ univ.filter (fun i => ¬ a i ≤ θ), a i ≤ ∑ i, a i :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => ha i)
  have hbad_bound : ((univ.filter (fun i => ¬ a i ≤ θ)).card : ℝ) * θ
      ≤ (Fintype.card ι : ℝ) * B :=
    le_trans hbad_weight (le_trans hbad_le_total hbudget)
  have hbad_div : ((univ.filter (fun i => ¬ a i ≤ θ)).card : ℝ)
      ≤ (Fintype.card ι : ℝ) * B / θ := by
    rw [le_div_iff₀ hθ]; exact hbad_bound
  linarith [hsplit, hbad_div]

variable {ι : Type} [Fintype ι] [Nonempty ι]
variable {F : Type} [Field F]

/-- **FPRUNE good-coordinate existence from the subspace-design budget (CZ25 Lemma 3.4,
existence half).** Let `C` be a `τ`-subspace-design code, and `ℋ ≤ C` a subspace of dimension
`r`. Write `ℋ_i := ℋ ⊓ ker(eval_i)` and `wt_η(X) := dim X + η`. If the capacity condition
`r·τ(r) + η < (1-η')·(r+η)` holds, then there is a coordinate `i` that is **good** for FPRUNE,
namely `wt_η(ℋ_i) ≤ (1-η')·wt_η(ℋ)`, i.e. `dim ℋ_i + η ≤ (1-η')·(r+η)`.

This discharges the existence content that `fprune_one_step` and
`fprune_expectation_lower_of_branch` currently take as the hypothesis `J.Nonempty`. The total
FPRUNE weight is `∑_i (dim ℋ_i + η) = (∑_i dim ℋ_i) + nη ≤ (r·τ(r) + η)·n` by the
subspace-design coordinate-dimension budget (Definition 2.16), so averaging
(`good_filter_nonempty_of_weight_budget`) forces a good coordinate to exist. -/
theorem good_coord_exists_of_design
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F)) (h : IsSubspaceDesign s τ C)
    (η η' : ℝ) (ℋ : Submodule F (ι → Fin s → F)) (hℋ : ℋ ≤ C)
    (r : ℕ) (hr : Module.finrank F ℋ = r)
    (hcap : (r : ℝ) * τ r + η < (1 - η') * ((r : ℝ) + η)) :
    (univ.filter (fun i =>
      (Module.finrank F (↥(ℋ ⊓
          (LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
          Submodule F (ι → Fin s → F))) : ℝ) + η
        ≤ (1 - η') * ((r : ℝ) + η))).Nonempty := by
  refine good_filter_nonempty_of_weight_budget
    (fun i => (Module.finrank F (↥(ℋ ⊓
        (LinearMap.ker
          (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
        Submodule F (ι → Fin s → F))) : ℝ) + η)
    ((1 - η') * ((r : ℝ) + η)) ((r : ℝ) * τ r + η) ?_ hcap
  -- budget: `∑_i (dim ℋ_i + η) ≤ n·(r·τ(r) + η)`
  have hdesign := h r ℋ hℋ hr.le
  rw [hr] at hdesign
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hn] at hdesign
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hexp : (Fintype.card ι : ℝ) * ((r : ℝ) * τ r + η)
      = (r : ℝ) * τ r * (Fintype.card ι : ℝ) + (Fintype.card ι : ℝ) * η := by ring
  rw [hexp]
  linarith [hdesign]

/-- **Design-instantiated FPRUNE one-step inequality.** The subspace-design budget supplies the
nonempty good-coordinate set required by `fprune_one_step`, so the one-step potential inequality
can be stated directly from the design capacity condition, without taking `J.Nonempty` as a raw
hypothesis. -/
theorem fprune_one_step_of_design
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F)) (h : IsSubspaceDesign s τ C)
    (η η' : ℝ) (hη : 0 < η) (hη' : 0 ≤ 1 - η')
    (ℋ : Submodule F (ι → Fin s → F)) (hℋ : ℋ ≤ C)
    (r : ℕ) (hr : Module.finrank F ℋ = r)
    (hcap : (r : ℝ) * τ r + η < (1 - η') * ((r : ℝ) + η)) :
    let d : ι → ℕ := fun i => Module.finrank F (↥(ℋ ⊓
      (LinearMap.ker
        (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
      Submodule F (ι → Fin s → F)))
    let J : Finset ι := univ.filter (fun i => (d i : ℝ) + η ≤ (1 - η') * ((r : ℝ) + η))
    η / ((r : ℕ) + η) ≤
      ∑ j ∈ J, ((((d j : ℝ) + η) * (1 - η')) / (∑ k ∈ J, ((d k : ℝ) + η)))
                  * (η / ((d j : ℕ) + η)) := by
  classical
  let d : ι → ℕ := fun i => Module.finrank F (↥(ℋ ⊓
    (LinearMap.ker
      (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
    Submodule F (ι → Fin s → F)))
  let J : Finset ι := univ.filter (fun i => (d i : ℝ) + η ≤ (1 - η') * ((r : ℝ) + η))
  change η / ((r : ℕ) + η) ≤
      ∑ j ∈ J, ((((d j : ℝ) + η) * (1 - η')) / (∑ k ∈ J, ((d k : ℝ) + η)))
                  * (η / ((d j : ℕ) + η))
  have hJ : J.Nonempty := by
    simpa [J, d] using good_coord_exists_of_design s τ C h η η' ℋ hℋ r hr hcap
  have hgood : ∀ j ∈ J, (d j : ℝ) + η ≤ (1 - η') * ((r : ℝ) + η) := by
    intro j hj
    simpa [J] using hj
  exact fprune_one_step η η' hη hη' r J d hJ hgood

/-- **Quantitative FPRUNE good-coordinate count for a subspace-design code.** Under the same
setup as `good_coord_exists_of_design` (with `0 < η` and `0 < (1-η')(r+η)`), at least
`n - n·(r·τ(r)+η)/((1-η')(r+η))` coordinates are FPRUNE-good. This is the design-code count
form of `card_good_ge_of_weight_budget`: it gives the *mass* of good coordinates the FPRUNE
sampling step distributes over (positive precisely in the capacity regime
`r·τ(r)+η < (1-η')(r+η)`). -/
theorem card_good_coord_ge_of_design
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F)) (h : IsSubspaceDesign s τ C)
    (η η' : ℝ) (hη : 0 < η) (ℋ : Submodule F (ι → Fin s → F)) (hℋ : ℋ ≤ C)
    (r : ℕ) (hr : Module.finrank F ℋ = r)
    (hθ : 0 < (1 - η') * ((r : ℝ) + η)) :
    (Fintype.card ι : ℝ)
        - (Fintype.card ι : ℝ) * ((r : ℝ) * τ r + η) / ((1 - η') * ((r : ℝ) + η))
      ≤ ((univ.filter (fun i =>
          (Module.finrank F (↥(ℋ ⊓
              (LinearMap.ker
                (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
              Submodule F (ι → Fin s → F))) : ℝ) + η
            ≤ (1 - η') * ((r : ℝ) + η))).card : ℝ) := by
  refine card_good_ge_of_weight_budget
    (fun i => (Module.finrank F (↥(ℋ ⊓
        (LinearMap.ker
          (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
        Submodule F (ι → Fin s → F))) : ℝ) + η)
    (fun i => add_nonneg (Nat.cast_nonneg _) hη.le)
    ((1 - η') * ((r : ℝ) + η)) ((r : ℝ) * τ r + η) hθ ?_
  -- budget: `∑_i (dim ℋ_i + η) ≤ n·(r·τ(r) + η)`  (same design budget as `good_coord_exists`)
  have hdesign := h r ℋ hℋ hr.le
  rw [hr] at hdesign
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hn] at hdesign
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hexp : (Fintype.card ι : ℝ) * ((r : ℝ) * τ r + η)
      = (r : ℝ) * τ r * (Fintype.card ι : ℝ) + (Fintype.card ι : ℝ) * η := by ring
  rw [hexp]
  linarith [hdesign]

/-- **A good coordinate strictly drops the dimension (FPRUNE progress / well-foundedness).**
Under the capacity condition, the design supplies a coordinate `i` that is FPRUNE-good
(`dim ℋ_i + η ≤ (1-η')(r+η)`) **and** strictly lowers the dimension, `dim ℋ_i < r`. The strict
drop is the well-foundedness datum the FPRUNE recursion needs: each step works inside a space of
strictly smaller dimension, so the recursion terminates. It follows from the good predicate
because `(1-η')(r+η) < r+η` when `0 < η'` and `0 < η` (so `0 < r+η`). -/
theorem exists_good_coord_dim_lt_of_design
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F)) (h : IsSubspaceDesign s τ C)
    (η η' : ℝ) (hη : 0 < η) (hη' : 0 < η')
    (ℋ : Submodule F (ι → Fin s → F)) (hℋ : ℋ ≤ C)
    (r : ℕ) (hr : Module.finrank F ℋ = r)
    (hcap : (r : ℝ) * τ r + η < (1 - η') * ((r : ℝ) + η)) :
    ∃ i, (Module.finrank F (↥(ℋ ⊓
          (LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
          Submodule F (ι → Fin s → F))) : ℝ) + η ≤ (1 - η') * ((r : ℝ) + η) ∧
      Module.finrank F (↥(ℋ ⊓
          (LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
          Submodule F (ι → Fin s → F))) < r := by
  obtain ⟨i, hi⟩ := good_coord_exists_of_design s τ C h η η' ℋ hℋ r hr hcap
  rw [Finset.mem_filter] at hi
  refine ⟨i, hi.2, ?_⟩
  -- `dim ℋ_i + η ≤ (1-η')(r+η) < (r+η)`  (since `η'·(r+η) > 0`), hence `dim ℋ_i < r`.
  have hrη : (0 : ℝ) < (r : ℝ) + η := by positivity
  have hstrict : (1 - η') * ((r : ℝ) + η) < (r : ℝ) + η := by nlinarith [mul_pos hη' hrη]
  have hlt : (Module.finrank F (↥(ℋ ⊓
          (LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
          Submodule F (ι → Fin s → F))) : ℝ) < (r : ℝ) := by linarith [hi.2, hstrict]
  exact_mod_cast hlt

end CodingTheory.ListDecoding

/-! ### `#print axioms` verification anchors -/

#print axioms CodingTheory.ListDecoding.good_filter_nonempty_of_weight_budget
#print axioms CodingTheory.ListDecoding.card_good_ge_of_weight_budget
#print axioms CodingTheory.ListDecoding.good_coord_exists_of_design
#print axioms CodingTheory.ListDecoding.fprune_one_step_of_design
#print axioms CodingTheory.ListDecoding.card_good_coord_ge_of_design
#print axioms CodingTheory.ListDecoding.exists_good_coord_dim_lt_of_design
