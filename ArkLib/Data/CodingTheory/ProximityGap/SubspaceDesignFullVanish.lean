/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.SubspaceDesign
import ArkLib.Data.Probability.Instances

/-!
# A τ-subspace-design has few fully-vanishing coordinates (issue #389, GG25 §4.3 toward B2)

The structural fact at the heart of why subspace-design codes list-decode (and of the GG25 §4.3
pruning toward curve-decodability): for a `τ`-subspace-design code `C` (GG25 Def 2.17 =
`IsSubspaceDesign`) and **any** dimension-`r` subspace `A ≤ C`, the number of coordinates `i` at
which **all** of `A` vanishes (`A ≤ ker projᵢ`, i.e. every `a ∈ A` has `aᵢ = 0`) is at most
`τ(r)·n`.

`subspaceDesign_fullVanish_card_le`. The proof is the design inequality read off on the
fully-vanishing coordinates: each such `i` has `A ⊓ ker projᵢ = A`, contributing the full
`finrank A = r` to `∑ᵢ finrank(A ⊓ ker projᵢ) ≤ r·τ(r)·n`; dividing by `r` gives the count bound.
A small dimension-`r` subspace can therefore be *pinned down* by sampling a few coordinates outside
this `τ(r)`-fraction — the separation mechanism `[KRSW23, Tam24]`/GG25 use for line-decodability.

Axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

open Finset CodingTheory
open scoped ProbabilityTheory NNReal

namespace ProximityGap

variable {ι : Type} [Fintype ι] [Nonempty ι] {F : Type} [Field F]

open Classical in
/-- **Few fully-vanishing coordinates** for a `τ`-subspace-design. If `A ≤ C` has dimension `r ≥ 1`,
the coordinates `i` where every codeword of `A` vanishes (`A ≤ ker projᵢ`) number at most `τ(r)·n`. -/
theorem subspaceDesign_fullVanish_card_le {s : ℕ} {τ : ℕ → ℝ}
    {C : Submodule F (ι → Fin s → F)} (h : IsSubspaceDesign s τ C)
    {r : ℕ} (hr : 1 ≤ r) {A : Submodule F (ι → Fin s → F)} (hAC : A ≤ C)
    (hrank : Module.finrank F A = r) :
    ((univ.filter (fun i : ι => A ≤ LinearMap.ker
        (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i))).card : ℝ)
      ≤ τ r * Fintype.card ι := by
  classical
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hdesign := h r A hAC hrank.le
  rw [div_le_iff₀ hn] at hdesign
  set full := univ.filter (fun i : ι => A ≤ LinearMap.ker
      (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) with hfull
  -- each fully-vanishing coordinate contributes the full `r` to the design sum
  have hlb : (r : ℝ) * full.card
      ≤ ∑ i : ι, (Module.finrank F (↥(A ⊓ LinearMap.ker
          (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i))) : ℝ) := by
    have hfull_eq : ∀ i ∈ full, (Module.finrank F (↥(A ⊓ LinearMap.ker
        (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i))) : ℝ) = (r : ℝ) := by
      intro i hi
      rw [hfull, mem_filter] at hi
      have heq : A ⊓ LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i) = A :=
        inf_eq_left.mpr hi.2
      rw [heq]
      exact_mod_cast hrank
    calc (r : ℝ) * full.card
        = ∑ _i ∈ full, (r : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ = ∑ i ∈ full, (Module.finrank F (↥(A ⊓ LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i))) : ℝ) :=
          (Finset.sum_congr rfl hfull_eq).symm
      _ ≤ ∑ i : ι, (Module.finrank F (↥(A ⊓ LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i))) : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
          intro i _ _; positivity
  -- combine with the (division-cleared) design inequality and cancel `r`
  have hcomb : (r : ℝ) * full.card ≤ (r : ℝ) * (τ r * Fintype.card ι) := by
    calc (r : ℝ) * full.card
        ≤ ∑ i : ι, (Module.finrank F (↥(A ⊓ LinearMap.ker
            (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i))) : ℝ) := hlb
      _ ≤ (Module.finrank F A * τ r) * Fintype.card ι := hdesign
      _ = (r : ℝ) * (τ r * Fintype.card ι) := by rw [hrank]; ring
  exact le_of_mul_le_mul_left hcomb hrpos

open Classical in
/-- **Large union-support (dual form).** A dimension-`r` subspace `A ≤ C` of a `τ`-subspace-design
is nonzero on at least `(1 − τ(r))·n` coordinates: at most `τ(r)·n` coordinates kill all of `A`.
This is the form the list-decoding/pruning argument consumes (a small subspace is "spread out"). -/
theorem subspaceDesign_support_card_ge {s : ℕ} {τ : ℕ → ℝ}
    {C : Submodule F (ι → Fin s → F)} (h : IsSubspaceDesign s τ C)
    {r : ℕ} (hr : 1 ≤ r) {A : Submodule F (ι → Fin s → F)} (hAC : A ≤ C)
    (hrank : Module.finrank F A = r) :
    ((1 - τ r) * Fintype.card ι : ℝ)
      ≤ ((univ.filter (fun i : ι => ¬ (A ≤ LinearMap.ker
          (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)))).card : ℝ) := by
  have hfv := subspaceDesign_fullVanish_card_le h hr hAC hrank
  have hsplit : (univ.filter (fun i : ι => A ≤ LinearMap.ker
        (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i))).card
      + (univ.filter (fun i : ι => ¬ (A ≤ LinearMap.ker
        (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)))).card
      = Fintype.card ι := by
    rw [Finset.filter_card_add_filter_neg_card_eq_card]; exact Finset.card_univ
  have hsplitℝ : ((univ.filter (fun i : ι => A ≤ LinearMap.ker
        (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i))).card : ℝ)
      + ((univ.filter (fun i : ι => ¬ (A ≤ LinearMap.ker
        (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)))).card : ℝ)
      = (Fintype.card ι : ℝ) := by exact_mod_cast hsplit
  have hexp : (1 - τ r) * (Fintype.card ι : ℝ)
      = (Fintype.card ι : ℝ) - τ r * Fintype.card ι := by ring
  rw [hexp]
  linarith [hfv, hsplitℝ]

open Classical in
/-- **Design → probability bridge.** A uniformly random coordinate does not fully-vanish a
dimension-`r` subspace `A ≤ C` of a `τ`-subspace-design with probability at least `1 − τ(r)` — the
single-step separation guarantee the GG25 §4.3 / `[KRSW23, Tam24]` pruning iterates (combining
`subspaceDesign_support_card_ge` with the uniform-coordinate law). -/
theorem subspaceDesign_random_coord_support_prob {s : ℕ} {τ : ℕ → ℝ}
    {C : Submodule F (ι → Fin s → F)} (h : IsSubspaceDesign s τ C)
    {r : ℕ} (hr : 1 ≤ r) {A : Submodule F (ι → Fin s → F)} (hAC : A ≤ C)
    (hrank : Module.finrank F A = r) :
    (1 - τ r : ℝ)
      ≤ (Pr_{ let i ←$ᵖ ι }[ ¬ (A ≤ LinearMap.ker
          (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) ]).toReal := by
  have hsupp := subspaceDesign_support_card_ge h hr hAC hrank
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.toReal_div, ENNReal.coe_toReal, NNReal.coe_div, NNReal.coe_natCast]
  rw [le_div_iff₀ hn]
  exact hsupp

end ProximityGap

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.subspaceDesign_fullVanish_card_le
#print axioms ProximityGap.subspaceDesign_support_card_ge
#print axioms ProximityGap.subspaceDesign_random_coord_support_prob
