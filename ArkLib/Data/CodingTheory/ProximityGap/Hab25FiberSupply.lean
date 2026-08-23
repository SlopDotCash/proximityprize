/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25K4FiberReduction

/-!
# The good-`x₀` fiber supply: one fiber point serves every factor

The per-component K4 reduction (`Hab25K4FiberReduction.lean`) is parameterized by a
fiber point `x₀` with `fiberAt x₀ R ≠ 0`. This file supplies it:

* `exists_fiberAt_ne_zero` — over a field larger than the `X`-degree, **some `x₀` keeps
  the fiber alive**: a nonzero coefficient survives evaluation at all but `≤ deg_X`
  points (the detecting polynomial trick, one `Z`-coefficient down);
* `fiberAt_ne_zero_of_dvd` — fiber nonvanishing **passes to every factor**: one good
  `x₀` for the interpolant `Q₀` serves all its irreducible factors `R` simultaneously
  (the fiber map is a ring hom, and divisors of nonzero elements are nonzero).

With this, all hypotheses of `cell_card_le_of_component_K4` except the per-component
capture itself (`hK4H`, the BCIKS20 C5.8/C5.9 kernel) have in-tree producers: `T₀` from
the graded Z-budget via `card_fiber_specialization_collapse_le`, and `x₀` from here.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Polynomial Polynomial.Bivariate Finset

attribute [local instance] Classical.propDecidable

variable {F₀ : Type} [Field F₀]

/-- **The good-`x₀` existence**: if the field is larger than the `X`-degree of every
`Y`-coefficient, some `x₀` keeps the fiber alive. -/
theorem exists_fiberAt_ne_zero [Fintype F₀] {R : (F₀[X])[X][Y]} (hR : R ≠ 0) {B : ℕ}
    (hdegX : ∀ j : ℕ, (R.coeff j).natDegree ≤ B) (hcard : B < Fintype.card F₀) :
    ∃ x₀ : F₀, fiberAt x₀ R ≠ 0 := by
  classical
  -- a surviving coefficient, two levels down
  obtain ⟨j₀, hj₀⟩ := Polynomial.support_nonempty.mpr hR
  set c : (F₀[X])[X] := R.coeff j₀ with hc
  have hc0 : c ≠ 0 := Polynomial.mem_support_iff.mp hj₀
  obtain ⟨a₀, ha₀⟩ := Polynomial.support_nonempty.mpr hc0
  have ha₀' : c.coeff a₀ ≠ 0 := Polynomial.mem_support_iff.mp ha₀
  obtain ⟨t₀, ht₀⟩ := Polynomial.support_nonempty.mpr ha₀'
  have ht₀' : (c.coeff a₀).coeff t₀ ≠ 0 := Polynomial.mem_support_iff.mp ht₀
  -- the detecting polynomial: the `Z^t₀`-slice of `c`, as a polynomial in `x₀`
  set p : F₀[X] := ∑ a ∈ Finset.range (c.natDegree + 1),
    Polynomial.C ((c.coeff a).coeff t₀) * Polynomial.X ^ a with hp
  have hpcoeff : ∀ a, p.coeff a =
      if a ∈ Finset.range (c.natDegree + 1) then (c.coeff a).coeff t₀ else 0 := by
    intro a
    rw [hp, Polynomial.finset_sum_coeff]
    by_cases hmem : a ∈ Finset.range (c.natDegree + 1)
    · rw [if_pos hmem, Finset.sum_eq_single a]
      · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
      · intro b _ hne
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
          if_neg (fun hc' => hne hc'.symm), mul_zero]
      · intro habs
        exact absurd hmem habs
    · rw [if_neg hmem, Finset.sum_eq_zero]
      intro b hb
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      have hba : b ≠ a := by
        intro hba
        exact hmem (hba ▸ hb)
      rw [if_neg (fun hc' => hba hc'.symm), mul_zero]
  have hp0 : p ≠ 0 := by
    intro habs
    apply ht₀'
    have := hpcoeff a₀
    rw [habs, Polynomial.coeff_zero,
      if_pos (Finset.mem_range.mpr (Nat.lt_succ_of_le (Polynomial.le_natDegree_of_ne_zero
        ha₀')))] at this
    exact this.symm
  have hpdeg : p.natDegree ≤ B := by
    refine le_trans (Polynomial.natDegree_sum_le_of_forall_le _ _ fun a ha => ?_)
      (le_refl B) |>.trans (le_refl B)
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    refine le_trans (Polynomial.natDegree_X_pow_le _) ?_
    have haB : a ≤ c.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
    exact le_trans haB (hdegX j₀)
  -- the detecting identity: `p(x₀)` is the `Z^t₀`-coefficient of `c(C x₀)`
  have hdetect : ∀ x₀ : F₀, (c.eval (Polynomial.C x₀)).coeff t₀ = p.eval x₀ := by
    intro x₀
    rw [Polynomial.eval_eq_sum_range, Polynomial.finset_sum_coeff, hp,
      Polynomial.eval_finset_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Polynomial.C_pow, Polynomial.coeff_mul_C, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  -- a point avoiding the `≤ B` roots of `p`
  have hex : ∃ x₀ : F₀, p.eval x₀ ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hsub : (Finset.univ : Finset F₀) ⊆ p.roots.toFinset := by
      intro x _
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0]
      exact hall x
    have h1 : Fintype.card F₀ ≤ p.roots.toFinset.card := by
      rw [← Finset.card_univ]
      exact Finset.card_le_card hsub
    have h2 : p.roots.toFinset.card ≤ p.natDegree :=
      le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' _)
    omega
  obtain ⟨x₀, hx₀⟩ := hex
  refine ⟨x₀, fun habs => hx₀ ?_⟩
  have hzero : (fiberAt x₀ R).coeff j₀ = 0 := by
    rw [habs, Polynomial.coeff_zero]
  rw [fiberAt, Polynomial.coe_mapRingHom, Polynomial.coeff_map,
    Polynomial.coe_evalRingHom] at hzero
  rw [← hdetect x₀, hzero, Polynomial.coeff_zero]

/-- **One good `x₀` serves every factor**: the fiber map is a ring hom, so fiber
nonvanishing passes from the interpolant to each of its divisors. -/
theorem fiberAt_ne_zero_of_dvd {R Q₀ : (F₀[X])[X][Y]} (hdvd : R ∣ Q₀) (x₀ : F₀)
    (hQ : fiberAt x₀ Q₀ ≠ 0) : fiberAt x₀ R ≠ 0 := by
  intro hR0
  apply hQ
  obtain ⟨c, hc⟩ := hdvd
  rw [hc, map_mul, hR0, zero_mul]

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms exists_fiberAt_ne_zero
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms fiberAt_ne_zero_of_dvd
