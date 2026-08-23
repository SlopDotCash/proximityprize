/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSIntegralFactorAssignment

/-!
# The x₀-fiber component pigeonhole (BCIKS20 Claim 5.7, the counting half)

The K4 lane receives cells `E` of scalars whose matching factors divide one specialized
irreducible factor: `∀ γ ∈ E, (Y − C (P γ)) ∣ R|_{Z:=γ}`. The Steps 5–7 capture works at
a good fiber `X := x₀`: each scalar contributes the planar point `(γ, P γ(x₀))` on the
fiber curve `R(x₀, Y, Z) = 0`, and the argument proceeds on the **most common irreducible
component** of that curve. This file proves that reduction — the *counting half* of
BCIKS20 Claim 5.7:

* `fiber_specialization_commute` — the two specialization orders agree:
  `(R|_{Z:=γ})|_{X:=x₀} = (R|_{X:=x₀})|_{Z:=γ}` (via `Polynomial.hom_eval₂`);
* `fiber_point_vanishes` — each cell scalar's fiber value is a root of the specialized
  fiber curve;
* `unit_shape_two` — units of `F[Z][Y]` are nonzero field constants (immune to
  `Z`-specialization), so the factorization of the fiber curve survives specializing;
* **`exists_fiber_component_pigeonhole`** — the cell splits along the irreducible
  components of the fiber curve (plus one degenerate class `R(x₀,·)|_{Z:=γ} = 0`), and
  some class carries at least a `1/(#factors+1)` fraction: a sub-cell `E' ⊆ E` with
  `|E| ≤ |E'| · (Ω(fiber) + 2)` whose members **all vanish on one irreducible component**
  `H` (or all degenerate — the branch the Z-degree budget kills).

The conclusion uses only *multiset* membership and the multiset factor count
`Ω = (factors …).card` — instance-free, safe for the rich-context K4 consumers.
What remains of Claim 5.7 downstream is the Step-6 input: many points of `E'` on one
irreducible `H(Y,Z)` force the Hensel branch data (the `#138`/`#139` kernel).

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial Polynomial.Bivariate

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

attribute [local instance] Classical.propDecidable

variable {F₀ : Type} [Field F₀]

/-- The mid-variable fiber map `X := x₀`: `F₀[Z][X][Y] → F₀[Z][Y]`, keeping `Z` and `Y`. -/
noncomputable def fiberAt (x₀ : F₀) : (F₀[X])[X][Y] →+* F₀[X][Y] :=
  Polynomial.mapRingHom (Polynomial.evalRingHom (Polynomial.C x₀ : F₀[X]))

/-- **The two specialization orders agree**: killing `Z` at `γ` then `X` at `x₀` equals
taking the `x₀`-fiber then killing `Z` at `γ`. -/
theorem fiber_specialization_commute (R : (F₀[X])[X][Y]) (x₀ γ : F₀) :
    (R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))).map
        (Polynomial.evalRingHom x₀) =
      (fiberAt x₀ R).map (Polynomial.evalRingHom γ) := by
  have hcomp : (Polynomial.evalRingHom x₀).comp
      (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) =
      (Polynomial.evalRingHom γ).comp
        (Polynomial.evalRingHom (Polynomial.C x₀ : F₀[X])) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp
    · simp
  rw [fiberAt, Polynomial.coe_mapRingHom, Polynomial.map_map, Polynomial.map_map, hcomp]

/-- **Each cell scalar's fiber value is a root of the specialized fiber curve**: from
`(Y − C (P γ)) ∣ R|_{Z:=γ}`, the value `P γ(x₀)` satisfies
`((fiberAt x₀ R)|_{Z:=γ}).eval (P γ(x₀)) = 0`. -/
theorem fiber_point_vanishes {R : (F₀[X])[X][Y]} {x₀ γ : F₀} {p : F₀[X]}
    (hdvd : (Polynomial.X - Polynomial.C p) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) :
    (((fiberAt x₀ R).map (Polynomial.evalRingHom γ)).eval (p.eval x₀)) = 0 := by
  have hroot : Polynomial.eval p
      (R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) = 0 := by
    rw [← Polynomial.dvd_iff_isRoot.mp hdvd]
  rw [← fiber_specialization_commute]
  have h := Polynomial.eval₂_at_apply
    (p := R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)))
    (Polynomial.evalRingHom x₀) p
  rw [Polynomial.coe_evalRingHom] at h
  rw [Polynomial.eval_map, h, hroot, Polynomial.eval_zero]

/-- Units of `F₀[Z][Y]` are nonzero field constants — two applications of
`Polynomial.isUnit_iff`. -/
lemma unit_shape_two {w : F₀[X][Y]} (hw : IsUnit w) :
    ∃ c : F₀, c ≠ 0 ∧ w = Polynomial.C (Polynomial.C c) := by
  obtain ⟨v, hvu, hv⟩ := Polynomial.isUnit_iff.mp hw
  obtain ⟨c, hcu, hc⟩ := Polynomial.isUnit_iff.mp hvu
  exact ⟨c, hcu.ne_zero, by rw [← hv, ← hc]⟩

/-- **Root capture by an irreducible factor of the fiber curve.** If the specialized
fiber curve is nonzero at `γ` and vanishes at `y`, then some irreducible factor of the
fiber curve specializes to vanish at `y` — the unit is a field constant and never
vanishes. -/
theorem exists_factor_root {G : F₀[X][Y]} (hG : G ≠ 0) (γ y : F₀)
    (h0 : (G.map (Polynomial.evalRingHom γ)).eval y = 0) :
    ∃ H, H ∈ UniqueFactorizationMonoid.factors G ∧
      ((H.map (Polynomial.evalRingHom γ)).eval y = 0) := by
  classical
  obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod (a := G) hG
  obtain ⟨c, hc0, hc⟩ := unit_shape_two u.isUnit
  -- evaluate the factorization at `(γ, y)`
  set ev : F₀[X][Y] →+* F₀ :=
    (Polynomial.evalRingHom y).comp (Polynomial.mapRingHom (Polynomial.evalRingHom γ))
    with hev
  have hevG : ev G = 0 := by
    rw [hev]
    simpa using h0
  have hprod : ev ((UniqueFactorizationMonoid.factors G).prod * u) = 0 := by
    rw [hu]; exact hevG
  rw [map_mul] at hprod
  have hevu : ev (u : F₀[X][Y]) = c := by
    rw [hc, hev]
    simp
  rw [hevu] at hprod
  have hprod0 : ev ((UniqueFactorizationMonoid.factors G).prod) = 0 := by
    rcases mul_eq_zero.mp hprod with h | h
    · exact h
    · exact absurd h hc0
  rw [← Multiset.prod_hom _ ev] at hprod0
  have h0mem : (0 : F₀) ∈ (UniqueFactorizationMonoid.factors G).map ev :=
    Multiset.prod_eq_zero_iff.mp hprod0
  obtain ⟨H, hHmem, hH0⟩ := Multiset.mem_map.mp h0mem
  refine ⟨H, hHmem, ?_⟩
  rw [hev] at hH0
  simpa using hH0

/-- **The x₀-fiber component pigeonhole (BCIKS20 Claim 5.7, counting half).** The cell
splits along the irreducible components of the fiber curve `R(x₀, Y, Z)` plus one
degenerate class, and some class carries a `1/(Ω+2)` fraction of the cell — either a
sub-cell on **one irreducible component** (the Step-6 input) or a degenerate sub-cell
(killed downstream by the Z-degree budget). The count uses the multiset factor count
`Ω := (factors (fiberAt x₀ R)).card` — instance-free. -/
theorem exists_fiber_component_pigeonhole
    (R : (F₀[X])[X][Y]) (x₀ : F₀) (E : Finset F₀) (P : F₀ → F₀[X])
    (hfib : fiberAt x₀ R ≠ 0)
    (hdvd : ∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) :
    ∃ E' ⊆ E,
      E.card ≤ E'.card *
        ((UniqueFactorizationMonoid.factors (fiberAt x₀ R)).card + 2) ∧
      ((∀ γ ∈ E', (fiberAt x₀ R).map (Polynomial.evalRingHom γ) = 0) ∨
        ∃ H, H ∈ UniqueFactorizationMonoid.factors (fiberAt x₀ R) ∧
          ∀ γ ∈ E', ((H.map (Polynomial.evalRingHom γ)).eval ((P γ).eval x₀) = 0)) := by
  classical
  -- the empty cell is its own (vacuous) answer
  by_cases hE0 : E = ∅
  · exact ⟨∅, by simp [hE0], by simp [hE0], Or.inl (by simp)⟩
  set G : F₀[X][Y] := fiberAt x₀ R with hG
  -- the class assignment, by choice (opaque `choose` fvars)
  have hex : ∀ γ : F₀, ∃ ij : Option (F₀[X][Y]),
      (γ ∈ E → G.map (Polynomial.evalRingHom γ) ≠ 0 →
        ∃ H, H ∈ UniqueFactorizationMonoid.factors G ∧ ij = some H ∧
          ((H.map (Polynomial.evalRingHom γ)).eval ((P γ).eval x₀) = 0)) ∧
      ((¬ (γ ∈ E ∧ G.map (Polynomial.evalRingHom γ) ≠ 0)) → ij = none) := by
    intro γ
    by_cases h : γ ∈ E ∧ G.map (Polynomial.evalRingHom γ) ≠ 0
    · obtain ⟨H, hHmem, hH0⟩ := exists_factor_root hfib γ ((P γ).eval x₀)
        (fiber_point_vanishes (hdvd γ h.1))
      exact ⟨some H, fun _ _ => ⟨H, hHmem, rfl, hH0⟩, fun hc => absurd h hc⟩
    · exact ⟨none, fun h1 h2 => absurd ⟨h1, h2⟩ h, fun _ => rfl⟩
  choose assign hpos hneg using hex
  -- the class index set and the cover
  set Index : Finset (Option (F₀[X][Y])) :=
    insert none ((UniqueFactorizationMonoid.factors G).toFinset.image some) with hIndex
  have hIndexCard : Index.card ≤
      (UniqueFactorizationMonoid.factors G).card + 2 := by
    refine le_trans (Finset.card_insert_le _ _) ?_
    have h1 := Finset.card_image_le
      (s := (UniqueFactorizationMonoid.factors G).toFinset) (f := Option.some)
    have h2 := Multiset.toFinset_card_le (UniqueFactorizationMonoid.factors G)
    omega
  have hmem : ∀ γ ∈ E, assign γ ∈ Index := by
    intro γ hγ
    by_cases h0 : G.map (Polynomial.evalRingHom γ) ≠ 0
    · obtain ⟨H, hHmem, hEq, _⟩ := hpos γ hγ h0
      rw [hEq, hIndex]
      exact Finset.mem_insert_of_mem
        (Finset.mem_image_of_mem _ (Multiset.mem_toFinset.mpr hHmem))
    · rw [hneg γ (fun hc => h0 hc.2), hIndex]
      exact Finset.mem_insert_self _ _
  set Ecl : Option (F₀[X][Y]) → Finset F₀ :=
    fun ij => E.filter (fun γ => assign γ = ij) with hEcl
  have hcover : E ⊆ Index.biUnion Ecl := by
    intro γ hγ
    exact Finset.mem_biUnion.mpr
      ⟨assign γ, hmem γ hγ, Finset.mem_filter.mpr ⟨hγ, rfl⟩⟩
  -- pigeonhole: some class has `|E| ≤ |class| · (Ω + 2)`
  have hpigeon : ∃ ij ∈ Index,
      E.card ≤ (Ecl ij).card *
        ((UniqueFactorizationMonoid.factors G).card + 2) := by
    by_contra hcon
    push_neg at hcon
    have hsum : E.card ≤ ∑ ij ∈ Index, (Ecl ij).card :=
      le_trans (Finset.card_le_card hcover) Finset.card_biUnion_le
    -- every class is strictly below the average
    have h1 : (∑ ij ∈ Index, (Ecl ij).card) *
        ((UniqueFactorizationMonoid.factors G).card + 2) <
        Index.card * E.card := by
      rw [Finset.sum_mul]
      have hne : Index.Nonempty := ⟨none, by
        rw [hIndex]; exact Finset.mem_insert_self _ _⟩
      calc ∑ ij ∈ Index, (Ecl ij).card *
            ((UniqueFactorizationMonoid.factors G).card + 2)
          < ∑ _ij ∈ Index, E.card := Finset.sum_lt_sum_of_nonempty hne hcon
        _ = Index.card * E.card := by
            rw [Finset.sum_const, smul_eq_mul]
    have h2 : Index.card * E.card ≤
        ((UniqueFactorizationMonoid.factors G).card + 2) * E.card :=
      Nat.mul_le_mul_right _ hIndexCard
    have h3 : E.card * ((UniqueFactorizationMonoid.factors G).card + 2) ≤
        (∑ ij ∈ Index, (Ecl ij).card) *
          ((UniqueFactorizationMonoid.factors G).card + 2) :=
      Nat.mul_le_mul_right _ hsum
    have hchain : E.card * ((UniqueFactorizationMonoid.factors G).card + 2) <
        ((UniqueFactorizationMonoid.factors G).card + 2) * E.card :=
      lt_of_le_of_lt h3 (lt_of_lt_of_le h1 h2)
    rw [Nat.mul_comm] at hchain
    exact absurd hchain (lt_irrefl _)
  obtain ⟨ij, hijIdx, hijcard⟩ := hpigeon
  -- the majority class is nonempty (the cell is not)
  have hEpos : 0 < E.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hE0)
  have hclpos : 0 < (Ecl ij).card := by
    rcases Nat.eq_zero_or_pos (Ecl ij).card with h0 | h0
    · rw [h0, zero_mul] at hijcard
      omega
    · exact h0
  refine ⟨Ecl ij, Finset.filter_subset _ _, hijcard, ?_⟩
  -- the majority class is degenerate or sits on one irreducible component
  cases ij with
  | none =>
    left
    intro γ hγ
    obtain ⟨hγE, hass⟩ := Finset.mem_filter.mp hγ
    by_contra h0
    obtain ⟨H, _, hEq, _⟩ := hpos γ hγE h0
    rw [hass] at hEq
    exact absurd hEq.symm (Option.some_ne_none _)
  | some H =>
    right
    obtain ⟨γ₀, hγ₀⟩ := Finset.card_pos.mp hclpos
    obtain ⟨hγ₀E, hass₀⟩ := Finset.mem_filter.mp hγ₀
    have h0 : G.map (Polynomial.evalRingHom γ₀) ≠ 0 := by
      intro habs
      rw [hneg γ₀ (fun hc => hc.2 habs)] at hass₀
      exact absurd hass₀.symm (Option.some_ne_none _)
    obtain ⟨H', hH'mem, hEq, _⟩ := hpos γ₀ hγ₀E h0
    rw [hass₀] at hEq
    obtain rfl : H = H' := Option.some.inj hEq
    refine ⟨H, hH'mem, ?_⟩
    intro γ hγ
    obtain ⟨hγE, hass⟩ := Finset.mem_filter.mp hγ
    have h0γ : G.map (Polynomial.evalRingHom γ) ≠ 0 := by
      intro habs
      rw [hneg γ (fun hc => hc.2 habs)] at hass
      exact absurd hass.symm (Option.some_ne_none _)
    obtain ⟨H'', hH''mem, hEq2, hH''0⟩ := hpos γ hγE h0γ
    rw [hass] at hEq2
    rwa [← Option.some.inj hEq2] at hH''0

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms fiber_specialization_commute
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms fiber_point_vanishes
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms exists_factor_root
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms exists_fiber_component_pigeonhole
