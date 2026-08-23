/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.BetaWeightGradedSupply
import ArkLib.ToMathlib.PerPlaceSeparabilitySupply

/-!
# Issue #304 — the multiplicative condition-discriminant assembly for the §6 matching set

The §6 matching set must contain every place `z` where the per-`z` geometry fires:
the per-`z` matching polynomial is nonzero/separable, and the per-place readings of the
clearing units (`ξ`, `W`) are nonzero.  Each such condition is the *nonvanishing locus of a
single `F[X]`-discriminant*; this file supplies the generic **multiplicative assembly** —
one product polynomial whose nonvanishing at `z` fires *all* conditions simultaneously,
with the degree of the product (≤ sum of the per-condition degrees) bounding the bad set —
and instantiates it with every per-condition discriminant currently in-tree.

## Part (a) — the generic product assembly (mechanical, reusable)

* `eval_prod_ne_zero_iff` — nonvanishing of `∏ i ∈ s, disc i` at `z` splits into all the
  per-condition nonvanishings.
* `conditions_of_prod_eval_ne_zero` — given per-condition lemmas
  `(disc i).eval z ≠ 0 → cond i z`, the product nonvanishing fires every `cond i z`.
* `prod_disc_ne_zero` — the product discriminant is nonzero when each factor is.
* `card_matching_gt_of_condition_discs` — the §6 cardinality bound with the *sum* of the
  per-condition degrees as the bad-set budget (`Polynomial.natDegree_prod_le` chain into
  `card_matching_gt_of_disc`).
* `discMatchingSet` / `mem_discMatchingSet` / `conditions_on_discMatchingSet` /
  `card_discMatchingSet_gt` — the canonical matching set (the nonvanishing locus of the
  product) satisfies the cover hypothesis *definitionally* and carries all conditions.

## Part (c) — the `gradedCardBudget` shape

* `gradedConcreteFin_of_condition_discs` — composes the product assembly with
  `ArkLib.gradedConcreteFin_of_disc`: the single field-size bound
  `gradedCardBudget dY D dH T + ∑ degrees < |F|` yields the whole `[k,T]` graded
  `hconcreteFin` family consumed by `hcardFin_of_graded`.

## Part (b) — the in-tree per-condition discriminants, wired

Per-condition discriminants found in-tree, each with its condition:

1. `ArkLib.PerPlaceSep.discLC fB = fB.discr * fB.leadingCoeff` —
   `eval z ≠ 0 →` the `z`-specialization `fB.map (evalRingHom z)` is nonzero, degree-
   preserving and **separable** (`specialized_ne_zero_and_separable`), and any per-`z`
   matching polynomial over `F⟦X⟧` with that residue has a **unit derivative** at every
   residue root (`isUnit_derivative_of_discLC` — the Hensel `hderiv` payload).
2. `BCIKS20AppendixA.elimPoly hH β` (the Lemma A.1 `Y`-resultant of `H̃′` with the canonical
   representative of `β : 𝒪 H`) — `eval z ≠ 0 → π_z z root β ≠ 0` for **every** rational
   root at `z` (`π_z_ne_zero_of_elimPoly_eval_ne_zero`, the contrapositive of
   `elimPoly_eval_eq_zero_of_mem_S_β`).  Instantiated at `β = ξ` and `β = W𝒪` — the
   per-place readings of the A.4 clearing units — whose global nonvanishing
   (`ξ_ne_zero` from `embeddingOf𝒪Into𝕃_ξ_ne_zero`, `W𝒪_ne_zero` from
   `liftToFunctionField_leadingCoeff_ne_zero`) makes the elimination polynomials nonzero
   (`elimPoly_ne_zero_of_ne_zero`).

`conditionDiscs` bundles the three; `matchingSet304_geometry_and_card` is the capstone:
**one** field-size inequality in the exact `gradedCardBudget` shape produces a matching set
on which *all* per-`z` conditions hold *and* whose cardinality dominates the whole graded
budget family.  `hensel_unit_derivative_on_discMatchingSet` adds the composed Hensel
unit-derivative supply on the same set.

## The honest residual

* `RootSupplyOn` — the **rational-root existence** condition (`Nonempty (rationalRoot
  (H̃′ H) z)`).  This is *not* a discriminant-nonvanishing condition and no `disc` with
  `eval z ≠ 0 → Nonempty (rationalRoot … z)` can exist in general: for `H̃′ = Y² − X` over
  `𝔽_q` (`q` odd) the places with a rational root are exactly the squares, whose complement
  has `≈ q/2` elements — no fixed-degree polynomial vanishes on all of them.  In BCIKS20 the
  root at good `z` is *supplied* by the §5 decoded geometry (the `CurveFamilyHensel` lane),
  not by a genericity argument; `RootSupplyOn` names that handoff, and
  `exists_root_with_readings_of_rootSupply` is its proven consumer here.

Axiom-clean: every declaration rests on `[propext, Classical.choice, Quot.sound]`.
-/

namespace ArkLib.Match304

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2

variable {F : Type} [Field F]

/-! ## Part (a) — the generic multiplicative assembly -/

section Generic

variable {ι : Type}

/-- Nonvanishing of the product discriminant at `z` is exactly the conjunction of all the
per-condition nonvanishings. -/
theorem eval_prod_ne_zero_iff (s : Finset ι) (disc : ι → F[X]) (z : F) :
    (∏ i ∈ s, disc i).eval z ≠ 0 ↔ ∀ i ∈ s, (disc i).eval z ≠ 0 := by
  rw [Polynomial.eval_prod]
  exact Finset.prod_ne_zero_iff

/-- **The condition assembly**: per-condition lemmas `(disc i).eval z ≠ 0 → cond i z` upgrade
the product nonvanishing at `z` to *all* the conditions at `z`. -/
theorem conditions_of_prod_eval_ne_zero {s : Finset ι} {disc : ι → F[X]}
    {cond : ι → F → Prop}
    (himp : ∀ i ∈ s, ∀ z : F, (disc i).eval z ≠ 0 → cond i z)
    {z : F} (hz : (∏ i ∈ s, disc i).eval z ≠ 0) :
    ∀ i ∈ s, cond i z :=
  fun i hi => himp i hi z ((eval_prod_ne_zero_iff s disc z).mp hz i hi)

/-- The product discriminant is nonzero as soon as each per-condition discriminant is. -/
theorem prod_disc_ne_zero {s : Finset ι} {disc : ι → F[X]}
    (h : ∀ i ∈ s, disc i ≠ 0) : (∏ i ∈ s, disc i) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr h

end Generic

section Counting

variable {ι : Type} [Fintype F] [DecidableEq F]

/-- **The §6 cardinality bound from condition discriminants**: any matching set containing the
joint nonvanishing locus of finitely many nonzero condition discriminants inherits
`N < #matchingSet` whenever `N + ∑ degrees < |F|` — the `natDegree_prod_le` chain into the
single-discriminant counter `card_matching_gt_of_disc`. -/
theorem card_matching_gt_of_condition_discs {s : Finset ι} {disc : ι → F[X]}
    (hne : ∀ i ∈ s, disc i ≠ 0) {matchingSet : Finset F}
    (hcover : ∀ z : F, (∀ i ∈ s, (disc i).eval z ≠ 0) → z ∈ matchingSet)
    {N : ℕ} (hbig : N + ∑ i ∈ s, (disc i).natDegree < Fintype.card F) :
    N < matchingSet.card :=
  card_matching_gt_of_disc (prod_disc_ne_zero hne)
    (fun z hz => hcover z ((eval_prod_ne_zero_iff s disc z).mp hz))
    (lt_of_le_of_lt
      (Nat.add_le_add_left (Polynomial.natDegree_prod_le s disc) N) hbig)

/-- **The canonical matching set of a family of condition discriminants**: the joint
nonvanishing locus.  It satisfies the cover hypothesis definitionally
(`mem_discMatchingSet`). -/
noncomputable def discMatchingSet (s : Finset ι) (disc : ι → F[X]) : Finset F :=
  Finset.univ.filter fun z : F => (∏ i ∈ s, disc i).eval z ≠ 0

/-- Membership in the canonical matching set is the conjunction of all the per-condition
nonvanishings. -/
theorem mem_discMatchingSet {s : Finset ι} {disc : ι → F[X]} {z : F} :
    z ∈ discMatchingSet s disc ↔ ∀ i ∈ s, (disc i).eval z ≠ 0 := by
  rw [discMatchingSet, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  exact eval_prod_ne_zero_iff s disc z

/-- Every place of the canonical matching set satisfies every per-condition payload. -/
theorem conditions_on_discMatchingSet {s : Finset ι} {disc : ι → F[X]}
    {cond : ι → F → Prop}
    (himp : ∀ i ∈ s, ∀ z : F, (disc i).eval z ≠ 0 → cond i z) :
    ∀ z ∈ discMatchingSet s disc, ∀ i ∈ s, cond i z :=
  fun z hz i hi => himp i hi z (mem_discMatchingSet.mp hz i hi)

/-- The cardinality bound for the canonical matching set. -/
theorem card_discMatchingSet_gt {s : Finset ι} {disc : ι → F[X]}
    (hne : ∀ i ∈ s, disc i ≠ 0)
    {N : ℕ} (hbig : N + ∑ i ∈ s, (disc i).natDegree < Fintype.card F) :
    N < (discMatchingSet s disc).card :=
  card_matching_gt_of_condition_discs hne
    (fun _ hz => mem_discMatchingSet.mpr hz) hbig

/-! ## Part (c) — the graded `|F|`-side shape -/

/-- **The graded cardinality family from condition discriminants** (the exact
`gradedCardBudget` shape of `ArkLib.gradedConcreteFin_of_disc`): a single field-size bound
`gradedCardBudget dY D dH T + ∑ degrees < |F|` yields the whole `[k,T]` graded
`hconcreteFin` family (in `WithBot ℕ`) consumed by `hcardFin_of_graded`. -/
theorem gradedConcreteFin_of_condition_discs {s : Finset ι} {disc : ι → F[X]}
    (hne : ∀ i ∈ s, disc i ≠ 0) {matchingSet : Finset F}
    (hcover : ∀ z : F, (∀ i ∈ s, (disc i).eval z ≠ 0) → z ∈ matchingSet)
    {dY D dH k T : ℕ}
    (hbig : ArkLib.gradedCardBudget dY D dH T + ∑ i ∈ s, (disc i).natDegree
        < Fintype.card F) :
    ∀ t, k ≤ t → t ≤ T → (↑matchingSet.card : WithBot ℕ)
      > ((((dY * (D - dH + 1) + D + (D - dH + 1)) * (2 * t - 1)
            + (D - dH + 1)) * dH : ℕ) : WithBot ℕ) :=
  ArkLib.gradedConcreteFin_of_disc (prod_disc_ne_zero hne)
    (fun z hz => hcover z ((eval_prod_ne_zero_iff s disc z).mp hz))
    (lt_of_le_of_lt
      (Nat.add_le_add_left (Polynomial.natDegree_prod_le s disc) _) hbig)

end Counting

/-! ## Part (b) — the in-tree per-condition discriminants -/

section ElimPolyCondition

variable {H : F[X][Y]}

/-- The canonical representative of a *nonzero* regular element is nonzero (its quotient class
recovers the element via `mk_canonicalRepOf𝒪`). -/
theorem canonicalRepOf𝒪_ne_zero_of_ne_zero (hH : 0 < H.natDegree) {β : 𝒪 H}
    (hβ : β ≠ 0) : canonicalRepOf𝒪 hH β ≠ 0 := fun h =>
  hβ (by rw [← mk_canonicalRepOf𝒪 hH β, h, map_zero])

/-- **The per-place reading condition of the elimination discriminant** (contrapositive of
`elimPoly_eval_eq_zero_of_mem_S_β`): where the Lemma-A.1 elimination polynomial of
`β : 𝒪 H` does not vanish, the place reading `π_z` of `β` is nonzero at **every** rational
root of `H̃′` over `z` — the per-`z` `W`/`ξ` nonvanishing payload of the §6 geometry. -/
theorem π_z_ne_zero_of_elimPoly_eval_ne_zero (hH : 0 < H.natDegree) (β : 𝒪 H)
    {z : F} (hz : (elimPoly hH β).eval z ≠ 0) :
    ∀ root : rationalRoot (H_tilde' H) z, π_z z root β ≠ 0 :=
  fun root h0 => hz (elimPoly_eval_eq_zero_of_mem_S_β hH β ⟨root, h0⟩)

/-- The elimination discriminant of a nonzero `β` is a nonzero polynomial — the
`disc ≠ 0` input of the counting side, from `elimPoly_ne_zero`. -/
theorem elimPoly_ne_zero_of_ne_zero [Fact (Irreducible H)] (hH : 0 < H.natDegree)
    {β : 𝒪 H} (hβ : β ≠ 0) : elimPoly hH β ≠ 0 :=
  elimPoly_ne_zero hH β (canonicalRepOf𝒪_ne_zero_of_ne_zero hH hβ)

end ElimPolyCondition

section Readings

variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- `ξ ≠ 0` in `𝒪 H`: the embedding into the function field is nonzero
(`embeddingOf𝒪Into𝕃_ξ_ne_zero`, PROVEN globally in `HenselNumerator`), and ring homs kill
zero. -/
theorem ξ_ne_zero (x₀ : F) (R : F[X][X][Y]) (hHyp : Hypotheses x₀ R H) :
    ξ x₀ R H hHyp ≠ 0 := fun h =>
  BCIKS20.HenselNumerator.embeddingOf𝒪Into𝕃_ξ_ne_zero H x₀ R hHyp
    (by rw [h, map_zero])

/-- `W𝒪 ≠ 0` in `𝒪 H`: its embedding is `liftToFunctionField H.leadingCoeff` (definitional),
which is nonzero by `liftToFunctionField_leadingCoeff_ne_zero`. -/
theorem W𝒪_ne_zero : BCIKS20.HenselNumerator.W𝒪 H ≠ 0 := fun h =>
  liftToFunctionField_leadingCoeff_ne_zero (H := H) (by
    have hemb : embeddingOf𝒪Into𝕃 H (BCIKS20.HenselNumerator.W𝒪 H)
        = liftToFunctionField (H := H) H.leadingCoeff := rfl
    rw [← hemb, h, map_zero])

end Readings

/-! ## The concrete §6 bundle: separability + `ξ`-reading + `W`-reading -/

section Concrete

variable (fB : F[X][Y]) (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
variable [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
variable (hH : 0 < H.natDegree) (hHyp : Hypotheses x₀ R H)

/-- **The three concrete §6 condition discriminants** (issue #304):

0. `discLC fB` — per-`z` nonzero/degree-preserving/separable specialization of the bivariate
   source `fB` (take `fB := H_tilde' H` for the matching polynomial itself);
1. `elimPoly hH ξ` — per-`z` nonvanishing of the `ξ`-reading at every rational root;
2. `elimPoly hH W𝒪` — per-`z` nonvanishing of the `W`-reading at every rational root. -/
noncomputable def conditionDiscs : Fin 3 → F[X] :=
  ![ArkLib.PerPlaceSep.discLC fB,
    elimPoly hH (ξ x₀ R H hHyp),
    elimPoly hH (BCIKS20.HenselNumerator.W𝒪 H)]

@[simp] theorem conditionDiscs_zero :
    conditionDiscs fB x₀ R H hH hHyp 0 = ArkLib.PerPlaceSep.discLC fB := rfl

@[simp] theorem conditionDiscs_one :
    conditionDiscs fB x₀ R H hH hHyp 1 = elimPoly hH (ξ x₀ R H hHyp) := rfl

@[simp] theorem conditionDiscs_two :
    conditionDiscs fB x₀ R H hH hHyp 2
      = elimPoly hH (BCIKS20.HenselNumerator.W𝒪 H) := rfl

/-- All three condition discriminants are nonzero, from the two genuine inputs
(`fB.discr ≠ 0`, `fB ≠ 0`) and the PROVEN global unit nonvanishings. -/
theorem conditionDiscs_ne_zero (hdiscr : fB.discr ≠ 0) (hfB : fB ≠ 0) :
    ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      conditionDiscs fB x₀ R H hH hHyp i ≠ 0 := by
  intro i _
  fin_cases i
  · exact ArkLib.PerPlaceSep.discLC_ne_zero hdiscr hfB
  · exact elimPoly_ne_zero_of_ne_zero hH (ξ_ne_zero H x₀ R hHyp)
  · exact elimPoly_ne_zero_of_ne_zero hH (W𝒪_ne_zero H)

/-- **All three per-`z` §6 conditions fire** at any place where the three condition
discriminants are nonvanishing: the specialization of `fB` is nonzero and separable, and the
`ξ`- and `W`-readings are nonzero at every rational root over `z`. -/
theorem conditions_of_conditionDiscs_eval_ne_zero (hdeg : 0 < fB.natDegree) {z : F}
    (hz : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      (conditionDiscs fB x₀ R H hH hHyp i).eval z ≠ 0) :
    (fB.map (Polynomial.evalRingHom z) ≠ 0
        ∧ (fB.map (Polynomial.evalRingHom z)).Separable)
      ∧ (∀ root : rationalRoot (H_tilde' H) z, π_z z root (ξ x₀ R H hHyp) ≠ 0)
      ∧ (∀ root : rationalRoot (H_tilde' H) z,
          π_z z root (BCIKS20.HenselNumerator.W𝒪 H) ≠ 0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ArkLib.PerPlaceSep.specialized_ne_zero_and_separable fB hdeg
      (by simpa using hz 0 (Finset.mem_univ _))
  · exact π_z_ne_zero_of_elimPoly_eval_ne_zero hH _
      (by simpa using hz 1 (Finset.mem_univ _))
  · exact π_z_ne_zero_of_elimPoly_eval_ne_zero hH _
      (by simpa using hz 2 (Finset.mem_univ _))

section Capstone

variable [Fintype F] [DecidableEq F]

/-- **The capstone: the §6 matching set from condition discriminants, in the exact
`gradedCardBudget` shape.**  One field-size inequality
`gradedCardBudget dY D dH T + ∑ degrees < |F|` (plus the two genuine `fB` inputs) yields a
matching set — the joint nonvanishing locus — on which

* every place has a nonzero, separable `fB`-specialization (the per-`z` matching-polynomial
  separability / Hensel unit-derivative source), and
* the `ξ`- and `W`-readings are nonzero at every rational root over every place, and

whose cardinality dominates the whole `[k,T]` graded budget family — exactly the
`hconcreteFin` input of `hcardFin_of_graded` at `matchingSet := discMatchingSet …`. -/
theorem matchingSet304_geometry_and_card (hdeg : 0 < fB.natDegree)
    (hdiscr : fB.discr ≠ 0) (hfB : fB ≠ 0)
    {dY D dH k T : ℕ}
    (hbig : ArkLib.gradedCardBudget dY D dH T
        + ∑ i, (conditionDiscs fB x₀ R H hH hHyp i).natDegree < Fintype.card F) :
    (∀ z ∈ discMatchingSet Finset.univ (conditionDiscs fB x₀ R H hH hHyp),
        (fB.map (Polynomial.evalRingHom z) ≠ 0
            ∧ (fB.map (Polynomial.evalRingHom z)).Separable)
          ∧ (∀ root : rationalRoot (H_tilde' H) z,
              π_z z root (ξ x₀ R H hHyp) ≠ 0)
          ∧ (∀ root : rationalRoot (H_tilde' H) z,
              π_z z root (BCIKS20.HenselNumerator.W𝒪 H) ≠ 0))
      ∧ (∀ t, k ≤ t → t ≤ T →
          (↑(discMatchingSet Finset.univ
              (conditionDiscs fB x₀ R H hH hHyp)).card : WithBot ℕ)
            > ((((dY * (D - dH + 1) + D + (D - dH + 1)) * (2 * t - 1)
                  + (D - dH + 1)) * dH : ℕ) : WithBot ℕ)) := by
  constructor
  · intro z hz
    exact conditions_of_conditionDiscs_eval_ne_zero fB x₀ R H hH hHyp hdeg
      (mem_discMatchingSet.mp hz)
  · exact gradedConcreteFin_of_condition_discs
      (conditionDiscs_ne_zero fB x₀ R H hH hHyp hdiscr hfB)
      (fun _ hz => mem_discMatchingSet.mpr hz) hbig

/-- **The composed Hensel unit-derivative supply on the matching set**: at every place of the
canonical matching set, any per-`z` matching polynomial over `F⟦X⟧` whose residue is the
`z`-specialization of `fB` has a unit derivative at every residue-level approximate root —
the `HenselDatum.hderiv` payload, via `PerPlaceSep.isUnit_derivative_of_discLC`. -/
theorem hensel_unit_derivative_on_discMatchingSet (hdeg : 0 < fB.natDegree) :
    ∀ z ∈ discMatchingSet Finset.univ (conditionDiscs fB x₀ R H hH hHyp),
      ∀ f : Polynomial (PowerSeries F),
        f.map ArkLib.PerPlaceSep.π = fB.map (Polynomial.evalRingHom z) →
        ∀ a₀ : PowerSeries F,
          (f.map ArkLib.PerPlaceSep.π).IsRoot (ArkLib.PerPlaceSep.π a₀) →
          IsUnit (f.derivative.eval a₀) := by
  intro z hz f hres a₀ hroot
  exact ArkLib.PerPlaceSep.isUnit_derivative_of_discLC fB hdeg
    (by simpa using mem_discMatchingSet.mp hz 0 (Finset.mem_univ _)) f hres a₀ hroot

end Capstone

end Concrete

/-! ## The honest residual — rational-root existence is not a discriminant condition -/

/-- **Honest residual (the per-place root supply).**  The remaining per-`z` geometry input is
the *existence* of a rational root of `H̃′ H` over `z`.  This is genuinely **not** the
nonvanishing locus of any `F[X]`-discriminant: for `H̃′ = Y² − X` over `𝔽_q` (`q` odd) the
places with a rational root are exactly the squares, whose complement has about `q/2`
elements, exceeding every fixed degree budget — so no polynomial `disc` with
`disc.eval z ≠ 0 → Nonempty (rationalRoot …)` exists in general.  In BCIKS20 §5 the root at
each good place is *constructed* by the decoded curve geometry (the `CurveFamilyHensel`
lane), and this named `Prop` is the cross-lane handoff. -/
def RootSupplyOn (H : F[X][Y]) (matchingSet : Finset F) : Prop :=
  ∀ z ∈ matchingSet, Nonempty (rationalRoot (H_tilde' H) z)

section ResidualConsumer

variable (fB : F[X][Y]) (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
variable [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
variable (hH : 0 < H.natDegree) (hHyp : Hypotheses x₀ R H)
variable [Fintype F] [DecidableEq F]

/-- **The proven consumer of the root-supply residual**: with a root supply on the canonical
matching set, every place carries an *existential* root at which both unit readings are
nonzero — the full `(1) ∧ (2) ∧ (3)` per-`z` geometry conjunction of the §6 lane. -/
theorem exists_root_with_readings_of_rootSupply
    (hsupply : RootSupplyOn H
      (discMatchingSet Finset.univ (conditionDiscs fB x₀ R H hH hHyp))) :
    ∀ z ∈ discMatchingSet Finset.univ (conditionDiscs fB x₀ R H hH hHyp),
      ∃ root : rationalRoot (H_tilde' H) z,
        π_z z root (ξ x₀ R H hHyp) ≠ 0
          ∧ π_z z root (BCIKS20.HenselNumerator.W𝒪 H) ≠ 0 := by
  intro z hz
  obtain ⟨root⟩ := hsupply z hz
  have h := mem_discMatchingSet.mp hz
  exact ⟨root,
    π_z_ne_zero_of_elimPoly_eval_ne_zero hH _
      (by simpa using h 1 (Finset.mem_univ _)) root,
    π_z_ne_zero_of_elimPoly_eval_ne_zero hH _
      (by simpa using h 2 (Finset.mem_univ _)) root⟩

end ResidualConsumer

end ArkLib.Match304

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`. -/
#print axioms ArkLib.Match304.eval_prod_ne_zero_iff
#print axioms ArkLib.Match304.conditions_of_prod_eval_ne_zero
#print axioms ArkLib.Match304.prod_disc_ne_zero
#print axioms ArkLib.Match304.card_matching_gt_of_condition_discs
#print axioms ArkLib.Match304.discMatchingSet
#print axioms ArkLib.Match304.mem_discMatchingSet
#print axioms ArkLib.Match304.conditions_on_discMatchingSet
#print axioms ArkLib.Match304.card_discMatchingSet_gt
#print axioms ArkLib.Match304.gradedConcreteFin_of_condition_discs
#print axioms ArkLib.Match304.canonicalRepOf𝒪_ne_zero_of_ne_zero
#print axioms ArkLib.Match304.π_z_ne_zero_of_elimPoly_eval_ne_zero
#print axioms ArkLib.Match304.elimPoly_ne_zero_of_ne_zero
#print axioms ArkLib.Match304.ξ_ne_zero
#print axioms ArkLib.Match304.W𝒪_ne_zero
#print axioms ArkLib.Match304.conditionDiscs
#print axioms ArkLib.Match304.conditionDiscs_zero
#print axioms ArkLib.Match304.conditionDiscs_one
#print axioms ArkLib.Match304.conditionDiscs_two
#print axioms ArkLib.Match304.conditionDiscs_ne_zero
#print axioms ArkLib.Match304.conditions_of_conditionDiscs_eval_ne_zero
#print axioms ArkLib.Match304.matchingSet304_geometry_and_card
#print axioms ArkLib.Match304.hensel_unit_derivative_on_discMatchingSet
#print axioms ArkLib.Match304.RootSupplyOn
#print axioms ArkLib.Match304.exists_root_with_readings_of_rootSupply
