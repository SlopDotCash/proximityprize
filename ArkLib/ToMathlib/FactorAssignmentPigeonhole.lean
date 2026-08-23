/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSFactorAssignment
import ArkLib.ToMathlib.PigeonholeFactorSupply

/-!
# Issue #304 — the factor-representative pigeonhole: the capstone's `hdvd` at ONE factor

The truncation capstone consumes per-`z` divisibilities at a **single** trivariate `R` (the
chosen factor's integer representative).  The S10 converse delivers them at the **full**
integer interpolant `Q₀`.  The bridge is [BCIKS20] Claim 5.7 (the in-tree
`exists_specialized_factor_assignment`): outside a nonzero bad set, every decoded linear
factor of `Q₀|_{Z:=z}` divides the specialization of **some** factor representative — and a
pigeonhole over the (finitely many) factors hands one representative at least
`|goodSet| / m` places.

* `card_factors_toFinset_pos` — the factor set is nonempty for non-unit `Q` (needed by the
  pigeonhole).
* `exists_rep_incidence_large` — **the factor-representative pigeonhole**: from the per-place
  decoded divisibilities at `Q₀` (S10-converse outputs), the Claim-5.7 assignment, and the
  count `m · n ≤ |goodSet|` — one factor `R'` whose representative receives `≥ n` places, each
  carrying the per-`z` divisibility **at that representative** — exactly the `hdvd` input
  shape of `gammaGenuine_eq_trunc_of_pigeonhole[_xiAdjusted/_abInitio]` at `R := rep R'`.
* `nonCollapse_of_cert` — the per-`z` non-collapse `Q₀|_{Z:=z} ≠ 0` from one nonzero
  coefficient certificate (any nonzero `F[X]`-entry of `Q₀` works), in the same
  disc-product form as every other per-place certificate on the lane.

With this brick, the per-place input chain of the truncation capstone is sourced end-to-end:
S10-converse divisibilities at `Q₀` → (Claim 5.7 + pigeonhole) divisibilities at ONE factor
representative → the capstone at that representative.

## References
* [BCIKS20] Claim 5.7, §5.2.6, §6; `GSFactorAssignment.lean`; issue #304.
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate

namespace ArkLib

namespace FactorAssignmentPigeonhole

variable {F : Type} [Field F]

/-! ## Non-collapse from a coefficient certificate -/

/-- **Per-`z` non-collapse from one coefficient certificate**: if some `F[X]`-entry
`(Q₀.coeff i).coeff j` is nonzero and survives at `z`, the specialization `Q₀|_{Z:=z}` is
nonzero.  The certificate is a single nonzero `F[X]`-polynomial — the same disc-product
currency as every other per-place condition on the lane. -/
theorem nonCollapse_of_cert {Q₀ : (F[X])[X][Y]} {i j : ℕ} {z : F}
    (hcert : ((Q₀.coeff i).coeff j).eval z ≠ 0) :
    Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) ≠ 0 := by
  intro h0
  have hcoeff := congrArg (fun p => (Polynomial.coeff p i).coeff j) h0
  simp only [Polynomial.coeff_map, Polynomial.coe_mapRingHom, Polynomial.coeff_zero] at hcoeff
  exact hcert hcoeff

/-! ## The factor-representative pigeonhole -/

/-- The factor multiset of a non-unit, nonzero element is nonempty. -/
theorem factors_toFinset_nonempty {α : Type*} [CommMonoidWithZero α] [IsCancelMulZero α]
    [UniqueFactorizationMonoid α] [DecidableEq α] {Q : α} (hQ0 : Q ≠ 0) (hQu : ¬IsUnit Q) :
    (UniqueFactorizationMonoid.factors Q).toFinset.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  have hms : UniqueFactorizationMonoid.factors Q = 0 := by
    by_contra hne
    obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hne
    exact absurd (Multiset.mem_toFinset.mpr hx)
      (by rw [hempty]; exact Finset.notMem_empty x)
  have hassoc := UniqueFactorizationMonoid.factors_prod hQ0
  rw [hms, Multiset.prod_zero] at hassoc
  exact hQu (associated_one_iff_isUnit.mp hassoc.symm)

/-- **The factor-representative pigeonhole (Claim 5.7 composed).**  From: the Claim-5.7
assignment data (`rep`, `bad`), per-good-place decoded divisibilities at `Q₀`
(S10-converse outputs), goodSet avoiding the bad set, and the count
`#factors · n ≤ |goodSet|` — one factor `R'` whose integer representative receives an
incidence set of `≥ n` places, each carrying the per-`z` divisibility **at that
representative**: exactly the capstone's `hdvd` input shape at `R := rep R'`. -/
theorem exists_rep_incidence_large [DecidableEq F] [DecidableEq ((RatFunc F)[X][Y])]
    {Q : (RatFunc F)[X][Y]} {Q₀ : (F[X])[X][Y]}
    (rep : (RatFunc F)[X][Y] → (F[X])[X][Y]) (bad : F[X])
    (hassign : ∀ z : F, bad.eval z ≠ 0 → ∀ q : F[X],
      (Polynomial.X - Polynomial.C q) ∣
          Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) →
        ∃ R ∈ (UniqueFactorizationMonoid.factors Q).toFinset,
          (Polynomial.X - Polynomial.C q) ∣
            (rep R).map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    (hfne : (UniqueFactorizationMonoid.factors Q).toFinset.Nonempty)
    {Pz : F → F[X]} {goodSet : Finset F}
    (hgood_bad : ∀ z ∈ goodSet, bad.eval z ≠ 0)
    (hdvd : ∀ z ∈ goodSet, (Polynomial.X - Polynomial.C (Pz z)) ∣
      Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    {n : ℕ}
    (hcount : (UniqueFactorizationMonoid.factors Q).toFinset.card * n ≤ goodSet.card) :
    ∃ R' ∈ (UniqueFactorizationMonoid.factors Q).toFinset,
      ∃ matchingSet : Finset F,
        matchingSet ⊆ goodSet ∧ n ≤ matchingSet.card ∧
        ∀ z ∈ matchingSet, (Polynomial.X - Polynomial.C (Pz z)) ∣
          (rep R').map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) := by
  classical
  set s := (UniqueFactorizationMonoid.factors Q).toFinset with hs
  -- per-place factor choice
  have hex : ∀ z ∈ goodSet, ∃ R ∈ s, (Polynomial.X - Polynomial.C (Pz z)) ∣
      (rep R).map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) :=
    fun z hz => hassign z (hgood_bad z hz) (Pz z) (hdvd z hz)
  set f : F → (RatFunc F)[X][Y] := fun z =>
    if h : ∃ R ∈ s, (Polynomial.X - Polynomial.C (Pz z)) ∣
        (rep R).map (Polynomial.mapRingHom (Polynomial.evalRingHom z))
    then h.choose else hfne.choose with hf
  have hmaps : ∀ z ∈ goodSet, f z ∈ s := by
    intro z hz
    rw [hf]
    simp only [dif_pos (hex z hz)]
    exact (hex z hz).choose_spec.1
  obtain ⟨R', hR', hcard⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to hmaps hfne hcount
  refine ⟨R', hR',
    goodSet.filter (fun z => (Polynomial.X - Polynomial.C (Pz z)) ∣
      (rep R').map (Polynomial.mapRingHom (Polynomial.evalRingHom z))),
    Finset.filter_subset _ _, ?_,
    fun z hz => (Finset.mem_filter.mp hz).2⟩
  refine le_trans hcard (Finset.card_le_card ?_)
  intro z hz
  rw [Finset.mem_filter] at hz ⊢
  refine ⟨hz.1, ?_⟩
  have h1 := hz.2
  rw [hf] at h1
  simp only [dif_pos (hex z hz.1)] at h1
  exact h1 ▸ (hex z hz.1).choose_spec.2

end FactorAssignmentPigeonhole

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.FactorAssignmentPigeonhole.nonCollapse_of_cert
#print axioms ArkLib.FactorAssignmentPigeonhole.factors_toFinset_nonempty
#print axioms ArkLib.FactorAssignmentPigeonhole.exists_rep_incidence_large
