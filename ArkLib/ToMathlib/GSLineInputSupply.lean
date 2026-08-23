/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.InterpolantInputSupply
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSOverRatFunc

/-!
# Issue #304 — `GSLineInput`'s global GS fields from the in-tree existence chain

`InterpolantInputSupply.GSLineInput` bundles the S10-converse surface of the Hensel lane.
Its fields split into two kinds:

* **global** (one-time GS existence, word-level): the `K = F(Z)`-level interpolant `Q` with
  its S2 `Conditions` for the generic fold `u 0 + Z·u 1`, and the integer representative
  `(d, Q₀)` — plus the numeric side conditions `deg + 1 ≤ n`, `1 ≤ m`, `2 ≤ deg`;
* **per-`z`** (the per-word residual): non-collapse of the specialization on the good set,
  degree + Johnson-radius proximity of the two competitors, order-0 agreement, separability.

This file discharges the **global** half from the in-tree existence chain and repackages the
per-`z` half as the honest residual:

* `exists_gs_chain` — the composed existence: from the numeric Johnson-regime conditions
  (`2 ≤ deg`, `n ≠ 0`, `1 ≤ m`) alone, a `K`-level GS interpolant with its `Conditions`
  AND an integer representative exist (`gs_existence_over_ratfunc` ∘
  `exists_integer_representative`).
* `canonicalQ` / `canonicalDenom` / `canonicalRep` (+ spec lemmas `canonicalDenom_ne_zero`,
  `canonicalQ_conditions`, `canonicalRep_map`) — a classical-choice canonical chain, so the
  per-`z` residual can be stated about ONE fixed representative.
* `rep_ne_zero` / `specialization_collapse_finite` (+ `canonicalRep_ne_zero`,
  `canonicalRep_collapse_finite`) — the production lane for the `hgood` residual: the
  integer representative is nonzero, hence its specialization collapses on a FINITE set of
  `z` only.  (What remains per word is exactly BCIKS20's finitely-many-bad-`z` accounting:
  the good set must avoid that finite set; we do not fabricate it.)
* `PerZResidual` — the per-word residual bundle: GSLineInput's six per-`z` fields, verbatim,
  about a given representative `Q₀`.
* `gsLineInput_of_chain` / `gsLineInput_of_johnson` — **the producers**: `GSLineInput` from
  the numeric conditions + (any chain | the canonical chain) + the per-`z` residual.  This
  is "`GSLineInput` minus its per-`z` fields".
* `hPz_of_johnson_conditions` — **the capstone**: the full `hPz` conclusion of
  `hPz_of_gs_line` from the numeric Johnson conditions and the per-representative per-`z`
  residual alone — no GS interpolant has to be supplied by the consumer.

## Honest residuals

The global GS fields are now FULLY discharged from numerics.  What remains per word is the
recognized per-`z` content of BCIKS20 §5 / Hab25 S10:

* `hgood` — the good set avoids the finite collapse set (`canonicalRep_collapse_finite`
  supplies finiteness; the avoidance is the paper's bad-`z` accounting);
* `hPdeg`/`hPdist`/`hQdist` — the per-`z` decoded-degree and Johnson-radius agreement counts;
* `h0` — the per-`z` order-0 common-approximation fact;
* `hsep` — per-`z` separability of the specialized interpolant (unit-discriminant route,
  `InterpolantInputSupply.hsep_of_discr_isUnit`).

None of these is goal-shaped: the conclusion `P z = (lift v₀ v₁).eval (C z)` is derived by
Hensel uniqueness downstream.

## References

* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5; Hab25 §3 Steps S2/S10.
-/

set_option linter.unusedSectionVars false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open ProximityGap Code ReedSolomon NNReal
open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace ArkLib

namespace GSLineInputSupply

/-! ## The composed global existence chain -/

section Chain

variable {F : Type} [Field F] {n : ℕ}

/-- **The composed GS existence chain (the global fields of `GSLineInput`).**  From the
numeric Johnson-regime conditions alone (`2 ≤ deg`, `n ≠ 0`, `1 ≤ m`), the `K = F(Z)`-level
GS interpolant for the generic fold exists together with an integer representative:
`gs_existence_over_ratfunc` composed with `exists_integer_representative`. -/
theorem exists_gs_chain (deg m : ℕ) (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    (hdeg2 : 2 ≤ deg) (hn : n ≠ 0) (hm : 1 ≤ m) :
    ∃ (Q : (RatFunc F)[X][Y]) (d : F[X]) (Q₀ : (F[X])[X][Y]),
      d ≠ 0 ∧
      GuruswamiSudan.Conditions deg m (gs_degree_bound deg n m)
        (GuruswamiSudan.OverRatFunc.liftedDomain ωs)
        (GuruswamiSudan.OverRatFunc.genericFold f₀ f₁) Q ∧
      Q₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
        Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) d)) * Q := by
  classical
  obtain ⟨Q, hQ⟩ := GuruswamiSudan.OverRatFunc.gs_existence_over_ratfunc deg m ωs f₀ f₁
    (by omega) hn hm
  obtain ⟨d, Q₀, hd, hrep⟩ := GuruswamiSudan.OverRatFunc.exists_integer_representative Q
  exact ⟨Q, d, Q₀, hd, hQ, hrep⟩

/-- The canonical (classical-choice) `K`-level GS interpolant of the generic fold. -/
noncomputable def canonicalQ (deg m : ℕ) (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    (hdeg2 : 2 ≤ deg) (hn : n ≠ 0) (hm : 1 ≤ m) : (RatFunc F)[X][Y] :=
  (exists_gs_chain deg m ωs f₀ f₁ hdeg2 hn hm).choose

/-- The canonical common denominator of the integer representative. -/
noncomputable def canonicalDenom (deg m : ℕ) (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    (hdeg2 : 2 ≤ deg) (hn : n ≠ 0) (hm : 1 ≤ m) : F[X] :=
  (exists_gs_chain deg m ωs f₀ f₁ hdeg2 hn hm).choose_spec.choose

/-- The canonical integer representative of the GS interpolant, over `F[Z][X][Y]`. -/
noncomputable def canonicalRep (deg m : ℕ) (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    (hdeg2 : 2 ≤ deg) (hn : n ≠ 0) (hm : 1 ≤ m) : (F[X])[X][Y] :=
  (exists_gs_chain deg m ωs f₀ f₁ hdeg2 hn hm).choose_spec.choose_spec.choose

/-- The canonical denominator is nonzero. -/
theorem canonicalDenom_ne_zero (deg m : ℕ) (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    (hdeg2 : 2 ≤ deg) (hn : n ≠ 0) (hm : 1 ≤ m) :
    canonicalDenom deg m ωs f₀ f₁ hdeg2 hn hm ≠ 0 :=
  (exists_gs_chain deg m ωs f₀ f₁ hdeg2 hn hm).choose_spec.choose_spec.choose_spec.1

/-- The canonical interpolant satisfies the S2 GS `Conditions` for the generic fold —
exactly the `hQ` field of `GSLineInput`. -/
theorem canonicalQ_conditions (deg m : ℕ) (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    (hdeg2 : 2 ≤ deg) (hn : n ≠ 0) (hm : 1 ≤ m) :
    GuruswamiSudan.Conditions deg m (gs_degree_bound deg n m)
      (GuruswamiSudan.OverRatFunc.liftedDomain ωs)
      (GuruswamiSudan.OverRatFunc.genericFold f₀ f₁)
      (canonicalQ deg m ωs f₀ f₁ hdeg2 hn hm) :=
  (exists_gs_chain deg m ωs f₀ f₁ hdeg2 hn hm).choose_spec.choose_spec.choose_spec.2.1

/-- The canonical integer-representative identity — exactly the `hrep` field of
`GSLineInput`. -/
theorem canonicalRep_map (deg m : ℕ) (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    (hdeg2 : 2 ≤ deg) (hn : n ≠ 0) (hm : 1 ≤ m) :
    (canonicalRep deg m ωs f₀ f₁ hdeg2 hn hm).map
        (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F)
          (canonicalDenom deg m ωs f₀ f₁ hdeg2 hn hm))) *
        canonicalQ deg m ωs f₀ f₁ hdeg2 hn hm :=
  (exists_gs_chain deg m ωs f₀ f₁ hdeg2 hn hm).choose_spec.choose_spec.choose_spec.2.2

end Chain

/-! ## The production lane for the `hgood` residual: the collapse set is finite -/

section Collapse

variable {F : Type} [Field F]

/-- An integer representative of a nonzero `K`-level polynomial is nonzero (the embedding is
injective and the denominator factor is a nonzero constant of the field `K`). -/
theorem rep_ne_zero {Q : (RatFunc F)[X][Y]} {d : F[X]} {Q₀ : (F[X])[X][Y]}
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) d)) * Q)
    (hd : d ≠ 0) (hQne : Q ≠ 0) : Q₀ ≠ 0 := by
  intro h0
  rw [h0, Polynomial.map_zero] at hrep
  have hφd : algebraMap F[X] (RatFunc F) d ≠ 0 := fun h =>
    hd ((map_eq_zero_iff _ (RatFunc.algebraMap_injective F)).mp h)
  exact (mul_ne_zero (by simpa using hφd) hQne) hrep.symm

/-- **The collapse set of a nonzero integer representative is finite.**  If `Q₀ ≠ 0`, then
`Q₀|_{Z:=z} = 0` forces `z` to be a root of any fixed nonzero `F[Z]`-coefficient of `Q₀`,
of which there are finitely many.  This is the cofinite-bad-set production lane for the
`hgood` residual of `GSLineInput` (what remains per word is the paper's accounting that the
good set avoids this finite set). -/
theorem specialization_collapse_finite {Q₀ : (F[X])[X][Y]} (hQ₀ : Q₀ ≠ 0) :
    {z : F | Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) = 0}.Finite := by
  obtain ⟨i, hi⟩ := Polynomial.support_nonempty.mpr hQ₀
  have hi' : Q₀.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
  obtain ⟨j, hj⟩ := Polynomial.support_nonempty.mpr hi'
  have hj' : (Q₀.coeff i).coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
  refine Set.Finite.subset (Polynomial.finite_setOf_isRoot hj') fun z hz => ?_
  have h1 : ((Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))).coeff i).coeff j
      = 0 := by
    rw [Set.mem_setOf_eq.mp hz]
    simp
  rw [Polynomial.coeff_map, Polynomial.coe_mapRingHom, Polynomial.coeff_map,
    Polynomial.coe_evalRingHom] at h1
  exact h1

variable {n : ℕ}

/-- The canonical integer representative is nonzero. -/
theorem canonicalRep_ne_zero (deg m : ℕ) (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    (hdeg2 : 2 ≤ deg) (hn : n ≠ 0) (hm : 1 ≤ m) :
    canonicalRep deg m ωs f₀ f₁ hdeg2 hn hm ≠ 0 :=
  rep_ne_zero (canonicalRep_map deg m ωs f₀ f₁ hdeg2 hn hm)
    (canonicalDenom_ne_zero deg m ωs f₀ f₁ hdeg2 hn hm)
    (canonicalQ_conditions deg m ωs f₀ f₁ hdeg2 hn hm).Q_ne_0

/-- The collapse set of the canonical integer representative is finite. -/
theorem canonicalRep_collapse_finite (deg m : ℕ) (ωs : Fin n ↪ F) (f₀ f₁ : Fin n → F)
    (hdeg2 : 2 ≤ deg) (hn : n ≠ 0) (hm : 1 ≤ m) :
    {z : F | (canonicalRep deg m ωs f₀ f₁ hdeg2 hn hm).map
        (Polynomial.mapRingHom (Polynomial.evalRingHom z)) = 0}.Finite :=
  specialization_collapse_finite (canonicalRep_ne_zero deg m ωs f₀ f₁ hdeg2 hn hm)

end Collapse

/-! ## The per-word residual bundle and the producers -/

section Producers

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **The per-word residual of `GSLineInput`** about a given integer representative `Q₀`:
exactly the six per-`z` fields of `GSLineInput`, verbatim — non-collapse on the good set,
degree + GS-Johnson-radius proximity of the decoded family `P` and of the lift-specialisation
competitor, order-0 agreement, and `F[X][Y]`-level separability.  These are the recognized
per-`z` ingredients of BCIKS20 §5 / Hab25 S10; none is goal-shaped. -/
structure PerZResidual (deg m : ℕ) (ωs : Fin n ↪ F) (δ : ℝ≥0)
    (u : WordStack F (Fin 2) (Fin n)) (P : F → Polynomial F) (v₀ v₁ : F[X])
    (Q₀ : (F[X])[X][Y]) : Prop where
  /-- per-good-`z` non-collapse of the specialization (the good set avoids the finite
  collapse set — see `specialization_collapse_finite`). -/
  hgood : ∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := ωs) u δ,
    Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)) ≠ 0
  /-- the decoded family has Reed–Solomon degree. -/
  hPdeg : ∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := ωs) u δ,
    (P z).degree < (deg : WithBot ℕ)
  /-- the decoded family is within the GS Johnson radius of the fold. -/
  hPdist : ∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := ωs) u δ,
    (hammingDist (fun i => u 0 i + z * u 1 i) (fun i => (P z).eval (ωs i)) : ℝ) / n <
      gs_johnson deg n m
  /-- the lift-specialisation competitor is within the GS Johnson radius of the fold. -/
  hQdist : ∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := ωs) u δ,
    (hammingDist (fun i => u 0 i + z * u 1 i)
        (fun i => (InterpolantInputSupply.liftSpec v₀ v₁ z).eval (ωs i)) : ℝ) / n <
      gs_johnson deg n m
  /-- per-`z` order-0 agreement of the two competitors. -/
  h0 : ∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := ωs) u δ,
    (P z).coeff 0 = (InterpolantInputSupply.liftSpec v₀ v₁ z).coeff 0
  /-- per-`z` `F[X][Y]`-level separability of the specialized interpolant. -/
  hsep : ∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := ωs) u δ,
    (Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))).Separable

/-- **`GSLineInput` from any GS chain + the per-word residual** — the generic producer:
the global fields are supplied by the chain witnesses, the per-`z` fields by the residual. -/
noncomputable def gsLineInput_of_chain {deg m : ℕ} {ωs : Fin n ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin 2) (Fin n)} {P : F → Polynomial F} {v₀ v₁ : F[X]}
    {Q : (RatFunc F)[X][Y]} {d : F[X]} {Q₀ : (F[X])[X][Y]}
    (hQ : GuruswamiSudan.Conditions deg m (gs_degree_bound deg n m)
      (GuruswamiSudan.OverRatFunc.liftedDomain ωs)
      (GuruswamiSudan.OverRatFunc.genericFold (u 0) (u 1)) Q)
    (hrep : Q₀.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F))) =
      Polynomial.C (Polynomial.C (algebraMap F[X] (RatFunc F) d)) * Q)
    (hk : deg + 1 ≤ n) (hm : 1 ≤ m) (hdeg2 : 2 ≤ deg)
    (res : PerZResidual deg m ωs δ u P v₀ v₁ Q₀) :
    InterpolantInputSupply.GSLineInput deg m ωs δ u P v₀ v₁ where
  Q := Q
  d := d
  Q₀ := Q₀
  hQ := hQ
  hrep := hrep
  hk := hk
  hm := hm
  hdeg2 := hdeg2
  hgood := res.hgood
  hPdeg := res.hPdeg
  hPdist := res.hPdist
  hQdist := res.hQdist
  h0 := res.h0
  hsep := res.hsep

/-- **`GSLineInput` minus its per-`z` fields, from numerics (the Johnson producer).**
The numeric Johnson-regime conditions (`deg + 1 ≤ n`, `1 ≤ m`, `2 ≤ deg`) discharge ALL
global fields via the canonical in-tree GS chain; only the per-word `PerZResidual` (about
the canonical representative) remains. -/
noncomputable def gsLineInput_of_johnson {deg m : ℕ} {ωs : Fin n ↪ F} {δ : ℝ≥0}
    {u : WordStack F (Fin 2) (Fin n)} {P : F → Polynomial F} {v₀ v₁ : F[X]}
    (hk : deg + 1 ≤ n) (hm : 1 ≤ m) (hdeg2 : 2 ≤ deg)
    (res : PerZResidual deg m ωs δ u P v₀ v₁
      (canonicalRep deg m ωs (u 0) (u 1) hdeg2 (NeZero.ne n) hm)) :
    InterpolantInputSupply.GSLineInput deg m ωs δ u P v₀ v₁ :=
  gsLineInput_of_chain
    (canonicalQ_conditions deg m ωs (u 0) (u 1) hdeg2 (NeZero.ne n) hm)
    (canonicalRep_map deg m ωs (u 0) (u 1) hdeg2 (NeZero.ne n) hm)
    hk hm hdeg2 res

end Producers

end GSLineInputSupply

/-! ## The capstone: `hPz` from the numeric Johnson conditions + per-word residual -/

section HPz

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

/-- **`hPz` from the numeric Johnson conditions (the capstone).**  The consumer supplies no
GS interpolant at all: the numeric Johnson-regime conditions (`deg + 1 ≤ n`, `1 ≤ m`,
`2 ≤ deg`) produce the whole global GS chain in-tree, and only the per-representative
per-word residual (`PerZResidual` about the canonical representative) and the linear degree
bounds remain.  The conclusion is the full `hPz` field, derived by Hensel uniqueness through
`hPz_of_gs_line` ∘ `gsLineInput_of_johnson`. -/
theorem hPz_of_johnson_conditions {deg m : ℕ} {ωs : Fin n ↪ F} {δ : ℝ≥0}
    {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]} [Fact (Irreducible H)] [Fact (0 < H.natDegree)]
    {hHyp : BCIKS20AppendixA.ClaimA2.Hypotheses x₀ R H}
    {u : WordStack F (Fin 2) (Fin n)} {P : F → Polynomial F}
    (hk : deg + 1 ≤ n) (hm : 1 ≤ m) (hdeg2 : 2 ≤ deg)
    (hres : ∀ v₀ v₁ : F[X],
      BCIKS20AppendixA.ClaimA2.γ x₀ R H hHyp = BCIKS20AppendixA.polyToPowerSeries𝕃 H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      GSLineInputSupply.PerZResidual deg m ωs δ u P v₀ v₁
        (GSLineInputSupply.canonicalRep deg m ωs (u 0) (u 1) hdeg2 (NeZero.ne n) hm))
    (hdeg : ∀ v₀ v₁ : F[X],
      BCIKS20AppendixA.ClaimA2.γ x₀ R H hHyp = BCIKS20AppendixA.polyToPowerSeries𝕃 H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      v₀.natDegree < 1 + 1 ∧ v₁.natDegree < 1 + 1) :
    ∀ v₀ v₁ : F[X],
      BCIKS20AppendixA.ClaimA2.γ x₀ R H hHyp = BCIKS20AppendixA.polyToPowerSeries𝕃 H
        ((Polynomial.map Polynomial.C v₀)
          + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)) →
      (∀ z ∈ RS_goodCoeffsCurve (k := 1) (deg := deg) (domain := ωs) u δ,
        P z = ((Polynomial.map Polynomial.C v₀)
            + (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)).eval
            (Polynomial.C z))
        ∧ v₀.natDegree < 1 + 1 ∧ v₁.natDegree < 1 + 1 :=
  ArkLib.hPz_of_gs_line
    (fun v₀ v₁ hlin =>
      GSLineInputSupply.gsLineInput_of_johnson hk hm hdeg2 (hres v₀ v₁ hlin))
    hdeg

end HPz

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.GSLineInputSupply.exists_gs_chain
#print axioms ArkLib.GSLineInputSupply.canonicalQ
#print axioms ArkLib.GSLineInputSupply.canonicalDenom
#print axioms ArkLib.GSLineInputSupply.canonicalRep
#print axioms ArkLib.GSLineInputSupply.canonicalDenom_ne_zero
#print axioms ArkLib.GSLineInputSupply.canonicalQ_conditions
#print axioms ArkLib.GSLineInputSupply.canonicalRep_map
#print axioms ArkLib.GSLineInputSupply.rep_ne_zero
#print axioms ArkLib.GSLineInputSupply.specialization_collapse_finite
#print axioms ArkLib.GSLineInputSupply.canonicalRep_ne_zero
#print axioms ArkLib.GSLineInputSupply.canonicalRep_collapse_finite
#print axioms ArkLib.GSLineInputSupply.PerZResidual
#print axioms ArkLib.GSLineInputSupply.gsLineInput_of_chain
#print axioms ArkLib.GSLineInputSupply.gsLineInput_of_johnson
#print axioms ArkLib.hPz_of_johnson_conditions
