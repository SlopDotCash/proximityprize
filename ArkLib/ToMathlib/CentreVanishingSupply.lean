/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.BranchValuePigeonhole
import ArkLib.Data.CodingTheory.GuruswamiSudan.GSSpecializedConditions

/-!
# Issue #304 — the centre-vanishing supply: the last §5 residual of the matching lane WIRED

`BranchValuePigeonhole.matching_supply_of_centre_vanishing` left one residual: the per-place
centre vanishing `(evalX (C x₀) Q₀)(z, y z) = 0` for the per-place decoded branch values.
This file closes it: the decoded branch value is the decoded codeword **evaluated at the
RS-domain point `x₀`**, `y z := (P z).eval x₀`, and the vanishing is the per-`z` GS matching
divisibility (`(Y − C (P z)) ∣ Q₀|_{Z:=z}` — the exact output shape of the S10 converse
`scalar_fold_decoded_divides_specialization`) **read at `x₀`**:

* `eval_hom_swap` — the evaluation-order swap, at the ring-hom level: evaluating
  `(Z, X) ↦ (z, x₀)` factors either way through the bivariate coefficient ring.
* `centre_vanishing_of_specialized_dvd` — from the per-`z` specialized matching divisibility,
  the centre vanishing at the decoded value: `(evalX (C x₀) Q₀)(z, (P z).eval x₀) = 0`.
* `hvan_of_specialized_dvd` — the family form, exactly the
  `BranchValuePigeonhole.matching_supply_of_centre_vanishing` input shape.
* `matching_supply_of_specialized_dvd` — **the composed §6 capstone**: from the
  centre-specialization factorization `evalX (C x₀) Q₀ = ∏ᵢ Hᵢ`, the per-good-place
  specialized matching divisibilities, and the count `m · n ≤ |goodSet|` — one factor
  receives an incidence set of size `≥ n` at the decoded values.  Combined with
  `incidenceRootFn[_val_monic]`: the complete `matchingSet`/`root`/`hbase` supply of the
  sound `mpFin` surface, **end-to-end from the GS divisibility lane**, F7/F8-evading.

After this file the matching lane's remaining §5 cargo is: the GS Conditions + integer
representative (produced, `GSLineInputSupply`), per-good-`z` proximity (the §5 probability
hypothesis), per-`z` non-collapse `Q₀|_{Z:=z} ≠ 0` (cofinite, `GSFactorAssignment` lane), and
the factorization of the centre specialization with a monic branch factor (S4 lane) — every
one a named, produced-or-finite GS-side fact.

## References
* [BCIKS20] §5.2.6/§6; `GSSpecializedConditions.lean` (the S10 converse).
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate BCIKS20AppendixA BCIKS20AppendixA.ClaimA2

namespace ArkLib

namespace CentreVanishingSupply

variable {F : Type} [Field F]

/-! ## The evaluation-order swap -/

/-- **The evaluation-order swap (hom level).**  Evaluating a bivariate `(F[X])[X]`-element at
`(Z, X) ↦ (z, x₀)` factors either way: `X` first (through `eval (C x₀)`) or `Z` first
(through `map (evalRingHom z)`). -/
theorem eval_hom_swap (z x₀ : F) :
    (Polynomial.evalRingHom z).comp (Polynomial.evalRingHom (Polynomial.C x₀))
      = (Polynomial.evalRingHom x₀).comp
          (Polynomial.mapRingHom (Polynomial.evalRingHom z)) := by
  refine RingHom.ext fun p => ?_
  simp only [RingHom.comp_apply, Polynomial.coe_evalRingHom, Polynomial.coe_mapRingHom]
  rw [Polynomial.eval_map, Polynomial.eval₂_evalRingHom]

/-- The bivariate-map form of the swap: the centre specialization then the place reading
equals the place specialization then the centre reading. -/
theorem evalX_map_swap (Q₀ : (F[X])[X][Y]) (z x₀ : F) :
    (Bivariate.evalX (Polynomial.C x₀) Q₀).map (Polynomial.evalRingHom z)
      = (Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))).map
          (Polynomial.evalRingHom x₀) := by
  rw [Bivariate.evalX_eq_map, Polynomial.map_map, Polynomial.map_map, eval_hom_swap]

/-! ## The centre vanishing from the specialized divisibility -/

/-- **The centre vanishing at the decoded value.**  If the per-`z` specialized matching
divisibility holds — `(Y − C P) ∣ Q₀|_{Z:=z}` (the S10-converse output shape) — then the
centre specialization of `Q₀` vanishes at `(z, P.eval x₀)`. -/
theorem centre_vanishing_of_specialized_dvd {Q₀ : (F[X])[X][Y]} {P : F[X]} {z : F}
    (hdvd : Polynomial.X - Polynomial.C P ∣
      Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))) (x₀ : F) :
    Polynomial.evalEval z (P.eval x₀)
      (Bivariate.evalX (Polynomial.C x₀) Q₀) = 0 := by
  -- read the divisibility at the RS point x₀
  have h1 := Polynomial.map_dvd (Polynomial.evalRingHom x₀) hdvd
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at h1
  have h2 : ((Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))).map
      (Polynomial.evalRingHom x₀)).eval ((Polynomial.evalRingHom x₀) P) = 0 :=
    Polynomial.dvd_iff_isRoot.mp h1
  rw [Polynomial.coe_evalRingHom] at h2
  -- convert the goal through the swap
  rw [← Polynomial.eval₂_evalRingHom, ← Polynomial.eval_map, evalX_map_swap]
  exact h2

/-! ## The family form and the composed capstone -/

/-- **The `hvan` family** — the exact input shape of
`BranchValuePigeonhole.matching_supply_of_centre_vanishing`, with the decoded branch values
`y z := (Pz z).eval x₀`. -/
theorem hvan_of_specialized_dvd {Q₀ : (F[X])[X][Y]} {Pz : F → F[X]}
    {goodSet : Finset F} (x₀ : F)
    (hdvd : ∀ z ∈ goodSet, Polynomial.X - Polynomial.C (Pz z) ∣
      Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))) :
    ∀ z ∈ goodSet,
      Polynomial.evalEval z ((Pz z).eval x₀)
        (Bivariate.evalX (Polynomial.C x₀) Q₀) = 0 :=
  fun z hz => centre_vanishing_of_specialized_dvd (hdvd z hz) x₀

/-- **The composed §6 capstone: the matching supply from the GS divisibility lane.**
From the centre-specialization factorization, the per-good-place specialized matching
divisibilities (the S10-converse outputs), and the count — one factor receives an incidence
set of size `≥ n` at the decoded branch values `(Pz z).eval x₀`.  No rational-surface
hypothesis; no incidence-degree cap (F7/F8 evaded). -/
theorem matching_supply_of_specialized_dvd {ι : Type*} [DecidableEq ι] [DecidableEq F]
    {x₀ : F} {Q₀ : (F[X])[X][Y]}
    {s : Finset ι} {Hf : ι → F[X][Y]}
    (hfac : Bivariate.evalX (Polynomial.C x₀) Q₀ = ∏ i ∈ s, Hf i) (hsne : s.Nonempty)
    {Pz : F → F[X]} {goodSet : Finset F}
    (hdvd : ∀ z ∈ goodSet, Polynomial.X - Polynomial.C (Pz z) ∣
      Q₀.map (Polynomial.mapRingHom (Polynomial.evalRingHom z)))
    {n : ℕ} (hcount : s.card * n ≤ goodSet.card) :
    ∃ i ∈ s, ∃ matchingSet : Finset F,
      matchingSet ⊆ goodSet ∧ n ≤ matchingSet.card ∧
      ∀ z ∈ matchingSet,
        Polynomial.evalEval z ((Pz z).eval x₀) (Hf i) = 0 :=
  BranchValuePigeonhole.matching_supply_of_centre_vanishing
    (R := Q₀) hfac hsne (hvan_of_specialized_dvd x₀ hdvd) hcount

end CentreVanishingSupply

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.CentreVanishingSupply.eval_hom_swap
#print axioms ArkLib.CentreVanishingSupply.evalX_map_swap
#print axioms ArkLib.CentreVanishingSupply.centre_vanishing_of_specialized_dvd
#print axioms ArkLib.CentreVanishingSupply.hvan_of_specialized_dvd
#print axioms ArkLib.CentreVanishingSupply.matching_supply_of_specialized_dvd
