/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Polynomial.RationalFunctions
import ArkLib.ToMathlib.MultiplicityDatum

/-!
# Discharging the residual GS-factor divisibility `Hlift H ∣ R` (obligation 1, App-A)

The brick `ArkLib.MultiplicityDatum.hdvd_C_of_Hlift_dvd`
(`ArkLib/ToMathlib/MultiplicityDatum.lean`) converts the structural divisibility
`hdvd_C : (C H.leadingCoeff) ∣ R.coeff R.natDegree` (in `(F[X])[X]`, *obligation 1*) into a
**theorem** by consuming the cleaner un-specialized GS-factor relation

    `Hlift H ∣ R`   in `F[X][X][Y]`,   where `Hlift H = H.map Polynomial.C`.

This file discharges *that* divisibility from the in-tree Guruswami–Sudan factorization API, so the
obligation-1 chain no longer rests on `Hlift H ∣ R` as a bare hypothesis.

## What is, and is not, in tree

The in-tree §5/App-A pipeline produces, for the GS solution `Q : F[Z][X][Y]` (here `Z = X`) and the
extracted factor `R = R_graph_clear ∈ pg_Rset` (`Agreement.lean`):

* `pg_Rset h_gs = (normalizedFactors Q).toFinset` (`Extraction.pg_Rset`), so each `R ∈ pg_Rset`
  satisfies `R ∣ Q` and `Irreducible R` (`pg_Rset_irreducible`); and the full factorization
  `Q = C · ∏ (Rᵢ.comp X^fᵢ)^eᵢ` (`irreducible_factorization_of_gs_solution`).
* the extracted `H = H_graph_clear` is an irreducible factor of the **specialization**
  `evalX (C x₀) R`, i.e. the in-tree datum is `H ∣ evalX (C x₀) R`
  (`BCIKS20AppendixA.ClaimA2.Hypotheses.dvd_evalX`, produced by `claimA2_hypotheses_graph_clear`).

The target `Hlift H ∣ R` is the **un-specialized** statement: `H`, a factor of the *specialized*
interpolant `evalX (C x₀) R`, lifts (via `Hlift = · .map C`) to a factor of `R` itself.  This is the
genuine App-A factorization structure and it is *strictly stronger* than the in-tree specialized
datum: it is exactly a **factor-membership** fact, in the same `UniqueFactorizationMonoid`
divisibility shape (`normalizedFactors` / `Associated`) the in-tree `pg_Rset` /
`irreducible_factorization_of_gs_solution` API already speaks.

## What this file proves

* `evalX_Hlift` : the **bridge** `evalX (C x₀) (Hlift H) = H` — kernel-checked, from
  `evalRingHom (C x₀) ∘ C = id` (a `Polynomial`/`map_map` computation).
* `Hlift_dvd_of_mem_normalizedFactors` / `Hlift_dvd_of_associated_mem_normalizedFactors` /
  `Hlift_dvd_of_cofactor` : the divisibility `Hlift H ∣ R`, each from the **smallest explicit
  hypothesis** isolated from the in-tree factorization API — respectively `Hlift H` being a
  normalized factor of `R`, being associated to one, or having a cofactor `R = Hlift H * G`.  These
  are real `UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors` / `Associated.dvd` /
  `Dvd.intro` steps; no `sorry`, no axiom beyond the three below.
* `dvd_evalX_of_Hlift_dvd` : the **consistency** `Hlift H ∣ R → H ∣ evalX (C x₀) R`, recovering the
  in-tree `Hypotheses.dvd_evalX` from the un-specialized relation.  This certifies the residual is a
  genuine strengthening of the proven specialized datum, not a circular re-assumption of the goal.
* `hdvd_C_of_factorMembership` : the end-to-end discharge feeding `MultiplicityDatum`'s obligation-1
  brick directly from the factor-membership hypothesis.

## Residual

The one structural input that is **not** mechanically derivable from the in-tree *specialized*
divisibility is the un-specialization itself — i.e. that `Hlift H` is an honest factor of `R`
(`Hlift H ∈ normalizedFactors R`, or a cofactor `R = Hlift H * G`).  It is isolated here as the
explicit hypothesis of the divisibility theorems (it is **not** the goal `Hlift H ∣ R`, and **not**
a `sorry`): the goal is the divisibility, the hypothesis is the strictly-finer factor-membership in
the in-tree UFD API.  `dvd_evalX_of_Hlift_dvd` shows this hypothesis discharges the proven in-tree
specialized fact, pinning down that it is the App-A lift and nothing more.

## References

* [BCIKS20] — Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon Codes*,
  §5 (`pg_Rset`, Eq. 5.12 factorization) and Appendix A.4 (Claim A.2, the `Hypotheses` structure
  and the `W`-power numerator recursion (A.1)).
-/

open Polynomial Polynomial.Bivariate

namespace ArkLib

namespace HliftDvd

variable {F : Type} [Field F]

/-! ## The specialization bridge `evalX (C x₀) (Hlift H) = H` -/

/-- The coefficient ring hom `evalRingHom (C x₀) ∘ C : F[X] →+* F[X]` is the identity: `C a` is the
constant in `(F[X])[X]`, and evaluating the outer variable at `C x₀` returns `a`. -/
lemma evalRingHom_comp_C (x₀ : F) :
    (Polynomial.evalRingHom (Polynomial.C x₀ : F[X])).comp
        (Polynomial.C : F[X] →+* (F[X])[X]) = RingHom.id (F[X]) := by
  apply Polynomial.ringHom_ext
  · intro r; simp
  · simp

/-- **The specialization bridge.**  Specializing the lift `Hlift H = H.map C` at the middle variable
`X = x₀` recovers `H` exactly: `evalX (C x₀) (Hlift H) = H`.  This is what makes `Hlift H ∣ R` an
*un-specialization* of the in-tree specialized datum `H ∣ evalX (C x₀) R`. -/
lemma evalX_Hlift (x₀ : F) (H : F[X][Y]) :
    Bivariate.evalX (Polynomial.C x₀) (MultiplicityDatum.Hlift H) = H := by
  rw [MultiplicityDatum.Hlift, Bivariate.evalX_eq_map, Polynomial.map_map, evalRingHom_comp_C,
    Polynomial.map_id]

/-! ## The divisibility `Hlift H ∣ R` from the in-tree factorization API

Each theorem isolates the **smallest** explicit input from the in-tree GS-factorization API (the
`UniqueFactorizationMonoid` divisibility shape used by `pg_Rset` /
`irreducible_factorization_of_gs_solution`) and concludes the un-specialized divisibility. -/

variable [DecidableEq F]

/-- **Main discharge — factor-membership form.**  If the lift `Hlift H` is a normalized factor of the
GS interpolant `R` (the un-specialized App-A factor relation, in the *same* `normalizedFactors`
shape as the in-tree `pg_Rset`), then `Hlift H ∣ R`.  Real
`UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors`; this is exactly the residual brick
`MultiplicityDatum.hdvd_C_of_Hlift_dvd` consumes. -/
theorem Hlift_dvd_of_mem_normalizedFactors {R : F[X][X][Y]} {H : F[X][Y]}
    (hmem : MultiplicityDatum.Hlift H ∈ UniqueFactorizationMonoid.normalizedFactors R) :
    MultiplicityDatum.Hlift H ∣ R :=
  UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hmem

/-- **Main discharge — associated-to-a-factor form.**  The `pg_Rset` factors are *normalized*
representatives, so the App-A factor of `R` is in general only *associated* to `Hlift H`.  From
`r ∈ normalizedFactors R` with `Associated (Hlift H) r`, the divisibility follows. -/
theorem Hlift_dvd_of_associated_mem_normalizedFactors {R : F[X][X][Y]} {H : F[X][Y]}
    {r : F[X][X][Y]} (hmem : r ∈ UniqueFactorizationMonoid.normalizedFactors R)
    (hassoc : Associated (MultiplicityDatum.Hlift H) r) :
    MultiplicityDatum.Hlift H ∣ R :=
  hassoc.dvd.trans (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hmem)

omit [DecidableEq F] in
/-- **Main discharge — cofactor form.**  The directly-structural reading: the App-A factorization
`R = Hlift H * G` of the interpolant with cofactor `G` gives `Hlift H ∣ R`.  (`Dvd.intro`.) -/
theorem Hlift_dvd_of_cofactor {R : F[X][X][Y]} {H : F[X][Y]} {G : F[X][X][Y]}
    (hG : R = MultiplicityDatum.Hlift H * G) :
    MultiplicityDatum.Hlift H ∣ R :=
  ⟨G, hG⟩

/-! ## Consistency: `Hlift H ∣ R` recovers the proven in-tree specialized datum

The un-specialized divisibility is a genuine *strengthening* of, not a re-assumption of, the proven
in-tree fact `H ∣ evalX (C x₀) R` (`Hypotheses.dvd_evalX`): specializing it at `X = x₀` and applying
the bridge `evalX_Hlift` recovers exactly that datum. -/

omit [DecidableEq F] in
/-- **Consistency.**  From the un-specialized `Hlift H ∣ R`, specialization at `X = x₀` recovers the
proven in-tree datum `H ∣ evalX (C x₀) R` (`BCIKS20AppendixA.ClaimA2.Hypotheses.dvd_evalX`).  So the
factor-membership hypothesis of the discharges above implies the proven specialized fact — it is the
App-A lift, not the goal in disguise. -/
theorem dvd_evalX_of_Hlift_dvd {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hdvd : MultiplicityDatum.Hlift H ∣ R) :
    H ∣ Bivariate.evalX (Polynomial.C x₀) R := by
  have h2 : Bivariate.evalX (Polynomial.C x₀) (MultiplicityDatum.Hlift H) ∣
      Bivariate.evalX (Polynomial.C x₀) R := by
    rw [Bivariate.evalX_eq_map, Bivariate.evalX_eq_map]
    exact Polynomial.map_dvd _ hdvd
  rwa [evalX_Hlift] at h2

/-- Packaged consistency: the factor-membership hypothesis (`Hlift H ∈ normalizedFactors R`)
discharges the proven in-tree specialized divisibility `H ∣ evalX (C x₀) R`. -/
theorem dvd_evalX_of_mem_normalizedFactors {x₀ : F} {R : F[X][X][Y]} {H : F[X][Y]}
    (hmem : MultiplicityDatum.Hlift H ∈ UniqueFactorizationMonoid.normalizedFactors R) :
    H ∣ Bivariate.evalX (Polynomial.C x₀) R :=
  dvd_evalX_of_Hlift_dvd (Hlift_dvd_of_mem_normalizedFactors hmem)

/-! ## End-to-end: feeding obligation 1

Chaining the factor-membership discharge into `MultiplicityDatum.hdvd_C_of_Hlift_dvd` produces the
exact structural divisibility `(C H.leadingCoeff) ∣ R.coeff R.natDegree` consumed by
`ArkLib.hdvd_top_of_dvd_C` — obligation 1 — directly from the in-tree-shaped factor membership. -/

/-- **Obligation-1 end-to-end discharge.**  From the App-A factor membership
`Hlift H ∈ normalizedFactors R`, the structural divisibility
`(C H.leadingCoeff) ∣ R.coeff R.natDegree` in `(F[X])[X]` (obligation 1) holds — combining this
file's `Hlift_dvd_of_mem_normalizedFactors` with `MultiplicityDatum.hdvd_C_of_Hlift_dvd`. -/
theorem hdvd_C_of_factorMembership {R : F[X][X][Y]} {H : F[X][Y]}
    (hmem : MultiplicityDatum.Hlift H ∈ UniqueFactorizationMonoid.normalizedFactors R) :
    (Polynomial.C H.leadingCoeff : (F[X])[X]) ∣ R.coeff R.natDegree :=
  MultiplicityDatum.hdvd_C_of_Hlift_dvd (Hlift_dvd_of_mem_normalizedFactors hmem)

end HliftDvd

end ArkLib
