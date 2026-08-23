/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25BranchPinning

/-!
# The linear-factor capture: branch existence is free at `deg_Y = 1`

The open core of #302 is the existence of the global branch through a component's
section. This file proves it **for `Y`-linear factors** — there the branch *is* the
rational section `−r₀/r₁`, and the decode family satisfies a global algebraic identity
by the factor theorem alone, with no Hensel and no Λ-weight counting:

* `linear_factor_decode_eq` — a decode dividing a `Y`-linear specialization satisfies
  `p · G.coeff 1 = −G.coeff 0` (factor theorem + degree count in the domain `F[X][Y]`);
* `linear_factor_decode_unique` — hence at nonvanishing leading coefficient the decode
  is **determined** (no choice in the family);
* **`linear_factor_family_identity`** — the family-level form: every cell decode
  satisfies `P γ · r₁|_γ = −r₀|_γ` for the *global* coefficients `r₁ = R.coeff 1`,
  `r₀ = R.coeff 0` of the `Y`-linear factor — the deg`_Y = 1` case of the C5.8 branch
  existence, with the branch data `(r₀, r₁)` carrying `R`'s own degree budgets;
* `linear_factor_global_dvd` — when the section clears globally (`r₁ ∣ r₀` in
  `F[Z][X]`), the quotient is the **literal global branch** `pHat` of
  `pinning_of_global_branch`: per-`γ` divisibility holds at every nonvanishing scalar.

What remains of the open core after this file is branch existence for components with
`deg_Y ≥ 2` — the genuinely transcendental-feeling half of C5.8 (Hensel series over the
function field + Λ-weight bounds, the #138/#139 kernel).

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Polynomial Polynomial.Bivariate Finset

attribute [local instance] Classical.propDecidable

variable {F₀ : Type} [Field F₀]

/-- **The factor theorem at `Y`-degree one**: a monic-linear divisor of a `Y`-linear
polynomial reads off its root — `p · G.coeff 1 = −G.coeff 0`. -/
theorem linear_factor_decode_eq {G : F₀[X][Y]} {p : F₀[X]}
    (hY : G.natDegree ≤ 1)
    (hdvd : (Polynomial.X - Polynomial.C p) ∣ G) :
    p * G.coeff 1 = -(G.coeff 0) := by
  classical
  obtain ⟨q, hq⟩ := hdvd
  rcases eq_or_ne G 0 with rfl | hG0
  · simp
  -- the cofactor is a constant
  have hq0 : q ≠ 0 := by
    intro habs
    rw [habs, mul_zero] at hq
    exact hG0 hq
  have hlin : (Polynomial.X - Polynomial.C p).natDegree = 1 := by
    simpa using Polynomial.natDegree_X_sub_C p
  have hdegmul : G.natDegree =
      (Polynomial.X - Polynomial.C p).natDegree + q.natDegree := by
    rw [hq]
    exact Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero p) hq0
  have hqdeg : q.natDegree = 0 := by omega
  obtain ⟨c, rfl⟩ := Polynomial.natDegree_eq_zero.mp hqdeg
  -- expand and match coefficients
  have h0 : G.coeff 0 = -(p * c) := by
    rw [hq, Polynomial.coeff_mul_C, Polynomial.coeff_sub, Polynomial.coeff_X_zero,
      Polynomial.coeff_C_zero, zero_sub, neg_mul]
  have h1 : G.coeff 1 = c := by
    rw [hq, Polynomial.coeff_mul_C, Polynomial.coeff_sub, Polynomial.coeff_X_one,
      Polynomial.coeff_C]
    norm_num
  rw [h0, h1, neg_neg]

/-- **Determinacy**: at nonvanishing leading coefficient, the decode of a `Y`-linear
specialization is unique — the family carries no choice. -/
theorem linear_factor_decode_unique {G : F₀[X][Y]} {p p' : F₀[X]}
    (hY : G.natDegree ≤ 1) (hc : G.coeff 1 ≠ 0)
    (hdvd : (Polynomial.X - Polynomial.C p) ∣ G)
    (hdvd' : (Polynomial.X - Polynomial.C p') ∣ G) :
    p = p' := by
  have h1 := linear_factor_decode_eq hY hdvd
  have h2 := linear_factor_decode_eq hY hdvd'
  exact mul_right_cancel₀ hc (h1.trans h2.symm)

/-- **The family identity (deg`_Y = 1` branch existence).** For a `Y`-linear factor
`R = C r₁·Y + C r₀` (globally: `r₁ = R.coeff 1`, `r₀ = R.coeff 0` in `F[Z][X]`), every
cell decode satisfies the global algebraic identity `P γ · r₁|_γ = −r₀|_γ` — the
branch is the rational section, its data inheriting `R`'s own degree budgets. -/
theorem linear_factor_family_identity {R : (F₀[X])[X][Y]}
    (hY : R.natDegree ≤ 1) (E : Finset F₀) (P : F₀ → F₀[X])
    (hdvd : ∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) :
    ∀ γ ∈ E, P γ * (R.coeff 1).map (Polynomial.evalRingHom γ) =
      -((R.coeff 0).map (Polynomial.evalRingHom γ)) := by
  intro γ hγ
  have hYγ : (R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))).natDegree ≤ 1 :=
    le_trans (Polynomial.natDegree_map_le) hY
  have h := linear_factor_decode_eq hYγ (hdvd γ hγ)
  rwa [Polynomial.coeff_map, Polynomial.coeff_map, Polynomial.coe_mapRingHom] at h

/-- **The global branch from a cleared section**: if the `Y`-linear factor's section
clears globally (`r₁ ∣ r₀` in `F[Z][X]`), the quotient is a literal global branch —
per-`γ` divisibility holds at every scalar where the leading coefficient survives.
This is the exact `hdvdp̂` input of `pinning_of_global_branch`. -/
theorem linear_factor_global_dvd {R : (F₀[X])[X][Y]}
    (hY : R.natDegree ≤ 1) {pHat : (F₀[X])[X]}
    (hclear : R.coeff 0 = -(pHat * R.coeff 1)) (γ : F₀)
    (hc : (R.coeff 1).map (Polynomial.evalRingHom γ) ≠ 0) :
    (Polynomial.X - Polynomial.C (pHat.map (Polynomial.evalRingHom γ))) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) := by
  classical
  set Rγ : F₀[X][Y] := R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ)) with hRγ
  set pγ : F₀[X] := pHat.map (Polynomial.evalRingHom γ) with hpγ
  set cγ : F₀[X] := (R.coeff 1).map (Polynomial.evalRingHom γ) with hcγ
  -- the specialization is the explicit linear polynomial
  have hcoeff1 : Rγ.coeff 1 = cγ := by
    rw [hRγ, Polynomial.coeff_map, Polynomial.coe_mapRingHom, hcγ]
  have hcoeff0 : Rγ.coeff 0 = -(pγ * cγ) := by
    rw [hRγ, Polynomial.coeff_map, Polynomial.coe_mapRingHom, hclear]
    rw [Polynomial.map_neg, Polynomial.map_mul]
  have hYγ : Rγ.natDegree ≤ 1 := le_trans (Polynomial.natDegree_map_le) hY
  -- write `Rγ` out of its two coefficients and factor
  have hexpand : Rγ = Polynomial.C (Rγ.coeff 1) * Polynomial.X +
      Polynomial.C (Rγ.coeff 0) := by
    ext j
    rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X, Polynomial.coeff_C]
    rcases j with _ | _ | j
    · simp
    · simp
    · have : Rγ.coeff (j + 2) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      simp [this]
  rw [hexpand, hcoeff1, hcoeff0]
  exact ⟨Polynomial.C cγ, by rw [Polynomial.C_neg, Polynomial.C_mul]; ring⟩

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms linear_factor_decode_eq
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms linear_factor_decode_unique
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms linear_factor_family_identity
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame in
#print axioms linear_factor_global_dvd
