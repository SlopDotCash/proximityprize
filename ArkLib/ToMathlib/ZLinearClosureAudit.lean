/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.S5Genuine
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AlphaWeightClearedObstruction

/-!
# Adversarial audit of the Claim 5.9 rendering (`gammaGenuine_Z_linear_target`) — issue #304

This file audits the deepest open #304 core: the Claim 5.9 target
`S5Genuine.gammaGenuine_Z_linear_target` (`γ = v₀ + C(functionFieldT)·v₁` with all coefficients on
the `liftToFunctionField (F[X])`-line), and formalizes the decisive structural facts. Everything
here is proven, axiom-clean; the verdict is **decisive against attacking the target as stated**
outside the monic class, and clarifies what the monic residual really is.

## FINDING 1 (rendering transposition — paper-side, documented)

In [BCIKS20] §5.2.7 (fulltext 1707–1740), Claim 5.9 reads: *"There exists degree ≤ k polynomials
v₀, v₁ ∈ F_q[X], such that γ = v₀(X) + Z·v₁(X)"*, where `Z` is the **ground/substitution
variable**: `π_z(Z) = z` (the proof goes through `γ(x) = w(x, Z) = u₀(x) + Z·u₁(x)` being "a linear
polynomial in `F_q[Z]`", Claims 5.10/5.11). In-tree, the ground `F[Z]`-line of `𝕃 H` is the image
of `liftToFunctionField : F[X] →+* 𝕃 H` (see the `RationalFunctionsCore` note "Here `F[X][Y]` is
`F[Z][T]`", and `π_z_lift := evalEvalRingHom z root.1`), while `functionFieldT` is the paper's
**`T`** — the adjoined root of `H̃`, sent by `π_z` to the *branch value* `t_z`, not to `z`. The
in-tree target (docstring: "`Z`'s image is `functionFieldT`") therefore renders "γ affine in `T`
with arbitrary `F[Z]`-coefficients" — a transposed surrogate of the paper's claim, not the claim.

## FINDING 2 (the faithful rendering is the curve collapse; PROVEN)

The faithful per-fixed-curve rendering of Claim 5.9 (`gammaGenuine_paperZ_linear` below: every
coefficient `αGenuine t` lies on the ground line, with `Z`-degree ≤ 1) is **FALSE for every curve
with `d_H = H.natDegree ≥ 2`** — refuted at order `0`: it would place `α₀ = T/W` on the ground
line, forcing `T` itself rational (`functionFieldT_ne_lift`), i.e. `d_H = 1`
(`natDegree_eq_one_of_gammaGenuine_paperZ_linear`). So the paper's Claim 5.9 is a **curve-collapse
statement** — its geometric proof (Claims 5.10/5.11 + interpolation) derives `d_H = 1` from the
counting hypotheses; it is *not* a coefficient property of a fixed nontrivial curve, and hence
**cannot be imported as a proof route for the in-tree per-`H` target** (which is consumed at fixed
`d_H ≥ 2` curves). The faithful consumers are the collapse/per-place formulations
(cf. `CurveFamilyZLinear.CurvePlaceReading`).

## FINDING 3 (the in-tree T-form target is FALSE for non-unit leading coefficient; PROVEN)

Even the transposed target is refuted at order `0` for every `H` with `2 ≤ d_H` whose leading
coefficient is not a unit: `α₀ = T/W` lies on the affine-in-`T` line
`lift(F[X]) + T·lift(F[X])` **iff** `IsUnit H.leadingCoeff`
(`α₀_T_repr_iff_isUnit_leadingCoeff`); hence
`not_gammaGenuine_Z_linear_target_of_not_isUnit_leadingCoeff`. Nobody should attack
`gammaGenuine_Z_linear_target` as stated outside the unit-leading-coefficient (monic-ish) class.

## FINDING 4 (span-closure dichotomy at `d_H = 2`; PROVEN both sides)

The module `M = lift(F[X]) + T·lift(F[X])` the target confines coefficients to is
**multiplicatively closed iff `d_H ≤ 2`**:
* `d_H ≥ 3`: `T² ∉ M` (`functionFieldT_sq_no_T_repr`) — `M` is not a subring, so the Newton/Hensel
  recursion (which multiplies coefficients and divides by `ζ ∉ M` in general) has **no
  recursion-local reason** to preserve `M`; any truth of the monic `d_H ≥ 3` target is a global
  geometric fact — and by FINDING 2 the paper's geometric argument proves the *collapse*, not the
  T-form target.
* `d_H = 2`: the modulus folds `T²` back into `M`
  (`T_repr_mul_closed_of_natDegree_eq_two`, `functionFieldT_sq_T_repr_of_natDegree_eq_two`), so
  `M` is closed under products — the only regime where a coefficient-recursion attack on the
  T-form target is even type-consistent.

## Honest residuals

This audit refutes/characterizes; it does not decide the truth of the T-form target for monic `H`
with `d_H ≥ 3` (deciding it negatively would need a concrete instance where some `αGenuine t`
escapes `M` — requiring an explicit Hensel-coefficient computation; positively it would need
external geometric inputs that, per FINDING 2, actually prove a different statement). All theorems
below are unconditional over their stated hypotheses; no axioms, no `sorry`.
-/

set_option linter.style.longLine false

noncomputable section

open Polynomial Polynomial.Bivariate PowerSeries
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine
open BCIKS20.HenselNumerator
open BCIKS20.HenselNumerator.S5Genuine
open BCIKS20.AlphaWeightClearedObstruction

namespace BCIKS20.ZLinearClosureAudit

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ## The injectivity-below-the-modulus engine -/

omit [Fact (Irreducible H)] in
/-- `liftBivariate` is injective on bivariate polynomials of `Y`-degree `< d_H`: two
representatives strictly below the modulus with the same image in `𝕃 H` are equal. This is the
two-sided form of `AlphaWeightClearedObstruction.liftBivariate_eq_zero_of_natDegree_lt`. -/
theorem eq_of_liftBivariate_eq_of_natDegree_lt {p q : F[X][Y]}
    (h : liftBivariate (H := H) p = liftBivariate (H := H) q)
    (hp : p.natDegree < H.natDegree) (hq : q.natDegree < H.natDegree) : p = q := by
  have hsub : liftBivariate (H := H) (p - q) = 0 := by rw [map_sub, h, sub_self]
  have hdeg : (p - q).natDegree < H.natDegree :=
    lt_of_le_of_lt (Polynomial.natDegree_sub_le p q) (max_lt hp hq)
  exact sub_eq_zero.mp (liftBivariate_eq_zero_of_natDegree_lt H hsub hdeg)

/-- The affine-in-`T` representative `C c₀ + X·C c₁` has `Y`-degree `≤ 1`. -/
theorem natDegree_linear_le (c₀ c₁ : F[X]) :
    (Polynomial.C c₀ + Polynomial.X * Polynomial.C c₁ : F[X][Y]).natDegree ≤ 1 := by
  refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
  · simp [Polynomial.natDegree_C]
  · refine le_trans (Polynomial.natDegree_mul_le) ?_
    simp [Polynomial.natDegree_X, Polynomial.natDegree_C]

/-! ## FINDING 2: the ground line does not contain `T` or `α₀` — the faithful Claim 5.9
rendering is the curve collapse -/

omit [Fact (Irreducible H)] in
/-- For `d_H ≥ 2` the adjoined root `T` is **not** on the ground `F[Z]`-line of `𝕃 H`. (In the
paper's variables: `T ∉ F_q[Z]` — the branch variable is genuinely algebraic of degree `d_H`.) -/
theorem functionFieldT_ne_lift (hdeg : 2 ≤ H.natDegree) (c : F[X]) :
    functionFieldT (H := H) ≠ liftToFunctionField (H := H) c := by
  intro h
  have hbig : liftBivariate (H := H) (Polynomial.X : F[X][Y])
      = liftBivariate (H := H) (Polynomial.C c : F[X][Y]) := by
    rw [liftBivariate_X, liftBivariate_C]; exact h
  have hX : (Polynomial.X : F[X][Y]).natDegree < H.natDegree := by
    rw [Polynomial.natDegree_X]; omega
  have hC : (Polynomial.C c : F[X][Y]).natDegree < H.natDegree := by
    rw [Polynomial.natDegree_C]; omega
  have heq := eq_of_liftBivariate_eq_of_natDegree_lt H hbig hX hC
  have h1 : (1 : ℕ) = 0 := by
    calc (1 : ℕ) = (Polynomial.X : F[X][Y]).natDegree := Polynomial.natDegree_X.symm
    _ = (Polynomial.C c : F[X][Y]).natDegree := by rw [heq]
    _ = 0 := Polynomial.natDegree_C c
  omega

/-- For `d_H ≥ 2` the order-0 Hensel coefficient `α₀ = T/W` is **not** on the ground
`F[Z]`-line. This refutes the faithful (paper-literal) Claim 5.9 rendering at order `0` for
every fixed curve with `d_H ≥ 2`. -/
theorem α₀_ne_lift (hdeg : 2 ≤ H.natDegree) (c : F[X]) :
    α₀ H ≠ liftToFunctionField (H := H) c := by
  intro h
  have hWne : liftToFunctionField (H := H) H.leadingCoeff ≠ 0 :=
    liftToFunctionField_leadingCoeff_ne_zero (H := H)
  have h2 : α₀ H * liftToFunctionField (H := H) H.leadingCoeff
      = liftToFunctionField (H := H) c * liftToFunctionField (H := H) H.leadingCoeff := by
    rw [h]
  rw [α₀, div_mul_cancel₀ _ hWne, ← map_mul] at h2
  exact functionFieldT_ne_lift H hdeg _ h2

/-- **The faithful (paper-literal) rendering of Claim 5.9** against a fixed curve `H`: every
genuine Hensel coefficient `αGenuine t` lies on the ground `F[Z]`-line with `Z`-degree `≤ 1`
(`γ = v₀(X) + Z·v₁(X)`, `v₀, v₁ ∈ F_q[X]`, fulltext 1713 — `Z` the substitution variable with
`π_z(Z) = z`, NOT the branch variable `T`). -/
def gammaGenuine_paperZ_linear (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) : Prop :=
  ∃ a b : ℕ → F, ∀ t, αGenuine H x₀ R hHyp t
    = liftToFunctionField (H := H) (Polynomial.C (a t) + Polynomial.X * Polynomial.C (b t))

/-- **FINDING 2 (refutation).** The faithful Claim 5.9 rendering is FALSE for every curve with
`d_H ≥ 2`: already `αGenuine 0 = α₀ = T/W` is off the ground line. -/
theorem not_gammaGenuine_paperZ_linear (hdeg : 2 ≤ H.natDegree)
    {x₀ : F} {R : F[X][X][Y]} (hHyp : ClaimA2.Hypotheses x₀ R H) :
    ¬ gammaGenuine_paperZ_linear H x₀ R hHyp := by
  rintro ⟨a, b, hab⟩
  have h0 := hab 0
  rw [αGenuine_zero] at h0
  exact α₀_ne_lift H hdeg _ h0

/-- **FINDING 2 (collapse form).** The faithful Claim 5.9 rendering *is* the curve collapse:
if it holds then `d_H = 1`. This is the machine-checked reason the paper's §5.2.7 geometric
argument (which proves exactly this rendering from the counting hypotheses) cannot serve as a
proof route for any per-fixed-curve target at `d_H ≥ 2`. -/
theorem natDegree_eq_one_of_gammaGenuine_paperZ_linear
    {x₀ : F} {R : F[X][X][Y]} (hHyp : ClaimA2.Hypotheses x₀ R H)
    (h : gammaGenuine_paperZ_linear H x₀ R hHyp) : H.natDegree = 1 := by
  have hpos : 0 < H.natDegree := Fact.out (p := 0 < H.natDegree)
  by_contra hne
  exact not_gammaGenuine_paperZ_linear H (by omega) hHyp h

/-! ## FINDING 3: the in-tree T-form target forces a unit leading coefficient -/

/-- **The order-0 membership characterization.** For `d_H ≥ 2`, the base coefficient
`α₀ = T/W` lies on the affine-in-`T` line `lift(F[X]) + T·lift(F[X])` **iff** the leading
coefficient `W = H.leadingCoeff` is a unit of `F[X]`. (Forward: clearing `W` and comparing
degree-`< d_H` representatives forces `c₁·W = 1`; backward: `α₀ = 0 + T·lift(W⁻¹)`.) -/
theorem α₀_T_repr_iff_isUnit_leadingCoeff (hdeg : 2 ≤ H.natDegree) :
    (∃ c₀ c₁ : F[X], α₀ H
        = liftToFunctionField (H := H) c₀
          + functionFieldT (H := H) * liftToFunctionField (H := H) c₁)
      ↔ IsUnit H.leadingCoeff := by
  have hWne : liftToFunctionField (H := H) H.leadingCoeff ≠ 0 :=
    liftToFunctionField_leadingCoeff_ne_zero (H := H)
  constructor
  · rintro ⟨c₀, c₁, h⟩
    -- Clear the denominator: `T = (lift c₀ + T·lift c₁) · lift W`.
    have h2 : α₀ H * liftToFunctionField (H := H) H.leadingCoeff
        = (liftToFunctionField (H := H) c₀
            + functionFieldT (H := H) * liftToFunctionField (H := H) c₁)
          * liftToFunctionField (H := H) H.leadingCoeff := by rw [h]
    rw [α₀, div_mul_cancel₀ _ hWne] at h2
    -- Pass to bivariate representatives below the modulus.
    have hbig : liftBivariate (H := H) (Polynomial.X : F[X][Y])
        = liftBivariate (H := H)
            ((Polynomial.C c₀ + Polynomial.X * Polynomial.C c₁)
              * Polynomial.C H.leadingCoeff) := by
      simp only [map_mul, map_add, liftBivariate_C, liftBivariate_X]
      exact h2
    have hX : (Polynomial.X : F[X][Y]).natDegree < H.natDegree := by
      rw [Polynomial.natDegree_X]; omega
    have hrle : ((Polynomial.C c₀ + Polynomial.X * Polynomial.C c₁)
        * Polynomial.C H.leadingCoeff : F[X][Y]).natDegree ≤ 1 := by
      refine le_trans (Polynomial.natDegree_mul_le) ?_
      rw [Polynomial.natDegree_C, add_zero]
      exact natDegree_linear_le c₀ c₁
    have heq := eq_of_liftBivariate_eq_of_natDegree_lt H hbig hX
      (lt_of_le_of_lt hrle (by omega))
    -- Compare the `Y`-coefficient at degree `1`: `1 = c₁ · W`.
    have h1 : (Polynomial.X : F[X][Y]).coeff 1
        = ((Polynomial.C c₀ + Polynomial.X * Polynomial.C c₁)
            * Polynomial.C H.leadingCoeff).coeff 1 :=
      congrArg (fun r : F[X][Y] => r.coeff 1) heq
    have hXC : (Polynomial.X * Polynomial.C c₁ : F[X][Y]).coeff 1 = c₁ := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, Polynomial.coeff_X_mul, Polynomial.coeff_C_zero]
    rw [Polynomial.coeff_X_one, Polynomial.coeff_mul_C, Polynomial.coeff_add, hXC] at h1
    simp only [Polynomial.coeff_C, if_neg (one_ne_zero (α := ℕ))] at h1
    rw [zero_add] at h1
    exact IsUnit.of_mul_eq_one c₁ (by rw [mul_comm]; exact h1.symm)
  · intro hu
    obtain ⟨u, hu_eq⟩ := hu.exists_right_inv
    refine ⟨0, u, ?_⟩
    rw [map_zero, zero_add, α₀, div_eq_iff hWne, mul_assoc, ← map_mul,
      show u * H.leadingCoeff = 1 from by rw [mul_comm]; exact hu_eq, map_one, mul_one]

/-- **FINDING 3 (positive form).** If the in-tree Claim 5.9 target
`gammaGenuine_Z_linear_target` holds for a curve with `d_H ≥ 2`, then `H.leadingCoeff` is a
unit. (Extract the order-0 coefficient of the target and apply the membership
characterization.) -/
theorem isUnit_leadingCoeff_of_gammaGenuine_Z_linear_target (hdeg : 2 ≤ H.natDegree)
    {x₀ : F} {R : F[X][X][Y]} (hHyp : ClaimA2.Hypotheses x₀ R H)
    (h : gammaGenuine_Z_linear_target H x₀ R hHyp) : IsUnit H.leadingCoeff := by
  obtain ⟨v₀, v₁, hsum, hco⟩ := h
  obtain ⟨c₀, c₁, h₀, h₁⟩ := hco 0
  have hα : α₀ H
      = liftToFunctionField (H := H) c₀
        + functionFieldT (H := H) * liftToFunctionField (H := H) c₁ := by
    have hc := congrArg (fun s => PowerSeries.coeff 0 s) hsum
    simp only [map_add, PowerSeries.coeff_C_mul, h₀, h₁] at hc
    rw [← hc, ← αGenuine_zero (H := H) x₀ R hHyp]
    rfl
  exact (α₀_T_repr_iff_isUnit_leadingCoeff H hdeg).mp ⟨c₀, c₁, hα⟩

/-- **FINDING 3 (refutation form, THE DECISIVE ONE).** For every curve `H` with `d_H ≥ 2` whose
leading coefficient is not a unit, the in-tree Claim 5.9 target
`gammaGenuine_Z_linear_target` is **FALSE** — for all `x₀`, `R`, `hHyp`. Already the order-0
coefficient `α₀ = T/W` escapes the affine-in-`T` line. Do not attack the target as stated
outside the unit-leading-coefficient class. -/
theorem not_gammaGenuine_Z_linear_target_of_not_isUnit_leadingCoeff
    (hdeg : 2 ≤ H.natDegree) (hlc : ¬ IsUnit H.leadingCoeff)
    {x₀ : F} {R : F[X][X][Y]} (hHyp : ClaimA2.Hypotheses x₀ R H) :
    ¬ gammaGenuine_Z_linear_target H x₀ R hHyp :=
  fun h => hlc (isUnit_leadingCoeff_of_gammaGenuine_Z_linear_target H hdeg hHyp h)

/-! ## FINDING 4: the span-closure dichotomy at `d_H = 2` -/

omit [Fact (Irreducible H)] in
/-- **`d_H ≥ 3`: the affine-in-`T` line is not multiplicatively closed** — `T·T = T²` escapes
`lift(F[X]) + T·lift(F[X])`. Consequence for the Hensel/Newton recursion: the iteration
multiplies coefficients, and already the square of the (monic-case) base coefficient `α₀ = T`
leaves the module the target confines coefficients to; no recursion-local argument can close
the target for `d_H ≥ 3`. -/
theorem functionFieldT_sq_no_T_repr (hdeg : 3 ≤ H.natDegree) :
    ¬ ∃ c₀ c₁ : F[X], functionFieldT (H := H) ^ 2
        = liftToFunctionField (H := H) c₀
          + functionFieldT (H := H) * liftToFunctionField (H := H) c₁ := by
  rintro ⟨c₀, c₁, h⟩
  have hbig : liftBivariate (H := H) ((Polynomial.X : F[X][Y]) ^ 2)
      = liftBivariate (H := H)
          (Polynomial.C c₀ + Polynomial.X * Polynomial.C c₁) := by
    simp only [map_pow, map_add, map_mul, liftBivariate_C, liftBivariate_X]
    exact h
  have hsq : ((Polynomial.X : F[X][Y]) ^ 2).natDegree < H.natDegree := by
    rw [Polynomial.natDegree_X_pow]; omega
  have hlin : (Polynomial.C c₀ + Polynomial.X * Polynomial.C c₁ : F[X][Y]).natDegree
      < H.natDegree := lt_of_le_of_lt (natDegree_linear_le c₀ c₁) (by omega)
  have heq := eq_of_liftBivariate_eq_of_natDegree_lt H hbig hsq hlin
  have h2 : (2 : ℕ) ≤ 1 := by
    calc (2 : ℕ) = ((Polynomial.X : F[X][Y]) ^ 2).natDegree :=
          (Polynomial.natDegree_X_pow 2).symm
    _ = (Polynomial.C c₀ + Polynomial.X * Polynomial.C c₁ : F[X][Y]).natDegree := by rw [heq]
    _ ≤ 1 := natDegree_linear_le c₀ c₁
  omega

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- Reduction mod the monicized modulus `H̃'` is invisible to `liftBivariate`: the fold-back
engine for FINDING 4's positive side. -/
theorem liftBivariate_modByMonic (p : F[X][Y]) :
    liftBivariate (H := H) (p %ₘ H_tilde' H) = liftBivariate (H := H) p := by
  have hzero : liftBivariate (H := H) (H_tilde' H) = 0 := by
    have hb : ToRatFunc.bivPolyHom (H_tilde' H) = H_tilde H := by
      rw [show ToRatFunc.bivPolyHom (H_tilde' H)
          = (H_tilde' H).map (ToRatFunc.univPolyHom (F := F)) from rfl,
        H_tilde_equiv_H_tilde']
    simp only [liftBivariate, RingHom.comp_apply, hb]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  conv_rhs => rw [← Polynomial.modByMonic_add_div p (H_tilde' H)]
  rw [map_add, map_mul, hzero, zero_mul, add_zero]

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- Any element of `𝕃 H` represented below `Y`-degree `2` is on the affine-in-`T` line. -/
theorem exists_T_repr_of_natDegree_le_one {q : F[X][Y]} (hq : q.natDegree ≤ 1) :
    ∃ c₀ c₁ : F[X], liftBivariate (H := H) q
      = liftToFunctionField (H := H) c₀
        + functionFieldT (H := H) * liftToFunctionField (H := H) c₁ := by
  refine ⟨q.coeff 0, q.coeff 1, ?_⟩
  conv_lhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one hq]
  simp only [map_add, map_mul, liftBivariate_C, liftBivariate_X]
  ring

omit [Fact (Irreducible H)] in
/-- **`d_H = 2`: the affine-in-`T` line IS multiplicatively closed** — the modulus `H̃'` (of
`Y`-degree `2`) folds every product back below degree `2`. This is the unique regime where a
coefficient-recursion attack on the T-form target is type-consistent. -/
theorem T_repr_mul_closed_of_natDegree_eq_two (hdeg2 : H.natDegree = 2)
    (c₀ c₁ d₀ d₁ : F[X]) :
    ∃ e₀ e₁ : F[X],
      (liftToFunctionField (H := H) c₀
          + functionFieldT (H := H) * liftToFunctionField (H := H) c₁)
        * (liftToFunctionField (H := H) d₀
            + functionFieldT (H := H) * liftToFunctionField (H := H) d₁)
      = liftToFunctionField (H := H) e₀
          + functionFieldT (H := H) * liftToFunctionField (H := H) e₁ := by
  have hHdeg : 0 < H.natDegree := Fact.out (p := 0 < H.natDegree)
  have hmonic := H_tilde'_monic H hHdeg
  set p : F[X][Y] := (Polynomial.C c₀ + Polynomial.X * Polynomial.C c₁)
      * (Polynomial.C d₀ + Polynomial.X * Polynomial.C d₁) with hp
  have hHt : (H_tilde' H).degree = ((2 : ℕ) : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hmonic.ne_zero, natDegree_H_tilde' hHdeg, hdeg2]
  have hlt : (p %ₘ H_tilde' H).degree < ((2 : ℕ) : WithBot ℕ) := by
    rw [← hHt]; exact Polynomial.degree_modByMonic_lt p hmonic
  have hq1 : (p %ₘ H_tilde' H).natDegree ≤ 1 := by
    rcases eq_or_ne (p %ₘ H_tilde' H) 0 with h0 | h0
    · rw [h0, Polynomial.natDegree_zero]; omega
    · have h2 : (p %ₘ H_tilde' H).natDegree < 2 :=
        (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hlt
      omega
  obtain ⟨e₀, e₁, he⟩ := exists_T_repr_of_natDegree_le_one H hq1
  refine ⟨e₀, e₁, ?_⟩
  calc (liftToFunctionField (H := H) c₀
          + functionFieldT (H := H) * liftToFunctionField (H := H) c₁)
        * (liftToFunctionField (H := H) d₀
            + functionFieldT (H := H) * liftToFunctionField (H := H) d₁)
      = liftBivariate (H := H) p := by
        rw [hp]; simp only [map_mul, map_add, liftBivariate_C, liftBivariate_X]
    _ = liftBivariate (H := H) (p %ₘ H_tilde' H) := (liftBivariate_modByMonic H p).symm
    _ = liftToFunctionField (H := H) e₀
          + functionFieldT (H := H) * liftToFunctionField (H := H) e₁ := he

omit [Fact (Irreducible H)] in
/-- **`d_H = 2` fold-back, explicit instance:** `T²` lies on the affine-in-`T` line. The exact
complement of `functionFieldT_sq_no_T_repr`: the dichotomy is sharp at `d_H = 2`. -/
theorem functionFieldT_sq_T_repr_of_natDegree_eq_two (hdeg2 : H.natDegree = 2) :
    ∃ c₀ c₁ : F[X], functionFieldT (H := H) ^ 2
      = liftToFunctionField (H := H) c₀
        + functionFieldT (H := H) * liftToFunctionField (H := H) c₁ := by
  obtain ⟨e₀, e₁, he⟩ := T_repr_mul_closed_of_natDegree_eq_two H hdeg2 0 1 0 1
  refine ⟨e₀, e₁, ?_⟩
  rw [← he, map_zero, map_one, mul_one, zero_add]
  ring

/-! ## The combined verdict -/

/-- **The audit verdict, combined.** For any curve `H` with `d_H ≥ 2`: (a) the faithful
(ground-`Z`) rendering of Claim 5.9 fails outright (it is the `d_H = 1` collapse), and (b) the
in-tree (T-form) target forces a unit leading coefficient — so as stated it is attackable at
most on the monic-ish class, where (FINDING 4) only `d_H = 2` admits a span-local route. -/
theorem claim59_rendering_dichotomy (hdeg : 2 ≤ H.natDegree)
    {x₀ : F} {R : F[X][X][Y]} (hHyp : ClaimA2.Hypotheses x₀ R H) :
    ¬ gammaGenuine_paperZ_linear H x₀ R hHyp ∧
      (gammaGenuine_Z_linear_target H x₀ R hHyp → IsUnit H.leadingCoeff) :=
  ⟨not_gammaGenuine_paperZ_linear H hdeg hHyp,
    isUnit_leadingCoeff_of_gammaGenuine_Z_linear_target H hdeg hHyp⟩

end BCIKS20.ZLinearClosureAudit

end

section AxiomAudit

#print axioms BCIKS20.ZLinearClosureAudit.eq_of_liftBivariate_eq_of_natDegree_lt
#print axioms BCIKS20.ZLinearClosureAudit.natDegree_linear_le
#print axioms BCIKS20.ZLinearClosureAudit.functionFieldT_ne_lift
#print axioms BCIKS20.ZLinearClosureAudit.α₀_ne_lift
#print axioms BCIKS20.ZLinearClosureAudit.gammaGenuine_paperZ_linear
#print axioms BCIKS20.ZLinearClosureAudit.not_gammaGenuine_paperZ_linear
#print axioms BCIKS20.ZLinearClosureAudit.natDegree_eq_one_of_gammaGenuine_paperZ_linear
#print axioms BCIKS20.ZLinearClosureAudit.α₀_T_repr_iff_isUnit_leadingCoeff
#print axioms BCIKS20.ZLinearClosureAudit.isUnit_leadingCoeff_of_gammaGenuine_Z_linear_target
#print axioms BCIKS20.ZLinearClosureAudit.not_gammaGenuine_Z_linear_target_of_not_isUnit_leadingCoeff
#print axioms BCIKS20.ZLinearClosureAudit.functionFieldT_sq_no_T_repr
#print axioms BCIKS20.ZLinearClosureAudit.liftBivariate_modByMonic
#print axioms BCIKS20.ZLinearClosureAudit.exists_T_repr_of_natDegree_le_one
#print axioms BCIKS20.ZLinearClosureAudit.T_repr_mul_closed_of_natDegree_eq_two
#print axioms BCIKS20.ZLinearClosureAudit.functionFieldT_sq_T_repr_of_natDegree_eq_two
#print axioms BCIKS20.ZLinearClosureAudit.claim59_rendering_dichotomy

end AxiomAudit
