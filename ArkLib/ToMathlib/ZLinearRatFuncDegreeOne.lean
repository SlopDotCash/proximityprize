/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.ZLinearClosureAudit

/-!
# Claim 5.9 windowed core, `d_H = 1` face + the RatFunc-coefficient target (issue #304)

This file probes the minimized Claim 5.9 core (`S5Genuine.gammaGenuine_Z_linear_target`, the
per-coefficient `Z`-degree-`≤ 1` shape of `αGenuine`) from the **low-degree side**: the curve
classes `d_H = 1` and `d_H ≤ 2`, where the codomain of the coefficient readings — `F[X]` via
`liftToFunctionField`, versus the full ground field `RatFunc F` — is exactly what is at stake.

## FINDING A (the `d_H = 1` face of the F[X]-target is an *integrality* statement; PROVEN)

`ZLinearClosureAudit` refuted the in-tree target for `2 ≤ d_H` with non-unit leading coefficient
via the injectivity-below-the-modulus engine. That engine is **unavailable at `d_H = 1`**
(`1` and `T` are `F(Z)`-linearly *dependent*: `T = −b̃` after monicization). Here we close the
remaining degree: for `d_H = 1` the order-0 membership `α₀ = T/W ∈ lift(F[X]) + T·lift(F[X])`
**still forces `IsUnit H.leadingCoeff`** — by a genuinely different, denominator-arithmetic
route: evaluating the function field at the rational branch point `T ↦ −φ(H.coeff 0)`
(`groundEval`, well-defined since `H̃ = T + φ(H.coeff 0)` at `d_H = 1`), the membership becomes
`b·(a·c₁ − 1) = a·c₀` in `F[X]` (`a = H.leadingCoeff`, `b = H.coeff 0`); coprimality of `a` and
`a·c₁ − 1` gives `a ∣ b`, and primitivity of the irreducible `H` forces `a` to be a unit
(`isUnit_leadingCoeff_of_α₀_T_repr_of_natDegree_eq_one`, iff-form
`α₀_T_repr_iff_isUnit_leadingCoeff_of_natDegree_eq_one`). Combining with the audit's `d_H ≥ 2`
result: the in-tree target forces `IsUnit H.leadingCoeff` at **every** degree
(`isUnit_leadingCoeff_of_gammaGenuine_Z_linear_target_all`,
`not_gammaGenuine_Z_linear_target_of_not_isUnit_leadingCoeff_all` — no degree hypothesis).

So the obstruction at `d_H = 1` is **purely about denominators** (the division by `W`), not
about `Z`-degree: the `F[X]`-codomain of the target's readings is too small.

## FINDING B (the RatFunc-coefficient target; the generalized reading is FREE for `d_H ≤ 2`)

We state the generalized target `gammaGenuine_Z_linear_target_ratfunc` — identical shape, but
the per-coefficient readings take values in the ground field `RatFunc F` (via the constant
embedding `liftRatFunc : RatFunc F →+* 𝕃 H`) instead of `F[X]`. PROVEN:

* `target_ratfunc_of_target` — the in-tree target implies the RatFunc target (so the
  generalized target is a faithful weakening; `liftToFunctionField = liftRatFunc ∘ univPolyHom`).
* `gammaGenuine_Z_linear_target_ratfunc_of_natDegree_le_two` — for `d_H ≤ 2` the RatFunc target
  holds **unconditionally** (for every `x₀`, `R`, `hHyp`): `{1, T}` spans `𝕃 H` over `F(Z)`
  when `deg H̃ ≤ 2` (`exists_ratfunc_T_repr_of_natDegree_le_two`, by `modByMonic` reduction
  below the monic modulus `H̃`). In particular the `d_H = 1` case of the RatFunc target goes
  through trivially — confirming that ALL content of the in-tree target at `d_H ≤ 2` is the
  integrality (`F[X]` vs `RatFunc F`) of the readings, none of it is `Z`-linearity.
* Recursion-closure at `d_H ≤ 2` (the compounding probe): the RatFunc affine-in-`T` line is
  closed under the Hensel recursion's operations — products
  (`ratfunc_T_repr_mul_closed_of_natDegree_le_two`) AND the `ζ`-division step
  (`ratfunc_T_repr_inv_closed_of_natDegree_le_two`), since the line is everything. The
  `F[X]`-line is product-closed at `d_H = 2` (audit FINDING 4) but NOT division-closed — that
  failure is exactly FINDING A.

## FINDING C (sharpness: `d_H ≥ 3` is the real `Z`-degree regime, even with RatFunc readings)

`functionFieldT_sq_no_ratfunc_T_repr`: for `d_H ≥ 3`, `T²` escapes the RatFunc affine-in-`T`
line (`eq_of_mk_eq_of_natDegree_lt`, the RatFunc-level injectivity-below-the-modulus engine).
So enlarging the readings to `RatFunc F` does NOT create a recursion-local route at `d_H ≥ 3`:
the genuine Claim-5.9 content there is the global geometric `Z`-degree input, for the RatFunc
target just as for the in-tree one. The successor residual
(`S5GenuineZLinearMonic.gammaGenuine_Z_linear_target_of_succ_of_monic`) remains the honest core.

## Honest residuals

* The truth of either target (F[X] or RatFunc form) for monic `H` with `d_H ≥ 3` is NOT decided
  here — that is the windowed successor residual (the paper's §5.2.7 geometric interpolation
  input). Nothing here fabricates it.
* Non-vacuity of the `d_H = 1`, non-unit-leading-coefficient class (`H = Z·Y + 1`) is exhibited
  concretely: `witnessCurve_irreducible` + `α₀_no_T_repr_witnessCurve` below.

All declarations are axiom-clean (`[propext, Classical.choice, Quot.sound]`); no
`sorry`/`admit`/`native_decide`.
-/

set_option linter.style.longLine false

noncomputable section

open Polynomial Polynomial.Bivariate PowerSeries
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine
open BCIKS20.HenselNumerator
open BCIKS20.HenselNumerator.S5Genuine

namespace BCIKS20.ZLinearRatFuncDegreeOne

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-! ## The ground-field constant embedding `RatFunc F →+* 𝕃 H` -/

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- Injectivity of the polynomial-to-rational-function coefficient embedding (public restatement
of the private `RationalFunctionsCore` fact). -/
theorem univPolyHom_inj : Function.Injective (ToRatFunc.univPolyHom (F := F)) := by
  simpa [ToRatFunc.univPolyHom] using (RatFunc.algebraMap_injective (K := F))

/-- The constant (T-degree-0) embedding of the full ground field `F(Z) = RatFunc F` into the
function field `𝕃 H`. This is the codomain the generalized Claim-5.9 readings live in; the
in-tree `liftToFunctionField` is its restriction to `F[Z] = F[X]`. -/
noncomputable def liftRatFunc (H : F[X][Y]) : RatFunc F →+* 𝕃 H :=
  RingHom.comp (Ideal.Quotient.mk (Ideal.span {H_tilde H})) Polynomial.C

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
@[simp]
theorem liftRatFunc_apply (c : RatFunc F) :
    liftRatFunc H c = Ideal.Quotient.mk (Ideal.span {H_tilde H}) (Polynomial.C c) := rfl

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
theorem functionFieldT_eq_mk :
    functionFieldT (H := H)
      = Ideal.Quotient.mk (Ideal.span {H_tilde H}) (Polynomial.X : Polynomial (RatFunc F)) := rfl

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- The in-tree coefficient embedding factors through the ground-field constant embedding:
`liftToFunctionField = liftRatFunc ∘ univPolyHom`. -/
theorem liftToFunctionField_eq_liftRatFunc (c : F[X]) :
    liftToFunctionField (H := H) c = liftRatFunc H (ToRatFunc.univPolyHom (F := F) c) := by
  show Ideal.Quotient.mk (Ideal.span {H_tilde H}) (coeffAsRatFunc c) = _
  rw [coeffAsRatFunc_eq_C]
  rfl

/-! ## The generalized (RatFunc-coefficient) Claim 5.9 target -/

/-- **The generalized Claim 5.9 target**: `γ = v₀ + C(T)·v₁` with all coefficients of `v₀, v₁` on
the full ground line `liftRatFunc (RatFunc F)` (T-degree `0`, arbitrary `Z`-denominators) —
the in-tree `gammaGenuine_Z_linear_target` with the readings relaxed from `F[X]` to `RatFunc F`.
FINDING A shows the relaxation is exactly the denominator content of the in-tree target at low
degree. -/
def gammaGenuine_Z_linear_target_ratfunc (x₀ : F) (R : F[X][X][Y])
    (hHyp : ClaimA2.Hypotheses x₀ R H) : Prop :=
  ∃ v₀ v₁ : (𝕃 H)⟦X⟧,
    gammaGenuine x₀ R H hHyp = v₀ + (PowerSeries.C (functionFieldT (H := H))) * v₁ ∧
    (∀ t, ∃ c₀ c₁ : RatFunc F,
      PowerSeries.coeff t v₀ = liftRatFunc H c₀ ∧
      PowerSeries.coeff t v₁ = liftRatFunc H c₁)

/-- The in-tree (F[X]-coefficient) target implies the generalized (RatFunc-coefficient) target:
the generalization is a faithful weakening. -/
theorem target_ratfunc_of_target {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (h : gammaGenuine_Z_linear_target H x₀ R hHyp) :
    gammaGenuine_Z_linear_target_ratfunc H x₀ R hHyp := by
  obtain ⟨v₀, v₁, hsum, hco⟩ := h
  refine ⟨v₀, v₁, hsum, fun t => ?_⟩
  obtain ⟨c₀, c₁, h₀, h₁⟩ := hco t
  exact ⟨ToRatFunc.univPolyHom (F := F) c₀, ToRatFunc.univPolyHom (F := F) c₁,
    by rw [h₀, liftToFunctionField_eq_liftRatFunc],
    by rw [h₁, liftToFunctionField_eq_liftRatFunc]⟩

/-- Per-coefficient reduction for the generalized target (the RatFunc analogue of
`gammaGenuine_Z_linear_of_coeffs_Z_linear`): per-coefficient `Z`-degree-`≤ 1` shape with RatFunc
readings assembles to the full generalized target. -/
theorem target_ratfunc_of_coeffs {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (hcoeff : ∀ t, ∃ c₀ c₁ : RatFunc F,
      αGenuine H x₀ R hHyp t
        = liftRatFunc H c₀ + functionFieldT (H := H) * liftRatFunc H c₁) :
    gammaGenuine_Z_linear_target_ratfunc H x₀ R hHyp := by
  classical
  choose c₀ c₁ hc using hcoeff
  refine ⟨PowerSeries.mk (fun t => liftRatFunc H (c₀ t)),
    PowerSeries.mk (fun t => liftRatFunc H (c₁ t)), ?_, ?_⟩
  · ext t
    rw [map_add, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
    change αGenuine H x₀ R hHyp t = _
    rw [hc t]
  · intro t
    exact ⟨c₀ t, c₁ t, by rw [PowerSeries.coeff_mk], by rw [PowerSeries.coeff_mk]⟩

/-- Per-coefficient extraction from the generalized target (converse of
`target_ratfunc_of_coeffs`): the generalized target yields the per-coefficient RatFunc readings
of every `αGenuine t`. -/
theorem coeffs_of_target_ratfunc {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H)
    (h : gammaGenuine_Z_linear_target_ratfunc H x₀ R hHyp) (t : ℕ) :
    ∃ c₀ c₁ : RatFunc F,
      αGenuine H x₀ R hHyp t
        = liftRatFunc H c₀ + functionFieldT (H := H) * liftRatFunc H c₁ := by
  obtain ⟨v₀, v₁, hsum, hco⟩ := h
  obtain ⟨c₀, c₁, h₀, h₁⟩ := hco t
  refine ⟨c₀, c₁, ?_⟩
  have hc := congrArg (fun s => PowerSeries.coeff t s) hsum
  simp only [map_add, PowerSeries.coeff_C_mul, h₀, h₁] at hc
  exact hc

/-! ## FINDING B: `{1, T}` spans `𝕃 H` over the ground field for `d_H ≤ 2` -/

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- The monicized modulus `H̃` is monic (map of the monic `H̃'`). -/
theorem H_tilde_monic (hpos : 0 < H.natDegree) : (H_tilde H).Monic := by
  have h := (H_tilde'_monic H hpos).map (ToRatFunc.univPolyHom (F := F))
  rwa [H_tilde_equiv_H_tilde' H] at h

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- `natDegree H̃ = natDegree H` (`= d_H`). -/
theorem natDegree_H_tilde (hpos : 0 < H.natDegree) :
    (H_tilde H).natDegree = H.natDegree := by
  rw [← H_tilde_equiv_H_tilde' H, (H_tilde'_monic H hpos).natDegree_map, natDegree_H_tilde' hpos]

omit [Fact (Irreducible H)] in
/-- **The spanning engine.** For `d_H ≤ 2`, every element of `𝕃 H` lies on the RatFunc
affine-in-`T` line: reduce any representative `modByMonic` the monic modulus `H̃` (degree
`≤ 2`), leaving a representative of `T`-degree `≤ 1`. This is why the generalized target is
FREE at `d_H ≤ 2` — and why the Hensel recursion trivially preserves the generalized
per-coefficient shape there (the line is everything). -/
theorem exists_ratfunc_T_repr_of_natDegree_le_two (hdeg : H.natDegree ≤ 2) (x : 𝕃 H) :
    ∃ c₀ c₁ : RatFunc F,
      x = liftRatFunc H c₀ + functionFieldT (H := H) * liftRatFunc H c₁ := by
  have hpos : 0 < H.natDegree := Fact.out (p := 0 < H.natDegree)
  have hmonic : (H_tilde H).Monic := H_tilde_monic H hpos
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  set r := p %ₘ H_tilde H with hr_def
  have hmk : Ideal.Quotient.mk (Ideal.span {H_tilde H}) p
      = Ideal.Quotient.mk (Ideal.span {H_tilde H}) r := by
    conv_lhs => rw [← Polynomial.modByMonic_add_div p (H_tilde H)]
    rw [map_add, map_mul,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), zero_mul, add_zero]
  have hrdeg : r.natDegree ≤ 1 := by
    rcases eq_or_ne r 0 with h0 | h0
    · rw [h0, Polynomial.natDegree_zero]; omega
    · have hlt : r.degree < (H_tilde H).degree := Polynomial.degree_modByMonic_lt p hmonic
      have h2 : r.natDegree < (H_tilde H).natDegree := Polynomial.natDegree_lt_natDegree h0 hlt
      rw [natDegree_H_tilde H hpos] at h2
      omega
  refine ⟨r.coeff 0, r.coeff 1, ?_⟩
  rw [hmk]
  conv_lhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one hrdeg]
  rw [map_add, map_mul, liftRatFunc_apply, liftRatFunc_apply, functionFieldT_eq_mk]
  ring

/-- **The generalized Claim 5.9 target holds unconditionally for `d_H ≤ 2`** — for every `x₀`,
`R`, `hHyp`. In particular the `d_H = 1` case of the RatFunc-coefficient reading goes through
(trivially). Together with FINDING A this pins the entire content of the in-tree target at
`d_H ≤ 2` on the *integrality* of the readings (`F[X]` vs `RatFunc F`), not on `Z`-linearity. -/
theorem gammaGenuine_Z_linear_target_ratfunc_of_natDegree_le_two (hdeg : H.natDegree ≤ 2)
    {x₀ : F} {R : F[X][X][Y]} (hHyp : ClaimA2.Hypotheses x₀ R H) :
    gammaGenuine_Z_linear_target_ratfunc H x₀ R hHyp :=
  target_ratfunc_of_coeffs H hHyp (fun t =>
    exists_ratfunc_T_repr_of_natDegree_le_two H hdeg (αGenuine H x₀ R hHyp t))

omit [Fact (Irreducible H)] in
/-- Recursion-closure probe, multiplicative step (`d_H ≤ 2`, RatFunc line): products of elements
on the RatFunc affine-in-`T` line stay on it. -/
theorem ratfunc_T_repr_mul_closed_of_natDegree_le_two (hdeg : H.natDegree ≤ 2) (x y : 𝕃 H) :
    ∃ c₀ c₁ : RatFunc F,
      x * y = liftRatFunc H c₀ + functionFieldT (H := H) * liftRatFunc H c₁ :=
  exists_ratfunc_T_repr_of_natDegree_le_two H hdeg (x * y)

/-- Recursion-closure probe, division step (`d_H ≤ 2`, RatFunc line): inverses stay on the
RatFunc affine-in-`T` line. This is the step the `F[X]`-line lacks (the Hensel recursion divides
by `ζ` and by powers of `W` — FINDING A is exactly that failure at order `0`). -/
theorem ratfunc_T_repr_inv_closed_of_natDegree_le_two (hdeg : H.natDegree ≤ 2) (x : 𝕃 H) :
    ∃ c₀ c₁ : RatFunc F,
      x⁻¹ = liftRatFunc H c₀ + functionFieldT (H := H) * liftRatFunc H c₁ :=
  exists_ratfunc_T_repr_of_natDegree_le_two H hdeg x⁻¹

/-! ## FINDING C: sharpness at `d_H ≥ 3`, RatFunc level -/

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- The RatFunc-level injectivity-below-the-modulus engine: representatives of `T`-degree
`< d_H` are unique. -/
theorem eq_of_mk_eq_of_natDegree_lt {p q : Polynomial (RatFunc F)}
    (h : Ideal.Quotient.mk (Ideal.span {H_tilde H}) p
      = Ideal.Quotient.mk (Ideal.span {H_tilde H}) q)
    (hp : p.natDegree < H.natDegree) (hq : q.natDegree < H.natDegree) : p = q := by
  by_contra hne
  have hpos : 0 < H.natDegree := by omega
  have hmem : p - q ∈ Ideal.span {H_tilde H} := Ideal.Quotient.eq.mp h
  have hdvd : H_tilde H ∣ p - q := Ideal.mem_span_singleton.mp hmem
  have hsub_ne : p - q ≠ 0 := sub_ne_zero.mpr hne
  have hle : (H_tilde H).natDegree ≤ (p - q).natDegree :=
    Polynomial.natDegree_le_of_dvd hdvd hsub_ne
  rw [natDegree_H_tilde H hpos] at hle
  have hsub_lt : (p - q).natDegree < H.natDegree :=
    lt_of_le_of_lt (Polynomial.natDegree_sub_le p q) (max_lt hp hq)
  omega

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- For `d_H ≥ 3`, `T²` escapes even the **RatFunc** affine-in-`T` line: relaxing the readings to
`RatFunc F` does not create a recursion-local route at `d_H ≥ 3`. The genuine Claim-5.9 content
there is the global geometric `Z`-degree input — the windowed successor residual. -/
theorem functionFieldT_sq_no_ratfunc_T_repr (hdeg : 3 ≤ H.natDegree) :
    ¬ ∃ c₀ c₁ : RatFunc F, functionFieldT (H := H) ^ 2
        = liftRatFunc H c₀ + functionFieldT (H := H) * liftRatFunc H c₁ := by
  rintro ⟨c₀, c₁, h⟩
  have hlin : (Polynomial.C c₀ + Polynomial.X * Polynomial.C c₁
      : Polynomial (RatFunc F)).natDegree ≤ 1 := by
    refine le_trans (Polynomial.natDegree_add_le _ _) (max_le ?_ ?_)
    · simp
    · refine le_trans Polynomial.natDegree_mul_le ?_
      simp
  have hmk : Ideal.Quotient.mk (Ideal.span {H_tilde H})
        ((Polynomial.X : Polynomial (RatFunc F)) ^ 2)
      = Ideal.Quotient.mk (Ideal.span {H_tilde H})
        (Polynomial.C c₀ + Polynomial.X * Polynomial.C c₁) := by
    rw [map_pow, map_add, map_mul]
    exact h
  have heq := eq_of_mk_eq_of_natDegree_lt H hmk
    (by rw [Polynomial.natDegree_X_pow]; omega)
    (lt_of_le_of_lt hlin (by omega))
  have h2 : (2 : ℕ) ≤ 1 := by
    calc (2 : ℕ) = ((Polynomial.X : Polynomial (RatFunc F)) ^ 2).natDegree :=
          (Polynomial.natDegree_X_pow 2).symm
    _ = (Polynomial.C c₀ + Polynomial.X * Polynomial.C c₁
          : Polynomial (RatFunc F)).natDegree := by rw [heq]
    _ ≤ 1 := hlin
  omega

/-! ## FINDING A: the `d_H = 1` face — `groundEval` and the denominator arithmetic -/

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- At `d_H = 1` the monicized modulus is the explicit linear polynomial
`H̃' = Y + C (H.coeff 0)`. -/
theorem H_tilde'_eq_of_natDegree_eq_one (hdeg1 : H.natDegree = 1) :
    H_tilde' H = Polynomial.X + Polynomial.C (H.coeff 0) := by
  rw [H_tilde', if_neg (by omega)]
  simp [hdeg1]

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- At `d_H = 1`, `H̃ = T + φ(H.coeff 0)` in `F(Z)[T]`. -/
theorem H_tilde_eq_of_natDegree_eq_one (hdeg1 : H.natDegree = 1) :
    H_tilde H = Polynomial.X
      + Polynomial.C (ToRatFunc.univPolyHom (F := F) (H.coeff 0)) := by
  rw [← H_tilde_equiv_H_tilde' H, H_tilde'_eq_of_natDegree_eq_one H hdeg1,
    Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- **The rational branch-point evaluation.** At `d_H = 1` the adjoined root is rational:
`T ≡ −φ(H.coeff 0) mod H̃`. Evaluating representatives there is well-defined on `𝕃 H`, giving a
ring hom `𝕃 H →+* F(Z)` — the tool the `d_H = 1` analysis runs on (the audit's
bivariate-representative engine is unavailable at `d_H = 1`). -/
noncomputable def groundEval (hdeg1 : H.natDegree = 1) : 𝕃 H →+* RatFunc F :=
  Ideal.Quotient.lift (Ideal.span {H_tilde H})
    (Polynomial.evalRingHom (-(ToRatFunc.univPolyHom (F := F) (H.coeff 0))))
    (by
      intro a ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
      rw [map_mul]
      have h0 : Polynomial.evalRingHom
          (-(ToRatFunc.univPolyHom (F := F) (H.coeff 0))) (H_tilde H) = 0 := by
        rw [Polynomial.coe_evalRingHom, H_tilde_eq_of_natDegree_eq_one H hdeg1]
        simp
      rw [h0, zero_mul])

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
@[simp]
theorem groundEval_mk (hdeg1 : H.natDegree = 1) (p : Polynomial (RatFunc F)) :
    groundEval H hdeg1 (Ideal.Quotient.mk (Ideal.span {H_tilde H}) p)
      = Polynomial.eval (-(ToRatFunc.univPolyHom (F := F) (H.coeff 0))) p := by
  rw [groundEval, Ideal.Quotient.lift_mk, Polynomial.coe_evalRingHom]

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- `groundEval` restricted to the ground line is `φ = univPolyHom` (it is a retraction of the
coefficient embedding). -/
theorem groundEval_liftToFunctionField (hdeg1 : H.natDegree = 1) (c : F[X]) :
    groundEval H hdeg1 (liftToFunctionField (H := H) c)
      = ToRatFunc.univPolyHom (F := F) c := by
  rw [show liftToFunctionField (H := H) c
      = Ideal.Quotient.mk (Ideal.span {H_tilde H}) (coeffAsRatFunc c) from rfl,
    groundEval_mk, coeffAsRatFunc_eq_C, Polynomial.eval_C]

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)] in
/-- `groundEval` reads `T` as the rational branch value `−φ(H.coeff 0)`. -/
theorem groundEval_functionFieldT (hdeg1 : H.natDegree = 1) :
    groundEval H hdeg1 (functionFieldT (H := H))
      = -(ToRatFunc.univPolyHom (F := F) (H.coeff 0)) := by
  rw [functionFieldT_eq_mk, groundEval_mk, Polynomial.eval_X]

/-- **FINDING A (forward).** At `d_H = 1`, the order-0 membership `α₀ = T/W ∈ lift(F[X]) +
T·lift(F[X])` forces `IsUnit H.leadingCoeff`. Route: push through `groundEval` to get
`−φb/φa = φc₀ − φb·φc₁` in `F(Z)`; clear the denominator to `b·(a·c₁ − 1) = a·c₀` in `F[X]`;
`IsCoprime a (a·c₁ − 1)` gives `a ∣ b`; primitivity of the irreducible `H = C a·Y + C b` forces
`IsUnit a`. The obstruction is pure denominator arithmetic — no `Z`-degree content. -/
theorem isUnit_leadingCoeff_of_α₀_T_repr_of_natDegree_eq_one (hdeg1 : H.natDegree = 1)
    (h : ∃ c₀ c₁ : F[X], α₀ H
        = liftToFunctionField (H := H) c₀
          + functionFieldT (H := H) * liftToFunctionField (H := H) c₁) :
    IsUnit H.leadingCoeff := by
  obtain ⟨c₀, c₁, h⟩ := h
  have hane : H.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr
      (Polynomial.ne_zero_of_natDegree_gt (Fact.out (p := 0 < H.natDegree)))
  have hφa : ToRatFunc.univPolyHom (F := F) H.leadingCoeff ≠ 0 := fun h0 =>
    hane (univPolyHom_inj (by simpa using h0))
  -- Push the membership through the branch-point evaluation.
  have happ := congrArg (groundEval H hdeg1) h
  rw [α₀] at happ
  simp only [map_div₀, map_add, map_mul, groundEval_functionFieldT H hdeg1,
    groundEval_liftToFunctionField H hdeg1] at happ
  rw [div_eq_iff hφa] at happ
  -- Clear denominators back in `F[X]`.
  have hkey : H.coeff 0 * (H.leadingCoeff * c₁ - 1) = H.leadingCoeff * c₀ := by
    apply univPolyHom_inj
    rw [map_mul, map_sub, map_mul, map_one, map_mul]
    linear_combination happ
  have hcop : IsCoprime H.leadingCoeff (H.leadingCoeff * c₁ - 1) := ⟨c₁, -1, by ring⟩
  have hdvd : H.leadingCoeff ∣ H.coeff 0 :=
    hcop.dvd_of_dvd_mul_right ⟨c₀, hkey⟩
  obtain ⟨e, he⟩ := hdvd
  have hprim : H.IsPrimitive :=
    (Fact.out (p := Irreducible H)).isPrimitive (by omega)
  refine hprim H.leadingCoeff ⟨Polynomial.X + Polynomial.C e, ?_⟩
  have hc1 : H.coeff 1 = H.leadingCoeff := by
    rw [Polynomial.leadingCoeff, hdeg1]
  conv_lhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one hdeg1.le]
  rw [hc1, he, Polynomial.C_mul]
  ring

/-- **FINDING A (iff form).** The `d_H = 1` analogue of the audit's
`α₀_T_repr_iff_isUnit_leadingCoeff` (which required `2 ≤ d_H`): the order-0 face of the in-tree
target holds at `d_H = 1` **iff** the leading coefficient is a unit. -/
theorem α₀_T_repr_iff_isUnit_leadingCoeff_of_natDegree_eq_one (hdeg1 : H.natDegree = 1) :
    (∃ c₀ c₁ : F[X], α₀ H
        = liftToFunctionField (H := H) c₀
          + functionFieldT (H := H) * liftToFunctionField (H := H) c₁)
      ↔ IsUnit H.leadingCoeff := by
  constructor
  · exact isUnit_leadingCoeff_of_α₀_T_repr_of_natDegree_eq_one H hdeg1
  · intro hu
    obtain ⟨u, hu_eq⟩ := hu.exists_right_inv
    have hWne : liftToFunctionField (H := H) H.leadingCoeff ≠ 0 :=
      liftToFunctionField_leadingCoeff_ne_zero (H := H)
    refine ⟨0, u, ?_⟩
    rw [map_zero, zero_add, α₀, div_eq_iff hWne, mul_assoc, ← map_mul,
      show u * H.leadingCoeff = 1 from by rw [mul_comm]; exact hu_eq, map_one, mul_one]

/-- **FINDING A at target level.** If the in-tree Claim 5.9 target holds for a `d_H = 1` curve,
the leading coefficient is a unit (extract the order-0 face, apply the membership analysis). -/
theorem isUnit_leadingCoeff_of_target_of_natDegree_eq_one (hdeg1 : H.natDegree = 1)
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
  exact isUnit_leadingCoeff_of_α₀_T_repr_of_natDegree_eq_one H hdeg1 ⟨c₀, c₁, hα⟩

/-! ## The combined any-degree verdict -/

/-- **The any-degree leading-coefficient necessity.** The in-tree Claim 5.9 target forces
`IsUnit H.leadingCoeff` at **every** degree: `d_H = 1` by FINDING A (denominator arithmetic),
`d_H ≥ 2` by the audit's representative engine. No degree hypothesis. -/
theorem isUnit_leadingCoeff_of_gammaGenuine_Z_linear_target_all
    {x₀ : F} {R : F[X][X][Y]} (hHyp : ClaimA2.Hypotheses x₀ R H)
    (h : gammaGenuine_Z_linear_target H x₀ R hHyp) : IsUnit H.leadingCoeff := by
  have hpos : 0 < H.natDegree := Fact.out (p := 0 < H.natDegree)
  rcases Nat.lt_or_ge H.natDegree 2 with h2 | h2
  · exact isUnit_leadingCoeff_of_target_of_natDegree_eq_one H (by omega) hHyp h
  · exact BCIKS20.ZLinearClosureAudit.isUnit_leadingCoeff_of_gammaGenuine_Z_linear_target
      H h2 hHyp h

/-- **The any-degree refutation.** For every curve `H` (any `d_H ≥ 1`) with non-unit leading
coefficient, the in-tree Claim 5.9 target is FALSE — completing the audit's `d_H ≥ 2` refutation
down to `d_H = 1`. Do not attack `gammaGenuine_Z_linear_target` as stated outside the
unit-leading-coefficient class, at any degree. -/
theorem not_gammaGenuine_Z_linear_target_of_not_isUnit_leadingCoeff_all
    (hlc : ¬ IsUnit H.leadingCoeff) {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H) :
    ¬ gammaGenuine_Z_linear_target H x₀ R hHyp :=
  fun h => hlc (isUnit_leadingCoeff_of_gammaGenuine_Z_linear_target_all H hHyp h)

/-- **The low-degree integrality dichotomy (capstone).** For `d_H ≤ 2`: the RatFunc-coefficient
reading of Claim 5.9 is unconditionally TRUE, while the in-tree `F[X]`-coefficient reading
forces a unit leading coefficient. The entire content of the in-tree target at `d_H ≤ 2` is
integrality of the readings; the `Z`-linearity content of Claim 5.9 lives only at `d_H ≥ 3`
(where, by `functionFieldT_sq_no_ratfunc_T_repr`, neither reading has a recursion-local route —
the windowed successor residual stands). -/
theorem claim59_low_degree_integrality_dichotomy (hdeg : H.natDegree ≤ 2)
    {x₀ : F} {R : F[X][X][Y]} (hHyp : ClaimA2.Hypotheses x₀ R H) :
    gammaGenuine_Z_linear_target_ratfunc H x₀ R hHyp ∧
      (gammaGenuine_Z_linear_target H x₀ R hHyp → IsUnit H.leadingCoeff) :=
  ⟨gammaGenuine_Z_linear_target_ratfunc_of_natDegree_le_two H hdeg hHyp,
    fun h => isUnit_leadingCoeff_of_gammaGenuine_Z_linear_target_all H hHyp h⟩

/-! ## Non-vacuity: the witness curve `Z·Y + 1` (`d_H = 1`, non-unit leading coefficient) -/

variable (F) in
/-- The witness curve `H = Z·Y + 1` (in-tree spelling `C(X)·Y + C(1) : F[X][Y]`): irreducible,
`d_H = 1`, leading coefficient `Z` non-unit — inhabiting the `d_H = 1` obstruction class of
FINDING A. -/
noncomputable def witnessCurve : F[X][Y] :=
  Polynomial.C Polynomial.X * Polynomial.X + Polynomial.C 1

omit [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

theorem witnessCurve_natDegree : (witnessCurve F).natDegree = 1 :=
  Polynomial.natDegree_linear Polynomial.X_ne_zero

theorem witnessCurve_leadingCoeff : (witnessCurve F).leadingCoeff = Polynomial.X :=
  Polynomial.leadingCoeff_linear Polynomial.X_ne_zero

theorem not_isUnit_witnessCurve_leadingCoeff : ¬ IsUnit (witnessCurve F).leadingCoeff := by
  rw [witnessCurve_leadingCoeff]
  exact Polynomial.not_isUnit_X

theorem witnessCurve_coeff_zero : (witnessCurve F).coeff 0 = 1 := by
  rw [witnessCurve, Polynomial.coeff_add, Polynomial.mul_coeff_zero]
  simp

/-- The witness curve is irreducible: it is nonconstant of `Y`-degree `1`, and any degree-0
factor divides the constant coefficient `1`, hence is a unit. -/
theorem witnessCurve_irreducible : Irreducible (witnessCurve F) := by
  constructor
  · intro hu
    have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [witnessCurve_natDegree] at h0
    exact one_ne_zero h0
  · intro u v huv
    have hc0 : u.coeff 0 * v.coeff 0 = 1 := by
      have hco := congrArg (fun p : F[X][Y] => p.coeff 0) huv
      simpa [Polynomial.mul_coeff_zero, witnessCurve_coeff_zero] using hco.symm
    have hne : witnessCurve F ≠ 0 :=
      Polynomial.ne_zero_of_natDegree_gt (n := 0) (by rw [witnessCurve_natDegree]; omega)
    have hu0 : u ≠ 0 := fun h => hne (by rw [huv, h, zero_mul])
    have hv0 : v ≠ 0 := fun h => hne (by rw [huv, h, mul_zero])
    have hdeg : u.natDegree + v.natDegree = 1 := by
      have hmul := Polynomial.natDegree_mul hu0 hv0
      rw [← huv, witnessCurve_natDegree] at hmul
      omega
    rcases Nat.eq_zero_or_pos u.natDegree with hu1 | hu1
    · left
      rw [Polynomial.eq_C_of_natDegree_eq_zero hu1]
      exact Polynomial.isUnit_C.mpr (IsUnit.of_mul_eq_one _ hc0)
    · right
      have hv1 : v.natDegree = 0 := by omega
      rw [Polynomial.eq_C_of_natDegree_eq_zero hv1]
      exact Polynomial.isUnit_C.mpr (IsUnit.of_mul_eq_one _ (by rwa [mul_comm] at hc0))

instance : Fact (Irreducible (witnessCurve F)) := ⟨witnessCurve_irreducible⟩

instance : Fact (0 < (witnessCurve F).natDegree) := ⟨by rw [witnessCurve_natDegree]; omega⟩

/-- **Non-vacuity of FINDING A.** For the witness curve `Z·Y + 1` the order-0 face of the
in-tree Claim 5.9 target FAILS outright: `α₀ = T/Z` admits no `F[X]`-affine-in-`T`
representation. The `d_H = 1` obstruction is realized by a concrete irreducible curve — the
refutation `not_gammaGenuine_Z_linear_target_of_not_isUnit_leadingCoeff_all` is not vacuous at
`d_H = 1`. -/
theorem α₀_no_T_repr_witnessCurve :
    ¬ ∃ c₀ c₁ : F[X], α₀ (witnessCurve F)
        = liftToFunctionField (H := witnessCurve F) c₀
          + functionFieldT (H := witnessCurve F)
            * liftToFunctionField (H := witnessCurve F) c₁ :=
  fun h => not_isUnit_witnessCurve_leadingCoeff
    (isUnit_leadingCoeff_of_α₀_T_repr_of_natDegree_eq_one (witnessCurve F)
      witnessCurve_natDegree h)

end BCIKS20.ZLinearRatFuncDegreeOne

end

section AxiomAudit

#print axioms BCIKS20.ZLinearRatFuncDegreeOne.univPolyHom_inj
#print axioms BCIKS20.ZLinearRatFuncDegreeOne.liftRatFunc
#print axioms BCIKS20.ZLinearRatFuncDegreeOne.liftRatFunc_apply
#print axioms BCIKS20.ZLinearRatFuncDegreeOne.functionFieldT_eq_mk
#print axioms BCIKS20.ZLinearRatFuncDegreeOne.liftToFunctionField_eq_liftRatFunc
#print axioms BCIKS20.ZLinearRatFuncDegreeOne.gammaGenuine_Z_linear_target_ratfunc
#print axioms BCIKS20.ZLinearRatFuncDegreeOne.target_ratfunc_of_target
#print axioms BCIKS20.ZLinearRatFuncDegreeOne.target_ratfunc_of_coeffs
#print axioms BCIKS20.ZLinearRatFuncDegreeOne.coeffs_of_target_ratfunc
#print axioms BCIKS20.ZLinearRatFuncDegreeOne.H_tilde_monic
#print axioms BCIKS20.ZLinearRatFuncDegreeOne.natDegree_H_tilde
#print axioms BCIKS20.ZLinearRatFuncDegreeOne.exists_ratfunc_T_repr_of_natDegree_le_two
#print axioms BCIKS20.ZLinearRatFuncDegreeOne.gammaGenuine_Z_linear_target_ratfunc_of_natDegree_le_two
#print axioms BCIKS20.ZLinearRatFuncDegreeOne.ratfunc_T_repr_mul_closed_of_natDegree_le_two
#print axioms BCIKS20.ZLinearRatFuncDegreeOne.ratfunc_T_repr_inv_closed_of_natDegree_le_two
#print axioms BCIKS20.ZLinearRatFuncDegreeOne.eq_of_mk_eq_of_natDegree_lt
#print axioms BCIKS20.ZLinearRatFuncDegreeOne.functionFieldT_sq_no_ratfunc_T_repr
#print axioms BCIKS20.ZLinearRatFuncDegreeOne.H_tilde'_eq_of_natDegree_eq_one
#print axioms BCIKS20.ZLinearRatFuncDegreeOne.H_tilde_eq_of_natDegree_eq_one
#print axioms BCIKS20.ZLinearRatFuncDegreeOne.groundEval
#print axioms BCIKS20.ZLinearRatFuncDegreeOne.groundEval_mk
#print axioms BCIKS20.ZLinearRatFuncDegreeOne.groundEval_liftToFunctionField
#print axioms BCIKS20.ZLinearRatFuncDegreeOne.groundEval_functionFieldT
#print axioms BCIKS20.ZLinearRatFuncDegreeOne.isUnit_leadingCoeff_of_α₀_T_repr_of_natDegree_eq_one
#print axioms BCIKS20.ZLinearRatFuncDegreeOne.α₀_T_repr_iff_isUnit_leadingCoeff_of_natDegree_eq_one
#print axioms BCIKS20.ZLinearRatFuncDegreeOne.isUnit_leadingCoeff_of_target_of_natDegree_eq_one
#print axioms BCIKS20.ZLinearRatFuncDegreeOne.isUnit_leadingCoeff_of_gammaGenuine_Z_linear_target_all
#print axioms BCIKS20.ZLinearRatFuncDegreeOne.not_gammaGenuine_Z_linear_target_of_not_isUnit_leadingCoeff_all
#print axioms BCIKS20.ZLinearRatFuncDegreeOne.claim59_low_degree_integrality_dichotomy
#print axioms BCIKS20.ZLinearRatFuncDegreeOne.witnessCurve
#print axioms BCIKS20.ZLinearRatFuncDegreeOne.witnessCurve_natDegree
#print axioms BCIKS20.ZLinearRatFuncDegreeOne.witnessCurve_leadingCoeff
#print axioms BCIKS20.ZLinearRatFuncDegreeOne.not_isUnit_witnessCurve_leadingCoeff
#print axioms BCIKS20.ZLinearRatFuncDegreeOne.witnessCurve_coeff_zero
#print axioms BCIKS20.ZLinearRatFuncDegreeOne.witnessCurve_irreducible
#print axioms BCIKS20.ZLinearRatFuncDegreeOne.α₀_no_T_repr_witnessCurve

end AxiomAudit
