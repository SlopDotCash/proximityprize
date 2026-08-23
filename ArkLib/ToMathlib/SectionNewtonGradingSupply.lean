/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.PolyRootGradedBound
import Mathlib.RingTheory.Polynomial.IntegralNormalization

/-!
# The grading supply for the Claim-5.8 engine: monicization transport (#304)

The engine `ArkLib.PolyRootGradedBound.exists_graded_preimage_of_eval_monic_eq_zero` consumes a
**monic** `T`-polynomial `P` over `B[X][Y]` carrying the balanced slope-`s` grading
`deg ((P.coeff c).coeff j) ≤ s·(P.natDegree − c)`.  The in-tree GS producers do **not** emit
this pair:

* `gs_existence_zDegree_curve` (curve fold, arity `L`) emits the **flat** budget
  `∀ b a, deg_Z ((Q₀.coeff b).coeff a) ≤ DZ`;
* `gs_existence_sloped` (pair fold) emits the **sloped** budget
  `∀ b a, deg_Z ((Q₀.coeff b).coeff a) ≤ W − b` (`W = slopedBudget`, slope `1`);

and neither interpolant is monic in `Y` — its `Y`-leading coefficient is an arbitrary kernel
element of `F[Z][X]`.

This file closes the *monicity* half of that gap and quantifies the slope cost exactly, via
Mathlib's `Polynomial.integralNormalization` (`P̃.coeff c = P.coeff c · ℓ^(d−1−c)`, `ℓ` the
leading coefficient, `d = P.natDegree`):

* `coeff_natDegree_mul_le` / `coeff_natDegree_pow_le` — per-inner-coefficient degree
  arithmetic in `R[X][Y]`;
* `integralNormalization_coeff_coeff_natDegree_le` — **the grading transport**: if `P` carries
  the sloped budget `deg ((P.coeff c).coeff j) ≤ W − s·c` (all `c`, including the top, so
  `deg_Z ℓ ≤ E := W − s·d`), then `integralNormalization P` carries the *balanced* grading at
  slope `s + E`:  `deg ≤ (W − s·c) + (d−1−c)·E ≤ (s+E)·(d−c)`.  At zero excess (`W = s·d`)
  the slope is preserved exactly — the leading coefficient is then forced inner-degree-free.
* `exists_graded_preimage_of_eval_sloped_eq_zero` — **the monicity-free engine**: a polynomial
  root `γ` over `Frac (B[X])` of a *non-monic* sloped `P` yields an integral representative of
  the twisted root `ℓ·γ` with all inner degrees `≤ s + (W − s·d)` (root transport
  `γ ↦ ℓ·γ` by `integralNormalization_eval₂_eq_zero`, then the monic engine).
* `exists_graded_preimage_of_eval_flat_eq_zero` — the `s = 0` instance consuming the flat
  curve budget verbatim (bound `W`).

What this file does **not** (and cannot cheaply) supply: the zero-excess balanced grading
`W = s·d` at slope `s` = curve degree for the relevant GS factor.  That needs the two-sided
multiplicativity of the `(1,0,s)`-weighted degree over a domain (only the `≤` half exists
in-tree, `ArkLib.BivariateDegreeToolkit.natWeightedDegree_mul_le`) together with a
monic-factor splitting argument — see the recon notes on #304.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5 (Claim 5.8), Appendix A.2/A.4.
-/

set_option linter.style.longLine false

open Polynomial Polynomial.Bivariate

namespace ArkLib

namespace SectionNewtonGradingSupply

/-! ## Per-inner-coefficient degree arithmetic -/

/-- Inner-coefficient degree bound for a product in `R[X][Y]`: if every inner coefficient of
`U` has degree `≤ u` and of `V` degree `≤ v`, then every inner coefficient of `U * V` has
degree `≤ u + v`. -/
theorem coeff_natDegree_mul_le {R : Type*} [Semiring R] {U V : R[X][Y]} {u v : ℕ}
    (hU : ∀ j, (U.coeff j).natDegree ≤ u) (hV : ∀ j, (V.coeff j).natDegree ≤ v) (j : ℕ) :
    ((U * V).coeff j).natDegree ≤ u + v := by
  rw [Polynomial.coeff_mul]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun x _ => ?_
  exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hU x.1) (hV x.2))

/-- Inner-coefficient degree bound for a power in `R[X][Y]`. -/
theorem coeff_natDegree_pow_le {R : Type*} [Semiring R] {U : R[X][Y]} {u : ℕ}
    (hU : ∀ j, (U.coeff j).natDegree ≤ u) (e : ℕ) (j : ℕ) :
    ((U ^ e).coeff j).natDegree ≤ e * u := by
  induction e generalizing j with
  | zero =>
      rw [pow_zero, Nat.zero_mul]
      rcases eq_or_ne j 0 with rfl | hj
      · simp
      · simp [Polynomial.coeff_one, hj]
  | succ e ih =>
      rw [pow_succ]
      calc ((U ^ e * U).coeff j).natDegree
          ≤ e * u + u := coeff_natDegree_mul_le ih hU j
        _ = (e + 1) * u := by rw [Nat.succ_mul]

/-! ## The grading transport under `integralNormalization` -/

/-- **The grading transport.**  If every double coefficient of `P : (B[X][Y])[T]` obeys the
sloped budget `deg ((P.coeff c).coeff j) ≤ W − s·c` (including the top coefficient, so the
leading coefficient has inner degree `≤ E := W − s·P.natDegree`), then `integralNormalization P`
carries the engine's balanced grading at slope `s + E`:

`deg (((integralNormalization P).coeff c).coeff j) ≤ (s + E) * (P.natDegree − c)` for
`c < P.natDegree`.  At zero excess (`W = s·P.natDegree`) the slope is preserved exactly. -/
theorem integralNormalization_coeff_coeff_natDegree_le {B : Type*} [Semiring B]
    {P : Polynomial (B[X][Y])} {s W : ℕ}
    (hsl : ∀ c j, ((P.coeff c).coeff j).natDegree ≤ W - s * c) :
    ∀ c < P.natDegree, ∀ j,
      ((P.integralNormalization.coeff c).coeff j).natDegree
        ≤ (s + (W - s * P.natDegree)) * (P.natDegree - c) := by
  intro c hc j
  rw [Polynomial.integralNormalization_coeff_ne_natDegree (Nat.ne_of_lt hc)]
  have hℓdef : P.leadingCoeff = P.coeff P.natDegree := rfl
  have hℓ : ∀ j, (P.leadingCoeff.coeff j).natDegree ≤ W - s * P.natDegree := by
    intro j
    rw [hℓdef]
    exact hsl P.natDegree j
  have h1 := coeff_natDegree_mul_le (fun j => hsl c j)
    (coeff_natDegree_pow_le hℓ (P.natDegree - 1 - c)) j
  refine h1.trans ?_
  have hCA : s * (P.natDegree - c) + s * c = s * P.natDegree := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hc.le]
  have he2 : (P.natDegree - c) * (W - s * P.natDegree)
      = (P.natDegree - 1 - c) * (W - s * P.natDegree) + (W - s * P.natDegree) := by
    have hdc : P.natDegree - c = P.natDegree - 1 - c + 1 := by omega
    rw [hdc, Nat.succ_mul]
  have hgoal : (s + (W - s * P.natDegree)) * (P.natDegree - c)
      = s * (P.natDegree - c) + (P.natDegree - c) * (W - s * P.natDegree) := by
    rw [Nat.add_mul, Nat.mul_comm (W - s * P.natDegree) (P.natDegree - c)]
  omega

/-! ## The monicity-free engine -/

/-- **The monicity-free Claim-5.8 engine.**  Let `B` be an integrally closed domain, `S` the
fraction field of `B[X]`, and `P : (B[X][Y])[T]` a *not necessarily monic* polynomial of
positive degree carrying the sloped budget `deg ((P.coeff c).coeff j) ≤ W − s·c`.  Then any
polynomial root `γ ∈ S[X]` of `P` yields, after twisting by the leading coefficient `ℓ`, an
integral representative `g` of `ℓ·γ` whose every inner coefficient has degree at most
`s + (W − s·P.natDegree)` — at zero excess, exactly the engine bound `s`.

This removes the `Monic` requirement from the engine interface (the documented honest
residual of the §5 GS-factor route) at the precise cost of the `ℓ`-twist and the excess
`E = W − s·d` in the slope. -/
theorem exists_graded_preimage_of_eval_sloped_eq_zero {B S : Type*} [CommRing B] [IsDomain B]
    [IsIntegrallyClosed B] [CommRing S] [Algebra (Polynomial B) S]
    [IsFractionRing (Polynomial B) S]
    {γ : Polynomial S} {P : Polynomial (B[X][Y])} {s W : ℕ}
    (hP : P ≠ 0) (hd : P.natDegree ≠ 0)
    (hsl : ∀ c j, ((P.coeff c).coeff j).natDegree ≤ W - s * c)
    (hroot : Polynomial.eval γ
      (P.map (Polynomial.mapRingHom (algebraMap (Polynomial B) S))) = 0) :
    ∃ g : B[X][Y],
      g.map (algebraMap (Polynomial B) S)
        = P.leadingCoeff.map (algebraMap (Polynomial B) S) * γ ∧
      ∀ j, (g.coeff j).natDegree ≤ s + (W - s * P.natDegree) := by
  classical
  have hinj : Function.Injective
      (Polynomial.map (algebraMap (Polynomial B) S) : B[X][Y] → Polynomial S) :=
    Polynomial.map_injective _ (IsFractionRing.injective _ _)
  -- the root equation in `eval₂` form
  have hz : Polynomial.eval₂ (Polynomial.mapRingHom (algebraMap (Polynomial B) S)) γ P = 0 := by
    rwa [← Polynomial.eval_map]
  -- root transport along the monicization: `ℓ·γ` is a root of `integralNormalization P`
  have hz' := Polynomial.integralNormalization_eval₂_eq_zero
    (Polynomial.mapRingHom (algebraMap (Polynomial B) S)) hz
    (fun x hx => hinj (by simpa using hx))
  have hroot' : Polynomial.eval
      ((Polynomial.mapRingHom (algebraMap (Polynomial B) S)) P.leadingCoeff * γ)
      (P.integralNormalization.map
        (Polynomial.mapRingHom (algebraMap (Polynomial B) S))) = 0 := by
    rwa [Polynomial.eval_map]
  -- the balanced grading of the monicization, at slope `s + (W − s·d)`
  have hgrade : ∀ c < P.integralNormalization.natDegree, ∀ j,
      ((P.integralNormalization.coeff c).coeff j).natDegree
        ≤ (s + (W - s * P.natDegree)) * (P.integralNormalization.natDegree - c) := by
    rw [Polynomial.natDegree_integralNormalization]
    exact integralNormalization_coeff_coeff_natDegree_le hsl
  obtain ⟨g, hg, hgdeg⟩ :=
    ArkLib.PolyRootGradedBound.exists_graded_preimage_of_eval_monic_eq_zero
      (Polynomial.monic_integralNormalization hP)
      (by rwa [Polynomial.natDegree_integralNormalization]) hgrade hroot'
  exact ⟨g, by rw [hg]; rfl, hgdeg⟩

/-- **The flat instance** (`s = 0`): the curve producer's flat budget
`deg ((P.coeff c).coeff j) ≤ W` yields an integral representative of `ℓ·γ` with inner degrees
`≤ W` — the glue for `gs_existence_zDegree_curve`-shaped inputs. -/
theorem exists_graded_preimage_of_eval_flat_eq_zero {B S : Type*} [CommRing B] [IsDomain B]
    [IsIntegrallyClosed B] [CommRing S] [Algebra (Polynomial B) S]
    [IsFractionRing (Polynomial B) S]
    {γ : Polynomial S} {P : Polynomial (B[X][Y])} {W : ℕ}
    (hP : P ≠ 0) (hd : P.natDegree ≠ 0)
    (hfl : ∀ c j, ((P.coeff c).coeff j).natDegree ≤ W)
    (hroot : Polynomial.eval γ
      (P.map (Polynomial.mapRingHom (algebraMap (Polynomial B) S))) = 0) :
    ∃ g : B[X][Y],
      g.map (algebraMap (Polynomial B) S)
        = P.leadingCoeff.map (algebraMap (Polynomial B) S) * γ ∧
      ∀ j, (g.coeff j).natDegree ≤ W := by
  obtain ⟨g, hg, hgdeg⟩ := exists_graded_preimage_of_eval_sloped_eq_zero (s := 0) (W := W)
    hP hd (fun c j => by simpa using hfl c j) hroot
  exact ⟨g, hg, fun j => by simpa using hgdeg j⟩

end SectionNewtonGradingSupply

end ArkLib

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.SectionNewtonGradingSupply.coeff_natDegree_mul_le
#print axioms ArkLib.SectionNewtonGradingSupply.coeff_natDegree_pow_le
#print axioms ArkLib.SectionNewtonGradingSupply.integralNormalization_coeff_coeff_natDegree_le
#print axioms ArkLib.SectionNewtonGradingSupply.exists_graded_preimage_of_eval_sloped_eq_zero
#print axioms ArkLib.SectionNewtonGradingSupply.exists_graded_preimage_of_eval_flat_eq_zero
