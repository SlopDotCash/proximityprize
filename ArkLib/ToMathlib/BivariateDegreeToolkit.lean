/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliza
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import ArkLib.Data.Polynomial.Bivariate
import ArkLib.Data.Polynomial.Trivariate

/-!
# A reusable weighted/total-degree arithmetic toolkit for bivariate/trivariate polynomials

This file collects **new** arithmetic helper lemmas about the bivariate degree functions
`Polynomial.Bivariate.natWeightedDegree`, `.totalDegree`, `.degreeX`, `.natDegreeY` (provided
by `CompPoly.ToMathlib.Polynomial.{BivariateDegree, BivariateWeightedDegree}`) and the
trivariate `Z`-specialization `Trivariate.eval_on_Z` (from `ArkLib.Data.Polynomial.Trivariate`).

They are of exactly the shape the BCIKS20 §5 list-decoding chain and its ingredient-C counting
need: additive/multiplicative degree bounds, weight-monotonicity, the three coordinate degrees
as instances of one weighted bound, "degree does not increase under `Z ↦ z` specialization"
facts, algebraic-homomorphism corollaries of `eval_on_Z`, and root-count-versus-degree helpers.

## Relation to the in-tree surface (no duplication)

The upstream files already prove:

* `natWeightedDegree_add_le`, `natWeightedDegree_sum_le`, `natWeightedDegree_smul_le`,
  `natWeightedDegree_monomial`, `degree_eval_le_weightedDegree`
  (in `CompPoly.ToMathlib.Polynomial.BivariateWeightedDegree`);
* `totalDegree_mul_le`, `totalDegree_mul`, `degreeX_mul_le`, `degreeX_mul`, `degreeY_mul`,
  `coeff_natDegree_le_degreeX`, `coeff_totalDegree_le`,
  `total_deg_as_weighted_deg`, `degreeX_as_weighted_deg`, `degreeY_as_weighted_deg`,
  `card_evalX_eq_zero_le_degreeX`
  (in `CompPoly.ToMathlib.Polynomial.BivariateDegree` and `ArkLib.Data.Polynomial.Bivariate`);
* `Trivariate.eval_on_Z_eq` and (in
  `ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.Agreement`)
  `c57_eval_on_Z_zero`, `c57_eval_on_Z_add`, `c57_eval_on_Z_mul`.

This file does **not** restate any of those.  The product/weighted bound
`natWeightedDegree_mul_le` is the genuinely missing general statement — the in-tree
`totalDegree_mul_le` and `degreeX_mul_le` are only its `(u,v) = (1,1)` and `(1,0)` instances.
The `eval_on_Z` results here are *corollaries* (`_one`, `_pow`, `_sum`, divisibility transport,
degree non-increase) built on the existing additive/multiplicative equations, not copies of them.

## References

- [BCIKS20] Eli Ben-Sasson, Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.
  Proximity gaps for Reed-Solomon codes. FOCS 2020, https://eprint.iacr.org/2020/654.
-/

open Polynomial Polynomial.Bivariate

namespace ArkLib

namespace BivariateDegreeToolkit

noncomputable section

variable {F : Type*}

/-! ## Section 1 — weighted-degree arithmetic over a semiring

The single elementwise estimate `weight_coeff_le_natWeightedDegree` underlies every bound:
each monomial `X^i Y^j` actually present in `f` contributes weight `≤ natWeightedDegree f u v`.
-/

section Semiring

variable [Semiring F]

/-- `natWeightedDegree` of the zero polynomial is `0`. -/
@[simp]
lemma natWeightedDegree_zero (u v : ℕ) :
    natWeightedDegree (0 : F[X][Y]) u v = 0 := by
  simp [natWeightedDegree]

/-- The elementwise weighted estimate: any `Y`-index `n` in the support of `f` contributes
weight `u * deg_X(coeff) + v * n` at most the weighted degree.  This is the basic building
block for all the additive/multiplicative bounds below. -/
theorem weight_coeff_le_natWeightedDegree (f : F[X][Y]) (u v : ℕ) {n : ℕ}
    (hn : n ∈ f.support) :
    u * (f.coeff n).natDegree + v * n ≤ natWeightedDegree f u v :=
  Finset.le_sup (f := fun m => u * (f.coeff m).natDegree + v * m) hn

/-- The weighted degree is monotone in both weights. -/
theorem natWeightedDegree_mono_weights (f : F[X][Y]) {u u' v v' : ℕ}
    (hu : u ≤ u') (hv : v ≤ v') :
    natWeightedDegree f u v ≤ natWeightedDegree f u' v' := by
  classical
  refine Finset.sup_le fun m hm => ?_
  refine le_trans ?_ (Finset.le_sup (f := fun m => u' * (f.coeff m).natDegree + v' * m) hm)
  exact Nat.add_le_add (Nat.mul_le_mul_right _ hu) (Nat.mul_le_mul_right _ hv)

/-- **Weighted-degree product bound.**  For *any* weight pair `(u, v)`,
`natWeightedDegree (f * g) u v ≤ natWeightedDegree f u v + natWeightedDegree g u v`.

This is the general statement the BCIKS20 §5 chain and ingredient-C counting need; the in-tree
`totalDegree_mul_le` and `degreeX_mul_le` are exactly its `(u,v) = (1,1)` and `(1,0)` cases.
Holds over an arbitrary semiform (no `IsDomain` needed for the upper bound). -/
theorem natWeightedDegree_mul_le (f g : F[X][Y]) (u v : ℕ) :
    natWeightedDegree (f * g) u v ≤ natWeightedDegree f u v + natWeightedDegree g u v := by
  classical
  set D := natWeightedDegree f u v + natWeightedDegree g u v with hD
  unfold natWeightedDegree
  refine Finset.sup_le ?_
  intro k hk
  rw [Polynomial.coeff_mul]
  -- The `v * k` part is bounded using *some* nonzero antidiagonal factorisation of the
  -- `k`-th product coefficient.
  have hk_le : v * k ≤ D := by
    have hcoeff_ne : (f * g).coeff k ≠ 0 := by
      have := Polynomial.mem_support_iff.mp hk
      simpa [Polynomial.coeff_mul] using this
    rw [Polynomial.coeff_mul] at hcoeff_ne
    obtain ⟨⟨i, j⟩, hij_mem, hij_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hcoeff_ne
    have hij : i + j = k := Finset.mem_antidiagonal.mp hij_mem
    have hfi : f.coeff i ≠ 0 := left_ne_zero_of_mul hij_ne
    have hgj : g.coeff j ≠ 0 := right_ne_zero_of_mul hij_ne
    have hi_le := weight_coeff_le_natWeightedDegree f u v (Polynomial.mem_support_iff.mpr hfi)
    have hj_le := weight_coeff_le_natWeightedDegree g u v (Polynomial.mem_support_iff.mpr hgj)
    have h1 : v * i ≤ natWeightedDegree f u v := le_trans (Nat.le_add_left _ _) hi_le
    have h2 : v * j ≤ natWeightedDegree g u v := le_trans (Nat.le_add_left _ _) hj_le
    have hsum : v * i + v * j ≤ D := Nat.add_le_add h1 h2
    have hexp : v * k = v * i + v * j := by rw [← hij]; ring
    omega
  -- Each antidiagonal term satisfies the full weighted bound.
  have hterm : ∀ x ∈ Finset.antidiagonal k,
      u * (f.coeff x.1 * g.coeff x.2).natDegree + v * k ≤ D := by
    intro x hx
    have hij : x.1 + x.2 = k := Finset.mem_antidiagonal.mp hx
    by_cases hfx : f.coeff x.1 = 0
    · simp only [hfx, zero_mul, Polynomial.natDegree_zero, Nat.mul_zero, Nat.zero_add]
      exact hk_le
    · by_cases hgx : g.coeff x.2 = 0
      · simp only [hgx, mul_zero, Polynomial.natDegree_zero, Nat.zero_add]
        exact hk_le
      · have hf_le := weight_coeff_le_natWeightedDegree f u v (Polynomial.mem_support_iff.mpr hfx)
        have hg_le := weight_coeff_le_natWeightedDegree g u v (Polynomial.mem_support_iff.mpr hgx)
        have hmul_le := Polynomial.natDegree_mul_le (p := f.coeff x.1) (q := g.coeff x.2)
        have hu_le : u * (f.coeff x.1 * g.coeff x.2).natDegree ≤
            u * (f.coeff x.1).natDegree + u * (g.coeff x.2).natDegree :=
          le_trans (Nat.mul_le_mul_left u hmul_le) (by ring_nf; exact le_refl _)
        have hvk : v * k = v * x.1 + v * x.2 := by rw [← hij]; ring
        omega
  -- Bound the natDegree of the antidiagonal sum by its maximal term.
  obtain ⟨x₀, hx₀mem, hx₀deg⟩ := Finset.exists_mem_eq_sup (Finset.antidiagonal k)
      ⟨(0, k), by simp⟩ (fun x => (f.coeff x.1 * g.coeff x.2).natDegree)
  have hnd_le : (∑ x ∈ Finset.antidiagonal k, f.coeff x.1 * g.coeff x.2).natDegree ≤
      (f.coeff x₀.1 * g.coeff x₀.2).natDegree := by
    rw [← hx₀deg]
    exact Polynomial.natDegree_sum_le_of_forall_le _ _
      (fun x hx => Finset.le_sup (f := fun x => (f.coeff x.1 * g.coeff x.2).natDegree) hx)
  calc u * (∑ x ∈ Finset.antidiagonal k, f.coeff x.1 * g.coeff x.2).natDegree + v * k
      ≤ u * (f.coeff x₀.1 * g.coeff x₀.2).natDegree + v * k :=
        Nat.add_le_add_right (Nat.mul_le_mul_left u hnd_le) (v * k)
    _ ≤ D := hterm x₀ hx₀mem

/-- The weighted degree of `1` is `0`. -/
@[simp]
lemma natWeightedDegree_one_le (u v : ℕ) :
    natWeightedDegree (1 : F[X][Y]) u v ≤ 0 := by
  classical
  refine Finset.sup_le fun m hm => ?_
  have hm0 : m = 0 := by
    by_contra hm0
    exact (Polynomial.mem_support_iff.mp hm) (by rw [Polynomial.coeff_one]; simp [hm0])
  subst hm0
  simp [Polynomial.coeff_one]

/-- **Weighted-degree power bound** (corollary of `natWeightedDegree_mul_le`):
`natWeightedDegree (f ^ n) u v ≤ n * natWeightedDegree f u v`. -/
theorem natWeightedDegree_pow_le (f : F[X][Y]) (u v n : ℕ) :
    natWeightedDegree (f ^ n) u v ≤ n * natWeightedDegree f u v := by
  induction n with
  | zero => simpa using natWeightedDegree_one_le (F := F) u v
  | succ k ih =>
      rw [pow_succ]
      calc natWeightedDegree (f ^ k * f) u v
          ≤ natWeightedDegree (f ^ k) u v + natWeightedDegree f u v :=
            natWeightedDegree_mul_le _ _ u v
        _ ≤ k * natWeightedDegree f u v + natWeightedDegree f u v :=
            Nat.add_le_add_right ih _
        _ = (k + 1) * natWeightedDegree f u v := by ring

/-! ## Section 2 — relating the weighted degree to the coordinate degrees

These tie `natWeightedDegree` to `degreeX`, `natDegreeY`, and `totalDegree`.  They make the
weighted machinery above usable for the concrete coordinate-degree fields of `ModifiedGuruswami`.
-/

/-- The `(u, 0)`-weighted degree is bounded by `u * degreeX`. -/
theorem natWeightedDegree_v_zero_le (f : F[X][Y]) (u : ℕ) :
    natWeightedDegree f u 0 ≤ u * degreeX f := by
  classical
  refine Finset.sup_le fun m _ => ?_
  simp only [Nat.zero_mul, Nat.add_zero]
  exact Nat.mul_le_mul_left u (coeff_natDegree_le_degreeX f m)

/-- The `(0, v)`-weighted degree is bounded by `v * natDegreeY`. -/
theorem natWeightedDegree_u_zero_le (f : F[X][Y]) (v : ℕ) :
    natWeightedDegree f 0 v ≤ v * natDegreeY f := by
  classical
  refine Finset.sup_le fun m hm => ?_
  simp only [Nat.zero_mul, Nat.zero_add]
  exact Nat.mul_le_mul_left v (Polynomial.le_natDegree_of_mem_supp m hm)

/-- The total degree is bounded by the sum of the two coordinate degrees. -/
theorem totalDegree_le_degreeX_add_natDegreeY (f : F[X][Y]) :
    totalDegree f ≤ degreeX f + natDegreeY f := by
  classical
  refine Finset.sup_le fun m hm => ?_
  exact Nat.add_le_add (coeff_natDegree_le_degreeX f m)
    (Polynomial.le_natDegree_of_mem_supp m hm)

/-- `degreeX f ≤ totalDegree f`. -/
theorem degreeX_le_totalDegree (f : F[X][Y]) : degreeX f ≤ totalDegree f := by
  classical
  exact Finset.sup_mono_fun (fun m _ => Nat.le_add_right _ _)

/-- `natDegreeY f ≤ totalDegree f`. -/
theorem natDegreeY_le_totalDegree (f : F[X][Y]) : natDegreeY f ≤ totalDegree f := by
  classical
  rw [degreeY_as_weighted_deg, total_deg_as_weighted_deg]
  exact natWeightedDegree_mono_weights f (Nat.zero_le 1) (le_refl 1)

/-- A single combined bound: `natWeightedDegree f u v ≤ max u v * totalDegree f`. -/
theorem natWeightedDegree_le_max_mul_totalDegree (f : F[X][Y]) (u v : ℕ) :
    natWeightedDegree f u v ≤ max u v * totalDegree f := by
  classical
  unfold natWeightedDegree totalDegree
  refine Finset.sup_le fun m hm => ?_
  refine le_trans ?_ (Nat.mul_le_mul_left (max u v)
    (Finset.le_sup (f := fun m => (f.coeff m).natDegree + m) hm))
  calc u * (f.coeff m).natDegree + v * m
      ≤ max u v * (f.coeff m).natDegree + max u v * m :=
        Nat.add_le_add (Nat.mul_le_mul_right _ (le_max_left u v))
          (Nat.mul_le_mul_right _ (le_max_right u v))
    _ = max u v * ((f.coeff m).natDegree + m) := by ring

end Semiring

/-! ## Section 3 — `Z ↦ z` specialization does not increase any degree

`Trivariate.eval_on_Z Q z = Q.map (mapRingHom (evalRingHom z))` (see `Trivariate.eval_on_Z_eq`),
a coefficientwise ring map.  Applying a ring map can only annihilate coefficients or shrink the
inner `X`-degree, never raise either coordinate.  The general weighted statement
`natWeightedDegree_eval_on_Z_le` yields all the coordinate-degree corollaries the §5 chain uses.
-/

section Field

-- `Trivariate.eval_on_Z` fixes the base field at universe `0` (`F : Type`), so this section
-- specializes the polynomial type accordingly.
variable {F : Type} [Field F]

/-- **Specialization does not increase the weighted degree.**  For every weight pair,
`natWeightedDegree (eval_on_Z Q z) u v ≤ natWeightedDegree Q u v`. -/
theorem natWeightedDegree_eval_on_Z_le (Q : F[Z][X][Y]) (z : F) (u v : ℕ) :
    natWeightedDegree (Trivariate.eval_on_Z Q z) u v ≤ natWeightedDegree Q u v := by
  classical
  rw [Trivariate.eval_on_Z_eq]
  unfold natWeightedDegree
  refine Finset.sup_le fun k hk => ?_
  have hkQ : k ∈ Q.support := Polynomial.support_map_subset _ Q hk
  have hcoeff : (Q.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))).coeff k
      = (Q.coeff k).map (Polynomial.evalRingHom z) := by
    rw [Polynomial.coeff_map]; rfl
  have hnd : ((Q.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))).coeff k).natDegree
      ≤ (Q.coeff k).natDegree := by rw [hcoeff]; exact Polynomial.natDegree_map_le
  calc u * ((Q.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))).coeff k).natDegree + v * k
      ≤ u * (Q.coeff k).natDegree + v * k := Nat.add_le_add_right (Nat.mul_le_mul_left u hnd) _
    _ ≤ _ := Finset.le_sup (f := fun m => u * (Q.coeff m).natDegree + v * m) hkQ

/-- `degreeX` does not increase under `Z ↦ z`. -/
theorem degreeX_eval_on_Z_le (Q : F[Z][X][Y]) (z : F) :
    degreeX (Trivariate.eval_on_Z Q z) ≤ degreeX Q := by
  rw [degreeX_as_weighted_deg, degreeX_as_weighted_deg]
  exact natWeightedDegree_eval_on_Z_le Q z 1 0

/-- The `Y`-degree does not increase under `Z ↦ z`, i.e. `≤ D_Y Q`. -/
theorem natDegreeY_eval_on_Z_le (Q : F[Z][X][Y]) (z : F) :
    natDegreeY (Trivariate.eval_on_Z Q z) ≤ Trivariate.D_Y Q := by
  rw [degreeY_as_weighted_deg]
  unfold Trivariate.D_Y
  rw [degreeY_as_weighted_deg]
  exact natWeightedDegree_eval_on_Z_le Q z 0 1

/-- `totalDegree` does not increase under `Z ↦ z`. -/
theorem totalDegree_eval_on_Z_le (Q : F[Z][X][Y]) (z : F) :
    totalDegree (Trivariate.eval_on_Z Q z) ≤ totalDegree Q := by
  rw [total_deg_as_weighted_deg, total_deg_as_weighted_deg]
  exact natWeightedDegree_eval_on_Z_le Q z 1 1

/-- The `(1, k)`-weighted-degree field of `ModifiedGuruswami` (`Q_deg`) is preserved as a bound
under `Z ↦ z`: `natWeightedDegree (eval_on_Z Q z) 1 k ≤ natWeightedDegree Q 1 k`. -/
theorem natWeightedDegree_one_k_eval_on_Z_le (Q : F[Z][X][Y]) (z : F) (k : ℕ) :
    natWeightedDegree (Trivariate.eval_on_Z Q z) 1 k ≤ natWeightedDegree Q 1 k :=
  natWeightedDegree_eval_on_Z_le Q z 1 k

/-! ## Section 4 — algebraic corollaries of `eval_on_Z`

The in-tree `c57_eval_on_Z_zero/_add/_mul` give `eval_on_Z` as a (zero/additive/multiplicative)
map; these are the further homomorphism corollaries (`_one`, `_pow`, `_sum`, divisibility
transport) that downstream divisibility chains consume.  They are derived directly from
`Trivariate.eval_on_Z_eq`, not re-derived from the `c57_*` lemmas, so this file does not depend on
the `Agreement` module. -/

/-- `eval_on_Z` sends `1` to `1`. -/
@[simp]
lemma eval_on_Z_one (z : F) : Trivariate.eval_on_Z (1 : F[Z][X][Y]) z = 1 := by
  rw [Trivariate.eval_on_Z_eq]; simp

/-- `eval_on_Z` commutes with powers. -/
lemma eval_on_Z_pow (p : F[Z][X][Y]) (z : F) (n : ℕ) :
    Trivariate.eval_on_Z (p ^ n) z = (Trivariate.eval_on_Z p z) ^ n := by
  rw [Trivariate.eval_on_Z_eq, Trivariate.eval_on_Z_eq, Polynomial.map_pow]

/-- `eval_on_Z` commutes with finite sums. -/
lemma eval_on_Z_sum {ι : Type*} (s : Finset ι) (g : ι → F[Z][X][Y]) (z : F) :
    Trivariate.eval_on_Z (∑ i ∈ s, g i) z = ∑ i ∈ s, Trivariate.eval_on_Z (g i) z := by
  rw [Trivariate.eval_on_Z_eq, Polynomial.map_sum]
  exact Finset.sum_congr rfl (fun i _ => (Trivariate.eval_on_Z_eq (g i) z).symm)

/-- **Divisibility transport under `Z ↦ z`** (corollary of multiplicativity): if `p ∣ q` over
`F[Z][X][Y]`, then `eval_on_Z p z ∣ eval_on_Z q z` over `F[X][Y]`.  This is the shape the residual
GS-multiplicity → graph-vanishing ("Gap B") divisibility chain consumes. -/
theorem dvd_eval_on_Z {p q : F[Z][X][Y]} (z : F) (h : p ∣ q) :
    Trivariate.eval_on_Z p z ∣ Trivariate.eval_on_Z q z := by
  obtain ⟨c, rfl⟩ := h
  refine ⟨Trivariate.eval_on_Z c z, ?_⟩
  rw [Trivariate.eval_on_Z_eq, Trivariate.eval_on_Z_eq, Trivariate.eval_on_Z_eq,
    Polynomial.map_mul]

end Field

/-! ## Section 5 — root-count versus degree

A clean `#roots ≤ degree`-style helper specialized to the weighted/total degree, built on the
in-tree `card_evalX_eq_zero_le_degreeX`. -/

section FieldDecEq

variable [Field F] [DecidableEq F]

/-- The number of `X`-evaluation roots of a nonzero `A` in a finite point set is at most its
`(1, 0)`-weighted degree (i.e. `degreeX`, phrased weightedly for the §5 counting). -/
theorem card_evalX_eq_zero_le_natWeightedDegree (A : F[X][Y]) (hA : A ≠ 0) (P : Finset F) :
    (P.filter (fun x => evalX x A = 0)).card ≤ natWeightedDegree A 1 0 := by
  rw [← degreeX_as_weighted_deg]
  exact card_evalX_eq_zero_le_degreeX A hA P

/-- The number of `X`-evaluation roots of a nonzero `A` in a finite point set is at most its
total degree. -/
theorem card_evalX_eq_zero_le_totalDegree (A : F[X][Y]) (hA : A ≠ 0) (P : Finset F) :
    (P.filter (fun x => evalX x A = 0)).card ≤ totalDegree A :=
  le_trans (card_evalX_eq_zero_le_degreeX A hA P) (degreeX_le_totalDegree A)

end FieldDecEq

end

end BivariateDegreeToolkit

end ArkLib

/-! ## Axiom audit

Each lemma above is kernel-clean: it depends only on `propext`, `Classical.choice`, `Quot.sound`
(no `sorry`, no `sorryAx`, no `native_decide`/`ofReduceBool`). -/

#print axioms ArkLib.BivariateDegreeToolkit.natWeightedDegree_zero
#print axioms ArkLib.BivariateDegreeToolkit.weight_coeff_le_natWeightedDegree
#print axioms ArkLib.BivariateDegreeToolkit.natWeightedDegree_mono_weights
#print axioms ArkLib.BivariateDegreeToolkit.natWeightedDegree_mul_le
#print axioms ArkLib.BivariateDegreeToolkit.natWeightedDegree_one_le
#print axioms ArkLib.BivariateDegreeToolkit.natWeightedDegree_pow_le
#print axioms ArkLib.BivariateDegreeToolkit.natWeightedDegree_v_zero_le
#print axioms ArkLib.BivariateDegreeToolkit.natWeightedDegree_u_zero_le
#print axioms ArkLib.BivariateDegreeToolkit.totalDegree_le_degreeX_add_natDegreeY
#print axioms ArkLib.BivariateDegreeToolkit.degreeX_le_totalDegree
#print axioms ArkLib.BivariateDegreeToolkit.natDegreeY_le_totalDegree
#print axioms ArkLib.BivariateDegreeToolkit.natWeightedDegree_le_max_mul_totalDegree
#print axioms ArkLib.BivariateDegreeToolkit.natWeightedDegree_eval_on_Z_le
#print axioms ArkLib.BivariateDegreeToolkit.degreeX_eval_on_Z_le
#print axioms ArkLib.BivariateDegreeToolkit.natDegreeY_eval_on_Z_le
#print axioms ArkLib.BivariateDegreeToolkit.totalDegree_eval_on_Z_le
#print axioms ArkLib.BivariateDegreeToolkit.natWeightedDegree_one_k_eval_on_Z_le
#print axioms ArkLib.BivariateDegreeToolkit.eval_on_Z_one
#print axioms ArkLib.BivariateDegreeToolkit.eval_on_Z_pow
#print axioms ArkLib.BivariateDegreeToolkit.eval_on_Z_sum
#print axioms ArkLib.BivariateDegreeToolkit.dvd_eval_on_Z
#print axioms ArkLib.BivariateDegreeToolkit.card_evalX_eq_zero_le_natWeightedDegree
#print axioms ArkLib.BivariateDegreeToolkit.card_evalX_eq_zero_le_totalDegree
