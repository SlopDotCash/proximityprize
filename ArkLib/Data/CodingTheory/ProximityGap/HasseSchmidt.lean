/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.ENat.Lattice
import Mathlib.RingTheory.Valuation.Basic

/-!
# Hasse–Schmidt derivations: a degenerate first-detection depth and a genuine detection order

## The original scaffolding is degenerate (audit finding PG-017, 2026-10-28)

Besides the structure `HasseSchmidtDerivation` itself, the first part of this file keeps, with
their original statements, the three declarations of an abandoned "non-Archimedean extrapolation
norm" idea. They are degenerate and are kept only as a checked record of that fact; nothing in the
repository uses them.

* `extrapolationNorm hs x`, the least depth `k` with `hs.D k x ≠ 0`, is **identically zero**
  (`extrapolationNorm_eq_zero`). Since `D 0 = id`, every nonzero `x` is detected at depth `0`; for
  `x = 0` the detection set is empty and the `ℕ`-valued convention `sInf ∅ = 0` again gives `0`.
* The class `ValuationDisparity` is therefore **vacuous**: the premise
  `extrapolationNorm hs x ≠ extrapolationNorm hs y` of its only field never holds, so every
  Hasse–Schmidt derivation over every field is an instance (`ValuationDisparity.vacuous`).
* `extrapolationNorm_add_of_disparity` is consequently content-free: its hypothesis is never
  satisfiable. It is not evidence of any valuation result, adversarial or otherwise.

Earlier docstrings described `ValuationDisparity` as an assumption not known to hold (and said to
fail) "against an adaptive adversary on a characteristic-2 STARK field", citing
`CandidateExtrapolation.lean`. That was wrong (the class holds vacuously), and the cited file is no
longer tracked: it was deleted from `ArkLib/Data/CodingTheory/Quarantine/` in commit `5a9c37a16`.
A still earlier revision presented the class projection as a "1M dollar proof" resolving the
Proximity Prize metric; per Issues #169/#171/#232 such fake-completion framing is banned.

## A nondegenerate replacement: the detection order through a ring homomorphism

The informative version of "first-detection depth" composes the derivation with a ring
homomorphism `φ : R →+* S` and takes values in `ℕ∞`, with the deliberate convention that the order
is `⊤` when `φ` kills every `D k x`:
`detectionOrder hs φ x = ⨅ (k : ℕ) (_ : φ (hs.D k x) ≠ 0), (k : ℕ∞)`. We prove:

* `detectionOrder_zero` (`= ⊤`), `detectionOrder_one` (`= 0` for nontrivial `S`) and
  `detectionOrder_neg`;
* the ultrametric inequality `min_le_detectionOrder_add` and the strong-triangle equality
  `detectionOrder_add_eq_min` for summands of distinct order, for *every* Hasse–Schmidt derivation
  and every `φ` (only the additivity of `φ ∘ D k` is used);
* `detectionOrder_mul`: if `S` has no zero divisors, the Leibniz rule makes the order additive on
  products, so `detectionValuation` packages it as an `AddValuation R ℕ∞` (for nontrivial `S`);
* nondegeneracy: for the polynomial Hasse derivatives `polynomialHasse A` and `φ` evaluation at
  `a`, the detection order of `f ≠ 0` is `rootMultiplicity a f`
  (`detectionOrder_polynomialHasse_eval`); in particular it is `n` on `(X - C a) ^ n` over any
  nontrivial commutative ring (`detectionOrder_polynomialHasse_X_sub_C_pow`). Through
  `φ = RingHom.id` it is `0` on every nonzero element (`detectionOrder_id_of_ne_zero`), which is
  exactly why `extrapolationNorm` degenerated.

None of this is a statement about Reed–Solomon codes, proximity gaps, `ε_mca` or the Proximity
Prize, and nothing in this file is progress on the prize.
-/

namespace ArkLib.CodingTheory

universe u
variable {R : Type u} [CommRing R]

/-- A sequence of additive operators `D : ℕ → R → R` is a Hasse–Schmidt derivation if it satisfies
the generalized Leibniz rule and `D 0 = id`. -/
structure HasseSchmidtDerivation (R : Type u) [CommRing R] where
  D : ℕ → (R →+ R)
  d_zero : ∀ x, D 0 x = x
  leibniz : ∀ (n : ℕ) (x y : R),
    D n (x * y) = (Finset.range (n + 1)).sum (fun i => D i x * D (n - i) y)

namespace HasseSchmidtDerivation

open Classical

/-- **Degenerate (identically zero); superseded by `detectionOrder`.** The "extrapolation norm":
the least depth `k` at which `D k x ≠ 0`, with the `ℕ`-valued convention `sInf ∅ = 0`. It is `0`
for every `x` (`extrapolationNorm_eq_zero`): `D 0 = id` detects every nonzero `x` at depth `0`,
and for `x = 0` the detection set is empty. Kept only as a record of that degeneracy. -/
noncomputable def extrapolationNorm (hs : HasseSchmidtDerivation R) (x : R) : ℕ :=
  sInf {k : ℕ | hs.D k x ≠ 0}

/-- The extrapolation norm is identically zero (audit finding PG-017): for `x ≠ 0` the detection
set contains `0` because `D 0 x = x`, and for `x = 0` it is empty, where `sInf ∅ = 0` on `ℕ`. -/
theorem extrapolationNorm_eq_zero (hs : HasseSchmidtDerivation R) (x : R) :
    extrapolationNorm hs x = 0 := by
  unfold extrapolationNorm
  refine Nat.sInf_eq_zero.mpr ?_
  by_cases hx : x = 0
  · right
    ext k
    simp [hx]
  · left
    change hs.D 0 x ≠ 0
    rwa [hs.d_zero]

/-- **Vacuous; kept only as a record.** The intended strong-triangle behaviour of
`extrapolationNorm`. Because `extrapolationNorm` is identically zero, the premise
`extrapolationNorm hs x ≠ extrapolationNorm hs y` never holds, so this class imposes no condition
at all: every Hasse–Schmidt derivation over every field is an instance
(`ValuationDisparity.vacuous`). For a nondegenerate order the strong-triangle equality holds
unconditionally; see `detectionOrder_add_eq_min`. -/
class ValuationDisparity (F : Type u) [Field F] (hs : HasseSchmidtDerivation F) where
  disparity (x y : F) : extrapolationNorm hs x ≠ extrapolationNorm hs y →
    extrapolationNorm hs (x + y) = min (extrapolationNorm hs x) (extrapolationNorm hs y)

/-- `ValuationDisparity` holds, vacuously, for every Hasse–Schmidt derivation over every field:
the premise of its only field contradicts `extrapolationNorm_eq_zero`. -/
instance ValuationDisparity.vacuous {F : Type u} [Field F] (hs : HasseSchmidtDerivation F) :
    ValuationDisparity F hs where
  disparity x y h :=
    absurd ((extrapolationNorm_eq_zero hs x).trans (extrapolationNorm_eq_zero hs y).symm) h

/-- **Content-free.** The strong-triangle equality for `extrapolationNorm` on inputs of distinct
norm. Its hypothesis `h_disjoint` is never satisfiable (`extrapolationNorm_eq_zero`) and the class
it assumes is vacuous (`ValuationDisparity.vacuous`), so this lemma says nothing; in particular it
is not evidence of any adversarial valuation result. The genuine statement for a nondegenerate
order is `detectionOrder_add_eq_min`. -/
theorem extrapolationNorm_add_of_disparity {F : Type u} [Field F]
    (hs : HasseSchmidtDerivation F) [ValuationDisparity F hs]
    (x y : F) (h_disjoint : extrapolationNorm hs x ≠ extrapolationNorm hs y) :
    extrapolationNorm hs (x + y) = min (extrapolationNorm hs x) (extrapolationNorm hs y) :=
  ValuationDisparity.disparity x y h_disjoint

end HasseSchmidtDerivation

/-! ### A nondegenerate replacement: the detection order through a ring homomorphism -/

namespace HasseSchmidtDerivation

section DetectionOrder

variable {S : Type*} [CommRing S] (hs : HasseSchmidtDerivation R) (φ : R →+* S)

/-- The **detection order** of `x` through `φ : R →+* S`: the least depth `k` at which
`φ (D k x) ≠ 0`, valued in `ℕ∞`, with the deliberate convention that it is `⊤` when `φ` kills
every `D k x` (in particular at `x = 0`). For the polynomial Hasse derivatives and `φ` evaluation
at `a` it is the order of vanishing at `a` (`detectionOrder_polynomialHasse_eval`). -/
noncomputable def detectionOrder (x : R) : ℕ∞ :=
  ⨅ (k : ℕ) (_ : φ (hs.D k x) ≠ 0), (k : ℕ∞)

theorem detectionOrder_le {x : R} {k : ℕ} (h : φ (hs.D k x) ≠ 0) :
    hs.detectionOrder φ x ≤ k :=
  iInf₂_le k h

theorem le_detectionOrder_iff {x : R} {n : ℕ} :
    (n : ℕ∞) ≤ hs.detectionOrder φ x ↔ ∀ k < n, φ (hs.D k x) = 0 := by
  refine ⟨fun hn k hk => ?_, fun h => le_iInf₂ fun k hk => ?_⟩
  · by_contra hne
    exact absurd (ENat.coe_le_coe.mp (hn.trans (hs.detectionOrder_le φ hne))) (not_le.mpr hk)
  · by_contra hlt
    exact hk (h k (ENat.coe_lt_coe.mp (not_le.mp hlt)))

theorem detectionOrder_eq_top_iff {x : R} :
    hs.detectionOrder φ x = ⊤ ↔ ∀ k, φ (hs.D k x) = 0 := by
  simp [detectionOrder]

theorem detectionOrder_eq_coe_iff {x : R} {n : ℕ} :
    hs.detectionOrder φ x = n ↔ φ (hs.D n x) ≠ 0 ∧ ∀ k < n, φ (hs.D k x) = 0 := by
  refine ⟨fun h => ⟨fun h0 => ?_, (hs.le_detectionOrder_iff φ).mp h.ge⟩,
    fun h => le_antisymm (hs.detectionOrder_le φ h.1) ((hs.le_detectionOrder_iff φ).mpr h.2)⟩
  have hlt := (hs.le_detectionOrder_iff φ).mp h.ge
  have hsucc : ((n + 1 : ℕ) : ℕ∞) ≤ hs.detectionOrder φ x := by
    refine (hs.le_detectionOrder_iff φ).mpr fun k hk => ?_
    by_cases hkn : k < n
    · exact hlt k hkn
    · obtain rfl : k = n := by omega
      exact h0
  rw [h] at hsucc
  exact absurd (ENat.coe_le_coe.mp hsucc) (by omega)

@[simp]
theorem detectionOrder_zero : hs.detectionOrder φ 0 = ⊤ :=
  (hs.detectionOrder_eq_top_iff φ).mpr fun k => by simp

@[simp]
theorem detectionOrder_one [Nontrivial S] : hs.detectionOrder φ 1 = 0 := by
  have h := (hs.detectionOrder_eq_coe_iff φ (x := 1) (n := 0)).mpr
    ⟨by simp [hs.d_zero], fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  exact_mod_cast h

@[simp]
theorem detectionOrder_neg (x : R) : hs.detectionOrder φ (-x) = hs.detectionOrder φ x := by
  simp [detectionOrder]

/-- The ultrametric inequality. It only uses that each `φ ∘ D k` is additive. -/
theorem min_le_detectionOrder_add (x y : R) :
    min (hs.detectionOrder φ x) (hs.detectionOrder φ y) ≤ hs.detectionOrder φ (x + y) := by
  refine le_iInf₂ fun k hk => ?_
  simp only [map_add] at hk
  by_cases hx : φ (hs.D k x) = 0
  · rw [hx, zero_add] at hk
    exact min_le_of_right_le (hs.detectionOrder_le φ hk)
  · exact min_le_of_left_le (hs.detectionOrder_le φ hx)

theorem detectionOrder_add_eq_left_of_lt {x y : R}
    (h : hs.detectionOrder φ x < hs.detectionOrder φ y) :
    hs.detectionOrder φ (x + y) = hs.detectionOrder φ x := by
  refine le_antisymm ?_ ?_
  · have key := hs.min_le_detectionOrder_add φ (x + y) (-y)
    rw [add_neg_cancel_right, detectionOrder_neg] at key
    exact (min_le_iff.mp key).resolve_right (not_le.mpr h)
  · have key := hs.min_le_detectionOrder_add φ x y
    rwa [min_eq_left h.le] at key

/-- The strong-triangle equality for summands of distinct detection order. Unlike the vacuous
`ValuationDisparity`, this holds unconditionally, for every Hasse–Schmidt derivation and every
ring homomorphism `φ`, and its premise can be met: the detection order takes every value `n : ℕ`
(`detectionOrder_polynomialHasse_X_sub_C_pow`). -/
theorem detectionOrder_add_eq_min {x y : R}
    (h : hs.detectionOrder φ x ≠ hs.detectionOrder φ y) :
    hs.detectionOrder φ (x + y) = min (hs.detectionOrder φ x) (hs.detectionOrder φ y) := by
  rcases lt_or_gt_of_ne h with h | h
  · rw [min_eq_left h.le, hs.detectionOrder_add_eq_left_of_lt φ h]
  · rw [min_eq_right h.le, add_comm, hs.detectionOrder_add_eq_left_of_lt φ h]

/-- If `S` has no zero divisors, the Leibniz rule makes the detection order additive on products:
when `x` and `y` are first detected at depths `a` and `b`, every term of the Leibniz expansion of
`φ (D k (x * y))` vanishes for `k < a + b`, and for `k = a + b` the only surviving term is
`φ (D a x) * φ (D b y) ≠ 0`. -/
theorem detectionOrder_mul [NoZeroDivisors S] (x y : R) :
    hs.detectionOrder φ (x * y) = hs.detectionOrder φ x + hs.detectionOrder φ y := by
  by_cases hx : hs.detectionOrder φ x = ⊤
  · rw [hx, top_add, hs.detectionOrder_eq_top_iff φ]
    intro n
    rw [hs.leibniz, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_mul, (hs.detectionOrder_eq_top_iff φ).mp hx i, zero_mul]
  by_cases hy : hs.detectionOrder φ y = ⊤
  · rw [hy, add_top, hs.detectionOrder_eq_top_iff φ]
    intro n
    rw [hs.leibniz, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_mul, (hs.detectionOrder_eq_top_iff φ).mp hy (n - i), mul_zero]
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hx
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp hy
  obtain ⟨hxa, hxlt⟩ := (hs.detectionOrder_eq_coe_iff φ).mp ha.symm
  obtain ⟨hyb, hylt⟩ := (hs.detectionOrder_eq_coe_iff φ).mp hb.symm
  rw [← ha, ← hb, ← ENat.coe_add, hs.detectionOrder_eq_coe_iff φ]
  refine ⟨?_, fun k hk => ?_⟩
  · rw [hs.leibniz, map_sum, Finset.sum_eq_single a]
    · rw [map_mul, Nat.add_sub_cancel_left]
      exact mul_ne_zero hxa hyb
    · intro i hi hia
      have hi' := Finset.mem_range.mp hi
      rw [map_mul]
      rcases lt_or_gt_of_ne hia with hia | hia
      · rw [hxlt i hia, zero_mul]
      · rw [hylt (a + b - i) (by omega), mul_zero]
    · intro ha'
      exact absurd (Finset.mem_range.mpr (by omega)) ha'
  · rw [hs.leibniz, map_sum]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [map_mul]
    rcases lt_or_ge i a with hia | hia
    · rw [hxlt i hia, zero_mul]
    · rw [hylt (k - i) (by omega), mul_zero]

/-- For a nontrivial `S` without zero divisors, the detection order is an additive valuation on
`R` with values in `ℕ∞`. -/
noncomputable def detectionValuation [Nontrivial S] [NoZeroDivisors S] : AddValuation R ℕ∞ :=
  AddValuation.of (hs.detectionOrder φ) (hs.detectionOrder_zero φ) (hs.detectionOrder_one φ)
    (hs.min_le_detectionOrder_add φ) (hs.detectionOrder_mul φ)

@[simp]
theorem detectionValuation_apply [Nontrivial S] [NoZeroDivisors S] (x : R) :
    hs.detectionValuation φ x = hs.detectionOrder φ x :=
  rfl

/-- Detection through the identity only tests for zero: every nonzero element is detected by
`D 0 = id` at depth `0`. This is exactly why `extrapolationNorm` is degenerate. -/
theorem detectionOrder_id_of_ne_zero {x : R} (hx : x ≠ 0) :
    hs.detectionOrder (RingHom.id R) x = 0 := by
  have h := (hs.detectionOrder_eq_coe_iff (RingHom.id R) (x := x) (n := 0)).mpr
    ⟨by simpa [hs.d_zero] using hx, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  exact_mod_cast h

end DetectionOrder

section Polynomial

open Polynomial

/-- The Hasse derivatives `Polynomial.hasseDeriv k` on `A[X]` form a Hasse–Schmidt derivation
(Leibniz rule: `Polynomial.hasseDeriv_mul`). -/
noncomputable def polynomialHasse (A : Type u) [CommRing A] : HasseSchmidtDerivation A[X] where
  D k := (hasseDeriv k).toAddMonoidHom
  d_zero f := hasseDeriv_zero' f
  leibniz n f g := by
    simp only [LinearMap.toAddMonoidHom_coe]
    rw [hasseDeriv_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

@[simp]
theorem polynomialHasse_D_apply {A : Type u} [CommRing A] (k : ℕ) (f : A[X]) :
    (polynomialHasse A).D k f = hasseDeriv k f :=
  rfl

/-- For the polynomial Hasse derivatives, detection through evaluation at `a` is the order of
vanishing at `a`: `(hasseDeriv k f).eval a` is the `k`-th Taylor coefficient of `f` at `a`
(`Polynomial.taylor_coeff`), so for `f ≠ 0` the detection order is `rootMultiplicity a f`. -/
theorem detectionOrder_polynomialHasse_eval {A : Type u} [CommRing A] (a : A) {f : A[X]}
    (hf : f ≠ 0) :
    (polynomialHasse A).detectionOrder (evalRingHom a) f = rootMultiplicity a f := by
  have key : ∀ k, evalRingHom a ((polynomialHasse A).D k f) = (taylor a f).coeff k := by
    intro k
    rw [polynomialHasse_D_apply, coe_evalRingHom, taylor_coeff]
  have ht : taylor a f ≠ 0 := fun h => hf ((taylor_eq_zero a f).mp h)
  rw [rootMultiplicity_eq_natTrailingDegree, ← taylor_apply, detectionOrder_eq_coe_iff]
  simp only [key]
  exact ⟨mt trailingCoeff_eq_zero.mp ht, fun k hk => coeff_eq_zero_of_lt_natTrailingDegree hk⟩

/-- The detection order is not degenerate: over any nontrivial commutative ring it takes the value
`n` on `(X - C a) ^ n` (through evaluation at `a`), whereas `extrapolationNorm` is `0` there, as
it is everywhere. -/
theorem detectionOrder_polynomialHasse_X_sub_C_pow {A : Type u} [CommRing A] [Nontrivial A]
    (a : A) (n : ℕ) :
    (polynomialHasse A).detectionOrder (evalRingHom a) ((X - C a) ^ n) = n := by
  rw [detectionOrder_polynomialHasse_eval a ((monic_X_sub_C a).pow n).ne_zero,
    rootMultiplicity_X_sub_C_pow]

end Polynomial

end HasseSchmidtDerivation
end ArkLib.CodingTheory
