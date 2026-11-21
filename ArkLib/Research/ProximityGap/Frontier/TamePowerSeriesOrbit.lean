/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

/-! # Conjugate branches of a tame power substitution

The rotation period of a root is bounded by the original value degree.
Its coefficients therefore descend to a parameter of exactly that period.
-/

set_option autoImplicit false
noncomputable section

open Function Polynomial PowerSeries
open scoped PowerSeries

namespace ArkLib.ProximityGap.Frontier.TamePowerSeriesOrbit

variable {K : Type*} [Field K]

theorem iterate_rescale (ζ : K) (j : ℕ) (y : K⟦X⟧) :
    (rescale ζ)^[j] y = rescale (ζ^j) y := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, rescale_rescale, pow_succ]

/-- Rotation by an nth root fixes every series in the original coordinate. -/
theorem rescale_expand_fixed {n : ℕ} (hn : n ≠ 0) {ζ : K} (hζ : ζ^n = 1) (u : K⟦X⟧) :
    rescale ζ (expand n hn u) = expand n hn u := by
  ext j
  rw [coeff_rescale, PowerSeries.coeff_expand]
  split_ifs with hj
  · obtain ⟨k,rfl⟩ := hj
    rw [pow_mul, hζ, one_pow, one_mul]
  · simp

/-- Power substitution intertwines the rotations in the two parameter rings. -/
theorem rescale_expand (ζ : K) {k : ℕ} (hk : k ≠ 0) (u : K⟦X⟧) :
    rescale ζ (expand k hk u) = expand k hk (rescale (ζ^k) u) := by
  ext j
  rw [coeff_rescale, PowerSeries.coeff_expand, PowerSeries.coeff_expand]
  split_ifs with hj
  · obtain ⟨l,rfl⟩ := hj
    rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hk), coeff_rescale, pow_mul]
  · simp

/-- The minimal rotation period is at most the value degree. Its distinct
rotations are actual roots of the polynomial in the expanded coordinate. -/
theorem orbit_length_le (F : K⟦X⟧[X]) (hF : F.Monic) {n : ℕ} (hn : n ≠ 0)
    {ζ : K} (hζ : ζ^n = 1) (y : K⟦X⟧) (hy : (F.map (PowerSeries.expand n hn (R := K)).toRingHom).IsRoot y) :
    minimalPeriod (rescale ζ) y ≤ F.natDegree := by
  classical
  let f := F.map (PowerSeries.expand n hn (R := K)).toRingHom
  have hf : f ≠ 0 := (hF.map _).ne_zero
  have hrot (j : ℕ) : f.IsRoot ((rescale ζ)^[j] y) := by
    rw [iterate_rescale]
    have hfix : f.map (rescale (ζ^j)) = f := by
      ext1 i
      simp only [f, Polynomial.coeff_map]
      apply rescale_expand_fixed
      rw [← pow_mul, Nat.mul_comm, pow_mul, hζ, one_pow]
    rw [← hfix]
    exact hy.map
  let e := minimalPeriod (rescale ζ) y
  have hcount : (Finset.range e).card ≤ f.roots.toFinset.card := by
    apply Finset.card_le_card_of_injOn (fun j => (rescale ζ)^[j] y)
    · intro j _
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hf).mpr (hrot j))
    · intro i hi j hj hij
      exact Function.iterate_injOn_Iio_minimalPeriod (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij
  simpa only [Finset.card_range] using
    hcount.trans (Multiset.toFinset_card_le _ |>.trans ((Polynomial.card_roots' _).trans natDegree_map_le))

/-- A full orbit of a root is represented over the parameter t with
X=t^e, where e is the orbit length. No extraneous fractional powers occur. -/
theorem root_descends_to_orbit {n : ℕ} (hn : 0 < n) {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    (y : K⟦X⟧) :
    let e := minimalPeriod (rescale ζ) y
    ∃ k : ℕ, ∃ hk : k ≠ 0, n = e*k ∧ ∃ u : K⟦X⟧, expand k hk u = y := by
  let e := minimalPeriod (rescale ζ) y
  have hper : IsPeriodicPt (rescale ζ) n y := by
    change (rescale ζ)^[n] y = y
    rw [iterate_rescale, hζ.pow_eq_one, rescale_one]
    rfl
  have he : 0 < e := hper.minimalPeriod_pos hn
  obtain ⟨k,hk⟩ := hper.minimalPeriod_dvd
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk; omega
  have hfix : rescale (ζ^e) y = y :=
    (iterate_rescale ζ e y).symm.trans (isPeriodicPt_minimalPeriod _ _)
  have hsupport (i : ℕ) (hi : y.coeff i ≠ 0) : k ∣ i := by
    have hc := congrArg (PowerSeries.coeff (R := K) i) hfix
    rw [coeff_rescale] at hc
    have heq : (ζ^e)^i = 1 := mul_right_cancel₀ hi (hc.trans (one_mul _).symm)
    rw [← pow_mul] at heq
    have hd := (hζ.pow_eq_one_iff_dvd (e*i)).mp heq
    rw [hk] at hd
    exact Nat.dvd_of_mul_dvd_mul_left he hd
  refine ⟨k,hk0,hk,PowerSeries.mk (fun j => y.coeff (k*j)),?_⟩
  ext i
  rw [PowerSeries.coeff_expand]
  split_ifs with hi
  · simp [coeff_mk, Nat.mul_div_cancel' hi]
  · exact (not_ne_iff.mp (fun h => hi (hsupport i h))).symm

theorem expand_injective {k : ℕ} (hk : k ≠ 0) :
    Function.Injective (PowerSeries.expand k hk (R := K)) := by
  intro a b hab
  ext i
  simpa only [PowerSeries.coeff_expand_mul] using congrArg (PowerSeries.coeff (k*i)) hab

/-- A root of the expanded polynomial yields a normalized representative.
All e scalings of this representative are distinct and the original equation
is satisfied over the coordinate s=t^e. -/
theorem normalized_root_orbit (F : K⟦X⟧[X]) (hF : F.Monic) {n : ℕ} (hn : 0 < n)
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) (y : K⟦X⟧)
    (hy : (F.map (PowerSeries.expand n hn.ne' (R := K)).toRingHom).IsRoot y) :
    ∃ (e k : ℕ) (he : e ≠ 0) (hk : k ≠ 0) (u : K⟦X⟧),
      n = e*k ∧ e ≤ F.natDegree ∧ expand k hk u = y ∧ IsPrimitiveRoot (ζ^k) e ∧
      (F.map (PowerSeries.expand e he).toRingHom).IsRoot u ∧
      Function.Injective (fun j : Fin e => rescale ((ζ^k)^j.val) u) := by
  let e := minimalPeriod (rescale ζ) y
  have hnper : IsPeriodicPt (rescale ζ) n y := by
    change (rescale ζ)^[n] y = y
    rw [iterate_rescale, hζ.pow_eq_one, rescale_one]
    rfl
  have he : e ≠ 0 := (hnper.minimalPeriod_pos hn).ne'
  obtain ⟨k,hk,hN,u,hu⟩ := root_descends_to_orbit hn hζ y
  change n = e*k at hN
  refine ⟨e,k,he,hk,u,hN,orbit_length_le F hF hn.ne' hζ.pow_eq_one y hy,hu,?_,?_,?_⟩
  · refine ⟨?_,fun i hi => ?_⟩
    · rw [← pow_mul, Nat.mul_comm, ← hN, hζ.pow_eq_one]
    · rw [← pow_mul, hζ.pow_eq_one_iff_dvd, hN, Nat.mul_comm e k] at hi
      exact Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hk) hi
  · apply Polynomial.IsRoot.of_map (f := (PowerSeries.expand k hk (R := K)).toRingHom)
      (hf := expand_injective hk)
    rw [Polynomial.map_map]
    have H : (PowerSeries.expand k hk (R := K)).toRingHom.comp (PowerSeries.expand e he).toRingHom =
        (PowerSeries.expand n hn.ne').toRingHom := by
      apply RingHom.ext
      intro w
      have hEq : k*e = n := (Nat.mul_comm k e).trans hN.symm
      have hcongr (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a=b) :
          PowerSeries.expand a ha w = PowerSeries.expand b hb w := by subst b; rfl
      exact (PowerSeries.expand_mul k hk e he w).symm.trans (hcongr _ _ _ _ hEq)
    rw [H]
    change (F.map (PowerSeries.expand n hn.ne' (R := K)).toRingHom).IsRoot (PowerSeries.expand k hk u)
    rwa [hu]
  · intro i j hij
    apply Fin.ext
    apply Function.iterate_injOn_Iio_minimalPeriod i.isLt j.isLt
    dsimp only
    rw [iterate_rescale, iterate_rescale, ← hu, rescale_expand, rescale_expand]
    apply congrArg (PowerSeries.expand k hk)
    simpa only [← pow_mul, Nat.mul_comm i.val k, Nat.mul_comm j.val k] using hij

#print axioms normalized_root_orbit
#print axioms orbit_length_le
#print axioms root_descends_to_orbit

end ArkLib.ProximityGap.Frontier.TamePowerSeriesOrbit
