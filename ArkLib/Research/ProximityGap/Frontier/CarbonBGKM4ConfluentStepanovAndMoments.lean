/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.MobiusStepanov
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumFourthMoment
import ArkLib.Data.CodingTheory.ProximityGap.CharPDeepMomentTail
import ArkLib.Data.CodingTheory.ProximityGap.DCEnergyCorrection
import ArkLib.Research.ProximityGap.Frontier._PrizeShapePrimeP30
import ArkLib.Research.ProximityGap.Frontier._PrizeShapePrimeP30Second

/-!
# Degree-2 Confluent Shift-Stepanov Bounds, Unconditional `O(n^{2r - 4/3})` Moment Ladder,
Sum-Product Expansion, and Midpoint-Resonance Exclusion

This module advances the analytic CORE and production moment bounds (`n = 2^30`) on four fronts,
using only prebuilt canonical substrate imports:

1. **Degree-2 Confluent Graded Shift-Stepanov Engine (`§1`):**
   Unlike fractional-linear Möbius auxiliaries (`MobiusStepanov`, which clear a degree-3 factor
   `X(X - a)(X - b)` and pay `+2` degrees per derivative), pure additive coset shifts
   `x^N = c₀ ∧ (x - a)^M ∈ {K_0, ..., K_{J-1}}` have no finite pole and clear the degree-2 factor
   `X(X - a)`. Each weighted derivative increases the residual degree by at most `1` rather than
   `2`, halving the graded derivative constraint triangle from `D(A + D - 1)` to
   `D A + D(D - 1)/2` and improving the asymptotic leading constant from `3` to
   `3 / 2^(1/3) ≈ 2.381`.
   At `N = M = 2^30` (`p > 2^41`), asymmetric optimization `(A = 838860, C = 1280, B = 2490,
   D = 1621001)` yields the unconditional pointwise coset-shift and representation cap
   `≤ 2,495,902 < 2^22` (`2495902^3 ≤ 64 * (2^30)^2`, discharging the Garcia–Voloch `4 n^(2/3)`
   threshold in characteristic `p`), alongside a `4`-coset simultaneous shift cap `≤ 6,291,183`.

2. **Exact Difference-Autocorrelation Moment Step, `O(n^{2r - 4/3})` Higher-Moment Ladder, and
   Cross-Coset Non-Antipodal Sextuple Bounds (`§2`):**
   Groups `CharPMomentRecursion.rEnergy_succ_double_sum` by difference `δ = s - t` to prove the
   exact identity
   `rEnergy G (r + 1) = |G| * rEnergy G r + ∑_{δ ≠ 0} diffCount G δ * autocorr G r δ`
   together with `∑_{δ ≠ 0} autocorr G r δ = |G|^(2r) - rEnergy G r`. Any off-diagonal difference
   cap `diffCount G δ ≤ M` (`M + 1 ≤ |G|`) therefore propagates to **every** rung `r ≥ 2`:
   `rEnergy G r ≤ (M + 1) * |G|^(2r - 2)`,
   delivering the first unconditional `O(n^{8/3})` fourth, `O(n^{14/3})` sixth, `O(n^{20/3})`
   eighth, and `O(n^{38/3})` fourteenth Gauss-sum moment bounds on `μ_{2^30}` (`p > 2^41`), plus
   cross-coset non-antipodal zero-sum sextuple bounds `≤ M * |C₁|^2 * |C₂|^2` across arbitrary
   sub-cosets (including `μ_8, μ_{16}, ..., μ_{2^30}`).

3. **Unconditional Sum-Product Expansion (`|G + G| > 430 |G|`), `DCEnergyBound` `r`-Fold Sumset
   Growth, and Real-Spectrum Law (`§3`):**
   Cauchy–Schwarz on `freq G r` gives `|G|^(2r) ≤ |Σ^r G| * rEnergy G r`, forcing unconditionally
   `|μ_{2^30} + μ_{2^30}| ≥ 461,925,605,526 > 430 * 2^30` whenever `p > 2^41` and `2^30 ∣ p - 1`,
   and near-maximal `r`-fold expansion `((2r - 1)!! + c) * |Σ^r G| ≥ |G|^r` under `DCEnergyBound`.
   Also proves `(eta ψ G b).im = 0` and `starRingEnd ℂ (eta ψ G b) = eta ψ G b` for `-G = G`.

4. **Unconditional Midpoint-Resonance Cap & Exclusion of `1 -> 2` Wick Defect at `P₁, P₂` (`§4`):**
   Proves `3|G|^2 - 3|G| ≤ rEnergy G 2` and `midpointCount G ≤ 2,495,902 * 2^30 < 2^52 < 2^59`
   unconditionally on `μ_{2^30}` at both certified production primes `P₁` and `P₂`, refuting
   `FirstStepOneUnitDefect` without auxiliary representation hypotheses.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.CarbonBGKM4ConfluentStepanovAndMoments

open Finset Polynomial AddChar
open ProximityGap.MobiusStepanov (weighted le_rootMultiplicity_of_weighted_vanishing)
open ArkLib.ProximityGap.Wronskian
  (eq_zero_of_sum_pow_block rootMultiplicity_sparse_lt eq_zero_of_sum_monomial_eq_zero)
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment (addEnergy)
open ArkLib.ProximityGap.SubgroupGaussSumMoment (rEnergy subgroup_gaussSum_moment)
open ArkLib.ProximityGap.CharPMomentRecursion
  (freq sum_freq rEnergy_eq_sum_freq_sq autocorr autocorr_zero rEnergy_succ_double_sum)
open ArkLib.ProximityGap.CharPDeepMomentTail (rEnergy_one)
open ArkLib.ProximityGap.DCEnergyCorrection (DCEnergyBound)

/-! ## §1. Degree-2 confluent graded shift-Stepanov engine -/

/-- Pure shift generator `X^e * (X - a)^i` (no finite pole factor). -/
noncomputable def shiftTerm {F : Type*} [Field F] (a : F) (e i : ℕ) : F[X] :=
  X ^ e * (X - C a) ^ i

/-- Shift-Stepanov auxiliary polynomial with `B` target blocks and `m` sparse `X`-exponents. -/
noncomputable def shiftAux {F : Type*} [Field F] {m B : ℕ} (a : F) (n : ℕ)
    (e : Fin m → ℕ) (w : Fin B → Fin m → F) : F[X] :=
  ∑ c : Fin B, ∑ j : Fin m, C (w c j) * shiftTerm a (e j) (n * c.val)

/-- Nonvanishing of `shiftAux` for any nonzero weight table `w ≠ 0`, proved via disjoint `(X - a)`
valuation blocks (`eq_zero_of_sum_pow_block`) and confluent sparse multiplicity
(`rootMultiplicity_sparse_lt`). -/
theorem shiftAux_ne_zero {F : Type*} [Field F] {m B n : ℕ} {a : F} (ha : a ≠ 0)
    {e : Fin m → ℕ} (hV : (Matrix.vandermonde (fun j => (e j : F))).det ≠ 0) (hm : m ≤ n)
    {w : Fin B → Fin m → F} (hw : w ≠ 0) :
    shiftAux a n e w ≠ 0 := by
  classical
  intro hz
  let block (c : Fin B) : F[X] := ∑ j : Fin m, C (w c j) * X ^ e j
  have hsum : ∑ c : Fin B, (X - C a) ^ (n * c.val) * block c = 0 := by
    calc ∑ c : Fin B, (X - C a) ^ (n * c.val) * block c
        = shiftAux a n e w := by
          unfold shiftAux
          refine Finset.sum_congr rfl (fun c _ => ?_)
          simp only [block, Finset.mul_sum, shiftTerm]
          exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = 0 := hz
  have heinj : Function.Injective e := fun j k h =>
    (Matrix.det_vandermonde_ne_zero_iff.mp hV) (congrArg (fun t : ℕ => (t : F)) h)
  have hblocks : ∀ c : Fin B, block c = 0 :=
    eq_zero_of_sum_pow_block a n block
      (fun c hc => lt_of_lt_of_le (rootMultiplicity_sparse_lt e (w c) a ha hV hc) hm) hsum
  apply hw
  funext c j
  exact congrFun (eq_zero_of_sum_monomial_eq_zero heinj (hblocks c)) j

/-- Degree-2 clearing multiplier `X * (X - a)`. -/
noncomputable def shiftClearing {F : Type*} [Field F] (a : F) : F[X] :=
  X * (X - C a)

/-- Degree-1 cleared logarithmic derivative factor `e * (X - a) + i * X`. -/
noncomputable def shiftLogFactor {F : Type*} [Field F] (a : F) (e i : ℕ) : F[X] :=
  C (e : F) * (X - C a) + C (i : F) * X

private theorem self_mul_deriv_pow {F : Type*} [Field F] (f : F[X]) (e : ℕ) :
    f * (f ^ e).derivative = C (e : F) * f.derivative * f ^ e := by
  cases e with
  | zero => simp
  | succ e =>
    rw [derivative_pow, Nat.add_sub_cancel, pow_succ, Nat.cast_add, Nat.cast_one]
    ring

private theorem weighted_shiftTerm {F : Type*} [Field F] (a : F) (e i : ℕ) :
    weighted (shiftClearing a) (shiftTerm a e i) =
      shiftLogFactor a e i * shiftTerm a e i := by
  simp only [weighted, shiftClearing, shiftTerm, shiftLogFactor, derivative_mul]
  have h1 := self_mul_deriv_pow (X : F[X]) e
  have h2 := self_mul_deriv_pow (X - C a) i
  simp only [derivative_X, derivative_sub, derivative_C, sub_zero, mul_one] at h1 h2
  set d1 := ((X : F[X]) ^ e).derivative
  set d2 := ((X - C a) ^ i).derivative
  linear_combination (X - C a) * (X - C a) ^ i * h1 + X * X ^ e * h2

/-- Residual polynomial multiplier after `r` cleared derivatives `weighted (shiftClearing a)`. -/
noncomputable def shiftResidual {F : Type*} [Field F] (a : F) (e i : ℕ) : ℕ → F[X]
  | 0 => 1
  | r + 1 => weighted (shiftClearing a) (shiftResidual a e i r) +
      shiftLogFactor a e i * shiftResidual a e i r

private theorem iterate_shiftTerm {F : Type*} [Field F] (a : F) (e i r : ℕ) :
    ((weighted (shiftClearing a))^[r]) (shiftTerm a e i) =
      shiftTerm a e i * shiftResidual a e i r := by
  induction r with
  | zero => simp [shiftResidual]
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, shiftResidual]
    set g := shiftTerm a e i
    set h := shiftResidual a e i r
    set W := shiftClearing a
    change W * (g * h).derivative = g * (W * h.derivative + shiftLogFactor a e i * h)
    rw [derivative_mul]
    calc W * (g.derivative * h + g * h.derivative)
        = (W * g.derivative) * h + g * (W * h.derivative) := by ring
      _ = g * (W * h.derivative + shiftLogFactor a e i * h) := by
          rw [show W * g.derivative = shiftLogFactor a e i * g from weighted_shiftTerm a e i]
          ring

private theorem deg_shiftClearing {F : Type*} [Field F] (a : F) :
    (shiftClearing a).natDegree ≤ 2 := by
  unfold shiftClearing
  calc (X * (X - C a) : F[X]).natDegree
      ≤ (X : F[X]).natDegree + (X - C a).natDegree := natDegree_mul_le
    _ = 2 := by rw [natDegree_X, natDegree_X_sub_C]

private theorem deg_shiftLogFactor {F : Type*} [Field F] (a : F) (e i : ℕ) :
    (shiftLogFactor a e i).natDegree ≤ 1 := by
  unfold shiftLogFactor
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · exact (natDegree_C_mul_le _ _).trans (le_of_eq (natDegree_X_sub_C a))
  · exact (natDegree_C_mul_le _ _).trans (le_of_eq natDegree_X)

/-- Each cleared derivative increases the residual degree by at most `1` (half the `2r` growth of
fractional-linear Möbius auxiliaries). -/
theorem deg_shiftResidual {F : Type*} [Field F] (a : F) (e i r : ℕ) :
    (shiftResidual a e i r).natDegree ≤ r := by
  induction r with
  | zero => simp [shiftResidual]
  | succ r ih =>
    rw [shiftResidual]
    set H := shiftResidual a e i r
    have hH : H.natDegree ≤ r := ih
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · by_cases hh : H.derivative = 0
      · change (shiftClearing a * H.derivative).natDegree ≤ r + 1
        simp [hh]
      · have hp : 0 < H.natDegree := by
          by_contra hz
          push Not at hz
          exact hh (derivative_of_natDegree_zero (Nat.eq_zero_of_le_zero hz))
        have hd := natDegree_derivative_le H
        have hmul : (shiftClearing a * H.derivative).natDegree ≤
            (shiftClearing a).natDegree + H.derivative.natDegree := natDegree_mul_le
        have hW := deg_shiftClearing a
        change (shiftClearing a * H.derivative).natDegree ≤ r + 1
        omega
    · have hmul : (shiftLogFactor a e i * H).natDegree ≤
          (shiftLogFactor a e i).natDegree + H.natDegree := natDegree_mul_le
      have hL := deg_shiftLogFactor a e i
      omega

/-- Reduced polynomial forced to vanish at derivative order `r` on a coset `x^(e j) = u j * x^(d j)`
with shifted power `(x - a)^n = K`. -/
noncomputable def shiftConstraint {F : Type*} [Field F] {m B : ℕ}
    (a K : F) (n : ℕ) (e d : Fin m → ℕ) (u : Fin m → F)
    (w : Fin B → Fin m → F) (r : ℕ) : F[X] :=
  ∑ c : Fin B, ∑ j : Fin m,
    C (w c j * u j * K ^ c.val) * X ^ d j * shiftResidual a (e j) (n * c.val) r

private theorem shiftConstraint_degree {F : Type*} [Field F] {m B : ℕ}
    (a K : F) (n : ℕ) (e d : Fin m → ℕ) (u : Fin m → F)
    (w : Fin B → Fin m → F) {A : ℕ} (hd : ∀ j, d j ≤ A) (r : ℕ) :
    (shiftConstraint a K n e d u w r).natDegree ≤ A + r := by
  refine natDegree_sum_le_of_forall_le _ _ (fun c _ => ?_)
  refine natDegree_sum_le_of_forall_le _ _ (fun j _ => ?_)
  refine natDegree_mul_le.trans (Nat.add_le_add ?_ (deg_shiftResidual a (e j) (n * c.val) r))
  refine natDegree_mul_le.trans ?_
  simpa only [natDegree_C, natDegree_X_pow, zero_add] using hd j

/-- Triangular graded index type of order `< D` and degree `< A + r`, of size `D A + D(D - 1)/2`. -/
abbrev GradedShiftCoeffs (A D : ℕ) := (r : Fin D) × Fin (A + r.val)

private theorem gradedShift_card_mul_two (A D : ℕ) :
    2 * Fintype.card (GradedShiftCoeffs A D) = D * (2 * A + (D - 1)) := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun r => A + r), Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm 2 (∑ x ∈ Finset.range D, x),
    Finset.sum_range_id_mul_two]
  ring

private noncomputable def gradedShiftMap {F : Type*} [Field F] {m B : ℕ}
    (a K : F) (n : ℕ) (e d : Fin m → ℕ) (u : Fin m → F) (A D : ℕ) :
    (Fin B → Fin m → F) →ₗ[F] (GradedShiftCoeffs A D → F) where
  toFun w l := (shiftConstraint a K n e d u w l.1.val).coeff l.2.val
  map_add' x y := by
    funext l
    simp [shiftConstraint, add_mul, Finset.sum_add_distrib]
  map_smul' v x := by
    funext l
    simp [shiftConstraint, mul_assoc, Finset.mul_sum]

private theorem exists_shift_joint_kernel {F : Type*} [Field F] {m B J : ℕ}
    (a : F) (K : Fin J → F) (n : ℕ) (e d : Fin m → ℕ) (u : Fin m → F)
    (A D : ℕ) (hgap : J * (D * (2 * A + (D - 1))) < 2 * (B * m)) :
    ∃ w : Fin B → Fin m → F, w ≠ 0 ∧
      ∀ i : Fin J, gradedShiftMap a (K i) n e d u A D w = 0 := by
  classical
  let L := LinearMap.pi (fun i : Fin J => gradedShiftMap (B := B) a (K i) n e d u A D)
  have hdim : Module.finrank F (Fin J → GradedShiftCoeffs A D → F) <
      Module.finrank F (Fin B → Fin m → F) := by
    rw [Module.finrank_pi_fintype F,
      Module.finrank_pi_fintype F (M := fun _ : Fin B => Fin m → F)]
    simp only [Module.finrank_pi, Fintype.card_fin, Finset.sum_const, Finset.card_univ,
      smul_eq_mul]
    have h2 := gradedShift_card_mul_two A D
    have hJ2 : 2 * (J * Fintype.card (GradedShiftCoeffs A D)) =
        J * (D * (2 * A + (D - 1))) := by
      rw [show 2 * (J * Fintype.card (GradedShiftCoeffs A D)) =
        J * (2 * Fintype.card (GradedShiftCoeffs A D)) by ring, h2]
    omega
  have hn : ¬Function.Injective L := fun hi =>
    (not_le_of_gt hdim) (LinearMap.finrank_le_finrank_of_injective hi)
  rw [← LinearMap.ker_eq_bot] at hn
  obtain ⟨w, hw, hne⟩ := (Submodule.ne_bot_iff _).mp hn
  exact ⟨w, hne, fun i => congrFun (LinearMap.mem_ker.mp hw) i⟩

private theorem shiftConstraint_zero_of_kernel {F : Type*} [Field F] {m B : ℕ}
    (a K : F) (n : ℕ) (e d : Fin m → ℕ) (u : Fin m → F)
    {A D : ℕ} (hA : 0 < A) (hd : ∀ j, d j < A) {w : Fin B → Fin m → F}
    (hk : gradedShiftMap a K n e d u A D w = 0) {r : ℕ} (hr : r < D) :
    shiftConstraint a K n e d u w r = 0 := by
  ext t
  rw [coeff_zero]
  by_cases ht : t < A + r
  · exact congrFun hk ⟨⟨r, hr⟩, ⟨t, ht⟩⟩
  · apply coeff_eq_zero_of_natDegree_lt
    have h := shiftConstraint_degree a K n e d u w (A := A - 1)
      (fun j => by have := hd j; omega) r
    omega

private theorem weighted_sum_local {F : Type*} [Field F] {I : Type*}
    (W : F[X]) (s : Finset I) (f : I → F[X]) (r : ℕ) :
    ((weighted W)^[r]) (∑ i ∈ s, f i) = ∑ i ∈ s, ((weighted W)^[r]) (f i) := by
  induction r with
  | zero => simp
  | succ r ih => simp [Function.iterate_succ_apply', ih, weighted, Finset.mul_sum]

private theorem weighted_const_local {F : Type*} [Field F]
    (W f : F[X]) (v : F) (r : ℕ) :
    ((weighted W)^[r]) (C v * f) = C v * ((weighted W)^[r]) f := by
  induction r with
  | zero => simp
  | succ r ih =>
    simp only [Function.iterate_succ_apply', ih, weighted, derivative_C_mul]
    ring

private theorem eval_weighted_shiftAux {F : Type*} [Field F] {m B : ℕ}
    (a K : F) (n : ℕ) (e d : Fin m → ℕ) (u : Fin m → F)
    (w : Fin B → Fin m → F) (r : ℕ) (x : F)
    (hxe : ∀ j, x ^ e j = u j * x ^ d j)
    (hxshift : (x - a) ^ n = K) :
    (((weighted (shiftClearing a))^[r]) (shiftAux a n e w)).eval x =
      (shiftConstraint a K n e d u w r).eval x := by
  classical
  simp only [shiftAux, shiftConstraint, weighted_sum_local, weighted_const_local,
    iterate_shiftTerm, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun j _ => ?_))
  simp only [shiftTerm, eval_mul, eval_pow, eval_sub, eval_X, eval_C, pow_mul, hxshift, hxe]
  ring

private theorem shiftAux_degree {F : Type*} [Field F] {m B : ℕ}
    (a : F) (n : ℕ) (e : Fin m → ℕ) (w : Fin B → Fin m → F)
    {E : ℕ} (hE : ∀ j, e j ≤ E) :
    (shiftAux a n e w).natDegree ≤ E + n * (B - 1) := by
  refine natDegree_sum_le_of_forall_le _ _ (fun c _ => ?_)
  refine natDegree_sum_le_of_forall_le _ _ (fun j _ => ?_)
  refine natDegree_mul_le.trans ?_
  rw [natDegree_C, zero_add]
  unfold shiftTerm
  refine natDegree_mul_le.trans ?_
  have hc : c.val ≤ B - 1 := by have := c.isLt; omega
  have h1 : ((X : F[X]) ^ e j).natDegree ≤ E := by
    simpa only [natDegree_X_pow] using hE j
  have h2 : ((X - C a) ^ (n * c.val)).natDegree ≤ n * (B - 1) := by
    rw [(monic_X_sub_C a).natDegree_pow, natDegree_X_sub_C, mul_one]
    exact Nat.mul_le_mul_left n hc
  exact Nat.add_le_add h1 h2

/-- **Degree-2 Confluent Graded Shift-Stepanov Bound.**
Bounds the number of regular points `x ∈ S` (`x ≠ 0, x ≠ a`) on any `u`-coset
(`x^(e j) = u j * x^(d j)`) whose shifted `n`-th power `(x - a)^n` lands in a `J`-element target
set `{K 0, ..., K (J - 1)}`. -/
theorem shift_stepanov_count_many_graded {F : Type*} [Field F] {m B n A D E J : ℕ}
    {a : F} (K : Fin J → F) (u : Fin m → F) (ha : a ≠ 0)
    {e d : Fin m → ℕ} (hV : (Matrix.vandermonde (fun j => (e j : F))).det ≠ 0)
    (hm : m ≤ n) (hE : ∀ j, e j ≤ E) (hA : 0 < A) (hd : ∀ j, d j < A)
    (hgap : J * (D * (2 * A + (D - 1))) < 2 * (B * m))
    (hfac : IsUnit (((D - 1).factorial : ℕ) : F))
    (S : Finset F) (hreg : ∀ x ∈ S, x ≠ 0 ∧ x ≠ a)
    (hxe : ∀ x ∈ S, ∀ j, x ^ e j = u j * x ^ d j)
    (hshift : ∀ x ∈ S, ∃ i : Fin J, (x - a) ^ n = K i) :
    D * S.card ≤ E + n * (B - 1) := by
  classical
  obtain ⟨w, hw, hk⟩ := exists_shift_joint_kernel a K n e d u A D hgap
  set P := shiftAux a n e w
  have hP : P ≠ 0 := shiftAux_ne_zero ha hV hm hw
  have hmult : ∀ x ∈ S, D ≤ P.rootMultiplicity x := by
    intro x hx
    obtain ⟨hx0, hxa⟩ := hreg x hx
    obtain ⟨i, hi⟩ := hshift x hx
    have hW : (shiftClearing a).eval x ≠ 0 := by
      simp [shiftClearing, hx0, sub_ne_zero.mpr hxa]
    apply le_rootMultiplicity_of_weighted_vanishing (shiftClearing a) hP hW hfac
    intro r hr
    rw [show P = shiftAux a n e w from rfl,
      eval_weighted_shiftAux a (K i) n e d u w r x (hxe x hx) hi,
      shiftConstraint_zero_of_kernel a (K i) n e d u hA hd (hk i) hr, eval_zero]
  calc D * S.card
      = ∑ _x ∈ S, D := by simp [Nat.mul_comm]
    _ ≤ ∑ x ∈ S, P.roots.count x := by
        refine Finset.sum_le_sum (fun x hx => ?_)
        rw [count_roots]
        exact hmult x hx
    _ = ∑ x ∈ S ∩ P.roots.toFinset, P.roots.count x := by
        refine (Finset.sum_subset Finset.inter_subset_left (fun x hx hx' => ?_)).symm
        exact Multiset.count_eq_zero.mpr
          (fun hm' => hx' (Finset.mem_inter.mpr ⟨hx, Multiset.mem_toFinset.mpr hm'⟩))
    _ ≤ ∑ x ∈ P.roots.toFinset, P.roots.count x :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun _ _ _ => Nat.zero_le _)
    _ = Multiset.card P.roots := P.roots.toFinset_sum_count_eq
    _ ≤ P.natDegree := P.card_roots'
    _ ≤ E + n * (B - 1) := shiftAux_degree a n e w hE

/-- **Rectangular asymmetric coset-shift bound** for `x^N = c₀` and
`(x - a)^M ∈ {K_0, ..., K_{J-1}}` over any field of prime characteristic `p`. -/
theorem coset_shift_rectangular_many {F : Type*} [Field F] {p N M A B C D J : ℕ} [CharP F p]
    (hp : p.Prime) (hA : 0 < A) (hC : 0 < C) (hAN : A ≤ N) (hsize : A * C ≤ M)
    (hchar : A - 1 + N * (C - 1) < p) (hD : D ≤ p)
    (hgap : J * (D * (2 * A + (D - 1))) < 2 * (B * (A * C)))
    {a c₀ : F} (K : Fin J → F) (ha : a ≠ 0)
    (S : Finset F) (hreg : ∀ x ∈ S, x ≠ 0 ∧ x ≠ a)
    (hpow : ∀ x ∈ S, x ^ N = c₀)
    (hshift : ∀ x ∈ S, ∃ i : Fin J, (x - a) ^ M = K i) :
    D * S.card ≤ A - 1 + N * (C - 1) + M * (B - 1) := by
  let d (j : Fin (A * C)) : ℕ := j.val % A
  let e (j : Fin (A * C)) : ℕ := d j + N * (j.val / A)
  let u (j : Fin (A * C)) : F := c₀ ^ (j.val / A)
  have hd (j : Fin (A * C)) : d j < A := Nat.mod_lt _ hA
  have he (j : Fin (A * C)) : e j ≤ A - 1 + N * (C - 1) := by
    have hq : j.val / A < C := (Nat.div_lt_iff_lt_mul hA).mpr (by simp [Nat.mul_comm])
    exact Nat.add_le_add (by have := hd j; omega) (Nat.mul_le_mul_left _ (by omega))
  have hinj : Function.Injective e := by
    intro i j h
    have hm := congrArg (· % N) h
    simp only [e, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt ((hd _).trans_le hAN)] at hm
    have hout : N * (i.val / A) = N * (j.val / A) :=
      Nat.add_left_cancel (show d i + N * (i.val / A) = d i + N * (j.val / A) by
        simpa [e, hm] using h)
    have hq := Nat.eq_of_mul_eq_mul_left (hA.trans_le hAN) hout
    apply Fin.ext
    calc i.val = d i + A * (i.val / A) := (Nat.mod_add_div i.val A).symm
      _ = d j + A * (j.val / A) := by rw [hm, hq]
      _ = j.val := Nat.mod_add_div j.val A
  have hv : (Matrix.vandermonde (fun j => (e j : F))).det ≠ 0 := by
    rw [Matrix.det_vandermonde_ne_zero_iff]
    intro i j hij
    exact hinj (CharP.natCast_injOn_Iio F p ((he i).trans_lt hchar) ((he j).trans_lt hchar) hij)
  have hf : IsUnit (((D - 1).factorial : ℕ) : F) := by
    rw [isUnit_iff_ne_zero, ne_eq, CharP.cast_eq_zero_iff F p]
    intro hh
    have := (Nat.Prime.dvd_factorial hp).mp hh
    have := hp.pos
    omega
  refine shift_stepanov_count_many_graded K u ha hv hsize he hA hd hgap hf S hreg ?_ hshift
  intro x hx j
  dsimp only [e, u]
  rw [pow_add, pow_mul, hpow x hx, mul_comm]

/-- **Unconditional `2,495,902 < 2^22` (`≈ 2.3803 * n^(2/3)`) coset-shift bound at `n = 2^30`.**
Improves `MobiusSubgroupBound.production_graph_graded` (`3,143,679`) by `647,777` points (`20.6%`)
for all coset shifts `x^(2^30) = c₀ ∧ (x - a)^(2^30) = K` (`c₀ ≠ 0, K ≠ 0, a ≠ 0`) over every field
of prime characteristic `p > 2^41` (including both designated primes `P₁` and `P₂`). -/
theorem production_coset_shift_count {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {p : ℕ} [CharP F p] (hp : p.Prime) (hbig : 2 ^ 41 < p)
    {a c₀ K : F} (ha : a ≠ 0) (hc₀ : c₀ ≠ 0) (hK : K ≠ 0) :
    (Finset.univ.filter (fun x : F =>
      x ^ (2 ^ 30 : ℕ) = c₀ ∧ (x - a) ^ (2 ^ 30 : ℕ) = K)).card ≤ 2495902 := by
  set S := Finset.univ.filter (fun x : F =>
    x ^ (2 ^ 30 : ℕ) = c₀ ∧ (x - a) ^ (2 ^ 30 : ℕ) = K)
  have hreg : ∀ x ∈ S, x ≠ 0 ∧ x ≠ a := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := (Finset.mem_filter.mp hx).2
    refine ⟨?_, ?_⟩
    · rintro rfl
      rw [zero_pow (by decide : (2 ^ 30 : ℕ) ≠ 0)] at hx1
      exact hc₀ hx1.symm
    · rintro rfl
      rw [sub_self, zero_pow (by decide : (2 ^ 30 : ℕ) ≠ 0)] at hx2
      exact hK hx2.symm
  have h := coset_shift_rectangular_many (N := 2 ^ 30) (M := 2 ^ 30)
    (A := 838860) (B := 2490) (C := 1280) (D := 1621001) (J := 1)
    hp (by decide) (by decide) (by decide) (by decide) (by omega) (by omega) (by decide)
    (fun _ => K) ha S hreg
    (fun x hx => (Finset.mem_filter.mp hx).2.1)
    (fun x hx => ⟨0, (Finset.mem_filter.mp hx).2.2⟩)
  omega

/-- **Unconditional `4`-coset simultaneous shift cap (`≤ 6,291,183 < 6 * n^(2/3)`) at `n = 2^30`.**
Bounds `x^(2^30) = c₀ ∧ (x - a)^(2^30) ∈ {K 0, K 1, K 2, K 3}` (e.g. an entire `μ_{2^32}`-coset)
simultaneously for all `p > 2^41`. -/
theorem production_fourCoset_shift_count {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {p : ℕ} [CharP F p] (hp : p.Prime) (hbig : 2 ^ 41 < p)
    {a c₀ : F} (K : Fin 4 → F) (ha : a ≠ 0) (hc₀ : c₀ ≠ 0) (hK : ∀ i, K i ≠ 0) :
    (Finset.univ.filter (fun x : F =>
      x ^ (2 ^ 30 : ℕ) = c₀ ∧ ∃ i : Fin 4, (x - a) ^ (2 ^ 30 : ℕ) = K i)).card ≤ 6291183 := by
  set S := Finset.univ.filter (fun x : F =>
    x ^ (2 ^ 30 : ℕ) = c₀ ∧ ∃ i : Fin 4, (x - a) ^ (2 ^ 30 : ℕ) = K i)
  have hreg : ∀ x ∈ S, x ≠ 0 ∧ x ≠ a := by
    intro x hx
    obtain ⟨hx1, ⟨i, hx2⟩⟩ := (Finset.mem_filter.mp hx).2
    refine ⟨?_, ?_⟩
    · rintro rfl
      rw [zero_pow (by decide : (2 ^ 30 : ℕ) ≠ 0)] at hx1
      exact hc₀ hx1.symm
    · rintro rfl
      rw [sub_self, zero_pow (by decide : (2 ^ 30 : ℕ) ≠ 0)] at hx2
      exact hK i hx2.symm
  have h := coset_shift_rectangular_many (N := 2 ^ 30) (M := 2 ^ 30)
    (A := 542293) (B := 4060) (C := 1980) (D := 1030530) (J := 4)
    hp (by decide) (by decide) (by decide) (by decide) (by omega) (by omega) (by decide)
    K ha S hreg
    (fun x hx => (Finset.mem_filter.mp hx).2.1)
    (fun x hx => (Finset.mem_filter.mp hx).2.2)
  omega

/-! ## §2. Exact difference-autocorrelation moment step, `O(n^{2r - 4/3})` moment ladder,
and cross-coset non-antipodal sextuple bounds -/

/-- Ordered additive representation count `repCount G t = #{x ∈ G : t - x ∈ G}`. -/
def repCount {F : Type*} [Sub F] [DecidableEq F] (G : Finset F) (t : F) : ℕ :=
  (G.filter (fun x => t - x ∈ G)).card

/-- Ordered difference count `diffCount G δ = #{x ∈ G : x - δ ∈ G}`. -/
def diffCount {F : Type*} [Sub F] [DecidableEq F] (G : Finset F) (δ : F) : ℕ :=
  (G.filter (fun x => x - δ ∈ G)).card

theorem diffCount_eq_repCount_of_neg_closed {F : Type*} [CommRing F] [DecidableEq F]
    {G : Finset F} (hneg : ∀ x ∈ G, -x ∈ G) (δ : F) :
    diffCount G δ = repCount G δ := by
  unfold diffCount repCount
  congr 1
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hx, hxd⟩
    refine ⟨hx, ?_⟩
    have := hneg (x - δ) hxd
    rwa [neg_sub] at this
  · rintro ⟨hx, hdx⟩
    refine ⟨hx, ?_⟩
    have := hneg (δ - x) hdx
    rwa [neg_sub] at this

private theorem diffCount_eq_double_sum {F : Type*} [CommRing F] [DecidableEq F]
    (G : Finset F) (δ : F) :
    diffCount G δ = ∑ s ∈ G, ∑ t ∈ G, if s - t = δ then 1 else 0 := by
  unfold diffCount
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  by_cases hm : s - δ ∈ G
  · simp only [hm, ↓reduceIte]
    rw [Finset.sum_eq_single (s - δ)]
    · simp
    · intro t _ hne
      have hne' : s - t ≠ δ := fun h => hne (by linear_combination -h)
      simp only [hne', ↓reduceIte]
    · intro hnot
      exact absurd hm hnot
  · simp only [hm, ↓reduceIte]
    symm
    refine Finset.sum_eq_zero (fun t ht => ?_)
    have hne' : s - t ≠ δ := by
      intro h
      have hst : s - δ = t := by linear_combination h
      exact hm (hst ▸ ht)
    simp only [hne', ↓reduceIte]

private theorem diffCount_zero {F : Type*} [CommRing F] [DecidableEq F] (G : Finset F) :
    diffCount G 0 = G.card := by
  unfold diffCount
  simp

/-- **Exact total mass of `r`-fold autocorrelations: `∑_δ autocorr G r δ = |G|^(2r)`.** -/
theorem sum_autocorr_eq {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (G : Finset F) (r : ℕ) :
    ∑ δ : F, autocorr G r δ = G.card ^ (2 * r) := by
  unfold autocorr
  rw [Finset.sum_comm]
  have hshift : ∀ e : F, ∑ δ : F, freq G r e * freq G r (e + δ) =
      freq G r e * G.card ^ r := by
    intro e
    rw [← Finset.mul_sum]
    have hbij : ∑ δ : F, freq G r (e + δ) = ∑ d : F, freq G r d :=
      Fintype.sum_equiv (Equiv.addLeft e) _ _ (fun _ => rfl)
    rw [hbij, sum_freq]
  rw [Finset.sum_congr rfl (fun e _ => hshift e), ← Finset.sum_mul, sum_freq, ← pow_add, two_mul]

/-- **Exact punctured autocorrelation mass:
`∑_{δ ≠ 0} autocorr G r δ = |G|^(2r) - rEnergy G r`.** -/
theorem sum_erase_zero_autocorr_eq {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (G : Finset F) (r : ℕ) :
    ∑ δ ∈ (Finset.univ : Finset F).erase 0, autocorr G r δ =
      G.card ^ (2 * r) - rEnergy G r := by
  have hsplit := (Finset.add_sum_erase (Finset.univ : Finset F)
    (fun δ => autocorr G r δ) (Finset.mem_univ 0)).symm
  rw [sum_autocorr_eq, autocorr_zero] at hsplit
  omega

/-- **Exact difference-autocorrelation moment identity:**
`rEnergy G (r + 1) = |G| * rEnergy G r + ∑_{δ ≠ 0} diffCount G δ * autocorr G r δ`. -/
theorem rEnergy_succ_eq_diffCount_autocorr {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (G : Finset F) (r : ℕ) :
    rEnergy G (r + 1) = G.card * rEnergy G r +
      ∑ δ ∈ (Finset.univ : Finset F).erase 0, diffCount G δ * autocorr G r δ := by
  have hfull : rEnergy G (r + 1) = ∑ δ : F, diffCount G δ * autocorr G r δ := by
    rw [rEnergy_succ_double_sum]
    have hexp : ∀ s ∈ G, ∀ t ∈ G, autocorr G r (s - t) =
        ∑ δ : F, (if s - t = δ then 1 else 0) * autocorr G r δ := by
      intro s _ t _
      rw [Finset.sum_eq_single (s - t)]
      · simp
      · intro δ _ hne
        simp only [Ne.symm hne, ↓reduceIte, zero_mul]
      · intro hnot
        exact absurd (Finset.mem_univ _) hnot
    calc ∑ s ∈ G, ∑ t ∈ G, autocorr G r (s - t)
        = ∑ s ∈ G, ∑ t ∈ G, ∑ δ : F, (if s - t = δ then 1 else 0) * autocorr G r δ :=
          Finset.sum_congr rfl (fun s hs => Finset.sum_congr rfl (fun t ht => hexp s hs t ht))
      _ = ∑ s ∈ G, ∑ δ : F, ∑ t ∈ G, (if s - t = δ then 1 else 0) * autocorr G r δ :=
          Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
      _ = ∑ δ : F, ∑ s ∈ G, ∑ t ∈ G, (if s - t = δ then 1 else 0) * autocorr G r δ :=
          Finset.sum_comm
      _ = ∑ δ : F, diffCount G δ * autocorr G r δ := by
          refine Finset.sum_congr rfl (fun δ _ => ?_)
          rw [diffCount_eq_double_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl (fun _ _ => (Finset.sum_mul _ _ _).symm)
  rw [hfull, ← Finset.add_sum_erase (Finset.univ : Finset F)
    (fun δ => diffCount G δ * autocorr G r δ) (Finset.mem_univ 0),
    diffCount_zero, autocorr_zero]

/-- **Universal moment-step bound from any nonzero difference cap `M`:**
`rEnergy G (r + 1) ≤ |G| * rEnergy G r + M * (|G|^(2r) - rEnergy G r)`. -/
theorem rEnergy_succ_le_of_diffBound {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (G : Finset F) (r M : ℕ) (hM : ∀ δ : F, δ ≠ 0 → diffCount G δ ≤ M) :
    rEnergy G (r + 1) ≤ G.card * rEnergy G r + M * (G.card ^ (2 * r) - rEnergy G r) := by
  rw [rEnergy_succ_eq_diffCount_autocorr]
  have hsum : ∑ δ ∈ (Finset.univ : Finset F).erase 0, diffCount G δ * autocorr G r δ ≤
      M * ∑ δ ∈ (Finset.univ : Finset F).erase 0, autocorr G r δ := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun δ hδ => ?_)
    exact Nat.mul_le_mul_right _ (hM δ (Finset.mem_erase.mp hδ).1)
  rw [sum_erase_zero_autocorr_eq] at hsum
  exact Nat.add_le_add_left hsum _

/-- **Closed-form `O(n^{2r - 4/3})` higher-moment ladder for all `r ≥ 2`:**
Whenever `∀ δ ≠ 0, diffCount G δ ≤ M` and `M + 1 ≤ |G|`, **every** `r ≥ 2` satisfies
`rEnergy G r ≤ (M + 1) * |G|^(2r - 2)`—improving the generic `|G|^(2r - 1)` ceiling by a full
factor of `|G| / (M + 1)` (`≈ 430×` on `μ_{2^30}`) at every moment rung simultaneously. -/
theorem rEnergy_le_mul_pow_of_diffBound {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (G : Finset F) {M : ℕ} (hM : ∀ δ : F, δ ≠ 0 → diffCount G δ ≤ M)
    (hMn : M + 1 ≤ G.card) {r : ℕ} (hr : 2 ≤ r) :
    rEnergy G r ≤ (M + 1) * G.card ^ (2 * r - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 2 := ⟨r - 2, by omega⟩
  induction k with
  | zero =>
    have hstep := rEnergy_succ_le_of_diffBound G 1 M hM
    rw [rEnergy_one] at hstep
    simp only [show 2 * (0 + 2) - 2 = 2 by rfl, show 2 * 1 = 2 by rfl] at hstep ⊢
    have hle : G.card ^ 2 - G.card ≤ G.card ^ 2 := Nat.sub_le _ _
    calc rEnergy G 2
        ≤ G.card * G.card + M * (G.card ^ 2 - G.card) := hstep
      _ ≤ G.card ^ 2 + M * G.card ^ 2 := by
          rw [← sq]
          exact Nat.add_le_add_left (Nat.mul_le_mul_left M hle) _
      _ = (M + 1) * G.card ^ 2 := by ring
  | succ k ih =>
    have hk2 : 2 ≤ k + 2 := by omega
    have ihk := ih hk2
    have hstep := rEnergy_succ_le_of_diffBound G (k + 2) M hM
    have hsub : G.card ^ (2 * (k + 2)) - rEnergy G (k + 2) ≤ G.card ^ (2 * (k + 2)) :=
      Nat.sub_le _ _
    have hexp1 : 2 * (k + 2) - 2 + 1 = 2 * k + 3 := by omega
    have hexp2 : 2 * (k + 2) = 2 * k + 4 := by omega
    have hexp3 : 2 * (k + 1 + 2) - 2 = 2 * k + 4 := by omega
    rw [hexp3]
    calc rEnergy G (k + 1 + 2)
        ≤ G.card * rEnergy G (k + 2) + M * G.card ^ (2 * (k + 2)) :=
          le_trans hstep (Nat.add_le_add_left (Nat.mul_le_mul_left M hsub) _)
      _ ≤ G.card * ((M + 1) * G.card ^ (2 * (k + 2) - 2)) + M * G.card ^ (2 * k + 4) := by
          rw [hexp2]
          exact Nat.add_le_add_right (Nat.mul_le_mul_left G.card ihk) _
      _ = (M + 1) * G.card ^ (2 * k + 3) + M * G.card ^ (2 * k + 4) := by
          rw [show G.card * ((M + 1) * G.card ^ (2 * (k + 2) - 2)) =
            (M + 1) * (G.card ^ (2 * (k + 2) - 2) * G.card) by ring, ← pow_succ, hexp1]
      _ ≤ G.card * G.card ^ (2 * k + 3) + M * G.card ^ (2 * k + 4) :=
          Nat.add_le_add_right (Nat.mul_le_mul_right _ hMn) _
      _ = (M + 1) * G.card ^ (2 * k + 4) := by
          rw [mul_comm G.card (G.card ^ (2 * k + 3)), ← pow_succ]
          ring

/-- Reconciliation between `SubgroupGaussSumFourthMoment.addEnergy` and `rEnergy G 2`. -/
theorem addEnergy_eq_rEnergy_two {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (G : Finset F) :
    addEnergy G = rEnergy G 2 := by
  have hpi2 : ∀ f : (Fin 2 → F) → ℕ,
      ∑ v ∈ Fintype.piFinset (fun _ : Fin 2 => G), f v =
        ∑ a ∈ G, ∑ b ∈ G, f ![a, b] := by
    intro f
    rw [← Finset.sum_product']
    refine Finset.sum_nbij' (fun v => (v 0, v 1)) (fun p => ![p.1, p.2]) ?_ ?_ ?_ ?_ ?_
    · intro v hv
      have hmem := Fintype.mem_piFinset.mp hv
      exact Finset.mem_product.mpr ⟨hmem 0, hmem 1⟩
    · intro p hp
      rcases Finset.mem_product.mp hp with ⟨hp0, hp1⟩
      exact Fintype.mem_piFinset.mpr (fun i => by fin_cases i <;> assumption)
    · intro v _
      funext i
      fin_cases i <;> rfl
    · intro _ _
      rfl
    · intro v _
      congr 1
      funext i
      fin_cases i <;> rfl
  symm
  unfold rEnergy addEnergy
  rw [hpi2]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun a' _ => ?_))
  rw [hpi2]
  refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun c' _ => ?_))
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **Unconditional Garcia–Voloch / HBK representation & difference cap on `μ_{2^30}` (`p > 2^41`),
satisfying `2495902^3 ≤ 64 * |G|^2`.** -/
theorem production_gvRepBound_unconditional {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {p : ℕ} [CharP F p] (hp : p.Prime) (hbig : 2 ^ 41 < p)
    {G : Finset F} (hG : ∀ x, x ∈ G ↔ x ^ (2 ^ 30 : ℕ) = 1) :
    (∀ t : F, t ≠ 0 → diffCount G t ≤ 2495902) ∧
      (∀ t : F, t ≠ 0 → repCount G t ≤ 2495902) ∧
      (G.card = 2 ^ 30 → 2495902 ^ 3 ≤ 64 * G.card ^ 2) := by
  have hneg : ∀ x ∈ G, -x ∈ G := by
    intro x hx
    have heven : Even (2 ^ 30 : ℕ) := by decide
    exact (hG (-x)).mpr ((heven.neg_pow x).trans ((hG x).mp hx))
  have hdiff : ∀ t : F, t ≠ 0 → diffCount G t ≤ 2495902 := by
    intro t ht
    have hsub : G.filter (fun x => x - t ∈ G) ⊆
        Finset.univ.filter (fun x : F =>
          x ^ (2 ^ 30 : ℕ) = 1 ∧ (x - t) ^ (2 ^ 30 : ℕ) = 1) := by
      intro x hx
      obtain ⟨hxG, hxtG⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, (hG x).mp hxG, (hG (x - t)).mp hxtG⟩
    exact le_trans (Finset.card_le_card hsub)
      (production_coset_shift_count hp hbig ht one_ne_zero one_ne_zero)
  refine ⟨hdiff, fun t ht => ?_, fun hcard => by rw [hcard]; decide⟩
  rw [← diffCount_eq_repCount_of_neg_closed hneg t]
  exact hdiff t ht

/-- **Unconditional sub-trivial moment ladder (`r ≥ 2`) on `μ_{2^30}` for all primes `p > 2^41`:**
certifies `rEnergy G r ≤ 2,495,903 * (2^30)^(2r - 2)` and
`∑_b ‖eta ψ G b‖^(2r) ≤ |F| * 2,495,903 * (2^30)^(2r - 2)` (in particular at `r = 2, 3, 4, 7`:
fourth, sixth, eighth, and fourteenth moments). -/
theorem production_moment_ladder_unconditional {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {p : ℕ} [CharP F p] (hp : p.Prime) (hbig : 2 ^ 41 < p)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G : Finset F} (hcard : G.card = 2 ^ 30)
    (hG : ∀ x, x ∈ G ↔ x ^ (2 ^ 30 : ℕ) = 1) {r : ℕ} (hr : 2 ≤ r) :
    rEnergy G r ≤ 2495903 * (2 ^ 30) ^ (2 * r - 2) ∧
      ∑ b : F, ‖eta ψ G b‖ ^ (2 * r) ≤
        (Fintype.card F : ℝ) * (2495903 * (2 ^ 30 : ℝ) ^ (2 * r - 2)) := by
  have hdiff := (production_gvRepBound_unconditional hp hbig hG).1
  have hE := rEnergy_le_mul_pow_of_diffBound G hdiff (by rw [hcard]; decide) hr
  rw [hcard] at hE
  refine ⟨hE, ?_⟩
  rw [subgroup_gaussSum_moment hψ G r]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  exact_mod_cast hE

/-- Ordered zero-sum sextuples `(x₁, x₂, y₁, y₂, z₁, z₂) ∈ C₁² × C₂² × C₃²` with non-antipodal
third pair `z₁ + z₂ ≠ 0` (covering every antipode-free zero-sum sextuple across any three cosets
`C₁, C₂, C₃`, e.g. `μ_8`, `μ_{16}`, or full `μ_{2^30}`). -/
def nonAntipodalCrossSextuples {F : Type*} [CommRing F] [DecidableEq F]
    (C₁ C₂ C₃ : Finset F) : Finset ((F × F) × (F × F) × (F × F)) :=
  ((C₁ ×ˢ C₁) ×ˢ ((C₂ ×ˢ C₂) ×ˢ (C₃ ×ˢ C₃))).filter
    (fun q => q.1.1 + q.1.2 + q.2.1.1 + q.2.1.2 + q.2.2.1 + q.2.2.2 = 0 ∧
      q.2.2.1 + q.2.2.2 ≠ 0)

/-- **General cross-coset non-antipodal zero-sum sextuple bound (`≤ M * |C₁|^2 * |C₂|^2`).**
Applies to arbitrary subsets/sub-cosets `C₁, C₂, C₃ ⊆ G` (beyond `μ_4`, e.g. `μ_8, μ_{16}, ...,
μ_{2^30}`) whenever `∀ t ≠ 0, repCount C₃ t ≤ M`. -/
theorem nonAntipodalCrossSextuples_card_le {F : Type*} [CommRing F] [DecidableEq F]
    (C₁ C₂ C₃ : Finset F) {M : ℕ} (hM : ∀ t : F, t ≠ 0 → repCount C₃ t ≤ M) :
    (nonAntipodalCrossSextuples C₁ C₂ C₃).card ≤ M * C₁.card ^ 2 * C₂.card ^ 2 := by
  set P12 := (C₁ ×ˢ C₁) ×ˢ (C₂ ×ˢ C₂)
  set S6 := nonAntipodalCrossSextuples C₁ C₂ C₃
  have hpart : S6.card =
      ∑ p ∈ P12, (S6.filter (fun q => (q.1, q.2.1) = p)).card :=
    Finset.card_eq_sum_card_fiberwise (fun q hq => by
      obtain ⟨hprod, _⟩ := Finset.mem_filter.mp hq
      obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hprod
      obtain ⟨hq21, _⟩ := Finset.mem_product.mp hq2
      exact Finset.mem_product.mpr ⟨hq1, hq21⟩)
  have hfib : ∀ p ∈ P12, (S6.filter (fun q => (q.1, q.2.1) = p)).card ≤ M := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    set t : F := -(p.1.1 + p.1.2 + p.2.1 + p.2.2)
    by_cases ht0 : t = 0
    · have hempty : S6.filter (fun q => (q.1, q.2.1) = p) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro q hq
        obtain ⟨hqS, hqp⟩ := Finset.mem_filter.mp hq
        obtain ⟨_, hsum, hnz⟩ := Finset.mem_filter.mp hqS
        have hq1 : q.1 = p.1 := congrArg Prod.fst hqp
        have hq21 : q.2.1 = p.2 := congrArg Prod.snd hqp
        rw [hq1, hq21] at hsum
        apply hnz
        dsimp only [t] at ht0
        linear_combination hsum + ht0
      rw [hempty, Finset.card_empty]
      exact Nat.zero_le M
    · have hinj_sub : (S6.filter (fun q => (q.1, q.2.1) = p)).image (fun q => q.2.2.1) ⊆
          C₃.filter (fun z₁ => t - z₁ ∈ C₃) := by
        intro z₁ hz₁
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz₁
        obtain ⟨hqS, hqp⟩ := Finset.mem_filter.mp hq
        obtain ⟨hqprod, hsum, _⟩ := Finset.mem_filter.mp hqS
        obtain ⟨_, hq2⟩ := Finset.mem_product.mp hqprod
        obtain ⟨_, hq22⟩ := Finset.mem_product.mp hq2
        obtain ⟨hz1C, hz2C⟩ := Finset.mem_product.mp hq22
        have hq1 : q.1 = p.1 := congrArg Prod.fst hqp
        have hq21 : q.2.1 = p.2 := congrArg Prod.snd hqp
        rw [hq1, hq21] at hsum
        have hz2_eq : t - q.2.2.1 = q.2.2.2 := by
          dsimp only [t]
          linear_combination -hsum
        exact Finset.mem_filter.mpr ⟨hz1C, hz2_eq ▸ hz2C⟩
      have hinj : Set.InjOn (fun q : (F × F) × (F × F) × (F × F) => q.2.2.1)
          (S6.filter (fun q => (q.1, q.2.1) = p) : Set _) := by
        intro q₁ hq₁ q₂ hq₂ hz1_eq
        change q₁.2.2.1 = q₂.2.2.1 at hz1_eq
        obtain ⟨hq₁S, hq₁p⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq₁)
        obtain ⟨hq₂S, hq₂p⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq₂)
        have hsum₁ := (Finset.mem_filter.mp hq₁S).2.1
        have hsum₂ := (Finset.mem_filter.mp hq₂S).2.1
        have h1 : q₁.1 = q₂.1 := (congrArg Prod.fst hq₁p).trans (congrArg Prod.fst hq₂p).symm
        have h21 : q₁.2.1 = q₂.2.1 :=
          (congrArg Prod.snd hq₁p).trans (congrArg Prod.snd hq₂p).symm
        have hz2_eq : q₁.2.2.2 = q₂.2.2.2 := by
          rw [h1, h21, hz1_eq] at hsum₁
          linear_combination hsum₁ - hsum₂
        exact Prod.ext h1 (Prod.ext h21 (Prod.ext hz1_eq hz2_eq))
      rw [← Finset.card_image_of_injOn hinj]
      exact le_trans (Finset.card_le_card hinj_sub) (hM t ht0)
  calc S6.card
      = ∑ p ∈ P12, (S6.filter (fun q => (q.1, q.2.1) = p)).card := hpart
    _ ≤ ∑ _p ∈ P12, M := Finset.sum_le_sum hfib
    _ = M * C₁.card ^ 2 * C₂.card ^ 2 := by
        rw [Finset.sum_const, smul_eq_mul]
        dsimp only [P12]
        rw [Finset.card_product, Finset.card_product, Finset.card_product]
        ring

/-- **Unconditional production bound on cross-coset non-antipodal zero-sum sextuples
(`≤ min |C₃| 2495902 * |C₁|^2 * |C₂|^2`) for arbitrary sub-cosets `C₁, C₂, C₃ ⊆ μ_{2^30}`.** -/
theorem production_crossCoset_sextuples_le {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {p : ℕ} [CharP F p] (hp : p.Prime) (hbig : 2 ^ 41 < p)
    {G : Finset F} (hG : ∀ x, x ∈ G ↔ x ^ (2 ^ 30 : ℕ) = 1)
    {C₁ C₂ C₃ : Finset F} (hC₃ : C₃ ⊆ G) :
    (nonAntipodalCrossSextuples C₁ C₂ C₃).card ≤
      min C₃.card 2495902 * C₁.card ^ 2 * C₂.card ^ 2 := by
  have hrepG := (production_gvRepBound_unconditional hp hbig hG).2.1
  refine nonAntipodalCrossSextuples_card_le C₁ C₂ C₃ (fun t ht => le_min ?_ ?_)
  · exact Finset.card_filter_le C₃ _
  · have hsub : C₃.filter (fun x => t - x ∈ C₃) ⊆ G.filter (fun x => t - x ∈ G) := by
      intro x hx
      obtain ⟨hxC, htxC⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hC₃ hxC, hC₃ htxC⟩
    exact le_trans (Finset.card_le_card hsub) (hrepG t ht)

/-! ## §3. Unconditional sum-product expansion (`|G + G| > 430 |G|`), `DCEnergyBound` sumset
growth, and real-spectrum law -/

/-- The `r`-fold sumset `Σ^r G = {d ∈ F : freq G r d > 0}`. -/
noncomputable def rFoldSumset {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (G : Finset F) (r : ℕ) : Finset F :=
  Finset.univ.filter (fun d : F => 0 < freq G r d)

/-- **Cauchy–Schwarz `r`-fold sumset–energy bridge (`|G|^(2r) ≤ |Σ^r G| * rEnergy G r`).** -/
theorem sumset_card_mul_rEnergy_ge {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (G : Finset F) (r : ℕ) :
    G.card ^ (2 * r) ≤ (rFoldSumset G r).card * rEnergy G r := by
  set S := rFoldSumset G r
  have hsum_S : ∑ d ∈ S, freq G r d = G.card ^ r := by
    rw [← sum_freq G r]
    refine Finset.sum_subset (Finset.filter_subset _ _) (fun d _ hd => ?_)
    have hle : freq G r d ≤ 0 := by
      by_contra hpos
      push Not at hpos
      exact hd (Finset.mem_filter.mpr ⟨Finset.mem_univ d, hpos⟩)
    exact Nat.eq_zero_of_le_zero hle
  have hsq_S : ∑ d ∈ S, freq G r d ^ 2 ≤ rEnergy G r := by
    rw [rEnergy_eq_sum_freq_sq]
    exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℕ)) (fun d => freq G r d)
  simp only [one_mul, one_pow, Finset.sum_const, smul_eq_mul, mul_one, hsum_S] at hcs
  rw [show G.card ^ (2 * r) = (G.card ^ r) ^ 2 by rw [← pow_mul, mul_comm]]
  exact le_trans hcs (Nat.mul_le_mul_left S.card hsq_S)

/-- **Unconditional quantitative BGK / Garcia–Voloch sum-product expansion on `μ_{2^30}`:**
While the product set `G * G = G` has cardinality `2^30`, the additive sumset `G + G = Σ^2 G`
has cardinality `≥ 461,925,605,526 > 430 * 2^30` (`≥ 0.40 * |G|^(4/3)`) over every prime field
`F` of characteristic `p > 2^41` containing `μ_{2^30}`. -/
theorem production_sumset_expansion_unconditional {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] {p : ℕ} [CharP F p] (hp : p.Prime) (hbig : 2 ^ 41 < p)
    {G : Finset F} (hcard : G.card = 2 ^ 30)
    (hG : ∀ x, x ∈ G ↔ x ^ (2 ^ 30 : ℕ) = 1) :
    461925605526 ≤ (rFoldSumset G 2).card ∧
      430 * G.card < (rFoldSumset G 2).card := by
  have hE2 := rEnergy_le_mul_pow_of_diffBound G
    (production_gvRepBound_unconditional hp hbig hG).1 (by rw [hcard]; decide) (le_refl 2)
  rw [hcard] at hE2
  have hcs := sumset_card_mul_rEnergy_ge G 2
  rw [hcard] at hcs ⊢
  simp only [show 2 * 2 - 2 = 2 by rfl, show 2 * 2 = 4 by rfl] at hE2 hcs
  have hmul : (2 ^ 30) ^ 4 ≤ (rFoldSumset G 2).card * (2495903 * (2 ^ 30) ^ 2) :=
    le_trans hcs (Nat.mul_le_mul_left _ hE2)
  have hdiv : (2 ^ 30) ^ 2 ≤ 2495903 * (rFoldSumset G 2).card := by
    have hpos : 0 < (2 ^ 30) ^ 2 := by decide
    have hmul' : (2 ^ 30) ^ 2 * (2 ^ 30) ^ 2 ≤
        (2 ^ 30) ^ 2 * (2495903 * (rFoldSumset G 2).card) := by
      calc (2 ^ 30) ^ 2 * (2 ^ 30) ^ 2 = (2 ^ 30) ^ 4 := by ring
        _ ≤ (rFoldSumset G 2).card * (2495903 * (2 ^ 30) ^ 2) := hmul
        _ = (2 ^ 30) ^ 2 * (2495903 * (rFoldSumset G 2).card) := by ring
    exact Nat.le_of_mul_le_mul_left hmul' hpos
  exact ⟨by omega, by omega⟩

/-- **Near-maximal `r`-fold sumset growth from `DCEnergyBound G r`:**
Whenever `DCEnergyBound G r` holds and `|G|^r ≤ c * |F|`, the `r`-fold sumset satisfies
`|G|^r ≤ ((2r - 1)!! + c) * |Σ^r G|` (e.g. `c = 1` at `P₁, P₂` for `r = 2, 3, 4, 5`). -/
theorem sumset_card_ge_of_dcEnergyBound {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {G : Finset F} {r c : ℕ} (hdc : DCEnergyBound G r)
    (hsub : G.card ^ r ≤ c * Fintype.card F) :
    G.card ^ r ≤ (Nat.doubleFactorial (2 * r - 1) + c) * (rFoldSumset G r).card := by
  by_cases hG0 : G.card ^ r = 0
  · rw [hG0]
    exact Nat.zero_le _
  · have hGr_pos : (0 : ℝ) < (G.card : ℝ) ^ r := by
      have : 0 < G.card ^ r := Nat.pos_of_ne_zero hG0
      exact_mod_cast this
    have hF_pos : (0 : ℝ) < (Fintype.card F : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
    have hdc' : (Fintype.card F : ℝ) * (rEnergy G r : ℝ) ≤
        (G.card : ℝ) ^ (2 * r) +
          (Fintype.card F : ℝ) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by
      unfold DCEnergyBound at hdc
      linarith
    have hsubR : (G.card : ℝ) ^ r ≤ (c : ℝ) * (Fintype.card F : ℝ) := by exact_mod_cast hsub
    have hpow2r : (G.card : ℝ) ^ (2 * r) ≤
        (Fintype.card F : ℝ) * ((c : ℝ) * (G.card : ℝ) ^ r) := by
      calc (G.card : ℝ) ^ (2 * r)
          = (G.card : ℝ) ^ r * (G.card : ℝ) ^ r := by rw [← pow_add, two_mul]
        _ ≤ ((c : ℝ) * (Fintype.card F : ℝ)) * (G.card : ℝ) ^ r :=
            mul_le_mul_of_nonneg_right hsubR hGr_pos.le
        _ = (Fintype.card F : ℝ) * ((c : ℝ) * (G.card : ℝ) ^ r) := by ring
    have hEr_le : (rEnergy G r : ℝ) ≤
        ((Nat.doubleFactorial (2 * r - 1) : ℝ) + (c : ℝ)) * (G.card : ℝ) ^ r := by
      have hmul : (Fintype.card F : ℝ) * (rEnergy G r : ℝ) ≤
          (Fintype.card F : ℝ) *
            (((Nat.doubleFactorial (2 * r - 1) : ℝ) + (c : ℝ)) * (G.card : ℝ) ^ r) := by
        calc (Fintype.card F : ℝ) * (rEnergy G r : ℝ)
            ≤ (Fintype.card F : ℝ) * ((c : ℝ) * (G.card : ℝ) ^ r) +
                (Fintype.card F : ℝ) *
                  ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by linarith
          _ = (Fintype.card F : ℝ) *
                (((Nat.doubleFactorial (2 * r - 1) : ℝ) + (c : ℝ)) * (G.card : ℝ) ^ r) := by ring
      exact le_of_mul_le_mul_left hmul hF_pos
    have hcsR : ((G.card : ℝ) ^ r) * (G.card : ℝ) ^ r ≤
        ((rFoldSumset G r).card : ℝ) * (rEnergy G r : ℝ) := by
      have hcs := sumset_card_mul_rEnergy_ge G r
      have hcs' : ((G.card ^ (2 * r) : ℕ) : ℝ) ≤
          (((rFoldSumset G r).card * rEnergy G r : ℕ) : ℝ) := by exact_mod_cast hcs
      simpa only [Nat.cast_pow, Nat.cast_mul, ← pow_add, two_mul] using hcs'
    have hfinR : ((G.card : ℝ) ^ r) * (G.card : ℝ) ^ r ≤
        (((Nat.doubleFactorial (2 * r - 1) : ℝ) + (c : ℝ)) *
          ((rFoldSumset G r).card : ℝ)) * (G.card : ℝ) ^ r := by
      calc ((G.card : ℝ) ^ r) * (G.card : ℝ) ^ r
          ≤ ((rFoldSumset G r).card : ℝ) * (rEnergy G r : ℝ) := hcsR
        _ ≤ ((rFoldSumset G r).card : ℝ) *
              (((Nat.doubleFactorial (2 * r - 1) : ℝ) + (c : ℝ)) * (G.card : ℝ) ^ r) :=
            mul_le_mul_of_nonneg_left hEr_le (Nat.cast_nonneg _)
        _ = (((Nat.doubleFactorial (2 * r - 1) : ℝ) + (c : ℝ)) *
              ((rFoldSumset G r).card : ℝ)) * (G.card : ℝ) ^ r := by ring
    have hcancelR := le_of_mul_le_mul_right hfinR hGr_pos
    exact_mod_cast hcancelR

/-- **Exact real-spectrum law for `-1`-closed subsets (including all dyadic subgroups `μ_{2^m}`):**
`starRingEnd ℂ (eta ψ G b) = eta ψ G b` and `(eta ψ G b).im = 0`. -/
theorem eta_eq_star_and_im_zero_of_neg_closed {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (ψ : AddChar F ℂ) {G : Finset F} (hneg : ∀ x ∈ G, -x ∈ G) (b : F) :
    (starRingEnd ℂ) (eta ψ G b) = eta ψ G b ∧ (eta ψ G b).im = 0 := by
  have hchar : 0 < ringChar F := by
    have := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  have hconj : (starRingEnd ℂ) (eta ψ G b) = eta ψ G b := by
    rw [ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta, map_sum]
    have hpt : ∀ x ∈ G, (starRingEnd ℂ) (ψ (b * x)) = ψ (b * (-x)) := by
      intro x _
      rw [AddChar.starComp_apply hchar, AddChar.inv_apply, mul_neg]
    rw [Finset.sum_congr rfl hpt]
    refine Finset.sum_nbij' (fun x => -x) (fun x => -x) (fun x hx => hneg x hx)
      (fun x hx => hneg x hx) (fun _ _ => neg_neg _) (fun _ _ => neg_neg _) (fun _ _ => rfl)
  refine ⟨hconj, ?_⟩
  have him := congrArg Complex.im hconj
  rw [Complex.conj_im] at him
  linarith

/-! ## §4. Unconditional midpoint-resonance cap and exclusion of `1 -> 2` Wick defect at `P₁, P₂` -/

/-- Midpoint resonance count `#{(x, y, z) ∈ G^3 : x + y = 2z} = ∑_{z ∈ G} repCount G (2z)`. -/
def midpointCount {F : Type*} [Ring F] [DecidableEq F] (G : Finset F) : ℕ :=
  ∑ z ∈ G, repCount G (2 * z)

/-- Cleared-denominator ledger for a one-unit first-step Newton defect (`c₁ ≤ 2`, matching
`BGKActualJointPeriodLaw.FirstStepOneUnitDefectLedger`). -/
def FirstStepOneUnitDefect (q n A M : ℤ) : Prop :=
  q * (A + n - 2 * M) - (n * (n - 1)) ^ 2 ≤ 2 * (n - 1) ^ 2 * (q - n)

/-- Unconditional antipodal additive-energy floor `3|G|^2 - 3|G| ≤ rEnergy G 2` for any `-1`-closed
nonzero subset `G` in odd characteristic. -/
theorem rEnergy_two_ge_three_card_sq_sub {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {G : Finset F} (h2 : (2 : F) ≠ 0) (h0 : (0 : F) ∉ G) (hneg : ∀ x ∈ G, -x ∈ G) :
    3 * G.card ^ 2 - 3 * G.card ≤ rEnergy G 2 := by
  by_cases hcard2 : G.card < 2
  · interval_cases G.card <;> simp
  · push Not at hcard2
    rw [← addEnergy_eq_rEnergy_two]
    set Q := ((G ×ˢ G) ×ˢ (G ×ˢ G)).filter (fun q => q.1.1 + q.1.2 = q.2.1 + q.2.2)
    have hQcard : addEnergy G = Q.card := by
      symm
      dsimp only [Q]
      rw [Finset.card_filter, Finset.sum_product, Finset.sum_product]
      unfold addEnergy
      exact Finset.sum_congr rfl (fun _ _ =>
        Finset.sum_congr rfl (fun _ _ => Finset.sum_product _ _ _))
    let T₁ : Finset ((F × F) × (F × F)) :=
      (G ×ˢ G).image (fun p => ((p.1, p.2), (p.1, p.2)))
    let T₂ : Finset ((F × F) × (F × F)) :=
      ((G ×ˢ G).filter (fun p => p.1 ≠ p.2)).image (fun p => ((p.1, p.2), (p.2, p.1)))
    let T₃ : Finset ((F × F) × (F × F)) :=
      ((G ×ˢ G).filter (fun p => p.2 ≠ p.1 ∧ p.2 ≠ -p.1)).image
        (fun p => ((p.1, -p.1), (p.2, -p.2)))
    have hT1_sub : T₁ ⊆ Q := by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp, hp⟩, rfl⟩
    have hT2_sub : T₂ ⊆ Q := by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨hpG, _⟩ := Finset.mem_filter.mp hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hpG
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hpG, Finset.mem_product.mpr ⟨hp2, hp1⟩⟩, add_comm _ _⟩
    have hT3_sub : T₃ ⊆ Q := by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨hpG, _⟩ := Finset.mem_filter.mp hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hpG
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr ⟨hp1, hneg p.1 hp1⟩,
          Finset.mem_product.mpr ⟨hp2, hneg p.2 hp2⟩⟩, ?_⟩
      simp
    have hdisj12 : Disjoint T₁ T₂ := by
      rw [Finset.disjoint_left]
      intro q h1 h2
      obtain ⟨p₁, _, rfl⟩ := Finset.mem_image.mp h1
      obtain ⟨p₂, hp₂, heq⟩ := Finset.mem_image.mp h2
      have hne := (Finset.mem_filter.mp hp₂).2
      have hfst : p₂.1 = p₁.1 := congrArg (fun r => r.1.1) heq
      have hsnd : p₂.2 = p₁.1 := congrArg (fun r => r.2.1) heq
      exact hne (hfst.trans hsnd.symm)
    have hdisj12_3 : Disjoint (T₁ ∪ T₂) T₃ := by
      rw [Finset.disjoint_left]
      intro q h12 h3
      obtain ⟨p₃, hp₃, rfl⟩ := Finset.mem_image.mp h3
      obtain ⟨_, hne1, hne2⟩ := Finset.mem_filter.mp hp₃
      rcases Finset.mem_union.mp h12 with h1 | h2
      · obtain ⟨p₁, _, heq⟩ := Finset.mem_image.mp h1
        have ha : p₁.1 = p₃.1 := congrArg (fun r => r.1.1) heq
        have hb : p₁.1 = p₃.2 := congrArg (fun r => r.2.1) heq
        exact hne1 (hb.symm.trans ha)
      · obtain ⟨p₂, _, heq⟩ := Finset.mem_image.mp h2
        have ha : p₂.2 = -p₃.1 := congrArg (fun r => r.1.2) heq
        have hb : p₂.2 = p₃.2 := congrArg (fun r => r.2.1) heq
        exact hne2 (hb.symm.trans ha)
    have hc1 : T₁.card = G.card ^ 2 := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => Prod.ext
        (congrArg (fun r => r.1.1) h) (congrArg (fun r => r.1.2) h)), Finset.card_product, sq]
    have hc2 : T₂.card = G.card ^ 2 - G.card := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => Prod.ext
        (congrArg (fun r => r.1.1) h) (congrArg (fun r => r.1.2) h))]
      have hdiag : ((G ×ˢ G).filter (fun p => p.1 = p.2)).card = G.card := by
        have himg : (G ×ˢ G).filter (fun p => p.1 = p.2) = G.image (fun x => (x, x)) := by
          ext p
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_image]
          constructor
          · rintro ⟨⟨hx, _⟩, heq⟩
            exact ⟨p.1, hx, Prod.ext rfl heq⟩
          · rintro ⟨x, hx, rfl⟩
            exact ⟨⟨hx, hx⟩, rfl⟩
        rw [himg, Finset.card_image_of_injective G (fun _ _ h => congrArg Prod.fst h)]
      have hcomp := Finset.card_filter_add_card_filter_not
        (fun p : F × F => p.1 = p.2) (s := G ×ˢ G)
      rw [hdiag, Finset.card_product, ← sq] at hcomp
      have hne : ((G ×ˢ G).filter (fun p => p.1 ≠ p.2)).card =
          ((G ×ˢ G).filter (fun p => ¬p.1 = p.2)).card := rfl
      rw [hne]
      omega
    have hc3 : T₃.card = G.card * (G.card - 2) := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => Prod.ext
        (congrArg (fun r => r.1.1) h) (congrArg (fun r => r.2.1) h))]
      have hfib : ((G ×ˢ G).filter (fun p => p.2 ≠ p.1 ∧ p.2 ≠ -p.1)).card =
          ∑ x ∈ G, ((G.erase x).erase (-x)).card := by
        rw [Finset.card_filter, Finset.sum_product]
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [← Finset.card_filter]
        congr 1
        ext y
        simp only [Finset.mem_filter, Finset.mem_erase]
        tauto
      rw [hfib]
      have heach : ∀ x ∈ G, ((G.erase x).erase (-x)).card = G.card - 2 := by
        intro x hx
        have hx0 : x ≠ 0 := fun h => h0 (h ▸ hx)
        have hnx_ne : -x ≠ x := by
          intro h
          apply mul_ne_zero h2 hx0
          linear_combination -h
        have hnx_mem : -x ∈ G.erase x := Finset.mem_erase.mpr ⟨hnx_ne, hneg x hx⟩
        rw [Finset.card_erase_of_mem hnx_mem, Finset.card_erase_of_mem hx]
        omega
      rw [Finset.sum_congr rfl heach, Finset.sum_const, smul_eq_mul]
    have hunion_sub : (T₁ ∪ T₂) ∪ T₃ ⊆ Q :=
      Finset.union_subset (Finset.union_subset hT1_sub hT2_sub) hT3_sub
    have hcard_u : ((T₁ ∪ T₂) ∪ T₃).card = 3 * G.card ^ 2 - 3 * G.card := by
      rw [Finset.card_union_of_disjoint hdisj12_3, Finset.card_union_of_disjoint hdisj12,
        hc1, hc2, hc3]
      obtain ⟨m, hm⟩ : ∃ m, G.card = m + 2 := ⟨G.card - 2, by omega⟩
      rw [hm]
      have hs1 : (m + 2) ^ 2 - (m + 2) = m ^ 2 + 3 * m + 2 := by
        rw [show (m + 2) ^ 2 = (m ^ 2 + 3 * m + 2) + (m + 2) by ring]
        exact Nat.add_sub_cancel _ _
      have hs2 : 3 * (m + 2) ^ 2 - 3 * (m + 2) = 3 * m ^ 2 + 9 * m + 6 := by
        rw [show 3 * (m + 2) ^ 2 = (3 * m ^ 2 + 9 * m + 6) + 3 * (m + 2) by ring]
        exact Nat.add_sub_cancel _ _
      rw [hs1, hs2]
      simp only [Nat.add_sub_cancel]
      ring
    rw [hQcard, ← hcard_u]
    exact Finset.card_le_card hunion_sub

private theorem roots_card_eq_of_orderOf {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {n : ℕ} (hn : 0 < n) {g : F} (hord : orderOf g = n) :
    (Finset.univ.filter (fun x : F => x ^ n = 1)).card = n := by
  set G := Finset.univ.filter (fun x : F => x ^ n = 1)
  have hge : n ≤ G.card := by
    let S := (Finset.range n).image (fun k => g ^ k)
    have hinj : Set.InjOn (fun k : ℕ => g ^ k) (Finset.range n : Set ℕ) := by
      intro i hi j hj heq
      have hi' : i ∈ Set.Iio (orderOf g) := by
        rw [hord]; exact Finset.mem_range.mp (Finset.mem_coe.mp hi)
      have hj' : j ∈ Set.Iio (orderOf g) := by
        rw [hord]; exact Finset.mem_range.mp (Finset.mem_coe.mp hj)
      exact pow_injOn_Iio_orderOf hi' hj' heq
    have hScard : S.card = n := by
      rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    have hSsub : S ⊆ G := by
      intro x hx
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [← pow_mul, mul_comm, pow_mul, ← hord, pow_orderOf_eq_one, one_pow]
    rw [← hScard]
    exact Finset.card_le_card hSsub
  have hle : G.card ≤ n := by
    set P : F[X] := X ^ n - 1
    have hP0 : P ≠ 0 := Polynomial.X_pow_sub_C_ne_zero hn 1
    have hPdeg : P.natDegree = n := Polynomial.natDegree_X_pow_sub_C
    by_contra hgt
    push Not at hgt
    refine hP0 (Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P G ?_ (hPdeg ▸ hgt))
    intro x hx
    simp only [P, eval_sub, eval_pow, eval_X, eval_one, (Finset.mem_filter.mp hx).2, sub_self]
  exact le_antisymm hle hge

local instance : Fact ArkLib.ProximityGap.PrizeShapePrimeP30.P.Prime :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P⟩

local instance : Fact ArkLib.ProximityGap.PrizeShapePrimeP30Second.P.Prime :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P⟩

/-- **First designated prime (`P₁`): unconditional `midpointCount ≤ 2,495,902 * 2^30 < 2^52` and
unconditional refutation of `FirstStepOneUnitDefect`.** Eliminates the `hrep` assumption of
`BGKActualJointPeriodLaw.productionP1_midpointResonance_le_of_nonzeroRepCap`. -/
theorem firstPrime_midpoint_and_no_firstStep_defect :
    let P₁ := ArkLib.ProximityGap.PrizeShapePrimeP30.P
    let G := (Finset.univ : Finset (ZMod P₁)).filter (fun x => x ^ (2 ^ 30 : ℕ) = 1)
    G.card = 2 ^ 30 ∧
      midpointCount G ≤ 2495902 * 2 ^ 30 ∧
      ¬ FirstStepOneUnitDefect P₁ (2 ^ 30) (rEnergy G 2) (midpointCount G) := by
  dsimp only
  set P₁ := ArkLib.ProximityGap.PrizeShapePrimeP30.P
  set G := (Finset.univ : Finset (ZMod P₁)).filter (fun x => x ^ (2 ^ 30 : ℕ) = 1)
  have hcard : G.card = 2 ^ 30 :=
    roots_card_eq_of_orderOf (by decide) ArkLib.ProximityGap.PrizeShapePrimeP30.orderOf_g
  have hG : ∀ x : ZMod P₁, x ∈ G ↔ x ^ (2 ^ 30 : ℕ) = 1 := by
    intro x
    simp [G]
  have hp : P₁.Prime := ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P
  have hbig : 2 ^ 41 < P₁ := by unfold P₁ ArkLib.ProximityGap.PrizeShapePrimeP30.P; decide
  have hrep := (production_gvRepBound_unconditional hp hbig hG).2.1
  have h2 : (2 : ZMod P₁) ≠ 0 := by
    intro hz
    have hdvd := (ZMod.natCast_eq_zero_iff 2 P₁).mp hz
    have hle := Nat.le_of_dvd (by decide : 0 < 2) hdvd
    omega
  have h0 : (0 : ZMod P₁) ∉ G := by
    intro hz
    have h1 := (hG 0).mp hz
    rw [zero_pow (by decide : (2 ^ 30 : ℕ) ≠ 0)] at h1
    exact zero_ne_one h1
  have hneg : ∀ x ∈ G, -x ∈ G := by
    intro x hx
    have heven : Even (2 ^ 30 : ℕ) := by decide
    exact (hG (-x)).mpr ((heven.neg_pow x).trans ((hG x).mp hx))
  have hmid : midpointCount G ≤ 2495902 * 2 ^ 30 := by
    unfold midpointCount
    calc ∑ z ∈ G, repCount G (2 * z)
        ≤ ∑ _z ∈ G, 2495902 := Finset.sum_le_sum (fun z hz =>
          hrep (2 * z) (mul_ne_zero h2 (fun hz0 => h0 (hz0 ▸ hz))))
      _ = 2495902 * 2 ^ 30 := by rw [Finset.sum_const, smul_eq_mul, hcard, mul_comm]
  have hA := rEnergy_two_ge_three_card_sq_sub h2 h0 hneg
  rw [hcard] at hA
  refine ⟨hcard, hmid, ?_⟩
  intro hdef
  unfold FirstStepOneUnitDefect at hdef
  have hAZ : (3 * (2 ^ 30 : ℤ) ^ 2 - 3 * (2 ^ 30 : ℤ)) ≤ (rEnergy G 2 : ℤ) := by
    have hsub : (3 * 2 ^ 30 : ℕ) ≤ 3 * (2 ^ 30) ^ 2 := by decide
    have hc : ((3 * (2 ^ 30) ^ 2 - 3 * 2 ^ 30 : ℕ) : ℤ) ≤ (rEnergy G 2 : ℤ) := by
      exact_mod_cast hA
    rwa [Nat.cast_sub hsub, Nat.cast_mul, Nat.cast_pow, Nat.cast_mul] at hc
  have hMZ : (midpointCount G : ℤ) ≤ 2495902 * 2 ^ 30 := by exact_mod_cast hmid
  have hPpos : (0 : ℤ) < (P₁ : ℤ) := by
    unfold P₁ ArkLib.ProximityGap.PrizeShapePrimeP30.P; norm_num
  have hP_A := mul_le_mul_of_nonneg_left hAZ hPpos.le
  have hP_M := mul_le_mul_of_nonneg_left hMZ (by linarith : (0 : ℤ) ≤ 2 * (P₁ : ℤ))
  have hgap : 2 * (P₁ : ℤ) * (2495902 * 2 ^ 30) <
      (P₁ : ℤ) * ((3 * (2 ^ 30 : ℤ) ^ 2 - 3 * (2 ^ 30 : ℤ)) + 2 ^ 30) -
        (2 ^ 30 * ((2 ^ 30 : ℤ) - 1)) ^ 2 -
        2 * ((2 ^ 30 : ℤ) - 1) ^ 2 * ((P₁ : ℤ) - 2 ^ 30) := by
    unfold P₁ ArkLib.ProximityGap.PrizeShapePrimeP30.P; norm_num
  linarith

/-- **Second designated prime (`P₂`): unconditional `midpointCount ≤ 2,495,902 * 2^30 < 2^52` and
unconditional refutation of `FirstStepOneUnitDefect`.** -/
theorem secondPrime_midpoint_and_no_firstStep_defect :
    let P₂ := ArkLib.ProximityGap.PrizeShapePrimeP30Second.P
    let G := (Finset.univ : Finset (ZMod P₂)).filter (fun x => x ^ (2 ^ 30 : ℕ) = 1)
    G.card = 2 ^ 30 ∧
      midpointCount G ≤ 2495902 * 2 ^ 30 ∧
      ¬ FirstStepOneUnitDefect P₂ (2 ^ 30) (rEnergy G 2) (midpointCount G) := by
  dsimp only
  set P₂ := ArkLib.ProximityGap.PrizeShapePrimeP30Second.P
  set G := (Finset.univ : Finset (ZMod P₂)).filter (fun x => x ^ (2 ^ 30 : ℕ) = 1)
  have hcard : G.card = 2 ^ 30 :=
    roots_card_eq_of_orderOf (by decide) ArkLib.ProximityGap.PrizeShapePrimeP30Second.orderOf_g
  have hG : ∀ x : ZMod P₂, x ∈ G ↔ x ^ (2 ^ 30 : ℕ) = 1 := by
    intro x
    simp [G]
  have hp : P₂.Prime := ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P
  have hbig : 2 ^ 41 < P₂ := by unfold P₂ ArkLib.ProximityGap.PrizeShapePrimeP30Second.P; decide
  have hrep := (production_gvRepBound_unconditional hp hbig hG).2.1
  have h2 : (2 : ZMod P₂) ≠ 0 := by
    intro hz
    have hdvd := (ZMod.natCast_eq_zero_iff 2 P₂).mp hz
    have hle := Nat.le_of_dvd (by decide : 0 < 2) hdvd
    omega
  have h0 : (0 : ZMod P₂) ∉ G := by
    intro hz
    have h1 := (hG 0).mp hz
    rw [zero_pow (by decide : (2 ^ 30 : ℕ) ≠ 0)] at h1
    exact zero_ne_one h1
  have hneg : ∀ x ∈ G, -x ∈ G := by
    intro x hx
    have heven : Even (2 ^ 30 : ℕ) := by decide
    exact (hG (-x)).mpr ((heven.neg_pow x).trans ((hG x).mp hx))
  have hmid : midpointCount G ≤ 2495902 * 2 ^ 30 := by
    unfold midpointCount
    calc ∑ z ∈ G, repCount G (2 * z)
        ≤ ∑ _z ∈ G, 2495902 := Finset.sum_le_sum (fun z hz =>
          hrep (2 * z) (mul_ne_zero h2 (fun hz0 => h0 (hz0 ▸ hz))))
      _ = 2495902 * 2 ^ 30 := by rw [Finset.sum_const, smul_eq_mul, hcard, mul_comm]
  have hA := rEnergy_two_ge_three_card_sq_sub h2 h0 hneg
  rw [hcard] at hA
  refine ⟨hcard, hmid, ?_⟩
  intro hdef
  unfold FirstStepOneUnitDefect at hdef
  have hAZ : (3 * (2 ^ 30 : ℤ) ^ 2 - 3 * (2 ^ 30 : ℤ)) ≤ (rEnergy G 2 : ℤ) := by
    have hsub : (3 * 2 ^ 30 : ℕ) ≤ 3 * (2 ^ 30) ^ 2 := by decide
    have hc : ((3 * (2 ^ 30) ^ 2 - 3 * 2 ^ 30 : ℕ) : ℤ) ≤ (rEnergy G 2 : ℤ) := by
      exact_mod_cast hA
    rwa [Nat.cast_sub hsub, Nat.cast_mul, Nat.cast_pow, Nat.cast_mul] at hc
  have hMZ : (midpointCount G : ℤ) ≤ 2495902 * 2 ^ 30 := by exact_mod_cast hmid
  have hPpos : (0 : ℤ) < (P₂ : ℤ) := by
    unfold P₂ ArkLib.ProximityGap.PrizeShapePrimeP30Second.P; norm_num
  have hP_A := mul_le_mul_of_nonneg_left hAZ hPpos.le
  have hP_M := mul_le_mul_of_nonneg_left hMZ (by linarith : (0 : ℤ) ≤ 2 * (P₂ : ℤ))
  have hgap : 2 * (P₂ : ℤ) * (2495902 * 2 ^ 30) <
      (P₂ : ℤ) * ((3 * (2 ^ 30 : ℤ) ^ 2 - 3 * (2 ^ 30 : ℤ)) + 2 ^ 30) -
        (2 ^ 30 * ((2 ^ 30 : ℤ) - 1)) ^ 2 -
        2 * ((2 ^ 30 : ℤ) - 1) ^ 2 * ((P₂ : ℤ) - 2 ^ 30) := by
    unfold P₂ ArkLib.ProximityGap.PrizeShapePrimeP30Second.P; norm_num
  linarith

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms shiftAux_ne_zero
#print axioms deg_shiftResidual
#print axioms shift_stepanov_count_many_graded
#print axioms coset_shift_rectangular_many
#print axioms production_coset_shift_count
#print axioms production_fourCoset_shift_count
#print axioms sum_autocorr_eq
#print axioms sum_erase_zero_autocorr_eq
#print axioms rEnergy_succ_eq_diffCount_autocorr
#print axioms rEnergy_succ_le_of_diffBound
#print axioms rEnergy_le_mul_pow_of_diffBound
#print axioms addEnergy_eq_rEnergy_two
#print axioms production_gvRepBound_unconditional
#print axioms production_moment_ladder_unconditional
#print axioms nonAntipodalCrossSextuples_card_le
#print axioms production_crossCoset_sextuples_le
#print axioms sumset_card_mul_rEnergy_ge
#print axioms production_sumset_expansion_unconditional
#print axioms sumset_card_ge_of_dcEnergyBound
#print axioms eta_eq_star_and_im_zero_of_neg_closed
#print axioms rEnergy_two_ge_three_card_sq_sub
#print axioms firstPrime_midpoint_and_no_firstStep_defect
#print axioms secondPrime_midpoint_and_no_firstStep_defect

end ArkLib.ProximityGap.Frontier.CarbonBGKM4ConfluentStepanovAndMoments
