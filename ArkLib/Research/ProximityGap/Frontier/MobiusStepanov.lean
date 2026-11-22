/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
Released under the MIT and Apache 2.0 licenses as described in LICENSE-MIT and LICENSE.
The weighted derivative argument adapts the Apache-2.0 HBK auxiliary multiplicity proof.
Authors: Proximity Prize contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.StepanovGeneratorIndep
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-! # Multiplicity and nonvanishing for a fractional linear Stepanov bound -/

set_option autoImplicit false

namespace ProximityGap.MobiusStepanov

open Polynomial Finset
open ArkLib.ProximityGap.Wronskian

variable {F : Type*} [Field F]

/-- A linear polynomial with prescribed root `a`. -/
noncomputable abbrev lin (a : F) : F[X] := X - C a

/-- Monomials obtained after clearing the common denominator of the auxiliary function. -/
noncomputable def term (a b : F) (e i j : ℕ) : F[X] := X^e * lin a^i * lin b^j

/-- Coefficients are indexed by a power of the rational function and a sparse `X`-block. -/
abbrev Weights (F : Type*) (m B : ℕ) := Fin B → Fin m → F

/-- The polynomial after clearing the denominator. -/
noncomputable def aux {m B : ℕ} (a b : F) (n : ℕ) (e : Fin m → ℕ) (w : Weights F m B) : F[X] :=
  ∑ c, ∑ j, C (w c j) * term a b (e j) (n*c) (n*(B-1-c))

/-- The auxiliary is nonzero whenever its coefficient vector is nonzero. The denominator never
vanishes at the zero of the numerator, so it does not change the disjoint valuation blocks. -/
theorem aux_ne_zero {m B n : ℕ} {a b : F} (ha : a ≠ 0) (hab : a ≠ b)
    {e : Fin m → ℕ} (hV : (Matrix.vandermonde (fun j => (e j : F))).det ≠ 0) (hm : m ≤ n)
    {w : Weights F m B} (hw : w ≠ 0) : aux a b n e w ≠ 0 := by
  classical
  intro hz
  let block (c : Fin B) : F[X] := ∑ j, C (w c j) * X ^ e j
  let Q (c : Fin B) := lin b ^ (n * (B - 1 - (c : ℕ)))
  have hQ (c : Fin B) : (Q c).eval a ≠ 0 := by simp [Q, lin, sub_ne_zero.mpr hab]
  have hQ0 (c : Fin B) : Q c ≠ 0 := fun h => hQ c (by rw [h, eval_zero])
  have hsum : ∑ c : Fin B, lin a ^ (n * c) * (Q c * block c) = 0 := by
    calc
      _ = aux a b n e w := by
        unfold aux
        apply sum_congr rfl
        intro c _
        simp only [Q, block, mul_sum, term]
        apply sum_congr rfl
        intro j _
        ring
      _ = 0 := hz
  have heinj : Function.Injective e := fun j k h =>
    (Matrix.det_vandermonde_ne_zero_iff.mp hV) (congrArg (fun t : ℕ => (t : F)) h)
  have hblocks : ∀ c : Fin B, Q c * block c = 0 := by
    apply eq_zero_of_sum_pow_block a n _ _ hsum
    intro c hc
    rw [rootMultiplicity_mul hc, rootMultiplicity_eq_zero (p := Q c) (by exact hQ c), zero_add]
    apply lt_of_lt_of_le _ hm
    exact rootMultiplicity_sparse_lt e (w c) a ha hV ((mul_ne_zero_iff.mp hc).2)
  apply hw
  funext c j
  have hb := (mul_eq_zero.mp (hblocks c)).resolve_left (hQ0 c)
  exact congrFun (eq_zero_of_sum_monomial_eq_zero heinj hb) j

/-- Weighted differentiation. -/
noncomputable def weighted (W P : F[X]) : F[X] := W * P.derivative

private theorem eval_iterate_derivative_weighted_eq_zero
    (W P : F[X]) (x : F) (n : ℕ)
    (hvanish : ∀ k ≤ n, eval x ((derivative^[k + 1]) P) = 0) :
    eval x ((derivative^[n]) (weighted W P)) = 0 := by
  rw [weighted, iterate_derivative_mul, eval_finsetSum]
  apply Finset.sum_eq_zero
  intro k hk
  rw [Finset.mem_range] at hk
  simp only [eval_smul, eval_mul]
  have hkder : eval x ((derivative^[k]) P.derivative) = 0 := by
    rw [← Function.iterate_succ_apply]
    exact hvanish k (by omega)
  rw [hkder, mul_zero, smul_zero]

private theorem eval_iterate_derivative_weighted_top
    (W P : F[X]) (x : F) (n : ℕ)
    (hvanish : ∀ k < n, eval x ((derivative^[k + 1]) P) = 0) :
    eval x ((derivative^[n]) (weighted W P)) =
      (W.eval x) * eval x ((derivative^[n + 1]) P) := by
  rw [weighted, iterate_derivative_mul, eval_finsetSum]
  rw [Finset.sum_eq_single n]
  · simp only [Nat.choose_self, one_smul, Nat.sub_self, Function.iterate_zero_apply,
      eval_mul]
    rw [← Function.iterate_succ_apply]
  · intro k hk hkn
    rw [Finset.mem_range] at hk
    simp only [eval_smul, eval_mul]
    have hklt : k < n := by omega
    have hkder : eval x ((derivative^[k]) P.derivative) = 0 := by
      rw [← Function.iterate_succ_apply]
      exact hvanish k hklt
    rw [hkder, mul_zero, smul_zero]
  · simp

/-- At a point where all lower ordinary derivatives vanish, the `m`-th cleared derivative has
the same leading jet as the ordinary derivative, multiplied by `(x(x-1))^m`. -/
theorem eval_iterate_weighted_eq_leading_jet
    (W P : F[X]) (x : F) (m : ℕ)
    (hvanish : ∀ j < m, eval x ((derivative^[j]) P) = 0) :
    eval x (((weighted W)^[m]) P) =
      (W.eval x) ^ m * eval x ((derivative^[m]) P) := by
  induction m generalizing P with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply]
      have hQvanish : ∀ j < m,
          eval x ((derivative^[j]) (weighted W P)) = 0 := by
        intro j hj
        apply eval_iterate_derivative_weighted_eq_zero W
        intro k hk
        exact hvanish (k + 1) (by omega)
      rw [ih (weighted W P) hQvanish,
        eval_iterate_derivative_weighted_top W P x m]
      · rw [pow_succ]
        ring
      · intro k hk
        exact hvanish (k + 1) (by omega)

/-- Vanishing of the first `D` cleared derivatives implies root multiplicity at least `D`, provided
the relevant factorial survives in the field and the clearing factor is nonzero at the point. -/
theorem le_rootMultiplicity_of_weighted_vanishing
    (W : F[X]) {P : F[X]} {x : F} {D : ℕ} (hP : P ≠ 0) (hW : W.eval x ≠ 0)
    (hfac : IsUnit (((D - 1).factorial : ℕ) : F))
    (hvanish : ∀ m < D, eval x (((weighted W)^[m]) P) = 0) :
    D ≤ P.rootMultiplicity x := by
  by_contra hD
  have hrD : P.rootMultiplicity x < D := Nat.lt_of_not_ge hD
  have hroot : P.IsRoot x := by
    rw [IsRoot]
    simpa using hvanish 0 (by omega)
  have hrpos : 0 < P.rootMultiplicity x := (rootMultiplicity_pos hP).mpr hroot
  have hlower : ∀ j < P.rootMultiplicity x,
      eval x ((derivative^[j]) P) = 0 := by
    intro j hj
    exact isRoot_iterate_derivative_of_lt_rootMultiplicity hj
  have hlead := eval_iterate_weighted_eq_leading_jet
    W P x (P.rootMultiplicity x) hlower
  rw [hvanish (P.rootMultiplicity x) hrD] at hlead
  have hclearing := hW
  have hderiv : eval x ((derivative^[P.rootMultiplicity x]) P) = 0 :=
    (mul_eq_zero.mp hlead.symm).resolve_left (pow_ne_zero _ hclearing)
  have heval := eval_iterate_derivative_rootMultiplicity (p := P) (t := x)
  rw [hderiv] at heval
  simp only [nsmul_eq_mul] at heval
  have hrle : P.rootMultiplicity x ≤ D - 1 := by omega
  obtain ⟨c, hc⟩ := Nat.factorial_dvd_factorial hrle
  have hfacdvd : (((P.rootMultiplicity x).factorial : ℕ) : F) ∣
      (((D - 1).factorial : ℕ) : F) := by
    refine ⟨(c : F), ?_⟩
    rw [← Nat.cast_mul, ← hc]
  have hfacr : IsUnit (((P.rootMultiplicity x).factorial : ℕ) : F) :=
    isUnit_of_dvd_unit hfacdvd hfac
  have hquot : eval x (P /ₘ (X - C x) ^ P.rootMultiplicity x) ≠ 0 :=
    eval_divByMonic_pow_rootMultiplicity_ne_zero x hP
  exact hquot ((mul_eq_zero.mp heval.symm).resolve_left hfacr.ne_zero)


/-- Clearing factor with all three distinguished linear factors. -/
noncomputable def clearing (a b : F) : F[X] := X * lin a * lin b

/-- Logarithmic derivative of a monomial after clearing the three linear factors. -/
noncomputable def logFactor (a b : F) (e i j : ℕ) : F[X] :=
  C (e : F) * lin a * lin b + C (i : F) * X * lin b + C (j : F) * X * lin a

private theorem self_mul_deriv_pow (f : F[X]) (e : ℕ) :
    f * (f ^ e).derivative = C (e : F) * f.derivative * f^e := by
  cases e with
  | zero => simp
  | succ e => rw [derivative_pow]; simp [pow_succ]; ring

private theorem weighted_term (a b : F) (e i j : ℕ) :
    weighted (clearing a b) (term a b e i j) = logFactor a b e i j * term a b e i j := by
  rw [weighted, term, derivative_mul, derivative_mul]
  change (X * lin a * lin b : F[X]) * _ = _
  calc
    _ = (X * (X^e).derivative) * lin a * lin b * lin a^i * lin b^j +
        (lin a * (lin a^i).derivative) * X * lin b * X^e * lin b^j +
        (lin b * (lin b^j).derivative) * X * lin a * X^e * lin a^i := by ring
    _ = _ := by rw [self_mul_deriv_pow, self_mul_deriv_pow, self_mul_deriv_pow];
                simp [logFactor, lin]; ring

/-- The residual multiplier after `r` weighted derivatives. -/
noncomputable def residual (a b : F) (e i j : ℕ) : ℕ → F[X]
  | 0 => 1
  | r+1 => weighted (clearing a b) (residual a b e i j r) +
      logFactor a b e i j * residual a b e i j r

/-- The `r`-th derivative retains the original large powers. -/
theorem iterate_term (a b : F) (e i j r : ℕ) :
    ((weighted (clearing a b))^[r]) (term a b e i j) =
      term a b e i j * residual a b e i j r := by
  induction r with
  | zero => simp [residual]
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, residual]
    let g := term a b e i j
    let h := residual a b e i j r
    let W := clearing a b
    change W * (g*h).derivative = g * (W * h.derivative + logFactor a b e i j * h)
    rw [derivative_mul]
    calc
      _ = (W*g.derivative)*h + g*(W*h.derivative) := by ring
      _ = _ := by rw [show W*g.derivative = logFactor a b e i j*g from weighted_term ..]; ring

private theorem deg_clear (a b : F) : (clearing a b).natDegree ≤ 3 := by
  unfold clearing lin
  calc
    _ ≤ ((X : F[X]) * (X-C a)).natDegree + (X-C b).natDegree := natDegree_mul_le
    _ ≤ ((X : F[X]).natDegree + (X-C a).natDegree) + (X-C b).natDegree := by gcongr; exact natDegree_mul_le
    _ = 3 := by simp

private theorem deg_logFactor (a b : F) (e i j : ℕ) : (logFactor a b e i j).natDegree ≤ 2 := by
  have bound (v : F) (f g : F[X]) (hf : f.natDegree = 1) (hg : g.natDegree = 1) :
      (C v * f * g).natDegree ≤ 2 := by
    calc
      _ ≤ (C v * f).natDegree + g.natDegree := natDegree_mul_le
      _ ≤ ((C v).natDegree + f.natDegree) + g.natDegree := by gcongr; exact natDegree_mul_le
      _ = 2 := by simp [hf,hg]
  unfold logFactor
  apply (natDegree_add_le _ _).trans
  apply max_le
  · apply (natDegree_add_le _ _).trans
    exact max_le (bound _ _ _ (natDegree_X_sub_C _) (natDegree_X_sub_C _))
      (bound _ _ _ natDegree_X (natDegree_X_sub_C _))
  · exact bound _ _ _ natDegree_X (natDegree_X_sub_C _)

/-- The price of each derivative is at most two degrees. -/
theorem deg_residual (a b : F) (e i j r : ℕ) : (residual a b e i j r).natDegree ≤ 2*r := by
  induction r with
  | zero => simp [residual]
  | succ r ih =>
    rw [residual]
    let H := residual a b e i j r
    have hH : H.natDegree ≤ 2*r := ih
    apply (natDegree_add_le _ _).trans
    apply max_le
    · by_cases hh : H.derivative = 0
      · change (clearing a b * H.derivative).natDegree ≤ _
        simp [hh]
      · have hp : 0 < H.natDegree := by
          by_contra! hz
          exact hh (derivative_of_natDegree_zero (by omega))
        have hd := natDegree_derivative_le H
        have hmul : (clearing a b * H.derivative).natDegree ≤
            (clearing a b).natDegree + H.derivative.natDegree := natDegree_mul_le
        have hW := deg_clear a b
        change (clearing a b * H.derivative).natDegree ≤ _
        omega
    · have hmul : (logFactor a b e i j * H).natDegree ≤
          (logFactor a b e i j).natDegree + H.natDegree := natDegree_mul_le
      have hL := deg_logFactor a b e i j
      change (logFactor a b e i j * H).natDegree ≤ _
      omega

/-- The polynomial forced to vanish at derivative order `r`. Here `d j` is an exponent
representative with the same value as `e j` on the subgroup. -/
noncomputable def constraint {m B : ℕ} (a b K : F) (n : ℕ) (e d : Fin m → ℕ)
    (w : Weights F m B) (r : ℕ) : F[X] :=
  ∑ c, ∑ j, C (w c j * K ^ (c : ℕ)) * X ^ d j * residual a b (e j) (n*c) (n*(B-1-c)) r

private theorem constraint_degree {m B : ℕ} (a b K : F) (n : ℕ) (e d : Fin m → ℕ)
    (w : Weights F m B) {A : ℕ} (hd : ∀ j, d j ≤ A) (r : ℕ) :
    (constraint a b K n e d w r).natDegree ≤ A + 2*r := by
  apply natDegree_sum_le_of_forall_le
  intro c _
  apply natDegree_sum_le_of_forall_le
  intro j _
  apply natDegree_mul_le.trans
  apply Nat.add_le_add _ (deg_residual ..)
  apply natDegree_mul_le.trans
  simpa only [natDegree_C, natDegree_X_pow, zero_add] using hd j

private noncomputable def extractCoefficients {m B : ℕ} (a b K : F) (n : ℕ) (e d : Fin m → ℕ)
    {I : Type*} (order index : I → ℕ) : Weights F m B →ₗ[F] (I → F) where
  toFun w l := (constraint a b K n e d w (order l)).coeff (index l)
  map_add' x y := by
    funext l
    simp [constraint, add_mul, sum_add_distrib]
  map_smul' v x := by
    funext l
    simp [constraint, mul_assoc, mul_sum]

/-- Coefficient extraction as a linear map on the auxiliary weights. -/
noncomputable def constraintMap {m B : ℕ} (a b K : F) (n : ℕ) (e d : Fin m → ℕ) (D W : ℕ) :
    Weights F m B →ₗ[F] (Fin D × Fin W → F) :=
  extractCoefficients a b K n e d (fun l => l.1.val) (fun l => l.2.val)

/-- The coefficient indices at order `r` stop at the actual degree bound. -/
abbrev GradedCoefficients (A D : ℕ) := (r : Fin D) × Fin (A + 2*r.val)

private theorem graded_card (A D : ℕ) :
    Fintype.card (GradedCoefficients A D) = D*(A+(D-1)) := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun r => A+2*r), sum_add_distrib]
  simp only [sum_const, card_range, nsmul_eq_mul]
  rw [← mul_sum, Nat.mul_comm 2 _, sum_range_id_mul_two, Nat.mul_add]
  rfl

private noncomputable def gradedMap {m B : ℕ} (a b K : F) (n : ℕ) (e d : Fin m → ℕ) (A D : ℕ) :
    Weights F m B →ₗ[F] (GradedCoefficients A D → F) :=
  extractCoefficients a b K n e d (fun l => l.1.val) (fun l => l.2.val)

private theorem exists_joint_kernel {m B J : ℕ} (a b : F) (K : Fin J → F)
    (n : ℕ) (e d : Fin m → ℕ) (A D : ℕ) (gap : J * (D * (A+(D-1))) < B * m) :
    ∃ w : Weights F m B, w ≠ 0 ∧ ∀ i, gradedMap a b (K i) n e d A D w = 0 := by
  classical
  let L := LinearMap.pi (fun i => @gradedMap F _ m B a b (K i) n e d A D)
  have hdim : Module.finrank F (Fin J → GradedCoefficients A D → F) <
      Module.finrank F (Weights F m B) := by
    change Module.finrank F (Fin J → GradedCoefficients A D → F) < Module.finrank F (Fin B → Fin m → F)
    rw [Module.finrank_pi_fintype F, Module.finrank_pi_fintype F (M := fun _ : Fin B => Fin m → F)]
    simpa only [Module.finrank_pi, graded_card, Fintype.card_fin, sum_const, card_univ,
      nsmul_eq_mul, Nat.cast_id] using gap
  have hn : ¬Function.Injective L := fun hi => (not_le_of_gt hdim)
    (LinearMap.finrank_le_finrank_of_injective hi)
  rw [← LinearMap.ker_eq_bot] at hn
  obtain ⟨w, hw, hne⟩ := (Submodule.ne_bot_iff _).mp hn
  exact ⟨w, hne, fun i => congrFun (LinearMap.mem_ker.mp hw) i⟩

private theorem constraint_zero_of_kernel {m B : ℕ} (a b K : F) (n : ℕ) (e d : Fin m → ℕ)
    {A D : ℕ} (hA : 0 < A) (hd : ∀ j, d j < A) {w : Weights F m B}
    (hk : gradedMap a b K n e d A D w = 0) {r : ℕ} (hr : r<D) :
    constraint a b K n e d w r = 0 := by
  ext t
  rw [coeff_zero]
  by_cases ht : t < A + 2*r
  · exact congrFun hk ⟨⟨r,hr⟩,⟨t,ht⟩⟩
  · apply coeff_eq_zero_of_natDegree_lt
    have h := constraint_degree a b K n e d w (A := A-1) (fun j => by have := hd j; omega) r
    omega

private theorem weighted_sum {I : Type*} (W : F[X]) (s : Finset I) (f : I → F[X]) (r : ℕ) :
    ((weighted W)^[r]) (∑ i ∈ s, f i) = ∑ i ∈ s, ((weighted W)^[r]) (f i) := by
  induction r with
  | zero => simp
  | succ r ih => simp [Function.iterate_succ_apply', ih, weighted, mul_sum]

private theorem weighted_const (W f : F[X]) (v : F) (r : ℕ) :
    ((weighted W)^[r]) (C v * f) = C v * ((weighted W)^[r]) f := by
  induction r with
  | zero => simp
  | succ r ih => simp only [Function.iterate_succ_apply', ih, weighted, derivative_C_mul]; ring

private theorem eval_weighted_aux {m B : ℕ} (a b K : F) (n : ℕ) (e d : Fin m → ℕ)
    (w : Weights F m B) (r : ℕ) (x : F) (hxe : ∀ j, x ^ e j = x ^ d j)
    (hxratio : (x-a)^n = K * (x-b)^n) :
    (((weighted (clearing a b))^[r]) (aux a b n e w)).eval x =
      ((x-b)^n)^(B-1) * (constraint a b K n e d w r).eval x := by
  classical
  simp only [aux, constraint, weighted_sum, weighted_const, iterate_term, eval_finsetSum,
    mul_sum, eval_mul, eval_C, eval_pow, eval_X]
  apply sum_congr rfl
  intro c _
  apply sum_congr rfl
  intro j _
  have hbc : (c : ℕ) + (B-1-c) = B-1 := by omega
  simp only [term, lin, eval_mul, eval_pow, eval_X, eval_sub, eval_C, pow_mul, hxratio, mul_pow, hxe]
  have hpows : ((x-b)^n)^(c : ℕ) * ((x-b)^n)^(B-1-c) = ((x-b)^n)^(B-1) := by
    rw [← pow_add, hbc]
  rw [← hpows]
  ring

private theorem aux_degree {m B : ℕ} (a b : F) (n : ℕ) (e : Fin m → ℕ) (w : Weights F m B)
    {E : ℕ} (hE : ∀ j, e j ≤ E) : (aux a b n e w).natDegree ≤ E+n*(B-1) := by
  apply natDegree_sum_le_of_forall_le
  intro c _
  apply natDegree_sum_le_of_forall_le
  intro j _
  apply natDegree_mul_le.trans
  rw [natDegree_C, zero_add]
  unfold term
  have h1 : (X ^ e j * lin a ^ (n*c) : F[X]).natDegree ≤ e j + n*c := by
    simpa [lin] using (natDegree_mul_le (p := (X : F[X]) ^ e j) (q := lin a ^ (n*c)))
  apply natDegree_mul_le.trans
  have h2 : (lin b ^ (n*(B-1-c))).natDegree = n*(B-1-c) := by simp [lin]
  rw [h2]
  have hbc : (c : ℕ) + (B-1-c) = B-1 := by omega
  calc
    _ ≤ e j + n*c + n*(B-1-c) := Nat.add_le_add_right h1 _
    _ = e j + n*(B-1) := by rw [Nat.add_assoc, ← Nat.mul_add, hbc]
    _ ≤ _ := Nat.add_le_add_right (hE j) _

/-- Multiplicity count for simultaneous subgroup values of a fractional linear function.
The target value may depend on the site. Each permitted target imposes one
additional block of derivative conditions on the same auxiliary polynomial. -/
theorem mobius_count_many_graded {m B n A D E J : ℕ} {a b : F} (K : Fin J → F) (ha : a ≠ 0) (hab : a ≠ b)
    {e d : Fin m → ℕ} (hV : (Matrix.vandermonde (fun j => (e j : F))).det ≠ 0)
    (hm : m ≤ n) (hE : ∀ j, e j ≤ E) (hA : 0 < A) (hd : ∀ j, d j < A)
    (hgap : J * (D * (A + (D-1))) < B*m) (hfac : IsUnit (((D-1).factorial : ℕ) : F))
    (S : Finset F) (hreg : ∀ x ∈ S, x ≠ 0 ∧ x ≠ a ∧ x ≠ b)
    (hxe : ∀ x ∈ S, ∀ j, x ^ e j = x ^ d j)
    (hratio : ∀ x ∈ S, ∃ i, (x-a)^n = K i * (x-b)^n) : D * S.card ≤ E + n * (B-1) := by
  classical
  obtain ⟨w,hw,hk⟩ := exists_joint_kernel a b K n e d A D hgap
  let P := aux a b n e w
  have hP : P ≠ 0 := aux_ne_zero ha hab hV hm hw
  have hmult : ∀ x ∈ S, D ≤ P.rootMultiplicity x := by
    intro x hx
    obtain ⟨hx0,hxa,hxb⟩ := hreg x hx
    obtain ⟨i, hi⟩ := hratio x hx
    have hW : (clearing a b).eval x ≠ 0 := by
      simp [clearing, lin, hx0, sub_ne_zero.mpr hxa, sub_ne_zero.mpr hxb]
    apply le_rootMultiplicity_of_weighted_vanishing (clearing a b) hP hW hfac
    intro r hr
    rw [show P = aux a b n e w from rfl,
        eval_weighted_aux a b (K i) n e d w r x (hxe x hx) hi,
        constraint_zero_of_kernel a b (K i) n e d hA hd (hk i) hr, eval_zero, mul_zero]
  calc
    D * S.card = ∑ _x ∈ S, D := by simp [Nat.mul_comm]
    _ ≤ ∑ x ∈ S, P.roots.count x := by
      apply sum_le_sum
      intro x hx
      rw [count_roots]
      exact hmult x hx
    _ = ∑ x ∈ S ∩ P.roots.toFinset, P.roots.count x := by
      refine (sum_subset inter_subset_left fun x hx hx' => ?_).symm
      exact Multiset.count_eq_zero.mpr fun hm' => hx' (mem_inter.mpr ⟨hx, Multiset.mem_toFinset.mpr hm'⟩)
    _ ≤ ∑ x ∈ P.roots.toFinset, P.roots.count x :=
      sum_le_sum_of_subset_of_nonneg inter_subset_right fun _ _ _ => Nat.zero_le _
    _ = Multiset.card P.roots := P.roots.toFinset_sum_count_eq
    _ ≤ P.natDegree := P.card_roots'
    _ ≤ _ := aux_degree a b n e w hE

/-- The coarser common-width constraint count also suffices. -/
theorem mobius_count_many {m B n A D E J : ℕ} {a b : F} (K : Fin J → F) (ha : a ≠ 0) (hab : a ≠ b)
    {e d : Fin m → ℕ} (hV : (Matrix.vandermonde (fun j => (e j : F))).det ≠ 0)
    (hm : m ≤ n) (hE : ∀ j, e j ≤ E) (hA : 0 < A) (hd : ∀ j, d j < A)
    (hgap : J * (D * (A + 2*(D-1))) < B*m) (hfac : IsUnit (((D-1).factorial : ℕ) : F))
    (S : Finset F) (hreg : ∀ x ∈ S, x ≠ 0 ∧ x ≠ a ∧ x ≠ b)
    (hxe : ∀ x ∈ S, ∀ j, x ^ e j = x ^ d j)
    (hratio : ∀ x ∈ S, ∃ i, (x-a)^n = K i * (x-b)^n) : D * S.card ≤ E + n * (B-1) := by
  apply mobius_count_many_graded K ha hab hV hm hE hA hd _ hfac S hreg hxe hratio
  exact lt_of_le_of_lt (Nat.mul_le_mul_left J (Nat.mul_le_mul_left D (by omega))) hgap

/-- Multiplicity count for simultaneous subgroup values of a fractional linear function.
The two affine factors are normalized to leading coefficient one. Their leading-coefficient
ratio in the original map is absorbed by `K`. -/
theorem mobius_count {m B n A D E : ℕ} {a b K : F} (ha : a ≠ 0) (hab : a ≠ b)
    {e d : Fin m → ℕ} (hV : (Matrix.vandermonde (fun j => (e j : F))).det ≠ 0)
    (hm : m ≤ n) (hE : ∀ j, e j ≤ E) (hA : 0 < A) (hd : ∀ j, d j < A)
    (hgap : D * (A + 2*(D-1)) < B*m) (hfac : IsUnit (((D-1).factorial : ℕ) : F))
    (S : Finset F) (hreg : ∀ x ∈ S, x ≠ 0 ∧ x ≠ a ∧ x ≠ b)
    (hxe : ∀ x ∈ S, ∀ j, x ^ e j = x ^ d j)
    (hratio : ∀ x ∈ S, (x-a)^n = K * (x-b)^n) : D * S.card ≤ E + n * (B-1) := by
  apply mobius_count_many (J := 1) (fun _ => K) ha hab hV hm hE hA hd
    (by simpa using hgap) hfac S hreg hxe
  exact fun x hx => ⟨0, hratio x hx⟩

#print axioms mobius_count_many_graded
#print axioms mobius_count_many
#print axioms aux_ne_zero
#print axioms mobius_count

/-- Weighted count for source subgroup order `2^30` and arbitrary target exponent. -/
theorem production_exponent_count {p m : ℕ} [CharP F p] (hp : p.Prime) (hbig : 2^37 < p) (hm : 4096*64 ≤ m)
    {a b K : F} (ha : a ≠ 0) (hab : a ≠ b) (S : Finset F)
    (hreg : ∀ x ∈ S, x ≠ 0 ∧ x ≠ a ∧ x ≠ b)
    (hpow : ∀ x ∈ S, x ^ (2^30 : ℕ) = 1)
    (hratio : ∀ x ∈ S, (x-a)^m = K * (x-b)^m) :
    2048 * S.card ≤ 4095 + 1073741824 * 63 + m * 63 := by
  let d (j : Fin (4096*64)) := (j : ℕ) % 4096
  let e (j : Fin (4096*64)) := d j + 1073741824 * ((j : ℕ) / 4096)
  have hd (j) : d j < 4096 := Nat.mod_lt _ (by decide)
  have he (j) : e j ≤ 4095 + 1073741824 * 63 := by
    have := j.isLt
    dsimp [d,e]
    omega
  have hinj : Function.Injective e := by
    intro i j hij
    have hi := hd i
    have hj := hd j
    apply Fin.ext
    dsimp [e,d] at hij hi hj
    omega
  have hV : (Matrix.vandermonde (fun j => (e j : F))).det ≠ 0 := by
    rw [Matrix.det_vandermonde_ne_zero_iff]
    intro i j hij
    apply hinj
    apply CharP.natCast_injOn_Iio F p _ _ hij
    · change e i < p; have := he i; omega
    · change e j < p; have := he j; omega
  have hfac : IsUnit ((((2048-1 : ℕ).factorial : ℕ) : F)) := by
    rw [isUnit_iff_ne_zero, ne_eq, CharP.cast_eq_zero_iff F p]
    intro hh
    have hle := (Nat.Prime.dvd_factorial hp).mp hh
    omega
  exact mobius_count (B := 64) (D := 2048) (A := 4096) (n := m) ha hab hV
    hm he (by decide) hd (by decide) hfac S hreg (fun x hx j => by
      change x ^ (d j + (2^30 : ℕ)*((j : ℕ)/4096)) = x ^ d j
      rw [pow_add, pow_mul, hpow x hx, one_pow, mul_one]) hratio

/-- Explicit count for subgroup order `2^30`, valid in every prime characteristic above `2^37`.
`a` and `b` are the distinct zero and pole of the fractional linear function. -/
theorem production_count {p : ℕ} [CharP F p] (hp : p.Prime) (hbig : 2^37 < p)
    {a b K : F} (ha : a ≠ 0) (hab : a ≠ b) (S : Finset F)
    (hreg : ∀ x ∈ S, x ≠ 0 ∧ x ≠ a ∧ x ≠ b)
    (hpow : ∀ x ∈ S, x ^ (2^30 : ℕ) = 1)
    (hratio : ∀ x ∈ S, (x-a)^(2^30 : ℕ) = K * (x-b)^(2^30 : ℕ)) :
    S.card ≤ 66060289 := by
  have h := production_exponent_count hp hbig (by decide : 4096*64 ≤ 2^30) ha hab S hreg hpow hratio
  omega

/-- The literal Möbius intersection, with the denominator interpreted using totalized field
division. Its pole maps to zero and cannot satisfy the subgroup membership equation. -/
theorem production_mobius_intersection {p : ℕ} [CharP F p] [Fintype F] [DecidableEq F]
    (hp : p.Prime) (hbig : 2^37 < p) {a b l : F} (ha : a ≠ 0) (hab : a ≠ b) (hl : l ≠ 0) :
    (univ.filter (fun x : F => x ^ (2^30 : ℕ) = 1 ∧
      (l * (x-a) / (x-b)) ^ (2^30 : ℕ) = 1)).card ≤ 66060289 := by
  apply production_count (K := (l ^ (2^30 : ℕ))⁻¹) hp hbig ha hab
  · intro x hx
    obtain ⟨hx,hy⟩ := (mem_filter.mp hx).2
    refine ⟨?_, ?_, ?_⟩
    · rintro rfl; simp at hx
    · rintro rfl; simp at hy
    · rintro rfl; simp at hy
  · intro x hx
    exact (mem_filter.mp hx).2.1
  · intro x hx
    have hy := (mem_filter.mp hx).2.2
    have hxb : x-b ≠ 0 := by intro he; simp [he] at hy
    rw [div_pow, mul_pow, div_eq_iff (pow_ne_zero _ hxb), one_mul] at hy
    calc
      _ = (l ^ (2^30 : ℕ))⁻¹ * (l ^ (2^30 : ℕ) * (x-a) ^ (2^30 : ℕ)) := by
        rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hl), one_mul]
      _ = _ := by rw [hy]

#print axioms production_mobius_intersection

end ProximityGap.MobiusStepanov
