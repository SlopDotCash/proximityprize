/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Data.MvPolynomial.WeightedDegree
import ArkLib.Data.Polynomial.Differential.Types
import ArkLib.ToMathlib.Polynomial.HasseTaylor.Lifting
import ArkLib.ToMathlib.Polynomial.HasseTaylor.Shift
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.Finsupp.Option
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.Tactic

/-!
# Prime-Field Hidden-Derivative Order, Bank Rank-Nullity, and Cofactor Engine (`PrimeHDOrder`)

Generalized, characteristic-free / prime-field-ready formalization of the higher-order contact
layer infrastructure (`Final50Order`, `Fast074` `order_of_locator_lines`, `PortLowBase`
`exists_fresh`/`sum_by_layer`, and `Fast070` `cofactor_rank`), parameterized over arbitrary jet
order `n` (`n = 2` for first-order `d = 1`, `n = 4` for `d = 3`, etc.) and any infinite field `L`
(such as `AlgebraicClosure K` over a prime field `K = ZMod p`).

Clean-room / attributed Apache-2.0 adaptation from `proximity-prize/proximity-prize`
(`Final50Order.lean`, `Fast074.lean`, `PortLowBase.lean`, `Fast070.lean`), generalized to
arbitrary parameters and sharpened with the strictly tighter `d = 1` weighted cofactor rank bound.

## Main statements

1. **Jet Rows & Bridge (`JetRow`, `jet`, `atJet`, `shiftJet`, `OrderAt`, `TrueWeightLE`,
   `Contact`, `symbolAt`, `jetRowEquivDifferential`):**
   Core polynomial ring `JetRow L n = MvPolynomial (Fin n) (Polynomial L)` and canonical ring
   isomorphism with ArkLib's `DifferentialPolynomial L d` (`n = d + 1`).
2. **Locator-Line Order Extraction (`eval_line`, `line_contacts_zero`, `order_of_locator_lines`,
   `order_of_contact`):**
   From `m_contact`-order contact at `agreement` nodes and weighted degree `≤ T`, extracts exact
   shift-order `OrderAt P S ((cutoff - T) / layerWidth + 1)` for every codeword `S` of degree
   `≤ physDeg` agreeing at `≥ agreement` nodes.
3. **Exact `bankEval` Rank-Nullity (`exists_fresh`, `sum_by_layer`, `divide_specialization`,
   `symbol_families`):**
   Using the exact kernel characterization `ker(bankEval x (T + 1)) = (X - x) * bank T` at a fresh
   abscissa `x`, extracts linearly independent specialized symbol families at each weight layer `T`
   whose ranks sum to at least `sourceRank`.
4. **Weighted Cofactor Rank & Tighter `d = 1` Bound (`cofactor_rank_weighted`,
   `cofactor_rank_d1`):**
   Strictly additive weighted total degrees on the integral domain `JetSymbol L n` bound the rank
   of multiples of `∏ F_j^(a_j)` by the exact residual exponent count; at `d = 1` (`n = 2`), gives
   the tighter `#142` count `#{ (b₀, b₁) | w * b₀ + (w - 1) * b₁ ≤ T - ∑ a_j W_j ∧ b₁ ≤ s - ∑ a_j d_j }`.
5. **Master Layer-Budget Theorem (`exists_availability`, `of_children`):**
   Given irreducible factors `f_1, ..., f_r` and any proper-cut provider (discharged unconditionally
   by `PrimeHDTopHasse` when `0 < deg_{Y_{n-1}}(f_i) < p`), produces availability orders `l_i`
   satisfying the exact layer-budget inequality.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace ArkLib.ProximityGap.Frontier.PrimeHDOrder

open Polynomial PolynomialDifferential
open scoped BigOperators

/-! ### Part 1: Core Definitions and Bridge to `DifferentialPolynomial` -/

/-- Multivariate polynomial in `n` jet variables `Y₀, ..., Y_{n-1}` with coefficients in `L[X]`. -/
abbrev JetRow (L : Type*) [CommRing L] (n : ℕ) := MvPolynomial (Fin n) (Polynomial L)

/-- Specialized symbol ring `L[Y₀, ..., Y_{n-1}]` obtained by evaluating `X = x`. -/
abbrev JetSymbol (L : Type*) [CommRing L] (n : ℕ) := MvPolynomial (Fin n) L

noncomputable section

/-- The `i`-th Hasse derivative jet `D^i S` of a univariate polynomial `S`. -/
def jet {L : Type*} [CommRing L] {n : ℕ} (S : Polynomial L) (i : Fin n) : Polynomial L :=
  Polynomial.hasseDeriv i.val S

/-- Evaluation of a jet row `P(X, Y₀, ..., Y_{n-1})` along the jet of `S`. -/
def atJet {L : Type*} [CommRing L] {n : ℕ} (P : JetRow L n) (S : Polynomial L) : Polynomial L :=
  MvPolynomial.eval (jet S) P

/-- Shifted jet polynomial `P(X, Y₀ + D⁰S, ..., Y_{n-1} + D^{n-1}S)`. -/
def shiftJet {L : Type*} [CommRing L] {n : ℕ} (P : JetRow L n) (S : Polynomial L) : JetRow L n :=
  MvPolynomial.eval₂ MvPolynomial.C (fun i => MvPolynomial.X i + MvPolynomial.C (jet S i)) P

/-- `shiftJet P S` as a ring homomorphism `JetRow L n →+* JetRow L n`. -/
def shiftJetHom {L : Type*} [CommRing L] {n : ℕ} (S : Polynomial L) : JetRow L n →+* JetRow L n :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i => MvPolynomial.X i + MvPolynomial.C (jet S i))

theorem shiftJetHom_apply {L : Type*} [CommRing L] {n : ℕ} (P : JetRow L n) (S : Polynomial L) :
    shiftJetHom S P = shiftJet P S := rfl

/-- Total jet-vanishing order at `S` is at least `d`: every monomial in `shiftJet P S` has
total jet degree at least `d`. -/
def OrderAt {L : Type*} [CommRing L] {n : ℕ} (P : JetRow L n) (S : Polynomial L) (d : ℕ) : Prop :=
  ∀ m ∈ (shiftJet P S).support, d ≤ m.degree

/-- If `OrderAt P S d` with `1 ≤ d`, then `P` vanishes identically along the jet of `S`. -/
theorem atJet_eq_zero_of_orderAt_pos {L : Type*} [CommRing L] {n : ℕ}
    {P : JetRow L n} {S : Polynomial L} {d : ℕ} (hd : 1 ≤ d) (h : OrderAt P S d) :
    atJet P S = 0 := by
  have hconst : (shiftJet P S).coeff 0 = atJet P S := by
    have hev : MvPolynomial.eval (0 : Fin n → Polynomial L) (shiftJet P S) = atJet P S := by
      unfold shiftJet atJet
      rw [MvPolynomial.hom_eval₂]
      have hC : (MvPolynomial.eval (0 : Fin n → Polynomial L)).comp MvPolynomial.C =
          RingHom.id (Polynomial L) := RingHom.ext fun p => by simp
      rw [hC]
      change MvPolynomial.eval₂ (RingHom.id _) _ P = MvPolynomial.eval₂ (RingHom.id _) _ P
      congr 1
      funext i
      simp
    rw [← hev, MvPolynomial.eval_zero]
    rfl
  rw [← hconst]
  by_contra hnz
  have hmem : (0 : Fin n →₀ ℕ) ∈ (shiftJet P S).support := MvPolynomial.mem_support_iff.mpr hnz
  have := h 0 hmem
  simp at this
  omega

/-- True differential specialization weight bound: every monomial `m` in `P` satisfies
`deg_X(P.coeff m) + ∑ i, (physDeg - i) * m i ≤ T`. -/
def TrueWeightLE {L : Type*} [CommRing L] {n : ℕ} (physDeg : ℕ) (P : JetRow L n) (T : ℕ) : Prop :=
  ∀ m ∈ P.support, (P.coeff m).natDegree + m.sum (fun i a => (physDeg - i.val) * a) ≤ T

/-- Pointwise contact condition of order `m_contact` at every node `(nodes i, w i)`:
`(X - nodes i)^m_contact ∣ P(X, S, D¹S, ...)` for every polynomial `S` hitting `(nodes i, w i)`. -/
def Contact {L I : Type*} [CommRing L] {n : ℕ} (nodes w : I → L) (m_contact : ℕ)
    (P : JetRow L n) : Prop :=
  ∀ i (S : Polynomial L), S.eval (nodes i) = w i →
    (Polynomial.X - Polynomial.C (nodes i)) ^ m_contact ∣ atJet P S

/-- Specialization of a jet row at `X = x`: `JetRow L n →+* JetSymbol L n`. -/
def symbolAt {L : Type*} [CommRing L] {n : ℕ} (x : L) : JetRow L n →+* JetSymbol L n :=
  MvPolynomial.map (Polynomial.evalRingHom x)

/-- `symbolAt x` as an `L`-linear map. -/
def symbolLinear {L : Type*} [CommRing L] {n : ℕ} (x : L) : JetRow L n →ₗ[L] JetSymbol L n :=
  ({ symbolAt x with
      commutes' := fun a => by
        change MvPolynomial.map (Polynomial.evalRingHom x) (MvPolynomial.C (Polynomial.C a)) =
          MvPolynomial.C a
        simp } : JetRow L n →ₐ[L] JetSymbol L n).toLinearMap

theorem symbolLinear_apply {L : Type*} [CommRing L] {n : ℕ} (x : L) (P : JetRow L n) :
    symbolLinear x P = symbolAt x P := rfl

/-- Canonical ring equivalence `JetRow R (d + 1) ≃+* DifferentialPolynomial R d`, sending
`X` inside coefficients to `MvPolynomial.X none` and `Y_i` to `MvPolynomial.X (some i)`. -/
def jetRowEquivDifferential {R : Type*} [CommRing R] (d : ℕ) :
    JetRow R (d + 1) ≃+* DifferentialPolynomial R d :=
  RingEquiv.ofRingHom
    (MvPolynomial.eval₂Hom
      (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X none))
      (fun i => MvPolynomial.X (some i)))
    (MvPolynomial.eval₂Hom
      (MvPolynomial.C.comp Polynomial.C)
      (fun v => match v with
        | none => MvPolynomial.C Polynomial.X
        | some i => MvPolynomial.X i))
    (by
      apply MvPolynomial.ringHom_ext
      · intro r; simp
      · rintro (_ | i) <;> simp)
    (by
      apply MvPolynomial.ringHom_ext
      · intro p
        induction p using Polynomial.induction_on' with
        | add p q hp hq =>
          simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, RingHom.id_apply] at hp hq ⊢
          rw [map_add, map_add, map_add, hp, hq]
        | monomial n a =>
          simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, RingHom.id_apply,
            Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial, map_mul, map_pow,
            MvPolynomial.eval₂Hom_X']
          rw [← map_pow, ← map_mul, Polynomial.C_mul_X_pow_eq_monomial]
      · intro i; simp)

/-- Locator polynomial `∏_{i ∈ A} (X - x_i)`. -/
def locator {L I : Type*} [CommRing L] (x : I → L) (A : Finset I) : Polynomial L :=
  ∏ i ∈ A, (Polynomial.X - Polynomial.C (x i))

theorem locator_monic {L I : Type*} [CommRing L] (x : I → L) (A : Finset I) :
    (locator x A).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C (x i)

theorem locator_natDegree {L I : Type*} [CommRing L] [Nontrivial L] (x : I → L) (A : Finset I) :
    (locator x A).natDegree = A.card := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [locator]
  | insert i s hi ih =>
    rw [locator, Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    have hm1 : (Polynomial.X - Polynomial.C (x i)).Monic := Polynomial.monic_X_sub_C (x i)
    have hm2 : (∏ j ∈ s, (Polynomial.X - Polynomial.C (x j))).Monic := locator_monic x s
    rw [hm1.natDegree_mul hm2, Polynomial.natDegree_X_sub_C]
    change 1 + (locator x s).natDegree = s.card + 1
    omega

theorem locator_eval_zero {L I : Type*} [CommRing L] (x : I → L) (A : Finset I)
    {i : I} (hi : i ∈ A) : (locator x A).eval (x i) = 0 := by
  rw [locator, Polynomial.eval_prod]
  exact Finset.prod_eq_zero hi (by simp)

/-! ### Part 2: Locator-Line Order Extraction (`Fast074` & `Final50OrderProof_1`) -/

/-- The directional line polynomial `P(X, jet(S) + t * jet(U)) ∈ (L[X])[t]`. -/
def line {L : Type*} [CommRing L] {n : ℕ} (P : JetRow L n) (S U : Polynomial L) :
    Polynomial (Polynomial L) :=
  MvPolynomial.eval₂ Polynomial.C
    (fun i => Polynomial.C (jet S i) + Polynomial.C (jet U i) * Polynomial.X) P

theorem eval_line {L : Type*} [CommRing L] {n : ℕ} (P : JetRow L n) (S U : Polynomial L) (c : L) :
    (line P S U).eval (Polynomial.C c) = atJet P (S + c • U) := by
  change (Polynomial.evalRingHom (Polynomial.C c))
    (MvPolynomial.eval₂ Polynomial.C
      (fun i => Polynomial.C (jet S i) + Polynomial.C (jet U i) * Polynomial.X) P) = _
  rw [MvPolynomial.hom_eval₂]
  have hC : (Polynomial.evalRingHom (Polynomial.C c)).comp Polynomial.C =
      RingHom.id (Polynomial L) := RingHom.ext fun f => by simp
  rw [hC]
  change MvPolynomial.eval _ P = MvPolynomial.eval (jet (S + c • U)) P
  have heq : (fun i : Fin n => (Polynomial.evalRingHom (Polynomial.C c))
      (Polynomial.C (jet S i) + Polynomial.C (jet U i) * Polynomial.X)) =
      jet (S + c • U) := by
    funext i
    simp only [Polynomial.coe_evalRingHom, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, jet, map_add]
    rw [(Polynomial.hasseDeriv i.val).map_smul, Algebra.smul_def, Polynomial.algebraMap_eq,
      mul_comm]
  rw [heq]

/-- Self-contained variable swap on `R[X][Y] →+* R[Y][X]`. -/
private def swapPoly {R : Type*} [CommSemiring R] :
    Polynomial (Polynomial R) →+* Polynomial (Polynomial R) :=
  Polynomial.eval₂RingHom (Polynomial.mapRingHom Polynomial.C) (Polynomial.C Polynomial.X)

private theorem swapPoly_monomial_monomial {R : Type*} [CommSemiring R] (n m : ℕ) (a : R) :
    swapPoly (Polynomial.monomial n (Polynomial.monomial m a)) =
      Polynomial.monomial m (Polynomial.monomial n a) := by
  unfold swapPoly
  rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial]
  simp only [Polynomial.coe_mapRingHom, Polynomial.map_monomial, ← Polynomial.C_pow]
  rw [Polynomial.monomial_mul_C, Polynomial.C_mul_X_pow_eq_monomial]

private theorem swapped_coeff {R : Type*} [CommSemiring R]
    (Q : Polynomial (Polynomial R)) (i j : ℕ) :
    ((swapPoly Q).coeff i).coeff j = (Q.coeff j).coeff i := by
  induction Q using Polynomial.induction_on' with
  | add P Q hp hq => simp [map_add, Polynomial.coeff_add, hp, hq]
  | monomial n P =>
    induction P using Polynomial.induction_on' with
    | add P Q hp hq =>
      rw [map_add, map_add, Polynomial.coeff_add, Polynomial.coeff_add, Polynomial.coeff_add,
        hp, hq, Polynomial.coeff_add]
    | monomial m c =>
      rw [swapPoly_monomial_monomial]
      by_cases hi : m = i <;> by_cases hj : n = j <;> simp [Polynomial.coeff_monomial, hi, hj]

private theorem eval_swapPoly {R : Type*} [CommSemiring R]
    (Q : Polynomial (Polynomial R)) (c : R) :
    (swapPoly Q).map (Polynomial.evalRingHom c) = Q.eval (Polynomial.C c) := by
  induction Q using Polynomial.induction_on' with
  | add P Q hp hq => simp [map_add, Polynomial.eval_add, hp, hq]
  | monomial n P =>
    induction P using Polynomial.induction_on' with
    | add P Q hp hq =>
      rw [map_add, map_add, Polynomial.map_add, Polynomial.eval_add, hp, hq]
    | monomial m a =>
      rw [swapPoly_monomial_monomial, Polynomial.map_monomial, Polynomial.coe_evalRingHom,
        Polynomial.eval_monomial, Polynomial.eval_monomial, ← Polynomial.C_pow,
        Polynomial.monomial_mul_C]

private theorem coeff_contact {L : Type*} [Field L] [Infinite L]
    (Q : Polynomial (Polynomial L)) (x : L) (r : ℕ)
    (h : ∀ c : L, (Polynomial.X - Polynomial.C x) ^ r ∣ Q.eval (Polynomial.C c)) (j : ℕ) :
    (Polynomial.X - Polynomial.C x) ^ r ∣ Q.coeff j := by
  let f : Polynomial L →+* Polynomial L := (Polynomial.taylorAlgHom x).toRingHom
  let A := Q.map f
  have heval (c : L) : A.eval (Polynomial.C c) = Polynomial.taylor x (Q.eval (Polynomial.C c)) := by
    change (Q.map f).eval (Polynomial.C c) = f (Q.eval (Polynomial.C c))
    have hC : f (Polynomial.C c) = Polynomial.C c := Polynomial.taylor_C x c
    rw [← hC, Polynomial.eval_map, Polynomial.eval₂_at_apply, hC]
  have hzero (i : ℕ) (hi : i < r) : (swapPoly A).coeff i = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hz (c : L) : ((swapPoly A).coeff i).eval c = 0 := by
      change Polynomial.evalRingHom c ((swapPoly A).coeff i) = 0
      rw [← Polynomial.coeff_map, eval_swapPoly, heval]
      exact Polynomial.X_pow_dvd_iff.mp
        ((Polynomial.X_pow_dvd_taylor_iff_X_sub_C_pow_dvd _ _ _).mpr (h c)) i hi
    simpa [Polynomial.IsRoot, hz] using (Set.infinite_univ : (Set.univ : Set L).Infinite)
  apply (Polynomial.X_pow_dvd_taylor_iff_X_sub_C_pow_dvd _ _ _).mp
  apply Polynomial.X_pow_dvd_iff.mpr
  intro i hi
  change (f (Q.coeff j)).coeff i = 0
  rw [← Polynomial.coeff_map, ← swapped_coeff, hzero i hi, Polynomial.coeff_zero]

/-- If `Q.eval (C c)` is divisible by `(X - x_i)^r` at all `i ∈ A` for every `c : L` and
`(Q.coeff j).natDegree < r * A.card`, then `Q.coeff j = 0`. -/
theorem line_contacts_zero {L I : Type*} [Field L] [Infinite L]
    (Q : Polynomial (Polynomial L)) (A : Finset I)
    (x : I → L) (hx : Function.Injective x) (r : ℕ)
    (h : ∀ i ∈ A, ∀ c : L, (Polynomial.X - Polynomial.C (x i)) ^ r ∣ Q.eval (Polynomial.C c))
    (j : ℕ) (hdeg : (Q.coeff j).natDegree < r * A.card) : Q.coeff j = 0 := by
  classical
  have hprod_dvd : (∏ i ∈ A, (Polynomial.X - Polynomial.C (x i)) ^ r) ∣ Q.coeff j := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ k _ hik
      exact (isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr (fun he => hik (hx he))).isUnit).pow
    · intro i hi
      exact coeff_contact Q (x i) r (h i hi) j
  by_contra hnz
  have hle := Polynomial.natDegree_le_of_dvd hprod_dvd hnz
  have hdeg_prod : (∏ i ∈ A, (Polynomial.X - Polynomial.C (x i)) ^ r).natDegree = r * A.card := by
    rw [Polynomial.natDegree_prod _ _ (fun i _ => pow_ne_zero _ (Polynomial.X_sub_C_ne_zero (x i)))]
    simp [Polynomial.natDegree_pow, mul_comm]
  omega

private theorem exists_direction {L : Type*} [Field L] {n : ℕ}
    (L_poly : Polynomial L) (x : L) (hx : L_poly.eval x ≠ 0) (v : Fin n → L) :
    ∃ V : Polynomial L, V.natDegree ≤ n - 1 ∧ ∀ i : Fin n, (jet (L_poly * V) i).eval x = v i := by
  classical
  cases n with
  | zero => exact ⟨0, by simp, fun i => Fin.elim0 i⟩
  | succ m =>
    let B := (Polynomial.X - Polynomial.C x) ^ (m + 1)
    have hB : B.Monic := (Polynomial.monic_X_sub_C x).pow _
    have hdeg : B.natDegree = m + 1 := by simp [B, Polynomial.natDegree_pow]
    have hcop : IsCoprime L_poly B := by
      apply (Polynomial.irreducible_X_sub_C x).coprime_pow_of_not_dvd
      simpa [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot] using hx
    obtain ⟨a, b, hab⟩ := hcop
    let P_v : Polynomial L := ∑ j : Fin (m + 1), Polynomial.monomial j.val (v j)
    let F := Polynomial.taylor (-x) P_v
    let V := (a * F) %ₘ B
    have hdiv : B ∣ L_poly * V - F := by
      refine ⟨-(b * F + L_poly * ((a * F) /ₘ B)), ?_⟩
      dsimp only [V]
      rw [Polynomial.modByMonic_eq_sub_mul_div]
      linear_combination F * hab
    have hjet : ∀ i < m + 1, (Polynomial.hasseDeriv i (L_poly * V - F)).eval x = 0 := by
      have ht := (Polynomial.X_pow_dvd_taylor_iff_X_sub_C_pow_dvd (L_poly * V - F) x (m + 1)).mpr hdiv
      have hcoeff := (Polynomial.X_pow_dvd_taylor_iff (L_poly * V - F) x (m + 1)).mp ht
      intro i hi
      simpa only [← Polynomial.taylor_coeff] using hcoeff i hi
    refine ⟨V, ?_, fun i => ?_⟩
    · have hne : B ≠ 1 := by
        intro h
        rw [h, Polynomial.natDegree_one] at hdeg
        omega
      have hsmall := Polynomial.natDegree_modByMonic_lt (a * F) hB hne
      rw [hdeg] at hsmall
      exact Nat.le_of_lt_succ hsmall
    · have h := hjet i.val i.isLt
      rw [map_sub, Polynomial.eval_sub, sub_eq_zero] at h
      change (Polynomial.hasseDeriv i.val (L_poly * V)).eval x = v i
      rw [h, ← Polynomial.taylor_coeff, show F = Polynomial.taylor (-x) P_v from rfl,
        Polynomial.taylor_taylor, add_neg_cancel, Polynomial.taylor_zero]
      simp only [P_v, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hne
        have : j.val ≠ i.val := fun he => hne (Fin.ext he)
        simp [this]
      · intro hnot; exact absurd (Finset.mem_univ i) hnot

private theorem coeff_line_through_zero {L : Type*} [CommRing L] {n : ℕ}
    (P : JetSymbol L n) (v : Fin n → L) (j : ℕ) :
    (MvPolynomial.eval₂ Polynomial.C (fun i => Polynomial.C (v i) * Polynomial.X) P).coeff j =
      MvPolynomial.eval v (MvPolynomial.homogeneousComponent j P) := by
  classical
  rw [MvPolynomial.eval₂_eq, Polynomial.finsetSum_coeff, MvPolynomial.homogeneousComponent_apply]
  change _ = MvPolynomial.eval₂Hom (RingHom.id _) v _
  rw [map_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _
  rw [MvPolynomial.eval₂Hom_monomial]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, ← map_pow (Polynomial.C (R := L)),
    ← map_prod (Polynomial.C (R := L)), ← map_mul (Polynomial.C (R := L)), ← mul_assoc,
    Finset.prod_pow_eq_pow_sum, Polynomial.coeff_C_mul_X_pow, RingHom.id_apply, Finsupp.degree_apply]
  split_ifs <;> simp_all

private theorem line_at_abscissa {L : Type*} [CommRing L] {n : ℕ}
    (P : JetRow L n) (S U : Polynomial L) (x : L) :
    (line P S U).map (Polynomial.evalRingHom x) =
      MvPolynomial.eval₂ Polynomial.C (fun i : Fin n => Polynomial.C ((jet U i).eval x) *
        Polynomial.X) (symbolAt x (shiftJet P S)) := by
  let f := Polynomial.evalRingHom x
  let g (i : Fin n) : Polynomial L := Polynomial.C (f (jet U i)) * Polynomial.X
  change (Polynomial.mapRingHom f) (MvPolynomial.eval₂ Polynomial.C
    (fun i => Polynomial.C (jet S i) + Polynomial.C (jet U i) * Polynomial.X) P) =
    MvPolynomial.eval₂Hom Polynomial.C g
      (MvPolynomial.map f (MvPolynomial.eval₂ MvPolynomial.C
        (fun i => MvPolynomial.X i + MvPolynomial.C (jet S i)) P))
  rw [MvPolynomial.hom_eval₂, MvPolynomial.eval₂Hom_map_hom]
  change _ = MvPolynomial.eval₂Hom (Polynomial.C.comp f) g
    (MvPolynomial.eval₂Hom MvPolynomial.C
      (fun i => MvPolynomial.X i + MvPolynomial.C (jet S i)) P)
  rw [MvPolynomial.map_eval₂Hom]
  have hl : (Polynomial.mapRingHom f).comp Polynomial.C = Polynomial.C.comp f :=
    RingHom.ext fun p => by simp
  have hr : (MvPolynomial.eval₂Hom (Polynomial.C.comp f) g).comp MvPolynomial.C =
      Polynomial.C.comp f := RingHom.ext fun p => by simp
  rw [hl, hr]
  congr 1
  funext i
  simp [g, add_comm]

/-- **`order_of_locator_lines` (`Fast074` generalized to arbitrary jet order `n` and any infinite
field `L`):** if `(line P S (L_poly * V)).coeff j = 0` for every `V` of degree `≤ n - 1` and every
`j < d` (with `L_poly ≠ 0`), then `OrderAt P S d`. -/
theorem order_of_locator_lines {L : Type*} [Field L] [Infinite L] {n : ℕ}
    (P : JetRow L n) (S L_poly : Polynomial L) (hL : L_poly ≠ 0) (d : ℕ)
    (h : ∀ V : Polynomial L, V.natDegree ≤ n - 1 → ∀ j < d, (line P S (L_poly * V)).coeff j = 0) :
    OrderAt P S d := by
  intro m hm
  by_contra! hlt
  have hz (x : L) (hx : L_poly.eval x ≠ 0) : ((shiftJet P S).coeff m).eval x = 0 := by
    let A := symbolAt x (shiftJet P S)
    let Q := MvPolynomial.homogeneousComponent m.degree A
    have hQ : Q = 0 := by
      apply MvPolynomial.funext
      intro v
      rw [map_zero]
      obtain ⟨V, hV, hv⟩ := exists_direction L_poly x hx v
      have heval := congrArg (Polynomial.evalRingHom x) (h V hV m.degree hlt)
      rw [map_zero, ← Polynomial.coeff_map, line_at_abscissa] at heval
      let along (u : Fin n → L) :=
        (MvPolynomial.eval₂ Polynomial.C (fun i => Polynomial.C (u i) * Polynomial.X) A).coeff
          m.degree
      have hdir := congrArg along (funext hv)
      have hvanish : along v = 0 := hdir.symm.trans heval
      simpa only [along, coeff_line_through_zero] using hvanish
    have hcoeff := congrArg (fun F : JetSymbol L n => F.coeff m) hQ
    simpa [Q, MvPolynomial.coeff_homogeneousComponent, A, symbolAt, MvPolynomial.coeff_map]
      using hcoeff
  have hzero : (shiftJet P S).coeff m = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine (Polynomial.finite_setOfPred_isRoot hL).infinite_compl.mono ?_
    intro x hx
    exact hz x hx
  exact MvPolynomial.mem_support_iff.mp hm hzero

/-- Required shift order `(cutoff - T) / layerWidth + 1` at weight layer `T`. -/
def requiredOrder (cutoff layerWidth T : ℕ) : ℕ :=
  (cutoff - T) / layerWidth + 1

private def LineBounded {L : Type*} [CommRing L] (layerWidth : ℕ)
    (Q : Polynomial (Polynomial L)) (b : ℕ) : Prop :=
  ∀ j, (Q.coeff j).natDegree ≤ b + layerWidth * j

private theorem lineBounded_mul {L : Type*} [CommRing L] {layerWidth a b : ℕ}
    {F G : Polynomial (Polynomial L)}
    (hF : LineBounded layerWidth F a) (hG : LineBounded layerWidth G b) :
    LineBounded layerWidth (F * G) (a + b) := by
  intro j
  rw [Polynomial.coeff_mul]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro ij hij
  have hsum := Finset.mem_antidiagonal.mp hij
  refine Polynomial.natDegree_mul_le.trans ((Nat.add_le_add (hF ij.1) (hG ij.2)).trans ?_)
  rw [← hsum, Nat.mul_add]
  omega

private theorem lineBounded_C {L : Type*} [CommRing L] {layerWidth a : ℕ}
    (f : Polynomial L) (hf : f.natDegree ≤ a) :
    LineBounded layerWidth (Polynomial.C f) a := by
  intro j
  by_cases h : j = 0
  · simpa [h] using hf
  · simp [Polynomial.coeff_C, h]

private theorem lineBounded_prod {L ι : Type*} [CommRing L] {layerWidth : ℕ}
    (A : Finset ι) (f : ι → Polynomial (Polynomial L)) (b : ι → ℕ)
    (hf : ∀ i ∈ A, LineBounded layerWidth (f i) (b i)) :
    LineBounded layerWidth (∏ i ∈ A, f i) (∑ i ∈ A, b i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using lineBounded_C (layerWidth := layerWidth) (1 : Polynomial L) (a := 0) (by simp)
  | insert i A hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact lineBounded_mul (hf i (Finset.mem_insert_self _ _))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))

private theorem lineBounded_pow {L : Type*} [CommRing L] {layerWidth b : ℕ}
    {f : Polynomial (Polynomial L)} (hf : LineBounded layerWidth f b) (k : ℕ) :
    LineBounded layerWidth (f ^ k) (b * k) := by
  induction k with
  | zero => simpa using lineBounded_C (layerWidth := layerWidth) (1 : Polynomial L) (a := 0) (by simp)
  | succ k ih =>
    rw [pow_succ, Nat.mul_succ]
    exact lineBounded_mul ih hf

private theorem line_degree {L : Type*} [CommRing L] {n : ℕ}
    (physDeg layerWidth T : ℕ) (hn : n - 1 ≤ physDeg)
    (P : JetRow L n) (S U : Polynomial L)
    (hP : TrueWeightLE physDeg P T) (hS : S.natDegree ≤ physDeg)
    (hU : U.natDegree ≤ physDeg + layerWidth) (j : ℕ) :
    ((line P S U).coeff j).natDegree ≤ T + layerWidth * j := by
  let b (i : Fin n) : ℕ := physDeg - i.val
  let F (i : Fin n) : Polynomial (Polynomial L) :=
    Polynomial.C (jet S i) + Polynomial.C (jet U i) * Polynomial.X
  have hF (i : Fin n) : LineBounded layerWidth (F i) (b i) := by
    intro k
    have hs : (jet S i).natDegree ≤ b i :=
      (Polynomial.natDegree_hasseDeriv_le S i.val).trans (Nat.sub_le_sub_right hS _)
    have hu : (jet U i).natDegree ≤ b i + layerWidth := by
      refine (Polynomial.natDegree_hasseDeriv_le U i.val).trans ((Nat.sub_le_sub_right hU _).trans ?_)
      have hi : i.val ≤ physDeg := by omega
      dsimp only [b]
      omega
    change ((Polynomial.C (jet S i) + Polynomial.C (jet U i) * Polynomial.X).coeff k).natDegree ≤
      b i + layerWidth * k
    rw [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X]
    by_cases h0 : k = 0
    · simpa [h0] using hs
    · by_cases h1 : k = 1
      · simpa [h1] using hu
      · simp [h0, h1]
  unfold line
  rw [MvPolynomial.eval₂_eq, Polynomial.finsetSum_coeff]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  have hterm := lineBounded_mul (lineBounded_C (layerWidth := layerWidth) (P.coeff m) le_rfl)
    (lineBounded_prod m.support (fun i => F i ^ m i) (fun i => b i * m i)
      (fun i _ => lineBounded_pow (hF i) (m i))) j
  exact hterm.trans (Nat.add_le_add_right (hP m hm) _)

/-- **`order_of_contact` (`Final50OrderProof_1` generalized):**
From `TrueWeightLE physDeg P T` and `Contact nodes w m_contact P`, any codeword `S` of degree
`≤ physDeg` agreeing with `w` on `≥ agreement` nodes satisfies
`OrderAt P S ((cutoff - T) / layerWidth + 1)`. -/
theorem order_of_contact {L I : Type*} [Field L] [Infinite L] {n : ℕ}
    (nodes w : I → L) (hnodes : Function.Injective nodes)
    (physDeg agreement m_contact cutoff layerWidth : ℕ)
    (hn : n - 1 ≤ physDeg)
    (hwidth : agreement + (n - 1) ≤ physDeg + layerWidth)
    (hcut : cutoff < m_contact * agreement)
    (P : JetRow L n) {T : ℕ} (hT : T ≤ cutoff)
    (hw : TrueWeightLE physDeg P T) (hc : Contact nodes w m_contact P)
    {S : Polynomial L} (hS : S.natDegree ≤ physDeg)
    {H : Finset I} (hH : agreement ≤ H.card)
    (hits : ∀ i ∈ H, S.eval (nodes i) = w i) :
    OrderAt P S (requiredOrder cutoff layerWidth T) := by
  classical
  obtain ⟨A, hAH, hA⟩ := Finset.exists_subset_card_eq hH
  let Loc := locator nodes A
  apply order_of_locator_lines P S Loc (locator_monic nodes A).ne_zero
  intro V hV j hj
  let U := Loc * V
  have hU : U.natDegree ≤ physDeg + layerWidth := by
    refine Polynomial.natDegree_mul_le.trans ?_
    rw [locator_natDegree nodes A, hA]
    omega
  have hcontact (i : I) (hi : i ∈ A) (c : L) :
      (Polynomial.X - Polynomial.C (nodes i)) ^ m_contact ∣ (line P S U).eval (Polynomial.C c) := by
    rw [eval_line]
    apply hc
    have hL0 : Loc.eval (nodes i) = 0 := locator_eval_zero nodes A hi
    have hU0 : U.eval (nodes i) = 0 := by simp [U, hL0]
    simpa [Polynomial.eval_add, Polynomial.eval_smul, hU0] using hits i (hAH hi)
  have hj' : j ≤ (cutoff - T) / layerWidth := Nat.lt_succ_iff.mp hj
  have hq := Nat.div_mul_le_self (cutoff - T) layerWidth
  rw [Nat.mul_comm _ layerWidth] at hq
  have hdeg_le : ((line P S U).coeff j).natDegree ≤ cutoff := by
    calc ((line P S U).coeff j).natDegree
        ≤ T + layerWidth * j := line_degree physDeg layerWidth T hn P S U hw hS hU j
      _ ≤ T + layerWidth * ((cutoff - T) / layerWidth) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left layerWidth hj') T
      _ ≤ T + (cutoff - T) := Nat.add_le_add_left hq T
      _ = cutoff := Nat.add_sub_of_le hT
  exact line_contacts_zero (line P S U) A nodes hnodes m_contact hcontact j
    (hdeg_le.trans_lt (hA.symm ▸ hcut))

/-! ### Part 3: Fresh Abscissa, Layer Summation, and Exact `bankEval` Rank-Nullity -/

/-- Over any infinite field `L`, given finitely many nodes and finitely many jet rows `f`, there
exists a fresh abscissa `x : L` avoiding all nodes and preserving the exact support of every `f i`. -/
theorem exists_fresh {L I : Type*} [Field L] [Infinite L] [Fintype I] {n m : ℕ}
    (nodes : I → L) (f : Fin m → JetRow L n) :
    ∃ x : L, (∀ i : I, x ≠ nodes i) ∧
      ∀ i, (symbolAt x (f i)).support = (f i).support := by
  classical
  let nodeSet : Finset L := Finset.univ.image nodes
  let rootSet : Finset L := Finset.univ.biUnion fun i : Fin m =>
    (f i).support.biUnion fun u => ((f i).coeff u).roots.toFinset
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset (nodeSet ∪ rootSet)
  rw [Finset.mem_union, not_or] at hx
  refine ⟨x, ?_, fun i => Finset.Subset.antisymm (MvPolynomial.support_map_subset _ _) ?_⟩
  · intro i h
    exact hx.1 (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, h.symm⟩)
  · intro u hu
    rw [MvPolynomial.mem_support_iff]
    change (MvPolynomial.map (Polynomial.evalRingHom x) (f i)).coeff u ≠ 0
    rw [MvPolynomial.coeff_map]
    intro heval
    have hroot : x ∈ ((f i).coeff u).roots :=
      (Polynomial.mem_roots (MvPolynomial.mem_support_iff.mp hu)).mpr heval
    exact hx.2 (Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ _, Finset.mem_biUnion.mpr ⟨u, hu, Multiset.mem_toFinset.mpr hroot⟩⟩)

/-- Layer grouping inequality (`PortLowBase.sum_by_layer`):
`∑_{T ≤ W} cost((W - T) / E) ≤ E * ∑_{k ≤ W / E} cost(k)`. -/
theorem sum_by_layer (W E : ℕ) (hE : 0 < E) (cost : ℕ → ℕ) :
    (∑ T ∈ Finset.range (W + 1), cost ((W - T) / E)) ≤
      E * ∑ k ∈ Finset.range (1 + W / E), cost k := by
  let S := Finset.range (W + 1)
  let R := Finset.range (1 + W / E)
  let U := Finset.range E
  let pair (T : ℕ) : ℕ × ℕ := ((W - T) / E, (W - T) % E)
  have hmem : ∀ T ∈ S, pair T ∈ R ×ˢ U := by
    intro T _
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_range.mpr (by
        change (W - T) / E < 1 + W / E
        have h : (W - T) / E ≤ W / E := Nat.div_le_div_right (Nat.sub_le W T)
        omega),
      Finset.mem_range.mpr (Nat.mod_lt _ hE)⟩
  have hinj : Set.InjOn pair (↑S : Set ℕ) := by
    intro T hT V hV h
    have hT' : T < W + 1 := Finset.mem_range.mp hT
    have hV' : V < W + 1 := Finset.mem_range.mp hV
    have he : W - T = W - V := by
      have ht := Nat.mod_add_div (W - T) E
      have hv := Nat.mod_add_div (W - V) E
      have hfst := congrArg Prod.fst h
      have hsnd := congrArg Prod.snd h
      change (W - T) / E = (W - V) / E at hfst
      change (W - T) % E = (W - V) % E at hsnd
      rw [hsnd, hfst, hv] at ht
      exact ht.symm
    omega
  calc _ ≤ ∑ p ∈ R ×ˢ U, cost p.1 := by
        refine Finset.sum_le_sum_of_injOn pair hinj ?_ (fun _ _ => le_rfl)
          (fun _ _ _ => Nat.zero_le _)
        intro p hp
        obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hp
        exact hmem T hT
    _ = _ := by rw [Finset.sum_product, Finset.mul_sum]; simp [U, R]

/-- If `symbolAt x P = 0`, then `P` is divisible by `MvPolynomial.C (X - C x)`. -/
theorem divide_specialization {L : Type*} [Field L] {n : ℕ}
    (P : JetRow L n) (x : L) (hP : symbolAt x P = 0) :
    ∃ Q : JetRow L n, MvPolynomial.C (Polynomial.X - Polynomial.C x) * Q = P := by
  classical
  let lin : Polynomial L := Polynomial.X - Polynomial.C x
  let Q : JetRow L n := ∑ u ∈ P.support, MvPolynomial.monomial u (P.coeff u /ₘ lin)
  refine ⟨Q, MvPolynomial.ext _ _ fun m => ?_⟩
  rw [MvPolynomial.coeff_C_mul]
  have hQcoeff : Q.coeff m = if m ∈ P.support then P.coeff m /ₘ lin else 0 := by
    simp only [Q, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
  rw [hQcoeff]
  by_cases hm : m ∈ P.support
  · rw [ite_eq_left hm]
    have hroot : (P.coeff m).eval x = 0 := by
      have h := congrArg (fun B : JetSymbol L n => B.coeff m) hP
      change (symbolAt x P).coeff m = (0 : JetSymbol L n).coeff m at h
      rw [symbolAt, MvPolynomial.coeff_map] at h
      exact h
    exact Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot
  · rw [ite_eq_right hm, mul_zero]
    exact (MvPolynomial.notMem_support_iff.mp hm).symm

theorem support_linear_mul {L : Type*} [Field L] {n : ℕ} (x : L) (P : JetRow L n) :
    (MvPolynomial.C (Polynomial.X - Polynomial.C x) * P).support = P.support := by
  ext m
  rw [MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul]
  exact mul_ne_zero_iff.trans (and_iff_right (Polynomial.X_sub_C_ne_zero x))

/-- Generic bank-row predicate at weight layer `T`: support inside a finite exponent set `Supp`,
`TrueWeightLE physDeg P T`, and `Contact nodes w m_contact P`. -/
def BankRow {L I : Type*} [CommRing L] {n : ℕ}
    (physDeg : ℕ) (nodes w : I → L) (m_contact : ℕ)
    (Supp : Finset (Fin n →₀ ℕ)) (T : ℕ) (P : JetRow L n) : Prop :=
  (∀ m ∈ P.support, m ∈ Supp) ∧ TrueWeightLE physDeg P T ∧ Contact nodes w m_contact P

private def jetEval {L : Type*} [CommRing L] {n : ℕ} (S : Polynomial L) :
    JetRow L n →ₗ[L] Polynomial L :=
  (MvPolynomial.aeval (jet S)).toLinearMap.restrictScalars L

private def bankSubmodule {L I : Type*} [Field L] {n : ℕ}
    (physDeg : ℕ) (nodes w : I → L) (m_contact : ℕ)
    (Supp : Finset (Fin n →₀ ℕ)) (T : ℕ) : Submodule L (JetRow L n) where
  carrier := {P | BankRow physDeg nodes w m_contact Supp T P}
  zero_mem' := by
    refine ⟨by simp, by simp [TrueWeightLE], ?_⟩
    intro i S _; simp [atJet]
  add_mem' {P Q} hP hQ := by
    refine ⟨?_, ?_, ?_⟩
    · intro m hm
      rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
      · exact hP.1 m h
      · exact hQ.1 m h
    · intro m hm
      have hdeg (R : JetRow L n) (hR : TrueWeightLE physDeg R T) :
          (R.coeff m).natDegree ≤ T - m.sum (fun i a => (physDeg - i.val) * a) := by
        by_cases h : m ∈ R.support
        · have := hR m h; omega
        · rw [MvPolynomial.notMem_support_iff.mp h, Polynomial.natDegree_zero]; exact Nat.zero_le _
      have hwt : m.sum (fun i a => (physDeg - i.val) * a) ≤ T := by
        rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
        · have := hP.2.1 m h; omega
        · have := hQ.2.1 m h; omega
      have hsum : ((P + Q).coeff m).natDegree ≤ max (P.coeff m).natDegree (Q.coeff m).natDegree :=
        Polynomial.natDegree_add_le _ _
      have := hsum.trans (max_le (hdeg P hP.2.1) (hdeg Q hQ.2.1))
      omega
    · intro i S hS
      change (Polynomial.X - Polynomial.C (nodes i)) ^ m_contact ∣ jetEval S (P + Q)
      rw [map_add]
      exact dvd_add (hP.2.2 i S hS) (hQ.2.2 i S hS)
  smul_mem' c P hP := by
    refine ⟨fun m hm => hP.1 m (MvPolynomial.support_smul hm), ?_, ?_⟩
    · intro m hm
      have hw := hP.2.1 m (MvPolynomial.support_smul hm)
      rw [MvPolynomial.coeff_smul]
      exact (Nat.add_le_add_right (Polynomial.natDegree_smul_le c (P.coeff m)) _).trans hw
    · intro i S hS
      have h : atJet (c • P) S = c • atJet P S := (jetEval S).map_smul c P
      rw [h, Polynomial.smul_eq_C_mul]
      exact (hP.2.2 i S hS).mul_left _

private instance finiteBankSubmodule {L I : Type*} [Field L] {n : ℕ}
    (physDeg : ℕ) (nodes w : I → L) (m_contact : ℕ)
    (Supp : Finset (Fin n →₀ ℕ)) (T : ℕ) :
    Module.Finite L (bankSubmodule physDeg nodes w m_contact Supp T) := by
  classical
  let coeffArr : JetRow L n →ₗ[L] ((↥Supp × Fin (T + 1)) → L) :=
    LinearMap.pi fun u =>
      (Polynomial.lcoeff L u.2.val).comp
        ((MvPolynomial.lcoeff (Polynomial L) u.1.val :
          JetRow L n →ₗ[Polynomial L] Polynomial L).restrictScalars L)
  let f := coeffArr.comp (bankSubmodule physDeg nodes w m_contact Supp T).subtype
  have hzero (Q : bankSubmodule physDeg nodes w m_contact Supp T) (hQ : f Q = 0) : Q = 0 := by
    apply Subtype.ext
    apply MvPolynomial.ext
    intro m
    change Q.val.coeff m = 0
    by_contra hnz
    have hm := MvPolynomial.mem_support_iff.mpr hnz
    have hSupp : m ∈ Supp := Q.property.1 m hm
    have hT : (Q.val.coeff m).natDegree ≤ T := (Nat.le_add_right _ _).trans (Q.property.2.1 m hm)
    apply hnz
    ext k
    rw [Polynomial.coeff_zero]
    by_cases hk : k < T + 1
    · exact congrFun hQ (⟨m, hSupp⟩, ⟨k, hk⟩)
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  apply Module.Finite.of_injective f
  intro P Q h
  apply sub_eq_zero.mp
  have hz := f.map_sub P Q
  rw [h, sub_self] at hz
  exact hzero (P - Q) hz

/-- **`symbol_families` (`Final50OrderProof_3` generalized):**
At any fresh abscissa `x` avoiding `nodes`, exact rank-nullity on `bankEval T : bank T → JetSymbol`
(`ker(bankEval (T + 1)) = (X - x) * bank T`) produces layer ranks `r T` summing to at least
`sourceRank`, together with `r T` linearly independent `symbolAt x (e i)` at every layer `T`. -/
theorem symbol_families {L I : Type*} [Field L] {n : ℕ}
    (physDeg : ℕ) (nodes w : I → L) (m_contact : ℕ)
    (Supp : Finset (Fin n →₀ ℕ)) (cutoff sourceRank : ℕ) (x : L)
    (hx : ∀ i : I, x ≠ nodes i)
    (hr : ∃ e : Fin sourceRank → JetRow L n, LinearIndependent L e ∧
      ∀ i, BankRow physDeg nodes w m_contact Supp cutoff (e i)) :
    ∃ r : ℕ → ℕ, sourceRank ≤ ∑ T ∈ Finset.range (cutoff + 1), r T ∧
      ∀ T ≤ cutoff, ∃ e : Fin (r T) → JetRow L n,
        (∀ i, BankRow physDeg nodes w m_contact Supp T (e i)) ∧
        LinearIndependent L (fun i => symbolAt x (e i)) := by
  classical
  let bank (T : ℕ) := bankSubmodule physDeg nodes w m_contact Supp T
  let bankEval (T : ℕ) : bank T →ₗ[L] JetSymbol L n := (symbolLinear x).comp (bank T).subtype
  have hmul_iff (T : ℕ) (P : JetRow L n) :
      BankRow physDeg nodes w m_contact Supp (T + 1)
        (MvPolynomial.C (Polynomial.X - Polynomial.C x) * P) ↔
      BankRow physDeg nodes w m_contact Supp T P := by
    unfold BankRow TrueWeightLE Contact
    rw [support_linear_mul]
    refine and_congr Iff.rfl (and_congr ?_ ?_)
    · refine forall_congr' fun m => forall_congr' fun hm => ?_
      rw [MvPolynomial.coeff_C_mul,
        Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero x) (MvPolynomial.mem_support_iff.mp hm),
        Polynomial.natDegree_X_sub_C]
      omega
    · simp only [atJet, map_mul, MvPolynomial.eval_C]
      refine forall_congr' fun i => forall_congr' fun S => forall_congr' fun _ => ?_
      have hc : IsCoprime (Polynomial.X - Polynomial.C (nodes i)) (Polynomial.X - Polynomial.C x) :=
        isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr (hx i).symm).isUnit
      exact hc.pow_left.dvd_mul_left_iff
  have hker0 : LinearMap.ker (bankEval 0) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro P hP
    obtain ⟨Q, hQ⟩ := divide_specialization P.val x hP
    apply Subtype.ext
    change P.val = 0
    rw [← hQ]
    suffices Q = 0 by simp [this]
    apply MvPolynomial.ext
    intro m
    change Q.coeff m = 0
    by_contra hnz
    have hm : m ∈ P.val.support := by
      rw [← hQ, support_linear_mul]
      exact MvPolynomial.mem_support_iff.mpr hnz
    have h := P.property.2.1 m hm
    rw [← hQ, MvPolynomial.coeff_C_mul,
      Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero x) hnz,
      Polynomial.natDegree_X_sub_C] at h
    omega
  have hker_succ (T : ℕ) :
      Module.finrank L (LinearMap.ker (bankEval (T + 1))) = Module.finrank L (bank T) := by
    let multLin : bank T →ₗ[L] bank (T + 1) :=
      LinearMap.codRestrict (bank (T + 1))
        ((LinearMap.mulLeft L (MvPolynomial.C (Polynomial.X - Polynomial.C x))).comp (bank T).subtype)
        (fun P => (hmul_iff T P.val).mpr P.property)
    let Lmap : bank T →ₗ[L] LinearMap.ker (bankEval (T + 1)) :=
      LinearMap.codRestrict _ multLin fun P => by
        rw [LinearMap.mem_ker]
        change symbolAt (n := n) x (MvPolynomial.C (Polynomial.X - Polynomial.C x) * P.val) = 0
        have h0 : symbolAt (n := n) x (MvPolynomial.C (Polynomial.X - Polynomial.C x)) = 0 := by
          simp [symbolAt]
        rw [RingHom.map_mul, h0, zero_mul]
    have hbij : Function.Bijective Lmap := by
      have hnz : (MvPolynomial.C (Polynomial.X - Polynomial.C x) : JetRow L n) ≠ 0 :=
        MvPolynomial.C_ne_zero.mpr (Polynomial.X_sub_C_ne_zero x)
      constructor
      · intro P Q h
        apply Subtype.ext
        have heq := congrArg (fun V : LinearMap.ker (bankEval (T + 1)) => V.val.val) h
        exact mul_left_cancel₀ hnz heq
      · intro P
        have h : symbolAt x P.val.val = 0 := LinearMap.mem_ker.mp P.property
        obtain ⟨Q, hQ⟩ := divide_specialization P.val.val x h
        have hmem : BankRow physDeg nodes w m_contact Supp (T + 1)
            (MvPolynomial.C (Polynomial.X - Polynomial.C x) * Q) := by
          rw [hQ]; exact P.val.property
        exact ⟨⟨Q, (hmul_iff T Q).mp hmem⟩, Subtype.ext (Subtype.ext hQ)⟩
    exact (LinearEquiv.ofBijective Lmap hbij).finrank_eq.symm
  let r (T : ℕ) := Module.finrank L (LinearMap.range (bankEval T))
  refine ⟨r, ?_, fun T _ => ?_⟩
  · have heq (T : ℕ) : Module.finrank L (bank T) = ∑ V ∈ Finset.range (T + 1), r V := by
      induction T with
      | zero =>
        have h := LinearMap.finrank_range_add_finrank_ker
          (K := L) (V := bank 0) (V₂ := JetSymbol L n) (bankEval 0)
        rw [hker0, finrank_bot, Nat.add_zero] at h
        simpa only [Nat.zero_add, Finset.sum_range_one] using h.symm
      | succ T ih =>
        have h := LinearMap.finrank_range_add_finrank_ker
          (K := L) (V := bank (T + 1)) (V₂ := JetSymbol L n) (bankEval (T + 1))
        rw [hker_succ T, ih, Nat.add_comm] at h
        rw [Finset.sum_range_succ]
        exact h.symm
    obtain ⟨e, he, hmem⟩ := hr
    have hi : LinearIndependent L (fun i => (⟨e i, hmem i⟩ : bank cutoff)) :=
      LinearIndependent.of_comp (bank cutoff).subtype he
    rw [← heq]
    simpa only [Fintype.card_fin] using hi.fintype_card_le_finrank
  · let b := Module.finBasis L (LinearMap.range (bankEval T))
    choose e he using fun i : Fin (r T) => LinearMap.mem_range.mp (b i).property
    refine ⟨fun i => (e i).val, fun i => (e i).property, ?_⟩
    have h : LinearIndependent L (fun i => (b i).val) :=
      b.linearIndependent.map' (LinearMap.range (bankEval T)).subtype
        (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    have heq : (fun i => symbolAt x (e i).val) = fun i => (b i).val := funext he
    rwa [heq]

/-! ### Part 4: Weighted Cofactor Rank & Tighter `d = 1` Specialization -/

private def wdEmbed {σ : Type*} (wt : σ → ℕ) : (σ →₀ ℕ) →+ (Option σ →₀ ℕ) where
  toFun d := d.optionElim (Finsupp.weight wt d)
  map_zero' := by ext i; cases i <;> simp
  map_add' d e := by ext i; cases i <;> simp

private theorem wdEmbed_injective {σ : Type*} (wt : σ → ℕ) : Function.Injective (wdEmbed wt) := by
  intro d e h
  have := congrArg Finsupp.some h
  simpa [wdEmbed] using this

private def wdLift {σ R : Type*} [CommSemiring R] (wt : σ → ℕ) :
    MvPolynomial σ R →+* MvPolynomial (Option σ) R :=
  AddMonoidAlgebra.mapDomainRingHom R (wdEmbed wt)

private theorem wdLift_injective {σ R : Type*} [CommSemiring R] (wt : σ → ℕ) :
    Function.Injective (wdLift (R := R) wt) :=
  AddMonoidAlgebra.mapDomain_injective (wdEmbed_injective wt)

private theorem degreeOf_wdLift {σ R : Type*} [CommSemiring R] (wt : σ → ℕ)
    (p : MvPolynomial σ R) :
    (wdLift wt p).degreeOf none = MvPolynomial.weightedTotalDegree wt p := by
  classical
  have hs : (wdLift wt p).support = p.support.image (wdEmbed wt) :=
    Finsupp.mapDomain_support_of_injective (wdEmbed_injective wt) _
  rw [MvPolynomial.degreeOf_eq_sup, hs, Finset.sup_image]
  simp [Function.comp_def, wdEmbed, MvPolynomial.weightedTotalDegree]

theorem weightedTotalDegree_mul_of_noZeroDivisors {σ R : Type*} [CommSemiring R]
    [NoZeroDivisors R] (wt : σ → ℕ) (p q : MvPolynomial σ R) (hp : p ≠ 0) (hq : q ≠ 0) :
    MvPolynomial.weightedTotalDegree wt (p * q) =
      MvPolynomial.weightedTotalDegree wt p + MvPolynomial.weightedTotalDegree wt q := by
  have hp' : wdLift wt p ≠ 0 := fun h => hp (wdLift_injective wt (h.trans (map_zero _).symm))
  have hq' : wdLift wt q ≠ 0 := fun h => hq (wdLift_injective wt (h.trans (map_zero _).symm))
  rw [← degreeOf_wdLift wt (p * q), map_mul, MvPolynomial.degreeOf_mul_eq hp' hq',
    degreeOf_wdLift, degreeOf_wdLift]

theorem weightedTotalDegree_prod_of_noZeroDivisors {σ R ι : Type*} [CommSemiring R]
    [NoZeroDivisors R] (wt : σ → ℕ) (s : Finset ι) (f : ι → MvPolynomial σ R)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    MvPolynomial.weightedTotalDegree wt (∏ i ∈ s, f i) =
      ∑ i ∈ s, MvPolynomial.weightedTotalDegree wt (f i) := by
  have hf' : ∀ i ∈ s, wdLift wt (f i) ≠ 0 := fun i hi h =>
    hf i hi (wdLift_injective wt (h.trans (map_zero _).symm))
  rw [← degreeOf_wdLift wt (∏ i ∈ s, f i), map_prod, MvPolynomial.degreeOf_prod_eq s _ hf']
  simp only [degreeOf_wdLift]

private theorem weightedTotalDegree_pow {σ R : Type*} [CommSemiring R] [NoZeroDivisors R]
    (wt : σ → ℕ) (P : MvPolynomial σ R) (hP : P ≠ 0) (a : ℕ) :
    MvPolynomial.weightedTotalDegree wt (P ^ a) = a * MvPolynomial.weightedTotalDegree wt P := by
  induction a with
  | zero =>
    rw [pow_zero, zero_mul, ← MvPolynomial.C_1, MvPolynomial.weightedTotalDegree_C]
  | succ a ih =>
    rw [pow_succ, weightedTotalDegree_mul_of_noZeroDivisors wt _ _ (pow_ne_zero _ hP) hP,
      ih, Nat.succ_mul]

/-- **General Dual-Weight Cofactor Rank Bound (`Fast070` `cofactor_rank` upgraded to arbitrary
weights):** if `e : Fin r → JetSymbol L n` are `L`-linearly independent, every `e i` is divisible by
`∏ j, F j ^ a j`, and satisfies `weightedTotalDegree wt₁ (e i) ≤ B₁` and
`weightedTotalDegree wt₂ (e i) ≤ B₂`, then `r` is bounded by the size of the residual exponent set
`S` whenever every exponent `u` with `u.weight wt₁ + W₁ ≤ B₁` and `u.weight wt₂ + W₂ ≤ B₂` lies in
`S` (and `r = 0` if `W₁ > B₁` or `W₂ > B₂`). -/
theorem cofactor_rank_weighted {L : Type*} [Field L] {n m r : ℕ}
    (wt₁ wt₂ : Fin n → ℕ) (B₁ B₂ : ℕ)
    (F : Fin m → JetSymbol L n) (a : Fin m → ℕ) (hF : ∀ j, F j ≠ 0)
    (e : Fin r → JetSymbol L n) (hli : LinearIndependent L e)
    (hcap : ∀ i, MvPolynomial.weightedTotalDegree wt₁ (e i) ≤ B₁ ∧
      MvPolynomial.weightedTotalDegree wt₂ (e i) ≤ B₂ ∧
      (∏ j, F j ^ a j) ∣ e i)
    (S : Finset (Fin n →₀ ℕ))
    (hS : ∀ u : Fin n →₀ ℕ,
      u.weight wt₁ + (∑ j, a j * MvPolynomial.weightedTotalDegree wt₁ (F j)) ≤ B₁ →
      u.weight wt₂ + (∑ j, a j * MvPolynomial.weightedTotalDegree wt₂ (F j)) ≤ B₂ →
      u ∈ S) :
    r ≤ if (∑ j, a j * MvPolynomial.weightedTotalDegree wt₁ (F j)) ≤ B₁ ∧
           (∑ j, a j * MvPolynomial.weightedTotalDegree wt₂ (F j)) ≤ B₂
        then S.card else 0 := by
  classical
  by_cases hr : r = 0
  · simp [hr]
  let P := ∏ j, F j ^ a j
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (hF j)
  have hdeg (wt : Fin n → ℕ) : MvPolynomial.weightedTotalDegree wt P =
      ∑ j, a j * MvPolynomial.weightedTotalDegree wt (F j) := by
    rw [weightedTotalDegree_prod_of_noZeroDivisors wt Finset.univ _ (fun j _ => pow_ne_zero _ (hF j))]
    exact Finset.sum_congr rfl fun j _ => weightedTotalDegree_pow wt (F j) (hF j) (a j)
  choose Q hQ using fun i => (hcap i).2.2
  have hQ_ne (i : Fin r) : Q i ≠ 0 := fun hz => hli.ne_zero i (by rw [hQ i, hz, mul_zero])
  have hliQ : LinearIndependent L Q := by
    refine LinearIndependent.of_comp (LinearMap.mulLeft L P) ?_
    have heq : (LinearMap.mulLeft L P) ∘ Q = e := funext fun i => (hQ i).symm
    rwa [heq]
  have hbounds (i : Fin r) :
      (∑ j, a j * MvPolynomial.weightedTotalDegree wt₁ (F j)) +
        MvPolynomial.weightedTotalDegree wt₁ (Q i) ≤ B₁ ∧
      (∑ j, a j * MvPolynomial.weightedTotalDegree wt₂ (F j)) +
        MvPolynomial.weightedTotalDegree wt₂ (Q i) ≤ B₂ := by
    obtain ⟨h1, h2, _⟩ := hcap i
    rw [hQ i, weightedTotalDegree_mul_of_noZeroDivisors wt₁ _ _ hP (hQ_ne i), hdeg wt₁] at h1
    rw [hQ i, weightedTotalDegree_mul_of_noZeroDivisors wt₂ _ _ hP (hQ_ne i), hdeg wt₂] at h2
    exact ⟨h1, h2⟩
  have h0 := hbounds ⟨0, Nat.pos_of_ne_zero hr⟩
  have hcond : (∑ j, a j * MvPolynomial.weightedTotalDegree wt₁ (F j)) ≤ B₁ ∧
      (∑ j, a j * MvPolynomial.weightedTotalDegree wt₂ (F j)) ≤ B₂ := ⟨by omega, by omega⟩
  rw [ite_eq_left hcond]
  let V : Submodule L (JetSymbol L n) := MvPolynomial.restrictSupport L (↑S : Set (Fin n →₀ ℕ))
  have hmem (i : Fin r) : Q i ∈ V := by
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro u hu
    rw [Finset.mem_coe]
    have hu1 : u.weight wt₁ ≤ MvPolynomial.weightedTotalDegree wt₁ (Q i) :=
      Finset.le_sup (f := fun u => u.weight wt₁) hu
    have hu2 : u.weight wt₂ ≤ MvPolynomial.weightedTotalDegree wt₂ (Q i) :=
      Finset.le_sup (f := fun u => u.weight wt₂) hu
    have hb := hbounds i
    exact hS u (by omega) (by omega)
  have : Module.Finite L V :=
    Module.Finite.of_basis
      (MvPolynomial.basisRestrictSupport (R := L) (s := (↑S : Set (Fin n →₀ ℕ))))
  have hfin : Module.finrank L V = S.card := by
    dsimp only [V]
    rw [Module.finrank_eq_card_basis
      (MvPolynomial.basisRestrictSupport (R := L) (s := (↑S : Set (Fin n →₀ ℕ))))]
    exact Fintype.card_coe S
  have hliV : LinearIndependent L (fun i => (⟨Q i, hmem i⟩ : V)) :=
    LinearIndependent.of_comp V.subtype hliQ
  have := hliV.fintype_card_le_finrank
  simpa only [Fintype.card_fin, hfin] using this

/-- Tighter `#142` first-order (`d = 1`, `n = 2`) weighted residual symbol count:
number of pairs `(b₀, b₁)` with `w * b₀ + (w - 1) * b₁ ≤ T_rem` and `b₁ ≤ s_rem`. -/
def d1ResidualCount (w T_rem s_rem : ℕ) : ℕ :=
  ∑ b₁ ∈ Finset.range (s_rem + 1),
    if (w - 1) * b₁ ≤ T_rem then (T_rem - (w - 1) * b₁) / w + 1 else 0

/-- Tighter `#142` `d = 1` cofactor rank bound: for `w ≥ 2`, `e : Fin r → JetSymbol L 2` linearly
independent with `wt_{(w, w-1)}(e i) ≤ T`, `deg_{Y₁}(e i) ≤ s`, and `(∏ F_j^(a_j)) ∣ e i`,
`r ≤ d1ResidualCount w (T - ∑ a_j W_j) (s - ∑ a_j d_j)` (or `0` when weights exceed `T` or `s`). -/
theorem cofactor_rank_d1 {L : Type*} [Field L] {m r : ℕ} (w T s : ℕ) (hw : 2 ≤ w)
    (F : Fin m → JetSymbol L 2) (a : Fin m → ℕ) (hF : ∀ j, F j ≠ 0)
    (e : Fin r → JetSymbol L 2) (hli : LinearIndependent L e)
    (hcap : ∀ i, MvPolynomial.weightedTotalDegree ![w, w - 1] (e i) ≤ T ∧
      MvPolynomial.weightedTotalDegree ![0, 1] (e i) ≤ s ∧
      (∏ j, F j ^ a j) ∣ e i) :
    r ≤ if (∑ j, a j * MvPolynomial.weightedTotalDegree ![w, w - 1] (F j)) ≤ T ∧
           (∑ j, a j * MvPolynomial.weightedTotalDegree ![0, 1] (F j)) ≤ s
        then d1ResidualCount w
          (T - ∑ j, a j * MvPolynomial.weightedTotalDegree ![w, w - 1] (F j))
          (s - ∑ j, a j * MvPolynomial.weightedTotalDegree ![0, 1] (F j))
        else 0 := by
  classical
  let W_sum := ∑ j, a j * MvPolynomial.weightedTotalDegree ![w, w - 1] (F j)
  let D_sum := ∑ j, a j * MvPolynomial.weightedTotalDegree ![0, 1] (F j)
  let T_rem := T - W_sum
  let s_rem := s - D_sum
  let pairs : Finset (Σ _ : ℕ, ℕ) :=
    (Finset.range (s_rem + 1)).sigma fun b₁ =>
      Finset.range (if (w - 1) * b₁ ≤ T_rem then (T_rem - (w - 1) * b₁) / w + 1 else 0)
  let mkExp (p : Σ _ : ℕ, ℕ) : Fin 2 →₀ ℕ :=
    Finsupp.single (0 : Fin 2) p.2 + Finsupp.single (1 : Fin 2) p.1
  have hmk_inj : Function.Injective mkExp := by
    intro p q h
    have h0 := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h
    have h1 := congrArg (fun f : Fin 2 →₀ ℕ => f 1) h
    simp [mkExp] at h0 h1
    cases p; cases q; simp_all
  let S : Finset (Fin 2 →₀ ℕ) := pairs.image mkExp
  have hScard : S.card = d1ResidualCount w T_rem s_rem := by
    rw [Finset.card_image_of_injective pairs hmk_inj]
    simp [pairs, d1ResidualCount, Finset.card_sigma]
  rw [← hScard]
  apply cofactor_rank_weighted ![w, w - 1] ![0, 1] T s F a hF e hli hcap S
  intro u hu1 hu2
  have huw : u.weight ![w, w - 1] = u 0 * w + u 1 * (w - 1) := by
    simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two, smul_eq_mul]
  have hud : u.weight ![0, 1] = u 1 := by
    simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two, smul_eq_mul]
  rw [huw] at hu1
  rw [hud] at hu2
  refine Finset.mem_image.mpr ⟨⟨u 1, u 0⟩, ?_, ?_⟩
  · rw [Finset.mem_sigma, Finset.mem_range, Finset.mem_range]
    dsimp only
    have hcomm1 : (w - 1) * u 1 = u 1 * (w - 1) := Nat.mul_comm _ _
    have h1 : u 1 ≤ s_rem := by dsimp [s_rem, D_sum]; omega
    have h2 : (w - 1) * u 1 ≤ T_rem := by dsimp [T_rem, W_sum]; omega
    have h3 : u 0 ≤ (T_rem - (w - 1) * u 1) / w := by
      rw [Nat.le_div_iff_mul_le (by omega : 0 < w)]
      dsimp [T_rem, W_sum]; omega
    exact ⟨by omega, by rw [ite_eq_left h2]; omega⟩
  · ext i; fin_cases i <;> simp [mkExp]

/-! ### Part 5: Master Availability & Layer-Budget Theorem (`Final50OrderProof.of_children`) -/

/-- Minimal availability order extraction (`Final50OrderProof.exists_availability`):
for any irreducible `f` and proper-cut provider `hcut_step`, there exists `l : ℕ` such that
`f^(requiredOrder cutoff layerWidth T - l) ∣ P` for every `BankRow` `P` at layer `T ≤ cutoff`,
and `0 < l → ProperCut f l`. -/
theorem exists_availability {L I : Type*} [Field L] {n : ℕ}
    (physDeg : ℕ) (nodes w : I → L) (m_contact : ℕ)
    (Supp : Finset (Fin n →₀ ℕ)) (cutoff layerWidth : ℕ)
    (ProperCut : JetRow L n → ℕ → Prop)
    (hcut_step : ∀ (f P : JetRow L n) (T a : ℕ), T ≤ cutoff →
      BankRow physDeg nodes w m_contact Supp T P → Irreducible f →
      a < requiredOrder cutoff layerWidth T → f ^ a ∣ P → ¬ f ^ (a + 1) ∣ P →
      ProperCut f (requiredOrder cutoff layerWidth T - a))
    {f : JetRow L n} (hirr : Irreducible f) :
    ∃ l : ℕ, (∀ T ≤ cutoff, ∀ P, BankRow physDeg nodes w m_contact Supp T P →
        f ^ (requiredOrder cutoff layerWidth T - l) ∣ P) ∧
      (0 < l → ProperCut f l) := by
  classical
  let admissible (l : ℕ) : Prop :=
    ∀ T ≤ cutoff, ∀ P, BankRow physDeg nodes w m_contact Supp T P →
      f ^ (requiredOrder cutoff layerWidth T - l) ∣ P
  have hex : ∃ l, admissible l := by
    refine ⟨cutoff / layerWidth + 1, fun T _ P _ => ?_⟩
    have hle : requiredOrder cutoff layerWidth T ≤ cutoff / layerWidth + 1 :=
      Nat.add_le_add_right (Nat.div_le_div_right (Nat.sub_le _ _)) _
    rw [Nat.sub_eq_zero_of_le hle, pow_zero]
    exact one_dvd P
  let l := Nat.find hex
  have hl : admissible l := Nat.find_spec hex
  refine ⟨l, hl, fun hlpos => ?_⟩
  have hbad : ¬ admissible (l - 1) := Nat.find_min hex (by omega)
  dsimp only [admissible] at hbad
  push Not at hbad
  obtain ⟨T, hT, P, hP, hnext⟩ := hbad
  have hle : l ≤ requiredOrder cutoff layerWidth T := by
    by_contra! hlt
    have heq : requiredOrder cutoff layerWidth T - (l - 1) = 0 := by omega
    exact hnext (by rw [heq, pow_zero]; exact one_dvd P)
  have hstep : requiredOrder cutoff layerWidth T - (l - 1) =
      (requiredOrder cutoff layerWidth T - l) + 1 := by omega
  have hcut := hcut_step f P T (requiredOrder cutoff layerWidth T - l) hT hP hirr
    (by omega) (hl T hT P hP) (by rwa [hstep] at hnext)
  have heq : requiredOrder cutoff layerWidth T - (requiredOrder cutoff layerWidth T - l) = l := by
    omega
  rwa [heq] at hcut

/-- **`of_children` (`Final50OrderProof.of_children` generalized):**
Combines `exists_availability`, `exists_fresh`, `symbol_families`, `sum_by_layer`, and any
layer-cost bound `hcost` into the master layer-budget inequality:
`sourceRank ≤ layerWidth * ∑ k < 1 + cutoff / layerWidth, cost l k`. -/
theorem of_children {L I : Type*} [Field L] [Infinite L] [Fintype I] {n m : ℕ}
    (physDeg : ℕ) (nodes w : I → L) (m_contact : ℕ)
    (Supp : Finset (Fin n →₀ ℕ)) (cutoff layerWidth sourceRank : ℕ) (hlw : 0 < layerWidth)
    (ProperCut : JetRow L n → ℕ → Prop)
    (hcut_step : ∀ (f P : JetRow L n) (T a : ℕ), T ≤ cutoff →
      BankRow physDeg nodes w m_contact Supp T P → Irreducible f →
      a < requiredOrder cutoff layerWidth T → f ^ a ∣ P → ¬ f ^ (a + 1) ∣ P →
      ProperCut f (requiredOrder cutoff layerWidth T - a))
    (hr : ∃ e : Fin sourceRank → JetRow L n, LinearIndependent L e ∧
      ∀ i, BankRow physDeg nodes w m_contact Supp cutoff (e i))
    (f : Fin m → JetRow L n)
    (hirr : ∀ i, Irreducible (f i))
    (hdiff : ∀ i j, i ≠ j → ¬ Associated (f i) (f j))
    (cost : (Fin m → ℕ) → ℕ → ℕ)
    (hcost : ∀ (l : Fin m → ℕ) (x : L),
      (∀ i, (symbolAt x (f i)).support = (f i).support) →
      ∀ (T : ℕ), T ≤ cutoff → ∀ (rT : ℕ) (e : Fin rT → JetRow L n),
        (∀ i, BankRow physDeg nodes w m_contact Supp T (e i)) →
        LinearIndependent L (fun i => symbolAt x (e i)) →
        (∀ i, (∏ j, symbolAt x (f j) ^ (requiredOrder cutoff layerWidth T - l j)) ∣
          symbolAt x (e i)) →
        rT ≤ cost l ((cutoff - T) / layerWidth)) :
    ∃ l : Fin m → ℕ,
      sourceRank ≤ layerWidth * ∑ k ∈ Finset.range (1 + cutoff / layerWidth), cost l k ∧
      ∀ i, 0 < l i → ProperCut (f i) (l i) := by
  classical
  choose l hl hcut using fun i =>
    exists_availability physDeg nodes w m_contact Supp cutoff layerWidth ProperCut hcut_step (hirr i)
  obtain ⟨x, hx, hsup⟩ := exists_fresh nodes f
  obtain ⟨r, hrank, hfamilies⟩ :=
    symbol_families physDeg nodes w m_contact Supp cutoff sourceRank x hx hr
  have hlayer : ∀ T ≤ cutoff, r T ≤ cost l ((cutoff - T) / layerWidth) := by
    intro T hT
    obtain ⟨e, he, hei⟩ := hfamilies T hT
    have hdiv (i : Fin (r T)) : (∏ j, f j ^ (requiredOrder cutoff layerWidth T - l j)) ∣ e i := by
      apply Fintype.prod_dvd_of_isRelPrime
      · intro j k hjk
        exact ((hirr j).isRelPrime_iff_not_dvd.mpr
          (fun h => hdiff j k hjk ((hirr j).associated_of_dvd (hirr k) h))).pow
      · intro j
        exact hl j T hT (e i) (he i)
    exact hcost l x hsup T hT (r T) e he hei fun i => by
      simpa only [map_prod, map_pow] using map_dvd (symbolAt x) (hdiv i)
  refine ⟨l, ?_, hcut⟩
  exact hrank.trans ((Finset.sum_le_sum fun T hT =>
    hlayer T (Nat.le_of_lt_succ (Finset.mem_range.mp hT))).trans
      (sum_by_layer cutoff layerWidth hlw (cost l)))

end

#print axioms order_of_locator_lines
#print axioms order_of_contact
#print axioms exists_fresh
#print axioms sum_by_layer
#print axioms symbol_families
#print axioms cofactor_rank_weighted
#print axioms cofactor_rank_d1
#print axioms exists_availability
#print axioms of_children

end ArkLib.ProximityGap.Frontier.PrimeHDOrder
