/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.DrdosDiscriminantBarrier
import ArkLib.Research.ProximityGap.Frontier.ComplementaryListPencil
import ArkLib.Research.ProximityGap.Frontier._PrizeShapePrimeP30
import ArkLib.Research.ProximityGap.Frontier._PrizeShapePrimeP30Second

/-!
# Quarter-Rate Complementary-Pencil Local-Contact Closure (`e = 536,870,914`)

This module formalizes the elementary, characteristic-free algebraic annihilation of the sole
remaining Rate-`1/4` prime-field `d = 1` list-decoding sliver (`d_{A_f} = 4, d_{B_f} ≤ 2,
ω_f ∈ [5.00, 5.06]`) at `e = 536,870,914` (`J + 1`), combining:

- `ComplementaryListPencil` (coprime rational representation `y(x) = B(x)/A(x)` with
  `deg A ≤ d`, `deg B ≤ 2d`, valid off an exceptional set `E` of size `≤ 3,080`), and
- `DrdosDiscriminantBarrier.local_contact_vanishing_equations` (exact `det = 1` local
  `(T, E)`-contact equations for `f = A_f(X, Y₀) Y₁ + B_f(X, Y₀)`).

## Main Results (100% Kernel-Checked, Zero `sorry`, Zero Custom Axioms)

1. **Exact Homogenized Rational Pullback & Bezout Divisibility (`linear_dvd_of_ratPullback_eq_zero`)**:
   Over ANY commutative ring `R`, for coprime `A, B : R[X]` and `P : BiPoly R` of `Y₀`-degree
   `≤ dP`, vanishing of `ratPullback A B dP P = ∑_{q=0}^{dP} P_q B^q A^{dP - q}` forces exact
   bivariate divisibility `(C A * X - C B) ∣ P` in `BiPoly R = R[X][Y₀]` via the 1-line Bezout
   unit `(C u + C v * X) * C A + (-C v) * (C A * X - C B) = 1` (no Gauss's lemma or UFD needed).

2. **Exact Shift Identity & Step-1 Multiplicity Pullback (`ratPullback_comp_shift`,
   `pow_dvd_ratPullback_of_biMultGE`)**:
   At any `(x₀, y₀)` with `B(x₀) = y₀ A(x₀)`, `biMultGE x₀ y₀ P m` implies
   `(X - C x₀)^m ∣ ratPullback A B dP P`.

3. **Universal All-`k` Contact Boost (`pow_dvd_ratPullback_A_of_contact`)**:
   Strictly generalizing the `k = 3` contact boost: over ANY integral domain `R`, if
   `LinearLocalContactGE x₀ y₀ A_f B_f k`, `B_f = (C A * X - C B) * C_f`, `B_f.natDegree ≤ d_A`,
   `A_f.natDegree ≤ d_A`, `A ≠ 0`, `B(x₀) = y₀ A(x₀)`, and the rational Wronskian does not vanish
   at `x₀` (`(B' A - A' B)(x₀) ≠ 0`), then an exact telescoping identity on `shiftBi C_f` forces
   **`(X - C x₀)^k ∣ ratPullback A B d_A A_f`** for **EVERY `k ≥ 0`**!

4. **General Common-Factor & Irreducibility Contradiction (`common_linear_factor_of_complementary_contact`,
   `irreducible_linear_factor_impossible`, `complementary_pencil_dichotomy`)**:
   Over ANY field `K` (including `𝔽_p`, `𝔽̄_p`, and char `0`) and ANY injective domain `dom : I ↪ K`:
   - If `B' A - A' B = 0` (with `char K = 0 ∨ max(deg A, deg B) < char K`), then `y` is constant on
     all good sites `G` with `A(x) ≠ 0`, capping the codeword list at `≤ 1`.
   - Otherwise `B' A - A' B ≠ 0` has at most `deg A + deg B - 1 ≤ 3d - 1` zeros, so whenever
     `W_B + d_B d < ∑_{i ∈ G} (k i - 1)` and `W_A + d_A d + (3d - 1) < ∑_{i ∈ G} k i`,
     `(C A * X - C B)` divides **BOTH `B_f` and `A_f`** — contradicting irreducibility of
     `f = A_f(X, Y₀) Y₁ + B_f(X, Y₀)` in `K[X][Y₀][Y₁]`!

5. **Production Rate-`1/4` Sliver Annihilation (`production_quarter_sliver_closed`,
   `first_prime_quarter_sliver_closed`, `second_prime_quarter_sliver_closed`)**:
   Because `pow_dvd_ratPullback_A_of_contact` boosts **every** `k_i ≥ 1` (not only `k_i = 3`),
   NEITHER an LP NOR `Res(A_f, B_f)` NOR `Disc(A_f)` is needed for Step 1 or Step 3: at
   `n = 2³⁰`, `d = 2²⁸ - 1`, `d_A = 4`, `d_B ≤ 2`, `|E| ≤ 3,080`, `k_cap ≤ 20,000`, EVERY
   irreducible factor with `5d ≤ W_B`, `W_A + d ≤ W_B + 1` (covering all `ω_f ∈ [5.00, ∞)`,
   including the entire `[5.00, 5.06]` sliver) and `∑ k_i ≥ n (1 + (ω_f - 1)/2 - 0.04)` is
   eliminated with `> 163.8M` roots of slack on BOTH `R_B` and `R_A` over `𝔽_p`, `𝔽̄_p`, and both
   designated primes `P₁` and `P₂`!
-/

set_option autoImplicit false

open Finset Polynomial BigOperators
open ArkLib.ProximityGap.Frontier.DrdosDiscriminantBarrier

namespace ArkLib.ProximityGap.Frontier.QuarterComplementaryContactClosure

/-! ### Part 1: Homogenized Rational Pullback & Characteristic-Free Bezout Divisibility -/

/-- Homogenized rational pullback
`ratPullback A B dP P = A^{dP} P(X, B/A) = ∑_{q=0}^{dP} P_q(X) B(X)^q A(X)^{dP - q}`
of a bivariate polynomial `P : BiPoly R = R[X][Y₀]` along `(A, B) : R[X] × R[X]`. -/
noncomputable def ratPullback {R : Type*} [CommRing R]
    (A B : R[X]) (dP : ℕ) (P : BiPoly R) : R[X] :=
  ∑ q ∈ Finset.range (dP + 1), P.coeff q * B ^ q * A ^ (dP - q)

lemma ratPullback_add {R : Type*} [CommRing R] (A B : R[X]) (dP : ℕ) (P Q : BiPoly R) :
    ratPullback A B dP (P + Q) = ratPullback A B dP P + ratPullback A B dP Q := by
  unfold ratPullback
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Polynomial.coeff_add]
  ring

lemma ratPullback_sum {R ι : Type*} [CommRing R] (A B : R[X]) (dP : ℕ)
    (s : Finset ι) (f : ι → BiPoly R) :
    ratPullback A B dP (∑ i ∈ s, f i) = ∑ i ∈ s, ratPullback A B dP (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ratPullback]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, ratPullback_add, ih, Finset.sum_insert ha]

lemma ratPullback_C_mul_X_pow {R : Type*} [CommRing R] (A B : R[X]) (dP q : ℕ)
    (hq : q ≤ dP) (p : R[X]) :
    ratPullback A B dP (Polynomial.C p * Polynomial.X ^ q) = p * B ^ q * A ^ (dP - q) := by
  unfold ratPullback
  rw [Finset.sum_eq_single q]
  · simp
  · intro j _ hne
    rw [Polynomial.coeff_C_mul_X_pow, ite_eq_right_iff.mpr (fun h => absurd h hne), zero_mul,
      zero_mul]
  · intro hmem
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hq)) hmem

/-- Exact weighted degree bound for `ratPullback A B dP P`:
if `deg A ≤ dA`, `deg B ≤ dA + δ`, and `deg_X(P_q) + q * δ ≤ W` for every `q ≤ dP`, then
`deg(ratPullback A B dP P) ≤ W + dP * dA`. -/
theorem natDegree_ratPullback_le {R : Type*} [CommRing R]
    (A B : R[X]) (dP dA δ W : ℕ) (P : BiPoly R)
    (hA : A.natDegree ≤ dA) (hB : B.natDegree ≤ dA + δ)
    (hW : ∀ q ≤ dP, (P.coeff q).natDegree + q * δ ≤ W) :
    (ratPullback A B dP P).natDegree ≤ W + dP * dA := by
  unfold ratPullback
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  rw [Finset.fold_max_le]
  refine ⟨Nat.zero_le _, fun q hq => ?_⟩
  have hqd : q ≤ dP := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
  have h1 : (P.coeff q * B ^ q * A ^ (dP - q)).natDegree ≤
      (P.coeff q).natDegree + q * B.natDegree + (dP - q) * A.natDegree := by
    calc
      (P.coeff q * B ^ q * A ^ (dP - q)).natDegree
          ≤ (P.coeff q * B ^ q).natDegree + (A ^ (dP - q)).natDegree :=
            Polynomial.natDegree_mul_le
      _ ≤ (P.coeff q).natDegree + (B ^ q).natDegree + (A ^ (dP - q)).natDegree :=
            Nat.add_le_add_right Polynomial.natDegree_mul_le _
      _ ≤ (P.coeff q).natDegree + q * B.natDegree + (dP - q) * A.natDegree :=
            Nat.add_le_add (Nat.add_le_add_left Polynomial.natDegree_pow_le _)
              Polynomial.natDegree_pow_le
  have h2 : q * B.natDegree ≤ q * (dA + δ) := Nat.mul_le_mul_left q hB
  have h3 : (dP - q) * A.natDegree ≤ (dP - q) * dA := Nat.mul_le_mul_left (dP - q) hA
  have h4 := hW q hqd
  have hsplit : q * dA + (dP - q) * dA = dP * dA := by
    rw [← Nat.add_mul, Nat.add_sub_of_le hqd]
  dsimp only [Function.comp_apply]
  nlinarith

/-- In `BiPoly R`, `C A * X - C B` divides `C (A ^ dP) * P - C (ratPullback A B dP P)` for any
`P` with `P.natDegree ≤ dP`. -/
theorem linear_dvd_sub_ratPullback {R : Type*} [CommRing R]
    (A B : R[X]) (dP : ℕ) (P : BiPoly R) (hdeg : P.natDegree ≤ dP) :
    (Polynomial.C A * Polynomial.X - Polynomial.C B) ∣
      (Polynomial.C (A ^ dP) * P - Polynomial.C (ratPullback A B dP P)) := by
  have hP : P = ∑ q ∈ Finset.range (dP + 1), Polynomial.C (P.coeff q) * Polynomial.X ^ q :=
    Polynomial.as_sum_range_C_mul_X_pow' P (Nat.lt_succ_of_le hdeg)
  have hrew : Polynomial.C (A ^ dP) * P - Polynomial.C (ratPullback A B dP P) =
      ∑ q ∈ Finset.range (dP + 1),
        Polynomial.C (P.coeff q * A ^ (dP - q)) *
          ((Polynomial.C A * Polynomial.X) ^ q - (Polynomial.C B) ^ q) := by
    unfold ratPullback
    have hmul : Polynomial.C (A ^ dP) * P =
        ∑ q ∈ Finset.range (dP + 1),
          Polynomial.C (A ^ dP) * (Polynomial.C (P.coeff q) * Polynomial.X ^ q) := by
      conv_lhs => rw [hP]
      rw [Finset.mul_sum]
    rw [hmul, map_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hqd : q ≤ dP := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
    have hpow : A ^ dP = A ^ (dP - q) * A ^ q := by
      rw [← pow_add, Nat.sub_add_cancel hqd]
    rw [hpow, mul_pow]
    simp only [map_mul, map_pow]
    ring
  rw [hrew]
  refine Finset.dvd_sum fun q _ => ?_
  exact dvd_mul_of_dvd_right (sub_dvd_pow_sub_pow (Polynomial.C A * Polynomial.X) (Polynomial.C B) q) _

/-- Elementary 1-line Bezout coprimality: `IsCoprime A B` in `R[X]` immediately implies
`IsCoprime (C A) (C A * X - C B)` in `BiPoly R = R[X][Y₀]`. -/
theorem isCoprime_C_linear {R : Type*} [CommRing R] {A B : R[X]} (hcop : IsCoprime A B) :
    IsCoprime (Polynomial.C A) (Polynomial.C A * Polynomial.X - Polynomial.C B) := by
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨Polynomial.C u + Polynomial.C v * Polynomial.X, -Polynomial.C v, ?_⟩
  have h1 : (Polynomial.C u + Polynomial.C v * Polynomial.X) * Polynomial.C A +
      (-Polynomial.C v) * (Polynomial.C A * Polynomial.X - Polynomial.C B) =
      Polynomial.C (u * A + v * B) := by
    simp only [map_add, map_mul]
    ring
  rw [h1, huv, map_one]

/-- **Exact Bivariate Divisibility from Vanishing Rational Pullback (Characteristic-Free).**
Over ANY commutative ring `R`, if `IsCoprime A B`, `P.natDegree ≤ dP`, and
`ratPullback A B dP P = 0`, then `(C A * X - C B) ∣ P` in `BiPoly R`. -/
theorem linear_dvd_of_ratPullback_eq_zero {R : Type*} [CommRing R]
    {A B : R[X]} {dP : ℕ} {P : BiPoly R}
    (hcop : IsCoprime A B) (hdeg : P.natDegree ≤ dP) (hzero : ratPullback A B dP P = 0) :
    (Polynomial.C A * Polynomial.X - Polynomial.C B) ∣ P := by
  have hdvd : (Polynomial.C A * Polynomial.X - Polynomial.C B) ∣ Polynomial.C A ^ dP * P := by
    have h := linear_dvd_sub_ratPullback A B dP P hdeg
    simpa [hzero, map_pow] using h
  have hcop_pow : IsCoprime (Polynomial.C A ^ dP) (Polynomial.C A * Polynomial.X - Polynomial.C B) :=
    (isCoprime_C_linear hcop).pow_left
  obtain ⟨u, v, huv⟩ := hcop_pow
  obtain ⟨q, hq⟩ := hdvd
  refine ⟨u * q + v * P, ?_⟩
  linear_combination -P * huv + u * hq

/-! ### Part 2: Exact Shift Identity, Step-1 Pullback Order, and Universal All-`k` Contact Boost -/

lemma comp_C_add_X_comp_X_sub_C {R : Type*} [CommRing R] (x₀ : R) (f : R[X]) :
    (f.comp (Polynomial.C x₀ + Polynomial.X)).comp (Polynomial.X - Polynomial.C x₀) = f := by
  rw [Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.C_comp, Polynomial.X_comp]
  have h : Polynomial.C x₀ + (Polynomial.X - Polynomial.C x₀) = Polynomial.X := by ring
  rw [h, Polynomial.comp_X]

lemma comp_X_sub_C_comp_C_add_X {R : Type*} [CommRing R] (x₀ : R) (f : R[X]) :
    (f.comp (Polynomial.X - Polynomial.C x₀)).comp (Polynomial.C x₀ + Polynomial.X) = f := by
  rw [Polynomial.comp_assoc, Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
  have h : Polynomial.C x₀ + Polynomial.X - Polynomial.C x₀ = Polynomial.X := by ring
  rw [h, Polynomial.comp_X]

lemma linear_pow_dvd_iff_X_pow_dvd_shift {R : Type*} [CommRing R] (x₀ : R) (f : R[X]) (m : ℕ) :
    (Polynomial.X - Polynomial.C x₀) ^ m ∣ f ↔
      Polynomial.X ^ m ∣ f.comp (Polynomial.C x₀ + Polynomial.X) := by
  constructor
  · rintro ⟨q, rfl⟩
    refine ⟨q.comp (Polynomial.C x₀ + Polynomial.X), ?_⟩
    rw [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.sub_comp, Polynomial.X_comp,
      Polynomial.C_comp]
    have h : Polynomial.C x₀ + Polynomial.X - Polynomial.C x₀ = Polynomial.X := by ring
    rw [h]
  · rintro ⟨q, hq⟩
    refine ⟨q.comp (Polynomial.X - Polynomial.C x₀), ?_⟩
    have h := congrArg (fun g => g.comp (Polynomial.X - Polynomial.C x₀)) hq
    rw [comp_C_add_X_comp_X_sub_C, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp] at h
    exact h

lemma coeff_zero_comp_C_add_X {R : Type*} [CommRing R] (x₀ : R) (f : R[X]) :
    (f.comp (Polynomial.C x₀ + Polynomial.X)).coeff 0 = f.eval x₀ := by
  rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp]
  simp

lemma coeff_one_comp_C_add_X {R : Type*} [CommRing R] (x₀ : R) (f : R[X]) :
    (f.comp (Polynomial.C x₀ + Polynomial.X)).coeff 1 = f.derivative.eval x₀ := by
  have hderiv : (f.comp (Polynomial.C x₀ + Polynomial.X)).derivative =
      f.derivative.comp (Polynomial.C x₀ + Polynomial.X) := by
    rw [Polynomial.derivative_comp, Polynomial.derivative_add, Polynomial.derivative_C,
      Polynomial.derivative_X, zero_add, one_mul]
  have hc0 : (f.comp (Polynomial.C x₀ + Polynomial.X)).derivative.coeff 0 =
      (f.comp (Polynomial.C x₀ + Polynomial.X)).coeff 1 := by
    rw [Polynomial.coeff_derivative]
    simp
  rw [← hc0, hderiv, coeff_zero_comp_C_add_X]

lemma shiftBi_zero {R : Type*} [CommRing R] (x₀ y₀ : R) :
    shiftBi x₀ y₀ (0 : BiPoly R) = 0 := by
  simp [shiftBi]

lemma shiftBi_sub {R : Type*} [CommRing R] (x₀ y₀ : R) (f g : BiPoly R) :
    shiftBi x₀ y₀ (f - g) = shiftBi x₀ y₀ f - shiftBi x₀ y₀ g := by
  unfold shiftBi
  simp [Polynomial.map_sub, Polynomial.sub_comp]

lemma shiftBi_sum {R ι : Type*} [CommRing R] (x₀ y₀ : R) (s : Finset ι) (f : ι → BiPoly R) :
    shiftBi x₀ y₀ (∑ i ∈ s, f i) = ∑ i ∈ s, shiftBi x₀ y₀ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [shiftBi_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, shiftBi_add, ih, Finset.sum_insert ha]

lemma shiftBi_C {R : Type*} [CommRing R] (x₀ y₀ : R) (p : R[X]) :
    shiftBi x₀ y₀ (Polynomial.C p) = Polynomial.C (p.comp (Polynomial.C x₀ + Polynomial.X)) := by
  unfold shiftBi
  simp [Polynomial.map_C, Polynomial.C_comp]

lemma shiftBi_X {R : Type*} [CommRing R] (x₀ y₀ : R) :
    shiftBi x₀ y₀ (Polynomial.X : BiPoly R) = Polynomial.C (Polynomial.C y₀) + Polynomial.X := by
  unfold shiftBi
  simp [Polynomial.map_X, Polynomial.X_comp]

lemma shiftBi_natDegree_le {R : Type*} [CommRing R] (x₀ y₀ : R) (P : BiPoly R) :
    (shiftBi x₀ y₀ P).natDegree ≤ P.natDegree := by
  unfold shiftBi
  have hlin : (Polynomial.C (Polynomial.C y₀) + Polynomial.X : BiPoly R).natDegree ≤ 1 := by
    refine (Polynomial.natDegree_add_le _ _).trans ?_
    simp [Polynomial.natDegree_C, Polynomial.natDegree_X_le]
  calc
    ((P.map (Polynomial.compRingHom (Polynomial.C x₀ + Polynomial.X))).comp
        (Polynomial.C (Polynomial.C y₀) + Polynomial.X)).natDegree
        ≤ (P.map (Polynomial.compRingHom (Polynomial.C x₀ + Polynomial.X))).natDegree *
            (Polynomial.C (Polynomial.C y₀) + Polynomial.X).natDegree :=
          Polynomial.natDegree_comp_le
    _ ≤ P.natDegree * 1 := Nat.mul_le_mul Polynomial.natDegree_map_le hlin
    _ = P.natDegree := Nat.mul_one _

/-- **Exact Shift Identity for `ratPullback` (Characteristic-Free).**
Shifting `X ↦ x₀ + T` in `ratPullback A B dP P` is identically equal to evaluating `ratPullback`
on `shiftBi x₀ y₀ P` along `(Ã, Δ)` where `Ã = A(x₀ + T)` and `Δ = B(x₀ + T) - y₀ A(x₀ + T)`. -/
theorem ratPullback_comp_shift {R : Type*} [CommRing R]
    (x₀ y₀ : R) (A B : R[X]) (dP : ℕ) (P : BiPoly R) (hdeg : P.natDegree ≤ dP) :
    (ratPullback A B dP P).comp (Polynomial.C x₀ + Polynomial.X) =
      ratPullback (A.comp (Polynomial.C x₀ + Polynomial.X))
        (B.comp (Polynomial.C x₀ + Polynomial.X) -
          Polynomial.C y₀ * A.comp (Polynomial.C x₀ + Polynomial.X))
        dP (shiftBi x₀ y₀ P) := by
  set At : R[X] := A.comp (Polynomial.C x₀ + Polynomial.X)
  set Bt : R[X] := B.comp (Polynomial.C x₀ + Polynomial.X)
  set Δ : R[X] := Bt - Polynomial.C y₀ * At
  have hP : P = ∑ q ∈ Finset.range (dP + 1), Polynomial.C (P.coeff q) * Polynomial.X ^ q :=
    Polynomial.as_sum_range_C_mul_X_pow' P (Nat.lt_succ_of_le hdeg)
  -- Check on each monomial `C (P.coeff q) * X^q` (`q ≤ dP`):
  have hmono : ∀ q ≤ dP, ∀ p : R[X],
      (p.comp (Polynomial.C x₀ + Polynomial.X)) * Bt ^ q * At ^ (dP - q) =
        ratPullback At Δ dP (shiftBi x₀ y₀ (Polynomial.C p * Polynomial.X ^ q)) := by
    intro q hq p
    have hshift : shiftBi x₀ y₀ (Polynomial.C p * Polynomial.X ^ q) =
        ∑ j ∈ Finset.range (q + 1),
          Polynomial.C (p.comp (Polynomial.C x₀ + Polynomial.X) *
            Polynomial.C y₀ ^ (q - j) * ((q.choose j : ℕ) : R[X])) * Polynomial.X ^ j := by
      have hpow : shiftBi x₀ y₀ (Polynomial.X ^ q : BiPoly R) =
          (Polynomial.X + Polynomial.C (Polynomial.C y₀)) ^ q := by
        induction q with
        | zero => simp [shiftBi]
        | succ k ih =>
            rw [pow_succ, shiftBi_mul, ih (by omega), shiftBi_X, pow_succ]
            ring
      rw [shiftBi_mul, shiftBi_C, hpow, add_pow, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [map_mul, map_pow, map_natCast]
      ring
    rw [hshift, ratPullback_sum]
    have hterm : ∀ j ∈ Finset.range (q + 1),
        ratPullback At Δ dP
          (Polynomial.C (p.comp (Polynomial.C x₀ + Polynomial.X) *
            Polynomial.C y₀ ^ (q - j) * ((q.choose j : ℕ) : R[X])) * Polynomial.X ^ j) =
        (p.comp (Polynomial.C x₀ + Polynomial.X) * At ^ (dP - q)) *
          (Δ ^ j * (Polynomial.C y₀ * At) ^ (q - j) * ((q.choose j : ℕ) : R[X])) := by
      intro j hj
      have hjq : j ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [ratPullback_C_mul_X_pow At Δ dP j (hjq.trans hq)]
      have hexp : dP - j = (dP - q) + (q - j) := by omega
      rw [hexp, pow_add, mul_pow]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← add_pow]
    have hsum_B : Δ + Polynomial.C y₀ * At = Bt := by dsimp [Δ]; ring
    rw [hsum_B]
    ring
  conv_rhs => rw [hP]
  rw [shiftBi_sum, ratPullback_sum]
  unfold ratPullback
  rw [Polynomial.sum_comp]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hqd : q ≤ dP := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
  rw [Polynomial.mul_comp, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.pow_comp]
  exact hmono q hqd (P.coeff q)

/-- **Step 1 Pullback Order Bound (`biMultGE → (X - C x₀)^m ∣ ratPullback`).**
Over ANY commutative ring `R`, if `P.natDegree ≤ dP`, `B.eval x₀ = y₀ * A.eval x₀`, and
`biMultGE x₀ y₀ P m`, then `(X - C x₀) ^ m ∣ ratPullback A B dP P`. -/
theorem pow_dvd_ratPullback_of_biMultGE {R : Type*} [CommRing R]
    (x₀ y₀ : R) (A B : R[X]) (dP m : ℕ) (P : BiPoly R)
    (hdeg : P.natDegree ≤ dP) (hval : B.eval x₀ = y₀ * A.eval x₀)
    (hmult : biMultGE x₀ y₀ P m) :
    (Polynomial.X - Polynomial.C x₀) ^ m ∣ ratPullback A B dP P := by
  rw [linear_pow_dvd_iff_X_pow_dvd_shift, ratPullback_comp_shift x₀ y₀ A B dP P hdeg]
  set At : R[X] := A.comp (Polynomial.C x₀ + Polynomial.X)
  set Δ : R[X] := B.comp (Polynomial.C x₀ + Polynomial.X) - Polynomial.C y₀ * At
  have hΔ0 : Δ.coeff 0 = 0 := by
    dsimp [Δ, At]
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, coeff_zero_comp_C_add_X,
      coeff_zero_comp_C_add_X, hval, sub_self]
  have hXdvdΔ : Polynomial.X ∣ Δ := Polynomial.X_dvd_iff.mpr hΔ0
  unfold ratPullback
  refine Finset.dvd_sum fun q _ => ?_
  by_cases hqm : m ≤ q
  · have h1 : (Polynomial.X : R[X]) ^ m ∣ (Polynomial.X : R[X]) ^ q :=
      pow_dvd_pow (Polynomial.X : R[X]) hqm
    have h2 : (Polynomial.X : R[X]) ^ q ∣ Δ ^ q := pow_dvd_pow_of_dvd hXdvdΔ q
    exact ((h1.trans h2).mul_left _).mul_right _
  · have hqlt : q < m := Nat.lt_of_not_ge hqm
    have hcoeff : Polynomial.X ^ (m - q) ∣ (shiftBi x₀ y₀ P).coeff q := by
      rw [Polynomial.X_pow_dvd_iff]
      intro p hp
      exact hmult p q (by omega)
    have hΔpow : Polynomial.X ^ q ∣ Δ ^ q := pow_dvd_pow_of_dvd hXdvdΔ q
    have hprod : Polynomial.X ^ m ∣ (shiftBi x₀ y₀ P).coeff q * Δ ^ q := by
      have hexp : m = (m - q) + q := by omega
      rw [hexp, pow_add]
      exact mul_dvd_mul hcoeff hΔpow
    exact hprod.mul_right _

/-! #### Local Shifted Algebra for `B_f = (C A * X - C B) * C_f` -/

lemma shiftBi_linear_factor {R : Type*} [CommRing R] (x₀ y₀ : R) (A B : R[X]) :
    shiftBi x₀ y₀ (Polynomial.C A * Polynomial.X - Polynomial.C B) =
      Polynomial.C (A.comp (Polynomial.C x₀ + Polynomial.X)) * Polynomial.X -
        Polynomial.C (B.comp (Polynomial.C x₀ + Polynomial.X) -
          Polynomial.C y₀ * A.comp (Polynomial.C x₀ + Polynomial.X)) := by
  rw [shiftBi_sub, shiftBi_mul, shiftBi_C, shiftBi_X, shiftBi_C]
  simp only [map_sub, map_mul]
  ring

lemma shiftCoeff_linear_mul {R : Type*} [CommRing R]
    (x₀ y₀ : R) (A B : R[X]) (C_f : BiPoly R) (p q : ℕ) :
    shiftCoeff x₀ y₀ ((Polynomial.C A * Polynomial.X - Polynomial.C B) * C_f) p q =
      (if 1 ≤ q then
          ∑ i ∈ Finset.range (p + 1),
            (A.comp (Polynomial.C x₀ + Polynomial.X)).coeff i *
              shiftCoeff x₀ y₀ C_f (p - i) (q - 1)
        else 0) -
      ∑ i ∈ Finset.range (p + 1),
        (B.comp (Polynomial.C x₀ + Polynomial.X) -
          Polynomial.C y₀ * A.comp (Polynomial.C x₀ + Polynomial.X)).coeff i *
          shiftCoeff x₀ y₀ C_f (p - i) q := by
  set Ã : R[X] := A.comp (Polynomial.C x₀ + Polynomial.X)
  set Δ : R[X] := B.comp (Polynomial.C x₀ + Polynomial.X) - Polynomial.C y₀ * Ã
  unfold shiftCoeff
  rw [shiftBi_mul, shiftBi_linear_factor]
  have hsub : ((Polynomial.C Ã * Polynomial.X - Polynomial.C Δ) * shiftBi x₀ y₀ C_f).coeff q =
      (if 1 ≤ q then Ã * (shiftBi x₀ y₀ C_f).coeff (q - 1) else 0) -
        Δ * (shiftBi x₀ y₀ C_f).coeff q := by
    rw [sub_mul, Polynomial.coeff_sub, mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
    congr 1
    cases q with
    | zero => simp
    | succ q' => simp [Polynomial.coeff_X_mul]
  rw [hsub, Polynomial.coeff_sub]
  congr 1
  · split_ifs with hq
    · rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    · simp
  · rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- If `B_f = (C A * X - C B) * C_f` has `biMultGE x₀ y₀ B_f m`, `B(x₀) = y₀ A(x₀)`, and
`A(x₀) ≠ 0`, then the quotient `C_f` inherits `biMultGE x₀ y₀ C_f (m - 1)`. -/
theorem biMultGE_quotient_of_linear_factor {R : Type*} [CommRing R] [IsDomain R]
    (x₀ y₀ : R) (A B : R[X]) (C_f : BiPoly R) (m : ℕ)
    (hA0 : A.eval x₀ ≠ 0) (hval : B.eval x₀ = y₀ * A.eval x₀)
    (hmult : biMultGE x₀ y₀ ((Polynomial.C A * Polynomial.X - Polynomial.C B) * C_f) m) :
    biMultGE x₀ y₀ C_f (m - 1) := by
  set Ã : R[X] := A.comp (Polynomial.C x₀ + Polynomial.X)
  set Δ : R[X] := B.comp (Polynomial.C x₀ + Polynomial.X) - Polynomial.C y₀ * Ã
  have hÃ0 : Ã.coeff 0 ≠ 0 := by rwa [coeff_zero_comp_C_add_X]
  have hΔ0 : Δ.coeff 0 = 0 := by
    dsimp [Δ, Ã]
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, coeff_zero_comp_C_add_X,
      coeff_zero_comp_C_add_X, hval, sub_self]
  have hmain : ∀ n < m - 1, ∀ p q, p + q = n → shiftCoeff x₀ y₀ C_f p q = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ihn =>
      intro hn p
      induction p using Nat.strong_induction_on with
      | h p ihp =>
        intro q hpq
        have hB0 : shiftCoeff x₀ y₀ ((Polynomial.C A * Polynomial.X - Polynomial.C B) * C_f)
            p (q + 1) = 0 := hmult p (q + 1) (by omega)
        rw [shiftCoeff_linear_mul] at hB0
        simp only [show 1 ≤ q + 1 by omega, ite_true, Nat.add_sub_cancel] at hB0
        rw [Finset.sum_range_succ'] at hB0
        have hsum1 : ∑ x ∈ Finset.range p,
            Ã.coeff (x + 1) * shiftCoeff x₀ y₀ C_f (p - (x + 1)) q = 0 := by
          refine Finset.sum_eq_zero fun x hx => ?_
          have hxp : x < p := Finset.mem_range.mp hx
          rw [ihn (p - (x + 1) + q) (by omega) (by omega) _ _ rfl, mul_zero]
        have hsum2 : ∑ i ∈ Finset.range (p + 1),
            Δ.coeff i * shiftCoeff x₀ y₀ C_f (p - i) (q + 1) = 0 := by
          refine Finset.sum_eq_zero fun i hi => ?_
          have hip : i ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          rcases i with _ | i'
          · rw [hΔ0, zero_mul]
          · rcases i' with _ | i''
            · rw [ihp (p - 1) (by omega) (q + 1) (by omega), mul_zero]
            · rw [ihn (p - (i'' + 2) + (q + 1)) (by omega) (by omega) _ _ rfl, mul_zero]
        change (∑ x ∈ Finset.range p, Ã.coeff (x + 1) * shiftCoeff x₀ y₀ C_f (p - (x + 1)) q) +
            Ã.coeff 0 * shiftCoeff x₀ y₀ C_f (p - 0) q -
            ∑ i ∈ Finset.range (p + 1), Δ.coeff i * shiftCoeff x₀ y₀ C_f (p - i) (q + 1) = 0 at hB0
        rw [hsum1, hsum2, zero_add, sub_zero, Nat.sub_zero] at hB0
        exact (mul_eq_zero.mp hB0).resolve_left hÃ0
  intro p q hpq
  exact hmain (p + q) hpq p q rfl

/-- Exact leading-degree formula for `(C A * X - C B) * C_f` when `biMultGE x₀ y₀ C_f (m - 1)`. -/
lemma shiftCoeff_linear_mul_homog {R : Type*} [CommRing R]
    (x₀ y₀ : R) (A B : R[X]) (C_f : BiPoly R) {m p q : ℕ}
    (hm : 1 ≤ m) (hpq : p + q = m)
    (hval : B.eval x₀ = y₀ * A.eval x₀) (hC : biMultGE x₀ y₀ C_f (m - 1)) :
    shiftCoeff x₀ y₀ ((Polynomial.C A * Polynomial.X - Polynomial.C B) * C_f) p q =
      (if 1 ≤ q then A.eval x₀ * shiftCoeff x₀ y₀ C_f p (q - 1) else 0) -
      (if 1 ≤ p then
          (B.comp (Polynomial.C x₀ + Polynomial.X) -
            Polynomial.C y₀ * A.comp (Polynomial.C x₀ + Polynomial.X)).coeff 1 *
            shiftCoeff x₀ y₀ C_f (p - 1) q
        else 0) := by
  set Ã : R[X] := A.comp (Polynomial.C x₀ + Polynomial.X)
  set Δ : R[X] := B.comp (Polynomial.C x₀ + Polynomial.X) - Polynomial.C y₀ * Ã
  have hÃ0 : Ã.coeff 0 = A.eval x₀ := coeff_zero_comp_C_add_X x₀ A
  have hΔ0 : Δ.coeff 0 = 0 := by
    dsimp [Δ, Ã]
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, coeff_zero_comp_C_add_X,
      coeff_zero_comp_C_add_X, hval, sub_self]
  rw [shiftCoeff_linear_mul]
  congr 1
  · split_ifs with hq
    · rw [Finset.sum_range_succ']
      have hrest : ∑ x ∈ Finset.range p,
          Ã.coeff (x + 1) * shiftCoeff x₀ y₀ C_f (p - (x + 1)) (q - 1) = 0 := by
        refine Finset.sum_eq_zero fun x hx => ?_
        have hxp : x < p := Finset.mem_range.mp hx
        rw [hC (p - (x + 1)) (q - 1) (by omega), mul_zero]
      change (∑ x ∈ Finset.range p, Ã.coeff (x + 1) * shiftCoeff x₀ y₀ C_f (p - (x + 1)) (q - 1)) +
          Ã.coeff 0 * shiftCoeff x₀ y₀ C_f (p - 0) (q - 1) = _
      rw [hrest, zero_add, Nat.sub_zero, hÃ0]
    · rfl
  · cases p with
    | zero =>
        simp only [Nat.zero_add, Finset.range_one, Finset.sum_singleton, Nat.sub_zero]
        change Δ.coeff 0 * shiftCoeff x₀ y₀ C_f 0 q = 0
        rw [hΔ0, zero_mul]
    | succ p' =>
        simp only [show 1 ≤ p' + 1 by omega, ite_true, Nat.add_sub_cancel]
        rw [Finset.sum_range_succ', Finset.sum_range_succ']
        have hrest : ∑ x ∈ Finset.range p',
            Δ.coeff (x + 2) * shiftCoeff x₀ y₀ C_f (p' + 1 - (x + 2)) q = 0 := by
          refine Finset.sum_eq_zero fun x hx => ?_
          have hxp : x < p' := Finset.mem_range.mp hx
          rw [hC (p' + 1 - (x + 2)) q (by omega), mul_zero]
        change (∑ x ∈ Finset.range p', Δ.coeff (x + 2) * shiftCoeff x₀ y₀ C_f (p' + 1 - (x + 2)) q) +
            Δ.coeff 1 * shiftCoeff x₀ y₀ C_f (p' + 1 - 1) q +
            Δ.coeff 0 * shiftCoeff x₀ y₀ C_f (p' + 1 - 0) q = _
        rw [hrest, hΔ0, zero_mul, zero_add, add_zero, Nat.add_sub_cancel]

/-! #### Exact Leading-Order Coefficient Helpers for `ratPullback` -/

lemma coeff_mul_of_vanish_below {R : Type*} [CommRing R] (f g : R[X]) (a b : ℕ)
    (hf : ∀ i < a, f.coeff i = 0) (hg : ∀ j < b, g.coeff j = 0) :
    (f * g).coeff (a + b) = f.coeff a * g.coeff b := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.sum_eq_single a]
  · simp
  · intro i hi hne
    have hle : i ≤ a + b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    by_cases hlt : i < a
    · rw [hf i hlt, zero_mul]
    · rw [hg (a + b - i) (by omega), mul_zero]
  · intro hmem
    exact absurd (Finset.mem_range.mpr (by omega)) hmem

lemma coeff_pow_of_coeff_zero {R : Type*} [CommRing R] (Δ : R[X]) (hΔ0 : Δ.coeff 0 = 0) :
    ∀ q : ℕ, (∀ j < q, (Δ ^ q).coeff j = 0) ∧ (Δ ^ q).coeff q = (Δ.coeff 1) ^ q := by
  intro q
  induction q with
  | zero =>
      exact ⟨fun j hj => absurd hj (Nat.not_lt_zero j), by simp⟩
  | succ q ih =>
      have hdvd : Polynomial.X ^ (q + 1) ∣ Δ ^ (q + 1) :=
        pow_dvd_pow_of_dvd (Polynomial.X_dvd_iff.mpr hΔ0) (q + 1)
      refine ⟨Polynomial.X_pow_dvd_iff.mp hdvd, ?_⟩
      rw [pow_succ, pow_succ]
      have h := coeff_mul_of_vanish_below (Δ ^ q) Δ q 1 ih.1 (fun j hj => by
        have hj0 : j = 0 := by omega
        subst hj0; exact hΔ0)
      rw [h, ih.2]

/-- **Universal All-`k` Contact Boost for `R_A = ratPullback A B d_A A_f`.**
Over ANY integral domain `R`, if `LinearLocalContactGE x₀ y₀ A_f B_f k`, `A_f.natDegree ≤ d_A`,
`B_f.natDegree ≤ d_A`, `A ≠ 0`, `B_f = (C A * X - C B) * C_f`, `B(x₀) = y₀ A(x₀)`, and
`(B' A - A' B)(x₀) ≠ 0`, then **`(X - C x₀) ^ k ∣ ratPullback A B d_A A_f`** for **EVERY `k : ℕ`**! -/
theorem pow_dvd_ratPullback_A_of_contact {R : Type*} [CommRing R] [IsDomain R]
    (x₀ y₀ : R) (A B : R[X]) (A_f B_f C_f : BiPoly R) (d_A k : ℕ)
    (hA_ne : A ≠ 0)
    (hA_deg : A_f.natDegree ≤ d_A) (hB_deg : B_f.natDegree ≤ d_A)
    (hBf_fac : B_f = (Polynomial.C A * Polynomial.X - Polynomial.C B) * C_f)
    (hcontact : LinearLocalContactGE x₀ y₀ A_f B_f k)
    (hval : B.eval x₀ = y₀ * A.eval x₀)
    (hW : (B.derivative * A - A.derivative * B).eval x₀ ≠ 0) :
    (Polynomial.X - Polynomial.C x₀) ^ k ∣ ratPullback A B d_A A_f := by
  cases k with
  | zero => simp
  | succ m =>
    -- Obtain local contact vanishing equations for `k = m + 1`.
    obtain ⟨hbiA, hbiB, hb0, ha0, hpair⟩ :=
      local_contact_vanishing_equations x₀ y₀ A_f B_f (m + 1) hcontact
    simp only [Nat.add_sub_cancel] at hbiA hbiB
    -- Shift to `T = X - x₀`.
    rw [linear_pow_dvd_iff_X_pow_dvd_shift, ratPullback_comp_shift x₀ y₀ A B d_A A_f hA_deg]
    set Ã : R[X] := A.comp (Polynomial.C x₀ + Polynomial.X)
    set Δ : R[X] := B.comp (Polynomial.C x₀ + Polynomial.X) - Polynomial.C y₀ * Ã
    set α₀ : R := A.eval x₀
    set δ₁ : R := Δ.coeff 1
    have hÃ0 : Ã.coeff 0 = α₀ := coeff_zero_comp_C_add_X x₀ A
    have hΔ0 : Δ.coeff 0 = 0 := by
      dsimp [Δ, Ã]
      rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, coeff_zero_comp_C_add_X,
        coeff_zero_comp_C_add_X, hval, sub_self]
    -- Show `α₀ * δ₁ = (B' A - A' B)(x₀) ≠ 0`, so BOTH `α₀ ≠ 0` and `δ₁ ≠ 0`.
    have hW_eq : α₀ * δ₁ = (B.derivative * A - A.derivative * B).eval x₀ := by
      have hδ1 : δ₁ = B.derivative.eval x₀ - y₀ * A.derivative.eval x₀ := by
        dsimp [δ₁, Δ, Ã]
        rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, coeff_one_comp_C_add_X,
          coeff_one_comp_C_add_X]
      rw [hδ1, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul]
      dsimp [α₀]
      linear_combination A.derivative.eval x₀ * hval
    have hα0_ne : α₀ ≠ 0 := left_ne_zero_of_mul (by rwa [hW_eq])
    have hδ1_ne : δ₁ ≠ 0 := right_ne_zero_of_mul (by rwa [hW_eq])
    -- Step A: `X ^ m ∣ ratPullback Ã Δ d_A (shiftBi x₀ y₀ A_f)` already holds by Step 1!
    have hdvd_m : Polynomial.X ^ m ∣ ratPullback Ã Δ d_A (shiftBi x₀ y₀ A_f) := by
      have h1 := pow_dvd_ratPullback_of_biMultGE x₀ y₀ A B d_A m A_f hA_deg hval hbiA
      rw [linear_pow_dvd_iff_X_pow_dvd_shift, ratPullback_comp_shift x₀ y₀ A B d_A A_f hA_deg] at h1
      exact h1
    -- So we only need to show `(ratPullback Ã Δ d_A (shiftBi x₀ y₀ A_f)).coeff m = 0`!
    rw [Polynomial.X_pow_dvd_iff]
    intro r hr
    by_cases hrm : r < m
    · exact Polynomial.X_pow_dvd_iff.mp hdvd_m r hrm
    · have hreq : r = m := by omega
      rw [hreq]
      -- Compute the `m`-th coefficient of `ratPullback Ã Δ d_A (shiftBi x₀ y₀ A_f)`.
      unfold ratPullback
      rw [Polynomial.finsetSum_coeff]
      have hterm_coeff : ∀ q ∈ Finset.range (d_A + 1),
          ((shiftBi x₀ y₀ A_f).coeff q * Δ ^ q * Ã ^ (d_A - q)).coeff m =
            if q ≤ m then shiftCoeff x₀ y₀ A_f (m - q) q * δ₁ ^ q * α₀ ^ (d_A - q) else 0 := by
        intro q _
        by_cases hqm : q ≤ m
        · rw [ite_eq_left_iff.mpr (fun h => absurd hqm h)]
          have hQ : ∀ i < m - q, ((shiftBi x₀ y₀ A_f).coeff q).coeff i = 0 :=
            fun i hi => hbiA i q (by omega)
          have hΔq := coeff_pow_of_coeff_zero Δ hΔ0 q
          have hprod1 : ∀ j < m, ((shiftBi x₀ y₀ A_f).coeff q * Δ ^ q).coeff j = 0 := by
            intro j hj
            have hdvd1 : Polynomial.X ^ (m - q) ∣ (shiftBi x₀ y₀ A_f).coeff q :=
              Polynomial.X_pow_dvd_iff.mpr hQ
            have hdvd2 : Polynomial.X ^ q ∣ Δ ^ q := Polynomial.X_pow_dvd_iff.mpr hΔq.1
            have hdvd12 : Polynomial.X ^ m ∣ (shiftBi x₀ y₀ A_f).coeff q * Δ ^ q := by
              rw [show m = (m - q) + q by omega, pow_add]
              exact mul_dvd_mul hdvd1 hdvd2
            exact Polynomial.X_pow_dvd_iff.mp hdvd12 j hj
          have hstep2 := coeff_mul_of_vanish_below ((shiftBi x₀ y₀ A_f).coeff q * Δ ^ q)
            (Ã ^ (d_A - q)) m 0 hprod1 (fun j hj => absurd hj (Nat.not_lt_zero j))
          rw [Nat.add_zero] at hstep2
          rw [hstep2]
          have hstep1 := coeff_mul_of_vanish_below ((shiftBi x₀ y₀ A_f).coeff q) (Δ ^ q)
            (m - q) q hQ hΔq.1
          rw [Nat.sub_add_cancel hqm] at hstep1
          rw [hstep1, hΔq.2]
          have hÃpow : (Ã ^ (d_A - q)).coeff 0 = α₀ ^ (d_A - q) := by
            rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow,
              ← Polynomial.coeff_zero_eq_eval_zero, hÃ0]
          rw [hÃpow]
          rfl
        · rw [ite_eq_right_iff.mpr (fun h => absurd h hqm)]
          have hΔq := coeff_pow_of_coeff_zero Δ hΔ0 q
          have hdvd : Polynomial.X ^ q ∣ (shiftBi x₀ y₀ A_f).coeff q * Δ ^ q * Ã ^ (d_A - q) :=
            ((Polynomial.X_pow_dvd_iff.mpr hΔq.1).mul_left _).mul_right _
          exact Polynomial.X_pow_dvd_iff.mp hdvd m (by omega)
      rw [Finset.sum_congr rfl hterm_coeff]
      -- Case `m = 0` (`k = 1`): only `q = 0` contributes, and `a_{0,0} = 0`.
      rcases m with _ | m'
      · have ha00 : shiftCoeff x₀ y₀ A_f 0 0 = 0 := ha0 0 (by omega)
        refine Finset.sum_eq_zero fun q _ => ?_
        split_ifs with hq
        · have hq0 : q = 0 := by omega
          subst hq0; simp [ha00]
        · rfl
      · -- Case `m = m' + 1 ≥ 1`: apply `biMultGE_quotient_of_linear_factor` and telescope!
        have hm1 : 1 ≤ m' + 1 := by omega
        have hbiC : biMultGE x₀ y₀ C_f m' := by
          have h := biMultGE_quotient_of_linear_factor x₀ y₀ A B C_f (m' + 1) hα0_ne hval
            (hBf_fac ▸ hbiB)
          simpa only [Nat.add_sub_cancel] using h
        -- Show `c_{m', 0} = 0` from `b_{m'+1, 0} = 0` and `δ₁ ≠ 0`.
        have hc_m0 : shiftCoeff x₀ y₀ C_f m' 0 = 0 := by
          have hb_m0 : shiftCoeff x₀ y₀ B_f (m' + 1) 0 = 0 := hb0 (m' + 1) (by omega)
          rw [hBf_fac, shiftCoeff_linear_mul_homog x₀ y₀ A B C_f hm1 (by omega) hval
            (by simpa only [Nat.add_sub_cancel] using hbiC)] at hb_m0
          rw [ite_eq_right_iff.mpr (fun h => by omega),
            ite_eq_left_iff.mpr (fun _ => by omega),
            Nat.add_sub_cancel, zero_sub, neg_eq_zero] at hb_m0
          exact (mul_eq_zero.mp (show δ₁ * shiftCoeff x₀ y₀ C_f m' 0 = 0 from hb_m0)).resolve_left
            hδ1_ne
        -- Show `shiftCoeff C_f p q = 0` whenever `d_A ≤ q` (since `deg B_f ≤ d_A` and `deg L = 1`).
        have hC_deg : ∀ p q, d_A ≤ q → shiftCoeff x₀ y₀ C_f p q = 0 := by
          intro p q hq
          by_cases hC0 : C_f = 0
          · subst hC0; simp [shiftCoeff, shiftBi_zero]
          · have hL_deg : (Polynomial.C A * Polynomial.X - Polynomial.C B).natDegree = 1 := by
              apply le_antisymm
              · refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ (by simp))
                exact (Polynomial.natDegree_mul_le).trans (by simp)
              · refine Polynomial.le_natDegree_of_ne_zero ?_
                simp [hA_ne]
            have hL_ne : Polynomial.C A * Polynomial.X - Polynomial.C B ≠ 0 := by
              intro h0; rw [h0, Polynomial.natDegree_zero] at hL_deg; omega
            have hBdeg_eq : B_f.natDegree = 1 + C_f.natDegree := by
              rw [hBf_fac, Polynomial.natDegree_mul hL_ne hC0, hL_deg]
            have hlt : (shiftBi x₀ y₀ C_f).natDegree < q :=
              (shiftBi_natDegree_le x₀ y₀ C_f).trans_lt (by omega)
            unfold shiftCoeff
            rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, Polynomial.coeff_zero]
        -- Show `shiftCoeff B_f p q = 0` whenever `d_A < q`.
        have hB_deg_coeff : ∀ p q, d_A < q → shiftCoeff x₀ y₀ B_f p q = 0 := by
          intro p q hq
          have hlt : (shiftBi x₀ y₀ B_f).natDegree < q :=
            (shiftBi_natDegree_le x₀ y₀ B_f).trans_lt (by omega)
          unfold shiftCoeff
          rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, Polynomial.coeff_zero]
        -- Truncate the sum to `M = min (m' + 1) d_A` (terms `q ≥ M` all vanish!).
        set M : ℕ := min (m' + 1) d_A
        have htrunc : ∑ q ∈ Finset.range (d_A + 1),
            (if q ≤ m' + 1 then shiftCoeff x₀ y₀ A_f (m' + 1 - q) q * δ₁ ^ q * α₀ ^ (d_A - q)
              else 0) =
            ∑ q ∈ Finset.range M,
              shiftCoeff x₀ y₀ A_f (m' + 1 - q) q * δ₁ ^ q * α₀ ^ (d_A - q) := by
          have hrhs : ∑ q ∈ Finset.range M,
              shiftCoeff x₀ y₀ A_f (m' + 1 - q) q * δ₁ ^ q * α₀ ^ (d_A - q) =
            ∑ q ∈ Finset.range M,
              (if q ≤ m' + 1 then shiftCoeff x₀ y₀ A_f (m' + 1 - q) q * δ₁ ^ q * α₀ ^ (d_A - q)
                else 0) := by
            refine Finset.sum_congr rfl fun q hq => ?_
            have hqM : q < M := Finset.mem_range.mp hq
            rw [ite_eq_left_iff.mpr (fun h => absurd (show q ≤ m' + 1 by omega) h)]
          rw [hrhs]
          symm
          refine Finset.sum_subset (Finset.range_mono (show M ≤ d_A + 1 by omega)) fun q hq hnot => ?_
          have hqd : q ≤ d_A := Nat.lt_succ_iff.mp (Finset.mem_range.mp hq)
          have hqM : M ≤ q := Nat.le_of_not_lt (by simpa [Finset.mem_range] using hnot)
          split_ifs with hqm
          · by_cases heqm : q = m' + 1
            · subst heqm
              have ha0m := ha0 (m' + 1) (by omega)
              simp [ha0m]
            · -- Here `q < m' + 1` and `q ≥ M = min (m' + 1) d_A`, so `q = d_A < m' + 1`!
              have hq_eq_dA : q = d_A := by omega
              have hpair_q := hpair (m' + 1 - q) q (by omega) (by omega)
              have hbq : shiftCoeff x₀ y₀ B_f (m' + 1 - q - 1) (q + 1) = 0 :=
                hB_deg_coeff _ _ (by omega)
              rw [hbq, add_zero] at hpair_q
              simp [hpair_q]
          · rfl
        rw [htrunc]
        -- Define telescoping sequence `T j` on `0 .. M`:
        let T : ℕ → R := fun j =>
          if j < M then shiftCoeff x₀ y₀ C_f (m' - j) j * δ₁ ^ j * α₀ ^ (d_A + 1 - j) else 0
        have htele : ∀ q ∈ Finset.range M,
            shiftCoeff x₀ y₀ A_f (m' + 1 - q) q * δ₁ ^ q * α₀ ^ (d_A - q) = T (q + 1) - T q := by
          intro q hq
          have hqM : q < M := Finset.mem_range.mp hq
          have hqm : q < m' + 1 := lt_of_lt_of_le hqM (min_le_left _ _)
          have hqd : q < d_A := lt_of_lt_of_le hqM (min_le_right _ _)
          have hpair_q := hpair (m' + 1 - q) q (by omega) (by omega)
          have ha_neg : shiftCoeff x₀ y₀ A_f (m' + 1 - q) q =
              -shiftCoeff x₀ y₀ B_f (m' - q) (q + 1) := by
            have heq : m' + 1 - q - 1 = m' - q := by omega
            rw [heq] at hpair_q
            exact eq_neg_of_add_eq_zero_left hpair_q
          have hb_exp := shiftCoeff_linear_mul_homog x₀ y₀ A B C_f hm1 (p := m' - q) (q := q + 1)
            (by omega) hval (by simpa only [Nat.add_sub_cancel] using hbiC)
          rw [← hBf_fac] at hb_exp
          simp only [show 1 ≤ q + 1 by omega, ite_true, Nat.add_sub_cancel] at hb_exp
          rw [ha_neg, hb_exp]
          have hTq : T q = shiftCoeff x₀ y₀ C_f (m' - q) q * δ₁ ^ q * α₀ ^ (d_A + 1 - q) := by
            dsimp [T]; simp [hqM]
          rw [hTq]
          have hα_exp : α₀ * α₀ ^ (d_A - q) = α₀ ^ (d_A + 1 - q) := by
            rw [show d_A + 1 - q = (d_A - q) + 1 by omega, pow_succ']
          by_cases hq1M : q + 1 < M
          · have hTq1 : T (q + 1) =
                shiftCoeff x₀ y₀ C_f (m' - (q + 1)) (q + 1) * δ₁ ^ (q + 1) * α₀ ^ (d_A - q) := by
              dsimp [T]
              rw [ite_eq_left_iff.mpr (fun h => absurd hq1M h), show d_A + 1 - (q + 1) = d_A - q by omega]
            rw [hTq1, ite_eq_left_iff.mpr (fun h => absurd (show 1 ≤ m' - q by omega) h)]
            have hsub_eq : m' - q - 1 = m' - (q + 1) := by omega
            rw [hsub_eq, pow_succ]
            dsimp [α₀, δ₁] at hα_exp ⊢
            linear_combination -shiftCoeff x₀ y₀ C_f (m' - q) q * δ₁ ^ q * hα_exp
          · have hTq1 : T (q + 1) = 0 := by dsimp [T]; simp [hq1M]
            rw [hTq1, zero_sub]
            have hsecond0 : (if 1 ≤ m' - q then
                δ₁ * shiftCoeff x₀ y₀ C_f (m' - q - 1) (q + 1) else 0) = 0 := by
              split_ifs with h1
              · -- Here `q + 1 ≥ M = min (m' + 1) d_A`, and `1 ≤ m' - q` means `q + 1 ≤ m' < m' + 1`,
                -- so `d_A ≤ q + 1` and `C_f` vanishes at `q + 1`!
                rw [hC_deg _ _ (by omega), mul_zero]
              · rfl
            change -(α₀ * shiftCoeff x₀ y₀ C_f (m' - q) q -
              (if 1 ≤ m' - q then δ₁ * shiftCoeff x₀ y₀ C_f (m' - q - 1) (q + 1) else 0)) *
              δ₁ ^ q * α₀ ^ (d_A - q) = _
            rw [hsecond0, sub_zero]
            linear_combination -shiftCoeff x₀ y₀ C_f (m' - q) q * δ₁ ^ q * hα_exp
        rw [Finset.sum_congr rfl htele, Finset.sum_range_sub T M]
        have hTM : T M = 0 := by dsimp [T]; simp
        have hT0 : T 0 = 0 := by
          dsimp [T]
          split_ifs
          · simp [hc_m0]
          · rfl
        rw [hTM, hT0, sub_self]

/-! ### Part 3: Multi-Site Divisibility, Wronskian Dichotomy, and Master Contradiction -/

/-- Coprimality of distinct linear factors `X - C a` and `X - C b` over any field `K`. -/
lemma isCoprime_X_sub_C {K : Type*} [Field K] {a b : K} (hab : a ≠ b) :
    IsCoprime (Polynomial.X - Polynomial.C a) (Polynomial.X - Polynomial.C b) := by
  refine ⟨Polynomial.C (b - a)⁻¹, Polynomial.C (a - b)⁻¹, ?_⟩
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hsum : (b - a)⁻¹ + (a - b)⁻¹ = 0 := by
    rw [show a - b = -(b - a) by ring, inv_neg, add_neg_cancel]
  have hconst : (b - a)⁻¹ * (-a) + (a - b)⁻¹ * (-b) = 1 := by
    rw [show a - b = -(b - a) by ring, inv_neg]
    calc
      (b - a)⁻¹ * (-a) + -(b - a)⁻¹ * (-b) = (b - a)⁻¹ * (b - a) := by ring
      _ = 1 := inv_mul_cancel₀ hba
  calc
    Polynomial.C (b - a)⁻¹ * (Polynomial.X - Polynomial.C a) +
        Polynomial.C (a - b)⁻¹ * (Polynomial.X - Polynomial.C b)
        = Polynomial.C ((b - a)⁻¹ + (a - b)⁻¹) * Polynomial.X +
          Polynomial.C ((b - a)⁻¹ * (-a) + (a - b)⁻¹ * (-b)) := by
          simp only [map_add, map_mul, map_neg]; ring
    _ = 1 := by rw [hsum, hconst, map_zero, zero_mul, zero_add, map_one]

/-- Multi-site divisibility product over any injective domain `dom : I ↪ K`. -/
theorem prod_linear_pow_dvd_of_forall_dvd {K I : Type*} [Field K] [DecidableEq I]
    (dom : I ↪ K) (S : Finset I) (e : I → ℕ) (P : K[X])
    (hdvd : ∀ i ∈ S, (Polynomial.X - Polynomial.C (dom i)) ^ (e i) ∣ P) :
    (∏ i ∈ S, (Polynomial.X - Polynomial.C (dom i)) ^ (e i)) ∣ P := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have h1 : (Polynomial.X - Polynomial.C (dom a)) ^ (e a) ∣ P :=
        hdvd a (Finset.mem_insert_self a s)
      have h2 : (∏ i ∈ s, (Polynomial.X - Polynomial.C (dom i)) ^ (e i)) ∣ P :=
        ih fun i hi => hdvd i (Finset.mem_insert_of_mem hi)
      have hcop : IsCoprime ((Polynomial.X - Polynomial.C (dom a)) ^ (e a))
          (∏ i ∈ s, (Polynomial.X - Polynomial.C (dom i)) ^ (e i)) := by
        refine IsCoprime.prod_right fun i hi => ?_
        have hne : dom a ≠ dom i := dom.injective.ne fun h => ha (h ▸ hi)
        exact ((isCoprime_X_sub_C hne).pow_left).pow_right
      exact hcop.mul_dvd h1 h2

lemma monic_prod_linear_pow {K I : Type*} [Field K] (dom : I ↪ K) (S : Finset I) (e : I → ℕ) :
    (∏ i ∈ S, (Polynomial.X - Polynomial.C (dom i)) ^ (e i)).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun i _ => (Polynomial.monic_X_sub_C (dom i)).pow (e i)

lemma natDegree_prod_linear_pow {K I : Type*} [Field K] (dom : I ↪ K) (S : Finset I) (e : I → ℕ) :
    (∏ i ∈ S, (Polynomial.X - Polynomial.C (dom i)) ^ (e i)).natDegree = ∑ i ∈ S, e i := by
  rw [Polynomial.natDegree_prod_of_monic _ _ fun i _ =>
    (Polynomial.monic_X_sub_C (dom i)).pow (e i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]

/-- Degree-vs-vanishing-order zero test over any field `K` and injective domain `dom : I ↪ K`. -/
theorem eq_zero_of_sum_dvd_gt_natDegree {K I : Type*} [Field K] [DecidableEq I]
    (dom : I ↪ K) (S : Finset I) (e : I → ℕ) (P : K[X])
    (hdvd : ∀ i ∈ S, (Polynomial.X - Polynomial.C (dom i)) ^ (e i) ∣ P)
    (hgt : P.natDegree < ∑ i ∈ S, e i) : P = 0 := by
  by_contra hne
  have hprod := prod_linear_pow_dvd_of_forall_dvd dom S e P hdvd
  have hle := Polynomial.natDegree_le_of_dvd hprod hne
  rw [natDegree_prod_linear_pow] at hle
  omega

/-- Over a field `K` with `char K = 0 ∨ P.natDegree < char K`, `P' = 0` forces `P` constant. -/
theorem eq_C_of_derivative_eq_zero {K : Type*} [Field K] {P : K[X]}
    (hchar : ringChar K = 0 ∨ P.natDegree < ringChar K) (hd : P.derivative = 0) :
    P = Polynomial.C (P.coeff 0) := by
  ext n
  rcases n with _ | n
  · simp
  · rw [Polynomial.coeff_C_succ]
    by_cases hlt : P.natDegree < n + 1
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt hlt
    · have hcoeff : ((n + 1 : ℕ) : K) * P.coeff (n + 1) = 0 := by
        have h := congrArg (fun f : K[X] => f.coeff n) hd
        rw [Polynomial.coeff_derivative, Polynomial.coeff_zero] at h
        simpa [mul_comm] using h
      have hcast_ne : ((n + 1 : ℕ) : K) ≠ 0 := by
        intro h0
        have hdvd : ringChar K ∣ n + 1 := ringChar.dvd h0
        rcases hchar with hc0 | hcp
        · rw [hc0, zero_dvd_iff] at hdvd; omega
        · have := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
          omega
      exact (mul_eq_zero.mp hcoeff).resolve_left hcast_ne

/-- If `IsCoprime A B`, `A ≠ 0`, `B' A - A' B = 0`, and `char K = 0 ∨ max(deg A, deg B) < char K`,
then `A` and `B` are both constants, so `B = C c * A` for a single constant `c : K`. -/
theorem const_of_coprime_wronskian_eq_zero {K : Type*} [Field K] {A B : K[X]}
    (hcop : IsCoprime A B) (hA_ne : A ≠ 0)
    (hchar : ringChar K = 0 ∨ max A.natDegree B.natDegree < ringChar K)
    (hW : B.derivative * A - A.derivative * B = 0) :
    ∃ c : K, B = Polynomial.C c * A := by
  have hEq : B.derivative * A = A.derivative * B := sub_eq_zero.mp hW
  have hAdvd : A ∣ A.derivative := by
    obtain ⟨u, v, huv⟩ := hcop
    refine ⟨u * A.derivative + v * B.derivative, ?_⟩
    linear_combination -A.derivative * huv - v * hEq
  have hBdvd : B ∣ B.derivative := by
    obtain ⟨u, v, huv⟩ := hcop
    refine ⟨u * A.derivative + v * B.derivative, ?_⟩
    linear_combination -B.derivative * huv + u * hEq
  have hA' : A.derivative = 0 := by
    by_contra hne
    have h1 := Polynomial.natDegree_le_of_dvd hAdvd hne
    have h2 : A.derivative.natDegree < A.natDegree := by
      have hpos : 0 < A.natDegree := by
        by_contra h0
        have hdeg0 : A.natDegree = 0 := by omega
        have hC := Polynomial.eq_C_of_natDegree_eq_zero hdeg0
        rw [hC, Polynomial.derivative_C] at hne
        exact hne rfl
      exact Polynomial.natDegree_derivative_lt (by omega)
    omega
  have hB' : B.derivative = 0 := by
    by_contra hne
    have h1 := Polynomial.natDegree_le_of_dvd hBdvd hne
    have h2 : B.derivative.natDegree < B.natDegree := by
      have hpos : 0 < B.natDegree := by
        by_contra h0
        have hdeg0 : B.natDegree = 0 := by omega
        have hC := Polynomial.eq_C_of_natDegree_eq_zero hdeg0
        rw [hC, Polynomial.derivative_C] at hne
        exact hne rfl
      exact Polynomial.natDegree_derivative_lt (by omega)
    omega
  have hAC : A = Polynomial.C (A.coeff 0) :=
    eq_C_of_derivative_eq_zero (hchar.imp_right fun h => lt_of_le_of_lt (le_max_left _ _) h) hA'
  have hBC : B = Polynomial.C (B.coeff 0) :=
    eq_C_of_derivative_eq_zero (hchar.imp_right fun h => lt_of_le_of_lt (le_max_right _ _) h) hB'
  have hA0 : A.coeff 0 ≠ 0 := by
    intro h0; rw [h0, map_zero] at hAC; exact hA_ne hAC
  refine ⟨B.coeff 0 / A.coeff 0, ?_⟩
  conv_lhs => rw [hBC]
  conv_rhs => rw [hAC]
  rw [← map_mul, Polynomial.coeff_C_zero, div_mul_cancel₀ _ hA0]

/-- When `y` agrees with a single constant `c` on `G`, any list of degree-`≤ d` polynomials
agreeing with `y` on `t > d + (|I| - |G|)` sites has cardinality `≤ 1`. -/
theorem constant_good_set_list_le_one {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    [DecidableEq K] (dom : I ↪ K) (y : I → K) (G : Finset I) (c : K) (d t : ℕ)
    (hconst : ∀ i ∈ G, y i = c) (ht : d + (Fintype.card I - G.card) < t)
    (S : Finset K[X])
    (hdeg : ∀ P ∈ S, P.natDegree ≤ d)
    (hagree : ∀ P ∈ S, t ≤ (Finset.univ.filter fun i => P.eval (dom i) = y i).card) :
    S.card ≤ 1 := by
  refine Finset.card_le_one.mpr fun P hP Q hQ => ?_
  have hEqC : ∀ R ∈ S, R = Polynomial.C c := by
    intro R hR
    by_contra hne
    have hRsub : (G.filter fun i => R.eval (dom i) = y i).image dom ⊆
        (R - Polynomial.C c).roots.toFinset := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
      rw [Finset.mem_filter] at hi
      rw [Multiset.mem_toFinset, Polynomial.mem_roots (sub_ne_zero.mpr hne), Polynomial.IsRoot,
        Polynomial.eval_sub, Polynomial.eval_C, hi.2, hconst i hi.1, sub_self]
    have hGagree : (G.filter fun i => R.eval (dom i) = y i).card ≤ d := by
      calc
        (G.filter fun i => R.eval (dom i) = y i).card
            = ((G.filter fun i => R.eval (dom i) = y i).image dom).card :=
              (Finset.card_image_of_injective _ dom.injective).symm
        _ ≤ (R - Polynomial.C c).roots.toFinset.card := Finset.card_le_card hRsub
        _ ≤ (R - Polynomial.C c).roots.card := Multiset.toFinset_card_le _
        _ ≤ (R - Polynomial.C c).natDegree := Polynomial.card_roots' _
        _ ≤ d := (Polynomial.natDegree_sub_le _ _).trans (max_le (hdeg R hR) (by simp))
    have hsplit : (Finset.univ.filter fun i => R.eval (dom i) = y i) ⊆
        (G.filter fun i => R.eval (dom i) = y i) ∪ (Finset.univ \ G) := by
      intro i hi
      by_cases hiG : i ∈ G
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hiG, (Finset.mem_filter.mp hi).2⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hiG⟩)
    have htot := hagree R hR
    have hcard_le := (Finset.card_le_card hsplit).trans (Finset.card_union_le _ _)
    have hsdiff : (Finset.univ \ G).card = Fintype.card I - G.card := by
      simp [Finset.card_sdiff]
    omega
  rw [hEqC P hP, hEqC Q hQ]

/-- Number of zeros of the nonzero rational Wronskian `W = B' A - A' B` on `G` is at most
`dA + dB - 1` whenever `1 ≤ dA + dB`. -/
theorem card_wronskian_zeros_le {K I : Type*} [Field K] [DecidableEq I] [DecidableEq K]
    (dom : I ↪ K) (G : Finset I) (A B : K[X]) (dA dB : ℕ)
    (hA : A.natDegree ≤ dA) (hB : B.natDegree ≤ dB)
    (hW : B.derivative * A - A.derivative * B ≠ 0) :
    (G.filter fun i => (B.derivative * A - A.derivative * B).eval (dom i) = 0).card ≤
      dA + dB - 1 := by
  set W := B.derivative * A - A.derivative * B
  have hdeg1 : (B.derivative * A).natDegree ≤ dA + dB - 1 := by
    by_cases hB0 : B.natDegree = 0
    · have hB' : B.derivative = 0 := by
        rw [Polynomial.eq_C_of_natDegree_eq_zero hB0, Polynomial.derivative_C]
      simp [hB']
    · have h1 := Polynomial.natDegree_derivative_lt hB0
      exact Polynomial.natDegree_mul_le.trans (by omega)
  have hdeg2 : (A.derivative * B).natDegree ≤ dA + dB - 1 := by
    by_cases hA0 : A.natDegree = 0
    · have hA' : A.derivative = 0 := by
        rw [Polynomial.eq_C_of_natDegree_eq_zero hA0, Polynomial.derivative_C]
      simp [hA']
    · have h1 := Polynomial.natDegree_derivative_lt hA0
      exact Polynomial.natDegree_mul_le.trans (by omega)
  have hWdeg : W.natDegree ≤ dA + dB - 1 :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le hdeg1 hdeg2)
  have hsub : (G.filter fun i => W.eval (dom i) = 0).image dom ⊆ W.roots.toFinset := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    rw [Finset.mem_filter] at hi
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hW, Polynomial.IsRoot]
    exact hi.2
  calc
    (G.filter fun i => W.eval (dom i) = 0).card
        = ((G.filter fun i => W.eval (dom i) = 0).image dom).card :=
          (Finset.card_image_of_injective _ dom.injective).symm
    _ ≤ W.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ W.roots.card := Multiset.toFinset_card_le _
    _ ≤ W.natDegree := Polynomial.card_roots' _
    _ ≤ dA + dB - 1 := hWdeg

/-- **Master Common-Linear-Factor Theorem (Steps 1–3 Combined, Arbitrary Field & Domain).**
If `A, B : K[X]` are coprime (`A ≠ 0`, `deg A ≤ d`, `deg B ≤ 2d`, `B' A - A' B ≠ 0`),
`A_f, B_f : BiPoly K` have `deg_{Y₀}(A_f) ≤ d_A`, `deg_{Y₀}(B_f) ≤ d_B ≤ d_A` with weighted
bounds `W_A, W_B`, and on the good site set `G` we have `B(x_i) = y_i A(x_i)` and
`LinearLocalContactGE x_i y_i A_f B_f (k i)` with:
- Step 1 slack: `W_B + d_B * d < ∑ i ∈ G, (k i - 1)`,
- Step 3 slack: `W_A + d_A * d + (3 * d - 1) < ∑ i ∈ G, k i`,
then **`(C A * X - C B)` divides BOTH `B_f` and `A_f` in `BiPoly K`**! -/
theorem common_linear_factor_of_complementary_contact {K I : Type*} [Field K] [DecidableEq I]
    (dom : I ↪ K) (y : I → K) (G : Finset I) (k : I → ℕ)
    (A B : K[X]) (A_f B_f : BiPoly K) (d d_A d_B W_A W_B : ℕ)
    (hcop : IsCoprime A B) (hA_ne : A ≠ 0)
    (hdegA_rat : A.natDegree ≤ d) (hdegB_rat : B.natDegree ≤ 2 * d)
    (hW_ne : B.derivative * A - A.derivative * B ≠ 0)
    (hAf_deg : A_f.natDegree ≤ d_A) (hBf_deg : B_f.natDegree ≤ d_B) (hdB_le : d_B ≤ d_A)
    (hWB : ∀ q ≤ d_B, (B_f.coeff q).natDegree + q * d ≤ W_B)
    (hWA : ∀ q ≤ d_A, (A_f.coeff q).natDegree + q * d ≤ W_A)
    (hgood : ∀ i ∈ G, B.eval (dom i) = y i * A.eval (dom i) ∧
      LinearLocalContactGE (dom i) (y i) A_f B_f (k i))
    (hstep1 : W_B + d_B * d < ∑ i ∈ G, (k i - 1))
    (hstep3 : W_A + d_A * d + (3 * d - 1) < ∑ i ∈ G, k i) :
    (Polynomial.C A * Polynomial.X - Polynomial.C B) ∣ B_f ∧
      (Polynomial.C A * Polynomial.X - Polynomial.C B) ∣ A_f := by
  classical
  -- Step 1: Show `R_B = ratPullback A B d_B B_f = 0`, hence `(C A * X - C B) ∣ B_f`.
  have hRB_deg : (ratPullback A B d_B B_f).natDegree ≤ W_B + d_B * d :=
    natDegree_ratPullback_le A B d_B d d W_B B_f hdegA_rat (by omega) hWB
  have hRB_dvd : ∀ i ∈ G, (Polynomial.X - Polynomial.C (dom i)) ^ (k i - 1) ∣
      ratPullback A B d_B B_f := by
    intro i hi
    obtain ⟨hval, hcon⟩ := hgood i hi
    have hbiB := (local_contact_vanishing_equations (dom i) (y i) A_f B_f (k i) hcon).2.1
    exact pow_dvd_ratPullback_of_biMultGE (dom i) (y i) A B d_B (k i - 1) B_f hBf_deg hval hbiB
  have hRB_zero : ratPullback A B d_B B_f = 0 :=
    eq_zero_of_sum_dvd_gt_natDegree dom G (fun i => k i - 1) _ hRB_dvd
      (lt_of_le_of_lt hRB_deg hstep1)
  have hBf_dvd : (Polynomial.C A * Polynomial.X - Polynomial.C B) ∣ B_f :=
    linear_dvd_of_ratPullback_eq_zero hcop hBf_deg hRB_zero
  obtain ⟨C_f, hBf_fac⟩ := hBf_dvd
  -- Step 2 & 3: Boost `ord(R_A) ≥ k i` off zeros of `W = B' A - A' B` (`≥ k i - 1` on zeros).
  set W := B.derivative * A - A.derivative * B
  let eA : I → ℕ := fun i => if W.eval (dom i) = 0 then k i - 1 else k i
  have hRA_dvd : ∀ i ∈ G, (Polynomial.X - Polynomial.C (dom i)) ^ (eA i) ∣
      ratPullback A B d_A A_f := by
    intro i hi
    obtain ⟨hval, hcon⟩ := hgood i hi
    dsimp [eA]
    split_ifs with hWi
    · have hbiA := (local_contact_vanishing_equations (dom i) (y i) A_f B_f (k i) hcon).1
      exact pow_dvd_ratPullback_of_biMultGE (dom i) (y i) A B d_A (k i - 1) A_f hAf_deg hval hbiA
    · exact pow_dvd_ratPullback_A_of_contact (dom i) (y i) A B A_f B_f C_f d_A (k i)
        hA_ne hAf_deg (hBf_deg.trans hdB_le) hBf_fac hcon hval hWi
  have hZ_card : (G.filter fun i => W.eval (dom i) = 0).card ≤ 3 * d - 1 := by
    have h := card_wronskian_zeros_le dom G A B d (2 * d) hdegA_rat hdegB_rat hW_ne
    have h3 : d + 2 * d = 3 * d := by omega
    rw [h3] at h
    exact h
  have hsum_eA : ∑ i ∈ G, k i ≤ (∑ i ∈ G, eA i) + (G.filter fun i => W.eval (dom i) = 0).card := by
    rw [Finset.card_filter, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    dsimp [eA]
    split_ifs <;> omega
  have hRA_deg : (ratPullback A B d_A A_f).natDegree ≤ W_A + d_A * d :=
    natDegree_ratPullback_le A B d_A d d W_A A_f hdegA_rat (by omega) hWA
  have hRA_zero : ratPullback A B d_A A_f = 0 :=
    eq_zero_of_sum_dvd_gt_natDegree dom G eA _ hRA_dvd (by omega)
  have hAf_dvd : (Polynomial.C A * Polynomial.X - Polynomial.C B) ∣ A_f :=
    linear_dvd_of_ratPullback_eq_zero hcop hAf_deg hRA_zero
  exact ⟨⟨C_f, hBf_fac⟩, hAf_dvd⟩

/-- **Irreducibility Contradiction in `K[X][Y₀][Y₁]`.**
Whenever `A ≠ 0` and `A_f ≠ 0`, a common factor `(C A * X - C B)` of `A_f` and `B_f` proves
that `f = C A_f * X + C B_f` is **reducible** in `Polynomial (BiPoly K) = K[X][Y₀][Y₁]`. -/
theorem not_irreducible_of_common_linear_factor {K : Type*} [Field K]
    {A B : K[X]} {A_f B_f : BiPoly K} (hA_ne : A ≠ 0) (hAf_ne : A_f ≠ 0)
    (hdvdB : (Polynomial.C A * Polynomial.X - Polynomial.C B) ∣ B_f)
    (hdvdA : (Polynomial.C A * Polynomial.X - Polynomial.C B) ∣ A_f) :
    ¬ Irreducible (Polynomial.C A_f * Polynomial.X + Polynomial.C B_f : Polynomial (BiPoly K)) := by
  intro hirr
  set L : BiPoly K := Polynomial.C A * Polynomial.X - Polynomial.C B
  obtain ⟨Aq, hAq⟩ := hdvdA
  obtain ⟨Bq, hBq⟩ := hdvdB
  have hfac : Polynomial.C A_f * Polynomial.X + Polynomial.C B_f =
      Polynomial.C L * (Polynomial.C Aq * Polynomial.X + Polynomial.C Bq) := by
    rw [hAq, hBq, map_mul, map_mul]
    ring
  rcases hirr.isUnit_or_isUnit hfac with hL_unit | hQ_unit
  · -- `C L` cannot be a unit since `L.natDegree = 1`.
    have hLu : IsUnit L := Polynomial.isUnit_C.mp hL_unit
    have hL_deg0 : L.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hLu
    have hL_coeff1 : L.coeff 1 = A := by
      dsimp [L]
      simp
    have hge1 : 1 ≤ L.natDegree := Polynomial.le_natDegree_of_ne_zero (hL_coeff1.symm ▸ hA_ne)
    omega
  · -- `C Aq * X + C Bq` cannot be a unit since `Aq ≠ 0` (`A_f = L * Aq ≠ 0`), so its `Y₁`-degree is 1.
    have hAq_ne : Aq ≠ 0 := fun h0 => hAf_ne (by rw [hAq, h0, mul_zero])
    have hQ_deg0 : (Polynomial.C Aq * Polynomial.X + Polynomial.C Bq).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hQ_unit
    have hQ_coeff1 : (Polynomial.C Aq * Polynomial.X + Polynomial.C Bq).coeff 1 = Aq := by
      simp
    have hge1 : 1 ≤ (Polynomial.C Aq * Polynomial.X + Polynomial.C Bq).natDegree :=
      Polynomial.le_natDegree_of_ne_zero (hQ_coeff1.symm ▸ hAq_ne)
    omega

/-- **Complete Constant-vs-Nonconstant Dichotomy (`#242` Master Theorem).**
Over ANY field `K` with `char K = 0 ∨ 2 * d < char K` (including `𝔽_p`, `𝔽̄_p`, char `0`),
ANY injective domain `dom : I ↪ K`, and ANY coprime rational representation `(A, B)` of `y` on
`G ⊆ I` (`A ≠ 0`, `A(x_i) ≠ 0` on `G`, `deg A ≤ d`, `deg B ≤ 2d`), for ANY irreducible
`f = C A_f * X + C B_f` with `A_f ≠ 0`, `deg_{Y₀} A_f ≤ d_A`, `deg_{Y₀} B_f ≤ d_B ≤ d_A`,
and Steps 1 & 3 slacks satisfied, EVERY list `S` of degree-`≤ d` codewords agreeing with `y` on
`t > d + (|I| - |G|)` sites has **cardinality `≤ 1`**! -/
theorem complementary_pencil_dichotomy {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    [DecidableEq K] (dom : I ↪ K) (y : I → K) (G : Finset I) (k : I → ℕ)
    (A B : K[X]) (A_f B_f : BiPoly K) (d t d_A d_B W_A W_B : ℕ)
    (hchar : ringChar K = 0 ∨ 2 * d < ringChar K)
    (hcop : IsCoprime A B) (hA_ne : A ≠ 0)
    (hdegA_rat : A.natDegree ≤ d) (hdegB_rat : B.natDegree ≤ 2 * d)
    (hAf_ne : A_f ≠ 0) (hAf_deg : A_f.natDegree ≤ d_A) (hBf_deg : B_f.natDegree ≤ d_B)
    (hdB_le : d_B ≤ d_A)
    (hWB : ∀ q ≤ d_B, (B_f.coeff q).natDegree + q * d ≤ W_B)
    (hWA : ∀ q ≤ d_A, (A_f.coeff q).natDegree + q * d ≤ W_A)
    (hgood : ∀ i ∈ G, A.eval (dom i) ≠ 0 ∧ B.eval (dom i) = y i * A.eval (dom i) ∧
      LinearLocalContactGE (dom i) (y i) A_f B_f (k i))
    (hstep1 : W_B + d_B * d < ∑ i ∈ G, (k i - 1))
    (hstep3 : W_A + d_A * d + (3 * d - 1) < ∑ i ∈ G, k i)
    (hirr : Irreducible (Polynomial.C A_f * Polynomial.X + Polynomial.C B_f : Polynomial (BiPoly K)))
    (ht : d + (Fintype.card I - G.card) < t)
    (S : Finset K[X])
    (hdeg : ∀ P ∈ S, P.natDegree ≤ d)
    (hagree : ∀ P ∈ S, t ≤ (Finset.univ.filter fun i => P.eval (dom i) = y i).card) :
    S.card ≤ 1 := by
  by_cases hW : B.derivative * A - A.derivative * B = 0
  · obtain ⟨c, hBc⟩ := const_of_coprime_wronskian_eq_zero hcop hA_ne
      (hchar.imp_right fun h => by omega) hW
    refine constant_good_set_list_le_one dom y G c d t (fun i hi => ?_) ht S hdeg hagree
    obtain ⟨hAi_ne, hval, -⟩ := hgood i hi
    have hBeval : B.eval (dom i) = c * A.eval (dom i) := by
      rw [hBc, Polynomial.eval_mul, Polynomial.eval_C]
    exact mul_right_cancel₀ hAi_ne (hval.symm.trans hBeval)
  · obtain ⟨hdvdB, hdvdA⟩ := common_linear_factor_of_complementary_contact dom y G k A B A_f B_f
      d d_A d_B W_A W_B hcop hA_ne hdegA_rat hdegB_rat hW hAf_deg hBf_deg hdB_le hWB hWA
      (fun i hi => ⟨(hgood i hi).2.1, (hgood i hi).2.2⟩) hstep1 hstep3
    exact False.elim (not_irreducible_of_common_linear_factor hA_ne hAf_ne hdvdB hdvdA hirr)

/-! ### Part 4: Production Rate-`1/4` (`n = 2³⁰`, `e = 536,870,914`) Sliver Annihilation -/

/-- Production Rate-`1/4` (`n = 2³⁰`, `d = 2²⁸ - 1`, `t = 2d = 536,870,910`) annihilation of the
entire `#228`/`#242` Rate-`1/4` sliver (`d_A = 4`, `d_B ≤ 2`, `5d ≤ W_B`, `W_A + d ≤ W_B + 1`,
covering all `ω_f ∈ [5.00, ∞)` including `[5.00, 5.06]`) over ANY field `K` of characteristic `0`
or `> 536,870,910` (including `𝔽_{P₁}`, `𝔽_{P₂}`, `AlgebraicClosure 𝔽_{P₁}`, `AlgebraicClosure 𝔽_{P₂}`)
and ANY injective domain of length `2³⁰`.

Even with `0.04` finite-`m` drop below `k_thr(ω_f) = 1 + (ω_f - 1)/2`
(`25 * ∑_{i ∈ I} k_i ≥ 50 * W_B + 46 * d`), `|E| ≤ 3,080` bad sites, and `k_i ≤ 20,000` on `E`
(covering every `m_q ∈ {160, 256, 512, 1024, ...}`), BOTH Step 1 (`R_B`) and Step 3 (`R_A`) hold
with `> 163.8M` roots of slack (zero LP, zero `Disc(A_f)`, zero `Res(A_f, B_f)` needed)! -/
theorem production_quarter_sliver_closed {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    [DecidableEq K] (dom : I ↪ K) (y : I → K)
    (hcard : Fintype.card I = 1073741824)
    (hchar : ringChar K = 0 ∨ 536870910 < ringChar K)
    (E : Finset I) (hE : E.card ≤ 3080)
    (k : I → ℕ) (hkE : ∀ i ∈ E, k i ≤ 20000)
    (A B : K[X]) (A_f B_f : BiPoly K) (d_B W_A W_B : ℕ)
    (hcop : IsCoprime A B) (hA_ne : A ≠ 0)
    (hdegA_rat : A.natDegree ≤ 268435455) (hdegB_rat : B.natDegree ≤ 536870910)
    (hAf_ne : A_f ≠ 0) (hAf_deg : A_f.natDegree ≤ 4) (hBf_deg : B_f.natDegree ≤ d_B)
    (hdB_le : d_B ≤ 2)
    (hWB_lo : 5 * 268435455 ≤ W_B) (hWA_le : W_A + 268435455 ≤ W_B + 1)
    (hWB : ∀ q ≤ d_B, (B_f.coeff q).natDegree + q * 268435455 ≤ W_B)
    (hWA : ∀ q ≤ 4, (A_f.coeff q).natDegree + q * 268435455 ≤ W_A)
    (hgood : ∀ i ∈ Finset.univ \ E, A.eval (dom i) ≠ 0 ∧ B.eval (dom i) = y i * A.eval (dom i) ∧
      LinearLocalContactGE (dom i) (y i) A_f B_f (k i))
    (havg : 50 * W_B + 46 * 268435455 ≤ 25 * ∑ i : I, k i)
    (hirr : Irreducible (Polynomial.C A_f * Polynomial.X + Polynomial.C B_f : Polynomial (BiPoly K)))
    (S : Finset K[X])
    (hdeg : ∀ P ∈ S, P.natDegree ≤ 268435455)
    (hagree : ∀ P ∈ S, 536870910 ≤ (Finset.univ.filter fun i => P.eval (dom i) = y i).card) :
    S.card ≤ 1 := by
  set G : Finset I := Finset.univ \ E
  have hGcard : G.card = 1073741824 - E.card := by
    simp [G, Finset.card_sdiff, hcard]
  have hsum_split : ∑ i : I, k i = (∑ i ∈ G, k i) + (∑ i ∈ E, k i) := by
    have hunion : G ∪ E = Finset.univ := Finset.sdiff_union_of_subset (Finset.subset_univ E)
    have hdisj : Disjoint G E := Finset.sdiff_disjoint
    rw [← hunion, Finset.sum_union hdisj]
  have hsumE : ∑ i ∈ E, k i ≤ 3080 * 20000 := by
    calc
      ∑ i ∈ E, k i ≤ ∑ _i ∈ E, 20000 := Finset.sum_le_sum hkE
      _ = E.card * 20000 := by simp
      _ ≤ 3080 * 20000 := Nat.mul_le_mul_right 20000 hE
  have hsum_sub : ∑ i ∈ G, k i ≤ (∑ i ∈ G, (k i - 1)) + G.card := by
    calc
      ∑ i ∈ G, k i ≤ ∑ i ∈ G, ((k i - 1) + 1) := Finset.sum_le_sum fun i _ => by omega
      _ = (∑ i ∈ G, (k i - 1)) + G.card := by rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
  refine complementary_pencil_dichotomy dom y G k A B A_f B_f
    268435455 536870910 4 d_B W_A W_B
    (by simpa only [show 2 * 268435455 = 536870910 by norm_num] using hchar)
    hcop hA_ne hdegA_rat (by simpa only [show 2 * 268435455 = 536870910 by norm_num] using hdegB_rat)
    hAf_ne hAf_deg hBf_deg (by omega) hWB hWA hgood ?_ ?_ hirr ?_ S hdeg hagree
  · -- Step 1 slack (`> 163.8M` roots!)
    have hdB_mul : d_B * 268435455 ≤ 2 * 268435455 := Nat.mul_le_mul_right _ hdB_le
    omega
  · -- Step 3 slack (`> 163.8M` roots!)
    omega
  · -- Constant-case list-size threshold `d + |E| < t`:
    omega

local instance : Fact (Nat.Prime ArkLib.ProximityGap.PrizeShapePrimeP30.P) :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30.prime_P⟩
local instance : Fact (Nat.Prime ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P⟩

/-- Characteristic check for `P₁` (first designated prime): `536,870,910 < P₁`. -/
theorem first_prime_char_gt :
    536870910 < ringChar (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P) := by
  rw [ZMod.ringChar_zmod_n]
  decide

/-- Characteristic check for `P₂` (second designated prime): `536,870,910 < P₂`. -/
theorem second_prime_char_gt :
    536870910 < ringChar (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) := by
  rw [ZMod.ringChar_zmod_n]
  decide

/-- First designated prime `P₁` instantiation of `production_quarter_sliver_closed`. -/
theorem first_prime_quarter_sliver_closed {I : Type*} [Fintype I] [DecidableEq I]
    (dom : I ↪ ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
    (y : I → ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)
    (hcard : Fintype.card I = 1073741824)
    (E : Finset I) (hE : E.card ≤ 3080)
    (k : I → ℕ) (hkE : ∀ i ∈ E, k i ≤ 20000)
    (A B : (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)[X])
    (A_f B_f : BiPoly (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P))
    (d_B W_A W_B : ℕ)
    (hcop : IsCoprime A B) (hA_ne : A ≠ 0)
    (hdegA_rat : A.natDegree ≤ 268435455) (hdegB_rat : B.natDegree ≤ 536870910)
    (hAf_ne : A_f ≠ 0) (hAf_deg : A_f.natDegree ≤ 4) (hBf_deg : B_f.natDegree ≤ d_B)
    (hdB_le : d_B ≤ 2)
    (hWB_lo : 5 * 268435455 ≤ W_B) (hWA_le : W_A + 268435455 ≤ W_B + 1)
    (hWB : ∀ q ≤ d_B, (B_f.coeff q).natDegree + q * 268435455 ≤ W_B)
    (hWA : ∀ q ≤ 4, (A_f.coeff q).natDegree + q * 268435455 ≤ W_A)
    (hgood : ∀ i ∈ Finset.univ \ E, A.eval (dom i) ≠ 0 ∧ B.eval (dom i) = y i * A.eval (dom i) ∧
      LinearLocalContactGE (dom i) (y i) A_f B_f (k i))
    (havg : 50 * W_B + 46 * 268435455 ≤ 25 * ∑ i : I, k i)
    (hirr : Irreducible (Polynomial.C A_f * Polynomial.X + Polynomial.C B_f :
      Polynomial (BiPoly (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P))))
    (S : Finset (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30.P)[X])
    (hdeg : ∀ P ∈ S, P.natDegree ≤ 268435455)
    (hagree : ∀ P ∈ S, 536870910 ≤ (Finset.univ.filter fun i => P.eval (dom i) = y i).card) :
    S.card ≤ 1 :=
  production_quarter_sliver_closed dom y hcard (Or.inr first_prime_char_gt) E hE k hkE A B A_f B_f
    d_B W_A W_B hcop hA_ne hdegA_rat hdegB_rat hAf_ne hAf_deg hBf_deg hdB_le hWB_lo hWA_le
    hWB hWA hgood havg hirr S hdeg hagree

/-- Second designated prime `P₂` instantiation of `production_quarter_sliver_closed`. -/
theorem second_prime_quarter_sliver_closed {I : Type*} [Fintype I] [DecidableEq I]
    (dom : I ↪ ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
    (y : I → ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)
    (hcard : Fintype.card I = 1073741824)
    (E : Finset I) (hE : E.card ≤ 3080)
    (k : I → ℕ) (hkE : ∀ i ∈ E, k i ≤ 20000)
    (A B : (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)[X])
    (A_f B_f : BiPoly (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P))
    (d_B W_A W_B : ℕ)
    (hcop : IsCoprime A B) (hA_ne : A ≠ 0)
    (hdegA_rat : A.natDegree ≤ 268435455) (hdegB_rat : B.natDegree ≤ 536870910)
    (hAf_ne : A_f ≠ 0) (hAf_deg : A_f.natDegree ≤ 4) (hBf_deg : B_f.natDegree ≤ d_B)
    (hdB_le : d_B ≤ 2)
    (hWB_lo : 5 * 268435455 ≤ W_B) (hWA_le : W_A + 268435455 ≤ W_B + 1)
    (hWB : ∀ q ≤ d_B, (B_f.coeff q).natDegree + q * 268435455 ≤ W_B)
    (hWA : ∀ q ≤ 4, (A_f.coeff q).natDegree + q * 268435455 ≤ W_A)
    (hgood : ∀ i ∈ Finset.univ \ E, A.eval (dom i) ≠ 0 ∧ B.eval (dom i) = y i * A.eval (dom i) ∧
      LinearLocalContactGE (dom i) (y i) A_f B_f (k i))
    (havg : 50 * W_B + 46 * 268435455 ≤ 25 * ∑ i : I, k i)
    (hirr : Irreducible (Polynomial.C A_f * Polynomial.X + Polynomial.C B_f :
      Polynomial (BiPoly (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P))))
    (S : Finset (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)[X])
    (hdeg : ∀ P ∈ S, P.natDegree ≤ 268435455)
    (hagree : ∀ P ∈ S, 536870910 ≤ (Finset.univ.filter fun i => P.eval (dom i) = y i).card) :
    S.card ≤ 1 :=
  production_quarter_sliver_closed dom y hcard (Or.inr second_prime_char_gt) E hE k hkE A B A_f B_f
    d_B W_A W_B hcop hA_ne hdegA_rat hdegB_rat hAf_ne hAf_deg hBf_deg hdB_le hWB_lo hWA_le
    hWB hWA hgood havg hirr S hdeg hagree

/-! ### Part 5: Complementary-Pencil Discriminant & Derivative-Pell Identities -/

/-- Exact discriminant square identity for complementary pairs `(f, g)` in a
`ComplementaryListPencil`:
`(f - g)^2 = (S + A U)^2 - 4(P + B U)` together with the fixed divisor relation
`(A f - B)(A g - B) = B^2 - S A B + P A^2` (invoking `ComplementaryListPencil.common_product`). -/
theorem complementary_pair_identities {R : Type*} [CommRing R] (A B S P U f g : R)
    (sum_eq : f + g = S + A * U) (product_eq : f * g = P + B * U) :
    (A * f - B) * (A * g - B) = B ^ 2 - S * A * B + P * A ^ 2 ∧
      (f - g) ^ 2 = (S + A * U) ^ 2 - 4 * (P + B * U) := by
  refine ⟨ProximityGap.ComplementaryListPencil.common_product A B S P U f g sum_eq product_eq, ?_⟩
  linear_combination (f + g + (S + A * U)) * sum_eq - 4 * product_eq

/-- Algebraic Derivative-Pell identity (`P_t U̇ = D_t Ḋ_t` in `#242`):
for a formal 1-parameter deformation `(U, D)` of the complementary-pencil Pell equation
`D^2 = (S + A U)^2 - 4(P + B U)` (with `(U', D')` its formal derivative holding `A, B, S, P`
fixed), if `2` is a non-zero-divisor (e.g. `char K ≠ 2`), then
`(A * (S + A * U) - 2 * B) * U' = D * D'`. -/
theorem complementary_derivative_pell_identity {K : Type*} [Field K]
    (hchar2 : (2 : K) ≠ 0) (A B S U U' D D' : K)
    (hdiff : 2 * D * D' = 2 * (S + A * U) * (A * U') - 4 * (B * U')) :
    (A * (S + A * U) - 2 * B) * U' = D * D' := by
  apply mul_left_cancel₀ hchar2
  linear_combination -hdiff

end ArkLib.ProximityGap.Frontier.QuarterComplementaryContactClosure

#print axioms ArkLib.ProximityGap.Frontier.QuarterComplementaryContactClosure.natDegree_ratPullback_le
#print axioms ArkLib.ProximityGap.Frontier.QuarterComplementaryContactClosure.linear_dvd_of_ratPullback_eq_zero
#print axioms ArkLib.ProximityGap.Frontier.QuarterComplementaryContactClosure.ratPullback_comp_shift
#print axioms ArkLib.ProximityGap.Frontier.QuarterComplementaryContactClosure.pow_dvd_ratPullback_of_biMultGE
#print axioms ArkLib.ProximityGap.Frontier.QuarterComplementaryContactClosure.pow_dvd_ratPullback_A_of_contact
#print axioms ArkLib.ProximityGap.Frontier.QuarterComplementaryContactClosure.common_linear_factor_of_complementary_contact
#print axioms ArkLib.ProximityGap.Frontier.QuarterComplementaryContactClosure.not_irreducible_of_common_linear_factor
#print axioms ArkLib.ProximityGap.Frontier.QuarterComplementaryContactClosure.complementary_pencil_dichotomy
#print axioms ArkLib.ProximityGap.Frontier.QuarterComplementaryContactClosure.production_quarter_sliver_closed
#print axioms ArkLib.ProximityGap.Frontier.QuarterComplementaryContactClosure.first_prime_quarter_sliver_closed
#print axioms ArkLib.ProximityGap.Frontier.QuarterComplementaryContactClosure.second_prime_quarter_sliver_closed
#print axioms ArkLib.ProximityGap.Frontier.QuarterComplementaryContactClosure.complementary_pair_identities
#print axioms ArkLib.ProximityGap.Frontier.QuarterComplementaryContactClosure.complementary_derivative_pell_identity
