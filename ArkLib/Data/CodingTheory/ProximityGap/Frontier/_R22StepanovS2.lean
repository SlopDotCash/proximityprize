/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R21StepanovS1
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R20StepanovScaffold
import ArkLib.ToMathlib.Polynomial.DivByMonicLinear

/-!
# LANE S2 (#466 round 22): auxiliary-polynomial EXISTENCE for the cubic Stepanov proof

Step S2 of `CubicStepanovUpper` (`_R20StepanovScaffold.lean`): given the classical parameter
budget, there EXISTS a nonzero auxiliary polynomial
`P = ∑_{j<J} (f^m·a_j + f^{m+e}·b_j)·X^{qj}` (`f = X(X−u)(X−v)`, `e = (q−1)/2`,
`deg a_j, deg b_j ≤ D`) of controlled degree whose Hasse derivatives of all orders `< m`
vanish at every point of the positive-fiber set `N⁺ = {s : f(s)^e = 1}`.

## The classical bookkeeping (validated numerically before formalization)

Vanishing is NOT imposed pointwise on `N⁺` (too many conditions).  Instead:
* `X^{qj}` is Hasse-derivative-constant for orders `0 < k < q` (base-`p` binomial vanishing
  `C(qj,k) ≡ 0 mod p`, proven here via the Frobenius identity `(1+X)^{q} = 1+X^{q}`);
* `f^{N−k} ∣ D^{(k)}(f^N·a)` (proven here by Leibniz induction), with quotient `r_{jk}` of
  degree `≤ D + 2k`, LINEAR in `a`;
* on `N⁺`, `f(s) ≠ 0`, `f(s)^e = 1`, `s^q = s`, so
  `(D^{(k)}P)(s) = f(s)^{m−k}·W_k(s)` where `W_k := ∑_j (r_{jk}+s_{jk})·X^j` has degree
  `≤ D + 2k + J − 1`.
* Imposing `W_k = 0` IDENTICALLY for `k < m` is `m(D+2m+J)` linear conditions (uniform
  bound) on `2J(D+1)` unknowns; when `m(D+2m+J) < 2J(D+1)` rank–nullity gives a nonzero
  kernel vector; `P ≠ 0` then follows from S1 (`cubic_aux_ne_zero`, budget `2D+3 < q`), and
  `deg P ≤ 3(m+e) + D + q(J−1)`.

Combining with the round-20 engine (`hasseDeriv_stepanov_degree_count`) yields the capstone
`m·#N⁺ ≤ 3(m+e) + D + q(J−1)` — for ANY admissible parameter triple `(m, J, D)`.

Probe: `scratchpad/probe_r22_s2_existence.py` — q = 13, 17, several `(u,v,m,J,D)`: kernel
vector found, exact divisibility verified, `P ≠ 0`, all Hasse derivatives of orders `< m`
vanish on `N⁺`, `m·#N⁺ ≤ deg P`.  All checks pass.

## What remains after S2 (honest scope — the S3 lane)

`CubicStepanovUpper` itself still needs, from `cubic_stepanov_positive_fiber_bound`:
1. the Euler-criterion bridge `quadraticChar F (f s) = 1 ↔ f(s)^{(q−1)/2} = 1` and the
   count identity `∑_s χ(f s) = 2·#N⁺ − (q − 3)` (via `cubic_zero_count`);
2. an explicit admissible parameter choice, e.g. `m ≈ ⌊√(2q/5)⌋`, `J = ⌈m/2⌉+1`,
   `D = ⌊(q−4)/2⌋` (satisfiable for `q` above an explicit threshold — check
   `m(D+2m+J) < 2J(D+1)` and `2D+3 < q`), giving `N⁺ ≤ q/2 + O(√q)` hence
   `∑ χ ≤ B` with `B = O(√q)`;
3. small-`q` cases below the threshold (trivial bound `q ≤ B` or `decide`).
None of that is claimed here.  No closure claimed.
-/

namespace ArkLib.ProximityGap.Frontier.R22StepanovS2

open Polynomial Finset
open ArkLib.ProximityGap.Frontier.R21StepanovS1
open ArkLib.ProximityGap.Frontier.R20StepanovScaffold

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

/-! ## 1. Base-`p` binomial vanishing: `X^{qj}` is Hasse-constant below order `q` -/

/-- `C(p^μ·j, k) = 0` in characteristic `p` for `0 < k < p^μ`: coefficient comparison in
`(1+X)^{p^μ j} = (1+X^{p^μ})^j` (Frobenius). -/
theorem cast_choose_prime_pow_mul_eq_zero {F : Type*} [Field F] {p : ℕ} (hp : p.Prime)
    [CharP F p] (μ j k : ℕ) (hk0 : 0 < k) (hkq : k < p ^ μ) :
    (((p ^ μ * j).choose k : ℕ) : F) = 0 := by
  haveI := Fact.mk hp
  haveI : CharP (Polynomial F) p := inferInstance
  haveI : ExpChar (Polynomial F) p := ExpChar.prime hp
  have key : ((1 : F[X]) + X) ^ (p ^ μ * j) = (1 + X ^ p ^ μ) ^ j := by
    rw [pow_mul, add_pow_char_pow, one_pow]
  have hL : (((1 : F[X]) + X) ^ (p ^ μ * j)).coeff k = (((p ^ μ * j).choose k : ℕ) : F) :=
    coeff_one_add_X_pow F (p ^ μ * j) k
  have hR : (((1 : F[X]) + X ^ p ^ μ) ^ j).coeff k = 0 := by
    rw [add_pow]
    rw [finset_sum_coeff]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [one_pow, one_mul, ← C_eq_natCast, mul_comm, ← pow_mul, coeff_C_mul, coeff_X_pow]
    have hne : p ^ μ * (j - i) ≠ k := by
      rcases Nat.eq_zero_or_pos (j - i) with hi | hi
      · rw [hi, Nat.mul_zero]; omega
      · have : p ^ μ ≤ p ^ μ * (j - i) := Nat.le_mul_of_pos_right _ hi
        omega
    rw [if_neg fun h => hne h.symm, mul_zero]
  rw [← hL, key, hR]

/-- Hasse derivatives of `X^{qj}` vanish for orders `0 < k < q`, `q = |F|`. -/
theorem hasseDeriv_X_card_mul_eq_zero {F : Type*} [Field F] [Fintype F] (j k : ℕ)
    (hk0 : 0 < k) (hkq : k < Fintype.card F) :
    hasseDeriv k ((X : F[X]) ^ (Fintype.card F * j)) = 0 := by
  obtain ⟨p, hcp, n, hp, hcard⟩ := FiniteField.card' F
  haveI := hcp
  rw [X_pow_eq_monomial, hasseDeriv_monomial]
  have hz : ((Fintype.card F * j).choose k : F) = 0 := by
    rw [hcard]
    exact cast_choose_prime_pow_mul_eq_zero hp (n : ℕ) j k hk0 (hcard ▸ hkq)
  rw [hz, zero_mul, monomial_zero_right]

/-- Below order `q`, multiplication by `X^{qj}` commutes with Hasse differentiation. -/
theorem hasseDeriv_mul_X_card_pow {F : Type*} [Field F] [Fintype F] (u : F[X]) (j k : ℕ)
    (hkq : k < Fintype.card F) :
    hasseDeriv k (u * X ^ (Fintype.card F * j))
      = hasseDeriv k u * X ^ (Fintype.card F * j) := by
  rw [hasseDeriv_mul]
  rw [Finset.sum_eq_single (k, 0)]
  · rw [hasseDeriv_zero']
  · rintro ⟨i, l⟩ hmem hne
    rw [Finset.mem_antidiagonal] at hmem
    have hl0 : 0 < l := by
      rcases Nat.eq_zero_or_pos l with h | h
      · exact absurd (by simp [h, ← hmem]) hne
      · exact h
    rw [hasseDeriv_X_card_mul_eq_zero j l hl0 (by omega), mul_zero]
  · intro h
    exact absurd (Finset.mem_antidiagonal.mpr (by omega)) h

/-! ## 2. Divisibility: `f^{N−k} ∣ D^{(k)}(f^N·a)` (the Leibniz induction) -/

/-- Core divisibility: `f^{N−k} ∣ D^{(k)}(f^N)` for `k ≤ N`. -/
theorem pow_sub_dvd_hasseDeriv_pow {F : Type*} [Field F] (f : F[X]) :
    ∀ N k : ℕ, k ≤ N → f ^ (N - k) ∣ hasseDeriv k (f ^ N) := by
  intro N
  induction N with
  | zero =>
    intro k hk
    interval_cases k
    simp
  | succ N ih =>
    intro k hk
    rw [pow_succ, mul_comm (f ^ N) f, hasseDeriv_mul]
    refine Finset.dvd_sum ?_
    rintro ⟨i, l⟩ hmem
    rw [Finset.mem_antidiagonal] at hmem
    rcases Nat.eq_zero_or_pos i with hi | hi
    · -- term `f · D^{(k)}(f^N)`
      have hl : l = k := by omega
      subst hi
      rw [hasseDeriv_zero', hl]
      rcases Nat.lt_or_ge k (N + 1) with hkN | hkN
      · have hdvd := ih k (by omega)
        have : N + 1 - k = (N - k) + 1 := by omega
        rw [this, pow_succ, mul_comm (f ^ (N - k)) f]
        exact mul_dvd_mul_left f hdvd
      · have : N + 1 - k = 0 := by omega
        rw [this, pow_zero]
        exact one_dvd _
    · -- term `D^{(i)}f · D^{(l)}(f^N)`, `i ≥ 1` so `l ≤ N`
      have hlN : l ≤ N := by omega
      have hdvd := ih l hlN
      refine dvd_trans (pow_dvd_pow f (show N + 1 - k ≤ N - l by omega)) ?_
      exact Dvd.dvd.mul_left hdvd _

/-- Product form: `f^{N−k} ∣ D^{(k)}(f^N·a)`. -/
theorem pow_sub_dvd_hasseDeriv_pow_mul {F : Type*} [Field F] (f a : F[X]) (N k : ℕ)
    (hk : k ≤ N) : f ^ (N - k) ∣ hasseDeriv k (f ^ N * a) := by
  rw [hasseDeriv_mul]
  refine Finset.dvd_sum ?_
  rintro ⟨i, l⟩ hmem
  rw [Finset.mem_antidiagonal] at hmem
  have hiN : i ≤ N := by omega
  refine dvd_trans (pow_dvd_pow f (show N - k ≤ N - i by omega)) ?_
  exact Dvd.dvd.mul_right (pow_sub_dvd_hasseDeriv_pow f N i hiN) _

/-! ## 3. Monic-quotient toolkit: exactness and linearity of `/ₘ` -/

theorem divByMonic_exact {F : Type*} [Field F] {g p : F[X]} (hg : g.Monic) (hdvd : g ∣ p) :
    g * (p /ₘ g) = p := by
  obtain ⟨c, rfl⟩ := hdvd
  rw [mul_divByMonic_cancel_left c hg]

/-- Additivity of `/ₘ`.  Now a thin wrapper over the ToMathlib PR-1 lemma
`Polynomial.add_divByMonic` (`ArkLib/ToMathlib/Polynomial/DivByMonicLinear.lean`), which holds
over any `CommRing` with no `Monic` hypothesis; the hypothesis is kept for call-site
compatibility. -/
theorem add_divByMonic {F : Type*} [Field F] {g : F[X]} (_hg : g.Monic) (p q : F[X]) :
    (p + q) /ₘ g = p /ₘ g + q /ₘ g :=
  _root_.Polynomial.add_divByMonic p q

/-- Scalar-linearity of `/ₘ`.  Now a thin wrapper over the ToMathlib PR-1 lemma
`Polynomial.smul_divByMonic`. -/
theorem smul_divByMonic {F : Type*} [Field F] {g : F[X]} (_hg : g.Monic) (c : F) (p : F[X]) :
    (c • p) /ₘ g = c • (p /ₘ g) :=
  _root_.Polynomial.smul_divByMonic c p

/-! ## 4. The coefficient blocks, the reduced witnesses `W_k`, and the auxiliary `P` -/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `polyOf D c = ∑ c_i X^i`: the degree-`≤ D` polynomial with coefficient vector `c`. -/
noncomputable def polyOf (D : ℕ) (c : Fin (D + 1) → F) : F[X] :=
  ∑ i : Fin (D + 1), C (c i) * X ^ (i : ℕ)

omit [Fintype F] [DecidableEq F] in
theorem polyOf_natDegree_le (D : ℕ) (c : Fin (D + 1) → F) : (polyOf D c).natDegree ≤ D := by
  refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  refine natDegree_mul_le.trans ?_
  rw [natDegree_C, natDegree_X_pow]
  omega

omit [Fintype F] [DecidableEq F] in
theorem polyOf_coeff (D : ℕ) (c : Fin (D + 1) → F) (i : Fin (D + 1)) :
    (polyOf D c).coeff (i : ℕ) = c i := by
  rw [polyOf, finset_sum_coeff]
  rw [Finset.sum_eq_single i]
  · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
  · intro b _ hb
    rw [coeff_C_mul, coeff_X_pow, if_neg (fun h => hb (Fin.ext h.symm)), mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

omit [Fintype F] [DecidableEq F] in
theorem polyOf_add (D : ℕ) (c d : Fin (D + 1) → F) :
    polyOf D (c + d) = polyOf D c + polyOf D d := by
  rw [polyOf, polyOf, polyOf, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.add_apply, C_add, add_mul]

omit [Fintype F] [DecidableEq F] in
theorem polyOf_smul (D : ℕ) (r : F) (c : Fin (D + 1) → F) :
    polyOf D (r • c) = r • polyOf D c := by
  rw [polyOf, polyOf, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, C_mul, smul_eq_C_mul, mul_assoc]

/-- The unknown vector: two `J × (D+1)` blocks of field elements. -/
@[reducible] def Unknowns (F : Type*) (J D : ℕ) : Type _ :=
  ((Fin J × Fin (D + 1)) → F) × ((Fin J × Fin (D + 1)) → F)

/-- The `k`-th reduced witness
`W_k = ∑_j (D^{(k)}(f^m a_j)/f^{m−k} + D^{(k)}(f^{m+e} b_j)/f^{m+e−k})·X^j`.
Its identical vanishing for `k < m` is the linear condition system. -/
noncomputable def redWitness (u v : F) (m e J D k : ℕ) (x : Unknowns F J D) : F[X] :=
  ∑ j : Fin J,
    (hasseDeriv k ((cubic u v) ^ m * polyOf D (fun i => x.1 (j, i)))
        /ₘ (cubic u v) ^ (m - k)
      + hasseDeriv k ((cubic u v) ^ (m + e) * polyOf D (fun i => x.2 (j, i)))
        /ₘ (cubic u v) ^ (m + e - k)) * X ^ (j : ℕ)

/-- The auxiliary polynomial `P = ∑_j (f^m a_j + f^{m+e} b_j)·X^{qj}`. -/
noncomputable def auxP (u v : F) (q m e J D : ℕ) (x : Unknowns F J D) : F[X] :=
  ∑ j : Fin J,
    ((cubic u v) ^ m * polyOf D (fun i => x.1 (j, i))
      + (cubic u v) ^ (m + e) * polyOf D (fun i => x.2 (j, i))) * X ^ (q * (j : ℕ))

theorem cubic_monic (u v : F) : (cubic u v).Monic := by
  rw [cubic_def]
  exact monic_X.mul ((monic_X_sub_C u).mul (monic_X_sub_C v))

theorem redWitness_add (u v : F) (m e J D k : ℕ) (x y : Unknowns F J D) :
    redWitness u v m e J D k (x + y)
      = redWitness u v m e J D k x + redWitness u v m e J D k y := by
  rw [redWitness, redWitness, redWitness, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hP1 : polyOf D (fun i => (x + y).1 (j, i))
      = polyOf D (fun i => x.1 (j, i)) + polyOf D (fun i => y.1 (j, i)) := by
    rw [← polyOf_add]; rfl
  have hP2 : polyOf D (fun i => (x + y).2 (j, i))
      = polyOf D (fun i => x.2 (j, i)) + polyOf D (fun i => y.2 (j, i)) := by
    rw [← polyOf_add]; rfl
  rw [hP1, hP2, mul_add, mul_add, map_add, map_add,
    add_divByMonic ((cubic_monic u v).pow _), add_divByMonic ((cubic_monic u v).pow _)]
  ring

theorem redWitness_smul (u v : F) (m e J D k : ℕ) (r : F) (x : Unknowns F J D) :
    redWitness u v m e J D k (r • x) = r • redWitness u v m e J D k x := by
  rw [redWitness, redWitness, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hP1 : polyOf D (fun i => (r • x).1 (j, i)) = r • polyOf D (fun i => x.1 (j, i)) := by
    rw [← polyOf_smul]; rfl
  have hP2 : polyOf D (fun i => (r • x).2 (j, i)) = r • polyOf D (fun i => x.2 (j, i)) := by
    rw [← polyOf_smul]; rfl
  rw [hP1, hP2, mul_smul_comm, mul_smul_comm, map_smul, map_smul,
    smul_divByMonic ((cubic_monic u v).pow _), smul_divByMonic ((cubic_monic u v).pow _),
    ← smul_add, smul_mul_assoc]

/-- The condition system as a LINEAR map: unknowns ↦ the first `D+2m+J` coefficients of
each `W_k`, `k < m`. -/
noncomputable def condMap (u v : F) (m e J D : ℕ) :
    Unknowns F J D →ₗ[F] ((Fin m × Fin (D + 2 * m + J)) → F) where
  toFun x := fun ki => (redWitness u v m e J D (ki.1 : ℕ) x).coeff (ki.2 : ℕ)
  map_add' x y := by
    funext ki
    rw [redWitness_add]
    simp [coeff_add]
  map_smul' r x := by
    funext ki
    rw [redWitness_smul]
    simp

/-! ## 5. Rank–nullity: a nonzero kernel vector exists under the classical count -/

theorem exists_kernel_vector (u v : F) (m e J D : ℕ)
    (hcount : m * (D + 2 * m + J) < 2 * (J * (D + 1))) :
    ∃ x : Unknowns F J D, x ≠ 0 ∧ condMap u v m e J D x = 0 := by
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective (condMap u v m e J D) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hne
    exact hcon x hne hx
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  simp only [Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
    Fintype.card_prod, Fintype.card_fin] at hle
  omega

/-! ## 6. Degree control and identical vanishing of the witnesses on the kernel -/

theorem natDegree_cubic_pow (u v : F) (n : ℕ) : ((cubic u v) ^ n).natDegree = 3 * n := by
  rw [(cubic_monic u v).natDegree_pow, cubic_natDegree, Nat.mul_comm]

theorem quotient_natDegree_le (u v : F) (a : F[X]) {Da : ℕ} (ha : a.natDegree ≤ Da)
    (N k : ℕ) (hk : k ≤ N) :
    (hasseDeriv k ((cubic u v) ^ N * a) /ₘ (cubic u v) ^ (N - k)).natDegree ≤ Da + 2 * k := by
  rw [natDegree_divByMonic _ ((cubic_monic u v).pow _)]
  have h1 : (hasseDeriv k ((cubic u v) ^ N * a)).natDegree
      ≤ ((cubic u v) ^ N * a).natDegree - k := natDegree_hasseDeriv_le _ _
  have h2 : ((cubic u v) ^ N * a).natDegree ≤ 3 * N + Da := by
    refine natDegree_mul_le.trans ?_
    rw [natDegree_cubic_pow]
    omega
  have h3 : ((cubic u v) ^ (N - k)).natDegree = 3 * (N - k) := natDegree_cubic_pow u v _
  omega

theorem redWitness_natDegree_le (u v : F) (m e J D k : ℕ) (x : Unknowns F J D)
    (hk : k ≤ m) (hJ : 0 < J) :
    (redWitness u v m e J D k x).natDegree ≤ D + 2 * k + (J - 1) := by
  refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  refine natDegree_mul_le.trans ?_
  rw [natDegree_X_pow]
  have hq1 := quotient_natDegree_le u v (polyOf D (fun i => x.1 (j, i)))
    (polyOf_natDegree_le _ _) m k hk
  have hq2 := quotient_natDegree_le u v (polyOf D (fun i => x.2 (j, i)))
    (polyOf_natDegree_le _ _) (m + e) k (by omega)
  have hadd := natDegree_add_le
    (hasseDeriv k ((cubic u v) ^ m * polyOf D (fun i => x.1 (j, i)))
      /ₘ (cubic u v) ^ (m - k))
    (hasseDeriv k ((cubic u v) ^ (m + e) * polyOf D (fun i => x.2 (j, i)))
      /ₘ (cubic u v) ^ (m + e - k))
  have hjlt : (j : ℕ) ≤ J - 1 := by omega
  omega

theorem redWitness_eq_zero_of_kernel (u v : F) (m e J D k : ℕ) (x : Unknowns F J D)
    (hk : k < m) (hJ : 0 < J) (hx : condMap u v m e J D x = 0) :
    redWitness u v m e J D k x = 0 := by
  ext n
  rw [coeff_zero]
  rcases Nat.lt_or_ge n (D + 2 * m + J) with hn | hn
  · exact congrFun hx (⟨k, hk⟩, ⟨n, hn⟩)
  · refine coeff_eq_zero_of_natDegree_lt ?_
    have := redWitness_natDegree_le u v m e J D k x (by omega) hJ
    omega

/-! ## 7. The pointwise Hasse-derivative factorization on the positive fibers -/

/-- **The S2 vanishing identity.** For `k ≤ m`, `k < q = |F|`, at any `s` with
`f(s) ≠ 0` and `f(s)^e = 1`: `(D^{(k)}P)(s) = f(s)^{m−k}·W_k(s)`. -/
theorem eval_hasseDeriv_auxP {F : Type*} [Field F] [Fintype F] [DecidableEq F] (u v : F)
    (m e J D k : ℕ) (x : Unknowns F J D) (hkm : k ≤ m) (hkq : k < Fintype.card F)
    (s : F) (hse : ((cubic u v).eval s) ^ e = 1) :
    (hasseDeriv k (auxP u v (Fintype.card F) m e J D x)).eval s
      = ((cubic u v).eval s) ^ (m - k) * (redWitness u v m e J D k x).eval s := by
  rw [auxP, map_sum, eval_finset_sum, redWitness, eval_finset_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  set f := cubic u v with hf
  set Pa := polyOf D (fun i => x.1 (j, i)) with hPa
  set Pb := polyOf D (fun i => x.2 (j, i)) with hPb
  -- exact-division identities
  have hd1 : f ^ (m - k) * (hasseDeriv k (f ^ m * Pa) /ₘ f ^ (m - k))
      = hasseDeriv k (f ^ m * Pa) :=
    divByMonic_exact ((cubic_monic u v).pow _)
      (pow_sub_dvd_hasseDeriv_pow_mul f Pa m k hkm)
  have hd2 : f ^ (m + e - k) * (hasseDeriv k (f ^ (m + e) * Pb) /ₘ f ^ (m + e - k))
      = hasseDeriv k (f ^ (m + e) * Pb) :=
    divByMonic_exact ((cubic_monic u v).pow _)
      (pow_sub_dvd_hasseDeriv_pow_mul f Pb (m + e) k (by omega))
  -- push the Hasse derivative through `· X^{qj}` and the sum
  rw [hasseDeriv_mul_X_card_pow _ (j : ℕ) k hkq, map_add]
  conv_lhs => rw [← hd1, ← hd2]
  -- evaluate
  have hsq : s ^ (Fintype.card F * (j : ℕ)) = s ^ (j : ℕ) := by
    rw [mul_comm, pow_mul, FiniteField.pow_card]
  have hpow : (f.eval s) ^ (m + e - k) = (f.eval s) ^ (m - k) * (f.eval s) ^ e := by
    rw [← pow_add]
    congr 1
    omega
  simp only [eval_mul, eval_add, eval_pow, eval_X]
  rw [hsq, hpow, hse, mul_one]
  ring

/-! ## 8. Nonzeroness (via S1) and the degree budget of the auxiliary -/

/-- Lift the coefficient blocks to `F[X][Y]` (outer `X` is the `Y` of `subq`). -/
noncomputable def liftY {J : ℕ} (g : Fin J → F[X]) : Polynomial (Polynomial F) :=
  ∑ j : Fin J, Polynomial.C (g j) * Polynomial.X ^ (j : ℕ)

omit [Fintype F] [DecidableEq F] in
theorem liftY_coeff {J : ℕ} (g : Fin J → F[X]) (n : ℕ) :
    (liftY g).coeff n = if h : n < J then g ⟨n, h⟩ else 0 := by
  rw [liftY, finset_sum_coeff]
  by_cases h : n < J
  · rw [dif_pos h, Finset.sum_eq_single (⟨n, h⟩ : Fin J)]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    · intro b _ hb
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        if_neg (fun hh => hb (Fin.ext hh.symm)), mul_zero]
    · intro hh; exact absurd (Finset.mem_univ _) hh
  · rw [dif_neg h]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_neg (fun hh => h (by rw [hh]; exact b.isLt)), mul_zero]

omit [Fintype F] [DecidableEq F] in
theorem subq_liftY {J : ℕ} (q : ℕ) (g : Fin J → F[X]) :
    ArkLib.ProximityGap.StepanovNonVanishing.subq q (liftY g)
      = ∑ j : Fin J, g j * X ^ (q * (j : ℕ)) := by
  rw [ArkLib.ProximityGap.StepanovNonVanishing.subq, liftY, Polynomial.eval₂_finset_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, RingHom.id_apply,
    ← pow_mul]

/-- `P = f^m·(A₀(X,X^q) + f^e·A₁(X,X^q))` — the bridge to the S1 non-vanishing. -/
theorem auxP_eq_mul (u v : F) (q m e J D : ℕ) (x : Unknowns F J D) :
    auxP u v q m e J D x
      = (cubic u v) ^ m
        * (ArkLib.ProximityGap.StepanovNonVanishing.subq q
            (liftY (fun j => polyOf D (fun i => x.1 (j, i))))
          + (cubic u v) ^ e
            * ArkLib.ProximityGap.StepanovNonVanishing.subq q
                (liftY (fun j => polyOf D (fun i => x.2 (j, i))))) := by
  rw [subq_liftY, subq_liftY, auxP, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_add]
  ring

theorem auxP_ne_zero {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hq_odd : Odd (Fintype.card F))
    {u v : F} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    {m e J D : ℕ} (hD : 2 * D + 3 < Fintype.card F)
    (he : e = (Fintype.card F - 1) / 2)
    (x : Unknowns F J D) (hx : x ≠ 0) :
    auxP u v (Fintype.card F) m e J D x ≠ 0 := by
  set A0 := liftY (fun j => polyOf D (fun i => x.1 (j, i))) with hA0
  set A1 := liftY (fun j => polyOf D (fun i => x.2 (j, i))) with hA1
  have hblk0 : ∀ jn, (A0.coeff jn).natDegree ≤ D := by
    intro jn
    rw [hA0, liftY_coeff]
    split_ifs
    · exact polyOf_natDegree_le _ _
    · simp
  have hblk1 : ∀ jn, (A1.coeff jn).natDegree ≤ D := by
    intro jn
    rw [hA1, liftY_coeff]
    split_ifs
    · exact polyOf_natDegree_le _ _
    · simp
  have hne : ¬(A0 = 0 ∧ A1 = 0) := by
    rintro ⟨h0, h1⟩
    apply hx
    have hz : ∀ (w : (Fin J × Fin (D + 1)) → F),
        liftY (fun j => polyOf D (fun i => w (j, i))) = 0 → w = 0 := by
      intro w hw
      funext ji
      obtain ⟨j, i⟩ := ji
      have hc := congrArg (fun p => (p.coeff (j : ℕ)).coeff (i : ℕ)) hw
      simp only [liftY_coeff, Polynomial.coeff_zero] at hc
      rw [dif_pos j.isLt] at hc
      rw [Fin.eta] at hc
      rw [polyOf_coeff] at hc
      exact hc
    exact Prod.ext (hz x.1 h0) (hz x.2 h1)
  have hinner := cubic_aux_ne_zero hq_odd hu hv huv hD A0 A1 hblk0 hblk1 hne
  rw [auxP_eq_mul, ← hA0, ← hA1, he]
  exact mul_ne_zero (pow_ne_zero _ (cubic_ne_zero u v)) hinner

theorem auxP_natDegree_le (u v : F) (q m e J D : ℕ) (x : Unknowns F J D) (hJ : 0 < J) :
    (auxP u v q m e J D x).natDegree ≤ 3 * (m + e) + D + q * (J - 1) := by
  refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
  refine natDegree_mul_le.trans ?_
  rw [natDegree_X_pow]
  have h1 : ((cubic u v) ^ m * polyOf D (fun i => x.1 (j, i))).natDegree ≤ 3 * m + D := by
    refine natDegree_mul_le.trans ?_
    have := polyOf_natDegree_le D (fun i => x.1 (j, i))
    rw [natDegree_cubic_pow]
    omega
  have h2 : ((cubic u v) ^ (m + e) * polyOf D (fun i => x.2 (j, i))).natDegree
      ≤ 3 * (m + e) + D := by
    refine natDegree_mul_le.trans ?_
    have := polyOf_natDegree_le D (fun i => x.2 (j, i))
    rw [natDegree_cubic_pow]
    omega
  have hadd := natDegree_add_le ((cubic u v) ^ m * polyOf D (fun i => x.1 (j, i)))
    ((cubic u v) ^ (m + e) * polyOf D (fun i => x.2 (j, i)))
  have hjq : q * (j : ℕ) ≤ q * (J - 1) := Nat.mul_le_mul_left q (by omega)
  omega

/-! ## 9. THE S2 THEOREM and the capstone fiber-count bound -/

/-- **S2 (auxiliary-polynomial existence).** Under the classical parameter budget
(`m(D+2m+J) < 2J(D+1)` unknowns-beat-conditions, `2D+3 < q` for S1, `m ≤ e`), there is a
NONZERO `P` of degree `≤ 3(m+e) + D + q(J−1)` all of whose Hasse derivatives of order `< m`
vanish at every point of `N⁺ = {s : f(s)^e = 1}`. -/
theorem cubic_stepanov_S2 {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hq_odd : Odd (Fintype.card F))
    {u v : F} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    {m J D : ℕ} (hJ : 0 < J)
    (hme : m ≤ (Fintype.card F - 1) / 2)
    (hD : 2 * D + 3 < Fintype.card F)
    (hcount : m * (D + 2 * m + J) < 2 * (J * (D + 1))) :
    ∃ P : F[X], P ≠ 0 ∧
      P.natDegree ≤ 3 * (m + (Fintype.card F - 1) / 2) + D + Fintype.card F * (J - 1) ∧
      ∀ s : F, ((cubic u v).eval s) ^ ((Fintype.card F - 1) / 2) = 1 →
        ∀ k < m, (hasseDeriv k P).eval s = 0 := by
  set e := (Fintype.card F - 1) / 2 with he
  obtain ⟨x, hx0, hxker⟩ := exists_kernel_vector u v m e J D hcount
  refine ⟨auxP u v (Fintype.card F) m e J D x,
    auxP_ne_zero hq_odd hu hv huv hD he x hx0,
    auxP_natDegree_le u v (Fintype.card F) m e J D x hJ, ?_⟩
  intro s hs k hk
  have hcard3 : 3 ≤ Fintype.card F := by
    have h2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
    rcases hq_odd with ⟨t, ht⟩
    omega
  have hkq : k < Fintype.card F := by omega
  rw [eval_hasseDeriv_auxP u v m e J D k x (le_of_lt hk) hkq s hs,
    redWitness_eq_zero_of_kernel u v m e J D k x hk hJ hxker, eval_zero, mul_zero]

/-- **The S2 capstone**: the Stepanov fiber-count bound
`m·#N⁺ ≤ 3(m+e) + D + q(J−1)` for EVERY admissible parameter triple, assembled with the
round-20 engine.  (The S3 lane instantiates `(m,J,D)` and converts `#N⁺` to the char sum.) -/
theorem cubic_stepanov_positive_fiber_bound {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hq_odd : Odd (Fintype.card F))
    {u v : F} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v)
    {m J D : ℕ} (hJ : 0 < J)
    (hme : m ≤ (Fintype.card F - 1) / 2)
    (hD : 2 * D + 3 < Fintype.card F)
    (hcount : m * (D + 2 * m + J) < 2 * (J * (D + 1))) :
    m * (Finset.univ.filter fun s : F =>
        ((cubic u v).eval s) ^ ((Fintype.card F - 1) / 2) = 1).card
      ≤ 3 * (m + (Fintype.card F - 1) / 2) + D + Fintype.card F * (J - 1) := by
  obtain ⟨P, hP0, hPdeg, hPvan⟩ := cubic_stepanov_S2 hq_odd hu hv huv hJ hme hD hcount
  refine le_trans ?_ hPdeg
  refine hasseDeriv_stepanov_degree_count hP0 ?_
  intro s hs
  rw [Finset.mem_filter] at hs
  exact hPvan s hs.2
end ArkLib.ProximityGap.Frontier.R22StepanovS2

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R22StepanovS2.cast_choose_prime_pow_mul_eq_zero
#print axioms ArkLib.ProximityGap.Frontier.R22StepanovS2.hasseDeriv_mul_X_card_pow
#print axioms ArkLib.ProximityGap.Frontier.R22StepanovS2.pow_sub_dvd_hasseDeriv_pow
#print axioms ArkLib.ProximityGap.Frontier.R22StepanovS2.pow_sub_dvd_hasseDeriv_pow_mul
#print axioms ArkLib.ProximityGap.Frontier.R22StepanovS2.add_divByMonic
#print axioms ArkLib.ProximityGap.Frontier.R22StepanovS2.smul_divByMonic
#print axioms ArkLib.ProximityGap.Frontier.R22StepanovS2.exists_kernel_vector
#print axioms ArkLib.ProximityGap.Frontier.R22StepanovS2.redWitness_eq_zero_of_kernel
#print axioms ArkLib.ProximityGap.Frontier.R22StepanovS2.eval_hasseDeriv_auxP
#print axioms ArkLib.ProximityGap.Frontier.R22StepanovS2.auxP_ne_zero
#print axioms ArkLib.ProximityGap.Frontier.R22StepanovS2.auxP_natDegree_le
#print axioms ArkLib.ProximityGap.Frontier.R22StepanovS2.cubic_stepanov_S2
#print axioms ArkLib.ProximityGap.Frontier.R22StepanovS2.cubic_stepanov_positive_fiber_bound
