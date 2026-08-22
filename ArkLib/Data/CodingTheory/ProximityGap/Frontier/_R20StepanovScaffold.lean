/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Taylor
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R19HasseAudit

/-!
# LANE STEPANOV (#466 round 20): scaffold for `hasse_cubic` (the round-19 pinned Mathlib gap)

Target (round-19 `_R19HasseAudit.lean`, `LegendreCubicHasse`):
`(∑_s χ(s(s−u)(s−v)))² ≤ 4·card F` for `χ = quadraticChar F`, `0 ≠ u ≠ v ≠ 0`,
`ringChar F ≠ 2` — Hasse for the full-2-torsion genus-1 curve `y² = s(s−u)(s−v)`.

## Route chosen: Stepanov/Bombieri elementary auxiliary-polynomial method

Audit of alternatives (see `_R19HasseAudit.lean` §(a)): Jacobi-sum evaluations are CM-only;
Schoof is out of scope; Manin's derivation proof needs derivation/formal-group calculus for
point counts that Mathlib lacks.  Stepanov needs only: polynomial degree/multiplicity
counting (Mathlib HAS: `Polynomial.card_roots'`, `Polynomial.count_roots`,
`rootMultiplicity`, `hasseDeriv`) + finite-field power identities (`x^q = x`).  It is the
only route whose entire toolbox already exists in Mathlib.

## What THIS file proves (axiom-clean; nothing assumed)

1. `affine_point_count` — the counting bridge, EXACT: for any `f : F → F`,
   `#{(s,y) : y² = f s} = card F + ∑_s χ(f s)` (double counting, fiber size `1 + χ`).
   Converts `hasse_cubic` verbatim into the point-count form (`N = q + S`) that the
   Stepanov method bounds.
2. `stepanov_degree_count` — the Stepanov ENGINE in general form: a nonzero polynomial
   vanishing to order `≥ m` at every point of a finset `S` has `m·|S| ≤ deg P`.
   (The final contradiction step of every Stepanov-style proof.)
3. `pow_dvd_stepanov_degree_count` — same engine with the hypothesis in the
   `(X − a)^m ∣ P` form the auxiliary-polynomial construction actually produces.
3'. `le_rootMultiplicity_of_hasseDeriv_eq_zero` + `hasseDeriv_stepanov_degree_count` —
   the CHAR-`p` vanishing workhorse: `(D^{(k)}P)(a) = 0` for all `k < m` forces
   `ord_a(P) ≥ m` (via `taylor_coeff` + `X_sub_C_pow_dvd_iff`; this is WHY Stepanov
   uses Hasse derivatives and not `derivative^[k]`, which dies at order `≥ p`), and
   the engine assembled directly on Hasse-derivative hypotheses — the exact interface
   the Leibniz bookkeeping of step S2 (below) will produce.
4. `twist_negation` — the full-2-torsion family is CLOSED under quadratic twist, EXACTLY:
   `∑_s χ(s(s−gu)(s−gv)) = χ(g)·∑_s χ(s(s−u)(s−v))` for `g ≠ 0`.
5. `legendreCubicHasse_of_stepanovUpper` — consequence of (4): a ONE-SIDED upper bound
   `S ≤ B` uniform over the family already gives the two-sided `LegendreCubicHasse`
   (twist by a nonsquare `g` negates `S` while staying inside the family).  This HALVES
   the remaining problem: only the one-sided bound — the natural output of the Stepanov
   auxiliary polynomial — is needed.  No lower-bound construction required.
6. `cubic_zero_count` — `#{s : s(s−u)(s−v) = 0} = 3` exactly (the 2-torsion fibers),
   pinning the `N = 2N⁺ + 3` bookkeeping for the Stepanov set.

## The remaining core, honestly scoped

`CubicStepanovUpper F B` (named Prop, exact statement below): the one-sided bound
`∑_s χ(s(s−u)(s−v)) ≤ B` uniform over the family.  Proven here:
`B ≥ 0, B² ≤ 4q, CubicStepanovUpper F B → LegendreCubicHasse F`.

Remaining work to discharge `CubicStepanovUpper` (measured against the classical proof,
e.g. Tao's exposition of Stepanov's method): assuming `N⁺ > q/2 + C√q`, construct an
auxiliary polynomial `P = ∑_i f_i(x)·(x^{(q−1)/2})^i` with low-degree coefficients `f_i`
chosen by linear algebra (more unknowns than vanishing constraints) such that (a) `P ≠ 0`
— an independence argument for `1, f(x)^{(q−1)/2}` over low-degree polynomials, valid
because `f = x(x−u)(x−v)` is SQUAREFREE (guaranteed by `0,u,v` distinct — exactly our
hypothesis); (b) `P` vanishes to order `m` at every point of the `N⁺`-set (Hasse-derivative
Leibniz bookkeeping using `y² = f`, `y^{q−1} = 1` on the set); then engine (2)/(3) gives
`m·N⁺ ≤ deg P`, contradiction.  Estimated Lean effort: dimension-count existence
~300-500 lines, nonvanishing ~300 lines (the delicate step), multiplicity bookkeeping via
`hasseDeriv` ~400-700 lines, plus small-`q` cases — realistic total 1500-2500 lines, a
dedicated multi-session lane.  NOT faked here: `CubicStepanovUpper` stays a named Prop.

No closure claimed.
-/

namespace ArkLib.ProximityGap.Frontier.R20StepanovScaffold

open Finset Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## 1. The counting bridge: char sum ↔ affine point count -/

/-- **Counting bridge** (exact, any `f`): the number of affine points of `y² = f(s)`
is `card F + ∑_s χ(f s)`.  Double counting: the fiber over `s` has `1 + χ(f s)` points. -/
theorem affine_point_count (hF : ringChar F ≠ 2) (f : F → F) :
    ((univ.filter fun p : F × F => p.2 ^ 2 = f p.1).card : ℤ)
      = Fintype.card F + ∑ s : F, quadraticChar F (f s) := by
  classical
  have hfib : (univ.filter fun p : F × F => p.2 ^ 2 = f p.1).card
      = ∑ s : F, (univ.filter fun y : F => y ^ 2 = f s).card := by
    rw [card_eq_sum_card_fiberwise
      (f := fun p : F × F => p.1) (t := univ) (fun p _ => mem_univ _)]
    refine sum_congr rfl fun s _ => ?_
    refine card_nbij (fun p => p.2) ?_ ?_ ?_
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_filter, mem_univ, true_and] at hp ⊢
      obtain ⟨h1, h2⟩ := hp
      simpa [h2] using h1
    · intro p hp p' hp' h
      simp only [Set.mem_setOf_eq, mem_coe, mem_filter, mem_univ, true_and] at hp hp'
      exact Prod.ext (hp.2.trans hp'.2.symm) h
    · intro y hy
      simp only [Set.mem_setOf_eq, mem_coe, mem_filter, mem_univ, true_and] at hy
      exact ⟨(s, y), by simp [hy], rfl⟩
  have hcount : ∀ s : F,
      ((univ.filter fun y : F => y ^ 2 = f s).card : ℤ) = quadraticChar F (f s) + 1 := by
    intro s
    have h := quadraticChar_card_sqrts hF (f s)
    have hset : {y : F | y ^ 2 = f s}.toFinset = univ.filter fun y : F => y ^ 2 = f s := by
      ext y; simp
    rw [hset] at h
    exact h
  rw [hfib]
  push_cast
  rw [sum_congr rfl fun s _ => hcount s, sum_add_distrib]
  simp [add_comm, card_univ]

/-! ## 2. The Stepanov degree-counting engine -/

/-- **Stepanov engine** (general form): a nonzero polynomial vanishing to order `≥ m`
at every point of `S` has degree `≥ m·|S|`.  This is the final contradiction step of
every Stepanov-style proof: an auxiliary polynomial of controlled degree cannot vanish
to high order on a large set. -/
theorem stepanov_degree_count {K : Type*} [CommRing K] [IsDomain K] [DecidableEq K]
    {P : K[X]} (hP : P ≠ 0) {S : Finset K} {m : ℕ}
    (h : ∀ a ∈ S, m ≤ P.rootMultiplicity a) :
    m * S.card ≤ P.natDegree := by
  classical
  calc m * S.card = ∑ _a ∈ S, m := by rw [sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ a ∈ S, P.roots.count a := by
        refine sum_le_sum fun a ha => ?_
        rw [count_roots]; exact h a ha
    _ = ∑ a ∈ S ∩ P.roots.toFinset, P.roots.count a := by
        refine (sum_subset inter_subset_left fun a haS hna => ?_).symm
        exact Multiset.count_eq_zero.mpr fun hmem =>
          hna (mem_inter.mpr ⟨haS, Multiset.mem_toFinset.mpr hmem⟩)
    _ ≤ ∑ a ∈ P.roots.toFinset, P.roots.count a :=
        sum_le_sum_of_subset_of_nonneg inter_subset_right fun _ _ _ => Nat.zero_le _
    _ = Multiset.card P.roots := P.roots.toFinset_sum_count_eq
    _ ≤ P.natDegree := P.card_roots'

/-- The engine with the vanishing hypothesis in the divisibility form
`(X − a)^m ∣ P` produced by the auxiliary-polynomial construction. -/
theorem pow_dvd_stepanov_degree_count {K : Type*} [CommRing K] [IsDomain K] [DecidableEq K]
    {P : K[X]} (hP : P ≠ 0) {S : Finset K} {m : ℕ}
    (h : ∀ a ∈ S, (X - C a) ^ m ∣ P) :
    m * S.card ≤ P.natDegree :=
  stepanov_degree_count hP fun a ha => (le_rootMultiplicity_iff hP).mpr (h a ha)

/-- **Hasse-derivative criterion for high-order vanishing** (char-`p` safe):
`(D^{(k)}P)(a) = 0` for all `k < m` forces `ord_a(P) ≥ m`.  Proof: the `k`-th Taylor
coefficient of `P` at `a` IS `(D^{(k)}P)(a)` (`taylor_coeff`), and `(X−a)^m ∣ P` iff the
first `m` Taylor coefficients vanish. -/
theorem le_rootMultiplicity_of_hasseDeriv_eq_zero {K : Type*} [Field K] [DecidableEq K]
    {P : K[X]} (hP : P ≠ 0) {a : K} {m : ℕ}
    (h : ∀ k < m, (Polynomial.hasseDeriv k P).eval a = 0) :
    m ≤ P.rootMultiplicity a := by
  rw [le_rootMultiplicity_iff hP, X_sub_C_pow_dvd_iff, X_pow_dvd_iff]
  intro d hd
  have hcoeff : (Polynomial.taylor a P).coeff d = 0 := by
    rw [Polynomial.taylor_coeff]; exact h d hd
  rwa [Polynomial.taylor_apply] at hcoeff

/-- The Stepanov engine assembled directly on Hasse-derivative hypotheses — the exact
interface the auxiliary-polynomial Leibniz bookkeeping (step S2 of the remaining core)
produces: a nonzero `P` whose Hasse derivatives of every order `< m` vanish on `S` has
`m·|S| ≤ deg P`. -/
theorem hasseDeriv_stepanov_degree_count {K : Type*} [Field K] [DecidableEq K]
    {P : K[X]} (hP : P ≠ 0) {S : Finset K} {m : ℕ}
    (h : ∀ a ∈ S, ∀ k < m, (Polynomial.hasseDeriv k P).eval a = 0) :
    m * S.card ≤ P.natDegree :=
  stepanov_degree_count hP fun a ha =>
    le_rootMultiplicity_of_hasseDeriv_eq_zero hP (h a ha)

/-- **The contradiction template**: no nonzero polynomial of degree `< m·|S|` has all
Hasse derivatives of order `< m` vanishing on `S`.  The terminal step of the method. -/
theorem stepanov_absurd {K : Type*} [Field K] [DecidableEq K]
    {P : K[X]} (hP : P ≠ 0) {S : Finset K} {m : ℕ}
    (hdeg : P.natDegree < m * S.card)
    (h : ∀ a ∈ S, ∀ k < m, (Polynomial.hasseDeriv k P).eval a = 0) : False :=
  absurd (hasseDeriv_stepanov_degree_count hP h) (not_le.mpr hdeg)

/-! ## 3. Twist closure of the full-2-torsion family: one-sided ⟹ two-sided -/

/-- **Twist negation** (exact): scaling `(u,v) ↦ (gu, gv)` multiplies the Legendre-cubic
char sum by `χ(g)`.  Substituting `s = g·t`: the cubic argument picks up `g³`, and
`χ(g³) = χ(g)` since `χ(g)² = 1` for `g ≠ 0`.  Hence the family is closed under quadratic
twist, and a nonsquare `g` NEGATES the sum. -/
theorem twist_negation {g : F} (hg : g ≠ 0) (u v : F) :
    ∑ s : F, quadraticChar F (s * ((s - g * u) * (s - g * v)))
      = quadraticChar F g * ∑ t : F, quadraticChar F (t * ((t - u) * (t - v))) := by
  classical
  calc ∑ s : F, quadraticChar F (s * ((s - g * u) * (s - g * v)))
      = ∑ t : F, quadraticChar F ((g * t) * (((g * t) - g * u) * ((g * t) - g * v))) :=
          (Fintype.sum_bijective (fun t => g * t) (mulLeft_bijective₀ g hg) _ _
            (fun t => rfl)).symm
    _ = ∑ t : F, quadraticChar F g * quadraticChar F (t * ((t - u) * (t - v))) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        have harg : (g * t) * (((g * t) - g * u) * ((g * t) - g * v))
            = g ^ 2 * (g * (t * ((t - u) * (t - v)))) := by ring
        rw [harg, map_mul, map_mul, quadraticChar_sq_one' hg, one_mul]
    _ = quadraticChar F g * ∑ t : F, quadraticChar F (t * ((t - u) * (t - v))) := by
        rw [Finset.mul_sum]

/-- **The named remaining core** (one-sided Stepanov bound), parametrized by the budget
`B` so the statement stays `Real.sqrt`-free.  The classical Stepanov construction proves
exactly this shape (with `B` of size `2√q + O(1)`; any `B` with `B² ≤ 4q` feeds the
transfer below — a weaker admissible pair like `B² ≤ 9q` would still discharge the
`_R19HasseAudit` budget chain with a larger constant). -/
def CubicStepanovUpper (F : Type*) [Field F] [Fintype F] [DecidableEq F] (B : ℤ) : Prop :=
  ∀ u v : F, u ≠ 0 → v ≠ 0 → u ≠ v →
    (∑ s : F, quadraticChar F (s * ((s - u) * (s - v)))) ≤ B

/-- **One-sided ⟹ two-sided**: an upper bound `B ≥ 0` with `B² ≤ 4q`, uniform over the
family, gives `LegendreCubicHasse` — apply the bound at `(u,v)` for the upper side and at
the nonsquare twist `(gu, gv)` for the lower side (`twist_negation` flips the sign). -/
theorem legendreCubicHasse_of_stepanovUpper (hF : ringChar F ≠ 2) {B : ℤ}
    (hB0 : 0 ≤ B) (hB : B ^ 2 ≤ 4 * Fintype.card F)
    (hU : CubicStepanovUpper F B) :
    ArkLib.ProximityGap.Frontier.R19HasseAudit.LegendreCubicHasse F := by
  intro u v hu hv huv
  obtain ⟨g, hgχ⟩ := quadraticChar_exists_neg_one hF
  have hg : g ≠ 0 := by
    intro h; rw [h] at hgχ; simp at hgχ
  set S : ℤ := ∑ s : F, quadraticChar F (s * ((s - u) * (s - v))) with hS
  have hupper : S ≤ B := hU u v hu hv huv
  have hlower : -B ≤ S := by
    have htw := twist_negation hg u v
    have hU' : ∑ s : F, quadraticChar F (s * ((s - g * u) * (s - g * v))) ≤ B :=
      hU (g * u) (g * v) (mul_ne_zero hg hu) (mul_ne_zero hg hv)
        (fun h => huv (mul_left_cancel₀ hg h))
    rw [htw, hgχ] at hU'
    linarith
  calc S ^ 2 ≤ B ^ 2 := sq_le_sq' hlower hupper
    _ ≤ 4 * Fintype.card F := hB

/-! ## 4. Exact zero count of the cubic (the 2-torsion fibers) -/

/-- The cubic `s(s−u)(s−v)` has EXACTLY 3 roots for `0, u, v` distinct: the 2-torsion
`x`-coordinates.  Pins the Stepanov bookkeeping `q = N⁺ + N⁻ + 3`, `N = 2N⁺ + 3`. -/
theorem cubic_zero_count {u v : F} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    (univ.filter fun s : F => s * ((s - u) * (s - v)) = 0).card = 3 := by
  classical
  have hset : (univ.filter fun s : F => s * ((s - u) * (s - v)) = 0)
      = {0, u, v} := by
    ext s
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, mul_eq_zero,
      sub_eq_zero]
  rw [hset]
  rw [card_insert_of_notMem (by simp [Ne.symm hu, Ne.symm hv]),
    card_insert_of_notMem (by simp [huv]), card_singleton]

/-- Three-valued bookkeeping for quadratic-character sums.  The sum is
`2·#χ=1 + #χ=0 − q`, pointwise from the values `1, 0, -1`. -/
theorem quadraticChar_sum_eq_two_pos_add_zero_sub_card (f : F → F) :
    ∑ s : F, quadraticChar F (f s)
      = 2 * (((univ.filter fun s : F => quadraticChar F (f s) = 1).card : ℕ) : ℤ)
        + (((univ.filter fun s : F => quadraticChar F (f s) = 0).card : ℕ) : ℤ)
        - Fintype.card F := by
  classical
  have hpt : ∀ s : F,
      quadraticChar F (f s)
        = 2 * (if quadraticChar F (f s) = 1 then (1 : ℤ) else 0)
          + (if quadraticChar F (f s) = 0 then (1 : ℤ) else 0) - 1 := by
    intro s
    rcases (quadraticChar_isQuadratic F) (f s) with h | h | h <;> simp [h]
  calc
    ∑ s : F, quadraticChar F (f s)
        = ∑ s : F,
            (2 * (if quadraticChar F (f s) = 1 then (1 : ℤ) else 0)
              + (if quadraticChar F (f s) = 0 then (1 : ℤ) else 0) - 1) := by
          exact Finset.sum_congr rfl fun s _ => hpt s
    _ = 2 * (((univ.filter fun s : F => quadraticChar F (f s) = 1).card : ℕ) : ℤ)
        + (((univ.filter fun s : F => quadraticChar F (f s) = 0).card : ℕ) : ℤ)
        - Fintype.card F := by
          rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const]
          rw [← Finset.mul_sum]
          have hpos :
              (∑ s : F, if quadraticChar F (f s) = 1 then (1 : ℤ) else 0)
                = (((univ.filter fun s : F => quadraticChar F (f s) = 1).card : ℕ) : ℤ) := by
            rw [← Finset.sum_filter]
            simp
          have hzero :
              (∑ s : F, if quadraticChar F (f s) = 0 then (1 : ℤ) else 0)
                = (((univ.filter fun s : F => quadraticChar F (f s) = 0).card : ℕ) : ℤ) := by
            rw [← Finset.sum_filter]
            simp
          rw [hpos, hzero]
          simp

/-- The zero fibers of the Stepanov cubic are exactly the zero values of the quadratic
character. -/
theorem cubic_quadraticChar_zero_count {u v : F} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    (univ.filter fun s : F => quadraticChar F (s * ((s - u) * (s - v))) = 0).card = 3 := by
  convert cubic_zero_count (F := F) hu hv huv using 2
  ext s
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro h
    have harg : s * ((s - u) * (s - v)) = 0 := quadraticChar_eq_zero_iff.mp h
    simpa [mul_eq_zero, sub_eq_zero] using harg
  · intro h
    have harg : s * ((s - u) * (s - v)) = 0 := by
      simpa [mul_eq_zero, sub_eq_zero] using h
    exact quadraticChar_eq_zero_iff.mpr harg

/-- Exact `N⁺` bookkeeping for the Stepanov cubic:
`S = 2·N⁺ + 3 − q`, where `N⁺` is the number of nonzero square fibers
(`χ(s(s-u)(s-v)) = 1`).  This is the arithmetic bridge used before the auxiliary-polynomial
contradiction bounds `N⁺`. -/
theorem cubic_charSum_eq_two_pos_add_three_sub_card {u v : F}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    ∑ s : F, quadraticChar F (s * ((s - u) * (s - v)))
      = 2 * (((univ.filter fun s : F =>
            quadraticChar F (s * ((s - u) * (s - v))) = 1).card : ℕ) : ℤ)
        + 3 - Fintype.card F := by
  rw [quadraticChar_sum_eq_two_pos_add_zero_sub_card
    (F := F) (fun s => s * ((s - u) * (s - v)))]
  rw [cubic_quadraticChar_zero_count hu hv huv]
  norm_num

/-- Positive-fiber formulation of `CubicStepanovUpper`: to prove the one-sided character-sum
bound, it is enough to bound the number of `s` with
`χ(s(s-u)(s-v)) = 1` by the corresponding affine-linear budget. -/
theorem cubicStepanovUpper_of_positiveFiber_bound {B : ℤ}
    (h :
      ∀ u v : F, u ≠ 0 → v ≠ 0 → u ≠ v →
        2 * (((univ.filter fun s : F =>
              quadraticChar F (s * ((s - u) * (s - v))) = 1).card : ℕ) : ℤ)
          + 3 - Fintype.card F ≤ B) :
    CubicStepanovUpper F B := by
  intro u v hu hv huv
  rw [cubic_charSum_eq_two_pos_add_three_sub_card hu hv huv]
  exact h u v hu hv huv

/-- Conversely, `CubicStepanovUpper` is exactly the same affine-linear positive-fiber
bound after the zero fibers have been counted.  This direction is mostly for rewriting
search goals into the finite-set form used by the Stepanov auxiliary-polynomial argument. -/
theorem positiveFiber_bound_of_cubicStepanovUpper {B : ℤ}
    (hU : CubicStepanovUpper F B) :
    ∀ u v : F, u ≠ 0 → v ≠ 0 → u ≠ v →
      2 * (((univ.filter fun s : F =>
            quadraticChar F (s * ((s - u) * (s - v))) = 1).card : ℕ) : ℤ)
        + 3 - Fintype.card F ≤ B := by
  intro u v hu hv huv
  rw [← cubic_charSum_eq_two_pos_add_three_sub_card hu hv huv]
  exact hU u v hu hv huv

#print axioms affine_point_count
#print axioms stepanov_degree_count
#print axioms pow_dvd_stepanov_degree_count
#print axioms le_rootMultiplicity_of_hasseDeriv_eq_zero
#print axioms hasseDeriv_stepanov_degree_count
#print axioms stepanov_absurd
#print axioms twist_negation
#print axioms legendreCubicHasse_of_stepanovUpper
#print axioms cubic_zero_count
#print axioms quadraticChar_sum_eq_two_pos_add_zero_sub_card
#print axioms cubic_quadraticChar_zero_count
#print axioms cubic_charSum_eq_two_pos_add_three_sub_card
#print axioms cubicStepanovUpper_of_positiveFiber_bound
#print axioms positiveFiber_bound_of_cubicStepanovUpper

end ArkLib.ProximityGap.Frontier.R20StepanovScaffold
