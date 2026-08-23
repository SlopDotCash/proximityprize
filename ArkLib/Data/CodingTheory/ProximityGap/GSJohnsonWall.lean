/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# GS-at-Johnson: the parameter arithmetic of the Guruswami–Sudan system

Round 14 of the proximity-prize grind (ArkLib #232, ABF26): the Guruswami–Sudan (GS)
algebraic/multiplicity route to Reed–Solomon list bounds.  The GS machine for
`RS[F, n, k]` interpolates a nonzero bivariate `Q(X,Y)` of `(1, k-1)`-weighted degree
`≤ D` vanishing to order `m` at the `n` points `(αᵢ, wᵢ)`; any codeword `f` agreeing
with `w` on `t` points with `t·m > D` forces `(Y - f(X)) ∣ Q`, so the list is at most
`deg_Y Q ≤ D/(k-1)`.  This file formalizes, as clean verified `ℕ`/`ℝ` arithmetic, the
PARAMETER SYSTEM of that machine and where it provably stops: the Johnson radius.

## What IS proven here (all over `ℕ` unless stated, no axioms beyond the classical three)

* `wdegMonomials k D` — the actual exponent set `{(i,j) : i + (k-1)·j ≤ D}` of
  `(1,k-1)`-weighted-degree-`≤ D` monomials, and the sharp counting lower bound
  `sq_lt_card_wdegMonomials : D² < 2(k-1)·#monomials` (Gauss-pairing proof).
* `interp_implies_monomial_excess` — for `k ≥ 2`, the arithmetic condition
  `n(k-1)m(m+1) < D²` really does imply `#monomials > n·C(m+1,2)` = the number of
  multiplicity-`m` vanishing constraints; i.e. the abstract system below is an honest
  (sufficient-form) parameterization of GS interpolation, not a free-floating inequality.
* `GSSystem n k m t D` — the GS parameter system:
  `interp : n(k-1)m(m+1) < D²` (interpolant exists, by the previous bullet) and
  `roots : t·m > D` (root order beats weighted degree along `Y = f(X)`).
* `gsFeasible_iff` — FEASIBILITY REGION: `∃ D, GSSystem n k m t D` holds **iff**
  `t·m > DGS n k m` where `DGS n k m = Nat.sqrt (n(k-1)m(m+1)) + 1` is the explicit
  minimal feasible weighted degree.  This is the exact threshold of the GS optimization.
* `gs_wall_sharp` — feasibility forces `n(k-1)(m+1) < t²·m`, i.e.
  `t² > n(k-1)(1 + 1/m)`: the multiplicity-`m` agreement threshold.
* `gs_johnson_wall`, `gs_johnson_wall_sqrt` — THE JOHNSON WALL: for EVERY multiplicity
  `m`, feasibility forces `t² > n(k-1)`, i.e. `t > Nat.sqrt (n(k-1))`.  No choice of
  `m` (or `D`) makes this parameter system certify agreement at or below `√((k-1)n)`.
* `DGS_sq_gt` — the threshold itself sits above Johnson for all `m`:
  `n(k-1)·m² < (DGS n k m)²` (so the required `t·m > DGS` always means `t > √(n(k-1))`).
* `gs_johnson_wall_real` — the real form: feasibility gives
  `√(n(k-1)·(1 + 1/m)) < t`, which tends to the Johnson bound `√((k-1)n)` as `m → ∞`.
* Concrete instances at `n = 16, k = 2` (so `√((k-1)n) = 4`): for `m = 3` the region is
  EXACTLY `t·3 > DGS = 14`, i.e. `t ≥ 5` — feasible at `t = 5` (with explicit `D = 14`,
  and the monomial count really exceeding the `96` constraints), infeasible at `t = 4`.
  Just above Johnson, never at it.

## What is NOT proven (honest scope)

* This is a no-go for THE GS PARAMETER SYSTEM in its standard sufficient form, where
  the interpolation condition is discharged via the monomial-count lower bound
  `#monomials > D²/(2(k-1))` (the form in which the GS optimization is actually run).
  A system that uses the exact lattice-point count instead is very slightly weaker at
  small parameters; its wall has the same `√((k-1)n)` asymptotics but is not formalized
  here.  Nothing here rules out OTHER algebraic certificates (different weightings,
  multivariate interpolation, folded/derivative codes …): whether any explicit such
  system beats Johnson for smooth-domain RS is exactly the open prize core.
* The algebraic half of the GS machine (interpolation/divisibility over `F[X,Y]`) is
  not re-proved here; this file is the parameter-optimization half, which is where the
  `√((k-1)n)` barrier lives.
-/

namespace GSJohnson

open Finset

/-! ## The monomial count of the GS interpolation space -/

/-- Exponent pairs `(i, j)` (for `X^i Y^j`) of `(1, k-1)`-weighted degree at most `D`.
The GS interpolation space is spanned by exactly these monomials, so its dimension is
the cardinality of this set.  (Both coordinates are forced `≤ D` when `k ≥ 2`, so
truncating the ambient grid at `D` loses nothing.) -/
def wdegMonomials (k D : ℕ) : Finset (ℕ × ℕ) :=
  (range (D + 1) ×ˢ range (D + 1)).filter fun p => p.1 + (k - 1) * p.2 ≤ D

/-- The column sum `∑_{j ≤ D/(k-1)} (D + 1 - (k-1)j)` is a lower bound for the monomial
count (it is in fact its exact value; only the bound is needed). -/
theorem sum_le_card_wdegMonomials {k : ℕ} (hk : 2 ≤ k) (D : ℕ) :
    ∑ j ∈ range (D / (k - 1) + 1), (D + 1 - (k - 1) * j) ≤ (wdegMonomials k D).card := by
  classical
  have hc : 0 < k - 1 := by omega
  have hcard : ((range (D / (k - 1) + 1)).sigma
      fun j => range (D + 1 - (k - 1) * j)).card
      = ∑ j ∈ range (D / (k - 1) + 1), (D + 1 - (k - 1) * j) := by
    rw [Finset.card_sigma]
    simp
  rw [← hcard]
  apply Finset.card_le_card_of_injOn (fun s => (s.2, s.1))
  · rintro ⟨j, i⟩ hp
    simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_range] at hp
    obtain ⟨hj, hi⟩ := hp
    have hJ : (k - 1) * (D / (k - 1)) ≤ D := by
      rw [mul_comm]; exact Nat.div_mul_le_self D (k - 1)
    have hmono : (k - 1) * j ≤ (k - 1) * (D / (k - 1)) :=
      Nat.mul_le_mul le_rfl (by omega)
    have hjle : j ≤ (k - 1) * j := Nat.le_mul_of_pos_left j hc
    simp only [Finset.mem_coe, wdegMonomials, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range]
    refine ⟨⟨?_, ?_⟩, ?_⟩ <;> omega
  · rintro ⟨j, i⟩ - ⟨j', i'⟩ - h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

/-- Gauss-pairing lower bound for the column sum: `(D+1)(D+2) ≤ 2c·∑_{j ≤ D/c} (D+1-cj)`
for any `c ≥ 1`.  (Pair the `j`-th and `(J-j)`-th columns; each pair contributes at
least `D + 2`.) -/
theorem mul_le_two_mul_sum {c : ℕ} (hc : 0 < c) (D : ℕ) :
    (D + 1) * (D + 2) ≤ 2 * c * ∑ j ∈ range (D / c + 1), (D + 1 - c * j) := by
  have hJ : c * (D / c) ≤ D := by
    rw [mul_comm]; exact Nat.div_mul_le_self D c
  have hrefl : ∑ j ∈ range (D / c + 1), (D + 1 - c * (D / c - j))
      = ∑ j ∈ range (D / c + 1), (D + 1 - c * j) := by
    have h := Finset.sum_range_reflect (fun j => D + 1 - c * j) (D / c + 1)
    simpa using h
  have hsplit : 2 * ∑ j ∈ range (D / c + 1), (D + 1 - c * j)
      = ∑ j ∈ range (D / c + 1), ((D + 1 - c * j) + (D + 1 - c * (D / c - j))) := by
    rw [Finset.sum_add_distrib, hrefl, two_mul]
  have hpoint : ∀ j ∈ range (D / c + 1),
      D + 2 ≤ (D + 1 - c * j) + (D + 1 - c * (D / c - j)) := by
    intro j hj
    simp only [Finset.mem_range] at hj
    have hsum : c * j + c * (D / c - j) = c * (D / c) := by
      rw [← Nat.mul_add]
      congr 1
      omega
    omega
  have hbound : (D / c + 1) * (D + 2)
      ≤ ∑ j ∈ range (D / c + 1), ((D + 1 - c * j) + (D + 1 - c * (D / c - j))) := by
    calc (D / c + 1) * (D + 2) = ∑ _j ∈ range (D / c + 1), (D + 2) := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum hpoint
  have hcJ : D + 1 ≤ c * (D / c + 1) := by
    have h1 : c * (D / c) + D % c = D := Nat.div_add_mod D c
    have h2 : D % c < c := Nat.mod_lt D hc
    have h3 : c * (D / c + 1) = c * (D / c) + c := by ring
    omega
  calc (D + 1) * (D + 2) ≤ (c * (D / c + 1)) * (D + 2) := Nat.mul_le_mul hcJ le_rfl
  _ = c * ((D / c + 1) * (D + 2)) := by ring
  _ ≤ c * (2 * ∑ j ∈ range (D / c + 1), (D + 1 - c * j)) := by
      rw [hsplit]; exact Nat.mul_le_mul le_rfl hbound
  _ = 2 * c * ∑ j ∈ range (D / c + 1), (D + 1 - c * j) := by ring

/-- THE COUNTING BRICK: the number of `(1, k-1)`-weighted-degree-`≤ D` monomials
strictly exceeds `D² / (2(k-1))`, in exact-`ℕ` form `D² < 2(k-1)·#monomials`. -/
theorem sq_lt_card_wdegMonomials {k : ℕ} (hk : 2 ≤ k) (D : ℕ) :
    D ^ 2 < 2 * (k - 1) * (wdegMonomials k D).card := by
  have hc : 0 < k - 1 := by omega
  have h3 : D ^ 2 < (D + 1) * (D + 2) := by nlinarith [sq_nonneg D]
  calc D ^ 2 < (D + 1) * (D + 2) := h3
  _ ≤ 2 * (k - 1) * ∑ j ∈ range (D / (k - 1) + 1), (D + 1 - (k - 1) * j) :=
      mul_le_two_mul_sum hc D
  _ ≤ 2 * (k - 1) * (wdegMonomials k D).card :=
      Nat.mul_le_mul le_rfl (sum_le_card_wdegMonomials hk D)

/-- HONESTY BRIDGE: the abstract interpolation condition `n(k-1)m(m+1) < D²` used in
`GSSystem` really implies that the monomial count strictly exceeds the number
`n·C(m+1,2)` of multiplicity-`m` vanishing constraints — so a nonzero interpolant of
weighted degree `≤ D` exists by linear algebra.  The `GSSystem` below is therefore an
honest (sufficient-form) rendering of the GS interpolation step, for every `k ≥ 2`. -/
theorem interp_implies_monomial_excess {n k m D : ℕ} (hk : 2 ≤ k)
    (hI : n * (k - 1) * m * (m + 1) < D ^ 2) :
    n * Nat.choose (m + 1) 2 < (wdegMonomials k D).card := by
  have h1 : n * (k - 1) * m * (m + 1) < 2 * (k - 1) * (wdegMonomials k D).card :=
    hI.trans (sq_lt_card_wdegMonomials hk D)
  have h3 : (k - 1) * (n * m * (m + 1)) < (k - 1) * (2 * (wdegMonomials k D).card) := by
    calc (k - 1) * (n * m * (m + 1)) = n * (k - 1) * m * (m + 1) := by ring
    _ < 2 * (k - 1) * (wdegMonomials k D).card := h1
    _ = (k - 1) * (2 * (wdegMonomials k D).card) := by ring
  have h4 : n * m * (m + 1) < 2 * (wdegMonomials k D).card :=
    Nat.lt_of_mul_lt_mul_left h3
  have h5 : 2 * Nat.choose (m + 1) 2 = m * (m + 1) := by
    have hdvd : 2 ∣ (m + 1) * m := by
      rw [mul_comm]; exact (Nat.even_mul_succ_self m).two_dvd
    rw [Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_div_cancel' hdvd]
    ring
  have h6 : 2 * (n * Nat.choose (m + 1) 2) = n * m * (m + 1) := by
    calc 2 * (n * Nat.choose (m + 1) 2) = n * (2 * Nat.choose (m + 1) 2) := by ring
    _ = n * (m * (m + 1)) := by rw [h5]
    _ = n * m * (m + 1) := by ring
  omega

/-! ## The GS parameter system and its feasibility region -/

/-- The Guruswami–Sudan parameter system for `RS[F, n, k]` at multiplicity `m`,
agreement `t`, weighted degree `D`:

* `interp : n(k-1)m(m+1) < D²` — by `interp_implies_monomial_excess` (for `k ≥ 2`) the
  `(1,k-1)`-weighted monomial count then strictly exceeds the `n·C(m+1,2)` vanishing
  constraints, so a nonzero interpolant `Q` of weighted degree `≤ D` exists;
* `roots : t·m > D` — agreement `t` then gives `Q(X, f(X))` a root count `t·m`
  exceeding its degree bound `D`, forcing `(Y - f(X)) ∣ Q` and a list bound
  `deg_Y Q ≤ D/(k-1)`. -/
structure GSSystem (n k m t D : ℕ) : Prop where
  interp : n * (k - 1) * m * (m + 1) < D ^ 2
  roots : D < t * m

/-- Joint satisfiability of the GS parameter system for some weighted degree `D`. -/
def GSFeasible (n k m t : ℕ) : Prop := ∃ D, GSSystem n k m t D

/-- The minimal weighted degree satisfying the interpolation condition: the explicit
GS threshold.  `gsFeasible_iff` shows the system is feasible iff `t·m > DGS n k m`. -/
def DGS (n k m : ℕ) : ℕ := Nat.sqrt (n * (k - 1) * m * (m + 1)) + 1

/-- FEASIBILITY REGION: the GS parameter system is satisfiable for some `D` **iff**
the agreement-multiplicity product clears the explicit threshold `DGS n k m`.
(The threshold on `t` itself is thus `t > DGS n k m / m`.) -/
theorem gsFeasible_iff {n k m t : ℕ} :
    GSFeasible n k m t ↔ DGS n k m < t * m := by
  constructor
  · rintro ⟨D, hI, hR⟩
    have h1 : Nat.sqrt (n * (k - 1) * m * (m + 1)) < D := Nat.sqrt_lt'.mpr hI
    unfold DGS
    omega
  · intro hlt
    refine ⟨DGS n k m, ⟨?_, hlt⟩⟩
    have h := Nat.lt_succ_sqrt' (n * (k - 1) * m * (m + 1))
    unfold DGS
    simpa using h

/-! ## The Johnson wall -/

/-- SHARP WALL: any feasible agreement satisfies `t²·m > n(k-1)(m+1)`, i.e.
`t² > n(k-1)(1 + 1/m)` — the exact multiplicity-`m` GS threshold. -/
theorem gs_wall_sharp {n k m t : ℕ} (h : GSFeasible n k m t) :
    n * (k - 1) * (m + 1) < t ^ 2 * m := by
  obtain ⟨D, hI, hR⟩ := h
  have h2 : n * (k - 1) * m * (m + 1) < t ^ 2 * m ^ 2 := by
    calc n * (k - 1) * m * (m + 1) < D ^ 2 := hI
    _ ≤ (t * m) ^ 2 := Nat.pow_le_pow_left hR.le 2
    _ = t ^ 2 * m ^ 2 := by ring
  have h3 : n * (k - 1) * (m + 1) * m < t ^ 2 * m * m := by
    calc n * (k - 1) * (m + 1) * m = n * (k - 1) * m * (m + 1) := by ring
    _ < t ^ 2 * m ^ 2 := h2
    _ = t ^ 2 * m * m := by ring
  exact lt_of_mul_lt_mul_right h3 (Nat.zero_le m)

/-- THE JOHNSON WALL: for EVERY multiplicity `m`, GS feasibility forces
`t² > n(k-1)`.  No choice of `m` or `D` lets the GS parameter system certify
agreement at or below the Johnson bound `√((k-1)n)`. -/
theorem gs_johnson_wall {n k m t : ℕ} (h : GSFeasible n k m t) :
    n * (k - 1) < t ^ 2 := by
  have hs := gs_wall_sharp h
  have h1 : n * (k - 1) * m < t ^ 2 * m :=
    lt_of_le_of_lt (Nat.mul_le_mul le_rfl (Nat.le_succ m)) hs
  exact lt_of_mul_lt_mul_right h1 (Nat.zero_le m)

/-- The Johnson wall in `Nat.sqrt` form: any feasible agreement strictly exceeds
`√(n(k-1))`. -/
theorem gs_johnson_wall_sqrt {n k m t : ℕ} (h : GSFeasible n k m t) :
    Nat.sqrt (n * (k - 1)) < t :=
  Nat.sqrt_lt'.mpr (gs_johnson_wall h)

/-- The threshold itself sits above Johnson for ALL multiplicities:
`(DGS n k m)² > n(k-1)·m²`, so the required `t·m > DGS n k m` always means
`(t·m)² > n(k-1)·m²`, i.e. `t > √(n(k-1))`. -/
theorem DGS_sq_gt (n k m : ℕ) : n * (k - 1) * m ^ 2 < DGS n k m ^ 2 := by
  have h := Nat.lt_succ_sqrt' (n * (k - 1) * m * (m + 1))
  calc n * (k - 1) * m ^ 2 = n * (k - 1) * m * m := by ring
  _ ≤ n * (k - 1) * m * (m + 1) := Nat.mul_le_mul le_rfl (by omega)
  _ < DGS n k m ^ 2 := by unfold DGS; simpa using h

/-- The Johnson wall over `ℝ`: any feasible agreement strictly exceeds
`√(n(k-1)(1 + 1/m))`, which decreases to the Johnson bound `√((k-1)n)` as `m → ∞`
but never reaches it. -/
theorem gs_johnson_wall_real {n k m t : ℕ} (h : GSFeasible n k m t) :
    Real.sqrt ((n * (k - 1) : ℕ) * (1 + 1 / (m : ℝ))) < (t : ℝ) := by
  obtain ⟨D, hI, hR⟩ := h
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp at hR
    · exact hm
  have ht : 0 < t := by
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp at hR
    · exact ht
  have hs : n * (k - 1) * (m + 1) < t ^ 2 * m := gs_wall_sharp ⟨D, hI, hR⟩
  have ht' : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [Real.sqrt_lt' ht']
  have hG : ((n * (k - 1) : ℕ) : ℝ) * (1 + 1 / (m : ℝ))
      = ((n * (k - 1) : ℕ) : ℝ) * ((m : ℝ) + 1) / (m : ℝ) := by
    field_simp
  rw [hG, div_lt_iff₀ hm']
  exact_mod_cast hs

/-! ## Concrete instances: the wall at `n = 16, k = 2` (Johnson bound `√16 = 4`)

Non-vacuity witnesses for every hypothesis above: an explicit feasible point just above
the wall, the exact feasibility region at `m = 3`, infeasibility at the wall, and a
verified monomial-count excess for the feasible point. -/

/-- Explicit feasible GS point just above Johnson: `n = 16, k = 2, m = 3, t = 5`
with witness degree `D = 14` (`16·1·3·4 = 192 < 196 = 14²` and `14 < 15 = t·m`). -/
theorem feasible_16_2_3_5 : GSFeasible 16 2 3 5 :=
  ⟨14, ⟨by norm_num, by norm_num⟩⟩

/-- At the feasible point, the interpolation condition really gives more monomials
(`120`) than constraints (`16·C(4,2) = 96`): the system is honest, not vacuous. -/
theorem monomial_excess_16_2_14 :
    16 * Nat.choose 4 2 < (wdegMonomials 2 14).card :=
  interp_implies_monomial_excess (by norm_num) (by norm_num)

/-- The explicit threshold at `n = 16, k = 2, m = 3`: `DGS = ⌊√192⌋ + 1 = 14`. -/
theorem DGS_16_2_3 : DGS 16 2 3 = 14 := by
  have h1 : 13 ≤ Nat.sqrt 192 := Nat.le_sqrt.mpr (by norm_num)
  have h2 : Nat.sqrt 192 < 14 := Nat.sqrt_lt'.mpr (by norm_num)
  have h3 : DGS 16 2 3 = Nat.sqrt 192 + 1 := by norm_num [DGS]
  omega

/-- The EXACT feasibility region at `n = 16, k = 2, m = 3`: feasible iff `t·3 > 14`,
i.e. iff `t ≥ 5` — strictly above the Johnson bound `4`. -/
theorem feasibility_region_16_2_3 (t : ℕ) : GSFeasible 16 2 3 t ↔ 14 < t * 3 := by
  rw [gsFeasible_iff, DGS_16_2_3]

/-- At the Johnson bound itself (`t = 4 = √(16·1)`) the system is infeasible at `m = 3`. -/
theorem infeasible_16_2_3_4 : ¬ GSFeasible 16 2 3 4 := by
  intro h
  have hw := gs_johnson_wall h
  norm_num at hw

/-- The wall at `n = 16, k = 2` for EVERY multiplicity `m`: feasibility forces `t > 4`. -/
theorem wall_16_2 (m t : ℕ) (h : GSFeasible 16 2 m t) : 4 < t := by
  have hw := gs_johnson_wall_sqrt h
  have h4 : Nat.sqrt (16 * (2 - 1)) = 4 := by
    have he : (16 * (2 - 1) : ℕ) = 16 := by norm_num
    rw [he]
    have h1 : 4 ≤ Nat.sqrt 16 := Nat.le_sqrt.mpr (by norm_num)
    have h2 : Nat.sqrt 16 < 5 := Nat.sqrt_lt'.mpr (by norm_num)
    omega
  omega

end GSJohnson

#print axioms GSJohnson.sq_lt_card_wdegMonomials
#print axioms GSJohnson.interp_implies_monomial_excess
#print axioms GSJohnson.gsFeasible_iff
#print axioms GSJohnson.gs_wall_sharp
#print axioms GSJohnson.gs_johnson_wall
#print axioms GSJohnson.gs_johnson_wall_sqrt
#print axioms GSJohnson.DGS_sq_gt
#print axioms GSJohnson.gs_johnson_wall_real
#print axioms GSJohnson.feasible_16_2_3_5
#print axioms GSJohnson.monomial_excess_16_2_14
#print axioms GSJohnson.feasibility_region_16_2_3
#print axioms GSJohnson.infeasible_16_2_3_4
#print axioms GSJohnson.wall_16_2
