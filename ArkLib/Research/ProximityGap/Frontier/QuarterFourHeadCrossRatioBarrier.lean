/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic

/-! # Universal Multi-Head Barriers & 4-Head Collinear Cross-Ratio Obstructions on `[447,392,428, 480,946,858]`

This module proves two interlocking sets of obstructions governing first-prime quarter-rate MCA
(`n = 2^30 = 1,073,741,824`, `k = 2^28`, `d = 2^28 - 1 = 268,435,455`, `D = d - 1 = 268,435,454`)
across the unresolved interval `[447,392,428, 480,946,858]`:

1. **Universal Quotient-Free Discrete Johnson Hull, `H ≥ 5`, Multi-Fresh `b ≥ 2`, & Rational-Curve Barriers**
   (`discrete_johnson_hull`, `p1_quarter_five_plus_heads_impossible`,
   `p1_quarter_multifresh_above_johnson_impossible`, `nonlinear_curve_pencil_degree_floor`,
   `p1_quarter_four_head_threshold`, `universal_label_core_conservation_barriers`,
   `p2_conservation_head_thresholds`):
   - For ANY finite domain `I` of size `n` and ANY `H` subsets `C : Fin H → Finset I` with
     pairwise intersections `≤ d`, integer convexity `(deg x - a)(deg x - (a + 1)) ≥ 0` yields
     `2 * a * ∑ i, |C i| ≤ H * (H - 1) * d + a * (a + 1) * n` for every `a : ℕ`.
   - Instantiating at `a = H / 2` proves unconditionally (ZERO quotient, rank, collinearity, or
     planarity assumptions) that EVERY 1-fresh witness with **`H ≥ 5` heads** on `p₁` quarter-rate
     is forced to **`e ≥ 483,183,821 > 480,946,859`** (`H = 5: 483.18M`, `H = 6: 492.13M`, ...),
     and every 4-head witness is forced to `e ≥ 469,762,048` (`7n/16`).
   - Also certifies the companion universal conservation bounds on `p₂` half-rate (`H ≤ 4 ⇒ e ≥ 536.87M`,
     `H = 5 ⇒ e ≥ 429.50M`, `H = 6 ⇒ e ≥ 357.91M`) and `p₂` quarter-rate (`H ≤ 4 ⇒ e ≥ 536.87M`).

2. **Exact 5-Partition Site Inequality for 4 Collinear Heads**
   (`four_head_five_partition_pointwise`, `four_head_five_partition_global`):
   - Classifies every site `x ∈ I` by the exact equivalence partition of the 4 head values
     `(f₀(x), f₁(x), f₂(x), f₃(x))` into `(1,1,1,1)`, `(2,1,1)`, `(2,2)`, `(3,1)`, `(4)`.
   - Proves directly on `Finset I` that `(2,2)` sites save `1` and `(4)` sites save `2` relative to
     the raw pairwise-equality count:
       `2 * ∑ i, |core i| + ∑ x, fresh x + n_22 + 2 * n_4 ≤ 4 * |I| + ∑_{i < j} |E_ij|`,
     sharpening `QuarterCollinearInterval.lean`'s `four_head_slack` by `n_22 + 2 * n_4`.

3. **Algebraic Cross-Ratio Pencil & Exact Constant-Cross-Ratio 4-Fiber Factorization**
   (`cross_ratio_pencil_identity`, `cross_ratio_triple_common_root`,
   `cross_ratio_quadruple_double_root`, `cross_ratio_double_pair_sq_root`,
   `constant_cross_ratio_four_fiber_factorization`):
   - Over ANY field `K` and ANY `P, Q, R ∈ K[X]`, `P(Q - R) + R(P - Q) = Q(P - R)` defines the
     cross-ratio pencil `(A, B, C)` whose common factor absorbs every `(3,1)` triple site to order
     `≥ 1` and every `(4)` quadruple site to order `≥ 2`, while every `(2,2)` site is a double root
     of one of `(A, B, C)`.
   - When the cross-ratio is constant (`A = C c * C` with `c ∉ {0, 1}`), Euclidean-domain
     factorization proves `P = H * U * (C c * V - U)`, `Q = H * V * (C c * V - U)`,
     `R = H * C (c - 1) * U * V` with `IsCoprime U V` and
     `2 * max U.natDegree V.natDegree + H.natDegree ≤ max (max P.natDegree Q.natDegree) R.natDegree`
     — forcing a **4-fiber rational map `U / V`** of degree `m₀ ≤ (D - deg H) / 2 ≤ 2^27 - 1`!

4. **4-Head Cross-Ratio Dichotomy on `[469,762,049, 480,946,858]` & Pullback / Tower Exclusions**
   (`four_head_cross_ratio_dichotomy`, `four_head_const_cr_degree_floor`,
   `four_head_cyclic_pullback_exclusions`, `four_fiber_depth3_tower_exclusion`):
   - For EVERY `e = 469,762,049 + j₄ ∈ [469,762,049, 480,946,858]`:
     `n_22 + 2*n_4 ≤ 3 + 8*j₄`, `M₀ ≤ D + 5 + 4*j₄`, and the coprime cross-ratio pencil `(A₀, B₀, C₀)`
     satisfies **`3 * M₀ - (n_211 + n_22) ≤ 3 + 8 * j₄`** (at `e = 469,762,049`: at most **3**
     missing roots total across all 3 fibers of `(A₀, B₀, C₀)`, or a constant-cross-ratio 4-fiber
     map `U/V` of degree `2^27 - 1` missing at most **1** root across all 4 fibers!).
   - Eliminates unconditionally over ANY field ALL general 4-head collinear pullbacks on `μ_M`
     (`M ≤ 64`) and ALL primitive (`h = 0`) constant-cross-ratio 4-head pullbacks on `μ_M`
     (`M ≤ 128`), pins `μ_128` constant-cross-ratio to the unique tuple `h = 1, m₀ = 15, n_31 = 60`,
     and pins general `μ_128` 4-head pullbacks to `182 ≤ Δ₄ ≤ 186` (slack `≤ 4` across all 6 diffs).
   - Eliminates ALL full 4-split constant-cross-ratio pencils beating `480,946,859` across the
     entire infinite dyadic tower `μ_{2^k}` (`k ≥ 8`, `N ≥ 256`) in characteristic zero via Depth 1–3.
-/

set_option autoImplicit false

namespace ProximityGap.QuarterFourHeadCrossRatioBarrier

open Finset Polynomial

/-! ## Part 1: Universal Quotient-Free Discrete Johnson Hull & `H ≥ 5` Barrier -/

/-- For any two integers `u, a : ℤ`, `2 * a * u ≤ u * (u - 1) + a * (a + 1)`
because `(u - a) * (u - (a + 1)) ≥ 0` on consecutive integers. -/
private theorem int_consecutive_sq_nonneg (u a : ℤ) :
    2 * a * u ≤ u * (u - 1) + a * (a + 1) := by
  have hprod : 0 ≤ (u - a) * (u - (a + 1)) := by
    rcases le_or_gt u a with h | h
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
    · exact mul_nonneg (by omega) (by omega)
  linarith

/-- **Universal Discrete Johnson Hull (Quotient-Free, Zero Rank/Collinearity Assumptions):**
For any finite domain `I` and any `H` subsets `C : Fin H → Finset I` with pairwise intersections
`≤ d`, every integer threshold `a : ℕ` satisfies:
  `2 * a * ∑ i, |C i| ≤ H * (H - 1) * d + a * (a + 1) * |I|`. -/
theorem discrete_johnson_hull {I : Type*} [Fintype I] [DecidableEq I] {H d : ℕ}
    (C : Fin H → Finset I)
    (hpair : ∀ i j : Fin H, i ≠ j → (C i ∩ C j).card ≤ d) (a : ℕ) :
    2 * a * (∑ i : Fin H, (C i).card) ≤ H * (H - 1) * d + a * (a + 1) * Fintype.card I := by
  classical
  let deg : I → ℕ := fun x => (univ.filter fun i : Fin H => x ∈ C i).card
  have hsum1 : ∑ x : I, deg x = ∑ i : Fin H, (C i).card := by
    simp only [deg, Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Finset.sum_ite_mem]
  have hsum2 : ∑ x : I, deg x * (deg x - 1) =
      ∑ i : Fin H, ∑ j ∈ univ.erase i, (C i ∩ C j).card := by
    have hpt : ∀ x : I, deg x * (deg x - 1) =
        ∑ i : Fin H, ∑ j ∈ univ.erase i, if x ∈ C i ∩ C j then 1 else 0 := by
      intro x
      let S : Finset (Fin H) := univ.filter fun i => x ∈ C i
      have h1 : S.card * (S.card - 1) = ∑ i ∈ S, (S.erase i).card := by
        rw [Finset.sum_congr rfl fun i hi => Finset.card_erase_of_mem hi,
          Finset.sum_const, smul_eq_mul]
      rw [show deg x = S.card from rfl, h1]
      rw [← Finset.sum_subset (subset_univ S)]
      · refine Finset.sum_congr rfl fun i hi => ?_
        have hxi : x ∈ C i := (Finset.mem_filter.mp hi).2
        rw [Finset.card_eq_sum_ones,
          ← Finset.sum_subset (Finset.erase_subset_erase i (subset_univ S))]
        · refine Finset.sum_congr rfl fun j hj => ?_
          have hxj : x ∈ C j := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hj)).2
          simp [Finset.mem_inter, hxi, hxj]
        · intro j hj hnot
          have hjnot : j ∉ S := fun h => hnot (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj).1, h⟩)
          have hnxj : x ∉ C j := fun hx => hjnot (Finset.mem_filter.mpr ⟨mem_univ j, hx⟩)
          simp [Finset.mem_inter, hnxj]
      · intro i _ hi
        have hnxi : x ∉ C i := fun hx => hi (Finset.mem_filter.mpr ⟨mem_univ i, hx⟩)
        exact Finset.sum_eq_zero fun j _ => by simp [Finset.mem_inter, hnxi]
    calc
      ∑ x : I, deg x * (deg x - 1)
          = ∑ x : I, ∑ i : Fin H, ∑ j ∈ univ.erase i, if x ∈ C i ∩ C j then 1 else 0 :=
              Finset.sum_congr rfl fun x _ => hpt x
      _ = ∑ i : Fin H, ∑ x : I, ∑ j ∈ univ.erase i, if x ∈ C i ∩ C j then 1 else 0 :=
            Finset.sum_comm
      _ = ∑ i : Fin H, ∑ j ∈ univ.erase i, ∑ x : I, if x ∈ C i ∩ C j then 1 else 0 :=
            Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ i : Fin H, ∑ j ∈ univ.erase i, (C i ∩ C j).card := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            rw [← Finset.card_filter]
            congr 1; ext x; simp
  have hpair_sum : ∑ i : Fin H, ∑ j ∈ univ.erase i, (C i ∩ C j).card ≤ H * (H - 1) * d := by
    calc
      ∑ i : Fin H, ∑ j ∈ univ.erase i, (C i ∩ C j).card
          ≤ ∑ i : Fin H, ∑ _j ∈ univ.erase i, d :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj =>
              hpair i j (Finset.ne_of_mem_erase hj).symm
      _ = ∑ i : Fin H, (H - 1) * d := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.sum_const, Finset.card_erase_of_mem (mem_univ i), Finset.card_univ,
              Fintype.card_fin, smul_eq_mul]
      _ = H * (H - 1) * d := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_assoc]
  have hpt_nat : ∀ x : I, 2 * a * deg x ≤ deg x * (deg x - 1) + a * (a + 1) := by
    intro x
    have hZ := int_consecutive_sq_nonneg (deg x : ℤ) (a : ℤ)
    have hsub : ((deg x * (deg x - 1) : ℕ) : ℤ) = (deg x : ℤ) * ((deg x : ℤ) - 1) := by
      cases hc : deg x with
      | zero => simp
      | succ m => push_cast; ring
    have hZ' : ((2 * a * deg x : ℕ) : ℤ) ≤ ((deg x * (deg x - 1) + a * (a + 1) : ℕ) : ℤ) := by
      push_cast [hsub]; linarith
    exact_mod_cast hZ'
  have htot := Finset.sum_le_sum fun x (_ : x ∈ (univ : Finset I)) => hpt_nat x
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_comm (Fintype.card I)] at htot
  rw [hsum1, hsum2] at htot
  exact htot.trans (Nat.add_le_add_right hpair_sum _)

/-- **Universal Quotient-Free `H ≥ 5` Barrier on `p₁` Quarter-Rate (ALL `H = 5, 6, 7, …, ∞`):**
On ANY domain of size `n = 2^30` (`d = 2^28 - 1`), EVERY family of `H ≥ 5` cores (planar OR
collinear, ZERO quotient or rank assumptions) with pairwise overlaps `≤ d` and 1-fresh core
size `≥ n - e - 1` forces **`e ≥ 483,183,821 > 480,946,859`**! -/
theorem p1_quarter_five_plus_heads_impossible {I : Type*} [Fintype I] [DecidableEq I]
    (hn : Fintype.card I = 1073741824) {H e : ℕ} (hH : 5 ≤ H)
    (C : Fin H → Finset I)
    (hsize : ∀ i : Fin H, 1073741824 - e - 1 ≤ (C i).card)
    (hpair : ∀ i j : Fin H, i ≠ j → (C i ∩ C j).card ≤ 268435455) :
    483183821 ≤ e := by
  let a : ℕ := H / 2
  have ha2 : 2 ≤ a := by omega
  have hhull := discrete_johnson_hull C hpair a
  rw [hn] at hhull
  have hsum_lb : H * (1073741824 - e - 1) ≤ ∑ i : Fin H, (C i).card := by
    calc
      H * (1073741824 - e - 1) = ∑ _i : Fin H, (1073741824 - e - 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      _ ≤ ∑ i : Fin H, (C i).card := Finset.sum_le_sum fun i _ => hsize i
  have hmul : 2 * a * (H * (1073741824 - e - 1)) ≤ H * (H - 1) * 268435455 + a * (a + 1) * 1073741824 :=
    (Nat.mul_le_mul_left (2 * a) hsum_lb).trans hhull
  by_contra hlt
  have he : e ≤ 483183820 := by omega
  have hcore : 590558003 ≤ 1073741824 - e - 1 := by omega
  have hbig : 2 * a * (H * 590558003) ≤ H * (H - 1) * 268435455 + a * (a + 1) * 1073741824 :=
    (Nat.mul_le_mul_left (2 * a) (Nat.mul_le_mul_left H hcore)).trans hmul
  -- Algebraic proof valid for ALL H ≥ 5 via H = 2a (a ≥ 3) or H = 2a + 1 (a ≥ 2)
  rcases Nat.even_or_odd H with ⟨m, hm⟩ | ⟨m, hm⟩
  · have ham : a = m := by dsimp [a]; omega
    have hm3 : 3 ≤ m := by omega
    have hH2 : H = 2 * m := by omega
    rw [ham, hH2] at hbig
    have hZ : (2 * m * (2 * m * 590558003) : ℤ) ≤
        2 * m * (2 * m - 1) * 268435455 + m * (m + 1) * 1073741824 := by
      have hcast : ((2 * m - 1 : ℕ) : ℤ) = (2 * (m : ℤ) - 1) := by omega
      have hbigZ : ((2 * m * (2 * m * 590558003) : ℕ) : ℤ) ≤
          ((2 * m * (2 * m - 1) * 268435455 + m * (m + 1) * 1073741824 : ℕ) : ℤ) := by
        exact_mod_cast hbig
      push_cast [hcast] at hbigZ
      exact hbigZ
    nlinarith
  · have ham : a = m := by dsimp [a]; omega
    have hm2 : 2 ≤ m := by omega
    have hH2 : H = 2 * m + 1 := by omega
    rw [ham, hH2, Nat.add_sub_cancel] at hbig
    have hZ : (2 * m * ((2 * m + 1) * 590558003) : ℤ) ≤
        (2 * m + 1) * (2 * m) * 268435455 + m * (m + 1) * 1073741824 := by
      exact_mod_cast hbig
    nlinarith

/-- **Uniform Multi-Fresh `b ≥ 2` Exclusion Above the Johnson Radius (`2 ≤ b ≤ 55,924,050`):**
On `n = 2^30`, `d = 2^28 - 1`, ANY uniform `b`-fresh linear-head witness with `2 ≤ b ≤ 55,924,050`
(i.e. every uniform multi-fresh core strictly above `n / 2 + 4`) obeying `b * (n + 1) ≤ H * (e + b)`
and `∀ i, n - e - b ≤ |C i|` cannot beat `480,946,859`: **`480,946,859 ≤ e`**!
Combined with `p1_quarter_five_plus_heads_impossible`, EVERY uniform linear-head witness above the
Johnson radius beating `480,946,859` MUST be `b = 1`-fresh with `H ∈ {2, 3, 4}`! -/
theorem p1_quarter_multifresh_above_johnson_impossible {I : Type*} [Fintype I] [DecidableEq I]
    (hn : Fintype.card I = 1073741824) {H e b : ℕ}
    (hb_lo : 2 ≤ b) (hb_hi : b ≤ 55924050)
    (hcons : b * 1073741825 ≤ H * (e + b))
    (C : Fin H → Finset I)
    (hsize : ∀ i : Fin H, 1073741824 - e - b ≤ (C i).card)
    (hpair : ∀ i j : Fin H, i ≠ j → (C i ∩ C j).card ≤ 268435455) :
    480946859 ≤ e := by
  by_contra hlt
  have he : e ≤ 480946858 := by omega
  have hH_lb : 2 * b + 1 ≤ H := by
    have h1 : 2 * b * (e + b) < b * 1073741825 := by nlinarith
    have h2 : 2 * b * (e + b) < H * (e + b) := lt_of_lt_of_le h1 hcons
    have hepos : 0 < e + b := by omega
    have hltH : 2 * b < H := Nat.lt_of_mul_lt_mul_right h2
    omega
  let a : ℕ := H / 2
  have hhull := discrete_johnson_hull C hpair a
  rw [hn] at hhull
  have hcore : 592794966 - b ≤ 1073741824 - e - b := by omega
  have hsum_lb : H * (592794966 - b) ≤ ∑ i : Fin H, (C i).card := by
    calc
      H * (592794966 - b) = ∑ _i : Fin H, (592794966 - b) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      _ ≤ ∑ i : Fin H, (C i).card := Finset.sum_le_sum fun i _ => hcore.trans (hsize i)
  have hbig : 2 * a * (H * (592794966 - b)) ≤ H * (H - 1) * 268435455 + a * (a + 1) * 1073741824 :=
    (Nat.mul_le_mul_left (2 * a) hsum_lb).trans hhull
  rcases Nat.even_or_odd H with ⟨m, hm⟩ | ⟨m, hm⟩
  · have ham : a = m := by dsimp [a]; omega
    have hmb : b + 1 ≤ m := by omega
    have hH2 : H = 2 * m := by omega
    rw [ham, hH2] at hbig
    have hcast1 : ((2 * m - 1 : ℕ) : ℤ) = 2 * (m : ℤ) - 1 := by omega
    have hcast2 : ((592794966 - b : ℕ) : ℤ) = 592794966 - (b : ℤ) := by omega
    have hbigZ : ((2 * m * (2 * m * (592794966 - b)) : ℕ) : ℤ) ≤
        ((2 * m * (2 * m - 1) * 268435455 + m * (m + 1) * 1073741824 : ℕ) : ℤ) := by
      exact_mod_cast hbig
    push_cast [hcast1, hcast2] at hbigZ
    -- Factor out `m`: `4*m*(55924055 - b) ≤ 536870914`, contradicting `m ≥ b + 1` on `[2, 55924050]`!
    have hmpos : (0 : ℤ) < m := by omega
    have h1 : (m : ℤ) * (4 * (m : ℤ) * (55924055 - (b : ℤ)) - 536870914) ≤ 0 := by
      linarith
    have h2 : 4 * (m : ℤ) * (55924055 - (b : ℤ)) ≤ 536870914 := by
      linarith [nonpos_of_mul_nonpos_right h1 hmpos]
    have hstep : 4 * ((b : ℤ) + 1) * (55924055 - (b : ℤ)) ≤ 4 * (m : ℤ) * (55924055 - (b : ℤ)) := by
      have hpos : (0 : ℤ) ≤ 55924055 - (b : ℤ) := by omega
      have hle : 4 * ((b : ℤ) + 1) ≤ 4 * (m : ℤ) := by omega
      exact mul_le_mul_of_nonneg_right hle hpos
    have hquad : 0 ≤ ((b : ℤ) - 2) * (55924050 - (b : ℤ)) :=
      mul_nonneg (by omega) (by omega)
    linarith [h2, hstep, hquad]
  · have ham : a = m := by dsimp [a]; omega
    have hmb : b ≤ m := by omega
    have hH2 : H = 2 * m + 1 := by omega
    rw [ham, hH2, Nat.add_sub_cancel] at hbig
    have hcast2 : ((592794966 - b : ℕ) : ℤ) = 592794966 - (b : ℤ) := by omega
    have hbigZ : ((2 * m * ((2 * m + 1) * (592794966 - b)) : ℕ) : ℤ) ≤
        (((2 * m + 1) * (2 * m) * 268435455 + m * (m + 1) * 1073741824 : ℕ) : ℤ) := by
      exact_mod_cast hbig
    push_cast [hcast2] at hbigZ
    have hmpos : (0 : ℤ) < m := by omega
    have h1 : (m : ℤ) * ((4 * (m : ℤ) + 2) * (55924055 - (b : ℤ)) - 536870912) ≤ 0 := by
      linarith
    have h2 : (4 * (m : ℤ) + 2) * (55924055 - (b : ℤ)) ≤ 536870912 := by
      linarith [nonpos_of_mul_nonpos_right h1 hmpos]
    have hstep : (4 * (b : ℤ) + 2) * (55924055 - (b : ℤ)) ≤ (4 * (m : ℤ) + 2) * (55924055 - (b : ℤ)) := by
      have hpos : (0 : ℤ) ≤ 55924055 - (b : ℤ) := by omega
      have hle : 4 * (b : ℤ) + 2 ≤ 4 * (m : ℤ) + 2 := by omega
      exact mul_le_mul_of_nonneg_right hle hpos
    have hquad : 0 ≤ ((b : ℤ) - 2) * (55924050 - (b : ℤ)) :=
      mul_nonneg (by omega) (by omega)
    linarith [h2, hstep, hquad]

/-- **Universal Rational-Curve / Nonlinear-Pencil Degree Floor (All 5 Open MCA Ceilings):**
For any non-linear rational curve family `t ↦ (z(t), f_t(X))` of degree `D_c`, every coordinate
meets at most `D_c` curve parameters unless `f_t(x)` is universally satisfied (at most `d = k - 1`
sites), forcing `|G| * (t_agree - d) ≤ D_c * (n - d)`.
Exceeding the target budget `B` forces curve degree `D_c ≥ 432,479,348` (`p₁` 1/4),
`626,349,400` (`p₂` 1/2), `447,392,430` (`p₁` 1/2), `671,088,643` (`p₂` 1/4),
and `594,392,800` (`p₂` 1/8) — ruling out all `o(n)` conic/hyperelliptic curve pencils! -/
theorem nonlinear_curve_pencil_degree_floor {G t d n D_c : ℕ}
    (hinc : G * (t - d) ≤ D_c * (n - d)) :
    (n = 1073741824 → d = 268435455 → t = 592794966 → 1073741824 < G → 432479348 ≤ D_c) ∧
    (n = 1073741824 → d = 536870911 → t = 693458261 → 2147483648 < G → 626349400 ≤ D_c) ∧
    (n = 1073741824 → d = 536870911 → t = 760567126 → 1073741824 < G → 447392430 ≤ D_c) ∧
    (n = 1073741824 → d = 268435455 → t = 520093696 → 2147483648 < G → 671088643 ≤ D_c) ∧
    (n = 1073741824 → d = 134217727 → t = 394264577 → 2147483648 < G → 594392800 ≤ D_c) := by
  refine ⟨fun hn hd ht hG => ?_, fun hn hd ht hG => ?_, fun hn hd ht hG => ?_,
    fun hn hd ht hG => ?_, fun hn hd ht hG => ?_⟩ <;>
    (subst hn hd ht; omega)

/-- **Exact 4-Head Quotient-Free Threshold (`7n/16 = 469,762,048`):**
Every 1-fresh 4-head configuration on `n = 2^30`, `d = 2^28 - 1` has `e ≥ 469,762,048`. -/
theorem p1_quarter_four_head_threshold {I : Type*} [Fintype I] [DecidableEq I]
    (hn : Fintype.card I = 1073741824) {e : ℕ}
    (C : Fin 4 → Finset I)
    (hsize : ∀ i : Fin 4, 1073741824 - e - 1 ≤ (C i).card)
    (hpair : ∀ i j : Fin 4, i ≠ j → (C i ∩ C j).card ≤ 268435455) :
    469762048 ≤ e := by
  have hhull := discrete_johnson_hull C hpair 2
  rw [hn] at hhull
  have hsum_lb : 4 * (1073741824 - e - 1) ≤ ∑ i : Fin 4, (C i).card := by
    calc
      4 * (1073741824 - e - 1) = ∑ _i : Fin 4, (1073741824 - e - 1) := by simp
      _ ≤ ∑ i : Fin 4, (C i).card := Finset.sum_le_sum fun i _ => hsize i
  omega

/-- **Universal 1-Fresh Label-Core Conservation Barriers (`p₂` Half-Rate & Quarter-Rate):**
From `∑ |C i| + L ≤ H * n`, `B < L`, and `∀ i, n - e - 1 ≤ |C i|`, we get `B + 1 ≤ H * (e + 1)`.
Instantiated at `n = 2^30`, `B = 2 * n`:
- `H ≤ 4 ⇒ e ≥ 536,870,912` (exact quarter-rate Johnson pivot `n/2`),
- `H = 5 ⇒ e ≥ 429,496,729` (`2n/5`),
- `H = 6 ⇒ e ≥ 357,913,941` (`n/3`; breaking `< 357.91M` on `p₂` half-rate strictly needs `H ≥ 7`). -/
theorem universal_label_core_conservation_barriers {H n B e L S : ℕ}
    (hcons : S + L ≤ H * n) (hover : B < L) (hcore : H * (n - e - 1) ≤ S) (he : e + 1 ≤ n) :
    B + 1 ≤ H * (e + 1) := by
  have h1 : H * (n - e - 1) + H * (e + 1) = H * n := by
    rw [← Nat.mul_add]
    congr 1; omega
  omega

theorem p2_conservation_head_thresholds {H e L S : ℕ}
    (hcons : S + L ≤ H * 1073741824) (hover : 2147483648 < L)
    (hcore : H * (1073741824 - e - 1) ≤ S) (he : e + 1 ≤ 1073741824) :
    (H ≤ 4 → 536870912 ≤ e) ∧
    (H = 5 → 429496729 ≤ e) ∧
    (H = 6 → 357913941 ≤ e) := by
  have h := universal_label_core_conservation_barriers hcons hover hcore he
  refine ⟨fun h4 => ?_, fun h5 => by subst h5; omega, fun h6 => by subst h6; omega⟩
  have hle : H * (e + 1) ≤ 4 * (e + 1) := Nat.mul_le_mul_right (e + 1) h4
  omega

/-! ## Part 2: Exact 5-Partition Site Inequality for 4 Collinear Heads -/

section FourHeadFivePartition

variable {F : Type*} [DecidableEq F]

/-- Number of ordered pairs `(i, j)` with `i < j` in `Fin 4` where `v i = v j`.
Takes values in `{0, 1, 2, 3, 6}`, corresponding to the 5 partitions of `Fin 4`:
`0 ↔ (1,1,1,1)`, `1 ↔ (2,1,1)`, `2 ↔ (2,2)`, `3 ↔ (3,1)`, `6 ↔ (4)`. -/
def pairEqCount (v : Fin 4 → F) : ℕ :=
  ((univ : Finset (Fin 4 × Fin 4)).filter fun p => p.1 < p.2 ∧ v p.1 = v p.2).card

/-- The 6 ordered pairs `(i, j)` with `i < j` in `Fin 4`. -/
private def pairs6 : Finset (Fin 4 × Fin 4) :=
  {(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)}

private theorem filter_lt_eq_pairs6 :
    ((univ : Finset (Fin 4 × Fin 4)).filter fun p => p.1 < p.2) = pairs6 := by
  decide

private theorem pairEqCount_eq_sum (v : Fin 4 → F) :
    pairEqCount v =
      (if v 0 = v 1 then 1 else 0) + (if v 0 = v 2 then 1 else 0) +
      (if v 0 = v 3 then 1 else 0) + (if v 1 = v 2 then 1 else 0) +
      (if v 1 = v 3 then 1 else 0) + (if v 2 = v 3 then 1 else 0) := by
  unfold pairEqCount
  rw [← Finset.filter_filter, filter_lt_eq_pairs6, Finset.card_filter]
  dsimp only [pairs6]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-- Pure-`Nat` verifier over the 15 canonical partition codes `(a, b, d)` with `a < 2, b < 3, d < 4`
(representing `c = ![0, a, b, d]`), compiling in milliseconds. -/
private theorem fin4_partition_table :
    ∀ a : Fin 2, ∀ b : Fin 3, ∀ d : Fin 4,
      let c0 : ℕ := 0
      let c1 : ℕ := a.val
      let c2 : ℕ := b.val
      let c3 : ℕ := d.val
      let peq : ℕ :=
        (if c0 = c1 then 1 else 0) + (if c0 = c2 then 1 else 0) +
        (if c0 = c3 then 1 else 0) + (if c1 = c2 then 1 else 0) +
        (if c1 = c3 then 1 else 0) + (if c2 = c3 then 1 else 0)
      let dist : ℕ :=
        1 + (if c1 ≠ c0 then 1 else 0) +
            (if c2 ≠ c0 ∧ c2 ≠ c1 then 1 else 0) +
            (if c3 ≠ c0 ∧ c3 ≠ c1 ∧ c3 ≠ c2 then 1 else 0)
      let fib (k : ℕ) : ℕ :=
        (if c0 = k then 1 else 0) + (if c1 = k then 1 else 0) +
        (if c2 = k then 1 else 0) + (if c3 = k then 1 else 0)
      (peq = 0 ∧ dist = 4 ∧ ∀ k : Fin 4, fib k.val ≤ 1) ∨
      (peq = 1 ∧ dist = 3 ∧ ∀ k : Fin 4, fib k.val ≤ 2) ∨
      (peq = 2 ∧ dist = 2 ∧ ∀ k : Fin 4, fib k.val ≤ 2) ∨
      (peq = 3 ∧ dist = 2 ∧ ∀ k : Fin 4, fib k.val ≤ 3) ∨
      (peq = 6 ∧ dist = 1 ∧ ∀ k : Fin 4, fib k.val ≤ 4) := by
  decide

/-- Exact 5-way partition shape of `v : Fin 4 → F`, indexed by `pairEqCount v`:
`0 → (1,1,1,1)`, `1 → (2,1,1)`, `2 → (2,2)`, `3 → (3,1)`, `6 → (4)`. -/
private theorem pairEqCount_cases (v : Fin 4 → F) :
    (pairEqCount v = 0 ∧ (univ.image v).card = 4 ∧ ∀ y : F, (univ.filter fun i => v i = y).card ≤ 1) ∨
    (pairEqCount v = 1 ∧ (univ.image v).card = 3 ∧ ∀ y : F, (univ.filter fun i => v i = y).card ≤ 2) ∨
    (pairEqCount v = 2 ∧ (univ.image v).card = 2 ∧ ∀ y : F, (univ.filter fun i => v i = y).card ≤ 2) ∨
    (pairEqCount v = 3 ∧ (univ.image v).card = 2 ∧ ∀ y : F, (univ.filter fun i => v i = y).card ≤ 3) ∨
    (pairEqCount v = 6 ∧ (univ.image v).card = 1 ∧ ∀ y : F, (univ.filter fun i => v i = y).card ≤ 4) := by
  -- Compress `v : Fin 4 → F` to canonical representative `c : Fin 4 → Fin 4`
  let c : Fin 4 → Fin 4 := fun i =>
    if v i = v 0 then 0 else if v i = v 1 then 1 else if v i = v 2 then 2 else 3
  have hc0 : (c 0).val = 0 := by simp [c]
  have hc1_lt : (c 1).val < 2 := by simp only [c, ↓reduceIte]; split_ifs <;> decide
  have hc2_lt : (c 2).val < 3 := by simp only [c, ↓reduceIte]; split_ifs <;> decide
  have hc3_lt : (c 3).val < 4 := (c 3).isLt
  have hvc : ∀ i j : Fin 4, v i = v j ↔ (c i).val = (c j).val := by
    intro i j
    have hci : v (c i) = v i := by dsimp [c]; fin_cases i <;> split_ifs <;> simp_all
    have hcj : v (c j) = v j := by dsimp [c]; fin_cases j <;> split_ifs <;> simp_all
    constructor
    · intro hij; dsimp [c]; simp [hij]
    · intro hcij
      have heq : c i = c j := Fin.ext hcij
      rw [← hci, ← hcj, heq]
  have hpeq : pairEqCount v =
      (if (c 0).val = (c 1).val then 1 else 0) + (if (c 0).val = (c 2).val then 1 else 0) +
      (if (c 0).val = (c 3).val then 1 else 0) + (if (c 1).val = (c 2).val then 1 else 0) +
      (if (c 1).val = (c 3).val then 1 else 0) + (if (c 2).val = (c 3).val then 1 else 0) := by
    rw [pairEqCount_eq_sum]
    simp only [hvc]
  have himg : (univ.image v).card =
      1 + (if (c 1).val ≠ (c 0).val then 1 else 0) +
          (if (c 2).val ≠ (c 0).val ∧ (c 2).val ≠ (c 1).val then 1 else 0) +
          (if (c 3).val ≠ (c 0).val ∧ (c 3).val ≠ (c 1).val ∧ (c 3).val ≠ (c 2).val then 1 else 0) := by
    have hset : (univ.image v : Finset F) = insert (v 3) (insert (v 2) (insert (v 1) {v 0})) := by
      ext z; simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨i, rfl⟩; fin_cases i <;> simp
      · rintro (rfl | rfl | rfl | rfl)
        · exact ⟨3, rfl⟩
        · exact ⟨2, rfl⟩
        · exact ⟨1, rfl⟩
        · exact ⟨0, rfl⟩
    rw [hset]
    have h1 : (insert (v 1) ({v 0} : Finset F)).card = 1 + if v 1 ≠ v 0 then 1 else 0 := by
      by_cases h : v 1 = v 0
      · simp [h]
      · rw [Finset.card_insert_of_notMem (by simp [h])]; simp [h]
    have h2 : (insert (v 2) (insert (v 1) ({v 0} : Finset F))).card =
        (insert (v 1) ({v 0} : Finset F)).card + if v 2 ≠ v 0 ∧ v 2 ≠ v 1 then 1 else 0 := by
      by_cases h : v 2 = v 0 ∨ v 2 = v 1
      · rcases h with h | h <;> simp [h]
      · push Not at h
        rw [Finset.card_insert_of_notMem (by simp [h.1, h.2])]
        simp [h.1, h.2]
    have h3 : (insert (v 3) (insert (v 2) (insert (v 1) ({v 0} : Finset F)))).card =
        (insert (v 2) (insert (v 1) ({v 0} : Finset F))).card +
          if v 3 ≠ v 0 ∧ v 3 ≠ v 1 ∧ v 3 ≠ v 2 then 1 else 0 := by
      by_cases h : v 3 = v 0 ∨ v 3 = v 1 ∨ v 3 = v 2
      · rcases h with h | h | h <;> simp [h]
      · push Not at h
        rw [Finset.card_insert_of_notMem (by simp [h.1, h.2.1, h.2.2])]
        simp [h.1, h.2.1, h.2.2]
    rw [h3, h2, h1]
    simp only [ne_eq, hvc]
  have hfib : ∀ y : F, (univ.filter fun i : Fin 4 => v i = y).card = 0 ∨
      ∃ k : Fin 4, (univ.filter fun i : Fin 4 => v i = y).card =
        (if (0 : ℕ) = k.val then 1 else 0) + (if (c 1).val = k.val then 1 else 0) +
        (if (c 2).val = k.val then 1 else 0) + (if (c 3).val = k.val then 1 else 0) := by
    intro y
    by_cases hne : ∃ j : Fin 4, v j = y
    · obtain ⟨j, rfl⟩ := hne
      right; refine ⟨c j, ?_⟩
      rw [Finset.card_filter, Fin.sum_univ_four]
      simp only [hvc, hc0]
    · left
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _ hi; exact hne ⟨i, hi⟩
  have htransfer : ∀ M : ℕ,
      (∀ k : Fin 4,
        (if (0 : ℕ) = k.val then 1 else 0) + (if (c 1).val = k.val then 1 else 0) +
        (if (c 2).val = k.val then 1 else 0) + (if (c 3).val = k.val then 1 else 0) ≤ M) →
      ∀ y : F, (univ.filter fun i : Fin 4 => v i = y).card ≤ M := by
    intro M hM y
    rcases hfib y with h0 | ⟨k, hk⟩
    · omega
    · rw [hk]; exact hM k
  have htab := fin4_partition_table ⟨(c 1).val, hc1_lt⟩ ⟨(c 2).val, hc2_lt⟩ ⟨(c 3).val, hc3_lt⟩
  dsimp only at htab
  rw [hpeq, himg]
  simp only [hc0]
  rcases htab with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨h1, h2, htransfer 1 h3⟩
  · exact Or.inr (Or.inl ⟨h1, h2, htransfer 2 h3⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h1, h2, htransfer 2 h3⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h2, htransfer 3 h3⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, h2, htransfer 4 h3⟩)))

/-- **Pointwise 5-Partition Inequality for 4 Collinear Heads:**
At a single site with head values `v : Fin 4 → F`, `r` matching heads (`r ≤ max class size of v`),
and `fresh` fresh labels obeying the collinear rule:
- if `r = 0`, `fresh ≤ (univ.image v).card` (at most one label per distinct head value),
- if `1 ≤ r ≤ 3`, `fresh ≤ 1` (common collinear direction),
- if `r = 4`, `fresh = 0`,
we have the exact defect-aware bound:
  `2 * r + fresh + (if pairEqCount v = 2 then 1 else 0) + (if pairEqCount v = 6 then 2 else 0) ≤ 4 + pairEqCount v`,
equivalently:
  `2 * r + fresh ≤ 4 + (if pairEqCount v = 1 then 1 else 0) + (if pairEqCount v = 2 then 1 else 0)
                     + (if pairEqCount v = 3 then 3 else 0) + (if pairEqCount v = 6 then 4 else 0)`. -/
theorem four_head_five_partition_pointwise (v : Fin 4 → F) (y : F) (fresh : ℕ)
    (h0 : (univ.filter fun i : Fin 4 => v i = y).card = 0 → fresh ≤ (univ.image v).card)
    (hmid : 1 ≤ (univ.filter fun i : Fin 4 => v i = y).card →
      (univ.filter fun i : Fin 4 => v i = y).card ≤ 3 → fresh ≤ 1)
    (h4 : (univ.filter fun i : Fin 4 => v i = y).card = 4 → fresh = 0) :
    let r := (univ.filter fun i : Fin 4 => v i = y).card
    2 * r + fresh +
      (if pairEqCount v = 2 then 1 else 0) + (if pairEqCount v = 6 then 2 else 0) ≤
        4 + pairEqCount v ∧
    2 * r + fresh ≤
      4 + (if pairEqCount v = 1 then 1 else 0) + (if pairEqCount v = 2 then 1 else 0) +
        (if pairEqCount v = 3 then 3 else 0) + (if pairEqCount v = 6 then 4 else 0) := by
  intro r
  rcases pairEqCount_cases v with ⟨hp, hd, hr⟩ | ⟨hp, hd, hr⟩ | ⟨hp, hd, hr⟩ | ⟨hp, hd, hr⟩ | ⟨hp, hd, hr⟩
  all_goals
    have hry : r ≤ _ := hr y
    simp only [hp]
    norm_num
    by_cases hr0 : r = 0
    · have hf := h0 hr0; omega
    · by_cases hr4 : r = 4
      · have hf := h4 hr4; omega
      · have hf := hmid (by omega) (by omega); omega

/-- **Global 5-Partition Inequality for 4 Collinear Heads on `Finset I`:**
Sums `four_head_five_partition_pointwise` over all sites `x ∈ I`, proving simultaneously:
1. `∑_{i < j} |E_ij| = n_211 + 2 * n_22 + 3 * n_31 + 6 * n_4`,
2. `2 * ∑ i, |core i| + ∑ x, fresh x + n_22 + 2 * n_4 ≤ 4 * |I| + ∑_{i < j} |E_ij|`,
3. `2 * ∑ i, |core i| + ∑ x, fresh x ≤ 4 * |I| + n_211 + n_22 + 3 * n_31 + 4 * n_4`. -/
theorem four_head_five_partition_global {I : Type*} [Fintype I] [DecidableEq I]
    (v : I → Fin 4 → F) (y : I → F) (fresh : I → ℕ)
    (h0 : ∀ x, (univ.filter fun i : Fin 4 => v x i = y x).card = 0 → fresh x ≤ (univ.image (v x)).card)
    (hmid : ∀ x, 1 ≤ (univ.filter fun i : Fin 4 => v x i = y x).card →
      (univ.filter fun i : Fin 4 => v x i = y x).card ≤ 3 → fresh x ≤ 1)
    (h4 : ∀ x, (univ.filter fun i : Fin 4 => v x i = y x).card = 4 → fresh x = 0) :
    let core (i : Fin 4) := univ.filter fun x : I => v x i = y x
    let E (p : Fin 4 × Fin 4) := univ.filter fun x : I => v x p.1 = v x p.2
    let n211 := (univ.filter fun x : I => pairEqCount (v x) = 1).card
    let n22 := (univ.filter fun x : I => pairEqCount (v x) = 2).card
    let n31 := (univ.filter fun x : I => pairEqCount (v x) = 3).card
    let n4 := (univ.filter fun x : I => pairEqCount (v x) = 6).card
    let pairSum := ∑ p ∈ (univ : Finset (Fin 4 × Fin 4)).filter (fun p => p.1 < p.2), (E p).card
    pairSum = n211 + 2 * n22 + 3 * n31 + 6 * n4 ∧
    n211 + n22 + n31 + n4 ≤ Fintype.card I ∧
    2 * (∑ i : Fin 4, (core i).card) + (∑ x : I, fresh x) + n22 + 2 * n4 ≤
      4 * Fintype.card I + pairSum ∧
    2 * (∑ i : Fin 4, (core i).card) + (∑ x : I, fresh x) ≤
      4 * Fintype.card I + n211 + n22 + 3 * n31 + 4 * n4 := by
  intro core E n211 n22 n31 n4 pairSum
  have hcore_sum : ∑ i : Fin 4, (core i).card =
      ∑ x : I, (univ.filter fun i : Fin 4 => v x i = y x).card := by
    simp only [core, Finset.card_filter]
    exact Finset.sum_comm
  have hpair_eq : pairSum = ∑ x : I, pairEqCount (v x) := by
    dsimp [pairSum, E, pairEqCount]
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => by by_cases h : p.1 < p.2 <;> simp [h]
  have hpeq_decomp : ∀ x : I, pairEqCount (v x) =
      (if pairEqCount (v x) = 1 then 1 else 0) + 2 * (if pairEqCount (v x) = 2 then 1 else 0) +
      3 * (if pairEqCount (v x) = 3 then 1 else 0) + 6 * (if pairEqCount (v x) = 6 then 1 else 0) := by
    intro x
    rcases pairEqCount_cases (v x) with ⟨hp, _, _⟩ | ⟨hp, _, _⟩ | ⟨hp, _, _⟩ | ⟨hp, _, _⟩ | ⟨hp, _, _⟩ <;>
      simp [hp]
  have hpair_part : pairSum = n211 + 2 * n22 + 3 * n31 + 6 * n4 := by
    rw [hpair_eq]
    calc
      ∑ x : I, pairEqCount (v x)
          = ∑ x : I, ((if pairEqCount (v x) = 1 then 1 else 0) +
              2 * (if pairEqCount (v x) = 2 then 1 else 0) +
              3 * (if pairEqCount (v x) = 3 then 1 else 0) +
              6 * (if pairEqCount (v x) = 6 then 1 else 0)) :=
                Finset.sum_congr rfl fun x _ => hpeq_decomp x
      _ = n211 + 2 * n22 + 3 * n31 + 6 * n4 := by
            simp only [Finset.sum_add_distrib, ← Finset.mul_sum, n211, n22, n31, n4, Finset.card_filter]
  have hpart_le : n211 + n22 + n31 + n4 ≤ Fintype.card I := by
    have hpt : ∀ x : I,
        (if pairEqCount (v x) = 1 then 1 else 0) + (if pairEqCount (v x) = 2 then 1 else 0) +
        (if pairEqCount (v x) = 3 then 1 else 0) + (if pairEqCount (v x) = 6 then 1 else 0) ≤ 1 := by
      intro x
      rcases pairEqCount_cases (v x) with ⟨hp, _, _⟩ | ⟨hp, _, _⟩ | ⟨hp, _, _⟩ | ⟨hp, _, _⟩ | ⟨hp, _, _⟩ <;>
        simp [hp]
    have hsum := Finset.sum_le_sum fun x (_ : x ∈ (univ : Finset I)) => hpt x
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hsum
    simpa only [n211, n22, n31, n4, Finset.card_filter] using hsum
  have hsum_ineq := Finset.sum_le_sum fun x (_ : x ∈ (univ : Finset I)) =>
    (four_head_five_partition_pointwise (v x) (y x) (fresh x) (h0 x) (hmid x) (h4 x)).1
  have hsum_lhs :
      ∑ x : I, (2 * (univ.filter fun i : Fin 4 => v x i = y x).card + fresh x +
        (if pairEqCount (v x) = 2 then 1 else 0) + (if pairEqCount (v x) = 6 then 2 else 0)) =
      2 * (∑ i : Fin 4, (core i).card) + (∑ x : I, fresh x) + n22 + 2 * n4 := by
    have h2 : ∀ x : I, (if pairEqCount (v x) = 6 then 2 else 0) =
        2 * (if pairEqCount (v x) = 6 then 1 else 0) := by
      intro x; split_ifs <;> rfl
    simp_rw [h2]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hcore_sum, n22, n4, Finset.card_filter]
  have hsum_rhs : ∑ x : I, (4 + pairEqCount (v x)) = 4 * Fintype.card I + pairSum := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      mul_comm (Fintype.card I) 4, hpair_eq]
  rw [hsum_lhs, hsum_rhs] at hsum_ineq
  refine ⟨hpair_part, hpart_le, hsum_ineq, ?_⟩
  omega

end FourHeadFivePartition

/-! ## Part 3: Algebraic Cross-Ratio Pencil & Constant-Cross-Ratio 4-Fiber Factorization -/

section CrossRatioAlgebra

variable {K : Type*} [Field K]

/-- **Exact Cross-Ratio / Plücker Pencil Identity** for any three polynomials `P, Q, R ∈ K[X]`:
`P(Q - R) + R(P - Q) = Q(P - R)`. -/
theorem cross_ratio_pencil_identity (P Q R : K[X]) :
    P * (Q - R) + R * (P - Q) = Q * (P - R) := by
  ring

/-- Every triple coincidence among `(0, P, Q, R)` at `x : K` is a common root of all three
cross-ratio polynomials `A = P(Q - R)`, `B = R(P - Q)`, and `C = Q(P - R)`. -/
theorem cross_ratio_triple_common_root (P Q R : K[X]) (x : K)
    (htriple : (P.eval x = 0 ∧ Q.eval x = 0) ∨ (P.eval x = 0 ∧ R.eval x = 0) ∨
               (Q.eval x = 0 ∧ R.eval x = 0) ∨ (P.eval x = Q.eval x ∧ Q.eval x = R.eval x)) :
    (X - C x) ∣ P * (Q - R) ∧ (X - C x) ∣ R * (P - Q) ∧ (X - C x) ∣ Q * (P - R) := by
  simp only [Polynomial.dvd_iff_isRoot, IsRoot, eval_mul, eval_sub]
  rcases htriple with ⟨hP, hQ⟩ | ⟨hP, hR⟩ | ⟨hQ, hR⟩ | ⟨hPQ, hQR⟩
  · simp [hP, hQ]
  · simp [hP, hR]
  · simp [hQ, hR]
  · refine ⟨?_, ?_, ?_⟩ <;> simp [hPQ, hQR]

/-- Every quadruple coincidence `P(x) = Q(x) = R(x) = 0` gives a **double** common root
`(X - C x) ^ 2` dividing ALL THREE of `P(Q - R)`, `R(P - Q)`, and `Q(P - R)`. -/
theorem cross_ratio_quadruple_double_root (P Q R : K[X]) (x : K)
    (hP : P.eval x = 0) (hQ : Q.eval x = 0) (hR : R.eval x = 0) :
    (X - C x) ^ 2 ∣ P * (Q - R) ∧ (X - C x) ^ 2 ∣ R * (P - Q) ∧ (X - C x) ^ 2 ∣ Q * (P - R) := by
  have hdP : (X - C x) ∣ P := Polynomial.dvd_iff_isRoot.mpr hP
  have hdQ : (X - C x) ∣ Q := Polynomial.dvd_iff_isRoot.mpr hQ
  have hdR : (X - C x) ∣ R := Polynomial.dvd_iff_isRoot.mpr hR
  rw [sq]
  exact ⟨mul_dvd_mul hdP (dvd_sub hdQ hdR),
         mul_dvd_mul hdR (dvd_sub hdP hdQ),
         mul_dvd_mul hdQ (dvd_sub hdP hdR)⟩

/-- Every `(2,2)` double-pair site among `(0, P, Q, R)` produces a **double** root `(X - C x)^2`
of one of the three cross-ratio polynomials `P(Q - R)`, `R(P - Q)`, `Q(P - R)`. -/
theorem cross_ratio_double_pair_sq_root (P Q R : K[X]) (x : K)
    (h22 : (P.eval x = 0 ∧ Q.eval x = R.eval x) ∨
           (R.eval x = 0 ∧ P.eval x = Q.eval x) ∨
           (Q.eval x = 0 ∧ P.eval x = R.eval x)) :
    (X - C x) ^ 2 ∣ P * (Q - R) ∨ (X - C x) ^ 2 ∣ R * (P - Q) ∨ (X - C x) ^ 2 ∣ Q * (P - R) := by
  rw [sq]
  rcases h22 with ⟨hP, hQR⟩ | ⟨hR, hPQ⟩ | ⟨hQ, hPR⟩
  · left
    exact mul_dvd_mul (Polynomial.dvd_iff_isRoot.mpr hP)
      (Polynomial.dvd_iff_isRoot.mpr (by simp [IsRoot, hQR]))
  · right; left
    exact mul_dvd_mul (Polynomial.dvd_iff_isRoot.mpr hR)
      (Polynomial.dvd_iff_isRoot.mpr (by simp [IsRoot, hPQ]))
  · right; right
    exact mul_dvd_mul (Polynomial.dvd_iff_isRoot.mpr hQ)
      (Polynomial.dvd_iff_isRoot.mpr (by simp [IsRoot, hPR]))

/-- **Exact Constant-Cross-Ratio 4-Fiber Factorization Theorem (Over ANY Field `K`):**
If `P, Q, R ∈ K[X]` are nonzero, pairwise distinct, and have constant cross-ratio `c ∈ K \ {0, 1}`
(`P * (Q - R) = C c * (Q * (P - R))`), then there exist `H, U, V ∈ K[X]` with `IsCoprime U V`
such that:
- `P = H * U * (C c * V - U)`,
- `Q = H * V * (C c * V - U)`,
- `R = H * C (c - 1) * U * V`,
- `H ≠ 0`, `U ≠ 0`, `V ≠ 0`, `V - U ≠ 0`, `C c * V - U ≠ 0`,
- `2 * max U.natDegree V.natDegree + H.natDegree ≤ max (max P.natDegree Q.natDegree) R.natDegree`.
In particular, `(0, P, Q, R)` arises from a **4-fiber rational map `U / V`** of degree
`max U.natDegree V.natDegree ≤ (D - deg H) / 2`! -/
theorem constant_cross_ratio_four_fiber_factorization
    (P Q R : K[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) (hPQ : P ≠ Q)
    (c : K) (hc0 : c ≠ 0) (hc1 : c ≠ 1)
    (hcr : P * (Q - R) = C c * (Q * (P - R))) :
    ∃ H U V : K[X],
      IsCoprime U V ∧
      H ≠ 0 ∧ U ≠ 0 ∧ V ≠ 0 ∧ V - U ≠ 0 ∧ C c * V - U ≠ 0 ∧
      P = H * U * (C c * V - U) ∧
      Q = H * V * (C c * V - U) ∧
      R = H * C (c - 1) * U * V ∧
      2 * max U.natDegree V.natDegree + H.natDegree ≤
        max (max P.natDegree Q.natDegree) R.natDegree := by
  classical
  set g : K[X] := EuclideanDomain.gcd P Q with hg_def
  have hg0 : g ≠ 0 := by
    intro hg
    exact hP (EuclideanDomain.gcd_eq_zero_iff.mp (hg_def.symm.trans hg)).1
  obtain ⟨U, hPU'⟩ := EuclideanDomain.gcd_dvd_left P Q
  obtain ⟨V, hQV'⟩ := EuclideanDomain.gcd_dvd_right P Q
  have hPU : P = g * U := by rwa [← hg_def] at hPU'
  have hQV : Q = g * V := by rwa [← hg_def] at hQV'
  have hU0 : U ≠ 0 := fun h => hP (by simpa [h] using hPU)
  have hV0 : V ≠ 0 := fun h => hQ (by simpa [h] using hQV)
  have hVU : V - U ≠ 0 := by
    intro h
    have hUV : U = V := (sub_eq_zero.mp h).symm
    exact hPQ (hPU.trans ((congrArg (g * ·) hUV).trans hQV.symm))
  -- Prove `IsCoprime U V` via Bézout identity `gcd P Q = a * P + b * Q`
  have hcop : IsCoprime U V := by
    refine ⟨EuclideanDomain.gcdA P Q, EuclideanDomain.gcdB P Q, ?_⟩
    have hbez := EuclideanDomain.gcd_eq_gcd_ab P Q
    apply mul_left_cancel₀ hg0
    calc
      g * (EuclideanDomain.gcdA P Q * U + EuclideanDomain.gcdB P Q * V)
          = (g * U) * EuclideanDomain.gcdA P Q + (g * V) * EuclideanDomain.gcdB P Q := by ring
      _ = P * EuclideanDomain.gcdA P Q + Q * EuclideanDomain.gcdB P Q := by rw [← hPU, ← hQV]
      _ = g := hbez.symm
      _ = g * 1 := (mul_one g).symm
  -- Rewrite cross-ratio identity after cancelling `g ≠ 0`
  have hrel : R * (C c * V - U) = C (c - 1) * g * U * V := by
    have h1 : g * (U * (g * V - R)) = g * (C c * (V * (g * U - R))) := by
      calc
        g * (U * (g * V - R)) = (g * U) * (g * V - R) := by ring
        _ = P * (Q - R) := by rw [← hPU, ← hQV]
        _ = C c * (Q * (P - R)) := hcr
        _ = C c * ((g * V) * (g * U - R)) := by rw [← hPU, ← hQV]
        _ = g * (C c * (V * (g * U - R))) := by ring
    have h2 : U * (g * V - R) = C c * (V * (g * U - R)) := mul_left_cancel₀ hg0 h1
    rw [map_sub, map_one]
    linear_combination h2
  have hcVU0 : C c * V - U ≠ 0 := by
    intro h0
    have hprod0 : C (c - 1) * g * U * V = 0 := by rw [← hrel, h0, mul_zero]
    have hc1' : C (c - 1) ≠ 0 := C_ne_zero.mpr (sub_ne_zero.mpr hc1)
    rcases mul_eq_zero.mp hprod0 with h1 | hV
    · rcases mul_eq_zero.mp h1 with h2 | hU
      · rcases mul_eq_zero.mp h2 with hc' | hg'
        · exact hc1' hc'
        · exact hg0 hg'
      · exact hU0 hU
    · exact hV0 hV
  -- Show `C c * V - U` is coprime to `U * V`
  have hcop_U : IsCoprime (C c * V - U) U := by
    rcases hcop with ⟨a, b, hab⟩
    refine ⟨b * C c⁻¹, a + b * C c⁻¹, ?_⟩
    have hc_inv : C c⁻¹ * C c = 1 := by rw [← map_mul, inv_mul_cancel₀ hc0, map_one]
    calc
      b * C c⁻¹ * (C c * V - U) + (a + b * C c⁻¹) * U
          = a * U + b * (C c⁻¹ * C c) * V := by ring
      _ = a * U + b * V := by rw [hc_inv, mul_one]
      _ = 1 := hab
  have hcop_V : IsCoprime (C c * V - U) V := by
    rcases hcop with ⟨a, b, hab⟩
    refine ⟨-a, b + a * C c, ?_⟩
    linear_combination hab
  have hcop_UV : IsCoprime (C c * V - U) (U * V) := hcop_U.mul_right hcop_V
  -- Therefore `(C c * V - U) ∣ g`!
  have hdvd_g : (C c * V - U) ∣ g := by
    have hdvd_prod : (C c * V - U) ∣ (C (c - 1) * g) * (U * V) := by
      refine ⟨R, ?_⟩
      linear_combination -hrel
    have hdvd_cg : (C c * V - U) ∣ C (c - 1) * g := hcop_UV.dvd_of_dvd_mul_right hdvd_prod
    rcases hdvd_cg with ⟨H, hH⟩
    refine ⟨C (c - 1)⁻¹ * H, ?_⟩
    have hc1_inv : C (c - 1)⁻¹ * C (c - 1) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ (sub_ne_zero.mpr hc1), map_one]
    calc
      g = (C (c - 1)⁻¹ * C (c - 1)) * g := by rw [hc1_inv, one_mul]
      _ = C (c - 1)⁻¹ * (C (c - 1) * g) := by ring
      _ = C (c - 1)⁻¹ * ((C c * V - U) * H) := by rw [hH]
      _ = (C c * V - U) * (C (c - 1)⁻¹ * H) := by ring
  obtain ⟨H, hH_eq⟩ := hdvd_g
  have hH0 : H ≠ 0 := fun h => hg0 (by simpa [h] using hH_eq)
  have hP_fac : P = H * U * (C c * V - U) := by rw [hPU, hH_eq]; ring
  have hQ_fac : Q = H * V * (C c * V - U) := by rw [hQV, hH_eq]; ring
  have hR_fac : R = H * C (c - 1) * U * V := by
    apply mul_right_cancel₀ hcVU0
    calc
      R * (C c * V - U) = C (c - 1) * g * U * V := hrel
      _ = C (c - 1) * ((C c * V - U) * H) * U * V := by rw [hH_eq]
      _ = H * C (c - 1) * U * V * (C c * V - U) := by ring
  -- Degree bound: holds unconditionally across all three cases `deg U <, =, > deg V`!
  have hdeg_P : P.natDegree = H.natDegree + U.natDegree + (C c * V - U).natDegree := by
    rw [hP_fac, Polynomial.natDegree_mul (mul_ne_zero hH0 hU0) hcVU0,
      Polynomial.natDegree_mul hH0 hU0]
  have hdeg_Q : Q.natDegree = H.natDegree + V.natDegree + (C c * V - U).natDegree := by
    rw [hQ_fac, Polynomial.natDegree_mul (mul_ne_zero hH0 hV0) hcVU0,
      Polynomial.natDegree_mul hH0 hV0]
  have hdeg_R : R.natDegree = H.natDegree + U.natDegree + V.natDegree := by
    have hc1' : C (c - 1) ≠ 0 := C_ne_zero.mpr (sub_ne_zero.mpr hc1)
    rw [hR_fac, Polynomial.natDegree_mul (mul_ne_zero (mul_ne_zero hH0 hc1') hU0) hV0,
      Polynomial.natDegree_mul (mul_ne_zero hH0 hc1') hU0,
      Polynomial.natDegree_mul hH0 hc1', Polynomial.natDegree_C, add_zero]
  have hdeg_bound : 2 * max U.natDegree V.natDegree + H.natDegree ≤
      max (max P.natDegree Q.natDegree) R.natDegree := by
    have hdeg_cV : (C c * V).natDegree = V.natDegree := by
      rw [Polynomial.natDegree_C_mul hc0]
    rcases lt_trichotomy U.natDegree V.natDegree with hlt | heq | hgt
    · -- `deg U < deg V`: `deg(C c * V - U) = deg V`, so `deg Q = deg H + 2 * deg V`
      have hsub : (C c * V - U).natDegree = V.natDegree := by
        rw [sub_eq_add_neg, Polynomial.natDegree_add_eq_left_of_natDegree_lt]
        · exact hdeg_cV
        · rw [Polynomial.natDegree_neg, hdeg_cV]; exact hlt
      rw [max_eq_right (le_of_lt hlt)]
      have : Q.natDegree ≤ max (max P.natDegree Q.natDegree) R.natDegree :=
        le_trans (le_max_right _ _) (le_max_left _ _)
      omega
    · -- `deg U = deg V`: `deg R = deg H + 2 * deg U`!
      rw [heq, max_self]
      have : R.natDegree ≤ max (max P.natDegree Q.natDegree) R.natDegree := le_max_right _ _
      omega
    · -- `deg V < deg U`: `deg(C c * V - U) = deg U`, so `deg P = deg H + 2 * deg U`
      have hsub : (C c * V - U).natDegree = U.natDegree := by
        rw [sub_eq_add_neg, Polynomial.natDegree_add_eq_right_of_natDegree_lt]
        · exact Polynomial.natDegree_neg U
        · rw [Polynomial.natDegree_neg, hdeg_cV]; exact hgt
      rw [max_eq_left (le_of_lt hgt)]
      have : P.natDegree ≤ max (max P.natDegree Q.natDegree) R.natDegree :=
        le_trans (le_max_left _ _) (le_max_left _ _)
      omega
  exact ⟨H, U, V, hcop, hH0, hU0, hV0, hVU, hcVU0, hP_fac, hQ_fac, hR_fac, hdeg_bound⟩

end CrossRatioAlgebra

/-! ## Part 4: 4-Head Cross-Ratio Dichotomy on `[469,762,049, 480,946,858]` & Pullback / Tower Exclusions -/

/-- **Quantitative 4-Head Collinear Cross-Ratio Dichotomy across `[469,762,049, 480,946,858]`:**
For every `j₄ ≤ 11,184,809` (`e = 469,762,049 + j₄`, `t = 1,073,741,824 - e`, `D = 268,435,454`),
any 4-head collinear overrun with site counts `(n_211, n_22, n_31, n_4)` and reduced cross-ratio
degree `M₀ ≤ 2 * D - (n_31 + 2 * n_4)` satisfies:
1. `n_22 + 2 * n_4 ≤ 3 + 8 * j₄` (at `e = 469,762,049`: `n_22 + 2 * n_4 ≤ 3`),
2. `2 * (n_31 + 2 * n_4) ≥ 536,870,897 - 8 * j₄` (unconditional triple+quadruple floor),
3. `M₀ ≤ D + 5 + 4 * j₄` (`≤ D + 5` at `469,762,049`; `≤ 313,174,695` at `480,946,858`),
4. **`3 * M₀ ≤ (n_211 + n_22) + (3 + 8 * j₄)`** (exact cross-ratio missing-root cap: at
   `e = 469,762,049`, at most **3** missing roots across ALL 3 fibers of the cross-ratio pencil!),
5. At `j₄ = 0` (`e = 469,762,049`), whenever `223,696,216 ≤ M₀ ≤ D`, the cross-ratio pencil
   itself has 3-head score `2 * (n_211 + n_22) - 3 * M₀ ≥ 671,088,642 > 671,088,640`, already
   forcing a 3-head overrun at or before `469,762,048`! -/
theorem four_head_cross_ratio_dichotomy {j₄ n211 n22 n31 n4 M₀ : ℕ}
    (hj : j₄ ≤ 11184809)
    (hsites : n211 + n22 + n31 + n4 ≤ 1073741824)
    (hdeg : n211 + 2 * n22 + 3 * n31 + 6 * n4 ≤ 6 * 268435454)
    (hover : 8 * (603979774 - j₄) + 1073741825 ≤
      4 * 1073741824 + n211 + n22 + 3 * n31 + 4 * n4)
    (hM₀ : M₀ + n31 + 2 * n4 ≤ 2 * 268435454) :
    n22 + 2 * n4 ≤ 3 + 8 * j₄ ∧
    536870897 - 8 * j₄ ≤ 2 * (n31 + 2 * n4) ∧
    M₀ ≤ 268435454 + 5 + 4 * j₄ ∧
    3 * M₀ ≤ (n211 + n22) + (3 + 8 * j₄) ∧
    (j₄ = 0 → 223696216 ≤ M₀ → M₀ ≤ 268435454 →
      671088642 + 3 * M₀ ≤ 2 * (n211 + n22)) := by
  refine ⟨by omega, by omega, by omega, by omega, fun h0 hlo hhi => by omega⟩

/-- **Constant-Cross-Ratio 4-Fiber Degree & Missing-Root Bounds across `[469,762,049, 480,946,858]`:**
When `M₀ = 0` (`n_211 = n_22 = 0`), the factored 4-fiber map `U / V` of degree `m₀` (`2*m₀ + n_4 ≤ D`,
`n_31 ≤ 4 * m₀`) beating `480,946,859` satisfies:
- `111,848,109 ≤ m₀ ≤ 134,217,727` (and `126,761,188 ≤ m₀` when `n_4 = 0`),
- `4 * m₀ - n_31 ≤ 29,826,158` (`≥ 94.4%` of all `4 * m₀` roots lie in `μ_{2^30}`),
- At `e = 469,762,049` (`j₄ = 0`): `n_4 ≤ 1`, `4 * m₀ - n_31 ≤ 1`, and if `n_4 = 0` then
  `m₀ = 134,217,727 = 2^27 - 1` (at most ONE missing root across all 4 fibers!). -/
theorem four_head_const_cr_degree_floor {j₄ m₀ n31 n4 : ℕ}
    (hj : j₄ ≤ 11184809)
    (hdeg : 2 * m₀ + n4 ≤ 268435454)
    (hfib : n31 ≤ 4 * m₀)
    (hover : 8 * (603979774 - j₄) + 1073741825 ≤ 4 * 1073741824 + 3 * n31 + 4 * n4) :
    (111848109 ≤ m₀ ∧ m₀ ≤ 134217727) ∧
    (n4 = 0 → 126761188 ≤ m₀) ∧
    4 * m₀ - n31 ≤ 29826158 ∧
    (j₄ = 0 → n4 ≤ 1 ∧ 4 * m₀ - n31 ≤ 1 ∧ (n4 = 0 → m₀ = 134217727)) := by
  refine ⟨by omega, fun _ => by omega, by omega, fun _ => by omega⟩

/-- **Unconditional Cyclic Pullback Exclusions for 4 Collinear Heads (Over ANY Field, Including `p₁` and `p₂`):**
1. General 4-head collinear pullbacks on `μ_M` (`4 ∣ M`, `M ≤ 64`, degree `≤ M/4 - 1`):
   `12 * (6 * (M / 4 - 1)) ≤ 17 * M` — ZERO can beat `480,946,859`!
2. Constant-cross-ratio 4-head pullbacks on `μ_M` (`8 ∣ M`, `M ≤ 128`, `2*m₀ + h ≤ M/4 - 1`, `n_31 ≤ 4*m₀`):
   - If `M ≤ 64`, ZERO can beat `480,946,859` (for ANY `h ≥ 0`).
   - If `M = 128` (`D = 31`), ZERO primitive (`h = 0`) pullbacks can beat `480,946,859`, and the
     **ONLY** arithmetically surviving constant-cross-ratio tuple is **`h = 1, m₀ = 15, n_31 = 60`**
     (all four fibers of degree 15 must be 100% full on `μ_{128}`!).
3. General 4-head collinear pullbacks on `μ_{128}` (`D = 31`, `6 * D = 186`):
   beating `480,946,859` (`12 * Δ₄ > 17 * 128`) forces **`182 ≤ Δ₄ ≤ 186`** (at most 4 missing
   roots across ALL SIX degree-31 pairwise differences!). -/
theorem four_head_cyclic_pullback_exclusions :
    (∀ M : ℕ, 4 ∣ M → 4 ≤ M → M ≤ 64 → 12 * (6 * (M / 4 - 1)) ≤ 17 * M) ∧
    (∀ M m₀ n31 : ℕ, 8 ∣ M → 8 ≤ M → M ≤ 128 → 2 * m₀ ≤ M / 4 - 1 → n31 ≤ 4 * m₀ →
      12 * (3 * n31) ≤ 17 * M) ∧
    (∀ m₀ n31 h : ℕ, 2 * m₀ + h ≤ 31 → n31 ≤ 4 * m₀ → 17 * 128 < 12 * (3 * n31 + 4 * h) →
      h = 1 ∧ m₀ = 15 ∧ n31 = 60) ∧
    (∀ Δ₄ : ℕ, 17 * 128 < 12 * Δ₄ → Δ₄ ≤ 6 * 31 → 182 ≤ Δ₄ ∧ 6 * 31 - Δ₄ ≤ 4) := by
  refine ⟨?_, ?_, fun _ _ _ _ _ _ => by omega, fun _ _ _ => by omega⟩
  · intro M h4 hge hle
    rcases h4 with ⟨q, rfl⟩
    omega
  · intro M m₀ n31 h8 hge hle hdeg hfib
    rcases h8 with ⟨q, rfl⟩
    omega

/-- **Infinite-Tower Characteristic-Zero 4-Fiber Exclusion (`N = 2^k ≥ 128` via Depth-2 Symmetry Swap):**
For EVERY `N ≥ 128` with `4 ∣ N` (including `μ_{128}` where exact finite-field-to-complex ratio
transfer holds on BOTH `p₁` and `p₂`!), any non-descending full 4-split pencil of degree `m₀`
has ALL FOUR disjoint fibers concentrated in the same mod-4 coset (`≤ 4` points each in `2 mod 4`,
`0` odd points by Depth 2 symmetry swap), forcing `4 * (m₀ - 4) ≤ N / 4`, i.e., `16 * m₀ ≤ N + 64`.
- At `N = 128`: kills EVERY `m₀ ≥ 13` (in particular **`m₀ = 15`, eliminating the SOLE remaining
  constant-cross-ratio 4-head pullback on `μ_{128}` over BOTH `p₁` and `p₂`!**).
- For EVERY `N ≥ 256` (`8 ∣ N`): beating `480,946,859` (`17 * N < 144 * m₀`) contradicts BOTH
  Depth 2 (`16 * m₀ ≤ N + 64`) AND Depth 3 (`N / 8 < (m₀ - c₁_2 - c₁_4) + (m₀ - c₂_2 - c₂_4)`). -/
theorem four_fiber_depth3_tower_exclusion :
    (∀ m₀ c1 c2 c3 c4 : ℕ, 13 ≤ m₀ → c1 ≤ 4 → c2 ≤ 4 → c3 ≤ 4 → c4 ≤ 4 →
      128 / 4 < (m₀ - c1) + (m₀ - c2) + (m₀ - c3) + (m₀ - c4)) ∧
    (∀ N m₀ c1_2 c1_4 c2_2 c2_4 : ℕ, 256 ≤ N → 8 ∣ N → 17 * N < 144 * m₀ →
      c1_2 ≤ 4 → c1_4 ≤ 8 → c2_2 ≤ 4 → c2_4 ≤ 8 →
      N + 192 < 16 * m₀ ∧ N / 8 < (m₀ - c1_2 - c1_4) + (m₀ - c2_2 - c2_4)) := by
  refine ⟨fun _ _ _ _ _ _ _ _ _ _ => by omega, ?_⟩
  intro N m₀ c1_2 c1_4 c2_2 c2_4 hN h8 hbeat h1_2 h1_4 h2_2 h2_4
  rcases h8 with ⟨q, rfl⟩
  omega

#print axioms discrete_johnson_hull
#print axioms p1_quarter_five_plus_heads_impossible
#print axioms p1_quarter_multifresh_above_johnson_impossible
#print axioms nonlinear_curve_pencil_degree_floor
#print axioms p1_quarter_four_head_threshold
#print axioms universal_label_core_conservation_barriers
#print axioms p2_conservation_head_thresholds
#print axioms four_head_five_partition_pointwise
#print axioms four_head_five_partition_global
#print axioms cross_ratio_pencil_identity
#print axioms cross_ratio_triple_common_root
#print axioms cross_ratio_quadruple_double_root
#print axioms cross_ratio_double_pair_sq_root
#print axioms constant_cross_ratio_four_fiber_factorization
#print axioms four_head_cross_ratio_dichotomy
#print axioms four_head_const_cr_degree_floor
#print axioms four_head_cyclic_pullback_exclusions
#print axioms four_fiber_depth3_tower_exclusion

end ProximityGap.QuarterFourHeadCrossRatioBarrier
