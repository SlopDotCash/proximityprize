/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G95CyclicCodeWeightDictionary
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.ComputeDegree

/-!
# G96 — the capacity/house extremal problem: the exact worth of the period invariants (#466)

**Lane.** Dimitrov's 2019 proof of Schinzel–Zassenhaus showed potential theory (transfinite
diameter, Pólya–Bertrandias rationality) can control the *house* of an algebraic integer where
Fourier methods cannot. G95 just made the prize wall `M(μ_n) = max_{b≠0}|η_b|` an exactly-known
extremal problem: the value multiset of the period family is `m = (p-1)/n` pairwise-distinct
real algebraic conjugates of multiplicity `n`, with power sums `P₁ = -1`, `P₂ = p - n`,
`P_r = -n^{r-1}` below wraparound (`sum_values`, `sum_values_sq`, `sum_values_pow_of_vanishing`),
integral symmetric functions (the period polynomial is monic in `ℤ[X]`), all values in
`[-n, n]`. **G96 asks: do these invariants pin the house — or is there an escape configuration
at every finite depth?** This file records the machine-checked answer.

## The probe verdict (probe_g96_extremal.py / probe_g96_integrality.py, session scratchpad)

The constrained extremal problem `maxhouse(D) = sup{house : real m-point multiset in [-n,n],
exact P₁..P_D}` was solved by truncated-Hausdorff (Hankel PSD) feasibility at β=4-shaped primes:

| n  | p       | m     | true M | √(n·log(p/n)) | maxhouse(2..6) | maxhouse(12) | D* (≤1.05·M) | 2·log₂m |
|----|---------|-------|--------|---------------|----------------|--------------|--------------|---------|
| 8  | 4073    | 509   | 7.54   | 7.06          | **8 = n**      | 7.74         | 12           | 18      |
| 16 | 65537   | 4096  | 13.84  | 11.54         | **16 = n**     | 14.29        | 12           | 24      |
| 32 | 1048609 | 32769 | 22.98  | 18.24         | **32 = n**     | 24.46        | 14           | 30      |

* **No finite-depth sufficiency below `log m`:** `maxhouse(D)` equals the trivial cap `n`
  through depth ≈ 6–8, decays along the moment ladder, and pins to `(1+o(1))·M` only at
  `D ≈ log₂ m` — the `r ≈ ln q` moment doctrine (dossier §2, `θ(r,β) = (β+r-1)/(2r) > 1/2`)
  is TIGHT from below: the ladder bound is exactly the worth of the data, no functional of the
  depth-`D` invariants beats it. At the prize (`m = 2^128`) that depth is ≈ 128 ≫ the
  wraparound onset — the open-window verdict of G81 restated on the value side.
* **Integrality does not bite (the capacity lever is empty here):** at `(p,n) = (41,8)`
  (true period polynomial `x⁵+x⁴-16x³+5x²+21x-9`, all `e_k ∈ ℤ` verified), the full
  `ℤ[X]`-realizable escape (exhaustive over the free tail coefficients — the scan windows
  `|e₄| ≤ 500`, `|e₅| ≤ 900` provably cover all admissible tails, since `Σr² = 33` forces
  `|e₄| ≤ 340`, `|e₅| ≤ 112` by AM-GM; 774 all-real-rooted witnesses) reaches house `4.662`
  vs real-relaxation `4.904` vs true `M = 4.529`: **integrality
  trims < 5% and the `ℤ[X]` escape still EXCEEDS the true house.** At `m = 9, 11` (rounding
  search, lower bounds) the `ℤ`-escape reaches 89–94% of the relaxation. There is no
  Dimitrov-style obstruction: the escape configuration is realizable inside `ℤ[X]` with the
  exact true head data.

## What is formalized (axiom-clean, constructive)

1. `escape_depth_three` — for every `(n, p, m)` with `n·m = p-1`, `p ≥ 3n²+n`: an explicit
   real `m`-point multiset in `[-n,n]` with the EXACT true invariants `P₁ = -1`, `P₂ = p-n`,
   `P₃ = -n²` and house `= n` (the trivial cap). Depth-3 data — everything G95 proves
   unconditionally at every scale — certifies NOTHING below trivial.
2. `escape_depth_four` — the parametric depth-4 escape: for ANY fourth-moment value `P₄` in
   the (explicitly given, always-satisfied-at-prize-shape) feasibility window and any spike
   `0 ≤ H ≤ n` inside it, an explicit multiset with exact `P₁..P₄` and `H` in support.
   `escape_depth_four_teeth` instantiates it at `(n,p) = (16, 65537)` with the TRUE fourth
   moment `P₄ = 2945069` (`N₀(μ₁₆,4) = 720 = 3n²-3n`, exact Wick, probe-verified) and spike
   `H = n = 16 > M = 13.84`: even the exact depth-4 true data admits the trivial-cap escape.
3. `zx_escape_witness` — **the integrality-no-bite theorem.** The explicit monic integer
   quintic `x⁵+x⁴-16x³+5x²+3x-1` (irreducible over ℚ; probe-verified by exhaustive
   linear/quadratic factor scan) has five distinct real roots in `(-8,8)` whose power sums are
   EXACTLY the true `(p,n) = (41,8)` period data `(P₁,P₂,P₃) = (-1, 33, -64)` — and its house
   exceeds `23/5 = 4.6 > M = 4.529…`. So full `ℤ[X]`-integrality + totally-real + cap + the
   exact depth-3 invariants still admit a house above the true one: the algebraic rigidity
   the capacity route would need is *absent* at explicit small scale.
   `zx_witness_exceeds_target_scale`: `23/5 > √(8·log₂(41/8))` — the escape is above the
   Gumbel/prize scale, not merely above `M`.
4. `escape_shadows_true_values` — the weld to G95: for an actual subgroup instance
   (`hψ` primitive, `G` the subgroup finset, `N₀(G,3) = 0`), the escape multiset of (1) has
   the same `ℂ`-power sums as the TRUE distinct-value set of the period family, degree-for-
   degree — the escape is literally indistinguishable from the truth at depth 3.

## Differentiation from the recorded record

* `_Attack02GaussPeriodHouse` (valuation/Stickelberger → house LOWER bound): G96 is not a
  valuation argument; it is the extremal-converse of the moment bridge.
* `_AttackE2_MomentConeSpikeNoGo` (max not a function of `(S₁,S₂,S₄)`, generic vectors): G96
  pins the escape at the TRUE prize invariants (incl. the odd G95 data `P₃ = -n²`), under the
  cap `|v| ≤ n` and the exact cardinality `m`, with house AT the cap, sweeps the depth
  parameter, and adds the `ℤ[X]`-realizability layer E2 never touched.
* `_N3IntegralityCapacityVacuity` (`|disc| ≥ 1` on the TRUE conjugates is vacuous): N3 killed
  the discriminant lever on the true configuration; G96 kills the *realizability* lever on the
  ESCAPE configuration — even demanding the escape be a genuine `ℤ[X]` system does not close
  the gap (774 witnesses at `m = 5`).
* `_wfTT07/_wfTT09/_wfTT10`, `_H1MahlerHouseDominantConjugate`, `_T5TropicalGaussianPeriodHouse`
  (capacity/Fekete/Mahler/equidistribution sign-reversals): those record that each capacity-
  theoretic *upper-bound lever* inverts to a lower bound. G96 explains WHY from the data side:
  the invariants those levers consume (moments + integrality) provably carry no house content
  below the moment-ladder depth — there is nothing for a capacity ceiling to grip.
* `MomentExponentThreshold` / dossier §2 (`θ(r,β) > 1/2`, the upper-bound ladder): G96 supplies
  the matching LOWER half (escape realizes the ladder), turning the ladder into a two-sided
  characterization of the worth of depth-`D` data.

## Honest scope

These are structure/no-go theorems about the INVARIANT DATA, not about `M` itself. They prove
that no argument consuming only {depth-`D` power sums, cardinality, cap, `ℤ[X]`-integrality,
total realness} can certify the prize bound for `D` below the `log m` moment depth — they do
NOT prove the prize bound false, and they leave open (as the surviving CORE shape) inputs that
see the *joint* frequency structure (which `b` carries which value), e.g. the signed/correlated
cross-arc functionals of the G80/G89 lane. The `maxhouse(D)` table is probe numerics
(Hankel relaxation, longdouble); the Lean theorems are the exact finite constructions.

## References

- V. Dimitrov, *A proof of the Schinzel–Zassenhaus conjecture on polynomials*, 2019/20.
- G. Pólya, *Über gewisse notwendige Determinantenkriterien…*; Bertrandias rationality.
- C. Smyth, *The Mahler measure of algebraic numbers: a survey*; Schur–Siegel–Smyth trace problem.
- R.J. McEliece, *Irreducible cyclic codes and Gauss sums*, 1974 (period-polynomial integrality).
- Bourgain–Glibichuk–Konyagin 2006 (the moment/energy upper route this file lower-bounds).

Issue #466. No `sorry`, no new axioms, no `native_decide`.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.G96CapacityHouseExtremal

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumRawMoment
open ArkLib.ProximityGap.G95CyclicCodeWeightDictionary

/-! ## §1. The depth-3 escape: the unconditional G95 data is worth nothing below the trivial cap

`P₁ = -1` (`sum_values`), `P₂ = p - n` (`sum_values_sq`), `P₃ = -n²`
(`sum_values_pow_of_vanishing`, odd antipodal depth) are the invariants G95 establishes at
every scale. We exhibit, for every prize-shaped `(n, m, p)`, an explicit `m`-point real
multiset in `[-n, n]` carrying exactly these three power sums with an element AT the cap `n`.

Construction: `K` antipodal pairs `±n` (`K = ⌊R/(2n²)⌋`), the odd-fixer pair
`u, v = (-1 ± √((4n²-1)/3))/2` (which satisfies `u+v = -1`, `u³+v³ = -n²` exactly), one tuner
pair `±w` absorbing the second-moment remainder, and zeros. Everything is closed-form. -/

theorem escape_depth_three (n m p : ℕ) (hn : 3 ≤ n) (hp : 3 * n ^ 2 + n ≤ p)
    (hm : n * m = p - 1) :
    ∃ V : Multiset ℝ,
      V.card = m ∧ (∀ x ∈ V, |x| ≤ (n : ℝ)) ∧ ((n : ℝ) ∈ V) ∧
      V.sum = -1 ∧
      (V.map fun x => x ^ 2).sum = (p : ℝ) - n ∧
      (V.map fun x => x ^ 3).sum = -(n : ℝ) ^ 2 := by
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpR : 3 * (n : ℝ) ^ 2 + (n : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp1 : 1 ≤ p := by nlinarith [hn, hp]
  have hmR : (n : ℝ) * (m : ℝ) = (p : ℝ) - 1 := by
    have h := congrArg (fun k : ℕ => (k : ℝ)) hm
    push_cast [Nat.cast_sub hp1] at h
    linarith [h]
  -- the odd-fixer square root
  set s : ℝ := Real.sqrt ((4 * (n : ℝ) ^ 2 - 1) / 3) with hs_def
  have hs_sq : s ^ 2 = (4 * (n : ℝ) ^ 2 - 1) / 3 := Real.sq_sqrt (by nlinarith)
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hs_le : s ≤ 2 * (n : ℝ) - 1 := by
    have h1 : (4 * (n : ℝ) ^ 2 - 1) / 3 ≤ (2 * (n : ℝ) - 1) ^ 2 := by nlinarith
    calc s ≤ Real.sqrt ((2 * (n : ℝ) - 1) ^ 2) := Real.sqrt_le_sqrt h1
      _ = |2 * (n : ℝ) - 1| := Real.sqrt_sq_eq_abs _
      _ = 2 * (n : ℝ) - 1 := abs_of_nonneg (by nlinarith)
  -- the second-moment budget and the pair count
  set R : ℝ := (p : ℝ) - n - (2 * (n : ℝ) ^ 2 + 1) / 3 with hR_def
  have hn2pos : (0 : ℝ) < 2 * (n : ℝ) ^ 2 := by nlinarith
  have hR_lb : 2 * (n : ℝ) ^ 2 ≤ R := by rw [hR_def]; nlinarith
  set K : ℕ := ⌊R / (2 * (n : ℝ) ^ 2)⌋₊ with hK_def
  have hRdivpos : 0 ≤ R / (2 * (n : ℝ) ^ 2) :=
    div_nonneg (by linarith [hR_lb, hn2pos]) (le_of_lt hn2pos)
  have hK_le : (K : ℝ) * (2 * (n : ℝ) ^ 2) ≤ R := by
    have h := Nat.floor_le hRdivpos
    rw [← hK_def] at h
    calc (K : ℝ) * (2 * (n : ℝ) ^ 2) ≤ (R / (2 * (n : ℝ) ^ 2)) * (2 * (n : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right h (le_of_lt hn2pos)
      _ = R := div_mul_cancel₀ R hn2pos.ne'
  have hK_gt : R < ((K : ℝ) + 1) * (2 * (n : ℝ) ^ 2) := by
    have h := Nat.lt_floor_add_one (R / (2 * (n : ℝ) ^ 2))
    rw [← hK_def] at h
    calc R = (R / (2 * (n : ℝ) ^ 2)) * (2 * (n : ℝ) ^ 2) := (div_mul_cancel₀ R hn2pos.ne').symm
      _ < ((K : ℝ) + 1) * (2 * (n : ℝ) ^ 2) := mul_lt_mul_of_pos_right h hn2pos
  have hK1 : 1 ≤ K := by
    rw [hK_def]
    apply Nat.le_floor
    rw [Nat.cast_one, le_div_iff₀ hn2pos, one_mul]
    exact hR_lb
  -- the tuner
  set w : ℝ := Real.sqrt ((R - (K : ℝ) * (2 * (n : ℝ) ^ 2)) / 2) with hw_def
  have hw_sq : w ^ 2 = (R - (K : ℝ) * (2 * (n : ℝ) ^ 2)) / 2 :=
    Real.sq_sqrt (by nlinarith [hK_le])
  have hw_nonneg : 0 ≤ w := Real.sqrt_nonneg _
  have hw_le : w ≤ (n : ℝ) := by
    have h1 : (R - (K : ℝ) * (2 * (n : ℝ) ^ 2)) / 2 ≤ (n : ℝ) ^ 2 := by nlinarith [hK_gt]
    calc w ≤ Real.sqrt ((n : ℝ) ^ 2) := Real.sqrt_le_sqrt h1
      _ = (n : ℝ) := Real.sqrt_sq (by positivity)
  -- cardinality bookkeeping
  have hKcast : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have hcard : 2 * K + 4 ≤ m := by
    have hr : ((2 * K + 4 : ℕ) : ℝ) ≤ (m : ℝ) := by
      push_cast
      -- 2K·n² ≤ R ≤ p−n; need (2K+4)·n² ≤ m·n² = n(p−1)/1·n… ⟺ p−n+4n² ≤ n(p−1)
      nlinarith [hK_le, hR_lb, hmR, hpR, hnR, hn2pos]
    exact_mod_cast hr
  -- the escape multiset
  refine ⟨Multiset.replicate K ((n : ℝ)) + Multiset.replicate K (-(n : ℝ)) +
      ((-1 + s) / 2 ::ₘ (-1 - s) / 2 ::ₘ w ::ₘ {-w}) +
      Multiset.replicate (m - (2 * K + 4)) 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- cardinality
    simp only [Multiset.card_add, Multiset.card_replicate, Multiset.card_cons,
      Multiset.card_singleton]
    omega
  · -- the cap |x| ≤ n
    intro x hx
    simp only [Multiset.mem_add, Multiset.mem_replicate, Multiset.mem_cons,
      Multiset.mem_singleton] at hx
    rcases hx with ((⟨-, rfl⟩ | ⟨-, rfl⟩) | (rfl | rfl | rfl | rfl)) | ⟨-, rfl⟩
    · rw [abs_of_nonneg (by positivity)]
    · rw [abs_neg, abs_of_nonneg (by positivity)]
    · rw [abs_le]; constructor <;> nlinarith only [hs_nonneg, hs_le, hnR]
    · rw [abs_le]; constructor <;> nlinarith only [hs_nonneg, hs_le, hnR]
    · rw [abs_of_nonneg hw_nonneg]; exact hw_le
    · rw [abs_neg, abs_of_nonneg hw_nonneg]; exact hw_le
    · simp
  · -- the cap is attained: n ∈ V
    have hKne : K ≠ 0 := by omega
    exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr
      (Or.inl (Multiset.mem_replicate.mpr ⟨hKne, rfl⟩))))))
  · -- P₁ = -1
    simp only [Multiset.sum_add, Multiset.sum_replicate, Multiset.sum_cons,
      Multiset.sum_singleton, nsmul_eq_mul, mul_zero]
    ring
  · -- P₂ = p - n
    simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
      Multiset.sum_replicate, Multiset.map_cons, Multiset.sum_cons, Multiset.map_singleton,
      Multiset.sum_singleton, nsmul_eq_mul]
    linear_combination (1 / 2 : ℝ) * hs_sq + 2 * hw_sq + hR_def
  · -- P₃ = -n²
    simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
      Multiset.sum_replicate, Multiset.map_cons, Multiset.sum_cons, Multiset.map_singleton,
      Multiset.sum_singleton, nsmul_eq_mul]
    linear_combination (-3 / 4 : ℝ) * hs_sq

/-- Teeth: the depth-3 escape at the concrete prize-shaped instance `(n, m, p) = (4, 64, 257)`
(the `μ₄ ⊂ F₂₅₇` shape whose `N₀(μ₄,3) = 0` is probe-verified): a 64-point multiset in
`[-4, 4]` with the exact true data `P₁ = -1`, `P₂ = 253`, `P₃ = -16` and house `= 4`. -/
theorem escape_depth_three_teeth :
    ∃ V : Multiset ℝ,
      V.card = 64 ∧ (∀ x ∈ V, |x| ≤ (4 : ℝ)) ∧ ((4 : ℝ) ∈ V) ∧
      V.sum = -1 ∧
      (V.map fun x => x ^ 2).sum = 253 ∧
      (V.map fun x => x ^ 3).sum = -16 := by
  have h := escape_depth_three 4 64 257 (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨V, h1, h2, h3, h4, h5, h6⟩ := h
  exact ⟨V, h1, by exact_mod_cast h2, by exact_mod_cast h3, h4, by
    rw [h5]; norm_num, by rw [h6]; norm_num⟩

/-! ## §2. The depth-4 escape: even the exact fourth moment leaves the cap in reach

Parametric in the fourth-moment value `P₄` (so it applies verbatim to the TRUE value, which
equals `(p·N₀(G,4) - n⁴)/n` by G95's `card_smul_sum_values_pow`) and in the spike `H`. The
bulk is two antipodal families `±β₁, ±β₂` (`A` copies each) whose squared magnitudes
`x, y = (S₂ ∓ √(4A·S₄ - S₂²))/(4A)` match the second AND fourth moment residuals exactly. -/

theorem escape_depth_four (n m p : ℕ) (P4 H S2 S4 : ℝ) (hn : 3 ≤ n)
    (hH0 : 0 ≤ H) (hHn : H ≤ (n : ℝ))
    (hS2def : S2 = (p : ℝ) - n - 2 * H ^ 2 - (2 * (n : ℝ) ^ 2 + 1) / 3)
    (hS4def : S4 = P4 - 2 * H ^ 4 - (2 * (n : ℝ) ^ 4 + 8 * (n : ℝ) ^ 2 - 1) / 9)
    (hS2pos : 0 < S2) (hS4pos : 0 < S4)
    (hwin : 4 * S4 ≤ S2 ^ 2)
    (hyn : 2 * S4 ≤ (n : ℝ) ^ 2 * S2)
    (hcount : S2 ^ 2 + 8 * S4 ≤ (m : ℝ) * S4) :
    ∃ V : Multiset ℝ,
      V.card = m ∧ (∀ x ∈ V, |x| ≤ (n : ℝ)) ∧ H ∈ V ∧
      V.sum = -1 ∧
      (V.map fun x => x ^ 2).sum = (p : ℝ) - n ∧
      (V.map fun x => x ^ 3).sum = -(n : ℝ) ^ 2 ∧
      (V.map fun x => x ^ 4).sum = P4 := by
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  -- the odd-fixer square root (same as depth 3)
  set s : ℝ := Real.sqrt ((4 * (n : ℝ) ^ 2 - 1) / 3) with hs_def
  have hs_sq : s ^ 2 = (4 * (n : ℝ) ^ 2 - 1) / 3 := Real.sq_sqrt (by nlinarith)
  have hs_nonneg : 0 ≤ s := Real.sqrt_nonneg _
  have hs_le : s ≤ 2 * (n : ℝ) - 1 := by
    have h1 : (4 * (n : ℝ) ^ 2 - 1) / 3 ≤ (2 * (n : ℝ) - 1) ^ 2 := by nlinarith
    calc s ≤ Real.sqrt ((2 * (n : ℝ) - 1) ^ 2) := Real.sqrt_le_sqrt h1
      _ = |2 * (n : ℝ) - 1| := Real.sqrt_sq_eq_abs _
      _ = 2 * (n : ℝ) - 1 := abs_of_nonneg (by nlinarith)
  clear_value s
  -- the bulk pair count
  set A : ℕ := ⌈S2 ^ 2 / (4 * S4)⌉₊ with hA_def
  have hA_ge : S2 ^ 2 / (4 * S4) ≤ (A : ℝ) := Nat.le_ceil _
  have hA_lt : (A : ℝ) < S2 ^ 2 / (4 * S4) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hA1 : 1 ≤ A := by
    rw [hA_def]
    rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Nat.ceil_pos]
    positivity
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA1
  clear_value A
  have h4Apos : (0 : ℝ) < 4 * (A : ℝ) := by linarith [hApos]
  -- division-free forms of the ceiling window
  have h4AS4_ge : S2 ^ 2 ≤ 4 * (A : ℝ) * S4 := by
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * S4)).mp hA_ge
    linarith [h]
  have hA4S4 : (A : ℝ) * (4 * S4) < S2 ^ 2 + 4 * S4 := by
    have h1 : (A : ℝ) * (4 * S4) < (S2 ^ 2 / (4 * S4) + 1) * (4 * S4) :=
      mul_lt_mul_of_pos_right hA_lt (by positivity)
    have h2 : (S2 ^ 2 / (4 * S4) + 1) * (4 * S4) = S2 ^ 2 + 4 * S4 := by
      field_simp
    linarith [h1, h2]
  have h4AS4_lt : 4 * (A : ℝ) * S4 < 2 * S2 ^ 2 := by nlinarith only [hA4S4, hwin]
  -- the discriminant square root
  set D : ℝ := Real.sqrt (4 * (A : ℝ) * S4 - S2 ^ 2) with hD_def
  have hD_sq : D ^ 2 = 4 * (A : ℝ) * S4 - S2 ^ 2 := Real.sq_sqrt (by linarith [h4AS4_ge])
  have hD_nonneg : 0 ≤ D := Real.sqrt_nonneg _
  have hD_le_S2 : D ≤ S2 := by nlinarith only [hD_sq, h4AS4_lt, hD_nonneg, hS2pos]
  -- the two bulk squared-magnitudes, pinned by their cleared-denominator equations
  set x : ℝ := (S2 - D) / (4 * (A : ℝ)) with hx_def
  set y : ℝ := (S2 + D) / (4 * (A : ℝ)) with hy_def
  have hx4A : 4 * (A : ℝ) * x = S2 - D := by
    rw [hx_def, mul_comm]
    exact div_mul_cancel₀ _ h4Apos.ne'
  have hy4A : 4 * (A : ℝ) * y = S2 + D := by
    rw [hy_def, mul_comm]
    exact div_mul_cancel₀ _ h4Apos.ne'
  clear_value D x y
  have hx0 : 0 ≤ x := by
    rw [hx_def]
    exact div_nonneg (by linarith [hD_le_S2]) (by linarith [h4Apos])
  have hy0 : 0 ≤ y := by
    rw [hy_def]
    exact div_nonneg (by linarith [hD_nonneg, hS2pos]) (by linarith [h4Apos])
  -- the moment identities carried by the bulk (division-free)
  have hxy_sum : 2 * (A : ℝ) * x + 2 * (A : ℝ) * y = S2 := by
    apply mul_left_cancel₀ (show (2 : ℝ) ≠ 0 by norm_num)
    linear_combination hx4A + hy4A
  have h16 : 16 * (A : ℝ) ^ 2 * (x ^ 2 + y ^ 2) = 8 * (A : ℝ) * S4 := by
    linear_combination (4 * (A : ℝ) * x + S2 - D) * hx4A +
      (4 * (A : ℝ) * y + S2 + D) * hy4A + 2 * hD_sq
  have hxy_sq : 2 * (A : ℝ) * x ^ 2 + 2 * (A : ℝ) * y ^ 2 = S4 := by
    apply mul_left_cancel₀ (mul_pos (show (0 : ℝ) < 8 by norm_num) hApos).ne'
    linear_combination h16
  -- the cap on the bulk magnitudes: x ≤ y ≤ n²
  have hS2le : S2 ≤ 2 * (A : ℝ) * (n : ℝ) ^ 2 := by
    have h2 : 2 * (A : ℝ) * (2 * S4) ≤ 2 * (A : ℝ) * ((n : ℝ) ^ 2 * S2) :=
      mul_le_mul_of_nonneg_left hyn (by linarith [hApos])
    have h1 : S2 * S2 ≤ (2 * (A : ℝ) * (n : ℝ) ^ 2) * S2 := by
      nlinarith only [h4AS4_ge, h2]
    exact le_of_mul_le_mul_right h1 hS2pos
  have hy_le : y ≤ (n : ℝ) ^ 2 := by
    rw [hy_def, div_le_iff₀ (by linarith [h4Apos])]
    -- S2 + D ≤ 2·S2 ≤ (4A)·n²
    nlinarith only [hD_le_S2, hS2le]
  have hx_le : x ≤ (n : ℝ) ^ 2 := by
    have hxy : x ≤ y := by
      have h : 4 * (A : ℝ) * x ≤ 4 * (A : ℝ) * y := by
        rw [hx4A, hy4A]; linarith [hD_nonneg]
      exact le_of_mul_le_mul_left h h4Apos
    linarith [hy_le]
  -- the bulk magnitudes
  set b1 : ℝ := Real.sqrt x with hb1_def
  set b2 : ℝ := Real.sqrt y with hb2_def
  have hb1_sq : b1 ^ 2 = x := Real.sq_sqrt hx0
  have hb2_sq : b2 ^ 2 = y := Real.sq_sqrt hy0
  have hb1_nonneg : 0 ≤ b1 := Real.sqrt_nonneg _
  have hb2_nonneg : 0 ≤ b2 := Real.sqrt_nonneg _
  have hb1_le : b1 ≤ (n : ℝ) := by
    calc b1 ≤ Real.sqrt ((n : ℝ) ^ 2) := Real.sqrt_le_sqrt hx_le
      _ = (n : ℝ) := Real.sqrt_sq (by positivity)
  have hb2_le : b2 ≤ (n : ℝ) := by
    calc b2 ≤ Real.sqrt ((n : ℝ) ^ 2) := Real.sqrt_le_sqrt hy_le
      _ = (n : ℝ) := Real.sqrt_sq (by positivity)
  clear_value b1 b2
  -- cardinality bookkeeping: 4A + 4 ≤ m
  have hcard : 4 * A + 4 ≤ m := by
    have hr : ((4 * A + 4 : ℕ) : ℝ) ≤ (m : ℝ) := by
      push_cast
      -- 4·S4·A < S2² + 4·S4 and S2² + 8·S4 ≤ m·S4, cancel S4 > 0
      nlinarith only [hA4S4, hcount, hS4pos]
    exact_mod_cast hr
  -- the escape multiset
  refine ⟨(H ::ₘ -H ::ₘ (-1 + s) / 2 ::ₘ {(-1 - s) / 2}) +
      Multiset.replicate A b1 + Multiset.replicate A (-b1) +
      Multiset.replicate A b2 + Multiset.replicate A (-b2) +
      Multiset.replicate (m - (4 * A + 4)) 0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- cardinality
    simp only [Multiset.card_add, Multiset.card_replicate, Multiset.card_cons,
      Multiset.card_singleton]
    omega
  · -- the cap |x| ≤ n
    intro z hz
    simp only [Multiset.mem_add, Multiset.mem_replicate, Multiset.mem_cons,
      Multiset.mem_singleton] at hz
    rcases hz with (((((rfl | rfl | rfl | rfl) | ⟨-, rfl⟩) | ⟨-, rfl⟩) | ⟨-, rfl⟩) | ⟨-, rfl⟩) | ⟨-, rfl⟩
    · rw [abs_of_nonneg hH0]; exact hHn
    · rw [abs_neg, abs_of_nonneg hH0]; exact hHn
    · rw [abs_le]; constructor <;> nlinarith only [hs_nonneg, hs_le, hnR]
    · rw [abs_le]; constructor <;> nlinarith only [hs_nonneg, hs_le, hnR]
    · rw [abs_of_nonneg hb1_nonneg]; exact hb1_le
    · rw [abs_neg, abs_of_nonneg hb1_nonneg]; exact hb1_le
    · rw [abs_of_nonneg hb2_nonneg]; exact hb2_le
    · rw [abs_neg, abs_of_nonneg hb2_nonneg]; exact hb2_le
    · simp
  · -- the spike is in the support
    exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr
      (Or.inl (Multiset.mem_add.mpr (Or.inl (Multiset.mem_add.mpr
        (Or.inl (Multiset.mem_cons_self _ _))))))))))
  · -- P₁ = -1
    simp only [Multiset.sum_add, Multiset.sum_replicate, Multiset.sum_cons,
      Multiset.sum_singleton, nsmul_eq_mul, mul_zero]
    ring
  · -- P₂ = p - n
    simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
      Multiset.sum_replicate, Multiset.map_cons, Multiset.sum_cons, Multiset.map_singleton,
      Multiset.sum_singleton, nsmul_eq_mul]
    linear_combination (1 / 2 : ℝ) * hs_sq + (A : ℝ) * hb1_sq + (A : ℝ) * hb1_sq +
      (A : ℝ) * hb2_sq + (A : ℝ) * hb2_sq + hxy_sum + hS2def
  · -- P₃ = -n²
    simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
      Multiset.sum_replicate, Multiset.map_cons, Multiset.sum_cons, Multiset.map_singleton,
      Multiset.sum_singleton, nsmul_eq_mul]
    linear_combination (-3 / 4 : ℝ) * hs_sq
  · -- P₄ = P4
    simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
      Multiset.sum_replicate, Multiset.map_cons, Multiset.sum_cons, Multiset.map_singleton,
      Multiset.sum_singleton, nsmul_eq_mul]
    linear_combination ((3 : ℝ) / 4 + (1 / 8 : ℝ) * (s ^ 2 + (4 * (n : ℝ) ^ 2 - 1) / 3)) * hs_sq +
      (2 * (A : ℝ) * (b1 ^ 2 + x)) * hb1_sq + (2 * (A : ℝ) * (b2 ^ 2 + y)) * hb2_sq +
      hxy_sq + hS4def

/-- Teeth: the depth-4 escape at `(n, m, p) = (16, 4096, 65537)` with the **true** fourth
moment `P₄ = 2945069` (from `n·P₄ = p·N₀(μ₁₆,4) - n⁴` with the probe-verified exact Wick value
`N₀(μ₁₆,4) = 720 = 3n² - 3n`) and the spike at the trivial cap `H = n = 16`: a 4096-point
multiset in `[-16,16]` with the exact true `P₁, P₂, P₃, P₄` and house `16 > M = 13.837…` —
the exact depth-4 data cannot see below the trivial cap at the prize shape. -/
theorem escape_depth_four_teeth :
    ∃ V : Multiset ℝ,
      V.card = 4096 ∧ (∀ x ∈ V, |x| ≤ (16 : ℝ)) ∧ ((16 : ℝ) ∈ V) ∧
      V.sum = -1 ∧
      (V.map fun x => x ^ 2).sum = 65521 ∧
      (V.map fun x => x ^ 3).sum = -256 ∧
      (V.map fun x => x ^ 4).sum = 2945069 := by
  have h := escape_depth_four 16 4096 65537 2945069 16 64838 2799206
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨V, h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨V, h1, by exact_mod_cast h2, by exact_mod_cast h3, h4, ?_, ?_, h7⟩
  · rw [h5]; norm_num
  · rw [h6]; norm_num

/-! ## §3. The integrality-no-bite witness: the escape is realizable inside `ℤ[X]`

The monic integer quintic `f = X⁵ + X⁴ - 16X³ + 5X² + 3X - 1` shares its three head
coefficients — equivalently (Newton) its first three power sums `(P₁,P₂,P₃) = (-1, 33, -64)` —
with the TRUE period polynomial `X⁵ + X⁴ - 16X³ + 5X² + 21X - 9` of `(p, n) = (41, 8)`
(computed exactly from `N₀` counts; all `e_k ∈ ℤ` verified). `f` is totally real with all five
roots in `(-8, 8)` and its house exceeds `23/5 = 4.6`, ABOVE the true house `M = 4.5290…` —
and `f` is irreducible over `ℚ` (no rational root since `f(±1) ≠ 0` with constant term `-1`;
no integer quadratic factor by exhaustive scan), so its roots form the conjugate system of a
genuine degree-5 algebraic integer in a totally real quintic field. Full `ℤ[X]`-integrality
adds no house rigidity beyond the real-moment relaxation. -/

theorem zx_escape_witness :
    ∃ r₁ r₂ r₃ r₄ r₅ : ℝ,
      (-8 < r₁ ∧ r₁ < -(23 / 5)) ∧ (-(23 / 5) < r₂ ∧ r₂ < 0) ∧
      (0 < r₃ ∧ r₃ < 39 / 100) ∧ (39 / 100 < r₄ ∧ r₄ < 1) ∧ (1 < r₅ ∧ r₅ < 8) ∧
      (∀ r ∈ [r₁, r₂, r₃, r₄, r₅], r ^ 5 + r ^ 4 - 16 * r ^ 3 + 5 * r ^ 2 + 3 * r - 1 = 0) ∧
      r₁ + r₂ + r₃ + r₄ + r₅ = -1 ∧
      r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2 + r₄ ^ 2 + r₅ ^ 2 = 33 ∧
      r₁ ^ 3 + r₂ ^ 3 + r₃ ^ 3 + r₄ ^ 3 + r₅ ^ 3 = -64 ∧
      23 / 5 < |r₁| := by
  -- the witness polynomial as a function
  set f : ℝ → ℝ := fun x => x ^ 5 + x ^ 4 - 16 * x ^ 3 + 5 * x ^ 2 + 3 * x - 1 with hf_def
  have hcont : Continuous f := by fun_prop
  -- the exact sign table
  have e0 : f (-8) < 0 := by norm_num [hf_def]
  have e1 : 0 < f (-(23 / 5)) := by norm_num [hf_def]
  have e2 : f 0 < 0 := by norm_num [hf_def]
  have e3 : 0 < f (39 / 100) := by norm_num [hf_def]
  have e4 : f 1 < 0 := by norm_num [hf_def]
  have e5 : 0 < f 8 := by norm_num [hf_def]
  -- five roots by the intermediate value theorem
  obtain ⟨r₁, hr₁m, hr₁⟩ := intermediate_value_Ioo (by norm_num : (-8 : ℝ) ≤ -(23 / 5))
    hcont.continuousOn (Set.mem_Ioo.mpr ⟨e0, e1⟩)
  obtain ⟨r₂, hr₂m, hr₂⟩ := intermediate_value_Ioo' (by norm_num : (-(23 / 5) : ℝ) ≤ 0)
    hcont.continuousOn (Set.mem_Ioo.mpr ⟨e2, e1⟩)
  obtain ⟨r₃, hr₃m, hr₃⟩ := intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 39 / 100)
    hcont.continuousOn (Set.mem_Ioo.mpr ⟨e2, e3⟩)
  obtain ⟨r₄, hr₄m, hr₄⟩ := intermediate_value_Ioo' (by norm_num : (39 / 100 : ℝ) ≤ 1)
    hcont.continuousOn (Set.mem_Ioo.mpr ⟨e4, e3⟩)
  obtain ⟨r₅, hr₅m, hr₅⟩ := intermediate_value_Ioo (by norm_num : (1 : ℝ) ≤ 8)
    hcont.continuousOn (Set.mem_Ioo.mpr ⟨e4, e5⟩)
  obtain ⟨h₁l, h₁r⟩ := Set.mem_Ioo.mp hr₁m
  obtain ⟨h₂l, h₂r⟩ := Set.mem_Ioo.mp hr₂m
  obtain ⟨h₃l, h₃r⟩ := Set.mem_Ioo.mp hr₃m
  obtain ⟨h₄l, h₄r⟩ := Set.mem_Ioo.mp hr₄m
  obtain ⟨h₅l, h₅r⟩ := Set.mem_Ioo.mp hr₅m
  -- pairwise distinctness from the interval chain
  have hd12 : r₁ ≠ r₂ := by intro h; rw [h] at h₁r; linarith
  have hd13 : r₁ ≠ r₃ := by intro h; rw [h] at h₁r; linarith
  have hd14 : r₁ ≠ r₄ := by intro h; rw [h] at h₁r; linarith
  have hd15 : r₁ ≠ r₅ := by intro h; rw [h] at h₁r; linarith
  have hd23 : r₂ ≠ r₃ := by intro h; rw [h] at h₂r; linarith
  have hd24 : r₂ ≠ r₄ := by intro h; rw [h] at h₂r; linarith
  have hd25 : r₂ ≠ r₅ := by intro h; rw [h] at h₂r; linarith
  have hd34 : r₃ ≠ r₄ := by intro h; rw [h] at h₃r; linarith
  have hd35 : r₃ ≠ r₅ := by intro h; rw [h] at h₃r; linarith
  have hd45 : r₄ ≠ r₅ := by intro h; rw [h] at h₄r; linarith
  -- the Vieta difference polynomial: Q := f - ∏(X - rᵢ), degree ≤ 4, kills all five roots
  set Q : Polynomial ℝ :=
    Polynomial.C (1 + (r₁ + r₂ + r₃ + r₄ + r₅)) * Polynomial.X ^ 4 +
    Polynomial.C (-16 - (r₁ * r₂ + r₁ * r₃ + r₁ * r₄ + r₁ * r₅ + r₂ * r₃ + r₂ * r₄ + r₂ * r₅ +
      r₃ * r₄ + r₃ * r₅ + r₄ * r₅)) * Polynomial.X ^ 3 +
    Polynomial.C (5 + (r₁ * r₂ * r₃ + r₁ * r₂ * r₄ + r₁ * r₂ * r₅ + r₁ * r₃ * r₄ + r₁ * r₃ * r₅ +
      r₁ * r₄ * r₅ + r₂ * r₃ * r₄ + r₂ * r₃ * r₅ + r₂ * r₄ * r₅ + r₃ * r₄ * r₅)) *
      Polynomial.X ^ 2 +
    Polynomial.C (3 - (r₁ * r₂ * r₃ * r₄ + r₁ * r₂ * r₃ * r₅ + r₁ * r₂ * r₄ * r₅ +
      r₁ * r₃ * r₄ * r₅ + r₂ * r₃ * r₄ * r₅)) * Polynomial.X +
    Polynomial.C (-1 + r₁ * r₂ * r₃ * r₄ * r₅) with hQ_def
  have hQ_eval : ∀ t : ℝ, Q.eval t =
      f t - (t - r₁) * (t - r₂) * (t - r₃) * (t - r₄) * (t - r₅) := by
    intro t
    simp only [hQ_def, hf_def, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X]
    ring
  have hQ_root : ∀ r ∈ ({r₁, r₂, r₃, r₄, r₅} : Finset ℝ), Q.eval r = 0 := by
    intro r hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [hQ_eval, hr₁]; ring
    · rw [hQ_eval, hr₂]; ring
    · rw [hQ_eval, hr₃]; ring
    · rw [hQ_eval, hr₄]; ring
    · rw [hQ_eval, hr₅]; ring
  have hcard5 : ({r₁, r₂, r₃, r₄, r₅} : Finset ℝ).card = 5 := by
    rw [Finset.card_insert_of_notMem (by simp [hd12, hd13, hd14, hd15]),
      Finset.card_insert_of_notMem (by simp [hd23, hd24, hd25]),
      Finset.card_insert_of_notMem (by simp [hd34, hd35]),
      Finset.card_insert_of_notMem (by simp [hd45]),
      Finset.card_singleton]
  have hQdeg : Q.natDegree ≤ 4 := by
    rw [hQ_def]
    compute_degree
  have hQ0 : Q = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' Q _ hQ_root
      (by rw [hcard5]; omega)
  -- the full functional factorization: f(t) = ∏(t - rᵢ) for every t
  have hfact : ∀ t : ℝ, t ^ 5 + t ^ 4 - 16 * t ^ 3 + 5 * t ^ 2 + 3 * t - 1 =
      (t - r₁) * (t - r₂) * (t - r₃) * (t - r₄) * (t - r₅) := by
    intro t
    have h := congrArg (Polynomial.eval t) hQ0
    rw [hQ_eval, hf_def] at h
    simpa [sub_eq_zero] using h
  -- Vandermonde extraction at the nodes 0, 1, -1, 2, -2 pins the three head Newton data
  have hv0 := hfact 0
  have hv1 := hfact 1
  have hvm1 := hfact (-1)
  have hv2 := hfact 2
  have hvm2 := hfact (-2)
  have he1 : r₁ + r₂ + r₃ + r₄ + r₅ = -1 := by
    linear_combination (1 / 4 : ℝ) * hv0 + (-1 / 6 : ℝ) * hv1 + (-1 / 6 : ℝ) * hvm1 +
      (1 / 24 : ℝ) * hv2 + (1 / 24 : ℝ) * hvm2
  have he2 : r₁ * r₂ + r₁ * r₃ + r₁ * r₄ + r₁ * r₅ + r₂ * r₃ + r₂ * r₄ + r₂ * r₅ +
      r₃ * r₄ + r₃ * r₅ + r₄ * r₅ = -16 := by
    linear_combination (1 / 6 : ℝ) * hv1 + (-1 / 6 : ℝ) * hvm1 +
      (-1 / 12 : ℝ) * hv2 + (1 / 12 : ℝ) * hvm2
  have he3 : r₁ * r₂ * r₃ + r₁ * r₂ * r₄ + r₁ * r₂ * r₅ + r₁ * r₃ * r₄ + r₁ * r₃ * r₅ +
      r₁ * r₄ * r₅ + r₂ * r₃ * r₄ + r₂ * r₃ * r₅ + r₂ * r₄ * r₅ + r₃ * r₄ * r₅ = -5 := by
    linear_combination (-5 / 4 : ℝ) * hv0 + (2 / 3 : ℝ) * hv1 + (2 / 3 : ℝ) * hvm1 +
      (-1 / 24 : ℝ) * hv2 + (-1 / 24 : ℝ) * hvm2
  -- assemble
  refine ⟨r₁, r₂, r₃, r₄, r₅, ⟨h₁l, h₁r⟩, ⟨h₂l, h₂r⟩, ⟨h₃l, h₃r⟩, ⟨h₄l, h₄r⟩, ⟨h₅l, h₅r⟩,
    ?_, he1, ?_, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    exacts [hr₁, hr₂, hr₃, hr₄, hr₅]
  · -- Newton: P₂ = e₁² - 2e₂ = 1 + 32 = 33
    linear_combination (r₁ + r₂ + r₃ + r₄ + r₅ - 1) * he1 - 2 * he2
  · -- Newton: P₃ = e₁³ - 3e₁e₂ + 3e₃ = -1 - 48 - 15 = -64
    linear_combination ((r₁ + r₂ + r₃ + r₄ + r₅) ^ 2 - (r₁ + r₂ + r₃ + r₄ + r₅) + 1 -
      3 * (r₁ * r₂ + r₁ * r₃ + r₁ * r₄ + r₁ * r₅ + r₂ * r₃ + r₂ * r₄ + r₂ * r₅ +
        r₃ * r₄ + r₃ * r₅ + r₄ * r₅)) * he1 + 3 * he2 + 3 * he3
  · -- the house exceeds 23/5
    rw [abs_of_neg (by linarith : r₁ < 0)]
    linarith

/-- The `ℤ[X]` escape house `23/5` exceeds the Gumbel/prize target scale
`√(n·log₂(p/n)) = √(8·log₂(41/8)) ≈ 4.343` at the witness instance: integrality-constrained
escapes live ABOVE the conjectured scale, not merely above the true house. -/
theorem zx_witness_exceeds_target_scale :
    Real.sqrt (8 * Real.logb 2 (41 / 8)) < 23 / 5 := by
  have hlogb : Real.logb 2 (41 / 8) ≤ 5 / 2 := by
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by norm_num)]
    -- 41/8 ≤ 2^(5/2) = √32
    have h32 : (2 : ℝ) ^ ((5 : ℝ) / 2) = Real.sqrt 32 := by
      rw [Real.sqrt_eq_rpow, show ((5 : ℝ) / 2) = 5 * (1 / 2) by ring,
        show (32 : ℝ) = (2 : ℝ) ^ (5 : ℝ) by
          rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num,
        ← Real.rpow_mul (by norm_num)]
    rw [h32, show (41 : ℝ) / 8 = Real.sqrt ((41 / 8) ^ 2) from
      (Real.sqrt_sq (by norm_num)).symm]
    apply Real.sqrt_le_sqrt
    norm_num
  calc Real.sqrt (8 * Real.logb 2 (41 / 8)) ≤ Real.sqrt 20 := by
        apply Real.sqrt_le_sqrt; linarith
    _ < 23 / 5 := by
        rw [show (23 : ℝ) / 5 = Real.sqrt ((23 / 5) ^ 2) from
          (Real.sqrt_sq (by norm_num)).symm]
        apply Real.sqrt_lt_sqrt (by norm_num)
        norm_num

/-! ## §4. The weld to G95: the escape shadows the TRUE value multiset exactly

For an actual period instance (primitive `ψ`, subgroup finset `G` of size `n`, `N₀(G,3) = 0`
below the odd wraparound), the depth-3 escape multiset has exactly the same first three
complex power sums as the true distinct-value set of the period family, and the same
cardinality. Any house bound derived from {`m`, cap, `P₁`, `P₂`, `P₃`} alone applies to both
configurations and hence cannot certify anything below the trivial cap `n`. -/

open scoped Classical in
theorem escape_shadows_true_values {p : ℕ} [hp : Fact p.Prime] {ψ : AddChar (ZMod p) ℂ}
    (hψ : ψ.IsPrimitive) {G : Finset (ZMod p)} (h1 : (1 : ZMod p) ∈ G)
    (h0 : (0 : ZMod p) ∉ G) (hmul : ∀ x ∈ G, ∀ y ∈ G, x * y ∈ G)
    (hneg : (-1 : ZMod p) ∈ G) (hvan3 : N0 G 3 = 0) (m : ℕ)
    (hn : 3 ≤ G.card) (hp3 : 3 * G.card ^ 2 + G.card ≤ p) (hm : G.card * m = p - 1) :
    ∃ V : Multiset ℝ,
      V.card = ((Finset.univ.filter fun c : ZMod p => c ≠ 0).image (eta ψ G)).card ∧
      (∀ x ∈ V, |x| ≤ (G.card : ℝ)) ∧ ((G.card : ℝ) ∈ V) ∧
      (((V.sum : ℝ) : ℂ) = ∑ v ∈ (Finset.univ.filter fun c : ZMod p => c ≠ 0).image (eta ψ G), v) ∧
      ((((V.map fun x => x ^ 2).sum : ℝ) : ℂ)
        = ∑ v ∈ (Finset.univ.filter fun c : ZMod p => c ≠ 0).image (eta ψ G), v ^ 2) ∧
      ((((V.map fun x => x ^ 3).sum : ℝ) : ℂ)
        = ∑ v ∈ (Finset.univ.filter fun c : ZMod p => c ≠ 0).image (eta ψ G), v ^ 3) := by
  obtain ⟨V, hcard, hcap, hmem, hs1, hs2, hs3⟩ :=
    escape_depth_three G.card m p hn hp3 hm
  have hGpos : 0 < G.card := Finset.card_pos.mpr ⟨1, h1⟩
  have hvalcard : ((Finset.univ.filter fun c : ZMod p => c ≠ 0).image (eta ψ G)).card = m := by
    rw [card_values hψ h1 h0 hmul, ← hm, Nat.mul_div_cancel_left m hGpos]
  refine ⟨V, by rw [hvalcard, hcard], hcap, hmem, ?_, ?_, ?_⟩
  · rw [sum_values hψ h1 h0 hmul, hs1]
    norm_num
  · rw [sum_values_sq hψ h1 h0 hmul hneg, hs2]
    push_cast
    ring
  · rw [sum_values_pow_of_vanishing hψ h1 h0 hmul (by norm_num) hvan3, hs3]
    push_cast
    ring

/-! ## Axiom audit -/

#print axioms ArkLib.ProximityGap.G96CapacityHouseExtremal.escape_depth_three
#print axioms ArkLib.ProximityGap.G96CapacityHouseExtremal.escape_depth_three_teeth
#print axioms ArkLib.ProximityGap.G96CapacityHouseExtremal.escape_depth_four
#print axioms ArkLib.ProximityGap.G96CapacityHouseExtremal.escape_depth_four_teeth
#print axioms ArkLib.ProximityGap.G96CapacityHouseExtremal.zx_escape_witness
#print axioms ArkLib.ProximityGap.G96CapacityHouseExtremal.zx_witness_exceeds_target_scale
#print axioms ArkLib.ProximityGap.G96CapacityHouseExtremal.escape_shadows_true_values

end ArkLib.ProximityGap.G96CapacityHouseExtremal
