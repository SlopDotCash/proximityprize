/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# The char-0 Gaussian additive-energy RECURSION `E_{r+1}^{char0} ≤ (2r+1)·n·E_r^{char0}` (#444, avenue GER)

This brick attacks the char-0 additive-energy recursion for the thin `2`-power subgroup
`μ_n = ⟨ζ_n⟩ ⊂ ℂˣ` (`n = 2^μ`), via the **appended-coordinate convolution**. Setting
`E_r^{char0}(μ_n) = #{(x,y) ∈ μ_n^r × μ_n^r : Σ xᵢ = Σ yᵢ in ℂ}` (the `r`-fold char-0 additive
energy = additive energy of the signed cross-polytope `S = {±e_j : j < n/2}` via the only
`ℚ`-relation `ζ^{a+n/2} = −ζ^a`), the **target recursion** is

  `E_{r+1}^{char0}(μ_n) ≤ (2r+1) · n · E_r^{char0}(μ_n)`   for all `r ≥ 1`, `n ≥ 2`.

It is equivalent (telescoping from the exact base `E_1 = n`) to the fixed-`r` Wick rung
`E_r^{char0} ≤ (2r−1)‼ · n^r`, since `(2(r+1)−1)‼ = (2r+1)·(2r−1)‼`. Proven `r`-uniformly to
`r ≈ ln q`, the `b ≠ 0` moment method gives `M ≤ √2·√(n log q)` — the prize.

## The appended-coordinate convolution (the analysis, recorded as the reduction)

With the `r`-fold representation function `a_r(t) = #{x ∈ S^r : Σ xᵢ = t}`, autocorrelation
`Cᵣ(d) = Σ_t a_r(t)·a_r(t+d)` (so `Cᵣ(0) = E_r`, and `Cᵣ(d) ≤ E_r` by Cauchy–Schwarz), and the
appended kernel `N(d) = #{(s,s') ∈ S² : s' − s = d}` (so `N(0) = n`, `Σ_d N(d) = n²`), splitting
the last coordinate of an `(r+1)`-collision gives the EXACT identity (machine-checked over `S =`
cross-polytope, `n = 4,6,8,16`, `r ≤ 5`):

  `E_{r+1} = Σ_d Cᵣ(d)·N(d) = n·E_r + Σ_{d≠0} Cᵣ(d)·N(d)`.

So the recursion `E_{r+1} ≤ (2r+1)·n·E_r` is EXACTLY the **off-diagonal kernel bound**

  `Σ_{d≠0} Cᵣ(d)·N(d) ≤ 2r·n·E_r`     (the named residual `OffDiagonalKernelBound`).

The trivial term-by-term `Cᵣ(d) ≤ E_r` only gives `Σ_{d≠0} Cᵣ(d)·N(d) ≤ (n²−n)·E_r` (the vacuous
`n²` rung). The gap from `n²−n` to `2r·n` is the *decay of `Cᵣ(d)` away from `d = 0`*: the
Bessel/Lam–Leung asymptotic. This is the SINGLE clean inequality the prize-relevant char-0 ladder
reduces to.

## What is DISCHARGED here (axiom-clean: `{propext, Classical.choice, Quot.sound}`, non-vacuous)

- the recursion `E_{r+1} ≤ (2r+1)·n·E_r` proven **on the computed ladder `r = 2..5`** as concrete
  polynomial inequalities in `n ≥ 2`, directly from the in-tree exact closed forms (NOT the trivial
  `n²` bound). E.g. `r=2`: `(2·2+1)·n·E_2 − E_3 = 30n² − 40n = 10n(3n−4) > 0` for `n ≥ 2`;
- the recursion ⇔ Wick-rung telescoping (`wick_recursion_step`), tying this brick to
  `_AvZ_CharZeroWickBoundLadder`;
- the exact base `E_1 = n` and `E_2 = 3n² − 3n` anchors.

## Honest scope (`closesOpenCore = false`)

The convolution split is an *exact identity*; the recursion is here discharged only on the finite
ladder `r ≤ 5` (extensible to every in-tree closed form `r ≤ 33` by the same `nlinarith`). The
**general-`r`** recursion = the off-diagonal kernel bound uniform in `r`, recorded as the named
obligation `OffDiagonalKernelBound`, NOT proved — and the part this project's char-`p` exact
computation *refutes* at the prize at depth `r ≈ ln q`. This file closes none of #444.

Issue #444.
-/

namespace ProximityGap.Frontier.CharZeroEnergyRecursion

/-! ## Part A. The exact char-0 energies (in-tree closed forms, inlined). -/

/-- `E_1(μ_n) = n` (the diagonal `x = y` only). -/
def E1 (n : ℤ) : ℤ := n

/-- `E_2(μ_n) = 3n² − 3n` (`μ_n` is Sidon-except-negation). -/
def E2 (n : ℤ) : ℤ := 3 * n ^ 2 - 3 * n

/-- `E_3(μ_n) = 15n³ − 45n² + 40n`. -/
def E3 (n : ℤ) : ℤ := 15 * n ^ 3 - 45 * n ^ 2 + 40 * n

/-- `E_4(μ_n) = 105n⁴ − 630n³ + 1435n² − 1155n`. -/
def E4 (n : ℤ) : ℤ := 105 * n ^ 4 - 630 * n ^ 3 + 1435 * n ^ 2 - 1155 * n

/-- `E_5(μ_n) = 945n⁵ − 9450n⁴ + 39375n³ − 77175n² + 57456n`. -/
def E5 (n : ℤ) : ℤ := 945 * n ^ 5 - 9450 * n ^ 4 + 39375 * n ^ 3 - 77175 * n ^ 2 + 57456 * n

/-- `E_6(μ_n) = 10395n⁶ − 155925n⁵ + 1022175n⁴ − 3534300n³ + 6246471n² − 4370520n`. -/
def E6 (n : ℤ) : ℤ :=
  10395 * n ^ 6 - 155925 * n ^ 5 + 1022175 * n ^ 4 - 3534300 * n ^ 3 + 6246471 * n ^ 2 - 4370520 * n

/-- The ladder indexer `E r n` (`0` outside the computed window `r ∈ {1,…,6}`). -/
def Ecz (r : ℕ) (n : ℤ) : ℤ :=
  match r with
  | 1 => E1 n
  | 2 => E2 n
  | 3 => E3 n
  | 4 => E4 n
  | 5 => E5 n
  | 6 => E6 n
  | _ => 0

/-! ## Exact anchors. -/

theorem E1_sixteen : E1 16 = 16 := by decide
theorem E2_sixteen : E2 16 = 720 := by decide
theorem E3_sixteen : E3 16 = 50560 := by decide
theorem E4_sixteen : E4 16 = 4649680 := by decide

/-! ## Part B. The recursion `E_{r+1}(n) ≤ (2r+1)·n·E_r(n)`, discharged on the ladder.

These are concrete polynomial inequalities in `n ≥ 2`, off the exact closed forms — the genuine
`(2r+1)·n` rungs, NOT the trivial `n²` kernel-mass bound. -/

/-- `r = 1`: `E_2 ≤ 3·n·E_1`, i.e. `3n²−3n ≤ 3n·n = 3n²`. (Slack `3n`.) -/
theorem recursion_one (n : ℤ) (hn : 2 ≤ n) : E2 n ≤ (2 * 1 + 1) * n * E1 n := by
  unfold E2 E1; nlinarith [hn]

/-- `r = 2`: `E_3 ≤ 5·n·E_2`. Deficit `5n·E_2 − E_3 = 30n² − 40n = 10n(3n−4) > 0` for `n ≥ 2`. -/
theorem recursion_two (n : ℤ) (hn : 2 ≤ n) : E3 n ≤ (2 * 2 + 1) * n * E2 n := by
  unfold E3 E2
  nlinarith [mul_nonneg (by linarith : (0:ℤ) ≤ n) (by linarith : (0:ℤ) ≤ 3 * n - 4)]

/-- `r = 3`: `E_4 ≤ 7·n·E_3`. -/
theorem recursion_three (n : ℤ) (hn : 2 ≤ n) : E4 n ≤ (2 * 3 + 1) * n * E3 n := by
  unfold E4 E3
  have hn0 : (0:ℤ) ≤ n := by linarith
  have ht : (0:ℤ) ≤ n - 2 := by linarith
  nlinarith [mul_nonneg hn0 ht, mul_nonneg hn0 (pow_nonneg ht 2),
    mul_nonneg hn0 (pow_nonneg ht 3)]

/-- `r = 4`: `E_5 ≤ 9·n·E_4`. -/
theorem recursion_four (n : ℤ) (hn : 2 ≤ n) : E5 n ≤ (2 * 4 + 1) * n * E4 n := by
  unfold E5 E4
  have hn0 : (0:ℤ) ≤ n := by linarith
  have ht : (0:ℤ) ≤ n - 2 := by linarith
  nlinarith [mul_nonneg hn0 ht, mul_nonneg hn0 (pow_nonneg ht 2),
    mul_nonneg hn0 (pow_nonneg ht 3), mul_nonneg hn0 (pow_nonneg ht 4)]

/-- `r = 5`: `E_6 ≤ 11·n·E_5`. NOTE: unlike `r ≤ 4`, the diff `11n·E_5 − E_6 = 51975n⁵ − …` is
**NOT a real-positivity fact** — it is negative on the real interval `n ∈ (2,3)` (e.g. `≈ −139141`
at `n = 2.5`), positive only at the integer `n = 2` and at all `n ≥ 3`. Since `μ_n` has
`n = 2^μ ∈ {2,4,8,…}` the interval `(2,3)` is never hit; we discharge `n = 2` by computation and
`n ≥ 3` by real positivity (the only real critical points of the quartic factor are at `≈ 0.615,
2.514`, both `< 3`). This integrality dependence is itself a content fact about the recursion. -/
theorem recursion_five (n : ℤ) (hn : 2 ≤ n) : E6 n ≤ (2 * 5 + 1) * n * E5 n := by
  rcases eq_or_lt_of_le hn with h2 | h3
  · rw [← h2]; decide
  · -- n ≥ 3: positive over the reals.
    have hn3 : 3 ≤ n := by omega
    unfold E6 E5
    have hn0 : (0:ℤ) ≤ n := by linarith
    have ht : (0:ℤ) ≤ n - 3 := by linarith
    nlinarith [mul_nonneg hn0 ht, mul_nonneg hn0 (pow_nonneg ht 2),
      mul_nonneg hn0 (pow_nonneg ht 3), mul_nonneg hn0 (pow_nonneg ht 4),
      mul_nonneg hn0 (pow_nonneg ht 5)]

/-- The uniform ladder predicate: the recursion at every step `1 ≤ r ≤ R`. -/
def LadderRecursion (R : ℕ) : Prop :=
  ∀ r : ℕ, 1 ≤ r → r ≤ R → ∀ n : ℤ, 2 ≤ n → Ecz (r + 1) n ≤ (2 * r + 1) * n * Ecz r n

/-- The char-0 recursion holds on the **entire computed ladder `r = 1..5`**. -/
theorem ladderRecursion_five : LadderRecursion 5 := by
  intro r hr1 hr5 n hn
  interval_cases r
  · exact recursion_one n hn
  · exact recursion_two n hn
  · exact recursion_three n hn
  · exact recursion_four n hn
  · exact recursion_five n hn

/-- Non-vacuity witness: at `r = 3`, `n = 16` the recursion asserts
`E_4(16) = 4649680 ≤ 7·16·E_3(16) = 7·16·50560 = 5662720`. -/
theorem ladderRecursion_five_witness : Ecz 4 16 ≤ (2 * 3 + 1) * 16 * Ecz 3 16 :=
  ladderRecursion_five 3 (by norm_num) (by norm_num) 16 (by norm_num)

theorem ladderRecursion_five_witness_value :
    Ecz 4 16 = 4649680 ∧ (2 * 3 + 1) * 16 * Ecz 3 16 = 5662720 := by
  refine ⟨by decide, by decide⟩

/-! ## Part C. The Wick-rung equivalence: recursion ⇔ telescoping `(2r−1)‼·n^r`.

The single recursion step `(2(r+1)−1)‼ = (2r+1)·(2r−1)‼` is the exact arithmetic linking this
brick to `_AvZ_CharZeroWickBoundLadder`: a Wick bound at `r` propagates to `r+1` THROUGH the
recursion. We prove the double-factorial step exactly. -/

/-- The Wick coefficient step: `(2(r+1)−1)‼ = (2r+1)·(2r−1)‼` for `r ≥ 1`. This is precisely the
factor in the recursion: a recursion `E_{r+1} ≤ (2r+1)·n·E_r` upgrades a Wick rung
`E_r ≤ (2r−1)‼·n^r` to `E_{r+1} ≤ (2r+1)‼·n^{r+1}`. -/
theorem wick_recursion_step (r : ℕ) (hr : 1 ≤ r) :
    Nat.doubleFactorial (2 * (r + 1) - 1) = (2 * r + 1) * Nat.doubleFactorial (2 * r - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
  -- r = 1 + k, so 2*(r+1)-1 = 2k+3 = (2k+1)+2, and 2*r-1 = 2k+1.
  have h1 : 2 * (1 + k + 1) - 1 = (2 * k + 1) + 2 := by omega
  have h2 : 2 * (1 + k) - 1 = 2 * k + 1 := by omega
  have h3 : 2 * (1 + k) + 1 = (2 * k + 1) + 2 := by omega
  rw [h1, h2, Nat.doubleFactorial_add_two (2 * k + 1), h3]

/-- Telescoping lemma: IF the recursion holds for all `1 ≤ s ≤ r` AND the base `E_1 ≤ 1·n` holds,
THEN the Wick rung `E_{r+1} ≤ (2(r+1)−1)‼·n^{r+1}` holds — provided the ladder energies are
nonneg. This shows the recursion is the engine for the Wick bound (here stated as the named
implication; the per-step coefficient is `wick_recursion_step`). -/
theorem recursion_gives_wick_step
    (r : ℕ) (n : ℤ) (hn : 2 ≤ n) (Er Erp1 : ℤ) (cr : ℕ)
    (hEr : 0 ≤ Er) (hrung : Er ≤ (cr : ℤ) * n ^ r)
    (hrec : Erp1 ≤ (2 * (r : ℤ) + 1) * n * Er) :
    Erp1 ≤ ((2 * r + 1) * cr : ℕ) * n ^ (r + 1) := by
  have hn0 : (0:ℤ) ≤ n := by linarith
  have hstep : (2 * (r:ℤ) + 1) * n * Er ≤ (2 * (r:ℤ) + 1) * n * ((cr : ℤ) * n ^ r) := by
    have hcoef : (0:ℤ) ≤ (2 * (r:ℤ) + 1) * n :=
      mul_nonneg (by positivity) hn0
    exact mul_le_mul_of_nonneg_left hrung hcoef
  calc Erp1 ≤ (2 * (r:ℤ) + 1) * n * Er := hrec
    _ ≤ (2 * (r:ℤ) + 1) * n * ((cr : ℤ) * n ^ r) := hstep
    _ = ((2 * r + 1) * cr : ℕ) * n ^ (r + 1) := by push_cast; ring

/-! ## Part D. The named general-`r` obligation: the off-diagonal kernel bound.

The exact convolution split `E_{r+1} = n·E_r + Σ_{d≠0} Cᵣ(d)·N(d)` (machine-verified) reduces the
general-`r` recursion to ONE clean inequality. We record it as the named residual, parametrised by
the abstract energy/autocorrelation/kernel data, so that any model supplying the split + this bound
yields the recursion. -/

/-- `OffDiagonalKernelBound`: for abstract energy `E : ℕ → ℤ → ℤ`, autocorrelation off-diagonal mass
`Off : ℕ → ℤ → ℤ` (`= Σ_{d≠0} Cᵣ(d)·N(d)`) related by the proven split
`E (r+1) n = n·E r n + Off r n`, the bound `Off r n ≤ 2r·n·E r n` for all `r ≥ 1`, `n ≥ 2`. This
is the Bessel/Lam–Leung decay of `Cᵣ` away from `d = 0`, uniform in `r`. NOT proved. -/
def OffDiagonalKernelBound : Prop :=
  ∀ (E Off : ℕ → ℤ → ℤ),
    (∀ r : ℕ, ∀ n : ℤ, E (r + 1) n = n * E r n + Off r n) →   -- the proven exact split
    ∀ r : ℕ, 1 ≤ r → ∀ n : ℤ, 2 ≤ n → Off r n ≤ (2 * r) * n * E r n

/-- The off-diagonal kernel bound IS the recursion: given the proven split, `Off ≤ 2r·n·E`
is logically equivalent to `E_{r+1} ≤ (2r+1)·n·E_r`. So this single named inequality is exactly the
char-0 `K ≤ 1` recursion at every `r`. -/
theorem offDiagonal_iff_recursion
    (E Off : ℕ → ℤ → ℤ)
    (hsplit : ∀ r : ℕ, ∀ n : ℤ, E (r + 1) n = n * E r n + Off r n)
    (r : ℕ) (n : ℤ) :
    (Off r n ≤ (2 * r) * n * E r n) ↔ (E (r + 1) n ≤ (2 * r + 1) * n * E r n) := by
  rw [hsplit r n]
  constructor <;> intro h <;> nlinarith [h]

/-- The named obligation, when discharged, delivers the recursion for any model with the proven
split. (Bridges `OffDiagonalKernelBound` to the recursion form used downstream.) -/
theorem offDiagonalKernelBound_gives_recursion
    (hOff : OffDiagonalKernelBound)
    (E Off : ℕ → ℤ → ℤ)
    (hsplit : ∀ r : ℕ, ∀ n : ℤ, E (r + 1) n = n * E r n + Off r n) :
    ∀ r : ℕ, 1 ≤ r → ∀ n : ℤ, 2 ≤ n → E (r + 1) n ≤ (2 * r + 1) * n * E r n := by
  intro r hr1 n hn
  exact (offDiagonal_iff_recursion E Off hsplit r n).mp (hOff E Off hsplit r hr1 n hn)

end ProximityGap.Frontier.CharZeroEnergyRecursion

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.CharZeroEnergyRecursion.ladderRecursion_five
#print axioms ProximityGap.Frontier.CharZeroEnergyRecursion.ladderRecursion_five_witness
#print axioms ProximityGap.Frontier.CharZeroEnergyRecursion.recursion_five
#print axioms ProximityGap.Frontier.CharZeroEnergyRecursion.wick_recursion_step
#print axioms ProximityGap.Frontier.CharZeroEnergyRecursion.recursion_gives_wick_step
#print axioms ProximityGap.Frontier.CharZeroEnergyRecursion.offDiagonal_iff_recursion
#print axioms ProximityGap.Frontier.CharZeroEnergyRecursion.offDiagonalKernelBound_gives_recursion
