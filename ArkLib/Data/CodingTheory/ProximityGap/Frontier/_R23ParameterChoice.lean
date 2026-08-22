/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R22StepanovAssembly

/-!
# LANE PARAM (#466 round 23): the explicit Stepanov parameter family —
# the pipeline fires UNCONDITIONALLY

This file instantiates the S2 parameters `(m, J, D)` and the budget `B` explicitly and
discharges every arithmetic side condition, making the round-22 pipeline
(`fourthMoment_quadChar_of_s2output_pipeline`) fire with ZERO named hypotheses.

## The optimization (probe `probe_r23_params.py` / `probe_r23_family.py`, 2026-07-07)

Minimizing `B(q) = ⌈(2·Dtot + 3m)/m⌉ − q` over admissible `(m, J, D)` subject to the
PROVEN S2 budgets (`m(D+2m+J) < 2J(D+1)`, `2D+3 < q`, `m ≤ (q−1)/2`):

* the binding constraint is the S1 budget `2D+3 < q` (D is pushed to its cap `(q−5)/2`);
  with `D = βq` free the continuous optimum is `B = 2√(2.5(1+2β)/β)·√q`, minimized at
  `β = 1/2`, giving the achievable constant
  **`C* = 2√10 ≈ 6.3246`** at `m ≈ √(2q/5)`, `J = m/2 + 1`, `D = (q−5)/2`.
* grid probe (all `m`, `J`, `D` at fixed `q`): best `B/√q` = 7.363 (q=101), 6.643 (1009),
  6.498 (10007), 6.402 (65537) — converging to `2√10` from above.  The round-22
  skeptic's 6.4 was already essentially optimal; `C*` cannot be beaten inside this
  constraint system (the `β = 1/2` wall is the S1 budget, not slack).

## The explicit family (this file, all ℕ-valued)

`s = √((q−4)/10)`, `m = 2s`, `J = s + 1`, `D = (q−5)/2`, and two budgets:
* `B = 4·√(10q)` (`≈ 12.65√q ≤ 13√q`): admissible for ALL odd `q ≥ 171` — and `q ≤ 169`
  is closed by the trivial bound (`K = 169 ≥ q`).  **ZERO GAP**: the chain fires at
  every finite field of odd characteristic.  Rung constant `Cw = 13 + 4 = 17`.
* `B = 2·√(10q) + 36` (`≈ 6.32√q + 36 ≤ 7√q` for large `q`): the tight family,
  `K = 49`, proven here for all odd `q ≥ 3251` (numerically admissible from
  `q ≥ 2825`; the AM–GM slack in the formal bound costs the difference).
  Rung constant `Cw = 11`.

Probe verification: all three budgets + admissibility checked exactly (as stated, with
`Nat.sqrt = isqrt` and floor division) for every odd `q` in `[91, 300001]` for the
`K = 169` family and every odd `q ≥ 2825` up to `3·10⁶` for the `K = 49` family, plus
spot checks at `q = 65537` and `q = 2²⁰ + 7`.

## Headline results (axiom-clean)

* `legendreCubicHasseC_unconditional : ringChar F ≠ 2 → LegendreCubicHasseC F 169` —
  the UNCONDITIONAL generic-constant Hasse bound `S² ≤ 169·q` for the Legendre cubic
  family at EVERY finite field of odd characteristic.  No named hypotheses.
* `fourthMoment_quadChar_unconditional` — the r=2 rung quadratic face
  `∑_s ‖T‖⁴ ≤ 17·|G|²·q` for every `G` with `|G|⁴ ≤ q`, unconditionally.
* `legendreCubicHasseC_49_of_large` / `fourthMoment_quadChar_tight_of_large` — the
  tight constants (`K = 49`, `Cw = 11`) for `q ≥ 3251`.
* `stepanovConstant = 7 = ⌈2√10⌉` — the ceiling of the achievable one-sided constant.

## Honest scope

The elementary-Stepanov constant `C* = 2√10` is what THIS constraint system achieves;
the sharp Hasse `C = 2` (`K = 4`) is NOT reached — the round-22 audit showed no consumer
needs it.  The `K = 49` family has a formal/numeric gap `q ∈ (2825, 3251)` (AM–GM slack
only, no mathematical obstruction); the `K = 169` family has no gap at all.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open ArkLib.ProximityGap.Frontier.R16LegendreCosetFace (shiftedCharSum)

namespace ArkLib.ProximityGap.Frontier.R23ParameterChoice

open ArkLib.ProximityGap.Frontier.R20StepanovScaffold
open ArkLib.ProximityGap.Frontier.R18FourthMomentTwist
open ArkLib.ProximityGap.Frontier.R20QuadFaceBridge
open ArkLib.ProximityGap.Frontier.R22StepanovS2
open ArkLib.ProximityGap.Frontier.R22StepanovAssembly

/-! ## 1. The explicit parameter family -/

/-- The base scale `s = ⌊√((q−4)/10)⌋ ≈ √(q/10)` (so `m = 2s ≈ √(2q/5)`, the continuous
optimum of the Stepanov budget under the `D < q/2` cap). -/
def sP (q : ℕ) : ℕ := Nat.sqrt ((q - 4) / 10)

/-- Hasse-derivative order `m = 2s`. -/
def mP (q : ℕ) : ℕ := 2 * sP q

/-- Block count `J = s + 1 = m/2 + 1` (the minimal `J` beating the rank-nullity count
at the `D`-cap). -/
def jP (q : ℕ) : ℕ := sP q + 1

/-- Per-block degree `D = (q−5)/2` — the S1 budget cap (`2D + 3 = q − 2 < q`). -/
def dP (q : ℕ) : ℕ := (q - 5) / 2

/-- The auxiliary square-root scale `b = ⌊√(10q)⌋` (note `s·b ≈ q`: the two floors pair
to a clean product lower bound, which is what makes the Nat-sqrt proofs tractable). -/
def bP (q : ℕ) : ℕ := Nat.sqrt (10 * q)

/-- The zero-gap budget `B = 4b ≈ 12.65·√q` (constant `k = 13`). -/
def bigB (q : ℕ) : ℕ := 4 * bP q

/-- The tight budget `B = 2b + 36 ≈ 6.32·√q + 36` (constant `k = 7`, `q ≥ 3251`). -/
def bigB7 (q : ℕ) : ℕ := 2 * bP q + 36

/-- The total-degree bound produced by S2 at these parameters
(`Dtot = 3(m+e) + D + q(J−1)`, `e = (q−1)/2`). -/
def dtotP (q : ℕ) : ℕ := 3 * (mP q + (q - 1) / 2) + dP q + q * (jP q - 1)

/-- **The achievable elementary-Stepanov constant**: `⌈2√10⌉ = 7`.  `2√10 ≈ 6.3246` is
the exact continuous optimum of `B/√q` over all admissible `(m, J, D)` (the binding
wall is the S1 budget `2D + 3 < q`); `7` is the least integer `k` with `C* ≤ k`. -/
def stepanovConstant : ℕ := 7

/-! ## 2. Nat-sqrt bracketing facts -/

theorem ten_sP_sq_le {q : ℕ} : 10 * (sP q * sP q) ≤ q - 4 := by
  have h1 : sP q * sP q ≤ (q - 4) / 10 := Nat.sqrt_le _
  calc 10 * (sP q * sP q) ≤ 10 * ((q - 4) / 10) := Nat.mul_le_mul_left _ h1
    _ ≤ q - 4 := Nat.mul_div_le _ _

theorem lt_ten_sP_succ_sq {q : ℕ} : q - 4 < 10 * ((sP q + 1) * (sP q + 1)) := by
  have h1 : (q - 4) / 10 < (sP q + 1) * (sP q + 1) := Nat.lt_succ_sqrt _
  have h2 := Nat.div_add_mod (q - 4) 10
  have h3 : (q - 4) % 10 < 10 := Nat.mod_lt _ (by norm_num)
  set d := (q - 4) / 10
  set S := (sP q + 1) * (sP q + 1)
  omega

theorem bP_sq_le {q : ℕ} : bP q * bP q ≤ 10 * q := Nat.sqrt_le _

theorem lt_bP_succ_sq {q : ℕ} : 10 * q < (bP q + 1) * (bP q + 1) := Nat.lt_succ_sqrt _

theorem sP_pos {q : ℕ} (hq : 14 ≤ q) : 1 ≤ sP q := by
  have : 1 * 1 ≤ (q - 4) / 10 := by
    have : 1 ≤ (q - 4) / 10 := Nat.le_div_iff_mul_le (by norm_num) |>.mpr (by omega)
    simpa using this
  exact Nat.le_sqrt.mpr this

/-- **The pairing lower bound** `(s+1)(b+1) ≥ q − 2`: the two sqrt floors multiply back
up to `q` because their radicands were chosen reciprocal (`(q−4)/10` and `10q`). -/
theorem pairing {q : ℕ} (hq : 4 ≤ q) : q ≤ (sP q + 1) * (bP q + 1) + 2 := by
  have hA : q ≤ 10 * ((sP q + 1) * (sP q + 1)) + 3 := by
    have := lt_ten_sP_succ_sq (q := q); omega
  have hB : 10 * q + 1 ≤ (bP q + 1) * (bP q + 1) := lt_bP_succ_sq
  have hA' : (q : ℤ) ≤ 10 * (((sP q : ℤ) + 1) * ((sP q : ℤ) + 1)) + 3 := by
    exact_mod_cast hA
  have hB' : 10 * (q : ℤ) + 1 ≤ ((bP q : ℤ) + 1) * ((bP q : ℤ) + 1) := by
    exact_mod_cast hB
  have hq' : (4 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
  set x : ℤ := ((sP q : ℤ) + 1) * ((bP q : ℤ) + 1) with hx
  have hs0 : (0 : ℤ) ≤ (sP q : ℤ) := Int.natCast_nonneg _
  have hb0 : (0 : ℤ) ≤ (bP q : ℤ) := Int.natCast_nonneg _
  have hx0 : (0 : ℤ) ≤ x := by positivity
  have hxsq : ((q : ℤ) - 2) ^ 2 ≤ x ^ 2 := by nlinarith [hA', hB', hq', hs0, hb0]
  have hfin : (q : ℤ) - 2 ≤ x := by
    by_contra hcon
    push_neg at hcon
    have : x ^ 2 < ((q : ℤ) - 2) ^ 2 := by nlinarith
    linarith
  have hgoal : (q : ℤ) ≤ ((sP q : ℤ) + 1) * ((bP q : ℤ) + 1) + 2 := by
    rw [hx] at hfin; linarith
  exact_mod_cast hgoal

/-! ## 3. The three budget theorems -/

/-- **Budget (i)** — the S2 rank-nullity count `m(D+2m+J) < 2J(D+1)`.
At our family this reduces to `5s² ≤ t−2` (where `q = 2t+1`), which is exactly what
`10s² ≤ q−4` gives. -/
theorem params_budget_i {q : ℕ} (hq : 15 ≤ q) (hodd : Odd q) :
    mP q * (dP q + 2 * mP q + jP q) < 2 * (jP q * (dP q + 1)) := by
  obtain ⟨t, ht⟩ := hodd
  have hs10 : 10 * (sP q * sP q) ≤ q - 4 := ten_sP_sq_le
  have hd : dP q = t - 2 := by unfold dP; omega
  have ht7 : 7 ≤ t := by omega
  obtain ⟨u, hu⟩ : ∃ u, t = u + 2 := ⟨t - 2, by omega⟩
  have hdu : dP q = u := by omega
  have h5 : 5 * (sP q * sP q) ≤ u := by omega
  rw [hdu]
  show 2 * sP q * (u + 2 * (2 * sP q) + (sP q + 1)) < 2 * ((sP q + 1) * (u + 1))
  nlinarith [h5, Nat.zero_le (sP q)]

/-- **Budget (ii)** — the S1 degree budget `2D + 3 < q` (with one unit of slack:
`2D + 3 = q − 2`). -/
theorem params_budget_ii {q : ℕ} (hq : 7 ≤ q) (hodd : Odd q) :
    2 * dP q + 3 < q := by
  obtain ⟨t, ht⟩ := hodd
  unfold dP
  omega

/-- The order bound `m ≤ e = (q−1)/2`. -/
theorem params_m_le {q : ℕ} (hq : 14 ≤ q) : mP q ≤ (q - 1) / 2 := by
  have hs10 : 10 * (sP q * sP q) ≤ q - 4 := ten_sP_sq_le
  have hs1 : 1 ≤ sP q := sP_pos hq
  have h4 : 4 * sP q ≤ 10 * (sP q * sP q) := by nlinarith
  unfold mP
  omega

/-- The key scale comparison for the zero-gap budget: `13s + 4b + 8 ≤ 2q` for
`q ≥ 171` (both `s ≈ 0.316√q` and `b ≈ 3.16√q` are `o(q)`). -/
theorem key_scale_13 {q : ℕ} (hq : 171 ≤ q) : 13 * sP q + 4 * bP q + 8 ≤ 2 * q := by
  have hs10 : 10 * (sP q * sP q) ≤ q - 4 := ten_sP_sq_le
  have hb : bP q * bP q ≤ 10 * q := bP_sq_le
  have hs10n : 10 * (sP q * sP q) + 4 ≤ q := by omega
  have hs10' : 10 * ((sP q : ℤ) * (sP q : ℤ)) + 4 ≤ (q : ℤ) := by exact_mod_cast hs10n
  have hb' : ((bP q : ℤ)) * ((bP q : ℤ)) ≤ 10 * (q : ℤ) := by exact_mod_cast hb
  have hq' : (171 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
  have goal' : 13 * (sP q : ℤ) + 4 * (bP q : ℤ) + 8 ≤ 2 * (q : ℤ) := by
    nlinarith [sq_nonneg ((sP q : ℤ) - 7), sq_nonneg ((bP q : ℤ) - 21),
      Int.natCast_nonneg (sP q), Int.natCast_nonneg (bP q)]
  exact_mod_cast goal'

/-- The shared admissibility core: with `q = 2t+1` the inequality
`2·Dtot + 3m ≤ m(B + q)` (at our `m, J, D`) is exactly `8t + 18s ≤ 2sB + 4`. -/
theorem budget_iii_core {s t q B : ℕ} (hq : q = 2 * t + 1) (ht : 2 ≤ t)
    (hkey : 8 * t + 18 * s ≤ 2 * (s * B) + 4) :
    2 * (3 * (2 * s + t) + (t - 2) + q * s) + 3 * (2 * s) ≤ 2 * s * (B + q) := by
  obtain ⟨u, hu⟩ : ∃ u, t = u + 2 := ⟨t - 2, by omega⟩
  subst hu hq
  have hexp : 2 * (3 * (2 * s + (u + 2)) + (u + 2 - 2) + (2 * (u + 2) + 1) * s)
      + 3 * (2 * s)
      = 2 * (s * (2 * (u + 2) + 1)) + 18 * s + 8 * (u + 2) - 4 := by
    have : u + 2 - 2 = u := by omega
    rw [this]; ring_nf; omega
  rw [hexp]
  have hrhs : 2 * s * (B + (2 * (u + 2) + 1))
      = 2 * (s * B) + 2 * (s * (2 * (u + 2) + 1)) := by ring
  omega

/-- **Budget (iii), zero-gap family** — admissibility of `B = 4b` for all odd
`q ≥ 171`:  `2·Dtot + 3m ≤ m(B + q)`. -/
theorem params_budget_iii {q : ℕ} (hq : 171 ≤ q) (hodd : Odd q) :
    2 * dtotP q + 3 * mP q ≤ mP q * (bigB q + q) := by
  obtain ⟨t, ht⟩ := hodd
  have ht2 : 85 ≤ t := by omega
  have he : (q - 1) / 2 = t := by omega
  have hd : dP q = t - 2 := by unfold dP; omega
  have hj : jP q - 1 = sP q := by unfold jP; omega
  have hpair : q ≤ (sP q + 1) * (bP q + 1) + 2 := pairing (by omega)
  have hkey13 : 13 * sP q + 4 * bP q + 8 ≤ 2 * q := key_scale_13 hq
  -- the key inequality 8t + 18s ≤ 8sb + 4
  have hkey : 8 * t + 18 * sP q ≤ 2 * (sP q * bigB q) + 4 := by
    have hsb : 2 * t ≤ sP q * bP q + sP q + bP q + 2 := by
      have : (sP q + 1) * (bP q + 1) = sP q * bP q + sP q + bP q + 1 := by ring
      omega
    unfold bigB
    nlinarith [hsb, hkey13]
  have hcore := budget_iii_core (s := sP q) (t := t) (q := q) (B := bigB q)
    (by omega) (by omega) hkey
  unfold dtotP mP
  rw [he, hd, hj]
  calc 2 * (3 * (2 * sP q + t) + (t - 2) + q * sP q) + 3 * (2 * sP q)
      ≤ 2 * sP q * (bigB q + q) := by
        have hm : mP q = 2 * sP q := rfl
        exact hcore
    _ = 2 * sP q * (bigB q + q) := rfl

/-- The square bound for the zero-gap budget: `(4b)² = 16b² ≤ 160q ≤ 169q`. -/
theorem bigB_sq_le {q : ℕ} : bigB q * bigB q ≤ 169 * q := by
  have hb : bP q * bP q ≤ 10 * q := bP_sq_le
  unfold bigB
  nlinarith [hb, Nat.zero_le q]

/-! ## 4. The tight family (`K = 49`, `q ≥ 3251`) -/

/-- The tight-scale comparison `25s ≥ 2b + 2` (i.e. `50s ≥ 4b + 4`, the surplus needed
to pay the `+36` constant): via the pairing bound, `q ≥ 3251` suffices. -/
theorem key_scale_7 {q : ℕ} (hq : 3251 ≤ q) : 2 * bP q + 2 ≤ 25 * sP q := by
  have hpair : q ≤ (sP q + 1) * (bP q + 1) + 2 := pairing (by omega)
  have hb : bP q * bP q ≤ 10 * q := bP_sq_le
  -- 25·s·(b+1) ≥ 25(q − 3 − b) ≥ (2b+2)(b+1) for q ≥ 3251
  have hq' : (3251 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
  have hb' : ((bP q : ℤ)) * ((bP q : ℤ)) ≤ 10 * (q : ℤ) := by exact_mod_cast hb
  have hpair' : (q : ℤ) ≤ ((sP q : ℤ) + 1) * ((bP q : ℤ) + 1) + 2 := by
    exact_mod_cast hpair
  have hs0 : (0 : ℤ) ≤ (sP q : ℤ) := Int.natCast_nonneg _
  have hb0 : (0 : ℤ) ≤ (bP q : ℤ) := Int.natCast_nonneg _
  have hstep : (2 * (bP q : ℤ) + 2) * ((bP q : ℤ) + 1) ≤ 25 * (sP q : ℤ) * ((bP q : ℤ) + 1) := by
    have hlow : 25 * ((q : ℤ) - 3 - (bP q : ℤ)) ≤ 25 * (sP q : ℤ) * ((bP q : ℤ) + 1) := by
      nlinarith [hpair']
    have hup : (2 * (bP q : ℤ) + 2) * ((bP q : ℤ) + 1) ≤ 25 * ((q : ℤ) - 3 - (bP q : ℤ)) := by
      nlinarith [hb', sq_nonneg ((bP q : ℤ) - 181), hq']
    linarith
  have hfin : 2 * (bP q : ℤ) + 2 ≤ 25 * (sP q : ℤ) :=
    le_of_mul_le_mul_right (by linarith [hstep]) (by linarith : (0 : ℤ) < (bP q : ℤ) + 1)
  exact_mod_cast hfin

/-- The square bound for the tight budget: `(2b + 36)² ≤ 49q` for `q ≥ 3251`. -/
theorem bigB7_sq_le {q : ℕ} (hq : 3251 ≤ q) : bigB7 q * bigB7 q ≤ 49 * q := by
  have hb : bP q * bP q ≤ 10 * q := bP_sq_le
  have hb' : ((bP q : ℤ)) * ((bP q : ℤ)) ≤ 10 * (q : ℤ) := by exact_mod_cast hb
  have hq' : (3251 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
  have hb0 : (0 : ℤ) ≤ (bP q : ℤ) := Int.natCast_nonneg _
  have goal' : (2 * (bP q : ℤ) + 36) * (2 * (bP q : ℤ) + 36) ≤ 49 * (q : ℤ) := by
    nlinarith [hb', sq_nonneg ((bP q : ℤ) - 180), hq', hb0]
  have : bigB7 q = 2 * bP q + 36 := rfl
  rw [this]
  exact_mod_cast goal'

/-- **Budget (iii), tight family** — admissibility of `B = 2b + 36` for odd `q ≥ 3251`. -/
theorem params_budget_iii_tight {q : ℕ} (hq : 3251 ≤ q) (hodd : Odd q) :
    2 * dtotP q + 3 * mP q ≤ mP q * (bigB7 q + q) := by
  obtain ⟨t, ht⟩ := hodd
  have he : (q - 1) / 2 = t := by omega
  have hd : dP q = t - 2 := by unfold dP; omega
  have hj : jP q - 1 = sP q := by unfold jP; omega
  have hpair : q ≤ (sP q + 1) * (bP q + 1) + 2 := pairing (by omega)
  have hk7 : 2 * bP q + 2 ≤ 25 * sP q := key_scale_7 hq
  have hkey : 8 * t + 18 * sP q ≤ 2 * (sP q * bigB7 q) + 4 := by
    have hsb : 2 * t ≤ sP q * bP q + sP q + bP q + 2 := by
      have : (sP q + 1) * (bP q + 1) = sP q * bP q + sP q + bP q + 1 := by ring
      omega
    unfold bigB7
    nlinarith [hsb, hk7]
  have hcore := budget_iii_core (s := sP q) (t := t) (q := q) (B := bigB7 q)
    (by omega) (by omega) hkey
  unfold dtotP mP
  rw [he, hd, hj]
  exact hcore

/-! ## 5. The field-level supply: `S2OutputSized` DISCHARGED -/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Odd cardinality from odd characteristic. -/
theorem odd_card_of_char_ne_two' (hF : ringChar F ≠ 2) : Odd (Fintype.card F) :=
  Nat.odd_iff.mpr (FiniteField.odd_card_of_char_ne_two hF)

/-- **The zero-gap sized S2 supply**: for every field of odd characteristic with
`q ≥ 171`, the explicit family `(mP, jP, dP, bigB)` discharges `S2OutputSized F 169`
completely — no named hypotheses left. -/
theorem s2OutputSized_holds (hF : ringChar F ≠ 2) (hq : 171 ≤ Fintype.card F) :
    S2OutputSized F 169 := by
  set q := Fintype.card F with hqdef
  have hodd : Odd q := odd_card_of_char_ne_two' hF
  have hm0 : 0 < mP q := by
    have := sP_pos (q := q) (by omega); unfold mP; omega
  refine ⟨mP q, dtotP q, (bigB q : ℤ), hm0, Int.natCast_nonneg _, ?_, ?_, ?_⟩
  · -- B² ≤ 169·q
    have := bigB_sq_le (q := q)
    have : ((bigB q : ℤ)) * ((bigB q : ℤ)) ≤ 169 * (q : ℤ) := by exact_mod_cast this
    nlinarith [this]
  · -- admissibility
    have h3 := params_budget_iii hq hodd
    have h3' : 2 * (dtotP q : ℤ) + 3 * (mP q : ℤ) ≤ (mP q : ℤ) * ((bigB q : ℤ) + (q : ℤ)) := by
      exact_mod_cast h3
    exact h3'
  · -- the S2Output itself, from the PROVEN round-22 S2 theorem
    have hS := s2Output_of_cubic_stepanov_S2 (F := F) hF hodd
      (m := mP q) (J := jP q) (D := dP q)
      (by unfold jP; omega)
      (params_m_le (by omega))
      (params_budget_ii (by omega) hodd)
      (params_budget_i (by omega) hodd)
    exact hS

/-- The tight sized supply (`K = 49`) for `q ≥ 3251`. -/
theorem s2OutputSized_holds_tight (hF : ringChar F ≠ 2) (hq : 3251 ≤ Fintype.card F) :
    S2OutputSized F 49 := by
  set q := Fintype.card F with hqdef
  have hodd : Odd q := odd_card_of_char_ne_two' hF
  have hm0 : 0 < mP q := by
    have := sP_pos (q := q) (by omega); unfold mP; omega
  refine ⟨mP q, dtotP q, (bigB7 q : ℤ), hm0, Int.natCast_nonneg _, ?_, ?_, ?_⟩
  · have := bigB7_sq_le (q := q) hq
    have : ((bigB7 q : ℤ)) * ((bigB7 q : ℤ)) ≤ 49 * (q : ℤ) := by exact_mod_cast this
    nlinarith [this]
  · have h3 := params_budget_iii_tight hq hodd
    exact_mod_cast h3
  · exact s2Output_of_cubic_stepanov_S2 (F := F) hF hodd
      (m := mP q) (J := jP q) (D := dP q)
      (by unfold jP; omega)
      (params_m_le (by omega))
      (params_budget_ii (by omega) hodd)
      (params_budget_i (by omega) hodd)

/-! ## 6. HEADLINES: the pipeline fires with zero named hypotheses -/

/-- **THE ROUND GOAL — UNCONDITIONAL generic-constant Hasse**: at EVERY finite field of
odd characteristic, `S² ≤ 169·q` uniformly over the Legendre cubic family.
`q ≤ 169` by the trivial bound, `q ≥ 171` by elementary Stepanov at the explicit
parameters (`q = 170` is even, so the split is exhaustive).  ZERO named hypotheses. -/
theorem legendreCubicHasseC_unconditional (hF : ringChar F ≠ 2) :
    LegendreCubicHasseC F 169 := by
  rcases Nat.lt_or_ge 169 (Fintype.card F) with hlarge | hsmall
  · have hodd : Odd (Fintype.card F) := odd_card_of_char_ne_two' hF
    have h171 : 171 ≤ Fintype.card F := by
      rcases hodd with ⟨t, ht⟩; omega
    exact legendreCubicHasseC_cases hF (Or.inr (s2OutputSized_holds hF h171))
  · exact legendreCubicHasseC_of_card_le hF (by exact_mod_cast hsmall)

/-- The tight version: `S² ≤ 49·q` for every odd-characteristic field with `q ≥ 3251`. -/
theorem legendreCubicHasseC_49_of_large (hF : ringChar F ≠ 2)
    (hq : 3251 ≤ Fintype.card F) :
    LegendreCubicHasseC F 49 :=
  legendreCubicHasseC_cases hF (Or.inr (s2OutputSized_holds_tight hF hq))

/-- **THE UNCONDITIONAL r=2 RUNG QUADRATIC FACE**: for every finite field of odd
characteristic and every `G` with `|G|⁴ ≤ q`,
`∑_s ‖T_{χ₂}(s)‖⁴ ≤ 17·|G|²·q`.  The entire round-19→23 Stepanov chain, closed. -/
theorem fourthMoment_quadChar_unconditional (hF : ringChar F ≠ 2)
    (G : Finset F) (hp : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ)) :
    ∑ s : F, ‖shiftedCharSum (quadCharC F) G s‖ ^ 4
      ≤ 17 * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ) := by
  have hsupply : (Fintype.card F : ℤ) ≤ (13 : ℤ) ^ 2 ∨ S2OutputSized F ((13 : ℤ) ^ 2) := by
    rcases Nat.lt_or_ge 169 (Fintype.card F) with hlarge | hsmall
    · have hodd : Odd (Fintype.card F) := odd_card_of_char_ne_two' hF
      have h171 : 171 ≤ Fintype.card F := by rcases hodd with ⟨t, ht⟩; omega
      refine Or.inr ?_
      rw [show ((13 : ℤ) ^ 2) = 169 by norm_num]
      exact s2OutputSized_holds hF h171
    · exact Or.inl (by exact_mod_cast hsmall)
  have := fourthMoment_quadChar_of_s2output_pipeline hF (k := 13) (by norm_num) hsupply G hp
  calc ∑ s : F, ‖shiftedCharSum (quadCharC F) G s‖ ^ 4
      ≤ (((13 : ℤ) : ℝ) + 4) * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ) := this
    _ = 17 * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ) := by norm_num

/-- The tight rung constant `Cw = 11` for `q ≥ 3251`. -/
theorem fourthMoment_quadChar_tight_of_large (hF : ringChar F ≠ 2)
    (hq : 3251 ≤ Fintype.card F)
    (G : Finset F) (hp : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ)) :
    ∑ s : F, ‖shiftedCharSum (quadCharC F) G s‖ ^ 4
      ≤ 11 * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ) := by
  have hsupply : (Fintype.card F : ℤ) ≤ (7 : ℤ) ^ 2 ∨ S2OutputSized F ((7 : ℤ) ^ 2) := by
    refine Or.inr ?_
    rw [show ((7 : ℤ) ^ 2) = 49 by norm_num]
    exact s2OutputSized_holds_tight hF hq
  have := fourthMoment_quadChar_of_s2output_pipeline hF (k := 7) (by norm_num) hsupply G hp
  calc ∑ s : F, ‖shiftedCharSum (quadCharC F) G s‖ ^ 4
      ≤ (((7 : ℤ) : ℝ) + 4) * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ) := this
    _ = 11 * (G.card : ℝ) ^ 2 * (Fintype.card F : ℝ) := by norm_num

end ArkLib.ProximityGap.Frontier.R23ParameterChoice

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R23ParameterChoice.params_budget_i
#print axioms ArkLib.ProximityGap.Frontier.R23ParameterChoice.params_budget_ii
#print axioms ArkLib.ProximityGap.Frontier.R23ParameterChoice.params_budget_iii
#print axioms ArkLib.ProximityGap.Frontier.R23ParameterChoice.params_budget_iii_tight
#print axioms ArkLib.ProximityGap.Frontier.R23ParameterChoice.pairing
#print axioms ArkLib.ProximityGap.Frontier.R23ParameterChoice.s2OutputSized_holds
#print axioms ArkLib.ProximityGap.Frontier.R23ParameterChoice.s2OutputSized_holds_tight
#print axioms
  ArkLib.ProximityGap.Frontier.R23ParameterChoice.legendreCubicHasseC_unconditional
#print axioms
  ArkLib.ProximityGap.Frontier.R23ParameterChoice.legendreCubicHasseC_49_of_large
#print axioms
  ArkLib.ProximityGap.Frontier.R23ParameterChoice.fourthMoment_quadChar_unconditional
#print axioms
  ArkLib.ProximityGap.Frontier.R23ParameterChoice.fourthMoment_quadChar_tight_of_large
