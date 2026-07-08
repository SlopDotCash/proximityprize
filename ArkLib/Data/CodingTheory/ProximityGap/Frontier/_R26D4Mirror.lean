/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R25D4Instantiate
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R25DirectClassCountPipeline

/-!
# LANE D4MIRROR (#466 round 26): the (m, J, D) numeric mirror at d = 4 —
# `TripleLinearHasseC` for order-4 characters, UNCONDITIONAL

Round 25 supplied the d = 4 face's per-fiber Stepanov count on the true (non-squarefree)
quintic kernel (`quintic_kernel_fiber_bound`) and the witness-free fold consumer
(`tripleLinearHasseC_of_directClassCount`).  This file is the `_R23ParameterChoice` mirror
at `d = 4`: it instantiates `(m, J, D)` explicitly, discharges every arithmetic side
condition, builds the two missing bridges (the character-fiber → power-fiber dictionary and
the kernel-shape decomposition for ALL nondegenerate tuples), and lands

* **`tripleLinearHasseC_d4_unconditional`** — for EVERY finite field and EVERY
  multiplicative character `χ` of order 4, `TripleLinearHasseC χ G 45`:
  `‖tripleSum χ u v w‖ ≤ 45·√q` at every nondegenerate tuple.  ZERO named hypotheses
  (`4 ∣ q − 1` and `Odd q` are consequences of `orderOf χ = 4`; `q ≤ 2025` closes by the
  trivial bound `‖S‖ ≤ q ≤ 45√q`).

## The optimization (probe `probe_r26_d4params.py`, 2026-07-08)

Minimizing the fold excess `4B − q` (`B` = per-class count) over admissible `(m, J, D)`
subject to the PROVEN r25 budgets (count `m(D+4m+J) < 4J(D+1)`, independence `4D+15 < q`,
`m < q`), with fiber supply `mB ≤ 5(m+3e) + D + q(J−1)`, `e = (q−1)/4`:

* the binding wall is the independence budget (`D` pushed to its cap `≈ q/4`); writing
  `J = m/4 + c` the excess is `≈ (12 + 4c)q/m + 23` with the count budget capping
  `m ≤ 2√(cq/17)`; the continuous optimum is `c = 3`, `m = 2√(3q/17) ≈ 0.840√q`, giving
  the achievable constant **`C₄* = 2√204 = 4√51 ≈ 28.566`** (the d = 4 analogue of round
  23's `C* = 2√10`; the `deg g = 5` face pays `15q/4` of excess through `5·3e` alone).
* grid probe: best `C₄` = 29.91 (q=1009), 28.97 (10007), 28.72 (10⁶+3) — converging to
  `2√204` from above.

## The explicit family (this file, all ℕ-valued; probe `probe_r26_d4family2.py`)

`s = √((q−16)/23)`, `m = 4s`, `J = s + 4`, `D = (q−16)/4`, `b = √(23q)`, `B = 9b ≈ 43.2√q`:
admissible for all `q ≡ 1 (mod 4)` with `q ≥ 2026`, rung constant `C₄ = 45`
(`(9b)² ≤ 1863q ≤ 2025q = (45√q)²`); `q ≤ 2025` closes by the trivial bound.  ZERO GAP.
(The count budget at `J = s + 4` is provable from `23s² ≤ q − 16` alone, all `s ≥ 1`;
probe-verified exactly, as stated with `Nat.sqrt` and floor division, for every
`q ≡ 1 (mod 4)` in `[17, 3·10⁶]`.)

## The two new bridges (both axiom-clean)

1. **Character-fiber dictionary** (`pow_div_ord_eq_one_of_chi_eq_one`,
   `chiFiber_subset_powerFiber`): for `χ` of order 4 and `x ≠ 0`, `χ x = 1` forces
   `x^((q−1)/4) = 1` (cyclicity of `Fˣ`: the kernel of `χ` is the unique index-4 subgroup
   = the 4th powers), hence every χ-fiber `{s : χ(g(s)) = c}` sits inside ONE power-fiber
   `{s : g(s)^((q−1)/4) = ζ}` — the r25 count supply applies verbatim.
2. **Kernel-shape decomposition** (`shape_decomp`): for every tuple `(u, v, w)` surviving
   the three R18 degeneracy clauses (`¬(u=w ∧ v=0)`, `¬(u=0 ∧ v=w)`, `¬(u=v ∧ w=0)`), the
   kernel `(us+1)(vs+1)(ws+1)³` equals `unit · (σ²r)(s)` pointwise with `r` SQUAREFREE of
   positive degree and `deg(σ²r) ≤ 5` — every one of the 11 coincidence patterns lands in
   the r25 `dBlockIndependence_four_sqmul` scope (the excluded patterns are exactly the
   perfect-4th-power/order-2 collapses, and they are exactly the degenerate tuples).

## What this buys (and honest scope)

With the round-24 weld, any family `X` of order-4 characters now gets
`FourthMomentTwistBound G X 49` unconditionally (`fourthMomentTwistBound_order4_family`);
for the tower subfamily `X₄ = {χ₂, χ₄, χ₄³}` the order-4 members are covered here at
`C₄ = 45` and the order-2 member by the round-23 chain — but the round-23 output is the
`quadChar` fourth-moment directly, not a `TripleLinearHasseC` for `χ₂`, so the single-`Cw`
statement for the MIXED family still needs either an order-2 instance of this file's fold
(same machinery, `T = {±1}`, `e = (q−1)/2` — no new mathematics) or a per-character
`FourthMomentTwistBound` combination lemma.  Recorded as the (only) residual; no closure
of the r = 2 rung claimed beyond the order-4 faces.  Issue #466, round 26, LANE D4MIRROR.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.R26D4Mirror

open ArkLib.ProximityGap.Frontier.R18FourthMomentTwist (mulChar_mul_conj IsDegenerate)
open ArkLib.ProximityGap.Frontier.R21HigherDFaces
open ArkLib.ProximityGap.Frontier.R22SuperellipticIndependence (DBlockIndependence)
open ArkLib.ProximityGap.Frontier.R24FullRungAssembly
open ArkLib.ProximityGap.Frontier.R24SuperellipticS2
open ArkLib.ProximityGap.Frontier.R25D4Instantiate

local notation "conj'" => starRingEnd ℂ

/-! ## 1. The explicit parameter family (all ℕ-valued) -/

/-- Base scale `s = ⌊√((q−16)/23)⌋ ≈ √(q/23)` (so `m = 4s ≈ 0.834√q`, just under the
continuous optimum `2√(3q/17) ≈ 0.840√q` of the d = 4 fold budget). -/
def s4P (q : ℕ) : ℕ := Nat.sqrt ((q - 16) / 23)

/-- Hasse-derivative order `m = 4s`. -/
def m4P (q : ℕ) : ℕ := 4 * s4P q

/-- Block count `J = s + 4 = m/4 + 4` (the `c = 4` offset makes the count budget provable
from `23s² ≤ q − 16` alone; the continuous optimum is `c = 3`). -/
def j4P (q : ℕ) : ℕ := s4P q + 4

/-- Per-block degree `D = (q−16)/4` — the independence-budget cap (`4D + 15 ≤ q − 1`). -/
def d4P (q : ℕ) : ℕ := (q - 16) / 4

/-- Auxiliary scale `b = ⌊√(23q)⌋` (reciprocal radicand to `s`: the pairing
`(s+1)(b+1) ≥ q − 8` is what makes the Nat-sqrt admissibility proof work). -/
def b4P (q : ℕ) : ℕ := Nat.sqrt (23 * q)

/-- The fold budget `B = 9b ≈ 43.2√q` (rung constant `C₄ = 45`, `81·23 = 1863 ≤ 2025`). -/
def bigB4 (q : ℕ) : ℕ := 9 * b4P q

/-- The total-degree supply produced by the r25 fiber bound at these parameters:
`Dtot = 5(m + 3e) + D + q(J−1)`, `e = (q−1)/4`. -/
def dtot4P (q : ℕ) : ℕ := 5 * (m4P q + 3 * ((q - 1) / 4)) + d4P q + q * (j4P q - 1)

/-! ## 2. Nat-sqrt bracketing -/

theorem s4_sq_le {q : ℕ} : 23 * (s4P q * s4P q) ≤ q - 16 := by
  have h1 : s4P q * s4P q ≤ (q - 16) / 23 := Nat.sqrt_le _
  calc 23 * (s4P q * s4P q) ≤ 23 * ((q - 16) / 23) := Nat.mul_le_mul_left _ h1
    _ ≤ q - 16 := Nat.mul_div_le _ _

theorem lt_s4_succ_sq {q : ℕ} : q - 16 < 23 * ((s4P q + 1) * (s4P q + 1)) := by
  have h1 : (q - 16) / 23 < (s4P q + 1) * (s4P q + 1) := Nat.lt_succ_sqrt _
  have h2 := Nat.div_add_mod (q - 16) 23
  have h3 : (q - 16) % 23 < 23 := Nat.mod_lt _ (by norm_num)
  set d := (q - 16) / 23
  set S := (s4P q + 1) * (s4P q + 1)
  omega

theorem b4_sq_le {q : ℕ} : b4P q * b4P q ≤ 23 * q := Nat.sqrt_le _

theorem lt_b4_succ_sq {q : ℕ} : 23 * q < (b4P q + 1) * (b4P q + 1) := Nat.lt_succ_sqrt _

theorem s4_pos {q : ℕ} (hq : 39 ≤ q) : 1 ≤ s4P q := by
  have : 1 * 1 ≤ (q - 16) / 23 := by
    have : 1 ≤ (q - 16) / 23 := Nat.le_div_iff_mul_le (by norm_num) |>.mpr (by omega)
    simpa using this
  exact Nat.le_sqrt.mpr this

/-- **The pairing lower bound** `(s+1)(b+1) ≥ q − 8`: the two sqrt floors multiply back up
to `q` because their radicands were chosen reciprocal (`(q−16)/23` and `23q`). -/
theorem pairing4 {q : ℕ} (hq : 64 ≤ q) : q ≤ (s4P q + 1) * (b4P q + 1) + 8 := by
  have hA : q ≤ 23 * ((s4P q + 1) * (s4P q + 1)) + 15 := by
    have := lt_s4_succ_sq (q := q); omega
  have hB : 23 * q + 1 ≤ (b4P q + 1) * (b4P q + 1) := lt_b4_succ_sq
  have hA' : (q : ℤ) ≤ 23 * (((s4P q : ℤ) + 1) * ((s4P q : ℤ) + 1)) + 15 := by
    exact_mod_cast hA
  have hB' : 23 * (q : ℤ) + 1 ≤ ((b4P q : ℤ) + 1) * ((b4P q : ℤ) + 1) := by
    exact_mod_cast hB
  have hq' : (64 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
  set x : ℤ := ((s4P q : ℤ) + 1) * ((b4P q : ℤ) + 1) with hx
  have hs0 : (0 : ℤ) ≤ (s4P q : ℤ) := Int.natCast_nonneg _
  have hb0 : (0 : ℤ) ≤ (b4P q : ℤ) := Int.natCast_nonneg _
  have hx0 : (0 : ℤ) ≤ x := by positivity
  have hxsq : ((q : ℤ) - 8) ^ 2 ≤ x ^ 2 := by nlinarith [hA', hB', hq', hs0, hb0]
  have hfin : (q : ℤ) - 8 ≤ x := by
    by_contra hcon
    push_neg at hcon
    have : x ^ 2 < ((q : ℤ) - 8) ^ 2 := by nlinarith
    linarith
  have hgoal : (q : ℤ) ≤ ((s4P q : ℤ) + 1) * ((b4P q : ℤ) + 1) + 8 := by
    rw [hx] at hfin; linarith
  exact_mod_cast hgoal

/-- The key scale comparison: `32s + 9b + 73 ≤ 2q` for `q ≥ 2026` (both `s ≈ 0.209√q`
and `b ≈ 4.80√q` are `o(q)`; numerically true from `q ≈ 800`). -/
theorem key_scale4 {q : ℕ} (hq : 2026 ≤ q) : 32 * s4P q + 9 * b4P q + 73 ≤ 2 * q := by
  have hs23 : 23 * (s4P q * s4P q) ≤ q - 16 := s4_sq_le
  have hb : b4P q * b4P q ≤ 23 * q := b4_sq_le
  have hs23n : 23 * (s4P q * s4P q) + 16 ≤ q := by omega
  have hs' : 23 * ((s4P q : ℤ) * (s4P q : ℤ)) + 16 ≤ (q : ℤ) := by exact_mod_cast hs23n
  have hb' : ((b4P q : ℤ)) * ((b4P q : ℤ)) ≤ 23 * (q : ℤ) := by exact_mod_cast hb
  have hq' : (2026 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
  have goal' : 32 * (s4P q : ℤ) + 9 * (b4P q : ℤ) + 73 ≤ 2 * (q : ℤ) := by
    nlinarith [sq_nonneg ((b4P q : ℤ) - 207), sq_nonneg (23 * (s4P q : ℤ) - 100),
      Int.natCast_nonneg (s4P q), Int.natCast_nonneg (b4P q)]
  exact_mod_cast goal'

/-! ## 3. The budget theorems -/

/-- **Budget (i)** — the d = 4 rank-nullity count `m(D + 4m + J) < 4J(D+1)`.
At our family (`J = s + 4`) this is provable from `23s² ≤ q − 16` alone. -/
theorem params4_count {q : ℕ} (hq : 39 ≤ q) (h4 : q % 4 = 1) :
    m4P q * (d4P q + 4 * m4P q + j4P q) < 4 * (j4P q * (d4P q + 1)) := by
  obtain ⟨t, ht⟩ : ∃ t, q = 4 * t + 1 := ⟨q / 4, by omega⟩
  have hs23 : 23 * (s4P q * s4P q) ≤ q - 16 := s4_sq_le
  have hs1 : 1 ≤ s4P q := s4_pos hq
  have hd : d4P q = t - 4 := by unfold d4P; omega
  have ht4 : 9 ≤ t := by omega
  obtain ⟨u, hu⟩ : ∃ u, t = u + 4 := ⟨t - 4, by omega⟩
  have hdu : d4P q = u := by omega
  rw [hdu]
  show 4 * s4P q * (u + 4 * (4 * s4P q) + (s4P q + 4)) < 4 * ((s4P q + 4) * (u + 1))
  -- 23 s² ≤ 4t − 15 = 4u + 1 ⟹ 68 s² + 12 s < 16 u + 16
  have hkey : 23 * (s4P q * s4P q) ≤ 4 * u + 1 := by omega
  nlinarith [hkey, hs1, Nat.zero_le (s4P q)]

/-- **Budget (ii)** — the independence budget at the cap: `4D + 15 < q`. -/
theorem params4_indep {q : ℕ} (hq : 17 ≤ q) (h4 : q % 4 = 1) :
    4 * d4P q + 15 < q := by
  unfold d4P; omega

/-- The order bound `m < q`. -/
theorem params4_m_lt {q : ℕ} (hq : 39 ≤ q) : m4P q < q := by
  have hs23 : 23 * (s4P q * s4P q) ≤ q - 16 := s4_sq_le
  have hs1 : 1 ≤ s4P q := s4_pos hq
  have : 4 * s4P q ≤ 23 * (s4P q * s4P q) := by nlinarith
  unfold m4P
  omega

/-- The admissibility core, in ℤ (linear in the atoms `s, b, t, s·b`). -/
theorem admiss_core4 {s b t q : ℤ} (hq : q = 4 * t + 1)
    (hpair : q ≤ (s + 1) * (b + 1) + 8)
    (hkey : 32 * s + 9 * b + 73 ≤ 2 * q) :
    92 * s + 112 * t - 4 ≤ 36 * (s * b) := by
  have h1 : (s + 1) * (b + 1) = s * b + s + b + 1 := by ring
  linarith [hpair, hkey, h1.symm.le, h1.le]

/-- **Budget (iii)** — fold admissibility of `B = 9b`:
`4·Dtot ≤ m·(B + (q − 3))` for all `q ≡ 1 (mod 4)`, `q ≥ 2026`. -/
theorem params4_admiss {q : ℕ} (hq : 2026 ≤ q) (h4 : q % 4 = 1) :
    4 * dtot4P q ≤ m4P q * (bigB4 q + (q - 3)) := by
  obtain ⟨t, ht⟩ : ∃ t, q = 4 * t + 1 := ⟨q / 4, by omega⟩
  have he : (q - 1) / 4 = t := by omega
  have hd : d4P q = t - 4 := by unfold d4P; omega
  have hj : j4P q - 1 = s4P q + 3 := by unfold j4P; omega
  have hpairN : q ≤ (s4P q + 1) * (b4P q + 1) + 8 := pairing4 (by omega)
  have hkeyN : 32 * s4P q + 9 * b4P q + 73 ≤ 2 * q := key_scale4 hq
  have hcore := admiss_core4 (s := (s4P q : ℤ)) (b := (b4P q : ℤ)) (t := (t : ℤ))
    (q := (q : ℤ)) (by exact_mod_cast ht)
    (by exact_mod_cast hpairN) (by exact_mod_cast hkeyN)
  -- unfold and cast
  unfold dtot4P m4P bigB4
  rw [he, hd, hj]
  have ht9 : 9 ≤ t := by omega
  obtain ⟨u, hu⟩ : ∃ u, t = u + 4 := ⟨t - 4, by omega⟩
  have hgoalZ : 4 * (5 * (4 * (s4P q : ℤ) + 3 * (t : ℤ)) + ((t : ℤ) - 4)
      + (q : ℤ) * ((s4P q : ℤ) + 3))
      ≤ 4 * (s4P q : ℤ) * (9 * (b4P q : ℤ) + ((q : ℤ) - 3)) := by
    have hqz : (q : ℤ) = 4 * (t : ℤ) + 1 := by exact_mod_cast ht
    nlinarith [hcore, hqz.le, hqz.ge]
  have hq3 : (3 : ℕ) ≤ q := by omega
  have hgoalZ' : 4 * (5 * (4 * (s4P q : ℤ) + 3 * (t : ℤ)) + (((t - 4 : ℕ)) : ℤ)
      + (q : ℤ) * ((s4P q : ℤ) + 3))
      ≤ 4 * (s4P q : ℤ) * (9 * (b4P q : ℤ) + (((q - 3 : ℕ)) : ℤ)) := by
    have h1 : (((t - 4 : ℕ)) : ℤ) = (t : ℤ) - 4 := by omega
    have h2 : (((q - 3 : ℕ)) : ℤ) = (q : ℤ) - 3 := by omega
    rw [h1, h2]
    exact hgoalZ
  have := hgoalZ'
  have hd' : (t : ℕ) - 4 = u := by omega
  exact_mod_cast hgoalZ'

/-- The square bound: `(9b)² = 81b² ≤ 1863q ≤ 2025q = (45)²q`. -/
theorem bigB4_sq_le {q : ℕ} : bigB4 q * bigB4 q ≤ 2025 * q := by
  have hb : b4P q * b4P q ≤ 23 * q := b4_sq_le
  unfold bigB4
  nlinarith [hb, Nat.zero_le q]

/-! ## 4. Field-level supply: the real-valued fold arithmetic -/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `B = 9b ≤ 45√q` in ℝ. -/
theorem bigB4_le_sqrt {q : ℕ} : (bigB4 q : ℝ) ≤ 45 * Real.sqrt q := by
  have h : (bigB4 q : ℝ) ^ 2 ≤ 2025 * (q : ℝ) := by
    have := bigB4_sq_le (q := q)
    have : ((bigB4 q * bigB4 q : ℕ) : ℝ) ≤ ((2025 * q : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this
    nlinarith [this]
  have h45 : (45 : ℝ) * Real.sqrt q = Real.sqrt (2025 * q) := by
    rw [show (2025 : ℝ) = 45 ^ 2 by norm_num, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by norm_num)]
  rw [h45]
  have hb0 : (0 : ℝ) ≤ (bigB4 q : ℝ) := by positivity
  calc (bigB4 q : ℝ) = Real.sqrt ((bigB4 q : ℝ) ^ 2) := (Real.sqrt_sq hb0).symm
    _ ≤ Real.sqrt (2025 * (q : ℝ)) := Real.sqrt_le_sqrt h

/-- **The fold arithmetic** at the explicit family: for `q ≡ 1 (mod 4)`, `q ≥ 2026`,
`4·(Dtot/m) − q + 3 ≤ 45√q`. -/
theorem d4_fold_arith (hq : 2026 ≤ Fintype.card F)
    (h4 : Fintype.card F % 4 = 1) :
    (4 : ℝ) * ((dtot4P (Fintype.card F) : ℝ) / (m4P (Fintype.card F) : ℝ))
      - (Fintype.card F : ℝ) + 3 ≤ 45 * Real.sqrt (Fintype.card F) := by
  set q := Fintype.card F with hqdef
  have hm0 : 0 < m4P q := by
    have := s4_pos (q := q) (by omega); unfold m4P; omega
  have hm' : (0 : ℝ) < (m4P q : ℝ) := by exact_mod_cast hm0
  have hadm := params4_admiss (q := q) hq h4
  have hadm' : 4 * (dtot4P q : ℝ) ≤ (m4P q : ℝ) * ((bigB4 q : ℝ) + ((q : ℝ) - 3)) := by
    have : ((4 * dtot4P q : ℕ) : ℝ) ≤ ((m4P q * (bigB4 q + (q - 3)) : ℕ) : ℝ) := by
      exact_mod_cast hadm
    push_cast at this
    have hq3 : ((q - 3 : ℕ) : ℝ) = (q : ℝ) - 3 := by
      have : 3 ≤ q := by omega
      push_cast [Nat.cast_sub this]
      ring
    rw [hq3] at this
    linarith [this]
  have hdiv : (4 : ℝ) * ((dtot4P q : ℝ) / (m4P q : ℝ)) ≤ (bigB4 q : ℝ) + ((q : ℝ) - 3) := by
    rw [← mul_div_assoc, div_le_iff₀ hm']
    calc (4 : ℝ) * (dtot4P q : ℝ) ≤ (m4P q : ℝ) * ((bigB4 q : ℝ) + ((q : ℝ) - 3)) := hadm'
      _ = ((bigB4 q : ℝ) + ((q : ℝ) - 3)) * (m4P q : ℝ) := by ring
  have := bigB4_le_sqrt (q := q)
  linarith

/-! ## 5. Order-4 character values: the class set `T₄ = μ₄ ⊂ ℂ` -/

/-- The four 4th roots of unity in ℂ. -/
noncomputable def T4 : Finset ℂ := {1, Complex.I, -1, -Complex.I}

theorem I_ne_one : (Complex.I : ℂ) ≠ 1 := by
  intro h
  have := congrArg Complex.im h
  norm_num at this

theorem T4_card : T4.card = 4 := by
  have h1 : (1 : ℂ) ≠ Complex.I := fun h => I_ne_one h.symm
  have h2 : (1 : ℂ) ≠ -1 := by norm_num
  have h3 : (1 : ℂ) ≠ -Complex.I := by
    intro h
    have := congrArg Complex.im h
    norm_num at this
  have h4 : (Complex.I : ℂ) ≠ -1 := by
    intro h
    have := congrArg Complex.im h
    norm_num at this
  have h5 : (Complex.I : ℂ) ≠ -Complex.I := by
    intro h
    have := congrArg Complex.im h
    norm_num at this
  have h6 : (-1 : ℂ) ≠ -Complex.I := by
    intro h
    have := congrArg Complex.im h
    norm_num at this
  unfold T4
  rw [Finset.card_insert_of_notMem (by simp [h1, h2, h3]),
    Finset.card_insert_of_notMem (by simp [h4, h5]),
    Finset.card_insert_of_notMem (by simp [h6]),
    Finset.card_singleton]

theorem T4_norm (c : ℂ) (hc : c ∈ T4) : ‖c‖ = 1 := by
  unfold T4 at hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> simp

theorem T4_sum : (∑ c ∈ T4, c) = 0 := by
  have h1 : (1 : ℂ) ∉ ({Complex.I, -1, -Complex.I} : Finset ℂ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    refine ⟨fun h => I_ne_one h.symm, by norm_num, ?_⟩
    intro h
    have := congrArg Complex.im h
    norm_num at this
  have h2 : (Complex.I : ℂ) ∉ ({-1, -Complex.I} : Finset ℂ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    push_neg
    constructor
    · intro h
      have := congrArg Complex.im h
      norm_num at this
    · intro h
      have := congrArg Complex.im h
      norm_num at this
  have h3 : (-1 : ℂ) ∉ ({-Complex.I} : Finset ℂ) := by
    simp only [Finset.mem_singleton]
    intro h
    have := congrArg Complex.im h
    norm_num at this
  unfold T4
  rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_insert h3,
    Finset.sum_singleton]
  ring

theorem mem_T4_of_pow_four {z : ℂ} (hz : z ^ 4 = 1) : z ∈ T4 := by
  have hsplit : (z ^ 2 - 1) * (z ^ 2 + 1) = 0 := by linear_combination hz
  unfold T4
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases mul_eq_zero.mp hsplit with h | h
  · have h2 : (z - 1) * (z + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h' | h'
    · exact Or.inl (by linear_combination h')
    · exact Or.inr (Or.inr (Or.inl (by linear_combination h')))
  · have h2 : (z - Complex.I) * (z + Complex.I) = 0 := by
      have hI : Complex.I ^ 2 = -1 := Complex.I_sq
      linear_combination h - hI
    rcases mul_eq_zero.mp h2 with h' | h'
    · exact Or.inr (Or.inl (by linear_combination h'))
    · exact Or.inr (Or.inr (Or.inr (by linear_combination h')))

variable {χ : MulChar F ℂ}

/-- Order-4 characters take 4th-root-of-unity values on nonzero arguments. -/
theorem chi_pow_four (hχ : orderOf χ = 4) {x : F} (hx : x ≠ 0) : (χ x) ^ 4 = 1 := by
  have h1 : χ ^ 4 = 1 := by
    rw [← hχ]
    exact pow_orderOf_eq_one χ
  calc (χ x) ^ 4 = (χ ^ 4) x := (MulChar.pow_apply' χ (n := 4) (by norm_num) x).symm
    _ = (1 : MulChar F ℂ) x := by rw [h1]
    _ = 1 := MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)

theorem chi_ne_zero {x : F} (hx : x ≠ 0) : χ x ≠ 0 :=
  left_ne_zero_of_mul_eq_one (mulChar_mul_conj χ hx)

theorem chi_mem_T4 (hχ : orderOf χ = 4) {x : F} (hx : x ≠ 0) : χ x ∈ T4 :=
  mem_T4_of_pow_four (chi_pow_four hχ hx)

/-- `conj (χ x) = (χ x)³` for order-4 `χ` and `x ≠ 0` (inverse of a 4th root of unity). -/
theorem conj_chi_eq_cube (hχ : orderOf χ = 4) {x : F} (hx : x ≠ 0) :
    conj' (χ x) = (χ x) ^ 3 := by
  have h1 : χ x * conj' (χ x) = 1 := mulChar_mul_conj χ hx
  have h4 : χ x * (χ x) ^ 3 = 1 := by
    have := chi_pow_four hχ hx
    calc χ x * (χ x) ^ 3 = (χ x) ^ 4 := by ring
      _ = 1 := this
  exact mul_left_cancel₀ (chi_ne_zero hx) (h1.trans h4.symm)

/-- **The kernel identity**: for order-4 `χ`,
`tripleVal χ u v w s = χ((us+1)(vs+1)·(ws+1)³)` — at every point (both sides vanish when
a factor does). -/
theorem tripleVal_eq_kernel (hχ : orderOf χ = 4) (u v w s : F) :
    tripleVal χ u v w s = χ ((u * s + 1) * (v * s + 1) * (w * s + 1) ^ 3) := by
  by_cases hw0 : w * s + 1 = 0
  · have hz : χ (0 : F) = 0 := χ.map_nonunit (by simp)
    rw [tripleVal, hw0]
    simp [hz]
  · rw [tripleVal, conj_chi_eq_cube hχ hw0, ← map_pow, ← map_mul]

/-- `tripleVal` values lie in `{0} ∪ T₄` for order-4 `χ`. -/
theorem tripleVal_mem (hχ : orderOf χ = 4) (u v w s : F) :
    tripleVal χ u v w s = 0 ∨ tripleVal χ u v w s ∈ T4 := by
  rw [tripleVal_eq_kernel hχ]
  by_cases h : (u * s + 1) * (v * s + 1) * (w * s + 1) ^ 3 = 0
  · left
    rw [h]
    exact χ.map_nonunit (by simp)
  · right
    exact chi_mem_T4 hχ h

/-! ## 6. The character-fiber → power-fiber dictionary -/

/-- **The dictionary core**: for `χ` of order 4 on a finite field, `χ x = 1` (`x ≠ 0`)
forces `x^((q−1)/4) = 1` — the kernel of `χ` is the unique index-4 subgroup of the cyclic
`Fˣ`, i.e. the 4th powers. -/
theorem pow_div_ord_eq_one_of_chi_eq_one (hχ : orderOf χ = 4) {x : F} (hx : x ≠ 0)
    (h1 : χ x = 1) : x ^ ((Fintype.card F - 1) / 4) = 1 := by
  have h4 : 4 ∣ Fintype.card F - 1 := hχ ▸ MulChar.orderOf_dvd_card_sub_one F χ
  obtain ⟨g0, hg0⟩ := IsCyclic.exists_generator (α := Fˣ)
  set ux : Fˣ := Units.mk0 x hx with huxdef
  obtain ⟨k, hk0⟩ := (mem_powers_iff_mem_zpowers).mpr (hg0 ux)
  have hk : g0 ^ k = ux := hk0
  set ω : ℂ := χ ↑g0 with hωdef
  have hg0ne : ((g0 : F)) ≠ 0 := Units.ne_zero g0
  have hω4 : ω ^ 4 = 1 := chi_pow_four hχ hg0ne
  -- orderOf ω = 4
  have hωdvd : orderOf ω ∣ 4 := orderOf_dvd_of_pow_eq_one hω4
  have hωpos : 0 < orderOf ω := by
    rcases Nat.eq_zero_or_pos (orderOf ω) with h0 | hp
    · rw [h0] at hωdvd
      omega
    · exact hp
  have hωsq_ne : ω ^ 2 ≠ 1 := by
    intro hω2
    have hχ2 : χ ^ 2 = 1 := by
      refine MulChar.ext fun a => ?_
      obtain ⟨j, hj⟩ := (mem_powers_iff_mem_zpowers).mpr (hg0 a)
      have hval : χ ↑a = ω ^ j := by
        rw [← hj]
        push_cast
        rw [map_pow]
      calc (χ ^ 2) ↑a = (χ ↑a) ^ 2 := MulChar.pow_apply' χ (n := 2) (by norm_num) _
        _ = (ω ^ j) ^ 2 := by rw [hval]
        _ = (ω ^ 2) ^ j := by ring
        _ = 1 := by rw [hω2, one_pow]
        _ = (1 : MulChar F ℂ) ↑a := (MulChar.one_apply_coe a).symm
    have : orderOf χ ∣ 2 := orderOf_dvd_of_pow_eq_one hχ2
    rw [hχ] at this
    omega
  have hωord : orderOf ω = 4 := by
    have hle : orderOf ω ≤ 4 := Nat.le_of_dvd (by norm_num) hωdvd
    have h124 : orderOf ω = 1 ∨ orderOf ω = 2 ∨ orderOf ω = 4 := by
      interval_cases (orderOf ω) <;> revert hωdvd <;> decide
    rcases h124 with h1 | h2 | h4'
    · exfalso
      apply hωsq_ne
      have hone : ω = 1 := by
        have := pow_orderOf_eq_one ω
        rwa [h1, pow_one] at this
      rw [hone, one_pow]
    · exfalso
      apply hωsq_ne
      have := pow_orderOf_eq_one ω
      rwa [h2] at this
    · exact h4'
  -- χ x = ω^k = 1 ⟹ 4 ∣ k
  have hxval : χ x = ω ^ k := by
    have hxeq : x = ((g0 ^ k : Fˣ) : F) := by
      rw [hk, huxdef]
      rfl
    rw [hxeq]
    push_cast
    rw [map_pow]
  have hωk : ω ^ k = 1 := hxval ▸ h1
  have h4k : 4 ∣ k := hωord ▸ orderOf_dvd_of_pow_eq_one hωk
  obtain ⟨k', hk'⟩ := h4k
  -- x^e = g0^(k·e) = g0^(k'(q−1)) = 1
  set e : ℕ := (Fintype.card F - 1) / 4 with hedef
  have h4e : 4 * e = Fintype.card F - 1 := Nat.mul_div_cancel' h4
  have hcard : g0 ^ (Fintype.card F - 1) = 1 := by
    have h : g0 ^ Fintype.card (Fˣ) = 1 := pow_card_eq_one
    rwa [Fintype.card_units] at h
  have hux_pow : (g0 ^ k) ^ e = 1 := by
    rw [← pow_mul, hk', mul_comm 4 k', mul_assoc, h4e, mul_comm k' (Fintype.card F - 1),
      pow_mul, hcard, one_pow]
  have hxval' : x ^ e = ((ux ^ e : Fˣ) : F) := by
    rw [huxdef]
    rw [Units.val_pow_eq_pow_val, Units.val_mk0]
  rw [hxval', ← hk, hux_pow, Units.val_one]

/-- **The fiber dictionary**: every χ-fiber of a polynomial value map sits inside ONE
power-fiber (`e = (q−1)/4`). -/
theorem chiFiber_subset_powerFiber (hχ : orderOf χ = 4) (g : F[X]) {c : ℂ} (hc : c ≠ 0) :
    ∃ ζ : F, (Finset.univ.filter fun s : F => χ (g.eval s) = c)
      ⊆ Finset.univ.filter fun s : F =>
          (g.eval s) ^ ((Fintype.card F - 1) / 4) = ζ := by
  by_cases hne : (Finset.univ.filter fun s : F => χ (g.eval s) = c).Nonempty
  · obtain ⟨s₀, hs₀⟩ := hne
    have hx₀ : χ (g.eval s₀) = c := (Finset.mem_filter.mp hs₀).2
    have hx₀ne : g.eval s₀ ≠ 0 := by
      intro h
      rw [h] at hx₀
      exact hc (hx₀.symm.trans (χ.map_nonunit (by simp)))
    refine ⟨(g.eval s₀) ^ ((Fintype.card F - 1) / 4), fun s hs => ?_⟩
    have hx : χ (g.eval s) = c := (Finset.mem_filter.mp hs).2
    have hxne : g.eval s ≠ 0 := by
      intro h
      rw [h] at hx
      exact hc (hx.symm.trans (χ.map_nonunit (by simp)))
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    -- χ(x·x₀⁻¹) = 1
    have hinv : χ ((g.eval s₀)⁻¹) = c⁻¹ := by
      have h1 : χ (g.eval s₀) * χ ((g.eval s₀)⁻¹) = 1 := by
        rw [← map_mul, mul_inv_cancel₀ hx₀ne, map_one]
      rw [hx₀] at h1
      field_simp at h1 ⊢
      linear_combination h1
    have hquot : χ (g.eval s * (g.eval s₀)⁻¹) = 1 := by
      rw [map_mul, hx, hinv, mul_inv_cancel₀ hc]
    have hquotne : g.eval s * (g.eval s₀)⁻¹ ≠ 0 :=
      mul_ne_zero hxne (inv_ne_zero hx₀ne)
    have hpow := pow_div_ord_eq_one_of_chi_eq_one hχ hquotne hquot
    rw [mul_pow, inv_pow] at hpow
    have hx₀epos : (g.eval s₀) ^ ((Fintype.card F - 1) / 4) ≠ 0 := pow_ne_zero _ hx₀ne
    field_simp at hpow
    exact hpow
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    exact ⟨1, by rw [hne]; exact Finset.empty_subset _⟩

/-! ## 7. The kernel-shape decomposition (all nondegenerate tuples) -/

/-- Squarefree: a single monic linear. -/
theorem sf_one (a : F) : Squarefree (X - C a : F[X]) :=
  (separable_X_sub_C (x := a)).squarefree

/-- Squarefree: product of two distinct monic linears. -/
theorem sf_two {a b : F} (hab : a ≠ b) : Squarefree ((X - C a) * (X - C b) : F[X]) := by
  have h1 : a ∉ ({b} : Finset F) := by simp [hab]
  have hprod : (∏ x ∈ ({a, b} : Finset F), (X - C x)) = (X - C a) * (X - C b) := by
    rw [Finset.prod_insert h1, Finset.prod_singleton]
  rw [← hprod]
  exact (separable_prod_X_sub_C_iff'.mpr fun x _ y _ h => h).squarefree

/-- Negated-inverse roots stay distinct. -/
theorem neg_inv_ne {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) :
    -x⁻¹ ≠ -y⁻¹ := by
  intro h
  exact hxy (inv_injective (neg_injective h))

/-- **The shape decomposition**: every tuple `(u, v, w)` surviving the three degeneracy
clauses has kernel `(us+1)(vs+1)(ws+1)³ = unit · (σ²r)(s)` with `σ²r` monic of degree
in `[1, 5]` and `r` squarefree of positive degree. -/
theorem shape_decomp (u v w : F)
    (h1 : ¬(u = w ∧ v = 0)) (h2 : ¬(u = 0 ∧ v = w)) (h3 : ¬(u = v ∧ w = 0)) :
    ∃ (σ r : F[X]) (κ : F), κ ≠ 0 ∧
      (∀ s : F, (u * s + 1) * (v * s + 1) * (w * s + 1) ^ 3
        = κ * (σ ^ 2 * r).eval s) ∧
      (σ ^ 2 * r).Monic ∧ Squarefree r ∧ 0 < r.natDegree ∧ σ ≠ 0 ∧
      (σ ^ 2 * r).natDegree ≤ 5 := by
  classical
  by_cases hu : u = 0
  · by_cases hv : v = 0
    · by_cases hw : w = 0
      · exact absurd ⟨hu.trans hw.symm, hv⟩ h1
      · -- kernel (ws+1)³ : σ = L_w, r = L_w
        refine ⟨X - C (-w⁻¹), X - C (-w⁻¹), w ^ 3, pow_ne_zero _ hw, ?_, ?_,
          sf_one _, by rw [natDegree_X_sub_C]; norm_num, X_sub_C_ne_zero _, ?_⟩
        · intro s
          simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, hu, hv]
          field_simp
          ring
        · exact ((monic_X_sub_C _).pow 2).mul (monic_X_sub_C _)
        · calc ((X - C (-w⁻¹)) ^ 2 * (X - C (-w⁻¹)) : F[X]).natDegree
              ≤ ((X - C (-w⁻¹) : F[X]) ^ 2).natDegree + (X - C (-w⁻¹) : F[X]).natDegree :=
                natDegree_mul_le
            _ ≤ 2 * (X - C (-w⁻¹) : F[X]).natDegree + (X - C (-w⁻¹) : F[X]).natDegree := by
                have := natDegree_pow_le (p := (X - C (-w⁻¹) : F[X])) (n := 2)
                omega
            _ ≤ 5 := by norm_num [natDegree_X_sub_C]
    · by_cases hw : w = 0
      · -- kernel (vs+1) : σ = 1, r = L_v
        refine ⟨1, X - C (-v⁻¹), v, hv, ?_, ?_, sf_one _,
          by rw [natDegree_X_sub_C]; norm_num, one_ne_zero, ?_⟩
        · intro s
          simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, eval_one, one_pow,
            one_mul, hu, hw]
          field_simp
          ring
        · simpa using monic_X_sub_C (-v⁻¹ : F)
        · simp [natDegree_X_sub_C]
      · -- kernel (vs+1)(ws+1)³, v ≠ w from h2 : σ = L_w, r = L_v·L_w
        have hvw : v ≠ w := fun h => h2 ⟨hu, h⟩
        refine ⟨X - C (-w⁻¹), (X - C (-v⁻¹)) * (X - C (-w⁻¹)), v * w ^ 3,
          mul_ne_zero hv (pow_ne_zero _ hw), ?_, ?_,
          sf_two (neg_inv_ne hv hw hvw), ?_, X_sub_C_ne_zero _, ?_⟩
        · intro s
          simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, hu]
          field_simp
          ring
        · exact ((monic_X_sub_C _).pow 2).mul ((monic_X_sub_C _).mul (monic_X_sub_C _))
        · rw [natDegree_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _),
            natDegree_X_sub_C, natDegree_X_sub_C]
          norm_num
        · calc ((X - C (-w⁻¹)) ^ 2 * ((X - C (-v⁻¹)) * (X - C (-w⁻¹))) : F[X]).natDegree
              ≤ ((X - C (-w⁻¹) : F[X]) ^ 2).natDegree
                + ((X - C (-v⁻¹)) * (X - C (-w⁻¹)) : F[X]).natDegree := natDegree_mul_le
            _ ≤ 2 * (X - C (-w⁻¹) : F[X]).natDegree
                + ((X - C (-v⁻¹) : F[X]).natDegree + (X - C (-w⁻¹) : F[X]).natDegree) := by
                have h1 := natDegree_pow_le (p := (X - C (-w⁻¹) : F[X])) (n := 2)
                have h2 := natDegree_mul_le (p := (X - C (-v⁻¹) : F[X]))
                  (q := (X - C (-w⁻¹) : F[X]))
                omega
            _ ≤ 5 := by simp [natDegree_X_sub_C]
  · by_cases hv : v = 0
    · by_cases hw : w = 0
      · -- kernel (us+1) : σ = 1, r = L_u
        refine ⟨1, X - C (-u⁻¹), u, hu, ?_, ?_, sf_one _,
          by rw [natDegree_X_sub_C]; norm_num, one_ne_zero, ?_⟩
        · intro s
          simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, eval_one, one_pow,
            one_mul, hv, hw]
          field_simp
          ring
        · simpa using monic_X_sub_C (-u⁻¹ : F)
        · simp [natDegree_X_sub_C]
      · -- kernel (us+1)(ws+1)³, u ≠ w from h1 : σ = L_w, r = L_u·L_w
        have huw : u ≠ w := fun h => h1 ⟨h, hv⟩
        refine ⟨X - C (-w⁻¹), (X - C (-u⁻¹)) * (X - C (-w⁻¹)), u * w ^ 3,
          mul_ne_zero hu (pow_ne_zero _ hw), ?_, ?_,
          sf_two (neg_inv_ne hu hw huw), ?_, X_sub_C_ne_zero _, ?_⟩
        · intro s
          simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, hv]
          field_simp
          ring
        · exact ((monic_X_sub_C _).pow 2).mul ((monic_X_sub_C _).mul (monic_X_sub_C _))
        · rw [natDegree_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _),
            natDegree_X_sub_C, natDegree_X_sub_C]
          norm_num
        · calc ((X - C (-w⁻¹)) ^ 2 * ((X - C (-u⁻¹)) * (X - C (-w⁻¹))) : F[X]).natDegree
              ≤ ((X - C (-w⁻¹) : F[X]) ^ 2).natDegree
                + ((X - C (-u⁻¹)) * (X - C (-w⁻¹)) : F[X]).natDegree := natDegree_mul_le
            _ ≤ 2 * (X - C (-w⁻¹) : F[X]).natDegree
                + ((X - C (-u⁻¹) : F[X]).natDegree + (X - C (-w⁻¹) : F[X]).natDegree) := by
                have h1' := natDegree_pow_le (p := (X - C (-w⁻¹) : F[X])) (n := 2)
                have h2' := natDegree_mul_le (p := (X - C (-u⁻¹) : F[X]))
                  (q := (X - C (-w⁻¹) : F[X]))
                omega
            _ ≤ 5 := by simp [natDegree_X_sub_C]
    · by_cases hw : w = 0
      · -- kernel (us+1)(vs+1), u ≠ v from h3 : σ = 1, r = L_u·L_v
        have huv : u ≠ v := fun h => h3 ⟨h, hw⟩
        refine ⟨1, (X - C (-u⁻¹)) * (X - C (-v⁻¹)), u * v, mul_ne_zero hu hv, ?_, ?_,
          sf_two (neg_inv_ne hu hv huv), ?_, one_ne_zero, ?_⟩
        · intro s
          simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, eval_one, one_pow,
            one_mul, hw]
          field_simp
          ring
        · simpa using (monic_X_sub_C (-u⁻¹ : F)).mul (monic_X_sub_C (-v⁻¹ : F))
        · rw [natDegree_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _),
            natDegree_X_sub_C, natDegree_X_sub_C]
          norm_num
        · have := natDegree_mul_le (p := (X - C (-u⁻¹) : F[X])) (q := (X - C (-v⁻¹) : F[X]))
          calc ((1 : F[X]) ^ 2 * ((X - C (-u⁻¹)) * (X - C (-v⁻¹)))).natDegree
              = ((X - C (-u⁻¹)) * (X - C (-v⁻¹)) : F[X]).natDegree := by
                rw [one_pow, one_mul]
            _ ≤ 5 := by
                simp only [natDegree_X_sub_C] at this ⊢
                omega
      · -- all nonzero: coincidence sub-cases
        by_cases huv : u = v
        · by_cases huw : u = w
          · -- u = v = w : kernel L_u⁵ : σ = L_u², r = L_u
            refine ⟨(X - C (-u⁻¹)) ^ 2, X - C (-u⁻¹), u * v * w ^ 3,
              by simp [mul_ne_zero, hu, hv, pow_ne_zero, hw], ?_, ?_, sf_one _,
              by rw [natDegree_X_sub_C]; norm_num, pow_ne_zero _ (X_sub_C_ne_zero _), ?_⟩
            · intro s
              simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, ← huv, ← huw]
              field_simp
              ring
            · exact ((monic_X_sub_C _).pow 2).pow 2 |>.mul (monic_X_sub_C _)
            · calc (((X - C (-u⁻¹)) ^ 2) ^ 2 * (X - C (-u⁻¹)) : F[X]).natDegree
                  ≤ (((X - C (-u⁻¹) : F[X]) ^ 2) ^ 2).natDegree
                    + (X - C (-u⁻¹) : F[X]).natDegree := natDegree_mul_le
                _ ≤ 2 * ((X - C (-u⁻¹) : F[X]) ^ 2).natDegree
                    + (X - C (-u⁻¹) : F[X]).natDegree := by
                    have := natDegree_pow_le (p := ((X - C (-u⁻¹) : F[X]) ^ 2)) (n := 2)
                    omega
                _ ≤ 2 * (2 * (X - C (-u⁻¹) : F[X]).natDegree)
                    + (X - C (-u⁻¹) : F[X]).natDegree := by
                    have := natDegree_pow_le (p := (X - C (-u⁻¹) : F[X])) (n := 2)
                    omega
                _ ≤ 5 := by norm_num [natDegree_X_sub_C]
          · -- u = v ≠ w : kernel L_u²L_w³ : σ = L_u·L_w, r = L_w
            refine ⟨(X - C (-u⁻¹)) * (X - C (-w⁻¹)), X - C (-w⁻¹), u * v * w ^ 3,
              by simp [mul_ne_zero, hu, hv, pow_ne_zero, hw], ?_, ?_, sf_one _,
              by rw [natDegree_X_sub_C]; norm_num,
              mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _), ?_⟩
            · intro s
              simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, ← huv]
              field_simp
              ring
            · exact (((monic_X_sub_C _).mul (monic_X_sub_C _)).pow 2).mul (monic_X_sub_C _)
            · calc (((X - C (-u⁻¹)) * (X - C (-w⁻¹))) ^ 2 * (X - C (-w⁻¹)) : F[X]).natDegree
                  ≤ ((((X - C (-u⁻¹)) * (X - C (-w⁻¹))) : F[X]) ^ 2).natDegree
                    + (X - C (-w⁻¹) : F[X]).natDegree := natDegree_mul_le
                _ ≤ 2 * (((X - C (-u⁻¹)) * (X - C (-w⁻¹))) : F[X]).natDegree
                    + (X - C (-w⁻¹) : F[X]).natDegree := by
                    have := natDegree_pow_le
                      (p := ((X - C (-u⁻¹)) * (X - C (-w⁻¹)) : F[X])) (n := 2)
                    omega
                _ ≤ 2 * ((X - C (-u⁻¹) : F[X]).natDegree + (X - C (-w⁻¹) : F[X]).natDegree)
                    + (X - C (-w⁻¹) : F[X]).natDegree := by
                    have := natDegree_mul_le (p := (X - C (-u⁻¹) : F[X]))
                      (q := (X - C (-w⁻¹) : F[X]))
                    omega
                _ ≤ 5 := by simp [natDegree_X_sub_C]
        · by_cases huw : u = w
          · -- u = w ≠ v : kernel L_u⁴L_v : σ = L_u², r = L_v
            refine ⟨(X - C (-u⁻¹)) ^ 2, X - C (-v⁻¹), u * v * w ^ 3,
              by simp [mul_ne_zero, hu, hv, pow_ne_zero, hw], ?_, ?_, sf_one _,
              by rw [natDegree_X_sub_C]; norm_num, pow_ne_zero _ (X_sub_C_ne_zero _), ?_⟩
            · intro s
              simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, ← huw]
              field_simp
              ring
            · exact (((monic_X_sub_C _).pow 2).pow 2).mul (monic_X_sub_C _)
            · calc (((X - C (-u⁻¹)) ^ 2) ^ 2 * (X - C (-v⁻¹)) : F[X]).natDegree
                  ≤ (((X - C (-u⁻¹) : F[X]) ^ 2) ^ 2).natDegree
                    + (X - C (-v⁻¹) : F[X]).natDegree := natDegree_mul_le
                _ ≤ 2 * (2 * (X - C (-u⁻¹) : F[X]).natDegree)
                    + (X - C (-v⁻¹) : F[X]).natDegree := by
                    have ha := natDegree_pow_le (p := ((X - C (-u⁻¹) : F[X]) ^ 2)) (n := 2)
                    have hb := natDegree_pow_le (p := (X - C (-u⁻¹) : F[X])) (n := 2)
                    omega
                _ ≤ 5 := by simp [natDegree_X_sub_C]
          · by_cases hvw : v = w
            · -- v = w ≠ u : kernel L_uL_v⁴ : σ = L_v², r = L_u
              refine ⟨(X - C (-v⁻¹)) ^ 2, X - C (-u⁻¹), u * v * w ^ 3,
                by simp [mul_ne_zero, hu, hv, pow_ne_zero, hw], ?_, ?_, sf_one _,
                by rw [natDegree_X_sub_C]; norm_num, pow_ne_zero _ (X_sub_C_ne_zero _), ?_⟩
              · intro s
                simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, ← hvw]
                field_simp
                ring
              · exact (((monic_X_sub_C _).pow 2).pow 2).mul (monic_X_sub_C _)
              · calc (((X - C (-v⁻¹)) ^ 2) ^ 2 * (X - C (-u⁻¹)) : F[X]).natDegree
                    ≤ (((X - C (-v⁻¹) : F[X]) ^ 2) ^ 2).natDegree
                      + (X - C (-u⁻¹) : F[X]).natDegree := natDegree_mul_le
                  _ ≤ 2 * (2 * (X - C (-v⁻¹) : F[X]).natDegree)
                      + (X - C (-u⁻¹) : F[X]).natDegree := by
                      have ha := natDegree_pow_le (p := ((X - C (-v⁻¹) : F[X]) ^ 2)) (n := 2)
                      have hb := natDegree_pow_le (p := (X - C (-v⁻¹) : F[X])) (n := 2)
                      omega
                  _ ≤ 5 := by simp [natDegree_X_sub_C]
            · -- all distinct: the generic quintic : σ = L_w, r = L_uL_vL_w
              refine ⟨X - C (-w⁻¹),
                (X - C (-u⁻¹)) * (X - C (-v⁻¹)) * (X - C (-w⁻¹)), u * v * w ^ 3,
                by simp [mul_ne_zero, hu, hv, pow_ne_zero, hw], ?_, ?_,
                radical_squarefree (neg_inv_ne hu hv huv) (neg_inv_ne hu hw huw)
                  (neg_inv_ne hv hw hvw), ?_, X_sub_C_ne_zero _, ?_⟩
              · intro s
                simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C]
                field_simp
                ring
              · exact ((monic_X_sub_C _).pow 2).mul
                  (((monic_X_sub_C _).mul (monic_X_sub_C _)).mul (monic_X_sub_C _))
              · rw [radical_natDegree]
                norm_num
              · calc ((X - C (-w⁻¹)) ^ 2
                      * ((X - C (-u⁻¹)) * (X - C (-v⁻¹)) * (X - C (-w⁻¹))) : F[X]).natDegree
                    ≤ ((X - C (-w⁻¹) : F[X]) ^ 2).natDegree
                      + ((X - C (-u⁻¹)) * (X - C (-v⁻¹)) * (X - C (-w⁻¹))
                          : F[X]).natDegree := natDegree_mul_le
                  _ ≤ 2 * (X - C (-w⁻¹) : F[X]).natDegree + 3 := by
                      have := natDegree_pow_le (p := (X - C (-w⁻¹) : F[X])) (n := 2)
                      rw [radical_natDegree]
                      omega
                  _ ≤ 5 := by norm_num [natDegree_X_sub_C]

/-! ## 8. The per-class count at the explicit family -/

/-- **The d = 4 class count** (the lane's central estimate): for order-4 `χ`,
`q ≥ 2026`, and every nondegenerate shape `(u, v, w)`, every nonzero class fiber of the
triple-linear kernel obeys `m·#fiber ≤ Dtot` at the explicit family. -/
theorem d4_class_count (hχ : orderOf χ = 4) (hq : 2026 ≤ Fintype.card F)
    (u v w : F)
    (h1 : ¬(u = w ∧ v = 0)) (h2 : ¬(u = 0 ∧ v = w)) (h3 : ¬(u = v ∧ w = 0))
    {c : ℂ} (hc : c ≠ 0) :
    m4P (Fintype.card F)
        * (Finset.univ.filter fun s : F => tripleVal χ u v w s = c).card
      ≤ dtot4P (Fintype.card F) := by
  classical
  set q := Fintype.card F with hqdef
  have h4 : 4 ∣ q - 1 := hχ ▸ MulChar.orderOf_dvd_card_sub_one F χ
  have hq2 : 2 ≤ q := Fintype.one_lt_card
  have hmod : q % 4 = 1 := by omega
  have hodd : Odd q := Nat.odd_iff.mpr (by omega)
  obtain ⟨σ, r, κ, hκ, hpt, hmono, hsf, hrdeg, hσ, hdeg5⟩ := shape_decomp u v w h1 h2 h3
  set g : F[X] := σ ^ 2 * r with hgdef
  have hg0 : g ≠ 0 := hmono.ne_zero
  have hdegpos : 0 < g.natDegree := by
    rw [hgdef, natDegree_mul (pow_ne_zero _ hσ) (Squarefree.ne_zero hsf)]
    omega
  -- the fiber rewrite: tripleVal = χ κ · χ(g(s))
  have hκval : χ κ ≠ 0 := chi_ne_zero hκ
  have hval : ∀ s : F, tripleVal χ u v w s = χ κ * χ (g.eval s) := by
    intro s
    rw [tripleVal_eq_kernel hχ, hpt s, map_mul]
  set c' : ℂ := (χ κ)⁻¹ * c with hc'def
  have hc' : c' ≠ 0 := mul_ne_zero (inv_ne_zero hκval) hc
  have hfilter : (Finset.univ.filter fun s : F => tripleVal χ u v w s = c)
      = Finset.univ.filter fun s : F => χ (g.eval s) = c' := by
    refine Finset.filter_congr fun s _ => ?_
    rw [hval s, hc'def]
    constructor
    · intro h
      field_simp
      linear_combination h
    · intro h
      rw [h]
      field_simp
  -- the power-fiber dictionary
  obtain ⟨ζ, hsub⟩ := chiFiber_subset_powerFiber hχ g hc'
  have hcardle : (Finset.univ.filter fun s : F => tripleVal χ u v w s = c).card
      ≤ (Finset.univ.filter fun s : F =>
          (g.eval s) ^ ((q - 1) / 4) = ζ).card := by
    rw [hfilter]
    exact Finset.card_le_card hsub
  -- the r25 fiber bound at the explicit family
  have hind : DBlockIndependence F 4 q (d4P q) g := by
    rw [hgdef]
    refine dBlockIndependence_four_sqmul σ r hσ hsf hrdeg hodd h4 ?_
    rw [← hgdef]
    have := params4_indep (q := q) (by omega) hmod
    omega
  have hcount : m4P q * (d4P q + (g.natDegree - 1) * m4P q + j4P q)
      < 4 * (j4P q * (d4P q + 1)) := by
    have hbase := params4_count (q := q) (by omega) hmod
    have hle : g.natDegree - 1 ≤ 4 := by omega
    calc m4P q * (d4P q + (g.natDegree - 1) * m4P q + j4P q)
        ≤ m4P q * (d4P q + 4 * m4P q + j4P q) := by
          refine Nat.mul_le_mul_left _ ?_
          have := Nat.mul_le_mul_right (m4P q) hle
          omega
      _ < 4 * (j4P q * (d4P q + 1)) := hbase
  have hfib := superelliptic_stepanov_fiber_bound g hmono hdegpos
    (d := 4) (m := m4P q) (e := (q - 1) / 4) (J := j4P q) (D := d4P q)
    (by unfold j4P; omega) hind rfl (params4_m_lt (by omega)) hcount ζ
  have hfib3 : m4P q * (Finset.univ.filter fun s : F =>
        (g.eval s) ^ ((q - 1) / 4) = ζ).card
      ≤ g.natDegree * (m4P q + 3 * ((q - 1) / 4)) + d4P q + q * (j4P q - 1) := by
    have h31 : (4 - 1 : ℕ) = 3 := rfl
    rw [← h31]
    exact hfib
  -- assemble: m·#fiber ≤ m·#powerfiber ≤ deg·(m+3e)+D+q(J−1) ≤ Dtot
  have hdegbd : g.natDegree * (m4P q + 3 * ((q - 1) / 4)) + d4P q + q * (j4P q - 1)
      ≤ dtot4P q := by
    unfold dtot4P
    have hmul : g.natDegree * (m4P q + 3 * ((q - 1) / 4))
        ≤ 5 * (m4P q + 3 * ((q - 1) / 4)) :=
      Nat.mul_le_mul_right _ hdeg5
    omega
  calc m4P q * (Finset.univ.filter fun s : F => tripleVal χ u v w s = c).card
      ≤ m4P q * (Finset.univ.filter fun s : F =>
          (g.eval s) ^ ((q - 1) / 4) = ζ).card := Nat.mul_le_mul_left _ hcardle
    _ ≤ g.natDegree * (m4P q + 3 * ((q - 1) / 4)) + d4P q + q * (j4P q - 1) := hfib3
    _ ≤ dtot4P q := hdegbd

/-! ## 9. The assembled unconditional `TripleLinearHasseC` at d = 4 -/

/-- Characters have norm at most 1 everywhere. -/
theorem chi_norm_le_one (χ : MulChar F ℂ) (x : F) : ‖χ x‖ ≤ 1 := by
  by_cases hx : x = 0
  · rw [hx, χ.map_nonunit (by simp)]
    simp
  · have h1 := congrArg norm (mulChar_mul_conj χ hx)
    rw [norm_mul, Complex.norm_conj, norm_one] at h1
    nlinarith [norm_nonneg (χ x), h1]

/-- The trivial bound: `‖tripleSum‖ ≤ q`. -/
theorem tripleSum_norm_le_card (χ : MulChar F ℂ) (u v w : F) :
    ‖tripleSum χ u v w‖ ≤ (Fintype.card F : ℝ) := by
  calc ‖tripleSum χ u v w‖
      ≤ ∑ s : F, ‖χ ((u * s + 1) * (v * s + 1)) * conj' (χ (w * s + 1))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _s : F, (1 : ℝ) := by
        refine Finset.sum_le_sum fun s _ => ?_
        rw [norm_mul]
        have h1 := chi_norm_le_one χ ((u * s + 1) * (v * s + 1))
        have h2 : ‖conj' (χ (w * s + 1))‖ ≤ 1 := by
          rw [Complex.norm_conj]
          exact chi_norm_le_one χ _
        nlinarith [norm_nonneg (χ ((u * s + 1) * (v * s + 1))),
          norm_nonneg (conj' (χ (w * s + 1)))]
    _ = (Fintype.card F : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- **Trivial branch**: at `q ≤ 2025 = 45²` the constant-45 Hasse bound is free. -/
theorem tripleLinearHasseC_of_card_le (χ : MulChar F ℂ) (G : Finset F)
    (hq : Fintype.card F ≤ 2025) : TripleLinearHasseC χ G 45 := by
  intro z _hz _hnd
  obtain ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩ := z
  have hsq : Real.sqrt (Fintype.card F) ≤ 45 := by
    have h1 : (Fintype.card F : ℝ) ≤ 2025 := by exact_mod_cast hq
    calc Real.sqrt (Fintype.card F) ≤ Real.sqrt 2025 := Real.sqrt_le_sqrt h1
      _ = 45 := by
        rw [show (2025 : ℝ) = 45 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hcard : (Fintype.card F : ℝ)
      = Real.sqrt (Fintype.card F) * Real.sqrt (Fintype.card F) :=
    (Real.mul_self_sqrt (by positivity)).symm
  calc ‖tripleSum χ (b₂ - a₁) (b₂ - a₂) (b₂ - b₁)‖
      ≤ (Fintype.card F : ℝ) := tripleSum_norm_le_card χ _ _ _
    _ = Real.sqrt (Fintype.card F) * Real.sqrt (Fintype.card F) := hcard
    _ ≤ 45 * Real.sqrt (Fintype.card F) := by
        have := Real.sqrt_nonneg (Fintype.card F : ℝ)
        nlinarith

/-- **Large-q branch**: the full fold at the explicit family. -/
theorem tripleLinearHasseC_d4_of_large (hχ : orderOf χ = 4) (G : Finset F)
    (hq : 2026 ≤ Fintype.card F) : TripleLinearHasseC χ G 45 := by
  classical
  set q := Fintype.card F with hqdef
  have h4 : 4 ∣ q - 1 := hχ ▸ MulChar.orderOf_dvd_card_sub_one F χ
  have hmod : q % 4 = 1 := by
    have : 2 ≤ q := Fintype.one_lt_card
    omega
  intro z hz hnd
  obtain ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩ := z
  set u : F := b₂ - a₁ with hu
  set v : F := b₂ - a₂ with hv
  set w : F := b₂ - b₁ with hw
  -- the three degeneracy clauses transfer to (u, v, w)
  have hnd1 : ¬(u = w ∧ v = 0) := by
    rintro ⟨huw, hv0⟩
    refine hnd (Or.inl ⟨?_, ?_⟩)
    · exact sub_right_inj.mp huw
    · exact (sub_eq_zero.mp hv0).symm
  have hnd2 : ¬(u = 0 ∧ v = w) := by
    rintro ⟨hu0, hvw⟩
    refine hnd (Or.inr (Or.inl ⟨?_, ?_⟩))
    · exact (sub_eq_zero.mp hu0).symm
    · exact (sub_right_inj.mp hvw)
  have hnd3 : ¬(u = v ∧ w = 0) := by
    rintro ⟨huv, hw0⟩
    refine hnd (Or.inr (Or.inr ⟨?_, ?_⟩))
    · exact sub_right_inj.mp huv
    · exact (sub_eq_zero.mp hw0).symm
  -- per-class bound
  have hm0 : 0 < m4P q := by
    have := s4_pos (q := q) (by omega); unfold m4P; omega
  have hm' : (0 : ℝ) < (m4P q : ℝ) := by exact_mod_cast hm0
  set B : ℝ := (dtot4P q : ℝ) / (m4P q : ℝ) with hBdef
  have hBc : ∀ c ∈ T4,
      (((Finset.univ.filter fun s : F => tripleVal χ u v w s = c).card : ℝ)) ≤ B := by
    intro c hc
    have hcne : c ≠ 0 := by
      intro h
      have := T4_norm c hc
      rw [h] at this
      simp at this
    have hcount := d4_class_count hχ hq u v w hnd1 hnd2 hnd3 hcne
    have hcount' : (m4P q : ℝ)
        * (((Finset.univ.filter fun s : F => tripleVal χ u v w s = c).card : ℝ))
        ≤ (dtot4P q : ℝ) := by exact_mod_cast hcount
    rw [hBdef, le_div_iff₀ hm']
    linarith [hcount']
  -- fold
  have hfold := class_fold_bound (val := fun s => tripleVal χ u v w s) T4
    T4_norm T4_sum (fun s => tripleVal_mem hχ u v w s) hBc
    (tripleVal_zero_fiber_card_le_three χ u v w)
  have harith := d4_fold_arith (F := F) hq hmod
  rw [← hqdef] at harith
  calc ‖tripleSum χ u v w‖
      = ‖∑ s : F, tripleVal χ u v w s‖ := by rw [tripleSum_eq_sum_tripleVal]
    _ ≤ (T4.card : ℝ) * B - (Fintype.card F : ℝ) + 3 := hfold
    _ = 4 * B - (q : ℝ) + 3 := by rw [T4_card, ← hqdef]; norm_num
    _ ≤ 45 * Real.sqrt q := by
        rw [hBdef]
        exact harith

/-- **THE ROUND GOAL — UNCONDITIONAL order-4 triple-linear Hasse**: for EVERY finite
field and EVERY multiplicative character of order 4,
`‖tripleSum χ u v w‖ ≤ 45√q` at every nondegenerate tuple.  ZERO named hypotheses
(`4 ∣ q−1`, `Odd q` follow from `orderOf χ = 4`; `q ≤ 2025` is the trivial branch). -/
theorem tripleLinearHasseC_d4_unconditional (hχ : orderOf χ = 4) (G : Finset F) :
    TripleLinearHasseC χ G 45 := by
  rcases Nat.lt_or_ge 2025 (Fintype.card F) with hlarge | hsmall
  · exact tripleLinearHasseC_d4_of_large hχ G (by omega)
  · exact tripleLinearHasseC_of_card_le χ G hsmall

/-! ## 10. The rung wiring: order-4 families get `Cw = 49` -/

/-- **The family weld at d = 4**: any family of order-4 characters satisfies the r = 2
rung fourth-moment bound at `Cw = 4 + 45 = 49`, unconditionally. -/
theorem fourthMomentTwistBound_order4_family
    (G : Finset F) (X : Finset (MulChar F ℂ))
    (hX : ∀ χ' ∈ X, orderOf χ' = 4)
    (hp : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.FourthMomentTwistBound
      G X (4 + 45) :=
  fourthMomentTwistBound_of_tripleLinearHasseC_family G X (fun _ => 45)
    (fun _ _ => by norm_num) (fun _ _ => le_refl _)
    (fun χ' hχ' => tripleLinearHasseC_d4_unconditional (hX χ' hχ') G) hp

/-- The d = 4 face is closed at every field: either no order-4 character exists
(`q ≢ 1 (mod 4)`, vacuous) or every one of them satisfies the constant-45 bound.  This is
the statement shape consumed by the tower assembly. -/
theorem d4_face_closed (G : Finset F) (χ' : MulChar F ℂ) :
    orderOf χ' ≠ 4 ∨ TripleLinearHasseC χ' G 45 := by
  by_cases h : orderOf χ' = 4
  · exact Or.inr (tripleLinearHasseC_d4_unconditional h G)
  · exact Or.inl h

end ArkLib.ProximityGap.Frontier.R26D4Mirror

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R26D4Mirror.params4_count
#print axioms ArkLib.ProximityGap.Frontier.R26D4Mirror.params4_admiss
#print axioms ArkLib.ProximityGap.Frontier.R26D4Mirror.pairing4
#print axioms ArkLib.ProximityGap.Frontier.R26D4Mirror.d4_fold_arith
#print axioms ArkLib.ProximityGap.Frontier.R26D4Mirror.pow_div_ord_eq_one_of_chi_eq_one
#print axioms ArkLib.ProximityGap.Frontier.R26D4Mirror.chiFiber_subset_powerFiber
#print axioms ArkLib.ProximityGap.Frontier.R26D4Mirror.shape_decomp
#print axioms ArkLib.ProximityGap.Frontier.R26D4Mirror.d4_class_count
#print axioms ArkLib.ProximityGap.Frontier.R26D4Mirror.tripleLinearHasseC_d4_unconditional
#print axioms ArkLib.ProximityGap.Frontier.R26D4Mirror.fourthMomentTwistBound_order4_family
#print axioms ArkLib.ProximityGap.Frontier.R26D4Mirror.d4_face_closed
