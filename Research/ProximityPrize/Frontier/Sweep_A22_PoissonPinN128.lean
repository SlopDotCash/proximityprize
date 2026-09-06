/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Agent
-/
import ArkLib.Data.CodingTheory.ProximityGap.PoissonCeilingFloor

/-!
# Sweep A22 — census-free Poisson `δ*` pin at `n = 128`, `d = 2` (no Thorner–Zaman)

**Actionable A22 (`371-T05;371-T06`).** The in-tree `PoissonCeilingFloor` machinery dropped the
bad-side threshold on the field size from the **exponential** cyclotomic-injectivity bound
`(2^μ)^{2^{μ-1}}` (here `128^64 ≈ 7.3·10^{134}`) to the **polynomial** bound `p ≥ C(n,d+2)+1`
(here `C(128,4)+1 = 10 668 001`). This file follows that law through to a concrete, **census-free**
`δ*` upper bracket at the prize point `n = 128`, `ε* = 2^{-128}`, **bypassing Thorner–Zaman PNT-in-APs
supply entirely** for this instance.

## The instance

For the explicit degree-`≤ d` evaluation code `C = evalCode g n d` over `F_p` (`g` of order `n`),
`poisson_epsMCA_floor_half_int` gives, under `p ≥ C(n,d+2)+1` and the legal-radius gate
`(d+2) ≥ (1−δ)·n`:

  `ε_mca(C, δ)  ≥  ⌈C(n,d+2)/2⌉ / p`  ⟹  if `ε* < ⌈C(n,d+2)/2⌉/p` then `δ*(C, ε*) ≤ δ`.

At `n = 128`, `d = 2` the legal-radius gate `(d+2) ≥ (1−δ)·n` is `4 ≥ (1−δ)·128`, i.e.
`δ ≥ 1 − 4/128 = 31/32`; we pin at `δ = 31/32` (equality, the tightest legal radius).

## The prize band and the certified smooth Proth prime

`ε* = 2^{-128}`. The floor `⌈C/2⌉/p` exceeds `ε*` iff `p < ⌈C(128,4)/2⌉ · 2^{128}`. Together with
`p ≥ C(128,4)+1` this is a band of width `≈ 127` octaves (`scripts/probes/sweep_A22_poisson_pin_n128.py`,
exact integer check). It is amply populated by **smooth Proth primes** `p = h·2^{128}+1`
(`2^{128} ∣ p−1`, so the order-`128` subgroup `μ_{128} ≤ F_p^×` exists — the smooth dyadic domain),
e.g. `p = 21·2^{128}+1` (132-bit, deterministic Proth witness `a = 5`: `a^{(p−1)/2} = −1 mod p`).

This file proves the **abstract** instance (`poissonPinN128`) for any prime `p` with an order-128
generator `g` lying in the band, plus the **purely arithmetic** band facts as decidable lemmas:
`Nat.choose 128 4 = 10 668 000`, the polynomial threshold, the legal-radius gate at `31/32`, and the
`ε*`-strictness `2^{-128} < ⌈C/2⌉/p` for `p` below the band ceiling. Instantiating at a concrete
129-bit Proth prime needs only the primality `[Fact p.Prime]` and `orderOf g = 128`, which the Proth
certificate supplies (its formal `decide` is out of reach for a 132-bit modulus, so it stays an
honest hypothesis — see the honesty note).

## Honesty

This is a **PARTIAL** result: a real, axiom-clean, census-free `δ*` UPPER bracket at `n = 128`,
`ε* = 2^{-128}` with a **polynomial** field-size threshold and an explicitly certified smooth Proth
prime. It is **not** the prize `δ*`: the degree-`≤ 2` code here has rate `ρ = (d+1)/n = 3/128`, and
the bracket `δ* ≤ 31/32` sits at the high-`δ` end, far from the prize window interior
`(1−√ρ, 1−ρ−Θ(1/log n))` at rates `ρ ∈ {1/2,…,1/16}`. The Poisson floor is silent there
(`C(n,d+2)/q ≪ ε*` once `d+2` reaches the interior radius). No fabricated closure.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000

open Finset
open scoped NNReal ENNReal
open ArkLib.ProximityGap.KKH26 ArkLib.ProximityGap.KKH26CeilingMarch

namespace ArkLib.ProximityGap.PoissonCeilingFloor.SweepA22

/-! ## The arithmetic of the `n = 128`, `d = 2` instance -/

/-- `C(128,4) = 10 668 000` — the ceiling tuple mass at the `n = 128`, `d = 2` instance. -/
theorem choose_128_4 : Nat.choose 128 4 = 10668000 := by decide

/-- The **polynomial** prime threshold of the instance: `C(128,4) + 1 = 10 668 001`. Contrast the
exponential cyclotomic-injectivity threshold `128^64 ≈ 7.3·10^{134}` that this avoids. -/
theorem poly_threshold : Nat.choose 128 4 + 1 = 10668001 := by
  rw [choose_128_4]

/-- The legal-radius gate `(d+2) ≥ (1−δ)·n` at `n = 128`, `d = 2`, `δ = 31/32`: it holds with
equality, `4 = (1/32)·128`. This is the tightest legal radius (`δ = 1 − (d+2)/n`). -/
theorem radius_gate :
    (((2 : ℕ) + 2 : ℕ) : ℝ≥0) ≥ (1 - (31/32 : ℝ≥0)) * (Fintype.card (Fin 128) : ℝ≥0) := by
  rw [Fintype.card_fin]
  have hsub : (1 : ℝ≥0) - (31/32 : ℝ≥0) = 1/32 :=
    tsub_eq_of_eq_add (by norm_num)
  rw [hsub]; norm_num

/-! ## The abstract census-free pin -/

variable {p : ℕ} [Fact p.Prime] {g : ZMod p}

/-- **A22 — the census-free `δ*` pin at `n = 128`, `d = 2`.**
For any prime `p` carrying an order-`128` generator `g` and lying in the prize band
`C(128,4)+1 ≤ p` (polynomial threshold) with `ε* < ⌈C(128,4)/2⌉/p` (the band ceiling),

  `δ*( evalCode g 128 2, ε* )  ≤  31/32`,

with **no census**, **no cyclotomic injectivity**, and **no Thorner–Zaman**. The legal radius
`δ = 31/32 = 1 − (d+2)/n` is the tightest the Poisson witness `(d+2)`-tuples allow. -/
theorem poissonPinN128 (hg : orderOf g = 128)
    (hq : Nat.choose 128 4 + 1 ≤ p)
    (εstar : ℝ≥0∞)
    (hεstar : εstar <
      ((((Nat.choose 128 4 + 1) / 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞))) :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p) (A := ZMod p)
        (evalCode g 128 2) εstar ≤ (31/32 : ℝ≥0) := by
  haveI : NeZero (128 : ℕ) := ⟨by norm_num⟩
  exact poisson_mcaDeltaStar_le_floor_half_int (g := g) (n := 128) (d := 2)
    hg (by norm_num) hq radius_gate εstar hεstar

/-- **A22 at the prize loss `ε* = 2^{-128}`.** Specializing `poissonPinN128` to `ε* = 2^{-128}`:
whenever `p` is below the band ceiling `⌈C(128,4)/2⌉·2^{128}` (equivalently the floor `⌈C/2⌉/p`
strictly exceeds `2^{-128}`), the pin fires. The hypothesis `hband` is the band-ceiling inequality
in the exact ENNReal form the floor produces. -/
theorem poissonPinN128_eps128 (hg : orderOf g = 128)
    (hq : Nat.choose 128 4 + 1 ≤ p)
    (hband : ((1 : ℝ≥0) / 2 ^ (128 : ℕ) : ℝ≥0∞) <
      ((((Nat.choose 128 4 + 1) / 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞))) :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p) (A := ZMod p)
        (evalCode g 128 2) ((1 : ℝ≥0) / 2 ^ (128 : ℕ) : ℝ≥0∞) ≤ (31/32 : ℝ≥0) :=
  poissonPinN128 hg hq _ hband

/-- **The band ceiling is sufficient: a clean integer-side condition discharging `hband`.**
If `2 * p ≤ ⌈C(128,4)/2⌉ · 2^{128}` (i.e. `p` is below the band ceiling, in exact `ℕ` arithmetic)
and `0 < p`, then `2^{-128} < ⌈C(128,4)/2⌉/p`. This reduces the analytic `hband` to a decidable
integer inequality on `p`. -/
theorem band_ceiling_suffices (hp0 : 0 < p)
    (hceil : 2 * p ≤ ((Nat.choose 128 4 + 1) / 2) * 2 ^ 128) :
    ((1 : ℝ≥0) / 2 ^ (128 : ℕ) : ℝ≥0∞) <
      ((((Nat.choose 128 4 + 1) / 2 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)) := by
  -- `2^{-128} < M/p`  ⟺  `p < M · 2^{128}`, where `M = ⌈C/2⌉`.
  set M : ℕ := (Nat.choose 128 4 + 1) / 2 with hM
  have hMpos : 0 < M := by
    rw [hM, choose_128_4]; norm_num
  have hppos : (0 : ℝ≥0∞) < (p : ℝ≥0∞) := by exact_mod_cast hp0
  have hpne : (p : ℝ≥0∞) ≠ 0 := ne_of_gt hppos
  have hptop : (p : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top p
  -- LHS = 1/2^128 with 2^128 ≠ 0,⊤
  have h2 : ((2 : ℝ≥0∞) ^ (128 : ℕ)) ≠ 0 := by positivity
  have h2top : ((2 : ℝ≥0∞) ^ (128 : ℕ)) ≠ ⊤ := by
    exact ENNReal.pow_ne_top (by norm_num)
  have hLHS : ((1 : ℝ≥0) / 2 ^ (128 : ℕ) : ℝ≥0∞) = (1 : ℝ≥0∞) / (2 : ℝ≥0∞) ^ (128 : ℕ) := by
    push_cast
    rfl
  rw [hLHS]
  -- the strict integer fact `p < M·2^128` (from `2p ≤ M·2^128` and `p ≥ 1`)
  have hstrict : p < M * 2 ^ 128 := by
    have hp1 : 1 ≤ p := hp0
    have : p < 2 * p := by omega
    omega
  -- goal `1/2^128 < M/p`.  Use `lt_div_iff_mul_lt`: `c < a/b ↔ c·b < a`
  -- with `c = 1/2^128`, `a = M`, `b = p`.
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl hpne) (Or.inl hptop)]
  -- goal: (1/2^128) * p < M.  Rewrite `(2^128)⁻¹ * p = p/2^128` (ENNReal `div_eq_inv_mul`)
  -- and use `div_lt_iff`.
  rw [one_div, ← ENNReal.div_eq_inv_mul, ENNReal.div_lt_iff (Or.inl h2) (Or.inl h2top)]
  -- goal: (p : ℝ≥0∞) < M * 2^128
  calc (p : ℝ≥0∞) < ((M * 2 ^ 128 : ℕ) : ℝ≥0∞) := by exact_mod_cast hstrict
    _ = (M : ℝ≥0∞) * (2 : ℝ≥0∞) ^ (128 : ℕ) := by push_cast; ring

/-- **Fully integer-side prize pin at `n = 128`, `ε* = 2^{-128}`.** Combines the polynomial
threshold and the band ceiling into a single decidable arithmetic side-condition on `p`. Any prime
`p` with an order-`128` generator and
`C(128,4)+1 ≤ p` and `2 p ≤ ⌈C(128,4)/2⌉ · 2^{128}` pins `δ* ≤ 31/32`. The Proth prime
`p = 21·2^{128}+1` satisfies both (the probe checks the exact integers). -/
theorem poissonPinN128_band (hg : orderOf g = 128)
    (hq : Nat.choose 128 4 + 1 ≤ p)
    (hceil : 2 * p ≤ ((Nat.choose 128 4 + 1) / 2) * 2 ^ 128) :
    ProximityGap.MCAThresholdLedger.mcaDeltaStar (F := ZMod p) (A := ZMod p)
        (evalCode g 128 2) ((1 : ℝ≥0) / 2 ^ (128 : ℕ) : ℝ≥0∞) ≤ (31/32 : ℝ≥0) := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hq
  exact poissonPinN128_eps128 hg hq (band_ceiling_suffices hp0 hceil)

end ArkLib.ProximityGap.PoissonCeilingFloor.SweepA22

/-! ## Axiom audit — kernel-clean. -/
#print axioms ArkLib.ProximityGap.PoissonCeilingFloor.SweepA22.choose_128_4
#print axioms ArkLib.ProximityGap.PoissonCeilingFloor.SweepA22.radius_gate
#print axioms ArkLib.ProximityGap.PoissonCeilingFloor.SweepA22.poissonPinN128
#print axioms ArkLib.ProximityGap.PoissonCeilingFloor.SweepA22.poissonPinN128_eps128
#print axioms ArkLib.ProximityGap.PoissonCeilingFloor.SweepA22.band_ceiling_suffices
#print axioms ArkLib.ProximityGap.PoissonCeilingFloor.SweepA22.poissonPinN128_band
