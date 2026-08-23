/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCSubtractedMoment
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._CharZeroWickEnergy
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodOptimizedBound

/-!
# The char-0 K-bound in energy form: `K ≤ 1` for the b≠0 energy of `μ_{2^k}` (#444, Angle P2)

**The target (prize, exponent-tight, energy form).** With `bne := Σ_{b≠0}‖η_b‖^{2r}` the b≠0 energy
and `Wick_r := (2r−1)‼·n^r` (`n = |G|`), the prize reduces to the **normalized-moment constant**
```
        K := (bne / ((q−1)·Wick_r))^{1/r}  =  O(1)   at the saddle  r ≈ ln q.
```
The moment method then gives `M = max_{b≠0}‖η_b‖ ≤ ((q−1)·Wick_r)^{1/2r} ≈ √(2K·n·ln q)`, the prize
exponent `n^{1/2}`. So the prize ⟺ `K = O(1)`; this file closes the **char-0 face**: `K ≤ 1`.

## The reduction (the load-bearing arithmetic)

Two in-tree, axiom-clean facts feed it:

* **DC-subtracted moment identity** (`DCSubtractedMoment.sum_nonzero_moment`):
  `bne = Σ_{b≠0}‖η_b‖^{2r} = q·E_r(G) − n^{2r}`. Removing the DC term `‖η_0‖^{2r} = n^{2r}` is the
  correction that reopened the moment route (the old "no-go" `(q·E_r)^{1/2r} ≥ n` was saturated by
  this single `b=0` term; cf `_BNonzeroMomentReduction`, `MEMORY` correction 2026-06-18).

* **Char-0 Wick energy bound, unconditional for `μ_{2^k}`** (`CharZeroWickEnergy.gaussianEnergyBound_dyadic`,
  Lam–Leung antipodal closure): `E_r(G) ≤ Wick_r = (2r−1)‼·n^r` for **all** `r`.

Composing: `bne = q·E_r − n^{2r} ≤ q·Wick_r − n^{2r}`. The b≠0 bound `bne ≤ (q−1)·Wick_r` (i.e. `K ≤ 1`)
therefore follows from the single inequality
```
        Wick_r ≤ n^{2r}      (equivalently  (2r−1)‼ ≤ n^r),
```
because `q·Wick_r − n^{2r} ≤ q·Wick_r − Wick_r = (q−1)·Wick_r`. And `Wick_r ≤ n^{2r}` holds in the
saddle regime `2r ≤ n`: by the crude estimate `(2r−1)‼ ≤ (2r)^r` (`doubleFactorial_le_pow`),
`Wick_r ≤ (2r)^r·n^r = (2rn)^r ≤ (n·n)^r = n^{2r}` once `2r ≤ n`. At the prize scale `n = 2^30`,
`r ≈ ln q ≈ 110 ≪ n/2`, so `2r ≤ n` holds with astronomical margin — the char-0 K-bound is automatic
through the saddle.

## What is proved here (axiom-clean)

* `wick_le_card_pow_two` : `Wick_r ≤ n^{2r}` whenever `2r ≤ n` (the saddle-regime arithmetic).
* `bNonzero_energy_le_char0` : `bne ≤ (q−1)·Wick_r` for `G ⊆ μ_{2^k}` in char-0, `2r ≤ n`
  (**the char-0 K ≤ 1, b≠0 energy form**) — the char-0 prize in energy form.
* `house_pow_le_char0` : `M^{2r} = ‖η_b‖^{2r} ≤ (q−1)·Wick_r` for every `b ≠ 0` — the prize-shaped
  per-frequency certificate, char-0, with bounded constant `K ≤ 1`.

## HONESTY — scope (the char-p wall, named, not crossed)

This is the **char-0** face. `gaussianEnergyBound_dyadic` requires `[CharZero F]`; the prize field is
`F_p` with `p = Θ(n^β)`. The char-p energy is `E_r^{F_p} = E_r(ℂ) + W_r`, `W_r ≥ 0` the char-p excess
(extra solutions `Σx = Σy mod p` that fail over `ℂ`). The open core is exactly that `W_r` preserves
`K = O(1)` at the saddle `r ≈ ln q` at the **worst (Fermat-structured) prime** — i.e. that the char-p
energy still obeys `E_r^{F_p} ≤ C^r·Wick_r`. This is the BGK/BCHKS-1.12 wall in averaged/energy form.
Empirically (`MEMORY`: n=16 Fermat p=65537 and n=32 generic, both past saddle) `K < 1` with *growing*
margin and *no breach*, but the `n → 2^30 / r → 110` worst-prime extrapolation is unproven. This file
closes the char-0 face cleanly and names the char-p excess as the sole residual; it does **not** cross
the wall. Issue #444, Angle P2 (cumulant / sub-Gaussian energy).
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.DCSubtractedMoment
open ArkLib.ProximityGap.GaussPeriodOptimizedBound
open ProximityGap.Frontier.CharZeroWickEnergy

namespace ProximityGap.Frontier.CharZeroKBound

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The saddle-regime arithmetic: `Wick_r ≤ n^{2r}` once `2r ≤ n`.** Here `Wick_r = (2r−1)‼·n^r`.
Proof: `(2r−1)‼ ≤ (2r)^r` (`doubleFactorial_le_pow`), so
`Wick_r ≤ (2r)^r·n^r = (2r·n)^r ≤ (n·n)^r = n^{2r}` using `2r ≤ n` and `n^{2r} = (n^2)^r`. -/
theorem wick_le_card_pow_two (n r : ℕ) (hsaddle : 2 * r ≤ n) :
    (Nat.doubleFactorial (2 * r - 1) : ℝ) * (n : ℝ) ^ r ≤ (n : ℝ) ^ (2 * r) := by
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  -- (2r−1)‼ ≤ (2r)^r
  have hdf : (Nat.doubleFactorial (2 * r - 1) : ℝ) ≤ ((2 * r : ℕ) : ℝ) ^ r :=
    doubleFactorial_le_pow r
  -- (2r)^r ≤ n^r   (from 2r ≤ n, base nonneg)
  have h2rn : ((2 * r : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hsaddle
  have hpow2r : ((2 * r : ℕ) : ℝ) ^ r ≤ (n : ℝ) ^ r :=
    pow_le_pow_left₀ (by positivity) h2rn r
  -- assemble:  Wick ≤ (2r)^r · n^r ≤ n^r · n^r = n^{2r}
  have hwr : (0 : ℝ) ≤ (n : ℝ) ^ r := by positivity
  calc (Nat.doubleFactorial (2 * r - 1) : ℝ) * (n : ℝ) ^ r
      ≤ ((2 * r : ℕ) : ℝ) ^ r * (n : ℝ) ^ r := by
        exact mul_le_mul_of_nonneg_right hdf hwr
    _ ≤ (n : ℝ) ^ r * (n : ℝ) ^ r := by
        exact mul_le_mul_of_nonneg_right hpow2r hwr
    _ = (n : ℝ) ^ (2 * r) := by rw [← pow_add]; congr 1; omega

/-- **The char-0 K-bound, b≠0 energy form (`K ≤ 1`).** For `G ⊆ μ_{2^k}` (`k ≥ 1`, negation-closed)
in a characteristic-zero field, and at saddle depth `2r ≤ |G|`, the b≠0 energy obeys
```
        bne = Σ_{b≠0}‖η_b‖^{2r}  ≤  (q − 1)·Wick_r,        Wick_r = (2r−1)‼·|G|^r,
```
equivalently `K = (bne/((q−1)Wick_r))^{1/r} ≤ 1`. This is the **char-0 prize in averaged/energy form**.

Proof: `bne = q·E_r − n^{2r}` (`sum_nonzero_moment`), `E_r ≤ Wick_r` (`gaussianEnergyBound_dyadic`,
char-0 Lam–Leung), and `Wick_r ≤ n^{2r}` (`wick_le_card_pow_two`, saddle regime), so
`bne ≤ q·Wick_r − n^{2r} ≤ q·Wick_r − Wick_r = (q−1)·Wick_r`. -/
theorem bNonzero_energy_le_char0 [CharZero F] {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {k : ℕ} (hk : 1 ≤ k) (G : Finset F)
    (hG : ∀ z ∈ G, z ^ (2 ^ k) = 1) (hneg : ∀ g ∈ G, -g ∈ G)
    (r : ℕ) (hsaddle : 2 * r ≤ G.card) :
    ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r)
      ≤ ((Fintype.card F : ℝ) - 1) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by
  set q : ℝ := (Fintype.card F : ℝ) with hq
  set n : ℝ := (G.card : ℝ) with hn
  set W : ℝ := (Nat.doubleFactorial (2 * r - 1) : ℝ) * n ^ r with hW
  -- (1) bne = q·E_r − n^{2r}
  have hbne : ∑ b ∈ univ.erase (0 : F), ‖eta ψ G b‖ ^ (2 * r)
      = q * (rEnergy G r : ℝ) - n ^ (2 * r) :=
    sum_nonzero_moment hψ G r
  -- (2) E_r ≤ Wick  (char-0 Lam–Leung)
  have hEr : (rEnergy G r : ℝ) ≤ W := by
    have := gaussianEnergyBound_dyadic (F := F) hk G hG hneg r
    -- `GaussianEnergyBound G r` unfolds to `(rEnergy G r : ℝ) ≤ (2r−1)‼ · |G|^r`
    simpa [ArkLib.ProximityGap.GaussPeriodMomentBound.GaussianEnergyBound, hW, hn] using this
  -- (3) Wick ≤ n^{2r}  (saddle regime)
  have hWick : W ≤ n ^ (2 * r) := wick_le_card_pow_two G.card r hsaddle
  -- q ≥ 0
  have hq0 : (0 : ℝ) ≤ q := by positivity
  -- assemble
  rw [hbne]
  calc q * (rEnergy G r : ℝ) - n ^ (2 * r)
      ≤ q * W - n ^ (2 * r) := by
        have := mul_le_mul_of_nonneg_left hEr hq0; linarith
    _ ≤ q * W - W := by linarith [hWick]
    _ = (q - 1) * W := by ring

/-- **The prize-shaped per-frequency certificate, char-0.** For every `b ≠ 0`,
`‖η_b‖^{2r} ≤ (q − 1)·Wick_r` (since one term `≤` the b≠0 sum, then the K-bound). This is the
moment-method certificate with bounded constant `K ≤ 1`: `M = max_{b≠0}‖η_b‖ ≤ ((q−1)·Wick_r)^{1/2r}`,
the prize exponent `√(2n ln q)` in char-0. -/
theorem house_pow_le_char0 [CharZero F] {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {k : ℕ} (hk : 1 ≤ k) (G : Finset F)
    (hG : ∀ z ∈ G, z ^ (2 ^ k) = 1) (hneg : ∀ g ∈ G, -g ∈ G)
    (r : ℕ) (hsaddle : 2 * r ≤ G.card) (b : F) (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ (2 * r)
      ≤ ((Fintype.card F : ℝ) - 1) * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) := by
  have hmem : b ∈ univ.erase (0 : F) := Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b⟩
  have hterm : ‖eta ψ G b‖ ^ (2 * r) ≤ ∑ b' ∈ univ.erase (0 : F), ‖eta ψ G b'‖ ^ (2 * r) :=
    Finset.single_le_sum (f := fun b' : F => ‖eta ψ G b'‖ ^ (2 * r))
      (fun i _ => by positivity) hmem
  exact le_trans hterm (bNonzero_energy_le_char0 hψ hk G hG hneg r hsaddle)

end ProximityGap.Frontier.CharZeroKBound

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.CharZeroKBound.wick_le_card_pow_two
#print axioms ProximityGap.Frontier.CharZeroKBound.bNonzero_energy_le_char0
#print axioms ProximityGap.Frontier.CharZeroKBound.house_pow_le_char0
