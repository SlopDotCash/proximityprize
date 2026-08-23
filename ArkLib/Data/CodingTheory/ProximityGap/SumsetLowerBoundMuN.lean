/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SumProductBridge
import ArkLib.Data.CodingTheory.ProximityGap.SidonSubgroupClosed

/-!
# The Elekes–Szabó / sum–product sumset lower bound for `μ_n` (#407, lane wf-NF)

This file lands the **sumset side** of the sum–product dichotomy for the prize-regime
multiplicative subgroup `μ_n ⊂ F_q` (`n = 2^m`, `q = p` prime, `p > 2^n`).

`SumProductBridge.card_pow_four_le_card_sumset_mul_energy` proves the Cauchy–Schwarz bridge
`|G|⁴ ≤ |G+G|·E(G)`, i.e. `|G+G| ≥ |G|⁴ / E(G)`.  `SidonSubgroupClosed.additiveEnergy_mu_n`
proves `E(μ_n) = 3n² − 3n` **exactly** in the prize regime (the Sidon-mod-negation minimum).
Composing the two yields a fully **proven, unconditional** lower bound on the ordinary
two-fold sumset of `μ_n`:

> **`card_sumset_mu_n_ge`** — `(3n² − 3n)·|μ_n + μ_n| ≥ n⁴`, i.e. `|μ_n + μ_n| ≥ n⁴/(3n²−3n)`.

Since `n⁴/(3n²−3n) = n³/(3n−3) > n²/3`, the sumset is **near-maximal** (`Θ(n²)`).  (The exact
value is `|μ_n+μ_n| = n²/2 + 1`; the bridge recovers the order of magnitude unconditionally.)

## What this means for the δ* core (HONEST — lane verdict: WALLED to the deep-moment wall)

The lane goal was to push the sum–product bridge **past** the r=2 Hardy–Brüdern–Kawada
energy `E₂ ≤ n^{5/2}` and toward the floor `M(n) ~ √n`.  This file establishes — and the
companion probe (`scripts/probes/probe_wf2NF_*.py`) verifies exactly at `n = 8..256`,
`p ~ n⁴` — the following decisive, honest picture:

* The sumset is **already maximal** (`|μ_n+μ_n| = n²/2 + 1`, this brick gives `> n²/3`).
* The energy is **already at the Sidon floor** (`E₂ = 3n²−3n = Θ(n²)`, the absolute minimum
  for a set containing `−1`; `energyExcess = 0` in the prize regime).  There is no slack left
  in the r=2 layer to exploit — Sidon *is* the floor of `E₂`.
* Yet the r=2 moment bound `M⁴ ≤ q·E₂ − n⁴` only certifies `M ≤ (3)^{1/4}·n^{3/2}` — the
  **Johnson-level cap**, a factor `~n` above the true `M ~ √n`.  The loss is intrinsic to the
  r=2 bridge (it discards all higher-order cancellation), **not** a defect of the energy size.

So the sum–product / Elekes–Szabó avenue at depth `r = 2` is **WALLED to the section-6
deep-moment wall**: closing the gap to the floor provably requires deep moments `r ~ log q`
(the probe confirms `M ≤ (q·E_r)^{1/2r} → √(2n log q)` monotonically in `r`).  This brick is a
true, unconditional asset (the proven sumset lower bound completing the dichotomy) but it
*reconfirms* the Johnson cap; it does **not** supply energy below the Sidon threshold, because
there is no "below" — the energy is already minimal.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

open Finset

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

variable {p : ℕ} [Fact p.Prime] {n m : ℕ}

/-- **The sumset lower bound for `μ_n`** (prize regime `p > 2^n`).  Composing the sum–product
bridge `|G|⁴ ≤ |G+G|·E(G)` with the exact Sidon-mod-negation energy `E(μ_n) = 3n² − 3n`:

`(3n² − 3n)·|μ_n + μ_n| ≥ n⁴`.

This is the cross-multiplied form of `|μ_n + μ_n| ≥ n⁴/(3n²−3n) = n³/(3n−3) > n²/3`: the
two-fold sumset of the prize-regime multiplicative subgroup is near-maximal (`Θ(n²)`),
unconditionally.  (`G.card = n` here, recorded as the `hcard` hypothesis the caller supplies
from `IsPrimitiveRoot`.) -/
theorem card_sumset_mu_n_ge (hn2 : n = 2 ^ m) (hm : 1 ≤ m) (hp : 2 ^ n < p)
    {ω : ZMod p} (hω : IsPrimitiveRoot ω n)
    {G : Finset (ZMod p)} (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) :
    (3 * G.card ^ 2 - 3 * G.card) * (sumset G).card ≥ G.card ^ 4 := by
  -- the exact energy in the prize regime
  have hE : additiveEnergy G = 3 * G.card ^ 2 - 3 * G.card :=
    ArkLib.ProximityGap.AdditiveEnergySidonModNeg.additiveEnergy_mu_n hn2 hm hp hω hGmem
  -- the bridge
  have hbridge : G.card ^ 4 ≤ (sumset G).card * additiveEnergy G :=
    card_pow_four_le_card_sumset_mul_energy G
  rw [hE] at hbridge
  -- rearrange to the stated orientation
  rw [ge_iff_le, mul_comm]
  exact hbridge

/-- **Strict near-maximality**: the sumset of `μ_n` strictly exceeds `n²/3`.  Equivalently
`3·|μ_n + μ_n| > n²` (cross-multiplied to avoid division), for `n ≥ 2`.  Witnesses the
sum–product dichotomy concretely: the minimal Sidon energy forces a `Θ(n²)` sumset. -/
theorem three_card_sumset_mu_n_gt (hn2 : n = 2 ^ m) (hm : 1 ≤ m) (hp : 2 ^ n < p)
    {ω : ZMod p} (hω : IsPrimitiveRoot ω n)
    {G : Finset (ZMod p)} (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1)
    (hGcard : 2 ≤ G.card) :
    G.card ^ 2 < 3 * (sumset G).card := by
  have hkey : (3 * G.card ^ 2 - 3 * G.card) * (sumset G).card ≥ G.card ^ 4 :=
    card_sumset_mu_n_ge hn2 hm hp hω hGmem
  set c := G.card with hc
  -- from (3c²−3c)·|S| ≥ c⁴ and 3c²−3c < 3c² we get 3c²·|S| > c⁴ (using c ≥ 2 ⟹ |S| ≥ 1),
  -- hence 3·|S| > c²; we prove the clean integer chain directly.
  have h1 : (3 * c ^ 2 - 3 * c) * (sumset G).card ≥ c ^ 4 := hkey
  have hSpos : 1 ≤ (sumset G).card := by
    rcases Nat.eq_zero_or_pos (sumset G).card with h0 | h
    · rw [h0, Nat.mul_zero] at h1
      have : 0 < c ^ 4 := by positivity
      omega
    · exact h
  have h2 : 3 * c ^ 2 - 3 * c + 3 * c = 3 * c ^ 2 := by
    have : 3 * c ≤ 3 * c ^ 2 := by nlinarith [hGcard]
    omega
  -- 3c²·|S| = (3c²−3c)·|S| + 3c·|S| ≥ c⁴ + 3c·|S| ≥ c⁴ + 3c·1 = c⁴ + 3c > c⁴
  have h3 : 3 * c ^ 2 * (sumset G).card ≥ c ^ 4 + 3 * c := by
    have hsplit : 3 * c ^ 2 * (sumset G).card
        = (3 * c ^ 2 - 3 * c) * (sumset G).card + 3 * c * (sumset G).card := by
      have hle : 3 * c ≤ 3 * c ^ 2 := by nlinarith [hGcard]
      have := Nat.sub_add_cancel hle
      nlinarith [this]
    rw [hsplit]
    have : 3 * c * (sumset G).card ≥ 3 * c * 1 := by
      exact Nat.mul_le_mul_left _ hSpos
    nlinarith [h1, this]
  -- now 3c²·|S| > c⁴ since 3c > 0, and c⁴ = c²·c², so 3·|S| > c² after cancelling c² > 0
  have hc2pos : 0 < c ^ 2 := by positivity
  have h4 : 3 * c ^ 2 * (sumset G).card > c ^ 2 * c ^ 2 := by
    have : c ^ 4 = c ^ 2 * c ^ 2 := by ring
    rw [this] at h3
    have h3c : 0 < 3 * c := by omega
    omega
  -- cancel the common factor c² (left factor in both 3·c²·|S| and c²·c²)
  have h5 : c ^ 2 * (3 * (sumset G).card) > c ^ 2 * c ^ 2 := by
    have hrw : 3 * c ^ 2 * (sumset G).card = c ^ 2 * (3 * (sumset G).card) := by ring
    rw [hrw] at h4; exact h4
  exact lt_of_mul_lt_mul_left h5 (Nat.zero_le _)

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.card_sumset_mu_n_ge
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.three_card_sumset_mu_n_gt
