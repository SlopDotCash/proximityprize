/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumFourthMoment
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergyBridge
import ArkLib.Data.CodingTheory.ProximityGap.SidonModNegEnergyEquality

/-!
# wf-B1 — W3-base: the kurtosis cap `M_4 ≤ 3n·M_2` (`m_1 ≤ 1`), PROVEN axiom-clean

This file closes the **r = 2** energy bound of the W3 program (issue #444). The first
Wick-normalized moment satisfies `m_1 ≤ 1`, equivalently the kurtosis cap
`M_4 ≤ 3n·M_2`, for the thin 2-power NTT subgroup `μ_n ⊂ F_p`.

## The exact reduction (no Hasse–Weil needed)

Write `η_b := ∑_{y∈G} ψ(b·y)`. The two in-tree Parseval laws give, for any finite field `F`
with `q = |F|` and any `G ⊆ F`:

* `∑_b ‖η_b‖² = q·|G|`         (`subgroup_gaussSum_secondMoment`)
* `∑_b ‖η_b‖⁴ = q·E(G)`        (`subgroup_gaussSum_fourthMoment`), `E(G) = addEnergy G`.

Splitting off the principal spike `b = 0` (`‖η_0‖ = |G|`):

* `∑_{b≠0} ‖η_b‖² = q·|G| − |G|²`   (= `m·M_2`)
* `∑_{b≠0} ‖η_b‖⁴ = q·E(G) − |G|⁴`  (= `m·M_4`)

The cap `M_4 ≤ 3·|G|·M_2` (divide by `m = q−1 > 0`) is therefore the **closed integer
inequality**

> `q·E(G) − |G|⁴  ≤  3·|G|·(q·|G| − |G|²)`.

With the **proven exact char-`p` energy** `E(μ_n) = 3n² − 3n` (`mu_n_additiveEnergy_eq`,
unconditional for `p > 2^n`, via the cyclotomic resultant — NOT a Hasse–Weil estimate, the
spurious 2+2 collisions are *exactly zero* in this regime), substituting `|G| = n`,
`E = 3n²−3n` makes the difference

> `m·(M_4 − 3n·M_2) = q·(3n²−3n) − n⁴ − 3n·(qn − n²) = −n·(n³ − 3n² + 3q)`,

which is `≤ 0` whenever `3q ≥ n²(3 − n)`. For `n ≥ 3` the RHS is `≤ 0 ≤ 3q`; for `n = 2`
it is `4 ≤ 3q` (any prime `q ≥ 2`). So the cap holds **unconditionally** in the regime where
the exact energy holds (`p > 2^n`, `n = 2^m`, `m ≥ 1`) — no prime threshold beyond exactness,
no curve point count.

## Pre-screen

`scripts/probes/rust/probe_wf8B1_kurtosis_cap.rs` at prize scale (`p ≈ n^4`, several primes
per `n`, `n` up to 128): max `M_4/(3n·M_2) = 0.992 < 1`, `spur = 0` everywhere. Matches the
exact algebra (the cap is tight as `q → ∞`: `m_1 → 1⁻`).

Issue #444 (lane B1). Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment
open ArkLib.ProximityGap.AdditiveEnergyBridge

namespace ArkLib.ProximityGap.Wf8B1KurtosisCap

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `∑_{b≠0} ‖η_b‖⁴ = q·E(G) − |G|⁴`. The fourth-moment Parseval law with the principal
spike `b = 0` (`‖η_0‖⁴ = |G|⁴`) split off. -/
theorem nonzero_fourthMoment {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 4
      = (Fintype.card F : ℝ) * (addEnergy G : ℝ) - (G.card : ℝ) ^ 4 := by
  have h0 : eta ψ G 0 = (G.card : ℂ) := by simp [eta, AddChar.map_zero_eq_one]
  have hn04 : ‖eta ψ G 0‖ ^ 4 = (G.card : ℝ) ^ 4 := by rw [h0, Complex.norm_natCast]
  have h4 := subgroup_gaussSum_fourthMoment hψ G
  have hsp : ∑ b : F, ‖eta ψ G b‖ ^ 4
      = ‖eta ψ G 0‖ ^ 4 + ∑ b ∈ Finset.univ.erase 0, ‖eta ψ G b‖ ^ 4 :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ 0)).symm
  rw [hsp, hn04] at h4
  linarith [h4]

/-- `∑_{b≠0} ‖η_b‖² = q·|G| − |G|²`. The second-moment Parseval law with the principal
spike `b = 0` (`‖η_0‖² = |G|²`) split off. -/
theorem nonzero_secondMoment {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2
      = (Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2 := by
  have h0 : eta ψ G 0 = (G.card : ℂ) := by simp [eta, AddChar.map_zero_eq_one]
  have hn02 : ‖eta ψ G 0‖ ^ 2 = (G.card : ℝ) ^ 2 := by rw [h0, Complex.norm_natCast]
  have h2 := subgroup_gaussSum_secondMoment hψ G
  have hsp : ∑ b : F, ‖eta ψ G b‖ ^ 2
      = ‖eta ψ G 0‖ ^ 2 + ∑ b ∈ Finset.univ.erase 0, ‖eta ψ G b‖ ^ 2 :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ 0)).symm
  rw [hsp, hn02] at h2
  linarith [h2]

/-- **The kurtosis cap, general form.** For any finite field `F` (`q = |F|`) and any
`G ⊆ F` with `|G| = n ≥ 2` and *exact* additive energy `E(G) = 3n² − 3n`, the
nonzero-frequency fourth power-sum is dominated by `3n` times the second power-sum:

> `∑_{b≠0} ‖η_b‖⁴ ≤ 3·n·∑_{b≠0} ‖η_b‖²`,

i.e. `M_4 ≤ 3n·M_2` (`m_1 ≤ 1`) after dividing by `m = q − 1 > 0`. Proved by substituting
the two Parseval split-sums and the exact energy, then the closed arithmetic
`q·(3n²−3n) − n⁴ ≤ 3n·(qn − n²)` ⟺ `n·(n³ − 3n² + 3q) ≥ 0`, which holds for `n ≥ 2` and any
prime `q ≥ 2`. No Hasse–Weil / curve point count — the exact energy makes the spur vanish. -/
theorem kurtosis_cap {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) {n : ℕ}
    (hcard : G.card = n) (hn : 2 ≤ n) (hE : addEnergy G = 3 * n ^ 2 - 3 * n) :
    ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 4
      ≤ 3 * (n : ℝ) * ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2 := by
  set q : ℝ := (Fintype.card F : ℝ) with hq
  have hq2 : (2 : ℝ) ≤ q := by
    rw [hq]; exact_mod_cast Fintype.one_lt_card
  -- the exact energy as a real number: 3n² − 3n (the ℕ-subtraction is exact since 3n² ≥ 3n).
  have hEr : (addEnergy G : ℝ) = 3 * (n : ℝ) ^ 2 - 3 * (n : ℝ) := by
    have hge : 3 * n ≤ 3 * n ^ 2 := by nlinarith [hn]
    rw [hE]
    have : ((3 * n ^ 2 - 3 * n : ℕ) : ℝ) = (3 * n ^ 2 : ℕ) - (3 * n : ℕ) :=
      Nat.cast_sub hge
    rw [this]; push_cast; ring
  rw [nonzero_fourthMoment hψ G, nonzero_secondMoment hψ G, hcard, hEr]
  -- closed inequality: q·(3n²−3n) − n⁴ ≤ 3n·(q·n − n²)
  -- ⟺ 0 ≤ 3n·(qn − n²) − q·(3n²−3n) + n⁴ = n·(n³ − 3n² + 3q) = n⁴ − 3n³ + 3qn.
  have hnr : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith [hnr, hq2, sq_nonneg ((n : ℝ) - 3), mul_nonneg (le_trans (by norm_num) hnr)
    (le_trans (by norm_num) hq2)]

end ArkLib.ProximityGap.Wf8B1KurtosisCap

namespace ArkLib.ProximityGap.Wf8B1KurtosisCap

open ArkLib.ProximityGap.EnergyEqualitySidonModNeg

variable {p : ℕ} [Fact p.Prime] {n m : ℕ}

/-- **W3-base closed for `μ_n`: `M_4 ≤ 3n·M_2` (`m_1 ≤ 1`).** For the thin 2-power NTT
subgroup `μ_n ⊂ F_p` (`n = 2^m`, `m ≥ 1`, `p > 2^n`), the nonzero-frequency fourth power-sum
of the subgroup Gauss sums `η_b = ∑_{y∈μ_n} ψ(b·y)` is at most `3n` times the second:

> `∑_{b≠0} ‖η_b‖⁴ ≤ 3·n·∑_{b≠0} ‖η_b‖²`.

Combines the general `kurtosis_cap` with the proven exact char-`p` energy
`E(μ_n) = 3n² − 3n` (`mu_n_additiveEnergy_eq` → `additiveEnergy_eq_addEnergy`). A primitive
additive character `ψ` is a proof device (one exists on every `ZMod p`). This pins the r = 2
W3 brick `m_1 ≤ 1` unconditionally in the deployed regime. -/
theorem mu_n_kurtosis_cap (hn2 : n = 2 ^ m) (hm : 1 ≤ m) (hp : 2 ^ n < p)
    {ω : ZMod p} (hω : IsPrimitiveRoot ω n)
    {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    ∑ b ∈ Finset.univ.erase (0 : ZMod p), ‖eta ψ (muN p n) b‖ ^ 4
      ≤ 3 * (n : ℝ) * ∑ b ∈ Finset.univ.erase (0 : ZMod p), ‖eta ψ (muN p n) b‖ ^ 2 := by
  have hcard : (muN p n).card = n := mu_n_card_eq hω
  have hn : 2 ≤ n := by rw [hn2]; calc 2 = 2 ^ 1 := rfl
                          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  -- exact energy in the `addEnergy` form via the in-tree bridge
  have hEadd : addEnergy (muN p n) = 3 * n ^ 2 - 3 * n := by
    rw [← additiveEnergy_eq_addEnergy (muN p n)]
    exact mu_n_additiveEnergy_eq hn2 hm hp hω
  exact kurtosis_cap hψ (muN p n) hcard hn hEadd

end ArkLib.ProximityGap.Wf8B1KurtosisCap

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Wf8B1KurtosisCap.nonzero_fourthMoment
#print axioms ArkLib.ProximityGap.Wf8B1KurtosisCap.nonzero_secondMoment
#print axioms ArkLib.ProximityGap.Wf8B1KurtosisCap.kurtosis_cap
#print axioms ArkLib.ProximityGap.Wf8B1KurtosisCap.mu_n_kurtosis_cap
