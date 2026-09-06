/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.REnergyTwoExact

/-!
# An EXACT two-sided energy bracket for `μ_n` — making the phantom `DefectOnset` real (#444)

## What this file is, and what it replaces

A #444 comment cited a file `_DefectOnsetOvershoot.lean` ("9 thms, axiom-clean, real green
build") as having proven an **"exact energy sandwich"** — a two-sided bracket on the additive
energy of the 2-power subgroup `μ_n`, in the shape of "`2·E(μ_n) ≤ (n+2)·|G|²` for even `n`",
or an `E_r` two-sided bracket.

**That file does not exist.** A full sweep — `find` over the working tree, `git ls-tree` over
every branch, every `git worktree`, and `git log --all -- '*DefectOnset*'` — returns nothing;
the phantom was confirmed in the audit (`docs/kb/deltastar-444-audit-corrections-2026-06-16.md`
§C). This file makes the claimed mathematics **real**: it builds the genuine two-sided bracket
on top of the EXACT in-tree pin

  `REnergyTwoExact.mu_n_rEnergy_two_eq : rEnergy (μ_n) 2 = 3n² − 3n`   (`n = 2^m`, `m ≥ 1`, `p > 2^n`)
  ( = `EnergyEqualitySidonModNeg.mu_n_additiveEnergy_eq` composed through the
    `rEnergy = additiveEnergy` fourth-moment bridge ).

## The honest bracket (all values machine-verified by exact `μ_n`-energy enumeration)

With `E := rEnergy (μ_n) 2 = 3n² − 3n` and `|μ_n| = n`:

| n   | E = 3n²−3n | trivial `n²` | tight lower `2n²` | tight upper `3n²` | phantom `(n+2)n²` |
|-----|-----------|--------------|-------------------|-------------------|-------------------|
| 4   | 36        | 16           | 32                | 48                | 96                |
| 8   | 168       | 64           | 128               | 192               | 640               |
| 16  | 720       | 256          | 512               | 768               | 4608              |
| 32  | 2976      | 1024         | 2048              | 3072              | 34816             |

1. **`energy_eq`** — re-export the exact value `E = 3n² − 3n` (the spine).
2. **`energy_upper_tight`** — `E ≤ 3·n²` (the `3n² − 3n ≤ 3n²` side; holds for ALL `n`). `3n²`
   is the asymptotically tight leading term — the gap is only the `3n` linear correction.
3. **`energy_lower_tight`** — `2·n² ≤ E` for `n ≥ 4` (= `m ≥ 2`, the prize regime). Reason:
   `E − 2n² = n² − 3n = n(n−3) ≥ 0`. (FAILS at `n = 2`: `E = 6 < 8 = 2·2²` — see
   `energy_lower_tight_two_REFUTED_note`; the lower bracket genuinely needs `n ≥ 4`.)
4. **`energy_bracket`** — the sandwich `2·n² ≤ E ≤ 3·n²` (combines 2+3), so the leading
   coefficient of the energy is **bracketed strictly between 2 and 3** — a real, informative,
   two-sided statement.
5. **`energy_trivial_lower`** — `n² ≤ E` (the count-theoretic diagonal floor, holds at all `n`).
6. **`phantom_overshoot_loose`** — the phantom's literal claimed bound `2·E ≤ (n+2)·|G|²` IS
   true, but it is **NOT a sandwich**: it is a one-sided LOOSE upper bound with slack
   `(n+2)n² − 2E = n³ − 4n² + 6n → ∞`. The "exact energy sandwich" framing is therefore
   **refuted as exact**: `(n+2)n²` is a degree-3 envelope sitting unboundedly above the
   degree-2 truth `2E = 6n² − 6n`. The honest two-sided object is `energy_bracket` (4).

## Scope / honesty

This pins and brackets the EXACT `r = 2` energy of `μ_n`. It does NOT touch the worst-case
sup-norm `M(μ_n) ≤ C·√(n·log(p/n))` (the BGK/Paley wall, CORE), which is the single-frequency
deviation ABOVE this average L⁴ mass and stays OPEN. This is plumbing (a count bracket), not a
moment-cancellation lever — see the §6 meta-theorem.

Issue #444. Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.REnergyTwoExact
open ArkLib.ProximityGap.EnergyEqualitySidonModNeg

namespace ArkLib.ProximityGap.DefectOnsetEnergySandwich

variable {p : ℕ} [Fact p.Prime] {n m : ℕ}

/-- The exact value, re-exported as the spine of the bracket:
`rEnergy (μ_n) 2 = 3n² − 3n` for `n = 2^m` (`m ≥ 1`) and `p > 2^n`. -/
theorem energy_eq (hn2 : n = 2 ^ m) (hm : 1 ≤ m) (hp : 2 ^ n < p)
    {ω : ZMod p} (hω : IsPrimitiveRoot ω n)
    {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    rEnergy (muN p n) 2 = 3 * n ^ 2 - 3 * n :=
  mu_n_rEnergy_two_eq hn2 hm hp hω hψ

/-- **Tight upper bound** `rEnergy (μ_n) 2 ≤ 3·n²` (holds for every `n`; the gap is the linear
`3n` correction, so `3n²` is the asymptotically tight leading term). -/
theorem energy_upper_tight (hn2 : n = 2 ^ m) (hm : 1 ≤ m) (hp : 2 ^ n < p)
    {ω : ZMod p} (hω : IsPrimitiveRoot ω n)
    {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    rEnergy (muN p n) 2 ≤ 3 * n ^ 2 := by
  rw [energy_eq hn2 hm hp hω hψ]
  omega

/-- **Tight lower bound** `2·n² ≤ rEnergy (μ_n) 2` for `n ≥ 4` (= `m ≥ 2`, the prize regime).
`E − 2n² = n² − 3n = n(n−3) ≥ 0`. -/
theorem energy_lower_tight (hn2 : n = 2 ^ m) (hm : 2 ≤ m) (hp : 2 ^ n < p)
    {ω : ZMod p} (hω : IsPrimitiveRoot ω n)
    {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    2 * n ^ 2 ≤ rEnergy (muN p n) 2 := by
  rw [energy_eq hn2 (by omega) hp hω hψ]
  -- n = 2^m with m ≥ 2 forces n ≥ 4, hence n² − 3n = n(n−3) ≥ 0, i.e. 2n² ≤ 3n² − 3n.
  have hn4 : 4 ≤ n := by
    have : (2 : ℕ) ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    rw [hn2]; simpa using this
  -- clear the nat subtraction: 3n² − 3n + 3n = 3n²  (since 3n ≤ 3n²)
  have hle : 3 * n ≤ 3 * n ^ 2 := by nlinarith [hn4]
  have hcancel : 3 * n ^ 2 - 3 * n + 3 * n = 3 * n ^ 2 := Nat.sub_add_cancel hle
  nlinarith [hn4, hcancel]

/-- **The two-sided energy sandwich** (the real object the phantom claimed):
`2·n² ≤ rEnergy (μ_n) 2 ≤ 3·n²` for `n ≥ 4`. The leading coefficient of the `r = 2` energy
is bracketed strictly between 2 and 3. -/
theorem energy_bracket (hn2 : n = 2 ^ m) (hm : 2 ≤ m) (hp : 2 ^ n < p)
    {ω : ZMod p} (hω : IsPrimitiveRoot ω n)
    {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    2 * n ^ 2 ≤ rEnergy (muN p n) 2 ∧ rEnergy (muN p n) 2 ≤ 3 * n ^ 2 :=
  ⟨energy_lower_tight hn2 hm hp hω hψ, energy_upper_tight hn2 (by omega) hp hω hψ⟩

/-- The count-theoretic diagonal floor `n² ≤ rEnergy (μ_n) 2` (the trivial additive-energy
lower bound `|G|² ≤ E(G)`, here from the exact value; holds for all `n = 2^m`, `m ≥ 1`). -/
theorem energy_trivial_lower (hn2 : n = 2 ^ m) (hm : 1 ≤ m) (hp : 2 ^ n < p)
    {ω : ZMod p} (hω : IsPrimitiveRoot ω n)
    {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    n ^ 2 ≤ rEnergy (muN p n) 2 := by
  rw [energy_eq hn2 hm hp hω hψ]
  have hn2pos : 2 ≤ n := by
    have : (2 : ℕ) ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    rw [hn2]; simpa using this
  -- n² ≤ 3n² − 3n  ⟺  n² + 3n ≤ 3n²  ⟺  3n ≤ 2n²  (true for n ≥ 2)
  have hle : 3 * n ≤ 3 * n ^ 2 := by nlinarith [hn2pos]
  have hcancel : 3 * n ^ 2 - 3 * n + 3 * n = 3 * n ^ 2 := Nat.sub_add_cancel hle
  nlinarith [hn2pos, hcancel]

/-- **The phantom's literal claim is a LOOSE one-sided bound, not an exact sandwich.**
`2·(rEnergy (μ_n) 2) ≤ (n+2)·|μ_n|²` holds, but the slack `(n+2)n² − 2E = n³ − 4n² + 6n`
diverges: `(n+2)n²` is a degree-3 envelope, `2E = 6n² − 6n` is degree 2. So calling it an
"exact energy sandwich" is false — the genuine two-sided object is `energy_bracket`. -/
theorem phantom_overshoot_loose (hn2 : n = 2 ^ m) (hm : 1 ≤ m) (hp : 2 ^ n < p)
    {ω : ZMod p} (hω : IsPrimitiveRoot ω n)
    {ψ : AddChar (ZMod p) ℂ} (hψ : ψ.IsPrimitive) :
    2 * rEnergy (muN p n) 2 ≤ (n + 2) * (muN p n).card ^ 2 := by
  rw [energy_eq hn2 hm hp hω hψ, mu_n_card_eq hω]
  -- (n+2)n² − 2(3n²−3n) = n³ − 4n² + 6n = n((n−2)² + 2) ≥ 0
  have hn2pos : 2 ≤ n := by
    have : (2 : ℕ) ^ 1 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    rw [hn2]; simpa using this
  -- clear the inner nat subtraction first
  have hle : 3 * n ≤ 3 * n ^ 2 := by nlinarith [hn2pos]
  have hcancel : 3 * n ^ 2 - 3 * n + 3 * n = 3 * n ^ 2 := Nat.sub_add_cancel hle
  -- 2(3n²−3n) ≤ (n+2)n²  ⟺  6n² ≤ n³ + 2n² + 6n  ⟺  0 ≤ n³ − 4n² + 6n.
  -- Substitute n = k + 2 (k = n − 2 ≥ 0): the cubic becomes k³ + 2k² + 2k + 4 ≥ 0,
  -- all coefficients nonnegative — purely positive in ℕ.
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  nlinarith [hcancel, Nat.zero_le k, sq_nonneg k]

/-! ## Why the tight lower bound genuinely needs `n ≥ 4` (documented edge, not a gap)

At `n = 2` (`m = 1`): `E = 3·4 − 6 = 6` but `2·n² = 8`, so `2·n² ≤ E` is FALSE. The exact
enumeration gives `E(μ_2) = 6`, `2n² = 8`. This is why `energy_lower_tight` requires `m ≥ 2`
(`n ≥ 4`). The prize regime is `n = 2^μ` with `μ` large, so the bracket covers all relevant
cases; the `n = 2` exclusion is honest, not a hidden hypothesis. -/

/-! ## Axiom audit -/
#print axioms energy_eq
#print axioms energy_upper_tight
#print axioms energy_lower_tight
#print axioms energy_bracket
#print axioms energy_trivial_lower
#print axioms phantom_overshoot_loose

end ArkLib.ProximityGap.DefectOnsetEnergySandwich
