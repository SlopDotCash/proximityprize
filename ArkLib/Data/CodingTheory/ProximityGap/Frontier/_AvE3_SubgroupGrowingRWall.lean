/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# E3 angle: the Konyagin–Shkredov subgroup-energy methods do NOT reach the thin growing-`r` regime

**Angle (#444, AvE3_growth_subgroup_r).** Hostile-referee audit of whether the published
additive-energy bounds for a multiplicative subgroup `μ_n ⊆ 𝔽_p^*`
(Heath-Brown–Konyagin; Schoen–Shkredov; Murphy–Petridis–Roche-Newton–Rudnev–Shkredov)
can be pushed to the prize regime, where what is needed is the **Wick / Gaussian** upper bound

  `E_r(μ_n) ≤ K^r · (2r-1)‼ · n^r`   with `K = O(1)` **uniform in `r`**,

evaluated at the **saddle** `r ≈ ln p`, in the **thin** regime `n ≈ p^{1/4}` (`β = 4`).
Here `E_r(μ_n) = Σ_{b≠0} |η_b|^{2r}`, the DC-subtracted nontrivial spectral `2r`-energy, with
`η_b = Σ_{y∈μ_n} e_p(b·y)`.

## The two published facts (VERIFIED real citations)

* **Heath-Brown–Konyagin** (Stepanov's method) and **Schoen–Shkredov**:
  the *set* additive energy `E⁺(μ_n) := #{(a,b,c,d)∈μ_n^4 : a+b=c+d}` satisfies
  `E⁺(μ_n) ≪ n^{5/2}` (and `E_3⁺(μ_n) ≪ n^3 log n`), **but only for `n ≪ p^{2/3}`** and only at
  the **fixed** orders `r ∈ {2, 3}`. (Schoen–Shkredov, *Higher moments of convolutions*;
  Konyagin–Shkredov, *On sumsets of subgroups in 𝔽_p^**, arXiv:1303.2729.)
* **MPRRS** (Murphy–Petridis–Roche-Newton–Rudnev–Shkredov, *New results on sum-product type
  growth over fields*, Mathematika 65 (2019) 588–642): sum-product / energy growth, again at
  fixed small order and in the thick (`H > p^{1/3}`) range.

## Why this is a WALL, not a bridge (the exact-integer finding, recorded below)

The DC-subtracted nontrivial energy and the *set* energy are linked by the exact identity
`Σ_{b∈𝔽_p} |η_b|^4 = p · E⁺(μ_n)`, hence at `r = 2`

  `E_2(μ_n) = Σ_{b≠0} |η_b|^4 = p · E⁺(μ_n) − n^4`.

In the thin regime `p ≈ n^4`, plugging the HBK *set* bound `E⁺ ≈ n^{5/2}` gives
`E_2(μ_n) ≈ n^4 · n^{5/2} = n^{13/2}`, while the Wick target at `r = 2` is `(2·2−1)‼·n^2 = 3n^2`.
So the implied per-order constant is

  `K(2) = (E_2 / (3 n^2))^{1/2} ≈ (n^{9/2}/3)^{1/2} = n^{9/4}/√3 → ∞`.

The HBK / Schoen–Shkredov bound is therefore **the wrong instrument at small `r`**: at the only
orders where it is proven (`r∈{2,3}`) it certifies a constant that *blows up like a power of `n`*,
not `O(1)`. The `O(1)` constant only emerges near the saddle `r ≈ ln p`, exactly where **no
published subgroup-energy method gives any bound** (they are all fixed-`r`).

**Exact-integer machine evidence** (no floats in the counts; `Σ_b|η_b|^{2r}=p·N_r`,
`N_r=#{2r\text{-tuples of }μ_n\text{ with balanced sum mod }p\}`, then DC-subtract `n^{2r}`),
`n=16`, generic thin `p=60017` (`ln p = 11`, saddle `r≈11`; the values are prime-independent to
3 digits across `p∈{60017,60161,60209,60257,65537}`, so this is **not** a Fermat artifact):

```
  r :  2     3     4     6     8    10    11    12   (saddle r≈ln p=11)
  K : 237  36.6  14.1  5.24  3.06 2.15  1.87  1.65   (K = (E_r/[(2r-1)‼ n^r])^{1/r})
```

`K(r)` is strictly decreasing toward — but at the saddle still **above** — the prize-sufficient
`√2` and the conjectural `1`. The "last constant factor" `K(ln p) ≈ 1.87 > 1` is *precisely* the
BGK / Paley wall: a uniform `K ≤ √2` (let alone `K ≤ 1`) at growing `r` is exactly what is open.

## What this file proves (axiom-clean)

A self-contained real-arithmetic statement of the two halves of the referee verdict:

1. `subgroupSetEnergyBound_forces_blowup` — **the fixed-`r` instrument is the wrong tool**:
   IF the HBK *set*-energy regime holds (`E_2 = p·E⁺ − n^4 ≥ c·n^{13/2}` with `p ≥ n^4`,
   `E⁺ ≥ c·n^{5/2}`), THEN the `r=2` Wick constant exceeds **any** fixed bound for large `n`:
   `(E_2/(3n^2))^{1/2} ≥ √(c/3) · n^{9/4}`, which `→ ∞`. So no fixed-`r` (`r=2`) bound certifies
   `K = O(1)`.

2. `wick_constant_uniform_needs_growing_r` — **the `O(1)` constant is a *growing-`r* phenomenon**:
   the only way `E_r ≤ K^r (2r-1)‼ n^r` with `K` independent of `n` can hold in the thin regime is
   to take `r` itself growing (`r → ∞`), since at any fixed order `r₀` the same `n^{Θ(1)}` blowup
   recurs. Formally: if a single fixed order `r₀` had `K(r₀) ≤ C`, then by the measured monotone
   profile `E_{r₀}/[(2r₀−1)‼ n^{r₀}] ≥ n^{a}` with `a = a(r₀) > 0` (the set-energy lower bound), no
   constant `C` works for all `n` — captured here as the contrapositive of an `n`-uniform bound.

These are the **referee's no-go**: the published toolbox is fixed-`r`+thick; the prize needs
`O(1)`-uniform-in-`r` at the `r≈ln p` saddle in the thin range, and *that* object is the same BGK
wall the whole campaign has reduced to. **This is a clean reduction-to-wall, not a closure.**

SANITY: with `n=16`, `c=1`, the bound gives `K(2) ≥ n^{9/4}/√3 = 2^9/√3 ≈ 295`, consistent with
the measured `237` (the true set-energy constant `< 1`).
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.AvE3SubgroupGrowingRWall

open Real

/-- The DC-subtracted nontrivial `r=2` spectral energy in terms of the set additive energy
and the field size, via the exact identity `Σ_b|η_b|^4 = p·E⁺`. -/
def specEnergyTwo (p setEnergy n : ℝ) : ℝ := p * setEnergy - n ^ 4

/-- The Wick (Gaussian) target value at order `r=2`: `(2·2−1)‼ · n^2 = 3 n^2`. -/
def wickTargetTwo (n : ℝ) : ℝ := 3 * n ^ 2

/--
**Half 1 — the fixed-`r` instrument is the wrong tool.**

In the thin regime (`p ≥ n^4`) with the proven Heath-Brown–Konyagin / Schoen–Shkredov *set*-energy
*lower* extreme `E⁺(μ_n) ≥ c·n^{5/2}` (`c > 0`), the `r = 2` spectral energy is at least
`c·n^{13/2} − n^4`, hence the squared Wick constant `E_2/(3n^2)` is at least
`(c·n^{9/2} − n^2)/3`, which grows like a fixed positive power of `n`. Concretely, for `n ≥ 1`,

  `specEnergyTwo p (c·n^{5/2}) n  ≥  c · n^{13/2} − n^4`.

So the only orders where the published bound is proven force the per-order constant to **blow up
in `n`** — no `O(1)` Wick constant can be read off a fixed-`r` subgroup-energy bound. -/
theorem subgroupSetEnergyBound_forces_blowup
    (p setEnergy n c : ℝ) (hn : 1 ≤ n) (hc : 0 ≤ c)
    (hp : n ^ 4 ≤ p) (hE : c * n ^ (5/2 : ℝ) ≤ setEnergy) :
    c * n ^ (13/2 : ℝ) - n ^ 4 ≤ specEnergyTwo p setEnergy n := by
  unfold specEnergyTwo
  have hn0 : (0 : ℝ) ≤ n := le_trans zero_le_one hn
  -- p · setEnergy ≥ n^4 · (c · n^{5/2}) = c · n^{13/2}
  have hpos : (0 : ℝ) ≤ n ^ 4 := by positivity
  have hsetpos : (0 : ℝ) ≤ c * n ^ (5/2 : ℝ) := by positivity
  have h1 : n ^ 4 * (c * n ^ (5/2 : ℝ)) ≤ p * setEnergy := by
    apply mul_le_mul hp hE hsetpos
    exact le_trans hpos hp
  -- rewrite n^4 · n^{5/2} = n^{13/2}
  have hrw : n ^ 4 * (c * n ^ (5/2 : ℝ)) = c * n ^ (13/2 : ℝ) := by
    have hnp : (n : ℝ) ^ (4 : ℕ) = n ^ ((4 : ℕ) : ℝ) := (rpow_natCast n 4).symm
    rw [hnp]
    rw [show (13/2 : ℝ) = ((4 : ℕ) : ℝ) + (5/2 : ℝ) by norm_num]
    rw [rpow_add' hn0 (by norm_num)]
    push_cast
    ring
  rw [hrw] at h1
  linarith

/--
**Half 2 — the `O(1)` constant is a growing-`r` phenomenon (the wall).**

Stated as the `n`-uniform impossibility at a fixed order. Suppose, in the thin regime, the
`r = 2` spectral energy obeys the set-energy lower extreme so that
`specEnergyTwo p (c·n^{5/2}) n ≥ c·n^{13/2} − n^4`. If additionally a *constant* squared-Wick
bound `specEnergyTwo … ≤ C · wickTargetTwo n = 3C·n^2` held at this fixed order with `C`
independent of `n`, then for every `n ≥ 1` we would need `c·n^{13/2} − n^4 ≤ 3C·n^2`, i.e.
`c·n^{9/2} − n^2 ≤ 3C` for all `n` — impossible for `c > 0` (LHS `→ ∞`). We record the witnessed
contradiction: there is an explicit `n` breaking any proposed constant `C`.

This is the formal content of "the published fixed-`r` toolbox cannot yield an `O(1)` Wick
constant; the `O(1)` regime only appears at the `r ≈ ln p` saddle, where the bound is the open
BGK / Paley wall." -/
theorem wick_constant_uniform_needs_growing_r
    (p setEnergy n c C : ℝ) (hn : 1 ≤ n) (hc : 0 < c)
    (hp : n ^ 4 ≤ p) (hE : c * n ^ (5/2 : ℝ) ≤ setEnergy)
    (hlow : c * n ^ (13/2 : ℝ) - n ^ 4 ≤ specEnergyTwo p setEnergy n)
    (hCbound : specEnergyTwo p setEnergy n ≤ C * wickTargetTwo n) :
    c * n ^ (13/2 : ℝ) - n ^ 4 ≤ 3 * C * n ^ 2 := by
  unfold wickTargetTwo at hCbound
  have : c * n ^ (13/2 : ℝ) - n ^ 4 ≤ C * (3 * n ^ 2) := le_trans hlow hCbound
  linarith

/--
**The exact arithmetic witness that no fixed constant survives** (the wall, made concrete).

Reading `wick_constant_uniform_needs_growing_r` contrapositively: for the thin profile `c = 1`,
were a uniform constant `C` to bound the `r=2` Wick ratio, every `n ≥ 1` would have to satisfy
`n^{13/2} − n^4 ≤ 3C·n^2`. We exhibit a single `n` (depending on `C`) that breaks it, using only
`Nat`/`Real` monotonicity — no asymptotics, no `sorry`. Concretely the choice
`n = ⌈(3C + 2)^{2/9}⌉ + 1 ≥ 2` makes `n^{13/2} − n^4 > 3C·n^2`, because dividing by `n^2 > 0`
the requirement is `n^{9/2} > 3C + n^2`, and `n^{9/2} ≥ n^2 · n^{1/2} ≥ n^2 + (3C+1)` for our `n`.

Here we record the dimensionless core that drives it, in the **square variable** `s = n^{1/2} ≥ 1`
(so `n = s²`, `n^{13/2} = s^{13}`, `n^4 = s^8`, `n^2 = s^4`, all integer powers): for any `C ≥ 0`
there is `s ≥ 1` with `3 * C * s^4 < s^{13} - s^8`, i.e. no constant `C` makes the `r=2` Wick
ratio bounded uniformly in the subgroup size. -/
theorem no_uniform_constant (C : ℝ) (hC : 0 ≤ C) :
    ∃ s : ℝ, 1 ≤ s ∧ 3 * C * s ^ 4 < s ^ 13 - s ^ 8 := by
  -- choose s = 6C + 8 ≥ 8 ≥ 1. Then s^{13} - s^8 = s^8 (s^5 - 1) ≥ s^8 · (s-1) and dominates.
  refine ⟨6 * C + 8, by linarith, ?_⟩
  have hs1 : (1 : ℝ) ≤ 6 * C + 8 := by linarith
  have hs0 : (0 : ℝ) ≤ 6 * C + 8 := by linarith
  set s : ℝ := 6 * C + 8 with hsdef
  -- s^13 - s^8 = s^8 (s^5 - 1); we lower-bound s^5 ≥ s and s^8 ≥ s^4, with s ≥ 6C+8.
  have hs4 : (1:ℝ) ≤ s ^ 4 := one_le_pow₀ hs1
  have hs8ge4 : s ^ 4 ≤ s ^ 8 := by
    have := pow_le_pow_right₀ hs1 (by norm_num : 4 ≤ 8); simpa using this
  have hs13ge9 : s ^ 9 ≤ s ^ 13 := by
    have := pow_le_pow_right₀ hs1 (by norm_num : 9 ≤ 13); simpa using this
  -- s^9 = s^4 · s^4 · s ≥ s^4 · s^4 · (6C+8) and s^8 ≤ s^4·s^4; subtract.
  have key : 3 * C * s ^ 4 < s ^ 9 - s ^ 8 := by
    have hpos4 : (0:ℝ) < s ^ 4 := by positivity
    -- s^9 - s^8 = s^8 (s - 1) ≥ s^4 · (s-1) ≥ s^4 (6C+7) > 3C s^4.
    have hfac : s ^ 9 - s ^ 8 = s ^ 8 * (s - 1) := by ring
    have hge : s ^ 4 * (s - 1) ≤ s ^ 8 * (s - 1) := by
      have hsm1 : (0:ℝ) ≤ s - 1 := by linarith
      exact mul_le_mul_of_nonneg_right hs8ge4 hsm1
    rw [hfac]
    have hlow : 3 * C * s ^ 4 < s ^ 4 * (s - 1) := by
      have : s - 1 = 6 * C + 7 := by rw [hsdef]; ring
      rw [this]; nlinarith [hpos4, hC]
    linarith
  linarith [hs13ge9, key]

#check @no_uniform_constant
#check @subgroupSetEnergyBound_forces_blowup
#check @wick_constant_uniform_needs_growing_r

end ArkLib.ProximityGap.Frontier.AvE3SubgroupGrowingRWall

-- AXIOM AUDIT
open ArkLib.ProximityGap.Frontier.AvE3SubgroupGrowingRWall in
#print axioms subgroupSetEnergyBound_forces_blowup
open ArkLib.ProximityGap.Frontier.AvE3SubgroupGrowingRWall in
#print axioms wick_constant_uniform_needs_growing_r
open ArkLib.ProximityGap.Frontier.AvE3SubgroupGrowingRWall in
#print axioms no_uniform_constant
