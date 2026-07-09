# δ* sweep A11 — Thinness-essential necessary condition (regime-gating + method exclusion)

**Date:** 2026-06-14 · **Actionable:** A11 (merged 407-T18) · **Status:** PARTIAL (axiom-clean brick)
**Artifacts:**
- `ArkLib/Data/CodingTheory/ProximityGap/Frontier/Sweep_A11_ThinnessEssential.lean` (axiom-clean)
- `scripts/probes/sweep_A11_thinness.py` (exact FFT witness data)

## The fact

The prize-conjecture **floor**

> `(FLOOR n p)` :  `B(μ_n) ≤ √(2·n·log p)`,  `B(μ_n) = max_{b≠0} ‖Σ_{x∈μ_n} e_p(bx)‖`

is **NOT a statement for all subgroup sizes** — it is regime-gated. At the worst structured prime
(Fermat `p = 65537 = 2^16+1`, `v₂(p−1) = 16`), varying `n = 2^μ` (exact FFT, probe):

| regime          | n        | β = log_n p | R = B/√(2n log p) | floor |
|-----------------|----------|-------------|-------------------|-------|
| THIN (prize)    | 4,8,16   | 8.0,5.3,4.0 | 0.42,0.59,0.73    | TRUE  |
| intermediate    | 32       | 3.2         | 0.95              | true  |
| **thick**       | **64**   | **2.67**    | **1.16**          | **FALSE** |
| **thick**       | **128**  | **2.29**    | **1.05**          | **FALSE** |
| very thick      | 256+     | ≤ 2         | < 1               | true  |

So `(FLOOR)` is **violated** in the intermediate-thickness window `β ∈ (≈2.3, ≈3.2)` at structured
2-power primes, and **holds** in the thin prize regime (`β ≥ 4`, `n ≤ p^{1/4}`) even at the worst
Fermat prime. The optimal conjecture is specifically a **thin-subgroup** statement.

The exact crossing sits between `β = 3.2` (n=32, R=0.946, true) and `β = 2.67` (n=64, R=1.158,
false): `R > 1` first at `n=64`. (Earlier #407 work refined "thin-essential" to "minimal-`v₂(p−1)`-
essential" — the violations are sharpest at high `v₂(p−1)`; the prize sits in the floor-TRUE zone.)

## What the Lean brick proves (axiom-clean, `[propext, Classical.choice, Quot.sound]`)

Two pivotal **integer-pinned** witnesses (squared, sqrt-free form `B² ≤ 2 n log p`), using the
rational bracket `11 < log 65537 < 12` (proven via `Real.exp_one_lt_d9` / `exp_one_gt_d9`):

- `floor_false_at_thick` : `n=64`, `B ≥ 43` ⟹ `B² ≥ 1849 > 1536 ≥ 2·64·log p` ⟹ **floor FALSE**.
- `floor_true_at_thin`  : `n=16`, `0 ≤ B ≤ 14` ⟹ `B² ≤ 196 ≤ 352 ≤ 2·16·log p` ⟹ **floor TRUE**.
- `regime_gated` : packages the two — `(FLOOR)` is simultaneously false thick / true thin.

The `B`-bounds `B(μ₆₄)=43.633 ≥ 43`, `B(μ₁₆)=13.838 ≤ 14` are the only **analytic inputs** (the
Gauss-period magnitudes, probe-certified to 4 sig figs — margins ≫ float error). Everything else is
exact, machine-checked real arithmetic. (n=128 needs `B≥56` but `B(μ₁₂₈)=55.93`, so it requires a
tighter `log` bound than `<12`; n=64 alone is airtight and suffices.)

## The method-exclusion corollary (FULLY PROVEN logic)

Model a proof "method" as `FloorMethod` = a certificate predicate `Cert : ℝ → Prop` + an analytic
profile `Bval : ℝ → ℝ` + a soundness field `Cert n → FloorHolds n (Bval n)`. Define

> `ThicknessMonotone M` :  `∀ n₀ n, Cert n₀ → n₀ ≤ n → Cert n`

— the defining property of every thickness-uniform technique (di Benedetto 2003.06165 Thm 3.1 /
generic sum-product / large sieve: their subgroup bound improves monotonically as `|H|` grows).

- `thicknessMonotone_method_cannot_certify_thin` : a sound, thickness-monotone method with the genuine
  `B(μ₆₄) ≥ 43` at the thick witness **cannot** certify the floor at the thin prize witness `n=16`
  (monotonicity carries `Cert 16 → Cert 64`; soundness forces `FloorHolds 64`; contradicts
  `floor_false_at_thick`).
- `certifying_thin_method_is_thinness_essential` : equivalently, any sound method that DOES certify
  the prize-thin floor **must not be thickness-monotone** — it must *fail* at the thicker `μ₆₄`.

This is a genuine **necessary condition on any proof of the prize floor**: it must be
*thinness-essential*. It excludes the entire class of thickness-monotone arguments — a real
constraint that reconciles the two concurrent #407 facts (β<4: sum-product applies but the bound can
be FALSE; β≥4: bound TRUE but sum-product vanishes; the prize sits exactly at the boundary).

## Honest status

PARTIAL. `(FLOOR)` itself in the prize regime (the open BGK/Paley wall) is NOT proven. This brick
proves the **regime-gating** and the **method-exclusion corollary** — a constraint on the solution,
not the solution. No fabricated closure. The witness `B`-bounds are honest probe-certified analytic
inputs, exactly as `B(μ_n)` is treated throughout the cone.

## Cross-refs
- #407 comment 2026-06-14T21:04:01Z (407-T18 regime-gating) + the `v₂(p−1)`-gated refinement.
- `Frontier/RegimePin.lean` (the complementary regime arithmetic: `index_const`, `beta_at_2pow32`,
  `burgess_gate`).
- `CumulantFermatObstruction.lean` / `SubgroupAdditiveEnergyFermat65537.lean` (same Fermat witness,
  energy side).
