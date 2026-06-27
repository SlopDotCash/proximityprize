# wf407 / B3-s128 — the s=128 KKH26 δ\* ceiling: Thorner–Zaman vs Myerson/Lehmer

**Thread:** B3-s128 (= #334-B3 = #357-T13 = #334-T15). **Date:** 2026-06-14.
**Verdict: WALLED** — the s=128 KKH26 δ\* ceiling reduces *exactly* to one named, recognized
open **effective analytic number theory** input (Thorner–Zaman / log-free Linnik PNT in the
AP `p ≡ 1 (mod n)` over the short interval `[n^β, 2n^β]`). The Myerson/Lehmer lacunary
cyclotomic-resultant route is **refuted as a substitute**. A clean axiom-clean reduction brick
pins the input and proves the surrounding chain is free.

## What the in-tree machine already is (read before re-attacking)

The whole B3 chain is built and wired, conditional on ONE named hypothesis:

- `KKH26ThornerZaman.lean` — `TZPrimeSupply n β supply` (the named [TZ24] hypothesis, *never an
  axiom*); the **counting half** `card_bigPrimeFactors_le` / `card_biUnion_bigPrimeFactors_le`
  (a nonzero integer ≤ M has ≤ log M/log x big prime factors) is **proven unconditionally**;
  `kkh26_good_prime_of_TZ` = the pigeonhole good-prime existence (conditional on `TZPrimeSupply`
  + the budget inequality `m·logM/log(n^β) < supply`).
- `KKH26PolyFieldCeiling.lean` — `kkh26_mcaDeltaStar_le_of_TZ`: the conditional headline,
  `δ* ≤ 1 − r/2^μ` at `p = Θ(n^β)`, conditional only on `TZPrimeSupply` + budget.
- `KKH26PolyFieldCeiling.lean` also records the collision-pair budget in paper form:
  `card_collisionPairs` proves `|collisionPairs μ r| = A(A-1)` and
  `card_collisionPairs_le_square` gives the common `A^2` upper bound, where
  `A = 2^r * C(2^(μ-1), r)`.
- `KKH26ThornerZamanConstructor.lean` — `tzPrimeSupply_of_subset`: discharge `TZPrimeSupply`
  from an *explicit finite list* of window primes (option (ii)). `KKH26ConcreteCeiling.lean` —
  full end-to-end at `n=4` with explicit primes, **no analytic NT**, axiom-clean.
- `Frontier/ThornerZamanInstance.lean` — concrete `tzPrimeSupply_{8,16,32,64}_{two,three}`
  (explicit primes in `[n^β, 2n^β]`).

So the *only* unproven input of the entire s=128 lane is the asymptotic supply
`(tzWindow n β).card ≥ n^{β−1−o(1)}`.

## The exact statement needed (the wall)

**`EffectiveTZLowerBound n β c`** (new brick `Frontier/WF407_B3_s128.lean`):
`c · n^{β−1} ≤ (tzWindow n β).card`, i.e. the window `[n^β, 2n^β]` of primes
`≡ 1 (mod n)` has `≥ c·n^{β−1}` elements. This is the explicit-constant form of
**[TZ24] Cor 3.1** (Thorner–Zaman, *Refinements to the prime number theorem in
arithmetic progressions*): via partial summation over the short interval,
`π(2x;n,1) − π(x;n,1) ≳ x/(φ(n)·log x)` at `x = n^β`, unconditional for **β > 12/5**,
conditional on Montgomery for β > 1.

- **Formalizable?** Not with present Mathlib. It rests on *log-free zero-density estimates* for
  Dirichlet L-functions (Linnik-type), which Mathlib does not have (Mathlib has Dirichlet
  characters and the non-vanishing of `L(1,χ)`, but no zero-density / explicit short-interval
  PNT-in-AP). This is a multi-year formalization, independent of coding theory.
- **Citable?** Yes — [TZ24] is a published, recognized analytic NT result. The honest move
  (taken in-tree) is the named-`Prop` hypothesis pattern.

## The decisive structural finding (corrects a conflation in the census literature)

Two *different* "s-thresholds" were being conflated under "Parseval opened s=64":

- **(A) census / explicit-threshold route** `p > M` (char-0 → char-p transfer of the
  vanishing-sum tower, at *fixed small* `|F| < 2^256`). Parseval halves the resultant bound
  exponent (`SidonResultantImproved.abs_resultant_fourTerm_sq_le`: `|Res| ≤ 2^{3n/4}` vs the
  pointwise `2^n`; `tower_closed_finite_parseval`: threshold `(2^m)^{2^{m−2}}` vs
  `(2^m)^{2^{m−1}}`). At m=7 this drops `p > 2^448` to `p > 2^224 < 2^256` — **this** is the
  "Parseval extends census coverage to n=128 at |F|<2^256" statement.
- **(B) KKH26 Lemma-2 polynomial-field route** `p = Θ(n^β)` (the *actual* δ\* ceiling). Needs a
  prime to **exist** in `[n^β, 2n^β]` avoiding all collision resultants.

**Finding (numerically exact, `wf407_B3-s128_{budget,verdict,myerson}.py`):** for route (B) at
the prize regime (n ~ 2^{2^μ}, so log₂ n = 2^μ = s), the bad-prime budget
`m·logM/log(n^β) ~ 2^{O(s)}` is **dwarfed** by the supply
`n^{β−1} = 2^{(β−1)·s}` for *every* ρ∈{1/2,1/4,1/8,1/16} and *every* β>~2.4,
for **both** the coarse `M = s^{s/2}` and the Parseval `M = 2^{3n/4}`. The
resultant-bound choice only lowers an already-dominated term. Indeed at
prize scale `M_parseval = n^{3/4} < n ≤ p`, so the Parseval threshold `p > M` is *automatically*
met — the Parseval halving is **irrelevant to route (B)**. The gate is purely prime *existence*.

## Q2: Myerson/Lehmer lacunary cyclotomic resultant maxima — REFUTED as a substitute

Sharp upper bounds on `|Res(f, Φ_k)|` for sparse ±1 `f` (Myerson/Lehmer) would *tighten M*,
helping route (A). But route (B)'s gate is prime *existence* in a short AP interval, which is
**orthogonal to the resultant size** (the avoidance budget is already free). No improvement to
`M` can manufacture a polynomial-size prime. So Myerson/Lehmer **cannot** open s=128 without
Thorner–Zaman. (It *can* further improve the s=128 census-coverage route (A) at fixed |F|.)

## The landed brick (axiom-clean, `[propext, Classical.choice, Quot.sound]`)

`ArkLib/.../Frontier/WF407_B3_s128.lean` (imports only `KKH26ThornerZaman`):
- `EffectiveTZLowerBound n β c` — the named open input (the exact effective TZ statement).
- `effectiveTZ_to_supply` — **bridge**: `EffectiveTZLowerBound` + `supply ≤ c·n^{β−1}` ⟹
  `TZPrimeSupply n β supply` (reduces the opaque hypothesis to the quantitative TZ count).
- `budget_monotone_in_resultantBound` — the bad budget is monotone in `M`; a sharper `M`
  (Parseval) never *enables* what coarse `M` blocked.
- `effectiveTZ_dominates_polyBudget` — **the s=128 reduction**: given `EffectiveTZLowerBound`
  and the polynomial margin `m·logM/log(n^β) < c·n^{β−1}` (true at prize scale for both M's),
  the good prime exists. The whole chain runs the moment `EffectiveTZLowerBound` lands.

## 2026-06-26 follow-up: square-budget consumer

`KKH26PolyFieldCeiling.lean` now exposes the exact collision-pair cardinality and square bound:

```lean
collisionPairs_eq_offDiag
card_collisionPairs
card_collisionPairs_le_square
coarseResultantLogRatio_nonneg
kkh26_good_prime_avoids_collisions_of_TZ_square_bound
kkh26_mcaDeltaStar_le_of_TZ_square_bound
```

`KKH26S128Ceiling.lean` specializes those to `s = 128` and adds the paper-facing wrappers:

```lean
s128_collisionPairs_card
s128_collisionPairs_card_le_square
s128_supply_beats_budget_of_square_bound
kkh26_mcaDeltaStar_le_s128_of_square_bound
s128_tightResultantLog_eq
kkh26_mcaDeltaStar_le_s128_tight_square_bound
kkh26_mcaDeltaStar_le_s128_tight_square_bound_log
kkh26_s128_ceiling_of_thornerZamanPNTinAP_square
kkh26_s128_of_polyModulusCount_square
kkh26_s128_ceiling_of_thornerZamanPNTinAP_tight_square
kkh26_s128_ceiling_of_thornerZamanPNTinAP_tight_square_log
kkh26_s128_ceiling_of_thornerZamanPNTinAP_floor_tight_square_log
kkh26_s128_ceiling_of_thornerZamanPNTinAP_floor_tight_square_log_auto_nonneg
kkh26_s128_ceiling_of_thornerZamanPNTinAP_density_margin_tight_square_log
kkh26_s128_of_polyModulusCount_tight_square
kkh26_s128_of_polyModulusCount_tight_square_log
kkh26_s128_of_polyModulusCount_floor_tight_square_log
kkh26_s128_of_polyModulusCount_floor_tight_square_log_auto_nonneg
kkh26_s128_of_polyModulusCount_density_margin_tight_square_log
```

The new wrapper lets callers supply the familiar square budget
`(2^r * C(64,r))^2 * 448*log 2 / log(n^β) < supply` directly.  It does not remove the named
`EffectivePNTinAP` / `TZPrimeSupply` wall; it only removes a small arithmetic mismatch between the
paper estimate and the exact `collisionPairs 7 r` budget used by the Lean consumer.

The general μ-level square-budget consumer is now available directly in
`KKH26PolyFieldCeiling.lean`, so callers no longer need to specialize `s = 128` to use the
`A^2` collision-family upper bound.  `KKH26TightCeiling.lean` also has the fixed-`r` counterparts
for the sharper `(2r)^(2^(μ-1))` resultant-size budget:

```lean
tightResultantLogRatio_nonneg
tightResultantLog_eq
kkh26_good_prime_avoids_collisions_of_TZ_tight_square_bound
kkh26_mcaDeltaStar_le_of_TZ_tight_square_bound
kkh26_mcaDeltaStar_le_of_TZ_tight_square_bound_log
```

`Frontier/_KKH26ThornerZamanTightBridge.lean` now composes the generic
`ThornerZamanPNT -> TZPrimeSupply` reduction with that normalized tight square-budget consumer:

```lean
kkh26_ceiling_of_thornerZamanPNT_tight_square_bound_log
kkh26_ceiling_of_thornerZamanPNT_natFloor_tight_square_bound_log
kkh26_ceiling_of_thornerZamanPNT_floor_tight_square_bound_log
kkh26_ceiling_of_thornerZamanPNT_floor_tight_square_bound_log_auto_nonneg
kkh26_ceiling_of_thornerZamanPNT_density_margin_tight_square_bound_log
```

The auto-nonneg floor form is the canonical consumer: its bad-prime budget is compared directly
against `⌊tzDensityLB n β ε⌋₊`, with neither a separate `supply` witness nor a separate
`0 ≤ tzDensityLB n β ε` side condition.  The density-margin form is one step more paper-facing:
it replaces the floor comparison by the real sufficient condition `budget + 1 ≤ tzDensityLB`.

At `s = 128`, the tight variants replace the coarse `448*log 2` factor by either
`log((2r)^64)` or the normalized form `64*log(2r)`.  The canonical s=128 floor-supply wrappers
are:

```lean
kkh26_s128_ceiling_of_thornerZamanPNTinAP_floor_tight_square_log
kkh26_s128_ceiling_of_thornerZamanPNTinAP_floor_tight_square_log_auto_nonneg
kkh26_s128_ceiling_of_thornerZamanPNTinAP_density_margin_tight_square_log
kkh26_s128_of_polyModulusCount_floor_tight_square_log
kkh26_s128_of_polyModulusCount_floor_tight_square_log_auto_nonneg
kkh26_s128_of_polyModulusCount_density_margin_tight_square_log
```

These are only arithmetic relaxations of the bad-prime budget; the polynomial-modulus prime-count
input remains the analytic wall.

## Verdict

**WALLED** to the named analytic input `EffectiveTZLowerBound` = effective Thorner–Zaman /
log-free Linnik PNT-in-APs (β > 12/5 unconditional). The s=128 prize rows are **not** gated by
the resultant bound (Parseval/Landau/Myerson-Lehmer), only by prime existence at polynomial
field size. Honest partial progress: the exact open statement is pinned as a citable named
`Prop`, the reduction is proven axiom-clean, and the Myerson/Lehmer alternative is refuted.

**Artifacts:** `Frontier/WF407_B3_s128.lean`,
`Frontier/_KKH26ThornerZamanTightBridge.lean`,
`scripts/probes/wf407_B3-s128_{budget,verdict,myerson}.py`.
**What remains:** formalize/cite `EffectiveTZLowerBound` (= [TZ24]); or, for *non*-prize
fixed-|F| rows, push the Parseval/Myerson census-coverage route (A) further. Neither closes the
prize core.
