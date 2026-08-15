# δ* #466 — SYZ6 finer-grading degenerate-channel ceiling (2026-07-10)

**File:** `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ6FinerGradingCeiling.lean`
(axiom-clean: `propext, Classical.choice, Quot.sound`; no `sorry`).

## Result

Unconditional production rate-`1/2` ceiling over the first certified prize field
`P = 2^30·(2^128 + 192) + 1`:

```
mcaDeltaStar (evalCode g (2^30) (2^29 − 1)) epsStar ≤ 358612991 / 2^30 ≈ 0.33398
```

(`firstPrime_rateHalf_mcaDeltaStar_le_exact`; the intrinsic form
`firstPrime_rateHalf_mcaDeltaStar_le_syz6` gives `≤ predecessorRadius (2^30) (342·2^20)`).

This sharpens the SYZ4 rung `369098751/2^30 = 11/32 − 2^-30 ≈ 0.34375`
(`_SYZ4DegenerateChannelCeiling.lean`); `syz6_radius_lt_syz4` records the strict inequality.

## How: same degenerate channel, finer grading

SYZ4 used `64` blocks of `2^24`, core `N={0..30}` (31 blocks), three `11`-block agreement
regions, agreement subsets of `42` blocks, complements `22`, giving `3·22·2^24 = 1107296256 > 2^30`
bad scalars at `predecessorRadius (2^30) (22·2^24)`.

SYZ6 refines to **`1024` blocks of `2^20`**:
- core `N = {0..510}` (`C = 511` blocks), degree `511·2^20 = 535822336 < 2^29` (degree cap OK);
- three agreement regions of `R = 171` blocks: `A₀={511..681}`, `A₁={682..852}`, `A₂={853..1023}`;
- each subset agrees on `N ∪ Aⱼ` = `682` blocks, `t = 682·2^20 = 715128832 ≥ 2^29`;
- its complement `2R = 342` blocks carries the bad scalars;
- `3·342·2^20 = 1075838976 > 2^30` (`badScalar_count_over_budget`), mass `> epsStar`
  since `P < 1075838976·2^128` (margin `2097152·2^128`);
- radius `= (342·2^20 − 1)/2^30 = 358612991/2^30`.

## Design / optimum

At block count `B` with `D = 3` subsets, minimize radius over core size `C`, region size
`R = (B−C)/3` subject to the degree cap `C·blk < 2^29` (i.e. `C < B/2`) and the over-budget
constraint `3R > C`. Optimum: `C = B/2 − 1` (largest the cap allows, with `B−C ≡ 0 mod 3`),
radius `= (2R·blk − 1)/2^30`. As `B → ∞` this `→ 1/3⁺`, the `D=3` infimum `(1−ρ)/(2−ρ)=1/3`
at `ρ=1/2`, approached but not attained. At `B=1024`: `C=511`, `R=171`, radius `358612991/2^30`.

**Honest gaps.**
- The remaining gap to `1/3 = 0.33333` (≈ `0.00065`) is **pure lattice** — a finer grading
  (larger `B`, e.g. `2^13` blocks of `2^17`, optimal `C = 2^12−1`, radius `→ 357913941/2^30`)
  closes it further at the cost of a heavier (but still per-region-constant) proof. `1/3` is the
  unattained infimum.
- The conceptual gap `[Johnson 1 − √(1/2) ≈ 0.2929, 1/3]` is **untouched** — Johnson remains
  strictly below, no contradiction.
- The unconditional good-side floor `178956971/2^30 ≈ 0.1667` is unchanged.
- The CORE (pinning `δ*` exactly) remains **OPEN**: sharpening the ceiling says nothing about
  `δ*` itself.

## Proof-engineering note (why it does not blow up at 1024 blocks)

The channel/pencil machinery (`pencilScalar`, `mcaEvent_pencil`, `rsCode_eq_of_agree_on_card_le`,
`binaryPow`, `slot_injective`) is restated verbatim from SYZ4 and is grading-independent (the
slot-disjointness `decide` runs over the fixed `nd`-pair inventory `{(1,1),(2,1),(3,2)}` raised to
`2^30`, not over blocks). The label-combinatorics consistency facts (`fact_S`, `fact_A`,
`fact_nd_inj`) — proved in SYZ4 by whole-range `decide` over `range 64` — would be infeasible by
`decide` over `range 1024` (Finset-union membership per value). SYZ6 instead proves them
**arithmetically**, constant work per region: `fin3_cases` (`j = 0 ∨ j = 1 ∨ j = 2`, `rcases … with
rfl` substitutes the `OfNat` literal so region-value lemmas match), region-normal-form lemmas
`m1_*`/`m0_*`/`nd_A0/A1/A2` reduce the block `if`-thresholds, and the block counts use
`filter_mem_SLab`/`card_SLab` (`|SLab j| = 511 + 171 = 682` via disjoint union) instead of a
`range 1024` filter `decide`. Full elaboration ~24s under `pg-iterate.sh` (no build lock).

Pitfall: `fin_cases j` yields `Fin.mk` literals that do **not** match `OfNat` `0/1/2` in named
rewrite lemmas ("did not find pattern"); `rcases (fin3_cases j) with rfl | rfl | rfl` substitutes
the `OfNat` literal and matches. `le_or_lt` is not in scope in this toolchain — use
`rcases (by omega : … ∨ …)`.
