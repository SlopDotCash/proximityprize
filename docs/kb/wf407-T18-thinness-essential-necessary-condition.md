# WF407-T18 — Thinness is ESSENTIAL: a machine-checked necessary condition for the δ* floor

**Thread:** 407-T18 (thinness-essential necessary condition / B_∞ ← B_{log n} Sidon bootstrap).
**Date:** 2026-06-14. **Verdict: PARTIAL** (a structural constraint-on-the-solution, not a closure;
the prize floor stays open). Honesty contract held — no fabricated closure.

## The object

`B(μ_n) = max_{b≠0} ‖Σ_{x∈μ_n} e_p(bx)‖` = worst Gauss period of the smooth subgroup `μ_n ⊆ F_p^*`.
`m = (p−1)/n` distinct periods (η constant on multiplicative cosets). `β = log_n p` = thickness
exponent (β→1 = thick/large-subgroup, β large = thin). Prize: `p ≈ n·2^128`, `m = 2^128` (FULLY
DYADIC), `n = 2^μ`, so the prize is extremely THIN (`log m ≈ 128 ln 2`).

## What T18 claimed, and what the exact numerics show

**Claim (T18):** the optimal-looking bound `B ≤ √(2 n log p)` is FALSE in the thick window
`β ≈ 2.3–3.2` (measured at Fermat p=65537), excluding every thickness-monotone method as a matter
of LOGIC. **CONFIRMED and sharpened** by exact coset enumeration (no sampling):

### (1) The thick-window violation — exact (probe `wf407_T18-thinness_thickwindow.py`)
At Fermat `p = 65537 = 2^16+1`, `μ_n` = the order-`n` subgroup (`n = 2^μ`):

| μ | n | β=16/μ | m | B | B/√(2n log p) | verdict |
|---|---|--------|---|---|---------------|---------|
| 5 | 32 | 3.20 | 2048 | 25.21 | 0.946 | ok (just under) |
| **6** | **64** | **2.67** | **1024** | **43.63** | **1.158** | **FALSE** |
| **7** | **128** | **2.29** | **512** | **55.93** | **1.050** | **FALSE** |
| 8 | 256 | 2.00 | 256 | 52.31 | 0.694 | ok |

Violation band on the Fermat group: `β ∈ [2.29, 2.67]`, max ratio `1.158`. So `B² > 2 n log p` is
FALSE on realizable `μ_n`. **Exact witness** (probe `wf407_T18-thinness_exact_witness.py`, worst
frequency `b=1`): `B² = 1903.838…`, `2·64·log 65537 = 1419.567…`, `B² − 2n log p = +484.27`.

### (2) The mechanism is 2-ADIC m, not thickness alone (probe `wf407_T18-thinness_dyadic_vs_thick.py`)
At FIXED β, fully-dyadic `m` (odd-part 1) systematically INFLATES `B` vs odd-rich `m`:

- n=64, β≈2.5: most-dyadic B/√(2n log p) = 0.855 (logMeff/log m = 1.20) vs most-odd = 0.752 (0.92).
- n=32, both β: dyadic > odd at the same thickness.

`logMeff := B²/(2n)` (effective `log` of #independent periods) reaches `logMeff/log m = 2.146` at
the Fermat dyadic point — the periods are FAR more concentrated than `m` independent Gaussians. This
is the "power-of-2 is the worst index" phenomenon (consistent with prior KB: dyadic-tower
`M(2n)²≤2M(n)²` REFUTED, ratios to 3.86). The diagonal (odd-rich m) NEVER violates `S_p` (≤0.82).

### (3) Pinned necessary-condition constants (probe `wf407_T18-thinness_neccond_pin.py`)
- `c_p := B²/(n log p)`: max `2.682` (THICK-dyadic class) vs `≤1.27` (THIN class). **The prize
  target constant 2 in `√(2n log p)` is realizable-false in the thick class.**
- `c_m := B²/(n log m)`: max `4.29` (thick) vs `2.18` (thin). **Even the honest `log m`-scale
  constant is regime-dependent**: the Salem–Zygmund chaining constant `c=2` (in-tree
  `SalemZygmundChaining.lean`, `√(2 n log m)`) is an upper bound ONLY once thinness makes `log m`
  large. As `log m → ∞` at fixed n (thin limit) `c_m` drops toward and below 2 and stays there.

## The verdict: a NECESSARY CONDITION (constraint-on-the-solution)

**A proof method is *thickness-monotone* if it establishes `B² ≤ 2 n log p` by an inequality that
is tightest as `β→1` (di-Benedetto sum-product, generic completion, any bound improving as
`|μ_n|/p→1`).** Such a method applied to the Fermat witness would prove `B² ≤ 2 n log p` there —
contradicting `B² = 1903.84 > 1419.57`. Therefore:

> **No thickness-monotone method can prove the prize Gauss-period floor.** A valid proof MUST
> exploit a feature ABSENT in the thick witness — the **thinness** of the prize (`log m` huge).

Stronger form (from `c_m`): even an `√(2 n log m)`-targeting proof must use that the prize, despite
`m = 2^128` being fully dyadic, is THIN (`log m` large), since the constant-2 `log m`-scale is
violated (up to 4.29) on the thick-dyadic witness class. The Salem–Zygmund / EVT route in-tree is
therefore **correctly aimed** (its scale becomes valid exactly in the thin limit) — T18 does NOT
refute it; it pins WHY thinness is the load-bearing hypothesis the route must consume.

## The B_∞ ← B_{log n} Sidon-depth bootstrap: where it breaks

The moment/Sidon route proves `B ≤ (q E_r)^{1/2r}` from the even energies `E_r(μ_n)` up to depth
`r ≈ log m`. The "thick failure" is exactly that at SMALL `log m` (thick) the optimal depth `r` is
tiny and the bound is loose (the violations above are at `log m ≈ 6.2–6.9`); at LARGE `log m` (thin
prize, `log m ≈ 89`) the depth `r ≈ log m ≈ 128` and the bound is the operative one. The bootstrap
"break at β<4" is the regime where `B²/(n log m) > 2`: precisely the fully-dyadic thick band
`β ∈ [1.2, 2.7]` (every dyadic-ladder row with `logMeff/log m > 1`). This re-confirms (does not
contradict) the W4 deep-moment wall and the EVT `B ≈ √(n log m)` law (memory
`arklib-389-deep-moment-wall`, `232-T08`): the moment method needs depth `r ≈ log m`, valid only
where `log m` is large = thin.

## Lean brick (axiom-clean)

`Research/ProximityPrize/Frontier/WF407_T18Thinness.lean`:
- `ThicknessMonotoneTarget n p Bsq := Bsq ≤ 2·n·log p` (the named target).
- `thicknessMonotone_refuted_at_witness`: with `B² ≥ 1903` (enumeration) and `log 65537 < 11.0905`,
  `¬ ThicknessMonotoneTarget 64 65537 B²` — machine-checked refutation.
- `witness_ratio_gt_two`: `2·64·log 65537 < B²` (the constant-2 violation).
- `SatisfiesThinnessNecessaryCondition Method` + `thicknessMonotone_fails_necessaryCondition` +
  `necessaryCondition_of_declines`: the necessary condition as a `Prop`, with the proof that any
  thickness-monotone method fails it and that it is non-vacuous.

Axiom audit: `[propext, Classical.choice, Quot.sound]`. The numerics supply the exact witness `B²`;
Lean proves the logical refutation. The `log 65537 < 11.0905` bound is the certified evidence layer.

## What remains / new avenues

- The floor `B ≤ C√(n log m)` is UNCHANGED open (this is a constraint, not a closure).
- The necessary condition tells the next agent: the Salem–Zygmund route (`SalemZygmundChaining.lean`)
  is the correctly-aimed survivor — its open input `SubGaussianMGF` with `σ²=O(n)` MUST be proven
  using thinness (`log m → ∞`), and it should be checked that the proof never silently assumes a
  thickness-monotone sub-step.
- New attackable sub-direction: pin the EXACT thin-limit value of `c_m = lim_{log m→∞} B²/(n log m)`
  at fixed dyadic n (data suggests it descends toward a plateau in [1.0, 1.4]; this is the true
  prize constant, vs the artifact `c=2`). Cross-link to `232-T20` (constant ≈1.33 plateau).

## Probes
- `scripts/probes/wf407_T18-thinness_thickwindow.py` — the thick-window violation map (Fermat + diagonal).
- `scripts/probes/wf407_T18-thinness_scale_pin.py` — three-scale comparison + effective M.
- `scripts/probes/wf407_T18-thinness_dyadic_vs_thick.py` — dyadic-m vs thickness discriminator.
- `scripts/probes/wf407_T18-thinness_neccond_pin.py` — pinned necessary-condition constants `c_p, c_m`.
- `scripts/probes/wf407_T18-thinness_exact_witness.py` — exact rational certificate for the Lean brick.
