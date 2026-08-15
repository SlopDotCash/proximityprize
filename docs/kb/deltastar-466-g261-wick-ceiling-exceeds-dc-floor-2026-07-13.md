# G261: the Wick/Gaussian moment ceiling exceeds the DC/Parseval floor by (2r-1)‼·q/n^r

Date: 2026-07-13
Issue: #466
Status: axiom-clean route no-go, not prize closure

## Question

The census / moment-method route to the prize collision moment lives between two ceilings:

- the **Wick/Gaussian main term** `Wick_r = (2r−1)‼ · n^r`, the natural upper bound a moment-method
  or Wick-pairing argument produces (the Gaussian `2r`-th moment count on `n` variables), and
- the **DC/Parseval floor** `DCfloor_r = n^{2r}/q`, the exact char-`p` moment the prize must
  lower-bound (the `b=0` DC mass the primitive-depth census reconstructs; see G63).

G63 proves the census is pinned *at or above* the floor (`q·census ≥ n^{2r}`), and G65 rules out any
nonnegative depth-reweighting yielding a strict weighted sub-floor. Those bound the census from
below. The quantitative question this note answers is conditional and exact: **how far apart are
Wick and DC on the side of the rank crossover where `n^r ≤ q`?** G262 records the sponsor-facing
scope correction across ranks five and six.

## Exact answer

The adversarial critic's fresh thin-prime family probe (`arklib-g56-frontier-resonant.json`, base-3
primitive census on `μ_n`, `n∈{8,16}`, thin regime `q = p`) exhibits the exact closed-form law

```text
Wick_r / DCfloor_r = (2r−1)‼ · q / n^r
```

verified to 12 significant figures on all 30 probe rows and reproduced exactly by the self-contained
integer probe `g261_wick_ceiling_exceeds_dc_floor_probe.py`.

Interpretation. The factor splits as `(2r−1)‼` times `q/n^r`. Under the explicit premise
`n^r ≤ q`, the ratio is at least `(2r−1)‼`; this is the exact content of G261's comparison.
It is not uniform across the two live sponsor ranks. G262 proves

```text
n^5 < P1,P2 < n^6.
```

Thus the G261 direction applies at rank five, where Wick lies hundreds of thousands of times above
DC. At rank six it reverses: DC is more than `400·Wick` at P1 and more than `200·Wick` at P2.
Combining with G63 gives `census_6 > 400·Wick_6` / `> 200·Wick_6`, so Wick cannot be an upper census
ceiling at rank six. See the G262 note for the exact division-free sponsor theorems.

## What is proved (Lean, axiom-clean over ℕ/ℝ, only Mathlib `Nat.doubleFactorial`)

File `Frontier/_G261WickCeilingExceedsDCFloor.lean`, namespace
`ArkLib.ProximityGap.Frontier.G261WickCeilingExceedsDCFloor`:

- `wick_mul_pow_eq_doubleFactorial_mul_dcFloorNum` — division-free exact identity
  `Wick_r · n^r = (2r−1)‼ · n^{2r}` (the cross-multiplied form of the ratio, no rational division).
- `wick_dcFloor_ratio_eq` — the exact real ratio `Wick_r / DCfloor_r = (2r−1)‼·q/n^r` for `0<n, 0<q`.
- `wick_ge_dcFloor_mul_doubleFactorial` — thin regime `n^r ≤ q` ⇒ `Wick_r ≥ (2r−1)‼ · DCfloor_r`.
- `wick_gt_dcFloor` — thin regime, `r ≥ 2` ⇒ `Wick_r > DCfloor_r` (strict overshoot; at the boundary
  `r=1, q=n` the ceilings coincide, so `r ≥ 2` is the honest strict hypothesis).
- `doubleFactorial_ratio_unbounded_step` — `(2(r+1)−1)‼ = (2r+1)·(2r−1)‼` (`r ≥ 1`): each depth step
  multiplies the ratio's `(2r−1)‼` factor by `≥ 3`, so the divergence is super-exponential, not a
  fixed-depth island.
- `not_wickCeiling_certifies_dcFloor` — packaged calibrated no-go.

Axioms `[propext, Classical.choice, Quot.sound]` on all six; the double-factorial recursion and the
identity are even lighter (no `Classical.choice`). No `sorry`, no `native_decide`, no `axiom`. Locked
build 3298 jobs green.

## Scope (honest)

Route-hygiene comparison, not a Jacobi estimate and not prize closure. It calibrates the exact gap
under its stated premise `n^r ≤ q`. G262 is the authoritative sponsor-rank scope: the premise holds
at rank five and fails at rank six, where characteristic-p DC/wraparound mass is provably super-Wick.
The surviving admissible route remains a genuinely joint, row-labelled sponsor-prime / Jacobi
estimate proved directly against the row label. CORE remains OPEN / ON-BGK.
