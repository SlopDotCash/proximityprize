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
below. The open quantitative question this note answers: **how far apart are the two ceilings the
route sits between, and does that gap help or hurt at prize depth on a thin 2-power subgroup?**

## Exact answer

The adversarial critic's fresh thin-prime family probe (`arklib-g56-frontier-resonant.json`, base-3
primitive census on `μ_n`, `n∈{8,16}`, thin regime `q = p`) exhibits the exact closed-form law

```text
Wick_r / DCfloor_r = (2r−1)‼ · q / n^r
```

verified to 12 significant figures on all 30 probe rows and reproduced exactly by the self-contained
integer probe `g261_wick_ceiling_exceeds_dc_floor_probe.py`.

Interpretation. The factor splits as `(2r−1)‼` (the Gaussian double-factorial, super-exponential in
depth) times `q/n^r` (exactly the thin-subgroup ratio: field size over the subgroup power). At a thin
prime, where the 2-power subgroup is small relative to the field (`q ≳ n^r`), the ratio is
`≥ (2r−1)‼`, which diverges super-exponentially at prize depth `r ≈ ln q`. The Wick ceiling therefore
sits a factor `(2r−1)‼·q/n^r` **above** the DC floor it would need to certify.

Consequence for the route. A moment-method argument that bounds the collision census by its own
Gaussian/Wick ceiling is off from the target Parseval floor by this super-exponential factor. G63
pins the census from below at the floor; G261 pins the Wick ceiling unboundedly above it. The moment
route is squeezed out from both sides at the thin prime and cannot beat Parseval by bounding through
its Wick ceiling.

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

Route-hygiene no-go, not a Jacobi estimate and not prize closure. It calibrates the exact,
`r`-uniform, thinness-essential gap between the moment route's own Wick ceiling and the target
Parseval floor. It does not restate G63 (a lower bound on the census); it bounds the distance between
the two ceilings and shows it diverges. The surviving admissible route remains a genuinely joint,
row-labelled sponsor-prime / Jacobi estimate proved directly against the row label — NOT through any
moment / Wick / census ceiling, which G261 shows is exponentially detached from the target at the
thin prime. CORE remains OPEN / ON-BGK.
