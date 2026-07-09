# A07 — Discharge InteriorCeiling at k=2 (the r=3 slice): first decisive higher-dim test

2026-06-14, sweep worker A07 (merged 357-T02; 371-T01).

## Verdict: PARTIAL — the r=3 (k=2) interior-ceiling pin SURVIVES numerically at all
prize-relevant primes; the Lean discharge was ALREADY landed and axiom-clean in tree.

## What A07 asked

At `n = 8`, `mu = 3`, `rho = 1/4` (the dimension-two / affine code `c0 + c1*x` on the
smooth domain `x_i = g^i`), the KKH26 interior ceiling is `delta* = 1 - 3/2^mu = 5/8`,
strictly in-window: Johnson `1 - sqrt(1/4) = 1/2 < 5/8 < 3/4 =` capacity. The actionable
asked to exhaustively enumerate the **k=2 bad-scalar count** for wide-circuit/pencil census
stacks and check it against the **KKH26 spread `2^3 * C(4,3) = 32`**; if the below-ceiling
count stays `<= 32` the r=3 pin survives, else `InteriorCeiling_k2_REFUTED`. Cross-check
field-independence at `p = 12289, 65537`.

## The pin structure (two-sided, both sides already PROVEN in tree)

The pin lives in `ArkLib/Data/CodingTheory/ProximityGap/KKH26DimTwoPin.lean`
(namespace `ArkLib.ProximityGap.KKH26DimTwo`), axiom-clean
(`[propext, Classical.choice, Quot.sound]`, no `sorry`):

- **GOOD side** — `dimTwo_badScalars_card_mul_twelve_le`: for EVERY stack `(u0,u1)` and
  agreement threshold `> 3` (i.e. `(1-delta)*n > 3`, threshold `t >= 4`, strictly below the
  ceiling radius), `#bad * 12 <= n(n-1)(n-2)`, i.e. `#bad <= n(n-1)(n-2)/12 = 28` at `n=8`.
  Mechanism = **triple-ownership**: each bad scalar owns `>= 12` ordered non-collinear
  `u1`-triples inside its witness set (via the collinearity determinant
  `colDet u0 + gamma*colDet u1 = 0`), disjoint across distinct bad scalars, against the
  `n(n-1)(n-2)` ordered distinct triples. This is the literal generalization of the `r=2`
  pair-ownership count (k=1) to triples (k=2).
- **BAD side** — KKH26 witness spread: the ceiling stack `(u0,u1) = (x^3, x^2)` at the
  ceiling threshold `t = 3` reaches `#bad >= 2^3 * C(4,3) = 32` (the in-tree lower-bound
  term of the `TwoPowerSubsetSumSpectrum` law `N(mu=3, r=3) = 2^3 C(4,3) + 2 C(4,1) =
  32 + 8 = 40`).
- **BAND nonempty** — `dimTwo_band_nonempty`: `28 < 32`, so the band `[28/p, 32/p)` is
  nonempty; that gap is exactly what lets the pin fire (`kkh26_dimTwo_deltaStar_pin`).
- **Concrete pin** — `deltaStar_dimTwo_pin_F12289`: `mcaDeltaStar(evalCode 4043 8 1, 28/12289)
  = 5/8`, machine-checked, the `g = 4043` generator of order 8 in `F_12289`.

So the LEAN half of A07 is not just feasible — it is **done**. The novel contribution of
this sweep is the numerical census + the field-independence cross-check the actionable
explicitly demanded, which the in-tree probe `probe_dim2_interior_ceiling.py` ran only at
`p = 257`.

## What this probe ran (`scripts/probes/sweep_A07_k2_interior.py`)

Wide-circuit / pencil census at `n = 8` over the THREE primes `257`, `12289` (NTT prime,
used by the Lean instance), `65537` (Fermat prime F_4), each with an order-8 generator
(`g = 4, 4043, 16` resp.; all verified `g^4 = -1`):

1. **BAD side**: `(x^3, x^2)` at the ceiling threshold `t = 3`.
2. **GOOD side**: ALL 64 monomial pencils `(x^e0, x^e1)`, `0 <= e0,e1 < 8`, plus 150 dense
   random + 150 low-entropy "wide circuit" stacks + a 1200-step hill-climb, at threshold
   `t = 4` (below the ceiling).
3. THREE independent badness checkers (exhaustive `mcaEvent`; derived `u1`-non-affine;
   fast pair-generated line) agree **byte-exactly** on all pencils + a random sample.

## Results

| prime p | ceiling stack `#bad @ t=3` | below-ceiling census max `@ t=4` | survives? |
|---|---|---|---|
| 257 | **40** (= full spectrum) | **9** (via `pencil(x^4,x^3)`) | yes |
| 12289 | **40** | 9 | yes |
| 65537 | **40** | 9 | yes |

(table reflects the converged run; see the probe's SUMMARY block.)

- BAD side reaches `40 >= 32 = ` the KKH26 spread at every prime (in fact the full
  spectrum `N(3,3) = 40`, identical across all three primes — q-independent count law).
- GOOD side below the ceiling never exceeds `9`, far below both the proven good bound `28`
  AND the spread `32`. So `below-ceiling #bad <= 32` holds with enormous slack:
  **the r=3 (k=2) interior-ceiling pin SURVIVES, decisively, at all three primes.**
- **Field-independence**: the ceiling count (40) and the good-side max (9) are IDENTICAL at
  `257 / 12289 / 65537` — the count law that drives the pin is q-independent, matching the
  q-independence of the `mcaDeltaStar` value claimed by the Lean pin.

The observed max of 9 is well inside the proven 28: the proven triple-ownership bound is not
tight at `n = 8`, but it does not need to be — the pin only needs `below-ceiling max < 32`,
and even the loose proven `28 < 32` suffices.

## Honest scope (why PARTIAL, not CLOSED-PROVEN)

- A07 is a **numerical-probe** actionable. The numerical contract (survives vs. refuted) is
  fully met: SURVIVES, at the prize-relevant primes, with q-independence confirmed.
- The PIN ITSELF is closed (axiom-clean Lean, already in tree). This sweep verifies it
  numerically and extends the evidence base to the prize primes; it does not itself add a
  new proven theorem — the Lean discharge predates this round.
- **This pins `delta*` only for the dimension-two (rate 1/4) member of the family.** The
  PRIZE regime is `n = 2^32`, `rho in {1/2,1/4,1/8,1/16}`, `eps* = 2^-128` — a production-
  dimension code, not the `k=2` slice. The per-rung ownership constant `K(r) = r!*...`
  degrades with the dimension `r`, and the full-window sweep is NOT a corollary of the
  ladder rungs (recorded in the Lean docstring). The decisive higher-dim test asked for by
  A07 (does the ownership mechanism survive the first dimension climb past pairs?) is
  answered YES: triples work exactly as pairs did, and the count still separates from the
  spectrum. That is the genuine increment — the mechanism is dimension-robust at `k=2`.

## Remaining gap

The production-dimension pin (`k = rho*n` with `n = 2^32`) is open. The ladder gives an
exact pin at each FIXED small rung `r` for large `mu`, but the constant `K(r)` degrades and
the union over rungs is not the window. The open core is unchanged: the window-interior
`delta*` at production dimension, equivalent to the four faces in the cone's open-core map
(B-form / energy-form / list-form / line-incidence). A07 closes the `k=2` numerical question
cleanly and confirms the Lean pin is sound and field-independent.

## Artifacts

- Probe: `scripts/probes/sweep_A07_k2_interior.py`
- Lean (pre-existing, axiom-clean): `ArkLib/Data/CodingTheory/ProximityGap/KKH26DimTwoPin.lean`
  (`dimTwo_badScalars_card_mul_twelve_le`, `dimTwo_band_nonempty`,
  `kkh26_dimTwo_deltaStar_pin`, `deltaStar_dimTwo_pin_F12289`).
