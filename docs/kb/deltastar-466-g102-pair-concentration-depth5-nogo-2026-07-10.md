# Issue #466 G102: depth 5 is out of reach of cardinality + pair-sum concentration

Date: 2026-07-10

## Statement

G87 discharged the production depth-four cutoff of the padded collision lane from a single
input: the pair-sum concentration `M = max_c pairCount S c`, via `J_4 ≤ (M+1)·n^6` and the
Stepanov-method bound `M ≤ ~4·n^{2/3}` (Garcia–Voloch 1988 / Heath-Brown–Konyagin 2000).  The
depth-5 analog `J_5 ≤ (M+1)·n^8` was measured ~`2^26` over the production Wick budget, leaving
open whether a smarter `(n, M)`-chain, sharper constants, or a stronger concentration theorem
could close depth 5.

**G102 proves they cannot, axiom-cleanly.**  The chain is extremally tight in both parameters:
the interval × Sidon hybrid

```text
S = { 5M·x + u : x ∈ ErdősTurán(b), u ∈ [0, M) },   ErdősTurán(b) = {2b·i + (i² mod b)}
```

at `(b, M) = (509, 2^21)` has cardinality `509·2^21 ≈ 2^30`, pair-sum concentration `≤ 2^22`
(exactly the Stepanov level `4·n^{2/3}`), and — by Cauchy–Schwarz against its `O(Mb²)`-sized
sum support — depth-5 equal-sum mass exceeding the production depth-5 Wick share:

```text
219‼ · (2^30)^5  <  J_5(S) · C(110,5)² · 105!        (margin > 2^16).
```

So **no envelope in `(cardinality, pair-sum concentration)` alone — sound for all sets — can
absorb the depth-5 sector**.  The exact-integer probe further measures that the `(n, M)` window
at depth 5 is *empty*: even perfect concentration `M = 2` (Sidon-optimal) admits witnesses at
`J_5 ~ n^8/10`, above budget.  The same witness family scales as `J_s ≳ M·n^{2s-2}/(10s)` at
every depth, so pair statistics are closed as an input class for all depths ≥ 5.

## Lean content (`Frontier/_G102PairConcentrationDepthFiveNoGo.lean`)

- `cs_floor` / `cs_floor_of_bounded` — depth-generic Cauchy–Schwarz floor
  `(n^s)² ≤ |sumImage|·J_s`, with `|sumImage| ≤ sL+1` for sets in `[0, L]`;
- `etFun_add_rigid` — Erdős–Turán four-point rigidity at every odd prime (`2p`-digit split +
  the `(i−k)(i−l) = 0` argument in `ZMod p`);
- `pairCount_etSidon_le` — the Erdős–Turán set is Sidon (`pairCount ≤ 2`);
- `card_hybrid`, `hybrid_le`, `pairCount_hybrid_le` — the hybrid witness has cardinality `bM`,
  support `≤ 10Mb² + M`, concentration `≤ 2M` (pair fibers factor through div/mod at spacing
  `5M`);
- `production_depth5_kernel` — the exact kernel inequality at `(509, 2^21)` vs `(2^30, 110)`;
- `depth5_pair_concentration_no_go` — the headline existence statement.

## Consequences and honest scope

- The tool-shape doctrine sharpens: the certificate that closes depth ≥ 5 must see
  **triple-scale or genuinely multiplicative** structure of `μ_n` — no pair statistic
  (energy `E(H)`, concentration `M`, or any function thereof with the cardinality) suffices.
- Bonus probe finding: real subgroups measure `M(μ_n) = 2` at every tested scale (consistent
  with O160 SidonModNeg) — and the no-go shows even that exact knowledge cannot close depth 5.
- This refutes a class of *approaches*, not `FourthPowerSaddleDCEnergy` or δ*; depths ≥ 5 of
  the padded collision lane remain open pending a non-pair certificate (e.g. triple-sum
  concentration `max_a N_3(a)`, for which no Stepanov analog is currently recorded).

Probe: `scripts/probes/probe_466_g102_pair_concentration_tightness.py` (exact integers;
outputs archived at `scripts/probes/_out_466_g102_tightness.txt`).
