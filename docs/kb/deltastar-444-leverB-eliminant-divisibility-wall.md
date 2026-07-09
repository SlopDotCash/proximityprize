# Lever-B: eliminant / norm-degree bounds SIZE not COUNT — confirmed divisibility wall (2026-06-17)

**Issue #444 · proximity prize.** Task **Lever-B**: try to bound the char-p SUPPLY surplus
`Spur_r = E_r(μ_n/F_p) − E_r^{c0}` via the **eliminant / resultant degree** of the relation variety,
i.e. bound the number of `≤2r`-term `±`-sums `α` of `2^μ`-th roots of unity with `p | N(α)`
(`N(α) = Res(Φ_n, α)` the cyclotomic field norm). **Verdict: CONFIRMED WALL.** The eliminant bounds
the SIZE of `N(α)` and the DEGREE `φ(n)`, but NOT the COUNT of short `α` with `p | N(α)` — that count
IS the surplus. No bound on `Spur_r`. (Honesty contract upheld.)

Probes (EVIDENCE, exact, not proof):
- `scripts/probes/probe_444_leverB_eliminant_normcount.py` (calibration, relation census, carrier count)
- `scripts/probes/probe_444_leverB_divisibility_wall.py` (size bound `|N|≤k^{φ(n)}`, carrier p-dependence)

## 0. CALIBRATION (reproduced first, as required)

`E_r^{c0}` brute baseline = the cyclotomic-ℚ-basis exact count, NOT `(2r−1)!!·n^r` (an over-counting
upper bound): `E_2(μ_8)=168` (vs 192), `E_2(μ_16)=720` (vs 768), `E_2(μ_32)=2976` (vs 3072),
`E_1=n` exactly. Matches in-tree `probe_char0_energy_check_407.py`. `Spur_r` is measured against the
BRUTE baseline. The `(2r−1)!!` is the count of genuinely PAIRED (ℤ[ζ]-vanishing, antipode-paired)
relations and is the leading term.

## 1. The eliminant gives a SIZE bound (verified exactly)

For a length-`k` `±1` relation `α`, the resultant `N(α) = Res(Φ_n, α)` satisfies the height/Bezout
bound `|N(α)| ≤ (‖α‖_1)^{φ(n)} = k^{φ(n)}`, with `deg_X Res = φ(n)`. Verified exactly:

| n | φ(n) | k | max\|N(α)\| | bound k^{φ(n)} | holds |
|---|------|---|------------|----------------|-------|
| 8  | 4 | 4 | 64    | 256    | yes |
| 8  | 4 | 6 | 144   | 1296   | yes |
| 16 | 8 | 4 | 4096  | 65536  | yes |
| 16 | 8 | 6 | 20736 | 1679616| yes |

So the eliminant DEGREE (`φ(n)`) and SIZE (`≤ k^{φ(n)}`) of each `N(α)` are genuinely controlled.

## 2. But the eliminant does NOT bound the carrier COUNT (the surplus)

A prize `p` is a surplus carrier IFF `p | N(α)` for some short `α`. For a FIXED prize `p` the carrier
count `#{α length ≤2r : p | N(α)}` is the thing `Spur_r` actually counts. It is wildly **p-dependent**
and **unbounded** by any constant times the paired `(2r−1)!!`. n=16, depth ≤4, paired baseline `3!!=3`:

```
   p   | #carriers (p|N) | ratio / (2r-1)!!
   17  |     6880        | 2293.3
   97  |      960        |  320.0
  113  |      512        |  170.7
  193  |        0*       |    0.0   (*distinct-±1 census; 193 IS a carrier via a coeff-2 relation)
  257  |      384        |  128.0
  337  |      256        |   85.3
  401  |        0        |    0.0
```

The ratio ranges from 0 to 2293 with NO p-independent cap. Lever-B therefore cannot deliver
`carriers ≤ C·(2r−1)!!` and cannot give `E_r ≤ (2n log m)^r`.

The `0` rows `{193,241,353,401,433}` are exactly the no-carrier primes of the **distinct-±1** census,
not of the full supply object: e.g. `193 | N(z^0 + z^1 − 2z^8) = 6562 = 2·17·193` is a **coeff-2
(repeated-root)** carrier (256 such short relations exist). This re-confirms the Unify-A/B
consolidation — the distinct-±1 generator is a strict sub-object of supply `{±1,…,±r}`-coeff
relations — and shows widening the alphabet does NOT rescue Lever-B: coeff-≤r relations still have
`‖α‖_1 ≤ rk` so `|N(α)| ≤ (rk)^{φ(n)}`, size bound intact, count still p-dependent.

## 3. The structural reason it bottoms out at divisibility

At the prize scale `r ~ log m ≈ 128`, depth `k = 2r ≈ 256`, `n = 2^30`, `φ(n) = 2^29`. The norm
budget `k^{φ(n)} ≈ 256^{2^29} = 2^{2^32}` is astronomically larger than the prize `p ~ n·2^128 ~
2^158`. Short-relation norms VASTLY exceed `p`, so `p | N(α)` is **generic, not rare**. The eliminant
controls `|N(α)|` and `deg`, but the number of large prime divisors of a generic integer of that size
is unbounded — and which short `α` have `p | N(α)` is exactly the open divisibility question. The
char-0 proxy confirms the regime gap: at small `n` (small `φ`) the norms are too small to reach a
`~10^9` prime, so BabyBear/KoalaBear give 0 carriers — the carriers only switch on once `φ(n)` is
large enough for `N(α)` to reach prize size, which is precisely the prize regime.

## 4. Connection to low-weight-multiple / Mersenne literature

The carrier question "how many short `±`-relations of `2^μ`-th roots have norm divisible by prize `p`"
is the cyclotomic analogue of the low-weight-multiple / `2^p−1`-large-factor wall
(`arklib-bchks-conj112`): a SIZE/degree budget (`|N(α)| ≤ k^{φ(n)}`, here; `2^p−1`, there) does not
bound the count of prize-size divisors. Both bottom out at the same divisibility wall.

## 5. Honest verdict

**CONFIRMED WALL.** Lever-B (eliminant / resultant degree) is a genuine SIZE/DEGREE bound on each
`N(α)` but **does not bound the COUNT** of short relations with `p | N(α)` — that count is the surplus
`Spur_r` itself, and it is p-dependent and unbounded by `(2r−1)!!`. No new bound on `Spur_r`. The open
core is unchanged: the magnitude/divisibility of `N(α)` over short `±`-relations at `r ~ log m`,
`n = 2^30` = the 25-year thin-subgroup BGK wall.

| axis | score | note |
|---|---|---|
| novelty | 5 | first explicit eliminant SIZE-bound `\|N\|≤k^{φ(n)}` + carrier-count p-dependence table |
| insight | 6 | separates SIZE/DEGREE (controlled) from COUNT (the wall); coeff-2 carrier reconciliation |
| proximity | 3 | confirms wall; does NOT bound Spur_r (honestly) |
| feasibility | 3 | divisibility of `N(α)` at `r~log m`, `n=2^30` is the open residual |

**No closure claimed.** Cross-refs: `deltastar-444-unifyA-supply-eq-demand-consolidation`,
`arklib-bchks-conj112-reduction`, `deltastar-444-frontier-synthesis-NOLARP-2026-06-16`,
memory `arklib-444-onBGK-verdict-settled`.
