<!-- #444 / Paley Graph Conjecture (BGK β=4). Authored 2026-08-20. Reproduction audit of the
section-4.2 constant table of deltastar-444-paley-phase-cancellation-essay-2026-06-21.md, whose
generating script is not in the tree. HONEST STATUS: PALEY_SETTLED=false — unchanged. The table
REPRODUCES EXACTLY (4/4 rows, every published digit). Extending it one rung to n=128 (p=268437889,
M=55.0643, C=1.2757, C^2=1.6274) does two things: it breaks the "monotonically rising, not
saturating" caution the essay attaches to its own conclusion, and it lands C on the ~1.28 the
tail-temperature reading predicted and the correction dismissed. ONE POINT, not a saturation.
No proof, no disproof; this narrows a stated caveat and adds a re-runnable harness. -->

# Reproducing the Paley constant table, and what happens at n = 128

## 0. Why this exists

Section 4.2 of
[the Paley phase-cancellation essay](deltastar-444-paley-phase-cancellation-essay-2026-06-21.md)
reports a four-row table of the Burgess-regime constant

$$
C(n) \;=\; \frac{M}{\sqrt{n\log(p/n)}}, \qquad M \;=\; \max_{b\neq0}|\eta_b|, \qquad
\eta_b \;=\; \sum_{h\in\mu_n} e_p(bh),
$$

at "the smallest prime $\equiv 1 \pmod n$ near $n^4$". That table carries real weight in the
document: it is the basis of the closing assessment that the empirical picture is "consistent with
the conjecture being **true**", and of the single caution attached to that assessment.

The script that produced it is not in the tree. This note re-derives every entry from scratch,
records the outcome, and leaves behind a harness so the claim stays checkable:
`scripts/probes/probe_paley_C_table.py`.

## 1. Pinning the prime-selection rule

"Near $n^4$" is not by itself a rule. The reading that reproduces the published primes is

> $p$ = the least prime with $p \equiv 1 \pmod n$ and $p \ge n^4$.

It recovers all four published primes exactly — $4129$, $65537$, $1048609$, $16777601$ at
$n = 8, 16, 32, 64$ — so the table is unambiguous once this is written down. Recording it matters:
a different-but-plausible reading, "the prime with the highest $v_2(p-1)$ near $n^4$" (a rule the
essay does discuss, in its remark that maximal-2-adic primes are *not* worst), selects different
primes and produces different numbers. The two rules are easy to conflate, and only the first one
is the table's.

## 2. The table reproduces exactly

| $n$ | $p$ | $M$ | $C$ | $C^2$ | published $M$ / $C$ / $C^2$ | |
|---|---|---|---|---|---|---|
| 8 | 4129 | 7.5582 | 1.0692 | 1.1432 | 7.5582 / 1.0692 / 1.1432 | match |
| 16 | 65537 | 13.8375 | 1.1995 | 1.4388 | 13.8375 / 1.1995 / 1.4388 | match |
| 32 | 1048609 | 22.9834 | 1.2600 | 1.5877 | 22.9834 / 1.2600 / 1.5877 | match |
| 64 | 16777601 | 38.5286 | 1.3635 | 1.8590 | 38.5286 / 1.3635 / 1.8590 | match |
| **128** | **268437889** | **55.0643** | **1.2757** | **1.6274** | — | **new** |

Four of four published rows agree to every digit printed. The essay's numerics in this section are
sound; the only thing that was missing was the code.

Two independent invariants are asserted inside the harness at every $n$, so a wrong subgroup or a
wrong transform cannot slip through unnoticed:

* **Parseval**, $\sum_{b=0}^{p-1}|\eta_b|^2 = pn$;
* **the fourth-moment law**, $\sum_{b\neq0}|\eta_b|^4 = pE_2 - n^4$ with $E_2 = 3n^2-3n$.

Both hold at every $n$ in the table. The second is the essay's own §4.1 claim, so that computation
is re-checked here too, at $n = 128$ as well as below.

## 3. What the next rung does

§4.2 sets two readings of these numbers against each other.

The first comes from the moderate-tail temperature: $c(n)$ "does converge geometrically to
$c_\infty \approx 1.635$, **suggesting $C_\infty \approx 1.28$**, matching the constant the campaign
repeatedly observes saturating near $1.28$."

The second is the correction that overrides it:

> The load-bearing identity $C(n) = \sqrt{c(n)}$ is **false** […] I measure
> $C^2 = 1.14 \to 1.44 \to 1.59 \to 1.86$ at $n=8,16,32,64$ — **monotonically rising, not
> saturating** […] the rising $C^2$ is a caution against premature confidence in either direction.

Note what the correction turns on. It is not an argument that $c(n)$ and $C$ must differ; it is the
observation that the four measured $C^2$ were still climbing, so a saturation prediction had nothing
to sit on. The next rung under the table's own rule:

$$
C^2:\quad 1.1432 \to 1.4388 \to 1.5877 \to 1.8590 \to \mathbf{1.6274},
\qquad
C:\quad 1.0692 \to 1.1995 \to 1.2600 \to 1.3635 \to \mathbf{1.2757}
$$

Two things happen at once. The rise is **not** monotone — $n=64$ is a local excursion and $C^2$ at
$n=128$ falls back between the $n=32$ and $n=64$ values. And $C$ lands at $1.2757$, which is the
$\approx 1.28$ the first reading predicted, to within $0.2\%$.

That is one point, and one point is not a saturation. But it is the specific point the correction
was missing, and it moves in the direction the correction ruled out.

The essay is not unaware of this regime: it reports a wider campaign over 40-prime windows out to
$n = 256$, finding $C$ bounded below $\sqrt2$ there. What was absent was this sequence — the
least-prime-$\ge n^4$ trace, which is the exact sequence the monotonicity caution is stated
about — carried past $n=64$.

## 4. What this does and does not settle

**It does not settle anything about the conjecture.** `PALEY_SETTLED=false` is unchanged. Four
limits are worth stating plainly, because the temptation to over-read a single new point is exactly
the failure mode the essay was guarding against.

1. **One prime per $n$ is not $M(n)$.** The quantity in the conjecture, as §1.1 of the essay
   defines it, is a maximum over admissible primes $p \approx n^4$. This table samples the *least*
   such prime at each $n$. Neither the rise through $n=64$ nor the fall at $n=128$ is directly a
   statement about $M(n)$; both are single-sample traces. A non-monotone sample is fully consistent
   with a monotone envelope.
2. **Five points do not exhibit saturation.** Removing a claimed monotone rise is not the same as
   demonstrating a bound. $C \in [1.07, 1.36]$ across $n = 8..128$, still under $\sqrt2 \approx
   1.4142$, with no observed divergence — which is what the essay already said the wider evidence
   showed. This note makes that reading *less* qualified, not confirmed. And the criticism cuts
   both ways: a table that stops at $n=128$ is exposed to exactly the objection raised here against
   one that stopped at $n=64$. If $C^2$ at $n=256$ comes back above $1.86$, the honest reading of
   $n=128$ becomes "one dip", not "the rise is not real". The claim defended here is only the
   narrow one — *monotone through $n=128$* is false — and that much no later row can undo.
3. **Hitting $1.28$ is weak evidence, and weak for a stateable reason.** $1.28$ is not an
   out-of-the-way target. The essay picked it because the campaign already saw $C$ hovering there,
   so it sits near the middle of the observed range $[1.07, 1.41]$ — a value a new sample has a
   fair chance of landing near for no reason at all. What makes the hit worth recording is not its
   precision but its *timing*: it is the first rung after the ones the correction was computed
   from, and it is the rung the correction predicted would keep climbing.
4. **The asymptotic is untouched.** The prize scale is $n \approx 2^{30}$. Nothing computable at
   $n \le 2^8$ reaches it.

What it does deliver is three things. The §4.2 numbers are confirmed reproducible under an
explicitly stated rule. The generating computation now exists in the tree instead of only in prose,
with two invariants asserted on every run. And the caveat the essay attached to its own conclusion
turns out to rest on where the table stopped: extended by one rung it is false, and the value it
was raised against is the one the next rung reports.

## 5. Reproducing

```
python3 scripts/probes/probe_paley_C_table.py            # n = 8..128
python3 scripts/probes/probe_paley_C_table.py 256        # a single n
```

A captured run is checked in at `scripts/probes/_out_paley_C_table.txt`.

Runtime is dominated by the scan over $b$: seconds through $n=32$, ~7 s at $n=64$, ~3.5 min at
$n=128$ on one core. The $b$-scan uses $|\eta_b| = |\eta_{p-b}|$ to halve the range, and reduces
$bh \bmod p$ through a 16-bit split of $h$ so that nothing overflows `int64` once $p$ approaches
$2^{32}$.

Cost is $\Theta(pn) = \Theta(n^5)$, so each rung is $32\times$ the last: $n=256$ is roughly two
hours single-core, $n=512$ roughly three days. That is why the table stops where it does, and it is
also why extending it is not the way to learn anything about $n \approx 2^{30}$.
