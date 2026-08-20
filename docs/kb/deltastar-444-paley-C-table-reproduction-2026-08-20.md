<!-- #444 / Paley Graph Conjecture (BGK β=4). Authored 2026-08-20. Reproduction audit of the
section-4.2 constant table of deltastar-444-paley-phase-cancellation-essay-2026-06-21.md, whose
generating script is not in the tree. HONEST STATUS: PALEY_SETTLED=false — unchanged. The table
REPRODUCES EXACTLY (4/4 rows, every published digit). Extending it two rungs, to n=128
(p=268437889, C^2=1.6274) and n=256 (p=4294968833, C^2=1.7541), falsifies the "monotonically
rising" half of the caution the essay attaches to its own conclusion: both new rungs sit BELOW the
n=64 value 1.8590. It does NOT establish the other half — six points are not a saturation. The
n=128 rung also landed C on the ~1.28 the tail-temperature reading predicted, but n=256 moved to
1.3244, so that hit did NOT persist and is recorded here as coincidence-compatible.
No proof, no disproof; this narrows one stated caveat and adds a re-runnable harness. -->

# Reproducing the Paley constant table, and what happens past n = 64

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
| **256** | **4294968833** | **86.4298** | **1.3244** | **1.7541** | — | **new** |

Four of four published rows agree to every digit printed. The essay's numerics in this section are
sound; the only thing that was missing was the code.

Two independent invariants are asserted inside the harness at every $n$, so a wrong subgroup or a
wrong transform cannot slip through unnoticed:

* **Parseval**, $\sum_{b=0}^{p-1}|\eta_b|^2 = pn$;
* **the fourth-moment law**, $\sum_{b\neq0}|\eta_b|^4 = pE_2 - n^4$ with $E_2 = 3n^2-3n$.

Both hold at every $n$ in the table. The second is the essay's own §4.1 claim, so that computation
is re-checked here too, at $n = 128$ and $n = 256$ as well as below. They earn their keep at the
top rung in particular: at $n = 256$ the modulus $p = 4294968833$ exceeds $2^{32}$, and these two
assertions are what rule out a silent `int64` overflow in the reduction quietly producing a
plausible-looking wrong $M$.

## 3. What the next two rungs do

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
to sit on. The next two rungs under the table's own rule:

$$
C^2:\quad 1.1432 \to 1.4388 \to 1.5877 \to 1.8590 \to \mathbf{1.6274} \to \mathbf{1.7541},
\qquad
C:\quad 1.0692 \to 1.1995 \to 1.2600 \to 1.3635 \to \mathbf{1.2757} \to \mathbf{1.3244}
$$

The rise is **not** monotone. $C^2$ falls at $n=128$, recovers part of the fall at $n=256$, and
**neither new rung regains the $n=64$ value $1.8590$**: the step sequence is
$+0.296, +0.149, +0.271, -0.232, +0.127$. Whatever these six numbers are doing, "monotonically
rising" is not a description of it, and the largest value in the trace is now an interior one.

The second rung is also a correction to the first draft of this note. At $n=128$, $C = 1.2757$ sat
within $0.34\%$ of the $\approx 1.28$ the tail-temperature reading predicted, and that looked like
the more striking of the two observations. At $n=256$, $C = 1.3244$ — $3.5\%$ high, ten times the
$n=128$ miss, though still nearer $1.28$ than the $n=64$ rung's $6.5\%$. **The apparent prediction
hit did not reproduce.** That is not a refutation of $C_\infty \approx 1.28$ — two samples
straddling a value at $\mp0.3\%$ and $+3.5\%$ refute nothing — but it removes the reason to find
the $n=128$ agreement impressive. It is retained in the table as data and discounted as evidence;
§4.3 says why it was always the weaker of the two claims. What survives is the narrow, checkable
one: the monotonicity statement, which two rungs now contradict rather than one.

The essay is not unaware of this regime: it reports a wider campaign over 40-prime windows out to
$n = 256$, finding $C$ bounded below $\sqrt2$ there. The new rungs agree with that — the trace
maximum over $n = 8..256$ is $C = 1.3635$ at $n=64$, comfortably under $\sqrt2 \approx 1.4142$ —
which is worth noting precisely because it is the one place these two independent computations
overlap, and they do not disagree. What was absent was this sequence — the least-prime-$\ge n^4$
trace, which is the exact sequence the monotonicity caution is stated about — carried past $n=64$.

## 4. What this does and does not settle

**It does not settle anything about the conjecture.** `PALEY_SETTLED=false` is unchanged. Four
limits are worth stating plainly, because the temptation to over-read a couple of new points is
exactly the failure mode the essay was guarding against.

1. **One prime per $n$ is not $M(n)$.** The quantity in the conjecture, as §1.1 of the essay
   defines it, is a maximum over admissible primes $p \approx n^4$. This table samples the *least*
   such prime at each $n$. Neither the rise through $n=64$ nor the non-monotonicity at $n=128$ and
   $n=256$ is directly a statement about $M(n)$; all are single-sample traces. A non-monotone
   sample is fully consistent with a monotone envelope.
2. **Six points do not exhibit saturation.** Removing a claimed monotone rise is not the same as
   demonstrating a bound. $C \in [1.07, 1.37]$ across $n = 8..256$, still under $\sqrt2 \approx
   1.4142$, with no observed divergence — which is what the essay already said the wider evidence
   showed. This note makes that reading *less* qualified, not confirmed. The first draft of this
   note pre-registered the test: *if $C^2$ at $n=256$ comes back above $1.86$, the honest reading
   of $n=128$ becomes "one dip", not "the rise is not real".* It came back at $\mathbf{1.7541}$,
   below the $n=64$ value, so that reading is not forced — but note what did and did not happen.
   $C^2$ **rose** from $n=128$ to $n=256$, so "the dip was a fluctuation on a still-rising curve"
   remains available; what is excluded is only the monotone reading. And the criticism still cuts
   both ways: a table stopping at $n=256$ is exposed to exactly the objection raised here against
   one stopping at $n=64$. The claim defended here is only the narrow one — *monotone through
   $n=256$* is false — and that much no later row can undo. $n=512$ is ~2.5 days on one core
   (§5), so the next test is affordable to anyone who wants to run it.
3. **Hitting $1.28$ was weak evidence, and the next rung confirmed the weakness.** $1.28$ is not
   an out-of-the-way target. The essay picked it because the campaign already saw $C$ hovering
   there, so it sits near the middle of the observed range $[1.07, 1.41]$ — a value a new sample
   has a fair chance of landing near for no reason at all. That was written *before* $n=256$ was
   available; $n=256$ then returned $C = 1.3244$, missing $1.28$ by $3.5\%$ — ten times the
   $n=128$ miss, though still inside the same band. So the $n=128$ agreement is best read as the
   coincidence this limit anticipated, and no weight rests on it here. The observation keeps only
   its *timing* interest — it was the first rung after the ones the correction was computed
   from — and timing interest is not evidence for a limit value.
4. **The asymptotic is untouched.** The prize scale is $n \approx 2^{30}$. Nothing computable at
   $n \le 2^8$ reaches it.

What it does deliver is three things. The §4.2 numbers are confirmed reproducible under an
explicitly stated rule. The generating computation now exists in the tree instead of only in prose,
with two invariants asserted on every run. And the *monotonicity* half of the caveat the essay
attached to its own conclusion turns out to rest on where the table stopped: extended by two rungs
it is false, with both new rungs below the $n=64$ value. The *saturation* half stands untouched —
this note removes a stated reason for doubting saturation without supplying a reason to believe it.

## 5. Reproducing

```
python3 scripts/probes/probe_paley_C_table.py            # n = 8..128
python3 scripts/probes/probe_paley_C_table.py 256        # a single n
```

A captured run is checked in at `scripts/probes/_out_paley_C_table.txt`. The default invocation
stops at $n=128$ so that it stays a few minutes long; the $n=256$ row in that file comes from the
second command, and the file records that provenance.

Runtime is dominated by the scan over $b$: seconds through $n=32$, ~7 s at $n=64$, ~3.5 min at
$n=128$, and 1 h 51 m at $n=256$, on one core. The $b$-scan uses $|\eta_b| = |\eta_{p-b}|$ to halve
the range, and reduces $bh \bmod p$ through a 16-bit split of $h$ so that nothing overflows
`int64` — at $n=256$, where $p = 4294968833 > 2^{32}$, that split is doing real work rather than
guarding a margin.

Cost is $\Theta(pn) = \Theta(n^5)$, so each rung is $32\times$ the last. The measured $n=128 \to
256$ step is $6675/216 = 30.9\times$, which is the predicted $32\times$ within timing noise, so the
extrapolation below is anchored rather than assumed: $n=512$ is ~2.5 days single-core. That is why
the table stops where it does, and it is also why extending it is not the way to learn anything
about $n \approx 2^{30}$.
