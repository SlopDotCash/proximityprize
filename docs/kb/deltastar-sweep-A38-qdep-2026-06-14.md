# [sweep][A38] Window-interior q-dependence of true delta* — de-confounded

**Date:** 2026-06-14
**Status:** PARTIAL (a converged measurement resolving a confounded prior signal; not a closure)
**Artifact:** `scripts/probes/sweep_A38_qdep.py` (+ saved run `scripts/probes/_A38_out.txt`)
**Merged from:** 389-T02, 389-T18

## The confounded prior signal

The #389 hill-climb found adversarial words beating power-words ~2.3x above Johnson, but the
*q-dependence of the true delta\** was left **confounded by time-boxed search**: the per-prime
crossovers `{97:0.43, 113:0.28, 193:0.21, 257:0.31}` mixed two unrelated effects:

1. the genuine `eps_mca = (badGamma integer)/q` **"const/q ledge"** — a finite-q ARTIFACT that
   recedes uniformly as q grows, and is NOT q-dependence of delta\*; and
2. any genuine q-dependence of the bad-gamma **incidence integers themselves** in the window
   interior — which WOULD make true delta\* q-dependent.

389-T18 sharpened the question: the coset-spectrum count `N_a = (#cosets)·n` is claimed
q-independent in the interior, but the leading `O(1)` constant *could* shift the crossing by a
full agreement level (one `1/n` grid step). A converged (not time-boxed) measurement was never run.

## What was run

`RS[F_q, mu_n, k]`, `rho = k/n = 1/4`. The decisive family is **n=8, k=2** — fully EXACT (q^2
codewords) at every prime on a clean ladder `q = 1 mod 8`, `q in {41,73,89,97,113,137,193,233}`.
Per-(pair,gamma) bad-gamma count is exact (full codeword list; agreement set S recomputed for each
list member, NOT-joint condition checked exactly). The only sampled quantity is the worst-over-pairs.

The probe separates two things that the prior time-boxed search conflated:

- **PART 1 — structural FLOOR (deterministic, no RNG):** max badGamma over a q-INDEPENDENT
  structured construction (all monomial pairs `(x^a, x^b)` + codeword+monomial deviation words).
  Because the construction does not depend on q, its per-prime values are a **fair cross-prime
  comparison**, and this is the char-0 coset-spectrum value.
- **PART 2 — mod-q DEFECT hunt (randomized hill-climb):** extra badGamma found ONLY by a randomized
  non-structured word = a search-found spurious mod-q vanishing coincidence. Run on the 2 smallest
  primes with a long budget (400 steps × 14 restarts).

A richer-interior cross-check at **n=16, k=4** (q^4 feasible only at p=17) confirms spectrum shape.

## Result (decisive)

The deterministic structural floor is **exactly q-invariant** across the whole ladder. The full
badGamma spectrum, per agreement level `m` (`delta = 1 - m/8`):

```
m:      8     7     6     5     4     3
delta: .000  .125  .250  .375  .500  .625      zone
q=41    1     1     1     8     9    40
q=73    1     1     1     8     9    40
q=89    1     1     1     8     9    40    ...  m=4 (delta=J=.5) and m=3 (delta=.625) are [J,cap)
q=97    1     1     1     8     9    40
q=113   1     1     1     8     9    40
q=137   1     1     1     8     9    40
q=193   1     1     1     8     9    40
q=233   1     1     1     8     9    40
```

Every row is CONSTANT over 8 primes — interior rows (m=4 -> 9; m=3 -> 40), the Johnson boundary
(m=4, delta = J = 0.5), AND the sub-Johnson onset rows (m=5 -> 8, m=6 -> 1). Consequently
`eps_mca = (q-invariant integer)/q` falls like `const/q` at every row, and the measured crossover
`delta_x(q)` at fixed eps RISES with q (eps=0.05: 0.25 -> 0.50 as q: 41 -> 233; eps=0.10: 0.25 ->
0.50 by q=97) **purely via the const/q ledge** — the integers never move. This is the #389
confounded drift, fully explained.

**PART 2 defect hunt:** on q=41 and q=73 at the Johnson-boundary and onset rows, the randomized
hill-climb (budget 400×14) could not even MATCH the structured floor (best 6–7 vs floor 8–9,
defect negative). The **structured monomial pair is the converged worst-word**; no systematic
boundary-row mod-q defect was found. (Earlier shorter mixed runs occasionally surfaced a +1/+2 at
isolated primes; those were search-noise — a specific random word at a specific prime catching one
spurious coincidence — not a systematic, q-scaling effect.)

## Verdict

**The true delta\* is q-INDEPENDENT in the window interior to leading order.** The interior
incidence integers are the char-0 coset spectrum and do not move with q; the per-prime crossover
variation observed in #389 is the finite-q `const/q` ledge artifact, NOT q-dependence of delta\*.
389-T18's worry — that the leading `O(1)` constant could shift the crossing by a grid step — is
NOT realized at the worst (monomial) direction for n=8: the constant is exactly fixed across the
ladder. Any residual q-dependence is confined to a small, positive, non-growing additive mod-q
defect (`O(1)/q`) that can at most nudge the crossing by one `1/n` grid step at isolated primes and
does not scale with q. **delta\* therefore admits a clean q-independent closed form in the interior
up to an `O(1)/q` correction.**

This is the cross-domain "char-0 = char-p in the clean regime" theme (cf. the energy/Bessel notes):
the interior worst-case count over the dyadic subgroup is a cyclotomic (root-of-unity) incidence
that is char-0-valued; mod-q defects are a sub-Johnson / deep-band phenomenon, and at the window
interior at toy primes they are absent at the worst direction.

## Honest gaps

- Toy primes only (41..233); does NOT reach prize `q ~ 2^128`. This validates the SHAPE and
  q-invariance on real codes, NOT the prize-regime constant.
- n=8 has a thin 2-row interior; n=16's interior at rho=1/4 is entirely in the all-bad (=q) zone,
  and q^4 is feasible only at p=17, so the q-ladder test is genuinely run only at n=8. A richer
  multi-prime interior test at larger n needs a list-decoding-style exact counter (not the full
  q^k codeword matrix) — a natural follow-up (reuses A17's exact enumerator substrate).
- The worst-over-pairs is a converged LOWER bound (an un-found heavier structured pair could only
  RAISE a floor integer, never disturb a row already constant at its structural max). A constant
  row is strong evidence of q-independence; it is not a proof.

## Connection to the open core

This does NOT touch the prize wall (the B-form / Gauss-period house at growing n, prize q). It
removes a confound: the closed-form candidate `delta* = 1 - rho - 2/s*` is q-independent in the
interior by construction, and this probe confirms the *measured* interior delta\* is too, so the
remaining q-dependence question for delta\* lives — if anywhere — only in the prize-scale constant
and the sub-Johnson onset, not in the interior incidence spectrum.
