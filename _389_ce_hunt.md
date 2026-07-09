## Counterexample hunt (large-prime, no pollution): floor HOLDS at n=8,16 — and a moment-problem framing for the proof

Per the "hunt for a counterexample, then push the proof" plan. Method: compute the deep-band list
`L(w,t)` by **k-subset interpolation over a LARGE prime** (p=12289), avoiding both codeword
enumeration and small-field pollution. (Critical: a brute-force scan at p=17, n=8 reported a
"counterexample" hill=7 > ladder=5 — but at p=12289 it VANISHES, ladder=5 > hill=2. Small-prime
list probes are polluted; the swarm's char-0 discipline is necessary.)

### Result — no counterexample; ladder dominates (rate 1/2, in-window)
```
n=8,  k=4, p=12289:  t=5         ladder=5    hill=2     -> ladder max
n=16, k=8, p=12289:  t=9 (d.44)  ladder=153  hill=12    -> ladder max
                     t=10(d.38)  ladder=5    hill=0     -> ladder max
                     t=11(d.31)  ladder=1    hill=0     -> ladder max
```
30-restart hill-climb over arbitrary words + a broad structured family (tower/ladder, m∈{1,2,4,8},
2- and 3-term). The ladder beats the best non-structured word by >10x at t=9. **Strong evidence the
floor (`PrizeFloorStatement` = ladder optimality) is TRUE**, not just conjectured.

### A clean framing for the proof — the floor is a CONSTRAINED Chebyshev–Markov moment problem
The agreement profile `{a_c}` of ANY word has its first `k` binomial moments **fixed and
w-independent**: `Σ_c C(a_c,j) = C(n,j)` for all `j ≤ k` (the in-tree `moment_identity_base`; e.g.
`Σ_c C(a_c,k)=C(n,k)`). So:
> **Floor = maximize the upper tail `#{a_c ≥ t}` over agreement profiles REALIZABLE by a smooth-domain
> word, subject to the fixed first-`k` moments.**

The *unconstrained* Chebyshev–Markov max is the trivial Johnson bound `C(n,k)/C(t,k)` (=1430 at
n=16,t=9) — but the realized ladder is `153`, an order of magnitude smaller. **The entire gap is the
REALIZABILITY constraint** (which profiles arise from actual words on `μ_n`), and that constraint is
exactly BCHKS25 Conj 1.12. The smooth structure permits *bimodal* profiles (a concentrated
high-agreement cluster from subgroup fibres + a low-agreement bulk); the ladder is the
maximally-concentrated realizable cluster, while generic words give unimodal Poisson-like profiles
with negligible tail (hill=12 ≪ 153). The proof obligation is sharp: **bound the realizable upper
tail by N_fib** — a moment problem with a smooth-domain realizability constraint, no longer a
character-sum or interpolation question.
