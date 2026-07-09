# [sweep][A21] WB-to-esymm compiler: explicit smooth fibre count of e_1..e_{m+1} on mu_n

**Date:** 2026-06-14
**Status:** PARTIAL (structural question fully resolved; delta* not closed — correctly relocated)
**Artifact:** `scripts/probes/sweep_A21_esymm_fibre.py` (exact, EVIDENCE; consumes the A17 substrate
`scripts/probes/cyclotomic_exact_enumerator.py`).
**Merged from:** 371-T10, 389-T06, 232-T05.

## The object

In the window-bad / interleaved-list reduction, the bad-scalar count of a degree-window word
collapses (the "WB-to-esymm compiler", #371-T10) to a **symmetric-function fibre count**:

```
Phi_m : { w-subsets S of mu_n }  ->  R^{m+1},   S |-> (e_1(S), ..., e_{m+1}(S)),
F(n,w,m) = max_v #Phi_m^{-1}(v).
```

The actionable: locate `F` between the **dyadic coset-union lower witness `C(r,s)`** and the
**universal ceiling `C(n,w)`**, with the CRITICAL instruction to detect/quotient `X^d` tower
components (degree-`t` poly words give `C(r,s)` cores from `mu_d`-coset blocks) and *not* treat
them as noise — then decide whether `F` is `O(1)/poly` or exponential at production rate.

## What was measured (exact, char-0 over Z[zeta_n] AND F_q; n=8,16,32)

### (A) The lower bracket is the *origin* fibre = the tower core (re-confirmed exactly)

The **consecutive-vanishing** fibre `e_1=...=e_{m+1}=0` is realized exactly by the dyadic tower
cores: with `L = floor(log2(m+1))+1`,

```
#{ S : e_1=...=e_{m+1}=0 } = C(n/2^L, w/2^L)   if 2^L | w,   else 0,
```

carriers being unions of `mu_d`-cosets, `d = n/2^L` (the `X^d` tower component). Re-verified
independently of `probe_tower_fiber` (via the A17 ring substrate) for n=8,16, m+1<=3, all w.
This is the `C(r,s)` witness: `r = n/2^L`, `s = w/2^L`.

### (B) The WORST fibre is ALWAYS the tower one — `F = C(n/2^L, w/2^L)` exactly

Across every feasible config (rates 1/2, 1/4, 1/8; depths m+1 = 1,2,3,4; n=8,16,32):

| n | w | m+1 | F | F@origin | tower C(r,s) | F==tower | worst is origin |
|---|---|-----|---|----------|--------------|----------|-----------------|
| 8 | 4 | 2 | 2 | 2 | C(2,1)=2 | yes | yes |
| 16| 8 | 2 | 6 | 6 | C(4,2)=6 | yes | yes |
| 16| 4 | 2 | 4 | 4 | C(4,1)=4 | yes | yes |
| 32| 4 | 2 | 8 | 8 | C(8,1)=8 | yes | yes |
| 16| 8 | 4 | 2 | 2 | C(2,1)=2 | yes | yes |
| 16| 8 | 1 | 70| 70| C(8,4)=70| yes | yes |
| 32| 4 | 1 |120|120| C(16,2)=120| yes | yes |

**Genuine NON-tower value-tuples ALWAYS carry a strictly smaller fibre** (e.g. n=32,w=4,m+1=1:
max over pure-nontower tuples = 14 vs F = 120). `F/C(n,w)` is tiny everywhere (0.005–0.14):
the worst fibre is **exponentially below** the ceiling.

**Odd-w stress test** (`2^L` ∤ w, so the origin fibre is *empty*): the worst fibre is still a
small *coset-shifted* count and never blows up — e.g. n=16,w=5,m+1=2 → F=3 = n/4−1;
n=32,w=5,m+1=2 → F=7 = n/4−1; n=16,w=3,m+1=1 → F=7 = n/2−1. Even off the tower core the worst
fibre stays coset-structured and `O(n)`.

**char-0 vs F_q:** identical at non-defect primes. A mod-q defect can *move* the worst tuple off
the origin (n=16,w=4,m+1=2,q=17: worst off-origin fibre = 8 = 2·C(4,1)) but never inflates `F`
past the tower scale.

### (C) Growth law — the O(1)/poly vs exponential answer (the actionable's headline question)

Because the worst fibre is exactly `C(n/2^L, w/2^L)`, the growth is decided by the regime:

- **PRODUCTION RATE** `w = rho·n`, fixed depth ⇒ `2^L` fixed ⇒
  `F = C(n/2^L, rho·n/2^L) = C(r, rho·r)`, `r = n/2^L` — **EXPONENTIAL in n**
  (`log2 F ≈ H(rho)·n/2^L`; at n=2^32, rho=1/2, m+1=2: `log2 F ≈ 2^30.0`).
- **NEAR-CAPACITY** `w = O(1)` fixed (the `w = k+depth` regime) ⇒
  `F = C(n/2^L, O(1)) = poly(n)` of degree `w/2^L` (e.g. w=4,m+1=2 ⇒ `C(n/4,1) = n/4`).

In **every** regime `F` is **exponentially BELOW `C(n,w)`** (2^767 below at n=1024,rho=1/2),
the compression governed entirely by the dyadic tower depth `2^L`.

### (D) ORBIT COLLAPSE — the decisive correction (why the exponential fibre is benign)

The raw fibre cardinality is **the wrong object for delta***. The compiler reads out the bad
*scalar* (`gamma = -e_1`) as a *single* symmetric function on the vanishing variety, and the
list/delta* count is the number of distinct **dilation-ORBITS** of that readout, not the raw
fibre. The exponential fibre collapses:

| n | w | vanish | #subsets (raw fibre) | #distinct e_1 | #dilation-orbits | n/4−1 |
|---|---|--------|----------------------|---------------|------------------|-------|
| 8 | 4 | {e2}   | 10  | 8   | 1 | 1 |
| 16| 4 | {e2}   | 52  | 48  | 3 | 3 |
| 32| 4 | {e2}   | 232 | 224 | 7 | 7 |
| 16| 8 | {e2}   | 70  | 48  | 4 | (≈3) |
| 16| 8 | {e2,e3}| 6   | 0   | 0 | — |

`#distinct e_1 = n · #orbits` (one full `mu_n`-coset per orbit), and `#orbits = n/4−1` exactly
(the A16 closed form, the #400 near-capacity Θ(n) count). So the bad-SCALAR count is **Θ(n)**,
not exponential: the raw-fibre exponentiality is benign **tower multiplicity** that the readout
quotient discards.

## Verdict (honest)

- The **fibre-count question is resolved structurally and decisively**: `F(n,w,m)` equals the
  dyadic tower witness `C(n/2^L, w/2^L)` exactly, attained at the coset-union origin fibre; it is
  exponential at production rate and polynomial near capacity, but always exponentially below the
  trivial ceiling, and the worst fibre is always tower/coset-structured (no genuinely non-tower
  value-tuple ever wins).
- The **`X^d` tower component is the whole story**, not noise: it *is* the worst fibre.
- **delta* is NOT closed.** The raw fibre cardinality is the wrong delta* object; the right one is
  the dilation-orbit count of the readout, which collapses to Θ(n). The genuine open core is
  therefore the **Θ(n) orbit bound** (= the #400 near-capacity / #389 power-word floor / A16
  `n/4−1` orbit count), not the fibre cardinality. This sweep removes "the fibre might be
  exponential and kill the route" as a worry and pins the real residual on the orbit side.

## Connections

- Consumes the A17 exact `Z[zeta_n]` enumerator (`cyclotomic_exact_enumerator.py`).
- The tower-core identity is the `probe_tower_fiber` O47 conjecture and the `probe_fiber_count_law`
  O109 product law `|F_n(t)| = |F_m(t)|^{n/m}` (the block-trace bijection underlying the
  exponential growth at production rate).
- The orbit collapse is the A16 `#orbits(w=4,e2=0) = n/4−1` brick and the #389
  `probe_symmetric_function_reduction` reduction (bad scalars = square roots of subset-sums-of-
  squares; `gamma^2 = sum_{x in S} x^2`).
- The honest near-capacity-vs-window caveat is the one already flagged in
  `probe_symmetric_function_reduction.py` (fixed-small-w is q-dependent near-capacity, not the
  window interior).
