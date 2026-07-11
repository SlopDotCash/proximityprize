# #505 PPC10 — proof-producing computation: exact matched-regime disjoint-census onset

Date: 2026-07-10.  Lane 10 of the 10×10 assault.  Status: deterministic exact probe, golden output,
and axiom-audited Lean certificate interface; **no production Paley bound and no proximity-gap
closure**.

## Target and result

The live #505 direction after the matching-moment census is the fully-disjoint equal-sum sector.
The falsify-first question for computational anchors was whether the characteristic-zero formulas
continue to hold at primes in the matched regime `p ≍ n^4`, making the first disjoint sector vanish.

`scripts/probes/probe_ppc10_orbit_census.py` enumerates nondecreasing subgroup words with exact
permutation-orbit weights.  It uses only integer field arithmetic and sorting.  The default run is
reproduced exactly by:

```bash
diff -u scripts/probes/_out_ppc10_orbit_census.txt \
  <(python3 scripts/probes/probe_ppc10_orbit_census.py)
```

The result is a clean onset, not persistence:

| `n` | `r` | matched prime `p` | exact energy `E_r` | char-zero excess | disjoint census `D_r` | Wick slack |
|---:|---:|---:|---:|---:|---:|---:|
| 128 | 3 | 268440577 | 30725120 | 0 | 0 | 732160 |
| 256 | 3 | 4294968833 | 248903680 | 184320 | 184320 | 2754560 |
| 512 | 3 | 68719484929 | 2001858560 | 368640 | 368640 | 11407360 |
| 128 | 4 | 268440577 | 27110661760 | 222781440 | 2454783744 | 1075061120 |

At depth three the last two cells satisfy `excess = D`, and the values are `720n` for both
`n=256,512`.  This is a useful structural conjecture seed, but two primes are not a theorem and the
`n=128` zero cell shows that any recurrence must include arithmetic onset data.  The robust verdict
is:

> The finite-anchor shortcut “matched-regime depth three remains characteristic zero” is false
> already at `n=256`.  Fully-disjoint accidents are not merely a deep-moment artifact.

All four energies nevertheless remain strictly below their Wick ceilings.  Exact computation finds
the wall; it does not break it.

## Exact checker design

For each nondecreasing word `a`, store its sum bucket, support, and permutation-orbit weight `w(a)`.
For one bucket, let `M` be its total ordered mass.  Then

```text
E = Σ_a w(a) M(sum(a)),
D = Σ_a w(a) Σ_{b in same bucket, supp(a)∩supp(b)=∅} w(b).
```

The probe verifies support-resolved versions before emitting centered terms

```text
B_s = p E_s - A_s n^r,
T_s = p D_s - A_s (n-s)^r,
C_s = T_s - B_s.
```

Every output cell includes a SHA-256 digest of the canonical sorted representative records.  The
digest is a reproducibility guard, not a mathematical proof by itself.

`Frontier/_PPC10OrbitCensusCertificate.lean` proves:

* weighted equal-bucket census equals the row/bucket-mass computation;
* weighted fully-disjoint census equals its row/disjoint-mass computation;
* replacing a representative by `w(a)` labeled copies gives exactly those weighted censuses;
* the centered support identity `T_s = B_s + C_s`;
* the concrete onset, non-persistence, and Wick arithmetic summaries.

The raw 11.7-million-record sort is intentionally not replayed inside the Lean kernel.  The formal
file proves the reusable checker mathematics and labels the large values as externally emitted exact
summaries.

## Ten proof-producing subangles, with kill criteria

1. **Exact finite-field census — SURVIVES AS AN ANCHOR TOOL.** Orbit compression reduces ordered
   enumeration to `binomial(n+r-1,r)` exact records and directly sees the #505 disjoint sector.  It
   refutes characteristic-zero persistence at `n=256`.

2. **Modular/resultant certificates — EXISTENCE, NOT MASS.** A sparse resultant can certify that one
   collision is realizable modulo `p`, but it does not count its orbit multiplicity or bound the sum
   of all accidents.  Use it to explain the `184320` family, not as a replacement for the census.

3. **Interval arithmetic — NO LEVER ON THIS CELL.** Every quantity here is an exact integer; interval
   enclosures only weaken the result.  Intervals remain appropriate for analytic spectral bounds,
   but cannot reveal cancellation lost before the exact `D_s` decomposition.

4. **SAT/SMT/CP-SAT certificates — REALIZABILITY GAP.** Abstract collision patterns can falsify
   combinatorial inequalities, but SAT satisfaction does not prove that a pattern comes from powers
   of one finite-field element.  A useful certificate must include field equations or an explicit
   embedding; otherwise it recreates the known pattern-vs-arithmetic gap.

5. **Gröbner/F4 traces — LOCAL SURVIVOR, GLOBAL EXPLOSION.** For a fixed support pattern, a checked
   Gröbner trace can classify a collision component.  The number of patterns and variables grows
   exponentially with depth, so the production use must first prove a bounded component taxonomy.

6. **Determinant/minor certificates — RANK ONLY.** Nonzero minors efficiently certify independence of
   a proposed constraint family.  They cannot upper-bound the remaining fully-disjoint fiber when
   that fiber is precisely the null direction.  Apply them after an arithmetic row nonzero on the
   disjoint sector has been found.

7. **Recurrence verification — CONJECTURE SEED, NOT YET A LAW.** The two nonzero depth-three cells
   give `D=excess=720n`; the previous cell gives zero.  The next test should classify the responsible
   orbit and prove an onset-conditioned recurrence.  Blind extrapolation from two values is retired.

8. **Primality/order witnesses — CHEAP AND NECESSARY.** The probe uses deterministic 64-bit
   Miller--Rabin bases and verifies `zeta^n=1`, `zeta^(n/2)≠1`.  Production certificates should use a
   kernel-checked Pocklington/order witness; this authenticates the field but supplies no discrepancy
   estimate.

9. **Exhaustive orbit reduction — CURRENT STRONGEST METHOD.** Nondecreasing words plus exact
   multinomial weights cut the `n=128,r=4` cell from `128^4` ordered words to 11,716,640 records.
   Support-aware bucket comparison then computes `D_s` without enumerating all ordered pairs.

10. **Certificate compression — FORMAL INTERFACE LANDED, PRODUCTION NO-GO.** The Lean orbit-expansion
    lemmas are the small trusted mathematical kernel, and SHA digests make traces reproducible.  But
    at `(n,r)=(2^30,110)` the representative count is about `2^2708 ≈ 10^815`; compression by
    permutation symmetry alone is decisively non-scalable.  A production certificate needs a new
    algebraic recurrence, component classification, or phase-sensitive estimate.

## Honest endpoint

The exact scan changes the priority map: the fully-disjoint sector appears already at depth three in
proper matched cells, so computations that assume a long characteristic-zero prefix should be
retired.  The `720n` onset family is the concrete next classification target.  Its classification
would explain these anchors, but a bound uniform through depth `r≈110` is still the Paley/BGK wall.

No prize gate is discharged here.
