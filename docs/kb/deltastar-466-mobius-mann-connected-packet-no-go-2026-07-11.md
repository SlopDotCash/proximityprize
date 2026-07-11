# δ* #466: uncentered Möbius-Mann connected packets amplify the DC bulk

Date: 2026-07-11 UTC. Status: exact reproducible no-go, CORE open.

## Question

The 10x10 synthesis proposed a Möbius-Mann full-depth calculus: lift an equal-sum pair to a signed zero-sum word, regard opposite pairs as the Wick packets, and use Möbius inversion over position partitions to isolate primitive non-pair packets. This is the most direct surviving characteristic-`p` wraparound target after the generic moment, primitive-weighting, orbit-only, and long Mann-exclusion routes were closed.

The exact question is whether ordinary partition-lattice Möbius inversion produces a positive primitive-packet census that can be bounded by the short-packet inputs from G136/ANT46/HBK and then fed to G133.

## Exact setup

For a multiplicative subgroup `H ⊆ F_p`, let

```text
M_m = #{(x_1,...,x_m) ∈ H^m : x_1+...+x_m = 0}.
```

Define connected coefficients `K_m` by the classical moment-cumulant law

```text
M_m = Σ_{π ∈ Part([m])} ∏_{B∈π} K_|B|.
```

Equivalently, distinguishing the block containing position one gives the exact recurrence

```text
K_m = M_m - Σ_{1≤k<m} choose(m-1,k-1) K_k M_(m-k).
```

This is the standard Möbius inversion on the partition lattice, or the ordinary connected/Ursell expansion. The executable probe computes both sides with exact integer arithmetic and asserts reconstruction at every depth.

Artifact:

```text
scripts/probes/probe_466_mobius_mann_connected_packet.py
```

## Obstruction 1: the Möbius coefficient is not a primitive-packet count

At length four, the negation-closed lawful zero-sum population is exactly

```text
lawful4 = 3n^2 - 3n.
```

Thus the literal number of primitive non-pair four-packets is

```text
primitive4 = M_4 - (3n^2 - 3n).
```

But partition Möbius inversion gives

```text
K_4 = M_4 - 3M_2^2 = M_4 - 3n^2 = primitive4 - 3n.
```

The discrepancy is not cosmetic. In the exact cell `H=μ_8 ⊆ F_257`, `M_4=168=3·8^2-3·8`, so there are **zero** primitive four-packets, while

```text
K_4 = -24.
```

Therefore `K_m` is a signed inclusion-exclusion weight, not a cardinality and not the supply counted by ANT46's projective packet orbits. A theorem of the form “Möbius inversion isolates the primitive packet Finset” is false already at length four.

The finite sweep makes the sign problem structural, not exceptional. Exact connected coefficients oscillate and rapidly exceed Wick in magnitude:

```text
n=32, p=193: K_6=3,085,760; K_10=-4,809,006,902,848;
              K_14=16,426,218,577,813,826,912.
n=32, p=257: K_6=1,415,840; K_10=-2,662,393,788,768;
              K_14=13,054,139,504,185,625,248.
```

Short packet classification remains useful, but it cannot be inserted as a nonnegative bound on the ordinary cumulants.

## Obstruction 2: the random characteristic-p main term becomes a huge Bernoulli cumulant

Replace every positive-length moment by the uniform finite-field main term

```text
M_m^DC = n^m/q.
```

After dividing out `n^m`, the connected generating function is exactly

```text
log(1 + (exp(z)-1)/q),
```

so `K_m^DC/n^m` is the `m`-th cumulant of a Bernoulli random variable of parameter `1/q`:

```text
K_m^DC / n^m
  = Σ_{j=1}^m (-1)^(j-1) (j-1)! S(m,j) q^(-j).
```

At production signed length `m=220`, `n=2^30`, and the conservative field cap `q=2^160`, exact rational arithmetic gives

```text
sign(K_220^DC) = negative,
log2(|K_220^DC| / (n^220/q)) = 59.000000,
log2((n^220/q) / (219!! n^110)) = 2442.247432,
log2(|K_220^DC| / (219!! n^110)) = 2501.247432.
```

The reason is visible in the first two Stirling terms:

```text
q^-1 - (2^219-1)q^-2 + ...;
```

at `q=2^160`, the two-block term is about `2^59` times the one-block DC term and has the opposite sign. Uncentered connected inversion therefore **amplifies** the DC bulk by 59 bits at the prize depth. It does not remove it.

Any proof forcing the arithmetic correction to cancel this signed Bernoulli cumulant down to Wick scale would require about 2501 bits of relative precision. That is stronger than the existing G133/G135 deep-census budget and is another form of the Paley/BGK wall, not a weaker sufficient condition.

## Integration with current frontier

- **G133 Fourier normal form:** the full-depth anomaly is already DC-centered. Applying ordinary connected inversion before this centering reintroduces the principal-character bulk in Bernoulli-cumulant form. Applying it after exact DC subtraction makes the connected tail a signed transform of the nonprincipal moment, so controlling it is again the open G133 anomaly.
- **G142-G145:** cancellation cores and intersection multiplicities are positive, lossless combinatorics. They remain valid. This no-go only blocks replacing their positive strata by ordinary signed cumulants.
- **G136 / ANT46:** size-four projective packets and their order/orbit divisibility remain real low-rung arithmetic. Their counts are not `K_4`; the exact offset `K_4=primitive4-3n` must be respected.
- **HBK:** the newly assembled depth-four additive-energy estimate controls a fixed low moment. It does not control the connected tail through length 220.
- **FS15-FS18:** those files correctly show fixed-depth resultant/Wick ladders are useful only at almost-all good primes and become regime-disjoint at prize depth. The Bernoulli-cumulant calculation is the connected-expansion version of the same reversal: at `m≈log q`, partition multiplicities overwhelm the fixed-depth norm advantage.

## Literature placement

The moment-cumulant formula is the classical Möbius inversion on the lattice of set partitions; in statistical mechanics the same signed objects are connected or Ursell functions. The generating-function identity `K(z)=log M(z)` explains both the signs and the Stirling coefficients. Lam-Leung/Mann theory is different: it classifies actual vanishing root-of-unity multisets and hence supplies positive packet structure in characteristic zero. Conflating these two notions of “connected” is the failed step.

Useful references:

- Gian-Carlo Rota, *On the Foundations of Combinatorial Theory I. Theory of Möbius Functions* (1964).
- Peter McCullagh, *Tensor Methods in Statistics*, chapters on cumulants and partition lattices.
- T. Y. Lam and K. H. Leung, *On vanishing sums of roots of unity* (J. Algebra, 2000).

## Corrected target

Do not formalize an uncentered moment-cumulant wrapper for G133. The exact surviving object must be **positive and canonical**:

1. define literal minimal zero-sum packet occurrences in a signed full-depth word;
2. choose or prove a canonical decomposition despite overlapping packet partitions;
3. bound decomposition multiplicity;
4. subtract the principal/DC population before any signed transform;
5. then use ANT46/HBK only on the actual positive packet census.

The binding implication remains a bound on packets through signed length 220. This is still the Paley/proximity wall. The present result is a reproducible method-class fence: ordinary partition Möbius inversion does not supply the hoped-for positive packet calculus.
