# G307: the sponsor-two invariant conductor-15 span is non-separating

Date: 2026-07-14
Issue: #466
Branch: `research/proximity-prize` only

## Verdict

The first sponsor-specific complex traces at sponsor two do not merely fail one at a time. The
complete quotient-generator-invariant linear span of conductor dividing fifteen,

```text
(P, L3, L5, L15),
```

admits no fixed strict separator for the coefficient-two weighted-kernel CORE target on an exact
five-cell dyadic census. An exact positive Farkas circuit proves the no-go over `Q`; the Lean payload
is axiom-clean. This closes the first mixed-conductor repair after the order-three and order-five
basis traces. It does not close CORE and does not exclude non-invariant or full-family
Gross-Koblitz/Jacobi data.

## 1. Why conductor fifteen is the right next class

At the certified second sponsor the quotient order is

```text
m2 = 2^129 + 13
   = 3 * 5^2 * 7 * 71 * 202172094073993 * 90308905535905320959.
```

Thus `75 | m2`. Since `m2` is odd, there is no nonprincipal real `{+1,-1}` character. The first real
phase normal is the primitive order-three conjugate pair, and the next is the primitive order-five
Galois trace. For a generator-invariant normal whose character conductor divides `15`, the primitive
Galois orbits give exactly four rational coordinates:

- `P`, the principal quotient coordinate;
- `L3`, with Ramanujan weight `c3(j)=2` if `3|j`, `-1` otherwise;
- `L5`, with weight `c5(j)=4` if `5|j`, `-1` otherwise;
- `L15`, with `c15(j)=c3(j)c5(j)` by multiplicativity of Ramanujan sums.

Consequently every fixed generator-invariant conductor-15 normal is
`alpha*P + beta*L3 + gamma*L5 + delta*L15`. Testing only `L3` or `L5` would leave a mixed-trace
loophole; G307 closes the whole four-dimensional span at once.

## 2. Exact weighted-kernel probe

Run:

```text
python3 scripts/probes/g307_sponsor_two_conductor15_span_nogo.py
```

For `H=mu_n <= F_p^*`, the script computes exact subset-sum histograms and

```text
W_a(t) = #{(y,z) in H^2 : a*y-z=t},
A_a(R) = p*sum_t W_a(t)R(t) - n^2*sum_t R(t).
```

For each cell it sums `A_{g^j}` against the four Ramanujan weights. All arithmetic is integer-only.
Every quotient-generator change by a unit is checked explicitly. The five target-oriented feature
vectors support the strictly positive relation:

```text
8238733293377050110946 * x(8,241,5)
+754877671516756422812 * x(8,601,5)
+3385823540912886383052 * x(8,601,6)
+1425371395806543001161 * x(16,241,5)
+299870825764606156 * x(16,2161,6)
= (0,0,0,0).
```

Here `x=sign(A2)*(P,L3,L5,L15)`. All coefficients are positive. If a fixed vector
`a=(alpha,beta,gamma,delta)` strictly oriented every target, then `a dot x_i > 0` for every cell;
pairing with the positive relation gives `0>0`, impossible. The circuit uses both ranks five and
six and includes an adjacent-rank pair at the same `(n,p)=(8,601)`.

In particular, the order-five basis trace alone cannot orient all five circuit cells. G307 is
stronger because no mixture with `P`, `L3`, or `L15` repairs it.

## 3. Asymptotic meaning and FS15-FS18 integration

A primitive conductor-15 trace uses at most

```text
phi(1)+phi(3)+phi(5)+phi(15) = 1+2+4+8 = 15
```

quotient characters, while sponsor two has `m2 = 2^129+13` quotient positions. The retained fraction
is `< 15/2^129`. This by itself is not a no-go, because a sparse trace could in principle carry a
special sign. The exact circuit supplies the missing sign obstruction: even before taking the
production limit, the complete invariant sparse span is non-separating.

FS15-FS18 are fully consumed rather than bypassed:

- FS15 gives per-frequency moment bounds only away from a depth-dependent exceptional set and proves
  that a fixed-depth good-prime ladder cannot beat the trivial norm in the relevant regime.
- FS16 sharpens the resultant envelope to `(2r)^(n/2)`, but this is an Archimedean magnitude bound;
  it does not determine the sign of a row-labelled Ramanujan trace.
- FS17 unions the fixed-depth exceptional sets. Its budget remains dominated by the deepest rung and
  does not select the explicit sponsor at logarithmic depth.
- FS18 completes odd/even zero-sum taxonomy and permits min-over-depth optimization on a good prime,
  but explicitly preserves the same good-window/prize-regime disjointness.

At production `r*=89`, G64 already forces the sponsor into the exceptional side by depth six. Thus
none of FS15-FS18 transfers the sign of `(P,L3,L5,L15)` to `A2`, and none repairs the circuit.

## 4. Literature placement

The Ramanujan weights are the standard Galois traces of primitive cyclic characters. Their
integer formulas and multiplicativity explain why the generator-invariant conductor-15 space has
four rational coordinates.

Gross-Koblitz and Stickelberger describe p-adic Gauss-sum values and valuations. Those data do not,
without an additional Archimedean theorem, determine the real sign of the weighted sponsor
covariance. G307 shows that the first invariant low-conductor Archimedean traces cannot provide such
a theorem uniformly.

Lu-Zheng-Zheng, *On the distribution of Jacobi sums* (J. reine angew. Math. 741 (2018), arXiv
1305.3405), proves equidistribution when at least two character sets vary. The CORE target fixes a
sponsor and a row-labelled rank weight. Earlier G248-G253 work quantifies the fixed-row mismatch;
G307 gives a separate finite obstruction at the first mixed conductor.

## 5. Closed and surviving surfaces

Closed:

- the order-five trace as a uniform target-sign surrogate;
- every fixed generator-invariant conductor-15 linear combination;
- every strictly positive uniform margin on that four-coordinate span.

Still open:

- sponsor-two generator-invariant conductors `25`, `75`, and higher;
- non-generator-invariant predeclared weights;
- the full row-labelled Gross-Koblitz/Jacobi family at `r*=89`.

The next candidate must not be fitted after observing the row. A legitimate survivor must be fixed
arithmetically in advance and prove both `ell_89 >= eta > 0` and `|A_89-ell_89| < eta`. Any argument
using only valuations, unsigned norms, quotient averages, or the four conductor-15 coordinates is
now fenced. CORE remains open / on-BGK.

## Artifacts

- Lean: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_G307SponsorTwoConductorFifteenSpanNoGo.lean`
- Probe: `scripts/probes/g307_sponsor_two_conductor15_span_nogo.py`
- Ledger: `[466-G307-sponsor-two-conductor15-span-nogo]`
