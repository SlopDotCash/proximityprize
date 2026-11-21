# Three quintic fibers on the sixteenth roots of unity

For each field containing a primitive sixteenth root $\zeta$, consider three disjoint five-element subsets of $\mu_{16}$ that are fibers of one rational function of degree five. Multiplying all sites by the inverse of the unique omitted site normalizes that site to $1$. For a fixed $\zeta$, the exact numbers of unordered normalized partitions are:

| Characteristic | Partitions |
| --- | ---: |
| 3 | 2 |
| 17 | 1 |
| 31 | 1 |
| Zero and every other odd characteristic | 0 |

Characteristic two has no primitive sixteenth root. The count in each row applies over every field of that characteristic that contains $\zeta$.

The census enumerates all $\binom{15}{5}\binom{10}{5}/6=126126$ normalized partitions, grouped into 15981 orbits under odd powers of $\zeta$. For blocks $A,B,C$, let $P_A,P_B,P_C$ be their monic vanishers. They form three fibers exactly when $P_B-P_A$ and $P_C-P_A$ are proportional. The rational function $P_B/P_A$ recovers the fibers in this case since the three blocks are disjoint. The ten two-by-two coefficient minors test proportionality. Taking the greatest common divisor of the odd parts of their nonzero cyclotomic norms leaves candidate characteristics $3,7,17,31$. The polynomial gcd of all ten minors with $X^8+1$ in each candidate characteristic then counts primitive roots where the minors vanish simultaneously. Characteristic $7$ has no surviving partition.

## A smooth-domain MCA witness

Over $\mathbb F_{17}$ use the full nonzero domain, code dimension $8$ and error count $4$. Put $P(x)=11+5x+11x^2+14x^3+4x^4+x^5$ and $W(x)=15+10x+3x^2+12x^3+12x^4$. The received rows $xW(x)/P(x)$ and $-W(x)/P(x)$ have exactly $15$ bad scalars, the residues $2$ through $16$. For each of the $\binom{16}{12}$ supports, interpolation on eight sites determines both row polynomials. The remaining four sites impose the scalar constraints and detect whether the rows already have a joint explanation. This produces the full bad-scalar set for this pair.

The pair attains the general endpoint upper bound $5\lfloor17/5\rfloor=15$ on this particular subgroup. Attainment at the prize length $2^{30}$ on the designated subgroups remains open. [General endpoint theorem](../../../ArkLib/Research/ProximityGap/Frontier/ApolarEndpointExact.lean)

Run `python3 -B scripts/probes/probe_mu16_quintic_fibers.py` to reproduce both finite computations using the Python standard library. The output includes exponent blocks and their common-root polynomial for each surviving characteristic. [Enumeration and witness verification](../../../scripts/probes/probe_mu16_quintic_fibers.py)
