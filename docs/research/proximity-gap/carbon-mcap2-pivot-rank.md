# Mixed-jet rank room at the second-prime Johnson pivots

On the second named prime at length $n=2^{30}$, the side of Johnson for the MCA supremum is decided by the single closed tests at **314,491,699** half-rate errors and **536,870,913** quarter-rate errors. [Pivot equivalences](../../../ArkLib/Research/ProximityGap/SecondPrimeJohnsonPivot.lean) Every existing second-prime safety proof (half rate through 313,215,000, quarter rate through 534,295,000) uses two ordinary mixed Hasse interpolants and the value resultant between them. This note shows that this route **cannot reach either pivot**. Classification: *refutation of a proof method (no-go)*; it neither proves nor refutes safety at the pivots. [Lean module](../../../ArkLib/Research/ProximityGap/Frontier/CarbonMCAP2PivotRank.lean) · [Integer probe](../../../scripts/probes/probe_carbon_mcap2_pivot_rank.py)

## Where the pivots sit

The earlier rank theorem rules out a positive dimension surplus whenever $t^2\le nd$. [Johnson jet room](johnson-jet-room.md) Each pivot is exactly one agreement step beyond that range:

| Rate | $d=k-1$ | Pivot errors | $t=n-e$ | $\delta=t^2-nd$ |
|---|---:|---:|---:|---:|
| $1/2$ | 536,870,911 | 314,491,699 | 759,250,125 | 1,082,833,961 |
| $1/4$ | 268,435,455 | 536,870,913 | 536,870,911 | **1** |

## The prefix identity

Fix a multiplicity $r\ge1$ and write $B=r(r+1)$. As in the Johnson room proof, the surplus of a shape $(r,v,s)$ is a nonnegative combination of unweighted prefix differences of one scalar column, truncated by the value cutoff. Prefixes of length at most $r$ are harmless whenever $2t\le n+d$. For a prefix whose effective length is $l\ge r+1$ one has the exact polynomial identity
$$
4rBd\,(2lrt-dl(l-1)-nB)
=-\Big(r(r+1)^2\big(4r^2(nd-t^2)+4rdt-4rd^2-d^2\big)
+r\big[(2r((r+1)t-ld)-(r+1)d)^2+4r(l-r-1)^2d^2\big]\Big).
$$
With $t^2\le nd+\delta$ the right side is nonpositive as soon as
$$
4r^2\delta+d^2+4rd^2\le 4rdt. \tag{R}
$$
For $l=r+1$ alone the weaker condition $\delta\le(t-d)^2$ suffices, so a shape with $v\le r$ never has a surplus. Condition (R) is a convex quadratic inequality in $r$; it holds on an interval $[1,R]$ once it holds at both ends.

**Theorem.** If $d\le t$, $2t\le n+d$, $t^2\le nd+\delta$ and either $v\le r$ (with $\delta\le(t-d)^2$) or (R) holds at $r$, then the ordinary mixed Hasse shape of multiplicity $r$, value cutoff $v$ and any total cutoff $s$ has at most as many coefficients as jet equations. (`pivot_no_room`)

## Consequences at the two pivots

The exact endpoints of (R) are **$R_{1/2}=110{,}255{,}990$** and **$R_{1/4}=72{,}057{,}593{,}769{,}492{,}479$** (both checked to fail at $R+1$). Hence a positive-surplus interpolant at the pivot needs

* half rate: multiplicity $r>110{,}255{,}990$ and value cutoff $v>r$; the current production shape has $(r,v)=(88,124)$;
* quarter rate: multiplicity $r>72{,}057{,}593{,}769{,}492{,}479$ and $v>r$.

`HalfSuccessorJetInterpolation.exists_surface` also needs $r\le s+1$. Two counting consequences follow:

1. **Quarter rate.** The total scalar/value degree $s$ of any constructible interpolant exceeds $2^{31}$. Its scalar-only factors alone may then carry more labels than the 128-bit budget, so the factor allocation cannot certify safety. (`quarter_surface_scalar_overflow`)
2. **Half rate.** For any two constructible interpolants, $s_1v_2>R_{1/2}^2>2^{31}$. The value-resultant cutoff above which a primary factor must divide the companion therefore exceeds the budget, and the single-resultant allowance for noncommon factors does too. (`half_surfaces_resultant_overflow`)

Thus deciding either Johnson sign at the second prime requires a different safety mechanism (or a failure construction, such as the split pencil of [SecondPrimeTransversePencil.lean](../../../ArkLib/Research/ProximityGap/Frontier/SecondPrimeTransversePencil.lean) at quarter rate). Incremental parameter retuning of the blown-up Gauss-graph windows cannot cross the pivots.

## Verification ledger

* **Lean (`CarbonMCAP2PivotRank.lean`)**: `pivot_no_room`, `pivot_data` (excesses and exact radius endpoints), `half_pivot_no_room`, `quarter_pivot_no_room`, `half_surplus_forces`, `quarter_surplus_forces`, `half_surface_requires`, `quarter_surface_requires`, `quarter_surface_scalar_overflow`, `half_surfaces_resultant_overflow`. Target axioms: `propext`, `Classical.choice`, `Quot.sound`.
* **Probe**: `python3 scripts/probes/probe_carbon_mcap2_pivot_rank.py` checks the excesses, the radius endpoints, random small shapes and the prefix identity.
* **Scope**: the statement concerns the ordinary uniform-order mixed Hasse rank test used by `exists_surface`. Variable-order (core-weighted) surfaces and other interpolation constructions are not covered.
