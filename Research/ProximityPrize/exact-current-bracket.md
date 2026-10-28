# Exact first-sponsor bracket

Author: Mikhail Izhutkin (@mashingaan)

## Instance and evidence pins

The code is `evalCode g 1073741824 536870911`, equivalently the dimension
`536870912` Reed-Solomon code on the injective domain `i ↦ g^i`.

- Prime `P = 365375409332725729550921208179070755120141565953`
- Generator `g = 303645430271030343624574566109998498685964493478`
- Length `n = 1073741824`
- Target error `epsStar = 1/340282366920938463463374607431768211456`
- Threshold object `MCAThresholdLedger.mcaDeltaStar`, a supremum of good radii

The attained-maximum sponsor formulation remains a separate equivalence obligation.
This investigation does not assume an equivalence merely from shared notation.

The frontier was read at these exact heads:

| PR | Head | Relevant content |
| --- | --- | --- |
| 222 | `f5cbee0fab99dce92f17091402dc6a04ed998d86` | Common-factor upper constructions and earlier canonical ceiling |
| 223 | `01811c0937d2f9d0fbdecefbcbe7021e0876fd4e` | One-way BCHKS bridge and exact production interface no-go results |
| 224 | `d7551e4c651f092ee75c42591ece6389a6181a63` | Canonical triple-incidence floor |

## Current bounds

The strongest axiom-clean finite bracket is

`221512374/1073741824 ≤ mcaDeltaStar C epsStar ≤ 178956971/536870912`.

The seven new modules passed the focused hosted kernel check and the audit of
all 39 declarations at `88a9ebb0e7a6f2f4e7aac4d0e1ba6c4705c4afb5` in
[run 38392632799](https://github.com/mashingaan/proximityprize/actions/runs/38392632799).
Only `propext`, `Classical.choice` and `Quot.sound` occur. The interval width is
exactly `136401568/1073741824`. This improves the original triple floor by
`10828818` Hamming steps and the intermediate exterior floor by `2752918` steps.

The previous axiom-clean lower bound from PR 224 was

`210683556/1073741824 ≤ mcaDeltaStar C epsStar`.

Its full hosted validation passed at the pinned head in
[run 38366369251](https://github.com/SlopDotCash/proximityprize/actions/runs/38366369251).

The full-scale construction from PR 222 now gives the axiom-clean ceiling

`mcaDeltaStar C epsStar ≤ 178956971/536870912`.

The complete canonical transfer in `_IncidenceFullScaleCores.lean` passed
hosted Lean at `0aea589b83e85cd791a592fe1852d6105c5e6f68` in
[run 38377420247](https://github.com/mashingaan/proximityprize/actions/runs/38377420247).
All 13 upper-construction declarations use only `propext`, `Classical.choice`
and `Quot.sound`. That run later stopped on a missing cube-moment object file
before the separate new lower transfers, so it is not a full-validation pass.

The previous interval after formalizing the upper bound had width

`147230386/1073741824 = 73615193/536870912`.

No matching threshold or prize closure is claimed.

The weighted-line continuation gives the intermediate lower bound

`214719988/1073741824 ≤ mcaDeltaStar C epsStar`.

Its integer budget passed independently in
[hosted run 38371632111](https://github.com/mashingaan/proximityprize/actions/runs/38371632111)
at `8122f9b281ca0aa77d3229f6c2275af5abb94022`.
This is `4036432` Hamming steps above PR 224. The production Lean transfer is
`IncidenceCanonicalWeighted.firstPrime_weighted_floor`, verified in run 38377879493.
Together with the full-scale ceiling, its bracket width is
`143193954/1073741824 = 71596977/536870912`.

The continuation retains the cube moment and improves the lower union mass.
On every canonical witness line, choose one private agreement coordinate per
head. They are distinct, and the error union of any two distinct heads contains
all of them. Thus a line of size `ell` contributes deficit at most `d+1-ell`
per distinct triple, rather than `d+1`. No extra RS hypothesis is introduced.
The weighted line function `ell^2*(d+1-ell)` is nondecreasing up to the cap
`b=t+1` under `3b≤2(d+1)`, which holds at the literal production parameters.

The improved weighted budget is

`s*Deficit ≤ s*m*b^2*(d+1-b) + (d+1)*(3m^3+s^2*m^2)`.

Repeated-index tuples retain the safe `3m^2` penalty. The exact optimized
production values are `t=214719987`, `s=56756`, with strict integer slack
`84086556016907437521639365648630530087415504642500`.
At `t=214719988` the slack is
`-77933888686913623791819247124213472026898589548800`.
These computations agree with the kernel-checked literal budget inequality.

The exterior-witness continuation gives the stronger lower bound

`218759456/1073741824 ≤ mcaDeltaStar C epsStar`.

Its exact budget passed in
[hosted run 38374574903](https://github.com/mashingaan/proximityprize/actions/runs/38374574903)
at `100980cf821015c01e253004d52463176114822d`.
The improvement over the previous PR 224 head is `8075900` Hamming steps. The interval
width against the full-scale ceiling is `139154486/1073741824`.

The additional line cap is a consequence of the same canonical witness data.
Private coordinates on a line of size `ell` give
`ell ≤ |E_a intersection E_b|+2` for any two distinct heads on that line.
Since `|E_a|,|E_b|≤t`, their union has size at most `2t-ell+2`.
There is a witness outside the line because its old occupancy cap is `t+1<m`.
The triple formed by that witness and the two line heads is noncollinear.
Distance forces its error union above `d`, whereas cardinality bounds it above
by `3t-ell+2`. Consequently `ell≤3t-d+1`.

For the literal first-sponsor budget, use
`t=218759455`, `b=119407454`, `s=56756`.
The strict integer slack is
`139225481466661345557935197338264914234189314395700`.
At the next error count the slack is
`-32863596224077189172708874475821146373704584396800`.
The canonical transfer is `IncidenceCanonicalExterior.firstPrime_exterior_floor`,
verified in hosted run 38377879493. This refinement adds no polynomial, cross-ratio,
or rational-function assumption beyond the distance condition already extracted.

## Constant-line continuation

For a decoded affine line, let `Q` be the coordinates where its two code
parameters do not jointly agree with the received rows. Two distinct heads
agreeing at a coordinate force joint agreement there. Consequently, on `Q`
at most one line head agrees. For a line of size `ell`, summing the error
incidences gives `ell*|Q| ≤ |Q|+ell*t`.

An outside witness exists because the canonical line cap is `t+1<m`.
Its decoded codeword differs from the corresponding codeword on this line.
Distance forces `d+1 ≤ |Q|+t`. If `ell≥4`, the two inequalities imply
`3(d+1)≤7t`. Thus `7t<3(d+1)` forces every line to contain at most three heads.
The entire argument uses the same canonical witnesses and code distance,
without an extra RS hypothesis.

With at most three heads per line, a distinct ordered pair admits at most one
distinct collinear completion. Therefore there are at most `m^2` ordered
distinct collinear triples. Repeated indices contribute at most `3m^2`.
Writing `D=d+1` and `U3` for total triple error-union mass, distance gives

`D*m^3 ≤ U3+4D*m^2`.

The existing exact cube-moment upper bound then excludes a bad family when

`n^2*D*m^3+(m*(n-t))^3 > n^3*m^3+4D*n^2*m^2`.

For `n=1073741824`, `D=536870913`, `m=n+1`, the literal certified value is
`t=221512372`. Its integer slack is
`2672890434693656925165436850380352537464120000`.
At the next error count the slack is
`-24438696480905180379533610272069166174458125`.
The independent hosted probe checks these values and `7t<3D`.
The lattice transfer proves `IncidenceCanonicalConstant.firstPrime_constant_floor`
at `221512373/1073741824`. The next integer fails this particular cube budget,
not the full canonical assumptions.

## Construction audit

Let `c = 536870910`, `a = 178956971`. Partition coordinates into the common
initial segment of size `c`, three consecutive groups of size `a`, and one
leftover coordinate. Assign group heights `0,1,2` and leftover height `3`.
The common coordinates can also have height `3`, because the locator vanishes there.

Let `Z(X) = ∏_{i<c}(X-g^i)`. The received rows are
`u1(i) = h(i) Z(g^i)` and `u0(i) = h(i)^2 g^i Z(g^i)`.
For group `j` use `v1 = j Z` and `v0 = j^2 X Z`.

The maximum degree is `c+1 = 536870911`, strictly below the dimension.
Each core has `c+a = 715827881` coordinates, at least the dimension.
For every coordinate `x` outside core `j`, the scalar
`gamma(j,x) = -(h(x)+j) g^x` gives agreement on core `j` plus `x`.
The exact support size is `715827882`, so the closed agreement inequality
holds at radius `178956971/536870912`.

Canonical nonjointness follows from interpolation uniqueness on the core.
Any putative row-1 codeword explaining the full witness must equal `j Z`,
which disagrees at `x` because both `h(x)-j` and `Z(g^x)` are nonzero.

The scalar coefficients lie in `{1,2,3,4,5}`. Their `n`-th powers modulo `P`
are pairwise distinct. A scalar collision therefore forces equal coefficients,
then equal coordinates by generator injectivity, then equal group indices.
This gives `3(n-c-a) = 1073741829 = n+5` distinct bad scalars.

The exact normalized error comparison is strict:

`1073741829 * 340282366920938463463374607431768211456 - P`
`= 1701411834604692317316873036952682627071 > 0`.

Thus the event mass exceeds `epsStar`, not merely its floor approximation `n/P`.
`mcaDeltaStar_le_of_bad` converts that strict error inequality into a non-strict
threshold ceiling at the bad radius. It does not assert goodness at the ceiling.

The full support claim uses the factorization
`w_j - (u0+gamma*u1) = (j-h) Z ((j+h)X+gamma)`.
Outside the core the first two factors are nonzero. Two further roots would
give a scalar collision, which the coefficient-power certificate excludes.
This claim concerns the designated head, not every possible alternative head.

## Finite extremal problem behind PR 224

Fix `m = 1073741825` distinct scalar parameters `gamma_i` and heads `w_i` in
a vector subspace `C` over the prime field. Let the coordinate set have size
`n = 1073741824`. Every witness has agreement set `T_i` and error set
`E_i = T_i^c`, with `|E_i| ≤ t`.

There are received rows `u0,u1` such that on `T_i`,
`w_i = u0 + gamma_i*u1`. No pair of elements of `C` jointly explains these
two received rows on `T_i`.

The only code-distance assumption used is that a codeword supported on at most
`d = 536870912` coordinates is zero. Consequently, a triple with error union
of size at most `d` lies on one affine head line. Every pair of distinct scalar
parameters determines its unique head line. A line contains at most `b = t+1`
witnesses, by the private-coordinate argument and canonical nonjointness.

The extremal question is whether such a family can exist. The RS wrapper is
needed to instantiate the support-distance assumption, not to evaluate the
remaining finite inequalities.

## Moment identities and finite budgets

After padding errors to size `t`, let `a_x` count witnesses agreeing at coordinate
`x`. For ordered tuples with repetition,

`U_r = sum_{i_1,...,i_r} |E_{i_1} union ... union E_{i_r}|`
`= n*m^r - sum_x a_x^r`.

Also `sum_x a_x = m(n-t)`. Convexity gives

`n^(r-1) U_r + (m(n-t))^r ≤ n^r m^r`.

The number of tuples with exactly `j` distinct indices is
`StirlingSecond(r,j) * falling(m,j)`. Therefore the repeated-index contribution
is exactly `m^r - falling(m,r)`. Dropping all their nonnegative union masses
is safe but may lose information. This loss is explicit, not an optimality claim.

For `r≥3`, a distinct tuple with union size at most `d` is collinear, because
each triple is collinear and the line through a fixed pair is unique.
Peel whole lines of size at least an integer `s≥2`. A collinear tuple mixed
between the peeled line and its complement contains exactly one peeled point.
Its remaining coordinates determine that point, giving at most `r*m^(r-1)`
mixed tuples per peeled block. There are at most `m/s` blocks. The terminal
family has line occupancy below `s`, giving at most `m^2*s^(r-2)` distinct
collinear tuples. Within the peeled blocks, the line cap gives `m*b^(r-1)`.

The resulting conservative budget is

`s L_r ≤ s*m*b^(r-1) + r*m^r + s^(r-1)*m^2`.

Combined with the moment identity, a positive value of

`s*n^(r-1)*(d+1)*falling(m,r) + s*(m(n-t))^r`
`- s*n^r*m^r`
`- n^(r-1)*(d+1)*(s*m*(t+1)^(r-1)+r*m^r+s^(r-1)*m^2)`

excludes the family under this budget. For each order the independent probe
minimizes the strictly convex block cost over integers and searches the exact
largest admissible `t`. All calculations use integers and rational arithmetic.
Orders above three remain research derivations until formalized.

The independent arithmetic check passed in
[hosted run 38370208361](https://github.com/mashingaan/proximityprize/actions/runs/38370208361)
at `250f0876459990653a2bafee77450ddc88c7b2ce`.

| Order | Optimal integer block | Largest certified error count | Prospective lattice floor |
| --- | --- | --- | --- |
| 3 | 56756 | 210683555 | 210683556/1073741824 |
| 4 | 1321123 | 169941563 | 169941564/1073741824 |
| 5 | 6739646 | 138942677 | 138942678/1073741824 |
| 6 | 18194417 | 117144077 | 117144078/1073741824 |

The triple optimum selects block `56756`, one above the block used in PR 224.
This improves arithmetic slack but not its integer threshold. Exact repeated-index
partitions also leave that threshold unchanged.

There is an all-orders obstruction for this particular budget. If `r≥4` and
`t/n≥1/6`, dropping its nonnegative collinearity penalty and replacing
`falling(m,r)` by `m^r` bounds its normalized slack above by

`1/2 + 1/n + (5/6)^4 - 1 = 1/n - 23/1296 < 0`.

Thus no higher order in this budget can certify even `1/6`, whereas the triple
floor is strictly larger than `1/6`. Further blind iteration of this same budget
cannot improve the current floor. This is an optimization obstruction for the
displayed inequalities, not a countermodel to all canonical witness assumptions.

Increasing the order in this particular budget is not automatically a stronger
argument. Nor does failure of this budget establish a barrier for the full
canonical assumptions. A barrier still requires a countermodel or sharp
optimization certificate satisfying all extracted assumptions.

## Theorem map

| Bound or step | Assumptions | Evidence |
| --- | --- | --- |
| PR 224 floor `210683556/1073741824` | Exact sponsor code, canonical events, RS support distance | Axiom-clean Lean and full CI |
| Weighted triple geometry | Canonical bad witnesses, linear code, pair-pinned agreement intersections | Seven axiom-clean Lean declarations in hosted run 38375209285 |
| Exterior occupancy cap | The same assumptions, triple support distance, one witness outside each line | Two axiom-clean Lean declarations in hosted run 38375209285 |
| Floor `218759456/1073741824` | Exterior occupancy cap, weighted triple budget, exact cube moment and lattice transfer | Independent arithmetic and canonical axiom-clean Lean in run 38377879493 |
| Constant line occupancy | Pairwise scalar pin, joint-agreement complement count, outside witness and code distance, literal `7t<3(d+1)` | Axiom-clean Lean in run 38388307522 |
| Floor `221512373/1073741824` | Constant line cap three, unique distinct collinear completion, cube moment and lattice transfer | Independent arithmetic and canonical axiom-clean Lean in run 38388307522 |
| Core sizes and locator degrees | Three finite coordinate embeddings and product degree bound | Axiom-clean Lean in run 38377420247 |
| Nonjointness | Core size at least dimension, RS interpolation uniqueness, off-core nonzero factors | Axiom-clean Lean in run 38377420247 |
| Scalar census | Exact generator order and five coefficient-power separations | Independent arithmetic and axiom-clean Lean in run 38377420247 |
| Ceiling `178956971/536870912` | All construction steps and strict normalized mass | Canonical axiom-clean Lean in run 38377420247 |
| Higher moment budgets | Line geometry, occupancy cap, support distance, exact repetitions, convexity | Independent hosted integer audit passed, research derivation above order three |

No refuted predecessor-cap, generic BGK estimate, or asymptotic Jeronimo
conclusion is used. Literature work will be restricted to a specific missing
finite structural lemma if this investigation identifies one.

## Refined pair-union cube budget

The strongest floor is now 221512374/1073741824. For each distinct pair,
`bad_witness_pair_union_distance` derives D <= |Ea union Eb|+t from an outside
canonical witness and code distance. `triple_mass_lower_of_pair_union` charges
t to each nondiagonal degenerate triple and D to each diagonal triple.
With line cap three this gives D*m^3 <= U3+4*t*m^2+D*m.
The production theorem uses t=221512373 and the exact integer cube inequality.
Both new geometry declarations and the canonical transfer passed the focused
hosted Lean and axiom check in run 38392632799 at 88a9ebb0e.
Earlier constant-budget values above document the predecessor proof.
