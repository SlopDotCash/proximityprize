# #466: ten-by-ten attack matrix for the centered depth-seven gate (2026-07-11)

## Control target and honesty convention

This is the current 100-cell research board requested for the Paley/proximity-gap campaign.  It
supersedes broad idea lists that predate the mandatory DC correction.  Every cell is tested against
the same production statement

```text
q * E_7(G) - n^14 <= q * 2^18 * n^7,
n = 2^30,
q = n * (2^128 + 192) + 1.
```

Equivalently, for a primitive additive character,

```text
sum_(b != 0) |eta_b|^14 <= q * 2^18 * n^7.
```

The status vocabulary is deliberately strict:

- **THEOREM**: an unconditional identity or bound is proved (normally also checked in Lean).
- **ACTIVE**: a new, quantitatively specified input could move the gate and has not been refuted.
- **EQUIVALENT**: a useful change of coordinates, but no reduction in mathematical strength.
- **INSUFFICIENT**: a theorem applies but its exact production budget misses.
- **REFUTED**: a proposed uniform statement has a counterexample or contradiction.
- **PROBE**: finite evidence only; never promoted to a theorem.

The ten named theories below are research programmes, not asserted mathematics.  Each has ten
independent sub-attacks, an exact win condition, and a falsifier.  The point is to make invention
testable.

## Angle 1: Centered Translate Restriction (CTR) -- harmonic analysis

**Theory.**  Treat the depth-six centered autocorrelation as a zero-mean, positive-definite,
multiplicatively invariant function and prove restriction directly on the nonlinear translate
`1-G`.

| sub-angle | status | exact attack / falsifier |
|---|---|---|
| CTR-1 exact physical-space collapse | **THEOREM** | `_BGKCenteredConvolutionCollapse`: `qE_7-n^14 = n sum_(u in G)(qC_6(1-u)-n^12)`. |
| CTR-2 Fourier audit | **THEOREM / EQUIVALENT** | The last expression equals `sum_(b!=0)|eta_b|^14`; this prevents mistaking dimension reduction for a moment bypass. |
| CTR-3 zero-global-mean restriction | **STRUCTURAL FORM REFUTED / FOURIER CONE EQUIVALENT** | A centered-delta kernel gives an unbounded zero-mean, additive-PSD, invariant scaling ray. More sharply, `_BGKCenteredTranslateConeDuality` proves the unit-mass orbit-spectral cone optimum is exactly `max_(b!=0)|eta_b|^2/n`, attained on one orbit: the generic cone theorem is the Paley bound itself. |
| CTR-4 positive/negative excursion pairing | **ACTIVE** | Construct an injection or transport from `u` with `D(1-u)>0` to ambient lags with compensating negative mass. It must retain weights, not merely supports. |
| CTR-5 dyadic martingale differences | **ACTIVE** | Decompose along `G_1 < ... < G_30=G` and seek orthogonality of centered increments on `1-G_j`. Falsifier: coherent increments with the same sign at every level. |
| CTR-6 polynomial restriction majorant | **EQUIVALENT risk** | Approximate `1_{1-G}` by an additive Fourier polynomial with small weighted coefficients. The coefficients are Gauss periods; any proof using their sup is circular. |
| CTR-7 signed density increment | **ACTIVE** | If the translate sum is too large, force a multiplicative coset on which `f_6-n^6/q` has larger density, then iterate to a forbidden concentration. Quantify entropy loss per step. |
| CTR-8 centered hypercontractivity | **UNIVERSAL FORM AND SCALAR BOOTSTRAPS REFUTED** | The exact `(13313,256)` cell exceeds `2^18`. A production orbit spike passes scalar moments through 12 and fails by 15--16 bits. Galois rationality and a period congruence kill that literal spike, but a nonzero integral trace-correct profile still passes the same ceilings and fails by 8--9 bits. The survivor needs quantitative simultaneous-conjugate arithmetic at seventh order. |
| CTR-9 additive uncertainty with invariance | **INSUFFICIENT unless strengthened** | Ordinary support uncertainty ignores signs and returns a `sqrt(q)` scale. A viable theorem must use simultaneous additive Fourier and multiplicative-orbit invariance. |
| CTR-10 local-to-global discrepancy | **ACTIVE** | Bound the `1-G` restriction by a small family of affine images whose signed average is the global zero mean. Required covering weights must have total variation `O(1)`, not `q/n`. |

## Angle 2: Primitive Packet Completion Transport (PPCT) -- additive combinatorics

**Theory.**  Charge every finite-characteristic depth-seven accident to primitive balanced leaves,
but measure signed completion multiplicity rather than positive packet existence.

| sub-angle | status | exact attack / falsifier |
|---|---|---|
| PPCT-1 FS11 generic/wraparound split | **THEOREM** | `E_7 = trivialCountG + wraparoundExcessG`. |
| PPCT-2 Wick payment | **THEOREM** | Pairing induction gives `trivialCountG <= 13!! n^7 = 135135 n^7`. |
| PPCT-3 corrected slack ledger | **THEOREM** | The remaining coefficient is exactly `2^18-13!!=127009`, with the mandatory `n^14` DC supply retained. |
| PPCT-4 injective/repeated partition | **THEOREM / GENERIC CONE CLOSED** | The marked sunflower law has `D_0=D_1=0`; positive Wick completion costs `158760` already at `D_2` and `2714355` over depths 2--6. The signed inverse is equivalent and has coefficient mass `2^143--2^144`. Total positivity gives only lower growth: the PF-infinity ray `D_7=T` has `W_2=...=W_6=0`, arbitrary `W_7`, leaving the exact primitive gap `135135-126871=8264` (6.115%). |
| PPCT-5 primitive nonzero leaf existence | **THEOREM on G153 chain** | Every injective depth-seven wraparound tuple reaches a primitive balanced leaf with nonzero cyclotomic label. |
| PPCT-6 charge-mass sandwich | **THEOREM / INSUFFICIENT** | Primitive charge mass lies between one and three times the injective excess; this is only a factor-three re-encoding. |
| PPCT-7 completion multiplicity | **NAIVE CAP AND PROPER-LEAF RECURSION REFUTED** | Small cells have fibres as large as `7242` and up to `44` packets per configuration. At `(n,p)=(16,337)` there are exactly `48` nonzero primitive depth-seven disjoint subset pairs, so recursion through leaves of depth at most six is false. |
| PPCT-8 signed leaf charge | **EXACT LOCAL/FIBER-CONSERVATION THEOREMS / production count open** | Actual witnesses lie in the five-letter alphabet with `l1<=14`. Exact local profiles dictate the formal kernel `(7!)^2[x^7y^7](xy)^A(x+y)^B(1+x^2+y^2)^C`; `2A+B+2Z=14`, so only the all-`+-1` sector uses 14 coordinates and its formal fixed-label factor is `14!`. Nonunit sectors use at most 13 coordinates, but source rarity cannot bound collision rarity; the full cardinality bijection is not packaged. The `ZMod 17` vector `[1,2,1,2,2,2,2,0]` refutes alphabet-only kernel-freeness. |
| PPCT-9 repeated-coordinate recursion | **THEOREM / FULLY CLOSED MODULO INJECTIVE INPUT** | All 88 Newton monomials, exact `B_k` masses, eta-to-rpow bridge, fixed `R=79880` target `<138`, `1/1024` secant, and end-to-end field consumer are formal. Internal first-collision covariance cannot replace the injective input: the deletion law also contains `2Cov(J,P)`, while G191 and G193 prove positive genuine-subgroup covariance for the lexicographic and symmetric partitions. Even returning all `138` repeated units leaves `135135-127009=8126`. |
| PPCT-10 BSG inverse theorem | **EQUIVALENT risk** | Large centered `E_7` should produce an approximate additive subgroup inside `G`; quantify parameters. Generic BSG losses must be checked against all 18 coefficient bits. |

## Angle 3: Annihilator Jacobi Tensorization (AJT) -- character-sum theory

**Theory.**  Expand the nonzero fourteenth moment through the annihilator `K=G^perp`, then exploit
the fact that all thirteen character variables lie in one subgroup rather than arbitrary sets.

| sub-angle | status | exact attack / falsifier |
|---|---|---|
| AJT-1 thirteen-variable top stratum | **THEOREM / exact equivalence** | `S13=(1/m) sum_c ((m eta_c+1)/sqrt(q))^14=(m^13/q^7) sum_c(eta_c+1/m)^14`; `_AJT13CenteredMomentEquivalence` checks the normalization and budget equivalence. |
| AJT-2 Lu--Zheng two-coordinate cancellation | **INSUFFICIENT / THEOREM arithmetic** | The applicable bound `(m-1)^12 sqrt(q)` misses the generous top-stratum socket by strictly `2^701` to `2^702`; `_BGKJacobiTensorProductionGap` checks the squared comparison in Lean. |
| AJT-3 annihilator tensorization law | **EQUIVALENT, not independent** | `S13 <= C m^7((q-1)/q)^6` iff the centered physical moment is `<=C q n^6`. Pursue only with genuinely new production-specific structure. |
| AJT-4 product-fibre orthogonality | **THEOREM / no free saving** | Summing every free character variable turns the tensor into the positive quantity `(a^{*14})(1)=||a^{*7}||_2^2`; orthogonality changes coordinates but supplies no cancellation. |
| AJT-5 diagonal partition | **ACTIVE** | Classify equality/product coincidences among the thirteen characters and pay them combinatorially; apply cancellation only to the genuinely transverse stratum. |
| AJT-6 iterative Jacobi recursion | **ACTIVE** | Use `J_r` factorization into binary Jacobi sums without taking absolute values between stages. Track whether cocycle phases telescope on `K`. |
| AJT-7 multiplicative large sieve on `K` | **ACTIVE / likely two-variable ceiling** | A useful form must save about `m^5`; standard large sieve cancels at most one or two free character variables. |
| AJT-8 principal-character boundary | **THEOREM at Wick scale** | `_AJT13CenteredBoundaryBridge` proves centered coefficient `135135` implies uncentered coefficient `2^18` for `m>=21`, using `(x-c)^14 <= (21/20)^13 x^14+21^13 c^14`. |
| AJT-9 phase-cocycle cohomology | **ACTIVE** | Regard normalized Jacobi sums as a `U(1)` cocycle on the character group and prove high tensor powers have no invariant section except classified diagonals. |
| AJT-10 small-prime scaling law | **GLOBAL CONSTANT REFUTED / production trend open** | Exact `(n,m,q)=(256,52,13313)` gives `S13/m^7=313471.77...>2^18`; production-exponent analogues trend toward Wick scale but do not prove the production cell. |

## Angle 4: Fermat Primitive Trace Compression (FPTC) -- algebraic geometry

**Theory.**  Interpret the centered moment as the primitive Frobenius trace of a Fermat-type
hypersurface, remove Tate/diagonal classes exactly, and bound only the residual cohomology.

| sub-angle | status | exact attack / falsifier |
|---|---|---|
| FPTC-1 point-count dictionary | **ACTIVE** | Express `qE_7-n^14` as a primitive point-count deviation for the equal-sums Fermat variety with coordinates restricted to `G`. |
| FPTC-2 Tate-class subtraction | **ACTIVE** | Match Wick pairings and the DC term to explicit algebraic cycles before invoking Weil. This is the geometric analogue of centering. |
| FPTC-3 singular-stratum resolution | **ACTIVE** | Blow up coordinate coincidences and show their exceptional divisors account for the `13!!` term. Falsifier: an unclassified component of comparable dimension. |
| FPTC-4 raw Deligne bound | **INSUFFICIENT** | Termwise square-root bounds multiplied by the Betti number reproduce the enormous character-family loss. |
| FPTC-5 monodromy invariant tensors | **ACTIVE** | Compute the geometric monodromy of the 13-fold Jacobi sheaf; win if invariants are exactly the diagonal partitions counted by PPCT. |
| FPTC-6 conductor independent of `m` | **REFUTED risk** | The sheaf rank/conductor normally grows with the annihilator family. A claimed uniform conductor must be checked against the number of characters. |
| FPTC-7 toric Newton-polytope compression | **ACTIVE** | Use Adolphson--Sperber nondegeneracy to replace ambient Betti growth by mixed volume after quotienting the six product constraints. |
| FPTC-8 per-prime equidistribution | **ACTIVE** | Vertical Sato--Tate averages over primes do not imply the fixed production prime. A viable theorem needs effective exceptional-prime control. |
| FPTC-9 trace-function tensor independence | **ACTIVE** | Apply Goursat--Kolchin--Ribet criteria to show off-diagonal tensor products have no trivial constituent; quantify the remaining family sum. |
| FPTC-10 geometric AJT bridge | **ACTIVE** | Prove FPTC-5 implies AJT-3 with an explicit constant, making monodromy computation a genuine consumer rather than an analogy. |

## Angle 5: Cyclotomic Valuation-to-Phase Transfer (CVPT) -- algebraic number theory

**Theory.**  Combine exact ideal/valuation information for cyclotomic relations with a new
archimedean phase-transfer principle; valuations alone count support but do not cancel phases.

| sub-angle | status | exact attack / falsifier |
|---|---|---|
| CVPT-1 resultant divisibility | **THEOREM** | Every wraparound relation gives production-prime divisibility of a nonzero cyclotomic norm. |
| CVPT-2 primitive norm packet | **THEOREM on G153 chain** | Injective accidents expose a nonzero primitive cyclotomic leaf. |
| CVPT-3 norm-size union bound | **INSUFFICIENT** | Bounding each norm and counting prime divisors controls possible primes, not the number or sign of relations at one fixed prime. |
| CVPT-4 Stickelberger ideal factorization | **ACTIVE** | Determine valuations of the Jacobi/Gauss products in AJT exactly; falsifier: all top-stratum terms have identical allowed valuation. |
| CVPT-5 Gross--Koblitz phase lift | **ACTIVE** | Use the `p`-adic gamma formula to relate valuations and unit phases, then seek cancellation in the unit part over the annihilator subgroup. |
| CVPT-6 product formula transfer | **ACTIVE** | Prove that unusually coherent complex phases force compensating growth at a controlled `p`-adic place, contradicting the exact norm. Ordinary product formula without localization is too weak. |
| CVPT-7 cyclotomic-unit regulator | **EQUIVALENT risk** | Determinant/regulator fixes products of conjugates, not the largest conjugate or the fourteenth Schatten norm. |
| CVPT-8 dyadic conductor recursion | **ACTIVE** | Factor the `2^30` cyclotomic tower and track primitive bad packets level by level. Win requires decay, not a factor-two loss, per lift. |
| CVPT-9 CRT reconstruction | **INSUFFICIENT at present** | Exact congruences reconstruct bounded integer counts only after a modulus exceeding their range; the required range is exponential in `n`. |
| CVPT-10 valuation-weighted signed charge | **ACTIVE** | Assign each PPCT primitive leaf its exact prime-adic multiplicity and a complex unit phase; prove orthogonality among leaves with distinct valuation profiles. |

## Angle 6: Nonbacktracking Wick Subtraction (NWS) -- spectral graph/operator theory

**Theory.**  Replace raw adjacency traces by a nonbacktracking or orthogonal-polynomial trace that
automatically subtracts tree/Wick excursions and isolates finite-field cycles.

| sub-angle | status | exact attack / falsifier |
|---|---|---|
| NWS-1 Paley eigenvalue dictionary | **THEOREM / EQUIVALENT** | Nonprincipal eigenvalues of `Cay(F_q,G)` are the periods `eta_b`. |
| NWS-2 raw trace moments | **THEOREM / EQUIVALENT** | `Tr(A^14)=qE_7`; subtracting only the principal eigenvalue gives the repaired target. |
| NWS-3 cyclotomic matrix Schatten bridge | **THEOREM-level identity; formalization pending** | Wu--Wang's `A=VDV` gives `s_j(A)=m|eta_j|` and exact Schatten-14 equivalence. |
| NWS-4 determinant/geometric mean | **INSUFFICIENT / FORMAL HOUSE FALSIFIER** | Product of singular values cannot upper-bound the fourteenth power sum. Separately, an irreducible monic integer family has fixed norm, trace, and the exact Wu--Wang--Pan linear-coefficient coordinate but an arbitrarily large real root, so one Jacobi determinant does not bound the period house. |
| NWS-5 nonbacktracking trace polynomial | **ORDINARY HASHIMOTO FORM REFUTED** | The exact degree-14 Ihara polynomial removes 14 cyclically adjacent reversals, versus all `C(14,2)=91` Wick first-pair placements, leaving coefficient `77d+14`. A closed nonbacktracking repeated-direction word survives, and equal adjacency eigenvalues can have opposite injective transforms. A univariate polynomial cannot isolate the packet. |
| NWS-6 Ihara zeta quotient / coloured Newton operator | **EXACT LATE SIGNED MATRIX / higher mixed arithmetic open** | The coloured Newton operator and physical Newton joins are exact. Cross Parseval turns every matrix cell into a collision count; the packets equal `J6,J7`, raw signed forms are `36C6,49C7`, and DC subtraction yields `(6!)²Δ6,(7!)²Δ7`. Opposite parity is a coefficient sign, not a covariance-sign theorem. Production pair Gram data still miss by 123--124 bits. |
| NWS-7 nonlinear period fixed point / Krein cone | **ALL-ORDERS POSITIVITY NO-GO / arithmetic active** | `|eta_b|^2=n+sum_(u!=1)eta_{b(u-1)}`. Schur multiplication is Fourier-profile convolution, and every nonnegative orbit profile survives all convolution powers. These positivity constraints leave the enlarged-cone LP at the worst-period square; fixed intersection values remain live. |
| NWS-8 transition/intersection arithmetic | **EXACT C12 ROW COUPLING / marginal NO-GO; alignment active** | The dominant cross count is exactly `C12=Σ_t W_G(t)R_r(t)`, with `W_G(t)=#{y∈G:2y−t∈G}` and `R_r` the adjacent subset-difference row. A two-cell theorem shows fixed masses and square masses permit inner product 0 or full, so Cauchy/Gram diagonals cannot force the gate. Joint cyclotomic-row placement is the live input. |
| NWS-9 dyadic interlacing | **ACTIVE** | Compare spectra for nested order-`2^j` subgroups via equitable partitions. Falsifier: no deterministic interlacing after changing the Cayley connection set. |
| NWS-10 deterministic lift theory | **ACTIVE** | Model `G_j -> G_{j+1}` as a signed graph lift and prove the new spectrum remains controlled. Random 2-lift theorems do not apply without pseudorandom signs. |

## Angle 7: Entropic Seven-Step Mixing (ESM) -- probability and information theory

**Theory.**  Study the distribution of the sum of seven independent uniform subgroup elements and
prove chi-square mixing at ambient, rather than support, scale.

| sub-angle | status | exact attack / falsifier |
|---|---|---|
| ESM-1 chi-square identity | **THEOREM / EQUIVALENT** | The target is `sum_x (r_7(x)/n^7-1/q)^2 <= 2^18/n^7`; for the injective law the exact normalized allowance lies between `2^-36` and `2^-35`. |
| ESM-2 fixed-depth inverse Littlewood--Offord | **INSUFFICIENT** | Costa's applicable bound is at scale `1/n`; its centered consequence misses by strictly `2^161` to `2^162`. |
| ESM-3 entropic CLT | **EXACT LATER DEFECT/SPLIT LEDGERS / arithmetic open** | Rational caps are exactly `Bn(r+1)^2Δ_(r+1)≤A(n-r)^2Δ_r`. One full unit or the distributed `(10.5,12.5)` pair closes under `501/500`. For the late pair the exact proposed split is `10500+21=10521` and `12500+25=12525`: bound the centered `U1-U2` energy, then a small signed tail. The first ratio is above `3+2^-29`. |
| ESM-4 log-Sobolev Cayley walk | **EQUIVALENT risk** | The log-Sobolev/spectral constant of the additive walk generated by `G` is governed by the same worst period. |
| ESM-5 collision-entropy tensorization | **GENERIC DISTINCT-SAMPLING ROUTE REFUTED / subgroup-specific active** | Coupling misses by over `141` energy bits and leaves a period ceiling `1835x` too large. Even `p_1,...,p_7=0` can leave `75%` of phase mass in Johnson grades 1--6, so Newton subtraction does not isolate the top exterior grade. |
| ESM-6 exact trajectory cells | **PROBE only / density and covariance-only theorems refuted** | Selected-cap successes rank 6→7 first and 5→6 second, but birthday crossing alone fails. Exact Newton decomposition finds dominant `cross12<0`; an adverse `(64,750209)` cell also has enough cross cancellation in isolation, while its `U1` diagonal excess makes both ratios fail. Only the combined `U1-U2` energy plus tail is stable; no finite cell proves production. |
| ESM-7 Stein coupling on cosets | **ACTIVE** | Build an exchangeable pair by multiplying a random summand by a random subgroup element; bound the Stein remainder in fourteenth norm. |
| ESM-8 mod-Gaussian correction | **SCALAR MOMENTS THROUGH SIX REFUTED / joint cumulant active** | `_BGKLowerMomentOrbitSpikeNoGo` passes even hypothetical Wick ceilings for powers `s^2,...,s^6` with `s=|eta|^2`, yet fails the `s^7` target by 15--16 bits. A viable correction must constrain the joint orbit profile at seventh order. |
| ESM-9 concentration over frequency | **INSUFFICIENT for worst case** | Average tail bounds can tolerate a bad orbit; coset invariance reduces `q-1` frequencies to `m` but does not remove the maximum. |
| ESM-10 entropy-production inverse theorem | **PHYSICAL TWO-COLOUR SOCKET / production estimate open** | At 2→3 Young drops the required signed mass. At 5→6/6→7, `L=V(U1-U2)` is literal: `C11+C22−2C12` minus exact DC. Erase/insert cancels repeated-U1 with fresh-U2 and leaves fresh weight1 minus fresh weight3. Defined tails feed the `10500+21`/`12500+25` ledgers; only the production estimates remain. |

## Angle 8: Projective Accident Orbit Rigidity (PAOR) -- incidence geometry

**Theory.**  Use the projective symmetry of signed zero-sum tuples to classify accident fibres
exactly, then charge geometric orbits rather than ordered tuples.

| sub-angle | status | exact attack / falsifier |
|---|---|---|
| PAOR-1 rerooting action | **THEOREM** | Rerooting preserves solutions, lawfulness, and accidents. |
| PAOR-2 scalar stabilizer exclusion | **THEOREM under accident and char != 2** | Nontrivial scalar symmetry forces a signed coordinate to be `1`, hence lawful; dropping accident gives counterexamples. |
| PAOR-3 fibre `1/2/6` classifier | **THEOREM** | Signed-injective gives 1, one repeated pair gives 2, and a `3+1` pattern gives 6; scalar symmetries are excluded for odd-characteristic accidents. |
| PAOR-4 orbit size `24/12` | **THEOREM at production** | Two-pair patterns are lawful and the certified `-3` test excludes `3+1`, so every production accident orbit has size 24 or 12 and the total count is divisible by 12. |
| PAOR-5 depth-seven higher symmetric group | **ACTIVE** | Generalize from quadruple `S_4` to the signed 14-coordinate action relevant to `E_7`; classify stabilizers by set partition. |
| PAOR-6 exact signature-fibre count | **THEOREM / production histogram open** | For fibre sizes `k_v` of `kappa_n(x)=(x-1)^n`, `#accidents=sum_v(k_v^2-2k_v+s_v)=sum_v k_v^2-2n+3`. This reduces `n^2` triples to an `n-1` histogram but is still too large directly. |
| PAOR-7 cyclotomic-unit signature | **THEOREM exact quotient / production injectivity open** | For exact root support, `accidents H=empty` iff `kappa_n` is injective modulo `x~x^-1`. This now conditionally forces marked `D_2=0` for both production primes, but no in-tree theorem proves the required `n=2^30` injectivity. |
| PAOR-8 canonical discriminant recurrence | **THEOREM reductions / exact finite certificate format / analytic open** | `K_(2n)=Sq(K_n)*J_(2n)` is formal. Projection gives 59/67-bit targets; Weil misses by 127--129 bits and the cyclotomic-number threshold reverses. A keyed-bucket `Nodup` format is wired to both production maps, but no table is populated and every certificate needs all `2^29` rows (10 GiB at 20 bytes each). |
| PAOR-9 incidence theorem regime check | **INSUFFICIENT unless subgroup-sensitive** | Generic point-line/point-curve incidence bounds lose powers of `q` at `n=q^0.19`. |
| PAOR-10 signed orbit census | **ACTIVE** | Attach a sign/centered weight to each projective orbit so orbit compression preserves DC cancellation instead of counting all accidents positively. |

## Angle 9: Dyadic Quotient Renormalization (DQR) -- arithmetic dynamics

**Theory.**  Exploit the exact chain of order-`2^j` subgroups as a renormalization flow and show
that the bad component contracts when one adjoins square roots.

| sub-angle | status | exact attack / falsifier |
|---|---|---|
| DQR-1 subgroup tower | **THEOREM** | `G_j` is the square image of `G_{j+1}` and `G_{j+1}=G_j union aG_j`. |
| DQR-2 period two-scale equation | **THEOREM** | `_DQR23TwoScaleCenteredRecursion` proves `eta_(G union aG)(b)=eta_G(b)+eta_G(ba)` and realness under `-1 in G`. |
| DQR-3 centered-energy recursion | **THEOREM, symmetrized** | The exact binomial ledger is palindromic at an adjoining twist `a^2 in G`, reducing it to seven paired cross strata plus the within term, with no absolute-value loss. |
| DQR-4 contraction coefficient | **UNIFORM CONTRACTION REFUTED / data layer theorem** | Every stratum is a centered rep--rep correlation at the quotient involution. At `p=65537`, the step ratio divided by `2^7` is `23.70` (`n=16`) and `28.41` (`n=32`), all cross terms aligned. Mean, inversion symmetry, and CS cannot control the distinguished point. |
| DQR-5 Hasse--Davenport lift | **INSUFFICIENT as currently used** | Known product identities reduce some phase degrees of freedom but stop with a linear-size residual. |
| DQR-6 renormalized Jacobi cocycle | **ACTIVE** | Track AJT normalized Jacobi phases under `K_j -> K_{j+1}` and look for a martingale-difference law. |
| DQR-7 exceptional-level budget | **ACTIVE, mandatory** | Small levels can expand by more than `28*2^7`; any tower proof must compensate them quantitatively. Exact ratio products telescope, so compensation needs new endpoint arithmetic rather than formal recursion alone. |
| DQR-8 production-index arithmetic | **THEOREM factorization / ACTIVE use** | `m=2^6*7^3*26407*279991*4533259*462478642316479903` is Lean-checked. Test CRT tensorization, but do not assume Jacobi phases factor with the abstract character group. |
| DQR-9 semiprimitive/CM branch | **PROBE / likely absent** | Test whether the production prime satisfies any semiprimitive congruence giving explicit periods. If not, record an exact exclusion. |
| DQR-10 tower transfer theorem | **EQUIVALENT endpoint risk** | The product of exact step ratios is the endpoint moment ratio. A transfer theorem is useful only if it injects new field-specific control; bare telescoping reconverges to the Paley wall. |

## Angle 10: Certificate-Carrying Per-Prime Descent (CPPD) -- computation and formal proof

**Theory.**  Combine symbolic reductions, exact finite certificates, and a small analytic residual
so every numerical claim is independently checkable and every extrapolation has a theorem.

| sub-angle | status | exact attack / falsifier |
|---|---|---|
| CPPD-1 exact production arithmetic | **THEOREM/probe certificate** | All exponent gaps and target constants are checked with integers; no floating-point verdicts. |
| CPPD-2 small-prime full spectrum | **PROBE** | Enumerate all dyadic subgroups feasible by FFT and record `E_7`, CTR translate values, AJT tensor values, and worst periods. |
| CPPD-3 conjecture falsifier harness | **ACTIVE** | Every proposed uniform lemma gets randomized and exhaustive small-field tests before Lean work. |
| CPPD-4 SAT/CP-SAT packet multiplicity | **ACTIVE** | Optimize PPCT completion multiplicity under exact polynomial and range constraints; emit counterexample certificates. |
| CPPD-5 symbolic orbit classifier | **ACTIVE** | Generate PAOR set-partition cases and proof obligations, but check every generated certificate in Lean. |
| CPPD-6 trace/cohomology computation | **ACTIVE** | Use exact finite-field cohomology for small arities to identify which FPTC strata actually carry the excess. |
| CPPD-7 production direct enumeration | **REFUTED by scale** | `m` is about `2^128`; neither coset FFT nor matrix construction is feasible at production. |
| CPPD-8 interval/rounding discipline | **THEOREM practice** | Use integer squaring for square-root comparisons and rational enclosures for logarithms; keep diagnostics separate from verdicts. |
| CPPD-9 Lean socket library | **THEOREM-rich / ACTIVE capstone** | CTR/AJT equivalences, exact subset variance, packet=`J6/J7`, DC-subtracted signed Newton ledgers, cross Parseval for physical joins, the `10500+21`/`12500+25` split consumers, the deletion-covariance no-go, projected-kappa forms, modular adapters, and the restricted sparse kernel are formal. The remaining task is the production two-colour/tail estimate or a checked finite certificate. |
| CPPD-10 hybrid closure | **ACTIVE** | Ideal endgame: an analytic theorem handles all but finitely many explicitly bounded strata/levels, and machine certificates close the finite remainder. |

## Ranked live queue after all 100 cells

1. **PPCT-8 injective capstone:** the repeated cone, including its `1/1024` noncircular
   bootstrap and actual-field wiring, is closed.  The sole main analytic task is the signed
   injective packet defect with coefficient `126871`. Equivalently, prove
   `(7!)^2 sum_y(q*a_y-C(n,7))^2 <= 126871*q^2*n^7` for the seven-subset sum histogram.
   Positive completion caps, proper-leaf recursion, generic exterior coupling, and the full
   real-rooted/total-positive sunflower cone are refuted.  Even with every proper depth removed,
   the primitive Wick ray leaves exactly `8264`, or `6.115...%`, to save arithmetically.  The
   sharpest current late coordinate is the centered energy of `U_1-U_2`, with exact numerator
   caps `10500` and `12500`, plus signed tail budgets `21` and `25`.  Internal repetition
   covariance cannot supply this: its correct deletion formula has an injective cross term and
   even a free repeated sector leaves an `8126` gap.  The actual cross term is
   `sum_t W_G(t)R_r(t)`; the next arithmetic theorem must align the shifted cyclotomic-intersection
   row with the adjacent subset-difference row beyond what separate Gram data can see.
2. **CTR-4/5/7:** exploit the exact zero-mean restriction structure on `1-G` without taking
   absolute values and with genuinely production-specific arithmetic.  The orbit-spectral cone
   is exactly dual to the worst-period problem. Galois rationality and moment congruences remove
   the literal spike, but an integral trace-correct profile still misses by 8--9 bits; likewise,
   exact intersection-row integrality and support miss by 25--26 bits.  The new input must couple
   actual ramified conjugates or many intersection values quantitatively at seventh order.
3. **PPCT-8 restricted sparse kernel:** count the support-14, `l1<=14` integer kernel slice at
   either explicit production root. Ordinary BCH/Hamming/Singleton/uncertainty bounds see only a
   distance-two single-check code, and generic fewnomial root bounds miss the subgroup by 116 bits.
   The sharp folded alphabet `{-2,-1,0,1,2}` and its nine local profiles are now formal, but the
   `ZMod 17` countermodel rules out universal kernel-freeness.  Exploit production arithmetic or
   average the restricted slice rather than trying to lower coefficient height further.
4. **PAOR-8 norm-collapse invariant:** accident emptiness is exactly kappa-signature injectivity,
   and its dyadic recurrence, projected character forms, and exact modular table adapters are
   proved.  The finite fallback is `2^29` evaluations (10 GiB at 20 bytes per row); compress that
   state arithmetically or generate and independently verify the certificate.  Generic
   Weil/cyclotomic-number estimates are quantitatively excluded.
5. **AJT-5/6/9 and NWS-6:** retain only off-diagonal or production-specific joint phase structure.
   AJT-3 is the centered moment wall in dual coordinates, while the exact dilation-coloured Newton
   operator shows that all one-colour Schatten data are permutation-blind.
6. **FPTC-5/9/10:** compute monodromy only if it controls the off-diagonal remainder with an
   explicit constant; raw Weil bounds are already known to lose the family cardinality.

The remaining cells are retained as controlled alternates or precise no-go results.  None is a
claim that the Paley graph conjecture or proximity-gap conjecture is solved.
