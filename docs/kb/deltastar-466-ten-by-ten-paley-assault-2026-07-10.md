# Ten-by-ten Paley / proximity assault (2026-07-10)

> **2026-07-11 successor:** the raw depth-seven endpoint used during this wave required a DC
> correction.  For the current exact target, updated literature, quantitative kill tests, and a
> new 100-cell ranking, use
> [`deltastar-466-ten-by-ten-centered-attack-matrix-2026-07-11.md`](deltastar-466-ten-by-ten-centered-attack-matrix-2026-07-11.md).

## Contract

The production core is the nonprincipal Gauss-period maximum

`M(G)=max_{b≠0}|Σ_{x∈G} ψ(bx)|`, `G=μ_(2^30)⊂F_P`,

or equivalently its DC-subtracted energy/census form at logarithmic depth.  A lane counts as a
survivor only if it yields an upper bound on `M`, the required centered moments, or the canonical
worst-case far-line incidence.  A new vocabulary for one of these objects is not a new implication.

Legend: **P** = prove/formalize, **X** = falsify-first experiment, **A** = audit against an existing
no-go.  Each item gives its first decisive action, not a claim that the method works.

## 1. Spectral and operator theory

1. **Ihara--Bass/Hashimoto lift.** Express nonprincipal Paley eigenvalues through a nonbacktracking
   determinant and test whether thin-subgroup tangles have bounded excess. **X:** exact tangle
   census at `n≤512`; fails if the determinant simply recovers `M` coefficientwise.
2. **Signed 2-lifts along the dyadic tower.** Treat `μ_(2n)=μ_n⊔gμ_n` as an arithmetic signed lift.
   **P:** identify the signing matrix; **X:** compare new-eigenvalue norm with MSS interlacing bounds.
3. **Matrix-polynomial recursion.** Replace scalar triangle inequalities by a `2×2` transfer matrix
   retaining cross-phase. **X:** singular-value recursion on exact periods; reject if norm is `2`
   at the worst frequency (Door-IV saturation collision).
4. **Tangle-free trace method.** Separate collision walks into locally tree-like and repeated-edge
   sectors. **P:** map the fully-disjoint census to nonbacktracking walks; target signed puncture
   correction rather than absolute walk counts.
5. **Resolvent/local law.** Seek a deterministic Stieltjes-transform equation for the cyclotomic
   Cayley operator. **X:** compare resolvent fluctuations across cosets; reject a law determined only
   by the known flat spectrum moments.
6. **Pseudospectral stability.** Embed the period vector in a structured nonnormal transfer
   operator whose spectral radius may be smaller than its norm. **A:** prove this operator does not
   have `M` as an exact singular value before investing.
7. **Terwilliger algebra with arithmetic colors.** Refine distance-regular data by dyadic coset
   labels. **P:** compute whether the refined algebra is strictly larger than the rank-three Paley
   algebra; ordinary Terwilliger data is already magnitude-blind.
8. **Quantum variance/QUE.** View multiplicative characters as arithmetic eigenstates and bound
   mass on additive characters. **X:** variance of exact period eigenvectors by conductor strata;
   target an effective sup norm, not averaged QUE.
9. **Interlacing families over coset representatives.** Average characteristic polynomials over
   dyadic half-coset choices. **P:** determine whether the actual subgroup is in the support of a
   real-rooted interlacing family; otherwise this cannot certify the explicit member.
10. **Operator-valued free probability.** Keep the two dyadic halves as amalgamated variables.
    **X:** test mixed free cumulants; reject if antipodal determinism makes the variables maximally
    dependent (the expected collision).

## 2. Additive combinatorics and growth

1. **Asymmetric BSG with a multiplicative side condition.** Large `M` gives a large additive Fourier
   coefficient; extract an additive approximate group still carrying many multiplicative ratios.
   **P:** quantify retention of `G/G=G`, the load-bearing thinness datum.
2. **Weighted BSG without level-set loss.** Apply BSG to period weights rather than threshold sets.
   **P:** formulate a weighted energy increment whose constants survive `r≈log P`.
3. **Higher-order BSG.** Use the full `A_r` excess instead of `E_2`. **X:** search whether a large
   logarithmic-depth moment forces bounded-complexity additive structure rather than a diffuse tail.
4. **Entropy sumset inequality.** Model `X+Y` for uniform `X,Y∈G`; a spike in Fourier space should
   lower entropy. **P:** seek a reverse entropic uncertainty inequality exploiting `XY^{-1}∈G`.
5. **Polynomial Freiman rigidity.** Classify subsets simultaneously low-doubling additively and
   contained in a cyclic multiplicative subgroup. **P:** finite-field quantitative theorem at
   density `P^{-3/4}`; generic PFR alone is far too lossy.
6. **Pivot amplification with phase retention.** Iterate sum-product pivots while carrying the
   complex sign of the offending Fourier coefficient. **X:** symbolic two-step calculation; reject
   if Cauchy--Schwarz erases the phase and returns classical BGK.
7. **Multiplicative derivatives.** Study `1_G(x)1_G(x+t)` as a multiplicative-ratio curve and average
   its additive Fourier transform over `t`. **P:** connect an `L∞` spike to many low-degree curve
   fibers susceptible to Stepanov.
8. **Incidence expansion on `(x,x+1)`.** Use the graph of the shift map inside `G×G` and Rudnev-type
   incidence bounds. **A:** constants/exponents must beat the known `n^{3/2}` energy scale.
9. **Additive energy increment by dyadic shells.** Decompose representation counts by ordered
   coset-profile size; HBK now controls the first 4096 prefixes conditionally. **P:** splice HBK head
   control with a tail entropy inequality.
10. **Approximate-ring obstruction.** Show a Paley spike creates a set approximately closed under
    both addition and multiplication, contradicting field simplicity. **P:** make the extracted set
    large enough and errors small enough; this is the precise quantitative BGK bottleneck.

## 3. Probability, moments, and census theory

1. **Mod-Gaussian convergence at growing order.** Prove cumulants of nonprincipal periods match a
   Gaussian uniformly through `r≈log P`. **P:** express cumulants via connected collision
   hypergraphs and bound each connected species.
2. **Dependency-graph Stein method.** Treat subgroup elements as dependent phases indexed by
   additive relations. **X:** compute dependency neighborhoods; reject if the graph is complete
   because all phases share the same frequency.
3. **Cluster expansion of collision partitions.** Möbius-invert the equality-pattern lattice and
   retain signs. **P:** bound connected clusters by cyclotomic accident counts rather than absolute
   partition counts.
4. **Exchangeable-pair coupling over frequencies.** Couple `b` with `bg`, `g∈G`; this is exactly
   exchangeable on cosets. **A:** the period is invariant under this coupling, so add a transverse
   additive perturbation or declare the naive coupling dead.
5. **Stein coupling over primes/embeddings.** Average conjugate cyclotomic reductions while keeping
   the certified prime as one coordinate. **P:** find a comparison inequality that returns an
   individual coordinate, not only the average.
6. **Martingale over dyadic subgroup halves.** Reveal coset halves and retain conditional phase.
   **X:** measure conditional variance; ordinary bounded-difference gives the known saving-neutral
   telescope, so require negative predictable covariance.
7. **Hypercontractivity on the collision lattice.** Put the centered wraparound indicator on a
   product space of tuple coordinates. **P:** exploit low influence after removing diagonals;
   diagonals must be subtracted before applying Bonami-type estimates.
8. **Log-Sobolev on constrained tuples.** Run a swap chain on fully-disjoint tuples with fixed sum.
   **P:** prove rapid mixing plus small observable Lipschitz norm; target the G133 census family.
9. **Saddle-point/local limit theorem.** Use the exact lattice-theta MGF but isolate nonzero residue
   classes. **P:** a uniform minor-arc estimate is required; a saddle calculation alone is the known
   phase-blind no-go.
10. **Moment SDP with signed puncture variables.** Optimize G133's puncture correction under all
    exact low-rung identities. **X:** finite SDP at `n≤128`; survivor only if its dual suggests a
    scalable inequality not equivalent to assuming the desired high moment.

## 4. Cyclotomic integers, norms, and resultants

1. **Bounded-height accident exclusion.** A surplus low-rung collision means the certified prime
   divides a nonzero short cyclotomic sum. **P:** exact accident law for each anchor `r≤10`.
2. **Subresultant ladder.** Encode `r(c)` by `gcd(X^n-1,(c-X)^n-1)` and bound aggregate subresultant
   valuations. **P:** replace an impossible single resultant bound by a moment of gcd degrees.
3. **Mann packet classification modulo a prime ideal.** Classify short relations into lawful
   antipodal packets plus prime-ideal accidents. **P:** extend the four-term dyadic classification
   to `2r≤20`.
4. **Galois-orbit divisibility amplification.** If one prime ideal divides a relation, study all
   conjugates and the rational norm. **A:** norm height is exponential; need orbit sparsity or local
   incompatibility, not the crude norm bound.
5. **Discriminant avoidance.** Show the certified prime avoids discriminants controlling new gcd
   multiplicities. **X:** compute discriminant valuations for small dyadic levels and extrapolate a
   recursive formula.
6. **Sparse multivariate resultant.** Use Newton polytopes of collision systems rather than dense
   degree. **P:** establish a mixed-volume height bound subexponential in `n`; degree-only bounds do
   not solve prime divisibility.
7. **Ideal-lattice minimum with support constraints.** Restrict the cyclotomic ideal lattice to
   `2r`-sparse coefficient vectors. **P:** lower-bound the norm of nonzero sparse vectors strongly
   enough to exceed the certified prime.
8. **Stickelberger annihilator congruences.** Test whether the special prime and dyadic conductor
   force valuations of short sums into forbidden classes. **X:** exact local valuation census for
   `n≤256`.
9. **Local-global short-relation principle.** Prove absence modulo several auxiliary split primes
   forces absence modulo the certified prime for the bounded support class. **A:** requires a real
   rigidity theorem; CRT sampling by itself has no implication.
10. **Cyclotomic-unit factorization.** Factor collision determinants into cyclotomic units and a
    small exceptional factor. **X:** symbolic factorization of anchor determinants; survivor if the
    exceptional factor has polynomial rather than exponential height.

## 5. p-adic analysis and arithmetic dynamics

1. **Gross--Koblitz phase expansion.** Express Gauss periods through `Γ_p` and seek cancellation
   between multiplicative characters. **P:** retain character-dependent unit phases; valuation-only
   bounds are already known to be useless.
2. **Dwork trace operator.** Realize the period as a trace of a nuclear operator whose non-unit-root
   spectrum contracts. **P:** identify a rank independent of `n`; conductor `≈n` reproduces Weil.
3. **p-adic stationary phase on the subgroup parameter.** Parameterize `G` by powers of a generator
   and analyze `ψ(bg^j)`. **A:** the phase has huge p-adic period; prove a nondegenerate derivative
   range before invoking stationary phase.
4. **Unit-root F-crystal slope gap.** Seek a slope gap special to `2`-power monodromy. **X:** compute
   Newton polygons of small conductor Gauss-period L-functions.
5. **Iwasawa measure across the dyadic tower.** Package half-period differences as moments of one
   measure. **P:** a nontrivial μ-invariant bound must depend on frequency; b-independent Amice norms
   collide with the existing no-go.
6. **Mahler coefficient cancellation.** Expand `j↦ψ(bg^j)` in the binomial basis. **X:** exact
   coefficient decay; reject if coefficients are units up to the conductor.
7. **Hensel stratification of collision varieties.** Count mod-p collisions by lifting from
   characteristic zero and classify singular strata. **P:** anchors first, then connected clusters.
8. **p-adic decoupling.** Treat short arcs of the exponential orbit as p-adic curved pieces.
   **A:** obtain a scale smaller than the subgroup length; otherwise decoupling is vacuous.
9. **Perfectoid tilt comparison.** Compare the dyadic tower with a characteristic-two tilt where
   Frobenius is simple. **P:** construct a trace-compatible observable; cardinality comparison alone
   cannot transport complex cancellation.
10. **Newton polygon of the period minimal polynomial.** Relate a large complex conjugate to p-adic
    slopes via the product formula. **A:** one large archimedean conjugate can be hidden by others;
    need a height distribution theorem, not a single norm.

## 6. Algebraic geometry, sheaves, and monodromy

1. **Family monodromy over the coset parameter.** Build the trace sheaf whose fibers are periods
   and prove large geometric monodromy. **P:** derive an effective *vertical* maximum bound, stronger
   than equidistribution over varying primes.
2. **Conductor compression by quotient stack.** Quotient the Kummer sheaf by the dyadic subgroup
   action. **P:** show conductor drops to `polylog n`; if it remains `Θ(n)`, Deligne gives only Weil.
3. **Tensor-power invariants.** Interpret `A_r` as Frobenius traces on tensor powers and classify
   invariant subspaces. **P:** lawful Wick pairings should be the only invariants through logarithmic
   depth; extra invariants are the exact wall.
4. **Geometric irreducibility of collision strata.** Separate diagonal components from the
   fully-disjoint sum-equality variety. **P:** bound component count/Betti numbers uniformly in r.
5. **Stratified Fourier transform.** Fourier-transform the punctured incidence variety stratum by
   stratum, retaining alternating signs. **P:** target G133's signed puncture correction.
6. **Tannakian independence of dyadic layers.** Prove successive Kummer layers have product
   monodromy after removing antipodal invariants. **X:** small-conductor monodromy computation.
7. **Vanishing-cycle control at collision diagonals.** Show all excess cohomology is supported on
   known matching strata. **P:** a decomposition theorem yielding exactly the census recurrence.
8. **Lang--Weil exceptional-locus bound.** Parameter values with anomalously many representations
   lie in a low-degree exceptional set. **A:** must bound the degree below the number of cosets; a
   degree `Θ(n)` exceptional polynomial is vacuous.
9. **Arithmetic fundamental-group expansion.** Treat periods as matrix coefficients of Frobenius in
   a monodromy group with expansion. **P:** effective expansion in the fixed-prime vertical family.
10. **Derived cancellation/signed Euler characteristic.** Use cohomological signs rather than total
    Betti numbers to bound centered counts. **X:** exact point counts and Euler factors for small r;
    reject if absolute-value Deligne is unavoidable.

## 7. Coding theory, syzygies, and incidence geometry

1. **Guarded predecessor count.** Quotient out the now-formal three-subset syzygy channel before
   counting bad scalars. **P:** define the guard and prove it still controls the canonical prize
   failure event.
2. **Distinct witness-codeword count.** Replace scalar count by distinct decoded witnesses to avoid
   pencils donating many scalars. **P:** establish the correct injection into a list-decoding object.
3. **Syzygy module classification.** Compute all low-rank relations among GRS restriction matrices.
   **P:** prove every persistent rank defect is generated by degenerate subset pencils.
4. **Matroid circuit growth.** View bad witness subsets as circuits of a represented matroid.
   **X:** circuit-overlap census; target an expansion theorem after contracting syzygy circuits.
5. **Secant-variety defectivity.** Bad stacks correspond to secants of a rational normal curve with
   unexpected intersection. **P:** classify defective secants at the production codimension.
6. **Tensor-rank flattenings.** Encode simultaneous witness conditions in a structured tensor.
   **X:** test whether higher flattenings detect exactly the rank defects missed by matrices.
7. **Subspace-design projection.** Use explicit subspace designs to kill common degeneracy while
   preserving the RS domain. **A:** changing the code/domain does not prove the original prize;
   only an internal projection with a reverse implication counts.
8. **List-recovery rather than list-decoding.** Each coordinate supplies a short affine list from
   the pencil. **P:** instantiate a sharp RS list-recovery theorem at the actual alphabet/list sizes.
9. **Polynomial-partition incidence bound.** Treat `(γ,S,p)` witnesses as points/varieties and
   partition by syndrome rank. **P:** isolate high-rank cells where one γ per S is truly useful.
10. **Puncture-and-lift induction.** Remove coordinates supporting syzygies, prove a guarded bound,
    then lift with an exact charge. **X:** check whether the charge telescopes below the prize budget.

## 8. Convex optimization, information theory, and dual certificates

1. **Thin-aware Delsarte LP.** Add multiplicative-subgroup orbit constraints to the usual Cayley
   graph LP. **P:** exhibit a constraint not determined by the known spectrum; ordinary LP is dead.
2. **Terwilliger/flag SDP with arithmetic labels.** Optimize local triple distributions refined by
   dyadic cosets. **X:** finite exact SDP and rational dual certificate at `n≤64`.
3. **Moment-SOS for period phases.** Variables are all coset periods with exact Parseval and product
   identities. **X:** determine the SOS degree needed to beat `n`; bounded degree is expected to hit
   the bounded-complexity no-go.
4. **Entropy duality.** Minimize entropy of the additive convolution subject to multiplicative
   support. **P:** derive a dual polynomial whose evaluation is a certified sup bound.
5. **Optimal transport on frequency cosets.** Couple the empirical period distribution to a Gaussian
   law. **A:** Wasserstein control does not imply `L∞`; require a transport-entropy inequality with a
   sharp tail constant.
6. **Vector discrepancy of subgroup phases.** Choose signs from dyadic halves to balance every
   frequency simultaneously. **P:** the actual signs are fixed; need an interlacing argument placing
   the arithmetic signing among good signings.
7. **Noncommutative Khintchine with deterministic correction.** Lift phases to matrices encoding
   collision dependencies. **P:** correction norm must be computed and smaller than the variance.
8. **Maximum-entropy completion of moments.** Fit the unique distribution with known moments and
   bound its support. **A:** truncated moments never control support without a determinacy margin;
   quantify rather than assume it.
9. **Invariant flag algebra.** Encode collision patterns as flags with subgroup identities.
   **X:** finite SDP for r≤10; survivor if a dual inequality extrapolates through r=110.
10. **Computer-discovered rational dual certificates.** Search exact inequalities combining anchor
    moments and census recurrences. **P:** replay certificates in Lean; reject certificates whose
    coefficients grow exponentially or assume the target moment.

## 9. Dynamics, transfer operators, and integrable systems

1. **Jacobi/Toda turnover with arithmetic gauge fixing.** The isospectral invariants alone cannot
   recover the turnover. **P:** add a canonical cyclotomic phase gauge and test if it controls the
   maximal recurrence coefficient.
2. **Ruelle transfer operator for multiplication by 2.** Encode dyadic exponent digits and additive
   phases. **P:** prove a spectral gap uniform in the 158-bit modulus.
3. **Arithmetic cocycle Lyapunov exponent.** Products of `2×2` half-period transfer matrices may
   contract typically. **X:** worst-coset Lyapunov spectrum; average contraction is insufficient.
4. **Renormalization fixed point.** Normalize period distributions at each dyadic level and seek a
   Gaussian fixed point with stable basin. **P:** a deterministic basin theorem including the
   certified initial condition.
5. **Wavelet-packet cancellation.** Haar-decompose the subgroup indicator along the dyadic tower.
   **X:** locate energy across packets; target an `L1→L∞` improvement from phase oscillation.
6. **Multiplicative cascade with signed weights.** Model half-period splits as a dependent cascade.
   **A:** establish decorrelation; naive cascade independence contradicts exact antipodal relations.
7. **Quantum cat-map analogy.** Relate subgroup orbits to eigenstates of an arithmetic map and use
   entropy bounds. **P:** construct an exact unitary conjugacy, not a metaphor.
8. **Arithmetic QUE in a fixed finite field.** Vary frequency within the fixed coset quotient and
   seek effective equidistribution. **P:** upgrade mean equidistribution to a maximum via a large
   sieve with thin-family constants.
9. **Scattering/resonance formulation.** Periods as reflection coefficients of a finite Jacobi
   operator. **X:** check whether resonances encode more than the already-known spectrum.
10. **Thermodynamic pressure of collision words.** Assign pressure to matching/nonmatching tuple
    patterns. **P:** show pressure below the Wick budget after DC subtraction; absolute pattern
    pressure is known to be too large.

## 10. Computational mathematics and proof-producing discovery

1. **Exact FFT anchor census.** Compute anchors `r≤10` at `n=128,256,512` across matched-regime
   primes to map exceptional-prime behavior. **P:** emit checkable integer certificates.
2. **Sparse convolution for production subquotients.** Project the certified subgroup to quotient
   rings/characters and test necessary inequalities. **A:** projection must preserve a one-way
   implication to the original maximum.
3. **SAT/SMT collision-pattern search.** Search abstract equality patterns satisfying all lawful
   constraints but violating census budgets. **P:** either emit a finite countermodel or an UNSAT
   certificate replayable in Lean.
4. **Symbolic recurrence mining.** Guess exact recurrences for anchor accident counts from small
   dyadic levels. **P:** prove candidates by cyclotomic tower induction.
5. **LLL short-relation search.** Find sparse cyclotomic relations whose norms contain the certified
   prime. **X:** support≤20 at progressively larger dyadic conductors; a hit refutes an anchor.
6. **Resultant-prime census.** Factor sparse collision resultants at small levels and study residue
   statistics of exceptional primes. **X:** test the predicted probability and structured-prime bias.
7. **Proof-producing NTT moment computation.** Use modular convolution plus CRT bounds to certify
   exact energies without trusting floating FFT. **P:** checker in Lean or a tiny audited kernel.
8. **Active-learning conjecture synthesis.** Train only to propose invariant inequalities, then
   adversarially test on all stored countermodels. **A:** no learned statement enters the ledger
   without a symbolic proof or explicit residual label.
9. **Automated literature-to-Lean transcription.** Extract exact hypotheses/constants from BGK,
   Shkredov, HBK, and modern Paley papers. **P:** instantiate at production and kernel-check whether
   any bound is nonvacuous.
10. **Portfolio scheduler with kill criteria.** Maintain machine-readable dependencies, expected
    exponent gain, and falsifier for all 100 cells. **P:** automatically retire a cell when it
    factors through a recorded no-go or fails its decisive probe.

## Cross-lane synthesis and initial ranking

The most credible near-term theorem targets are:

1. HBK head-profile auxiliaries (`2.9` + the already formalized 4096-prefix reduction).
2. Short cyclotomic accident classification for production anchors (`4.1`--`4.3`).
3. Connected collision/cluster bounds feeding the G133 signed puncture correction (`3.1`, `3.3`,
   `6.3`, `6.5`).
4. Syzygy-module classification and a guarded incidence consumer (`7.1`--`7.3`).
5. Proof-producing exact anchor computation (`10.1`, `10.7`) to kill or prioritize the per-prime
   anchor hypotheses before deeper formalization.

Every other cell remains in the portfolio, but it must pass its stated first test before receiving a
large formalization budget.

## Post-wave result ledger

The first parallel wave did not prove the Paley or proximity-gap conjecture.  It did separate one
production theorem, three narrower structural survivors, and several exact method-class
obstructions.  “Negative” below means that the stated mechanism was actually falsified or fenced;
it does not mean that the surrounding mathematical field is irrelevant.

| Field | Strongest result from this wave | Honest status |
|---|---|---|
| Spectral/operator | The first exact G133 support-bucket tests have same-sign puncture corrections, so regrouping supports supplies no hidden cancellation there. | Finite falsifier for the proposed regrouping, not a general spectral theorem. |
| Additive combinatorics | The HBK auxiliary-polynomial chain now gives `E(mu_(2^30))^2 <= 128*(2^30)^5` at both certified primes. | **Production theorem.** It closes the depth-four/HBK input, not the logarithmic-depth Paley maximum. |
| Probability/census | Exact orbit-compressed censuses locate the first fully-disjoint mass at small matched-regime cells and distinguish characteristic-zero from prime-field excess. | Proof-producing calibration; it exposes rather than closes the high-depth sector. |
| Cyclotomic/norm | Rung-two accidents are stable under an order-four re-rooting action, hence occur in packets of at least four; `#accidents <= 3` is exactly accident-freeness.  A triple-equal signed packet forces `-3` into the subgroup, and exact certificates exclude that stratum at both prize primes. | Axiom-clean sharpening of G136.  Full production accident-freeness is still unproved; the remaining expected projective orbit sizes are 12 and 24. |
| p-adic | Valuation, Newton-polygon, and dyadic-tower formulations still fail to return an individual complex embedding; no tested slope statement controls the maximum. | No production survivor without a new archimedean-distribution bridge. |
| Geometry/sheaves | Tensor invariants and connected collision strata identify the right object, but conductor grows with the subgroup order and ordinary Deligne bounds revert to Weil. | The live geometric target is logarithmic-depth connected-stratum control with vertical, fixed-prime constants. |
| Coding/syzygy | A nonzero divided-difference kernel pair has at most one critical external-anchor channel.  Raw scalar-to-decoded-codeword injection is explicitly false. | Useful guarded rigidity rung; the event-level charge/extraction theorem remains open. |
| Convex/information | Every positive matching-moment row vanishes on the fully-disjoint coordinate; their common nonnegative recession cone is exactly that ray. | Exact LP/SOS/entropy method-class no-go unless a new arithmetic row sees full depth. |
| Dynamics/transfer | Both unweighted and unit-phase dyadic sibling transfers have norm-preserving right inverses and centered fixed modes. | Exact unrestricted-contraction no-go; only arithmetic range avoidance can survive. |
| Proof-producing computation | Exact integer probes and SHA-pinned outputs certify the small-cell onset and orbit expansion. | Discovery/certificate infrastructure, not an extrapolation theorem. |

The HBK chain received an independent line-by-line audit.  It matches the coefficient and
constraint counts of HBK Lemma 5, validates the triangular conversion from iterates of
`X(X-1)d/dX` to ordinary multiplicity, checks the Lemma 6 nonvanishing conditions, and exhaustively
checks all `1 <= k <= 4096` production prefixes.  It also passed 2,514 admissible small-prime test
instances.  Direct per-file checks of both prize-prime endpoints report only the standard Lean
axioms and no `sorryAx`.  A serialized landing build is still pending because another shared build
owns the repository lock.

## New synthesis: the Moebius--Mann full-depth calculus

The ten fields point to one common object.  Turn an equal-sum pair

`x_1+...+x_r = y_1+...+y_r`

into the signed zero-sum word

`x_1,...,x_r,-y_1,...,-y_r` in `G`.

Because `-1` lies in the dyadic subgroup, this remains a word in `G`.  Ordinary Wick terms are the
two-letter zero-sum packets.  The fully-disjoint G133 sector is precisely the part with no
left--right two-letter packet.  The genuinely arithmetic objects are therefore the primitive
zero-sum packets of lengths `3,...,2r`, together with the ways they intersect and assemble.

This suggests a concrete theory rather than another analogy:

1. **Moebius layer.**  Invert the partition lattice of the `2r` signed positions.  Pair blocks give
   the Wick main term; connected non-pair blocks define arithmetic cumulants.
2. **Mann layer.**  Classify short primitive blocks up to projective re-rooting and permutation.
   ANT46 is the first nontrivial orbit law in this layer, and its production certificates eliminate
   the only triple-equal/size-four projective stratum at both certified primes.
3. **HBK layer.**  Bound the aggregate supply of short blocks by auxiliary-polynomial incidence
   estimates.  The new coefficient-128 theorem provides the first production-scale input.
4. **Intersection layer.**  Charge overlaps of primitive blocks by the G143--G145 intersection
   multiplicities or by guarded divided-difference syzygies.
5. **Full-depth layer.**  Prove that the exponential generating function of connected blocks stays
   below the Wick budget through `r=110`; this is exactly the missing implication to the Paley
   maximum rather than a reformulation in moment language.

The associated falsifier is sharp.  Any proposed invariant should be evaluated on the pure
full-depth basis vector before further work.  If its coefficient is zero, CXI01 puts it in the
overlap-blind cone.  If its dyadic evolution is an unrestricted sibling average, DYN09 supplies a
norm-preserving obstruction.  If it merely partitions the puncture correction by support, SAC01's
same-sign cells show why no cancellation appears.  A surviving invariant must instead be nonzero
on primitive disjoint packets, annihilate lawful pairings, and admit an arithmetic bound independent
of the unknown top moment.

The next formal theorem target is consequently a **connected-packet expansion** for the G133
census, followed by the full `S_4` orbit-card theorem and classification of the exact `720n`
depth-three onset family.  That target composes the strongest positive outputs of the wave; it is
also honest about the wall: no bound for connected packet sizes through `220` has yet been proved.
