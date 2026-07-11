# #466 — BGK moment tower + production depth-five welds (2026-07-10)

**Session goal:** "prove BGK". Honest outcome: BGK (`WorstCaseIncompleteSumBound`, the
~25-year-open generalized-Paley-graph sup-bound) is **not** discharged — it cannot be, short of
resolving the open conjecture. What landed instead is the complete formal reduction making the
depth ladder hang off that single named Prop, end to end at the literal prize numbers.

## Landed (all axiom-clean: `propext, Classical.choice, Quot.sound`; real `lake build`)

1. `Frontier/_BGKSupBoundMomentTower.lean` (commit `f5c554cb5`)
   - `offZero_secondMoment`: exact off-zero Parseval `∑_{b≠0}‖η_b‖² = q|G| − |G|²`.
   - `etaMomentTower_of_worstCase`: **the tower** — for every `r ≥ 1`,
     `∑_{b≠0}‖η_b‖^{2r} ≤ M^{r−1}(q|G| − |G|²)`; relaxed form and the `r = 5` tenth-moment
     corollary. One chaining step (`x^r ≤ M^{r−1}x` on `0 ≤ x ≤ M`) + the exact base case.

2. `Frontier/_BGKDepthREnergyLaw.lean` (commit `f5c554cb5`)
   - `moment_eq_card_energy`: **exact depth-`r` Parseval/energy law**
     `∑_b‖η_b‖^{2r} = q·E_r(G)` with `E_r` = ordered `r`-tuple sum-collision census
     (`rEnergy`). Unconditional, pure orthogonality; proved via `Finset.sum_pow'` +
     an inline `addChar_map_sum`. Generalizes the in-tree depth-2 `addEnergy` identity to all
     depths at once.
   - `rEnergy_le_of_worstCase`: the dossier §8 independence form as a theorem modulo BGK:
     `q·E_r ≤ |G|^{2r} + M^{r−1}·q·|G|` for every `r ≥ 1`.

3. `Frontier/_BGKProductionDepthFiveWeld.lean` (commit `9b692408d`)
   - `rEnergy_le_production_ceiling` / `bgk_production_depthFive_weld`: at the literal prize
     instance (`|G| = 2³⁰`, `q ≥ 2¹⁵⁸`; `productionQ_ge` checks the prize field), ANY BGK
     sup-bound `M ≤ 2⁴⁰` (round-30 scale `C·n·log n ≈ 2³⁵`) forces
     `E₅ ≤ 2²³⁵ = productionCollisionCeiling`, hence composed with the kernel-checked G112
     arithmetic `E₅·productionDepthFiveBase ≤ productionWick`. Margin:
     `E₅ ≤ 2¹⁴² + 2¹⁹⁰ ≪ 2²³⁵` (≥ 45 bits of headroom).

4. `Frontier/_BGKInjectiveFiveWeld.lean`
   - `injEnergy_le_rEnergy`: the injective five-tuple census (the ACTUAL G112 production map,
     `productionSource = n.descFactorial 5`) embeds in the ordered energy (pure monotonicity).
   - `bgk_production_injective_weld`: the production envelope transfers to the injective map,
     same hypotheses, same single open input.

## Upshot for the campaign map

The G86/G111/G112 depth-five production socket and, more generally, EVERY finite-depth moment
rung is now formally exactly ONE named inequality away from closed: prove
`WorstCaseIncompleteSumBound ψ G M` at any `M ≤ 2⁴⁰` on the prize subgroup and the depth-five
Wick envelope (both ordered and injective censuses) follows by landed theorems. The converse
caution from `_PrizeFloorOfBGK.lean` stands: the sup-bound feeds the energy/moment lane; the
far-line incidence input (BCHKS 1.12 hyperplane upgrade) remains the second, independent open
input for the δ* floor itself.

## Lean gotchas (recorded for reuse)

- `exponentiation.threshold` defaults to 256: `norm_num` will NOT evaluate `2^300`; raise via
  `set_option exponentiation.threshold 512` (plus `maxRecDepth 8192`) or restructure with
  `pow_mul`/`pow_add`.
- `add_le_add_right h _` can mis-unify on ℝ sums of pow-atoms; `add_le_add h le_rfl` is robust.
- Frontier files importing other Frontier files need the imported module's olean:
  `lake-locked.sh build <Module>` once; `pg-iterate.sh` alone fails on a missing olean.
- The build lock can queue ≥10 min behind concurrent agents; run locked builds in background.

## Addendum 2026-07-11: depth-9 threshold + Wick probe + instance ladder

- `_BGKDepthNineThreshold.lean` (4fb1e30a7): depth-≤7 moment certificates provably cannot
  reach M ≤ 2⁵¹ (diagonal floor); depth-9 Wick `E₉ ≤ 17‼·n⁹` at q ≤ 2¹⁵⁹ closes the lane —
  sup-bound Prop ELIMINATED in favor of this one counting inequality.
- `_BGKProvenInstanceFullGroup.lean` (d2d0abe33): FIRST discharged instance of the Prop
  (index 1, M = 1 exact, Ramanujan). `_BGKConstIndexMomentTower.lean` (986122aad): composed
  with the in-tree Gauss-period discharge — unconditional every-depth tower/energy law for ALL
  constant-index subgroups. Ladder: index 1 + constant index PROVEN; prize index 2¹²⁸ open
  (Gauss-period route floors at √q = 2⁷⁹ ≫ 2²⁵·⁵ — can never reach the prize regime).
- **Wick-ratio probe** (`probe_bgk_depth9_wick_ratio.py`): E₉/(17‼·n⁹) at small scale:
  ratio ≈ 3973 at (n=32, p=257) — exact Wick FAILS shallow (echoes the depth-3 refutation) —
  but decays with p/n²: n=16 crosses 1 at p/n² ≈ 8 (0.31 at p/n² = 30); n=32: 83 → 38 → 23
  at p/n² = 12/26/64. Prize regime p/n² = 2⁹⁸: numerics support truth; excess grows with n at
  fixed p/n², which IS the certification difficulty. The weld tolerates ratio ≤ 32.

## Addendum 2: exponent comparison + terminal state (2026-07-11)

Landed after the first addendum: coset amplification (`_BGKCosetAmplification.lean`, threshold
9→7), the depth-6 amplified no-go (`_BGKDepthSixAmplifiedNoGo.lean`, threshold EXACTLY 7), and
the consolidated residual `DepthSevenFlatnessResidual` (`_BGKDepthSevenFlatnessResidual.lean`)
with both consumers proven.  **This raw interface is subsequently refuted and corrected in
Addendum 3 below.**

**Exponent ladder for `M(n) = max‖η_b‖`, `n = 2³⁰` (δ in `M ≤ n^{1−δ}`):**
- trivial: δ = 0 (`M = n`).
- published SOTA (BGK/di Benedetto): δ ≈ 0.011 — machine-checked INSUFFICIENT for the prize
  (`_BGKSOTAInsufficiency.lean`) AND out of regime (valid `n ≳ q^{1/4}`; prize `n = q^{0.19}`).
- **the depth-five lane's nine-bit target (this session): δ = 0.15** (`M ≤ n^{0.85} = 2²⁵·⁵`)
  was originally routed through the raw `DepthSevenFlatnessResidual`; the valid route is the
  DC-subtracted successor in Addendum 3 — 14× the published exponent, 3.3× less than Paley.
- full prize floor: δ = 1/2 − o(1) (Paley-graph conjecture scale).

**Terminal state of the goal "prove BGK":** the condition requires cancellation exponents
(0.15 for the lane, 0.5 for the prize) in a regime (`n = q^{0.19}`) where the entire published
literature — not merely the formalized subset — provides none. Machine-checked in-tree: SOTA
insufficiency + regime exclusion. No agent session can honestly discharge it; the residual is
the sharp, fully-consumed, numerically-supported handoff point.

## Addendum 3: mandatory DC correction (2026-07-11)

The raw `DepthSevenFlatnessResidual` in Addendum 2 is **REFUTED**.  It bounded the full energy
`E_7`, but the zero frequency contributes `n^14` to `q E_7`.  At `n=2^30`, `q≤2^159`:

```text
DC floor:          2^420 = n^14 ≤ q E_7
raw proposed cap:  q E_7 ≤ 2^159 · 2^18 · 2^210 = 2^387.
```

The contradiction is formalized in `_BGKDepthSevenFlatnessResidualRefuted.lean`; the historical
raw file is retained only because its conditional implications are logically valid.

The corrected live residual is

```text
q E_7 - n^14 ≤ q · 2^18 · n^7,
```

equivalently an off-zero fourteenth-moment bound.  This gives the exact coset-amplification budget

```text
Σ_{b≠0}|eta_b|^14 ≤ n · (2^51)^7 = 2^387,
```

and the new file proves both the `WorstCaseIncompleteSumBound` and production depth-five consumers.
The coefficient `2^18` is `1.9399...` times the Gaussian constant `13!!=135135`; the correction
therefore preserves the intended factor-two cushion while restoring the mandatory DC baseline.
At the exact production cardinality the largest integral coefficient permitted by the numeric
budget is `2^19-1`, but `2^18` is the uniform power-of-two coefficient under only `q≤2^159`.

`_BGKRenergyRepresentationBridge.lean` closes a separate representation seam exposed by the audit:
the BGK lane and the older census library used extensionally equal but non-definitionally-equal
`rEnergy` definitions.  The bridge proves equality unconditionally and shows that the standard
depth-seven `DCEnergyBound` (coefficient `13!!`) implies the repaired BGK residual (coefficient
`2^18`).  Consequently G121--G145-style census work and the BGK consumer now target the same exact
centered quantity.

The live BGK gate remains genuine: prove the **centered** depth-seven flatness residual, not the
impossible raw-energy statement.

## Addendum 4: exact centered convolution collapse (2026-07-11)

`_BGKCenteredConvolutionCollapse.lean` rewrites the corrected residual without characters or
division.  For the ordered `r`-fold representation count `f_r` and its autocorrelation
`C_r(delta)=sum_d f_r(d)f_r(d+delta)`, it proves

```text
q E_(r+1) - n^(2r+2)
  = sum_(s,t in G) (q C_r(s-t) - n^(2r))
  = n * sum_(u in G) (q C_r(1-u) - n^(2r)).
```

The second equality uses the multiplicative-subgroup dilation symmetry and the reindexing
`t=s*u`.  At `r=6`, this is exactly the repaired depth-seven numerator.  Consequently the
coefficient-`2^18` residual is equivalent to

```text
n * sum_(u in G) (q C_6(1-u) - n^12) <= q * 2^18 * n^7.
```

At the production parameters `n=2^30`, `q<=2^159`, division by `n` gives the explicit
one-dimensional budget `2^357`.  The file also proves
`sum_delta (q C_r(delta)-n^(2r))=0`: this is a zero-global-mean signed discrepancy.  It explains
why the positive FS11/primitive-packet census can supply useful structure yet cannot by itself
close the repaired residual; a closing argument must preserve cancellation along `1-G`.

For honesty, the same file proves the Fourier-side audit

```text
n * sum_(u in G) (q C_6(1-u)-n^12) = sum_(b != 0) |eta_b|^14.
```

Hence the individual translate terms are signed but their whole sum is nonnegative.  This is an
exact lower-dimensional face of the off-zero fourteenth moment, not an aggregate-method escape.

## Addendum 5: projective accident packet classifier (2026-07-11)

`_ANT46RungTwoAccidentOrbit.lean` now proves the full `S_4` re-rooting classifier after closing a
scalar-symmetry seam that is false for arbitrary zero-sum quadruples.  Under the accident and
odd-characteristic hypotheses, any nontrivial common scalar would force a signed coordinate to be
`1`, hence a lawful Mann family.  The projective identity fibre therefore has size exactly
`1`, `2`, or `6`, according to the signed-coordinate equality partition.

The `2+2` pattern is lawful.  At both certified production primes the existing `-3` certificate
also excludes the `3+1` pattern.  Consequently every production accident orbit has size `24` or
`12`, and the total accident count is divisible by `12`.  This sharpens the old packet-of-four
result but does not establish emptiness; any independent production upper bound `<12` would now
close the rung-two accident residual.

The exact residual is now one-dimensional.  Put `kappa_n(x)=(x-1)^n` on nontrivial `n`-th roots.
The file proves

```text
accidents H = empty  <->  kappa_n is injective modulo x ~ x^(-1),
#accidents = sum_v (k_v^2 - 2*k_v + s_v) = sum_v k_v^2 - 2*n + 3,
```

where `k_v` is a signature-fibre size and `s_v` records the unique self-inverse root.  The
small-prime probe independently matches this formula against direct triples at 409 bad cells and
refutes `p>n^3` as a cleanliness criterion.  For production, a sufficient exact certificate is
`P_i` not dividing `Disc(K_n)*K_n(2^n)`, with `deg K_n=2^29-1`; direct construction is infeasible,
so the new live PAOR socket is a logarithmic dyadic resultant/discriminant recurrence.

That recurrence is now exact.  `_ANT46KappaDyadicRecurrence.lean` proves

```text
K_(2n)(T) = Sq(K_n)(T) * J_(2n)(T),
J_(2n)(T) = Res_u(R_n(u), T^2 + A_n(u)T + (u-2)^n),
R_(2n)(u) = R_n(u^2-2).
```

The probe verifies the resultants and `Disc(K_n)K_n(2^n)` bad-prime criterion through `K_32`.
It refutes square-only and recycled-`K_n` scalar recurrences.  The honest production boundary is
that the exact 28-level trace circuit still feeds a norm of width `2^28`; a new norm-collapse
invariant could still yield a succinct certificate, so this is a state-specific no-go rather than
a general impossibility theorem.

## Addendum 6: weighted collision moments and Jacobi equivalence (2026-07-11)

`_BGKWeightedCollisionMoment.lean` proves the coefficient-weighted master identity

```text
sum_b (prod_i eta_(c_i b)) (prod_j eta_(-d_j b))
  = q * weightedCollisionCount(G,c,d),
```

and its nonzero-frequency/DC-subtracted form. The first set-partition stratum with one repeated
left coordinate is therefore represented exactly by

```text
sum_(b != 0) eta_(2b) * eta_b^5 * eta_(-b)^7
  = q * oneRepeatCollisionCount - n^13.
```

This is the current signed socket for the repeated-coordinate part of the primitive-packet
decomposition. It preserves the DC cancellation that a positive collision envelope loses.

`_BGKRepeatedSectorNewtonAbsorption.lean` completes the exact partition ledger.  For
`D_7=7!e_7`, Newton inversion gives

```text
p_1^14-D_7^2 = 42*p_2*p_1^12 - 651*p_2^2*p_1^10
                 - 140*p_3*p_1^11 + lower-factor terms.
```

The absolute coefficient masses by factor count start `B_13=42`, `B_12=791` and total
`25,401,599`.  At `n=2^30`, generalized 14-Hölder evaluates to `137.8488...<138`; the exact
bootstrap reserves `138` units for repeated strata and leaves `126871` for the signed injective
packet defect.  The file proves the arithmetic, Newton identity, DC bridge, and noncircular
secant barrier.  `_BGKFourteenFactorYoung.lean` proves the underlying fourteen-factor AM--GM and
optimized-padding lemma. `_BGKShiftedEtaPaddedHolder.lean` additionally proves the exact
nonzero-frequency dilation law, handles all coefficient shifts `1,...,7`, constructs the
canonical NNReal padding scale even when the moment vanishes, and supplies a witness-free Holder
bound for every `k<=13` Newton monomial. `_BGKRepeatedNewtonFullEnumeration.lean` now checks all
88 nonzero monomials by `ring`, computes the complete `B_k` table in the kernel, and wires every
term to that Holder bound.  Fixed integer padding `R=79880` then proves the exact fixed-target
estimate `F(T)<=138*q*n^7` using rational arithmetic.  The finite enumeration, dilation, Holder,
and scalar seams are closed.  At that fixed-target stage, the only bootstrap interface was the
already-isolated above-target concave secant inequality with slope `1/1024`.

`_BGKRepeatedEnvelopeSecantClosure.lean` now closes that last interface and the actual-field
wiring.  It proves the canonical padding envelope equals the literal twelve-stratum rpow
envelope, derives the `1/1024` secant from concavity, transports the fixed `R=79880` certificate
to `H(T)<=138*S`, and exposes one final consumer:

```text
productionSlackBarrier_of_actualEtaEnvelope
```

Given `M14=135135*S+total`, `total<=injective+repeatedEtaEnvelope`, and
`injective<=126871*S`, it proves `total<=127009*S`.  These are exactly the intended moment
decomposition, recurrence, and injective allocation inputs.  No repeated-sector enumeration,
dilation, scalar, monotonicity, secant, or field-wiring residual remains.

`_AJT13CenteredMomentEquivalence.lean` records a complementary no-shortcut result. If `K` is
the annihilator of `G`, `m=|K|`, and `eta_c` are the quotient Gauss periods, complete character
orthogonality gives

```text
S13(K) = (m^13/q^7) * sum_c (eta_c + 1/m)^14.
```

Thus `S13 <= C*m^7*((q-1)/q)^6` is equivalent to the centered physical bound
`sum_c(eta_c+1/m)^14 <= C*q*n^6`. Jacobi tensorization remains a useful coordinate system for
off-diagonal structure, but the bare `m^7` statement is the original centered wall rather than a
new analytic input. An aligned-phase array has the exact second-moment scale while violating the
public fourteenth-moment coefficient, so coefficient moduli and cyclic product geometry alone are
insufficient.

`_AJT13CenteredBoundaryBridge.lean` closes the remaining principal-character bookkeeping at the
natural Gaussian constant.  Weighted convexity proves
`(x-c)^14 <= (21/20)^13*x^14 + 21^13*c^14`; after summing `m` coordinates with `c=1/m`, the
translation error is at most one for `m>=21`, and the exact rational calculation
`135135*(21/20)^13+1 < 2^18` leaves over 7,326 coefficient units.  Therefore a centered
Wick-scale theorem is already a complete consumer for the original public moment target.

## Addendum 7: dyadic recursion data layer and contraction falsifier (2026-07-11)

The DQR files now prove the exact two-scale identity, all mixed-stratum rep--rep correlation laws,
their centered form, the all-twist factorization, and the adjoining-involution palindrome.  The
fourteenth-moment ledger reduces to seven paired cross strata per level.  This does not yield a
uniform contraction theorem.  Exact small-field FFT cells at `p=65537` have

```text
moment step ratio / 2^7 = 23.70... at n=16,
moment step ratio / 2^7 = 28.41... at n=32,
```

with all thirteen unpaired cross contributions of the same sign.  Abstract mean-zero,
inversion-symmetric discrepancy can place `(m-1)/m` of its L2 mass at the quotient involution, so
twist averaging and one-point Cauchy--Schwarz cannot fix this.  Finally, the product of exact level
ratios telescopes to the endpoint moment ratio.  DQR remains a useful localization, but a closing
tower theorem must add production-specific exceptional-level control; recursion by itself is an
equivalent reformulation of the Paley endpoint.

## Addendum 8: exact injective coordinate and three quantitative no-go theorems (2026-07-11)

The coefficient-`126871` injective residual has an exact exterior coordinate.  If
`a_y=#{S subset G: |S|=7, sum(S)=y}`, then

```text
sum_(b != 0) |D7(b)|^2 <= 126871*q*n^7
  iff
(7!)^2 * sum_y (q*a_y-C(n,7))^2 <= 126871*q^2*n^7.
```

`_BGKDepthSevenInjectiveVarianceEquivalence.lean` proves the identity by subset-product Fourier
expansion and Parseval.  Three tempting routes are now quantitatively excluded:

- generic sampling-without-replacement coupling loses over `141` energy bits and yields only
  `|eta|<=85047155`, over `1835` times the Paley ceiling;
- one-sided Kneser mixing loses `162--163` bits, while two-sided mixing loses `190--191` bits;
- the Johnson local-injectivity/Hoffman cap loses `163--164` bits;
- vanishing Newton power sums `p_1,...,p_7` still leaves exactly three quarters of a
  primitive-root phase vector's norm in Johnson grades `1,...,6`; grade six alone carries `7/16`.

The Zhu--Wan subgroup subset-sum asymptotic is also vacuous here: its thin-subgroup per-fibre
error bar exceeds the complete seven-subset population by over `252` bits.  Finally, an exact
small-cell census at `(n,p)=(16,337)` finds `48` nonzero primitive depth-seven disjoint pairs, so
universal recursion through proper leaves of depth at most six is false.  The live input must
control the centered, subgroup-specific primitive sector; exterior terminology, association
schemes, and positive packet completion do not reduce its strength by themselves.

The exact marked sunflower identity now separates that statement without losing the cyclotomic
marker:

```text
W_7 = sum_(r=0)^6 D_r*C(n-2r,7-r) + D_7.
```

Here `D_r` counts globally disjoint, equal-sum, nonzero-lift petal pairs.  Existing depth-at-most-six
packet theorems supply structural leaves but no cardinal bounds on the weighted `D_2,...,D_6`
sum, so both the amplified lower-depth census and the primitive `D_7` term remain honest sockets.

`_BGKSevenOverlapProductionBudget.lean` removes the two vacuous terms (`D_0=D_1=0`) and evaluates
the exact production completion coefficients.  A deliberately optimistic positive Wick bound
already charges `158760` units at depth two, more than the full `126871` injective allowance; the
depths `2,...,6` total `2714355`, strictly between 21 and 22 allowances.  The same file maps every
marked depth-two pair into the existing ANT46 projective-accident classifier, assuming the
cyclotomic lift is odd.  This is a clean route to extra arithmetic, but it also proves that
termwise positive completion is not the capstone: one needs signed/DC cancellation or marked
strata far below their ambient Wick envelopes.

The depth-two consumer is now exact.  `accidents H=empty`, or the stronger existing
`DifferenceSignatureInjectiveModInversion H (2^30)` hypothesis for
`kappa_n(x)=(x-1)^n`, forces the marked `D_2` Finset to be empty; there are conditional consumers
for each production prime.  No in-tree theorem currently instantiates that injectivity or
unconditional accident-freeness.  The existing production facts stop at 12-divisibility and the
exclusion of triple-equal packets, so `kappa` injectivity is a genuine arithmetic residual rather
than hidden bookkeeping.

`_ANT46KappaProductionReduction.lean` compresses that residual as far as the current algebra
allows.  Choosing one representative of each non-self inversion class turns injectivity into the
nonvanishing of an ordered discriminant times the self-class value.  At production the canonical
polynomial degree is `536870911`, its literal Sylvester order is `1073741821`, and it has
`144115187270549505` unordered root pairs, so direct resultant expansion is not a small
certificate.  A second reduction projects signatures through a certified large prime factor of
the cofactor: order `462478642316479903` for the first prime and
`90308905535905320959` for the second.  Projected injectivity is sufficient and discards all
small cofactor components, but existing Lucas/order certificates establish only the group shapes,
not separation.  The live `D_2` input is now a prime-specific power-residue separation theorem.

`_BGKMarkedSunflowerInverse.lean` tests whether a signed triangular inversion supplies the missing
cancellation.  Catalan--Lagrange inversion gives

```text
D7 = W7 -(n-12)W6 + ((n-10)(n-13)/2)W5 - ...
     - ((n-4)(n-10)(n-11)(n-12)(n-13)/120)W2.
```

The file proves both this identity and its converse relative to the lower forward rows: inversion
alone is exactly equivalent to the original seventh common-core equation.  At `n=2^30` the
absolute inverse-coefficient mass is between `2^143` and `2^144`.  That is amplification rather
than automatically a 143-bit loss, since a correctly normalized `W_j` bound can carry powers of
`n` that compensate.  The honest new target is therefore a depth-correlated/cyclotomic estimate,
not separate unscaled bounds followed by a triangle inequality.

The centered-translate route has an analogous structural boundary.  In
`_BGKCenteredTranslatePDNoGo.lean`, a five-point centered-delta kernel proves that global mean
zero, additive positive semidefiniteness, and multiplicative invariance alone admit an unbounded
restriction scaling ray.  The exact proper-subgroup autocorrelation cell `(p,n)=(13313,256)` has
normalized coefficient `312012.706...>2^18`.  This is not a production counterexample; it rules
out a universal three-hypothesis CTR theorem and forces any surviving restriction argument to use
additional production-specific arithmetic.

`_BGKCenteredTranslateConeDuality.lean` identifies the exact convex obstruction in Fourier
coordinates.  For nonnegative zero-DC weights constant on `G`-orbits,

```text
sum_(u in G) D_w(1-u) = (1/|G|) * sum_b w_b*|eta_b|^2.
```

At unit spectral mass the optimum is `max_(b!=0)|eta_b|^2/|G|`, and a single-orbit weight attains
it.  Thus the universal spectral-cone bound is precisely the worst-period/Paley problem, not a
weaker relaxation.  The file works directly with spectral weights; it does not separately
formalize the finite Bochner representation from arbitrary PSD kernels.

The actual autocorrelation is more rigid, with `w_b=|eta_b|^12`, but scalar lower moments still do
not exploit that rigidity.  `_BGKLowerMomentOrbitSpikeNoGo.lean` constructs an exact
production-parameter orbit profile satisfying Parseval, orbit multiplicity, `|eta_b|^2<=n^2`,
and even hypothetical Wick ceilings for powers `2,...,6`.  Its seventh power sum lies strictly
between `2^15` and `2^16` times the repaired target.  Those Wick transfers are themselves not
known at the production primes, so the countermodel grants more than the current theory.  A
closing CTR/entropy theorem must impose genuinely joint seventh-order arithmetic on the period
profile rather than interpolate scalar energies.

## Addendum 9: primitive-ray, restricted-code, and period-arithmetic boundary (2026-07-11)

The marked-sunflower cone now has a complete generic-correlation audit.
`_BGKSunflowerCorrelationNoGo.lean` proves the exact adjacent inequalities

```text
W4 >= (n-6)W3,
2W5 >= (n-7)W4,
3W6 >= (n-8)W5,
4W7 >= (n-9)W6.
```

Their direction is lower growth, not an upper cap.  More decisively, the pure ray `D7=T`, with
all other `D_r=0`, has `W2=...=W6=0` and arbitrary `W7=T`.  Its generating polynomial is
`T*z^7*(1+z)^(n-14)`, with roots only at zero and minus one, so the obstruction survives
real-rootedness, PF-infinity, total positivity, ultra-log-concavity, and every scalar shadow
inequality valid for the whole sunflower cone.  At the Wick scale,

```text
13!! = 135135 = 126871 + 8264,
938/1000 < 126871/135135 < 939/1000.
```

Thus even hypothetical vanishing of `D2,...,D6` leaves a primitive arithmetic saving of exactly
`8264`, or `6.115...%`, to prove.  The same file retains the full label distribution: it proves
the sunflower identity coefficientwise and after every additive character, and gives a finite
coefficient-vector reduction modulo `29` that reflects zero for every depth-seven label of degree
below `2^29` and coefficient height at most `14`.

`_BGKPrimitiveDepthSevenSparseCodeNoGo.lean` turns the surviving primitive object into an exact
small-alphabet code.  `_BGKPrimitiveFoldedAlphabet.lean` now proves the sharp source-sensitive
version: folding an order-`2^30` root at `g^(2^29)=-1`, every globally disjoint seven-petal
collision produces a nonzero integer vector `d` with

```text
eval_g(d)=0,   d_j in {-2,-1,0,1,2},   ||d||_1 <= 14,   |supp(d)| <= 14.
```

The proof also classifies the exact nine local source profiles.  At both certified production
roots it supplies a nonzero integer resultant `N` with `P | N` and
`P <= |N| <= 14^(2^29)`.  The height improvement `14 -> 2` does not lower that norm base because
the resultant envelope sees the unchanged endpoint `l1` mass.  Moreover the five-letter alphabet
is sharp and not universally kernel-free: in `ZMod 17`, `g=3` has order `16`, and globally
disjoint seven-subsets collide with folded vector `[1,2,1,2,2,2,2,0]`.  Thus a production proof
must use arithmetic special to the two roots or an average/counting theorem.  If coefficients are
relaxed to the full prime field, evaluation is only one parity check of exact Hamming distance two,
so ordinary BCH, Hamming, Singleton, or linear uncertainty bounds remain blind.

The same file now gives the formal source-fiber enumerator dictated by the exact local profiles.
With
`A=#{j:|d_j|=2}`, `B=#{j:|d_j|=1}`, and `C=#{j:d_j=0}`, its bivariate kernel is

```text
(7!)^2 [x^7 y^7] (xy)^A (x+y)^B (1+x^2+y^2)^C.
```

For every actual lift, `2A+B+2Z=14`, where `Z` counts occupied zero-label coordinates.  Hence
`B` is even and the occupied folded-coordinate count is `7+B/2`.  The unique degree-14 sector is
fourteen distinct `+-1` coordinates; its formal fixed-label ordered factor is
`(7!)^2*C(14,7)=14!`.  Every nonunit sector has degree at most 13, and global disjointness already
forces the folded label nonzero because each side has odd size seven.  This is a genuine target
compression, not an `8264` saving: the lower-degree sectors are rare among all sources but may be
arbitrarily enriched among collisions until a production equidistribution estimate is proved.
The full source-cardinality bijection for the displayed generating function remains to be packaged.

[Kelley's sparse-polynomial root theorem](https://arxiv.org/abs/1602.00208) does retain the number
of monomials, but its optimistic `t=14`, `C=1` scale is between `2^146` and `2^148` at the first
prime and between `2^147` and `2^149` at the second.  This is over 116 bits above the complete
`2^30` root subgroup.  The live coding statement is therefore a production-specific count on the
five-letter, support-14, `l1<=14` slice, not a theorem about the ambient linear code or universal
kernel-freeness of that slice.

The correct subset/tuple covariance normalization is also formal.  If `A` is the unordered
`r`-subset histogram, then the ordered-injective histogram is `J=r!*A`, not `A`, and

```text
V(J) = (r!)^2 V(A),
V(R) = V(J) + V(D_rep) + 2 Cov(J,D_rep).
```

`_BGKInjectiveFactorialCovarianceAudit.lean` proves the exact iff gate and the depth-seven factor
`(7!)^2=25401600`.  A genuine two-point group-sum counterprofile has `V(J)=4>V(R)=0`, so a
universal sampling-without-replacement contraction is false even with correct totals and a
pointwise nonnegative repetition defect.  This agrees with the concurrent G178 multiplicative-
subgroup counterexample on issue #466.  A production-specific signed covariance theorem remains
possible, but the unscaled G176 deletion gate cannot discharge the BGK target.

The depth-two `kappa` route has likewise reached its present literature boundary.
`_ANT46ProjectedCharacterNoGo.lean` proves exact cyclic-code Parseval, shifted Jacobi-mode,
cyclotomic-intersection, and cyclotomic-unit/Kummer formulas for projected signature collisions.
Generic modewise Weil bounds miss the inversion-injectivity floor by 127--129 bits.  The
[Do Duc--Leung--Schmidt cyclotomic-number theorem](https://arxiv.org/abs/1903.07314) would give a
constant intersection cap under `p>(sqrt(14))^k`; the production arithmetic proves the reverse
comparison `P^2<14^k` at both primes.  Kummer reciprocity consequently exposes a simultaneous
Frobenius-separation problem for roughly `2^29` cyclotomic units, but does not supply its
certificate.

`_ANT46ProjectedKappaBucketCertificate.lean` supplies the exact deterministic certificate format
for that finite problem.  Cover the inversion transversal by buckets, require the projected-value
list in each bucket to be `Nodup`, and require distinct bucket ranges to be disjoint; a keyed
variant makes the second condition automatic.  Natural-number square-and-multiply evaluators are
proved equal to both projected production maps and feed the existing inversion-transversal
adapter.  The exact dimensions are

```text
inputs = 2^29 = 536870912,
pairs = C(2^29,2) = 144115187807420416,
2^20 buckets * 512 rows = 2^29 rows,
20 bytes * 2^29 = 10 GiB.
```

The projection exponents have 100 and 93 bits and the target prime-order groups have 59 and 67
bits.  Bucketization therefore changes the working set but does not compress the certificate:
every exact cover contains at least `2^29` row entries.  A formal `ZMod 7` counterexample also
shows that one scalar product fingerprint cannot certify `Nodup`.  This is a feasible
certificate-carrying per-prime route, not a completed injectivity proof; the full table still has
to be generated and independently checked, or replaced by genuinely new arithmetic compression.

Finally, `_BGKPeriodProfileArithmeticAudit.lean` tests arithmetic omitted by the scalar orbit
spike.  Galois transitivity excludes a single rational squared conjugate, and the necessary
period-power congruence rejects the literal `2^53` spike already at depth two with a nonzero
137-bit residue.  These are real constraints.  They are not quantitatively sufficient: a second
nonzero integral signed profile has exactly `m` slots, trace `-1`, squared trace `q-n`, and Wick
ceilings through depth six, yet exceeds the seventh target by 8--9 bits.  One seventh-moment
congruence still leaves exactly `2^198` complete `q`-steps below the target.

The 2026 [Wu--Wang--Pan Jacobi determinant](https://arxiv.org/abs/2506.14316) controls the linear
coefficient of the period minimal polynomial.  The audit constructs an irreducible monic family

```text
X^4 + X^3 + (1-A(A+1))X^2 + X + 1
```

with fixed norm, trace coefficient, and linear coefficient, but a real root in `[A/2,A]` for
every `A>=2`.  Thus one exact determinant, even with norm and irreducibility, does not upper-bound
the house.  [Wu--Ji](https://arxiv.org/abs/2605.27169) concerns a quadratic-character product
matrix rather than the growing-index production profile.  The surviving period target is a
quantitative theorem coupling all totally-real ramified conjugates (or all moment residues) at
seventh order.

The ordinary graph-normal-ordering route does not bypass that target.
`_BGKHashimotoWickSeparationNoGo.lean` computes

```text
H14(d-1,x)
 = x^14 -14(d-1)x^12 +77(d-1)^2x^10 - ... -2(d-1)^7.
```

Its first subtraction coefficient counts only 14 cyclically adjacent reversals; Wick/injective
normal ordering sees all `C(14,2)=91` first-pair placements, leaving exactly `77d+14`.  A concrete
length-14 integer word is closed and cyclically nonbacktracking while repeating directions.  A
second formal counterexample gives two unit-phase families with the same first power sum but
ordered-injective transforms `-5040` and `5040`.  Hence no univariate adjacency/Hashimoto
polynomial can isolate `D7`.  A dilation-coloured theory would need the full Newton inputs
`eta_b,...,eta_(7b)` and would still face the primitive common-core subtraction.  A genuinely new
Ramanujan cap would close the public raw-moment route with coefficient `4096`; this is not by
itself a direct `D7` extraction, and Ihara--Bass supplies no such cap on a regular generalized
Paley graph.

`_BGKDilationColoredNewtonOperatorNoGo.lean` then builds the correct multicolour replacement.
Convolution by `G,2G,...,7G` gives seven commuting operators with a common additive-character
eigenbasis, and the full degree-seven Newton polynomial in those operators has eigenvalue exactly
the ordered-injective transform `7!*e_7`.  This retains all seven power sums that univariate Ihara
discarded.  Nevertheless every nonzero colour has the same entire marginal Schatten profile by
the permutation `b -> jb`.  A two-frequency coefficient-scale model of commuting real diagonal
joint spectra with identical marginal norm moments for every colour and exponent has exact Newton
energies

```text
66816 < 126871 < 25401600 = (7!)^2.
```

The Newton scalar is sign-indefinite even on commuting real diagonal contractions.  Thus neither
separate Schatten estimates nor a generic Schur/SOS certificate can close the operator lane.  Its
precise live theorem is a mixed subgroup-arithmetic correlation bound for
`(eta_b,eta_(2b),...,eta_(7b))`, whose squared Newton trace is the injective variance itself.

`_BGKDilationPermutationCopulaNoGo.lean` verifies that this is not merely an artifact of allowing
unrelated colour permutations.  On the genuine multiplier action of `1,...,7` on `ZMod 13`, two
base sign profiles with the same value multiset produce identical marginal moments for every
colour and exponent, yet

```text
953600 < 13*126871 < 64641152.
```

Their normalized Newton traces therefore straddle the allowance.  This is deliberately an
abstract dilation copula, not an additive Fourier transform of a multiplicative subgroup.  It
shows that the live input must use that latter arithmetic realization, not only the common
dilation action.

`_BGKActualJointPeriodLaw.lean` computes the first exact layer of that realization.  For arbitrary
colour weights, every mixed product of periods and conjugate periods is `q` times the matching
weighted additive collision count.  The powers of the seven production colours `1,...,7` are
certifiably distinct at both primes, giving the exact nonzero-frequency Gram law

```text
diagonal = q*n-n^2,        off diagonal = -n^2.
```

Thus the actual profiles form a regular-simplex frame and cannot realize the aligned-copula
countermodel.  Pairwise correlation is nevertheless 123--124 bits below the `65,663,244`-unit
leakage scale.  At the first transition the deleted-pair energy is exactly `q*(A+n-2M)`, with
`A` the ordered additive energy and `M=#{x+y=2z}`.  The production antipodal floor on `A` makes a
selected `3 -> 2` defect require `M>2^59`; a nonzero-shift representation cap `2^22` gives
`M<=n*2^22=2^52`.  The surviving joint-law input is therefore a favorable signed higher
weighted-collision correlation, not pairwise orthogonality.

`_BGKSevenStepFlatteningProductionNoGo.lean` isolates the exact entropy socket.  The normalized
injective chi-square allowance is strictly between `2^-36` and `2^-35`.  If the first summand is
followed by six uniform normalized contractions, their integer numerators must have product at
most `126871`; hence `7^6=117649` fits while `8^6=262144` fails.  Each transition must save more
than 27 `L2` bits.  Ordinary positive BSG loses 98--99 bits before extracting one production
subgroup point.  Even granting the classical shifted-intersection scale `4*n^(2/3)=2^22` saves
only eight bits, leaving an exact 19-bit one-step deficit, while Hart's sixfold-covering size gate
is reversed by over 1048 cleared bits.  The remaining probabilistic target is therefore a
centered, trajectory-weighted six-step flattening inequality whose contraction numerators multiply
to at most `126871`.

`_BGKWickTrajectoryDefectBudget.lean` identifies a much sharper sufficient input.  The six
Gaussian/Wick transition numerators are

```text
3, 5, 7, 9, 11, 13,       product = 135135.
```

The literal production allowance, including the finite-population/DC normalization, lies strictly
between `126871` and `126872`.  Replacing any one Wick numerator by its predecessor leaves a
product at most `124740<126871`.  The spare margin even permits multiplying every transition
bound by `501/500`, a uniform `0.2%` overhead at all six steps.  Formal six-ratio telescopes consume
both the exact and robust profiles and prove the final depth-seven discrepancy target.  This does
not prove the missing transition estimate: it shows that one integer unit of improvement at one
step suffices even after small, explicitly budgeted finite-population losses elsewhere.

`_BGKCenteredTrajectoryContraction.lean` supplies the actual subset-trajectory consumer.  Writing
`Z_r` for centered `r`-subset discrepancy, six inequalities `n*Z_(r+1)<=c_r*Z_r` with
`prod c_r<=126871` imply the exact remaining seven-subset variance target.  Its deleted-diagonal
Newton transition retains all seven dilation colours.  A real subgroup counterexample in
`ZMod 17` has `Z_7=Z_1>0`, forcing every universal product to be at least
`8^6=262144`; the theorem must be production-specific.  More sharply, at the production
parameters the antipodal zero-sum fiber forces

```text
n*Z_2/Z_1 > 3 + 2^-29.
```

The first transition therefore satisfies neither the Wick cap `3` nor the robust selected-defect
cap `2*(501/500)`.  The selected one-unit improvement must be sought at one of transitions
`2 -> 3`, ..., `6 -> 7`.  The antipodal lower proxy is below the ordinary robust cap `3.006`, but
that comparison is explicitly not an upper bound on the full first ratio.

`_BGKCyclotomicKreinSchurNoGo.lean` performs the all-orders positivity audit on the enlarged
orbit-spectral cone.  For a translation kernel, Schur multiplication is additive convolution of
its Fourier profile.
Nonnegative multiplicative-orbit profiles are closed under that convolution, so every Schur power
is automatically Krein-admissible.  The single-orbit extremizer consequently survives the full
hierarchy, and the unit-mass cone optimum remains exactly the worst period square.  Combining only
this positivity with the valency bound misses the production target by 191--192 bits.  In the
formally self-dual dictionary of [Nomura--Terwilliger](https://arxiv.org/abs/2405.10491), a useful
next theorem must therefore impose the exact arithmetic values and coupling of the intersection
numbers, rather than merely their nonnegativity.

`_BGKCyclotomicIntersectionIntegralityAudit.lean` keeps the actual integer structure constants.
For `p_ST(z)=#{x in S : z-x in T}`, the additive-character transform is exactly the product of
the two relation periods; total mass and multiplicative-orbit invariance are also formal.  At both
certified primes, Cauchy--Davenport rules out a product row supported on only one cyclotomic class.
That sharp support statement is still almost vacuous quantitatively: the standard integral row
constraints admit `(n-1,1)`.  At `n=2^30` they force one leaked unit, while reducing the primitive
coefficient by `8264` requires

```text
ceil(8264*2^30/135135) = 65663244,
2^25 < 65663244 < 2^26.
```

Thus exact integrality, row mass, and support size are 25--26 bits short.  The surviving
association-scheme theorem must force a quantitative spread or signed correlation among many
specific cyclotomic intersection numbers.
