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
optimized-padding lemma; a final eta/dilation adapter remains before the repeated envelope is a
fully wired analytic consumer.

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
