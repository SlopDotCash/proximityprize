# #466 DYN09 — ten dynamics attacks and the dyadic-transfer right-inverse no-go

Date: 2026-07-10

Branch: `research/proximity-prize`

Status: one new axiom-clean no-go; core open

## Target audited

The production target is not raw energy or a bulk law.  In the current interfaces it is either

- the DC-centered `relationAnomaly` budget of `_R366CenteredRelationAnomaly.lean` / G75, hence the
  single-embedding first-incidence signed mass from #505; or
- after the G121--G127 census arc, the fully-disjoint equal-sum sector left outside the triangular
  moment LP.

Therefore a dynamics proposal counts only if it bounds a signed, worst-frequency quantity on the
*actual arithmetic state*.  A spectral gap for an unrelated ensemble, an average Lyapunov exponent,
or an absolute partition function is only a reformulation.

The exact probe is `scripts/probes/probe_dyn09_ten_angles.py`.  It uses only integers and
`fractions.Fraction`; its ten outputs are deterministic.

## External calibration

Classical Ruelle gaps use expansion plus a regularity space and, in the positive-weight case, yield
decay of correlations; see Nakano--Sakamoto, [*Spectra of expanding maps on Besov
spaces*](https://arxiv.org/abs/1710.09673).  Twisted eventual contraction additionally needs
non-local-integrability/non-concentration inputs, as made explicit in Leclerc,
[*Julia sets of hyperbolic rational maps have positive Fourier dimension*](https://arxiv.org/abs/2112.00701).
Those hypotheses are precisely what the finite dyadic sibling operator does not provide for free.

The Paley socket is exact, not analogical: generalized-Paley eigenvalues are Gaussian periods
(Podestá--Videla, [*Spectral properties of generalized Paley graphs*](https://arxiv.org/abs/2310.15378)).
Cat-map QUE is a different symplectic system; even there invariant rational subspaces can support
localized super-scars (Kelmer, [*Arithmetic quantum unique ergodicity for symplectic linear maps of
the multidimensional torus*](https://arxiv.org/abs/math-ph/0510079)).  Hence a cat-map analogy needs
an exact conjugacy and a worst-state theorem before it touches this target.

## Ten falsify-first subangles

1. **Jacobi/Toda turnover with gauge fixing — no new control.**  The exact probe checks the
   cospectral pair `J(5,0)` and `J(3,4)` through traces `1..12`: every trace agrees while the local
   edge readouts are `5` and `4`.  This extends the small check behind
   `_AssaultV2_JacobiToda.lean`; conserved spectral data still does not locate the turnover.

2. **Ruelle transfer for the dyadic sibling map — decisively refuted in the unrestricted space.**
   The normalized sibling average has an exact right inverse.  Its fine-to-fine conditional
   expectation is idempotent, has `L∞` operator norm one, and fixes a nonzero centered mode.
   `_DYN09DyadicTransferRightInverseNoGo.lean` proves this, including arbitrary nonzero branch
   weights and a pointwise-norm-preserving right inverse for unit weights.

3. **Arithmetic cocycle Lyapunov exponent — average contraction is insufficient.**  Two exact
   diagonal transfer matrices can contract their second coordinate on every step while sharing an
   invariant first coordinate.  All `2^8` words fix that direction, so the worst Lyapunov exponent
   is zero.  A production theorem must exclude an invariant/aligned direction for the actual period
   cocycle, which is the missing worst-coset phase statement.

4. **Renormalization fixed point — bulk statistics do not determine the edge.**  The rational
   vectors `(1,0,-1,0)` and `(3/5,4/5,-3/5,-4/5)` have identical mass, mean, and second moment but
   maxima `1` and `4/5`.  A Gaussian/variance fixed point can coexist with different extremes.

5. **Wavelet-packet cancellation — zero detail need not mean a small state.**  The centered fine
   vector `(1,1,-1,-1)` has both Haar details zero, while its coarse mode is `(1,-1)` with full
   amplitude.  Wavelet energy localization alone misses the norm-preserving coarse range.

6. **Signed multiplicative cascade — independence is the theorem, not a model.**  Perfectly
   correlated sibling weights give mass `2^L`; after the natural `2^L` normalization the amplitude
   is exactly one at every level.  Any square-root cascade estimate must first prove decorrelation
   of the arithmetic branches.

7. **Quantum cat-map analogy — wrong dynamics without a conjugacy.**  The exact `Z/16` shift has a
   hard return at time `16`: the delta-state correlation is `1,0,...,0,1`.  It has recurrence rather
   than a uniform hyperbolic decay mechanism.  This is consistent with the already-landed
   `_DilationZeroEntropyNoGo.lean`.

8. **Arithmetic QUE — mean equidistribution does not upgrade to the maximum.**  At half of the
   `Z/16` orbit, the exact time-average remains total-variation distance `1/2` from uniform.  Even an
   eventual orbit-average theorem would not bound the worst Gaussian-period eigenvalue without a
   quantitative thin-family maximal inequality.

9. **Scattering/resonance formulation — spectral relabeling.**  The two Jacobi matrices in angle 1
   have the same characteristic polynomial `lambda^3-25 lambda`, hence identical resonances, but
   different local recurrence maxima.  The scattering data adds no invariant unless arithmetic
   norming constants are supplied; those constants encode the missing state.

10. **Thermodynamic pressure of collision words — absolute pressure is phase-blind.**  At depth
    `12`, aligned and parity-balanced binary word weights have the same absolute partition function
    `4096`, while their signed sums are respectively `4096` and `0`.  Absolute pattern pressure
    cannot decide the DC-centered, signed first-incidence anomaly.  Any viable pressure must retain
    cross-orbit signs, at which point its pressure bound is the desired cancellation estimate.

## New formal result

`_DYN09DyadicTransferRightInverseNoGo.lean` proves:

- `siblingAverage_coarseLift`;
- `haarProjection_idempotent`;
- `not_strictMeanZeroContraction` for every `c < 1`;
- `weightedTransfer_phaseCompensatedLift` for arbitrary nonvanishing weights;
- `norm_phaseCompensatedLift` for unit weights;
- `weightedHaarProjection_idempotent`;
- `weightedTransfer_normPreserving_rightInverse`.

`scripts/pg-iterate.sh` passes and every printed endpoint uses only `propext`,
`Classical.choice`, and `Quot.sound`; there is no `sorryAx`.

## What survives

The only dynamics survivor is a **restricted-state range-avoidance theorem**: prove that the actual
Gauss-period/twisted-incidence state has a quantitatively large Haar-detail component, uniformly at
the maximizing frequency and through logarithmic depth.  Abstractly, the transfer cannot contract
because its compensated coarse range is norm preserving.  Arithmetic progress would have to show
that the production state stays away from that range.

This is a sharp socket, but not yet a gain: “stays away from the aligned range” is the needed
worst-coset Jacobi-phase decorrelation, and a DC-centered version is the same kind of signed
cross-orbit estimate isolated by #505.  No theorem here bounds `relationAnomaly`, `depthFiber G r r`,
`DCEnergyBound`, the Paley maximum, or `delta*`.  The core remains open.
