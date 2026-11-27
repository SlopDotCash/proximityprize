# Rate-1/2 SYZ Strip Audit: Unconditional Refutation of F2 (`StripSyzygyControlledCeiling`), `StripMasterHypothesis` Vacuity, and On-Domain 4-Coset Sylvester / Near-Balance No-Go at $n = 2^{30}$

## Summary and Honesty Classification (`DOSSIER.md` §6)

This note documents the machine-checked results in
[`CarbonSYZMasterAuditAndF2Refutation.lean`](../../../ArkLib/Research/ProximityGap/Frontier/CarbonSYZMasterAuditAndF2Refutation.lean)
and companion verification script
[`probe_carbon_syz_master_audit.py`](../../../scripts/probes/probe_carbon_syz_master_audit.py).

Per `DOSSIER.md` §6, every theorem here is classified honestly as a **refutation / no-go** of an
isolated strip residual or master hypothesis:

1. **Unconditional refutation of F2 (`SYZ66.StripSyzygyControlledCeiling`) and the entire
   `SYZ46 → SYZ57 → SYZ60 → SYZ66` census chain on the first prize prime (`ZMod P₁`,
   $n = 2^{30}, k = 2^{29}$).**
   Combining the unconditional four-head septic-core construction
   `ProximityGap.FirstPrimeSepticCores.over_budget` at radius $313{,}174{,}699 / 2^{30}$ with
   monotonicity of $\varepsilon_{\mathrm{MCA}}$ (`ProximityGap.epsMCA_mono`) up to the strip
   predecessor radius $357{,}913{,}940 / 2^{30} < 1/3$ proves
   $$\varepsilon^* < \varepsilon_{\mathrm{MCA}}\!\left(\mathrm{evalCode}(g, 2^{30}, 2^{29}-1),\, \frac{357{,}913{,}940}{2^{30}}\right).$$
   Consequently `SYZ60Dictionary.BadCountCeiling`, **`SYZ66.StripSyzygyControlledCeiling` (F2)**,
   `SYZ57Transport.CountingDictionary`, and `SYZ46.StripCensusBound` are all **provably `False`**
   (`not_badCountCeiling`, `not_stripSyzygyControlledCeiling`, `not_countingDictionary`,
   `not_stripCensusBound`), and an explicit dependent syzygy-carrying stack exists at the strip
   predecessor with $\mathrm{mcaBadCount} \ge 2^{30} + 1$.
2. **Structural vacuity of `StripMasterHypothesis` (`SYZ40`), `StripMasterHypothesis'` (`SYZ41`),
   and `StripMasterHypothesis''` (`SYZ42`).**
   Each master hypothesis universally quantifies `realizability` / `realizabilityCore` over
   $k \le U_{\mathrm{card}} \le n$. Instantiating at $U_{\mathrm{card}} = n$ produces a
   `SuperadditiveUnion n k n` configuration, for which
   `SYZ20JointRankSuperadditive.union_card_lt_length` yields $2(n - k) + 1 \le 2(n - k)$, a
   contradiction for every $k \le n$. Any conditional theorem taking `StripMasterHypothesis`,
   `StripMasterHypothesis'`, or `StripMasterHypothesis''` as an antecedent is therefore vacuously
   true until the range is restricted to $U_{\mathrm{card}} \le n - 1$ (or routed through
   stack-level union-avoidance).
3. **Unconditional refutation of literal `SYZ40.UniformSylvesterInjective` and symbolic 4-coset
   refutation of `SYZ38.SylvesterInjective` and unconditional near-balance $\iota \le 1$ on
   `RegionSyzygyRealizable ∩ StrictBandCores` at $n = 2^{30}$ on BOTH certified prize primes.**
   - Literal `SYZ40.UniformSylvesterInjective K n k` omits pairwise coprimality and squarefreeness
     and is `False` over every field $K$ for $n = 2k$, $k \ge 2$ (`not_uniformSylvesterInjective`).
   - Even with genuine smooth subgroup roots, pairwise-disjoint squarefree vanishing polynomials,
     and strict-band core sizes $2n/3 < s < 3n/4$ (`SYZ50.StrictBandCores`), partitioning any
     order-$4d$ subgroup $\langle g \rangle \subset K^\times$ ($d \ge 4$) into its four $\mu_d$-cosets
     $$S_r = \{\, g^{4j+r} : 0 \le j < d \,\} \quad (r \in \{0,1,2,3\}), \qquad
       \prod_{x \in S_r} (X - x) = X^d - \omega^r \quad (\omega = g^d)$$
     carries the exact nonzero **floor-attained constant syzygy**
     $$(X^d - 1)(\omega - \omega^2) + (X^d - \omega)(\omega^2 - 1) + (X^d - \omega^2)(1 - \omega) = 0$$
     of minimal product-degree $\delta_1 = d = \max(d, d, d)$, imbalance
     $\iota = \lfloor d/2 \rfloor \ge 2$, and nonzero in-budget Sylvester kernel
     (`fourCoset_regionSyzygyRealizable`, `fourCoset_strictBandCores_and_imbalance`,
     `fourCoset_not_sylvesterInjective`).
   - **Two-class scope precision (`SYZ59` / `SYZ69` / `_F1RegionSyzygyInterface`):** In the
     two-class F1 dichotomy $(\delta_1 = \max(a,b,c)) \lor (\iota \le 1)$, this 4-coset witness
     lies in the **floor-attained constant-syzygy branch** $\delta_1 = d = \max(d, d, d)$ rather
     than `SYZ59.middleBand` ($\max < \delta_1 \le \lfloor S/2 \rfloor - 2$). Accordingly, it does
     **not** refute `RegionMiddleExclusion`; instead, it proves at $n = 2^{30}$ ($d = 2^{28}$,
     $t = 178{,}956{,}972$, exact strip core size $2d + t = 715{,}827{,}884$) over **both**
     `ZMod PrizeShapePrimeP30.P` and `ZMod PrizeShapePrimeP30Second.P` that neither
     `SYZ38.SylvesterInjective` nor unconditional near-balance $\iota \le 1$ can hold on
     `RegionSyzygyRealizable ∩ StrictBandCores` (`ι = 2^{27} = 134{,}217{,}728`).

## Scope Separation: Why `P₁` Fails at $2^{30} + 1$ While `P₂` Remains Open

- **Why F2 fails on `P₁`:** On the first certified prize prime
  $P_1 = 2^{30}(2^{128} + 192) + 1$ (`PrizeShapePrimeP30.P`), the 128-bit MCA bad-scalar budget is
  $\lfloor P_1 / 2^{128} \rfloor = 2^{30}$, so any stack with $\ge 2^{30} + 1$ bad scalars strictly
  exceeds $\varepsilon^* = 2^{-128}$. The four-head septic-core construction
  (`FirstPrimeSepticCores`) achieves $\mathrm{ordinary} + 4 \cdot \mathrm{special} = 2^{30} + 1$
  bad scalars at $313{,}174{,}699 / 2^{30} < 357{,}913{,}940 / 2^{30}$ via 4-label amplification on
  its special fiber, breaking the $2^{30}$ per-stack ceiling inside $(7/24, 1/3)$ and refuting
  `StripSyzygyControlledCeiling` (F2), `BadCountCeiling`, `CountingDictionary`, and
  `StripCensusBound`.
- **Why this does NOT close `P₂`:** On `PrizeShapePrimeP30Second.P`,
  $P_2 = 2^{30}(2 \cdot 2^{128} + 13) + 1$ has 128-bit bad-scalar budget
  $\lfloor P_2 / 2^{128} \rfloor = 2^{31}$ rather than $2^{30}$, so $2^{30} + 1$ bad scalars
  consume only $\approx \frac{1}{2}\varepsilon^*$. On $P_2$ at rate $1/2$, the first-failing MCA
  error-count bracket remains $[282{,}513{,}457,\, 387{,}740{,}104]$ kernel-checked
  (`HalfRatePopulationCover.lean` vs. `SecondPrimeTetrahedron.lean`) and
  $[313{,}215{,}001,\, 387{,}740{,}104]$ with written blow-up safety (`HalfBlowupGaussWindow.lean`;
  whether half-rate MCA crosses the Johnson pivot $314{,}491{,}699$ is undecided).
- **Why stack-level constraints are essential for F1/F3:** Because the 4-coset floor-attained
  constant-syzygy witness realizes `RegionSyzygyRealizable` and `StrictBandCores` at $n = 2^{30}$
  over both `P₁` and `P₂` with $\iota = 2^{27}$ and a nontrivial in-budget Sylvester kernel, no
  purely region-level or subgroup-geometry hypothesis can force `SYZ38.SylvesterInjective` or
  $\iota \le 1$; any obstruction to over-budget lifts must invoke stack-level agreement and
  G87 syndrome constraints.
