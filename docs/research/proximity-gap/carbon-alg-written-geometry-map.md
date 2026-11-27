# Written-geometry audit for the second-prime safety bounds and dyadic involutions

Author: Carbon `alg-geom`, 2026-11-27. Status categories follow `DOSSIER.md` §6.

## 1. Dyadic 4-transposition rigidity: closed in Lean (all orders, characteristic zero)

`dyadic-involution-pairs.md` calls the all-orders complex argument "a written proof undergoing
formalization". This is out of date. Its full content is kernel-checked:

- `DyadicSevenProjectivities.all_orders`: seven matched dyadic roots force a scaling or
  reciprocal scaling, at every order `2^m`, in every characteristic-zero field;
- `DyadicFourPairGeometry.pattern` and `incident`: reduction of four transpositions to that
  seven-site statement;
- `DyadicFourPairPrime.dihedral` and `DyadicFourPairSmooth.dihedral`: transfer to prime fields
  and to arbitrary smooth cosets when `12^φ(2^m) < p²`.

The missing piece was the packaged characteristic-zero statement. It is now
`ProximityGap.CarbonAlgDyadicComplexDihedral.dihedral_of_charZero` (and `complex_dihedral`) in
[`CarbonAlgDyadicComplexDihedral.lean`](../../../ArkLib/Research/ProximityGap/Frontier/CarbonAlgDyadicComplexDihedral.lean).
**Exact theorem**: every nonsingular trace-zero projectivity that exchanges four disjoint pairs of
`2^m`-th roots of unity is `x ↦ -x` or `x ↦ t/x`, for every `m`. There is no height
hypothesis.

Scope note: the prime-field transfer still needs `12^φ(2^m) < p²`. This holds at order 128
for every sponsor-size prime. It fails at order `2^30`. That is a statement about transfer from
characteristic zero, not about rigidity in characteristic zero.

## 2. Second-prime MCA safety bounds: the precise remaining geometric inputs

The written lower bounds 312,800,001 / 313,215,001 (rate 1/2), 533,150,001 / 534,295,001
(rate 1/4) and 671,088,640 (rate 1/8) all use the same pipeline. The Lean side already checks
the surfaces, the factor accounting (`TwoSurfaceFactorAccounting.two_surface_accounting`), the
rich-head and core-union bounds, the counting half of the tangent bound
(`TangentHeadCount.tangent_head_population_nat`), and every finite allocation. The pipeline is
kernel-checked **except** for one per-component price, the `NonlinearComponentCap` interface in
`TwoSurfaceFactorAccounting`. Nothing in the tree discharges that interface for any price yet.
Packet L1d (`LogarithmicComponentCap`) does not exist.

The price needs three inputs for each irreducible nonlinear common factor `F`:

| Input | Lean status | Remaining geometry |
|---|---|---|
| (a) Tangent height `Σ c_z ≤ C₀ = 2AG + 2Wm` | `two_resultant_height_budget` proves the bound *given* the fiber divisibilities `D_z ∣ gcd(A_a, A_a′)·gcd(H, U H_X)`. `implicit_derivative_divides_of_regular_at_branches` derives those divisibilities from `regularOnPlaneBranches F D` | Branch regularity of `D₁ = H∂_Z` and `D₂ = U(H_X∂_Z − H_Z∂_X)` at every height-one prime of `k[X,Z]` |
| (b) Regular agreement loss `Σ ℓ_z ≤ (G+m)n` | `RepeatedSectionSpecialization.received_tangent` (all multiplicities `j < char`) *given* `regularOnPlaneBranches F D₁` | Same branch regularity of `D₁` |
| (c) Pairwise tangent counting | Fully checked (`TangentHeadCount`) | none |

So for the **ordinary** price `logDerivPrice` the only missing input is one algebraic statement.

> **BranchRegular(F).** For every prime `π` of `k[X,Z]` and every height-one prime `w` of the
> normalization of `k[X,Z]_(π)` in `k(X,Z)[Y]/F`, both `D₁` and `D₂` map the branch ring
> `B_w` into itself.

`TameLogarithmicDVR.tame_logarithmic_lift` and `UnramifiedDerivationDVR.unramified_lift`
already prove BranchRegular locally from four hypotheses at `w`:

1. the residue extension is separable;
2. the ramification index is invertible;
3. `B_w` is a localization of a finite algebra over the base DVR;
4. either `D(π) ∈ (π)` (logarithmic) or `w` is unramified.

Hypotheses (1) and (2) follow from `[E:K] = b < char`. Hypothesis (3) is
`HeightOneNormalization.localNormalization_finite` plus the localization at `w`.

Hypothesis (4) has three cases. If `π ∣ H`, then `D₁π = Hπ_Z ∈ (π)`. If `π ∈ k[X]`, then
`D₁π = 0`. Otherwise `π` does not divide the reduced discriminant, and the remaining obligation
is that `w` is unramified. When the leading `Y`-coefficient `lc_Y(F)` is a unit at `π`, this
follows from étaleness of `R_π[Y]/F`. When `lc_Y(F)` is not a unit at `π`, the written proof
uses its coordinate change (`logarithmic-section-heights.md`, first paragraph). Formalizing that
step is the substantive open task. It must also treat the horizontal factors `Z = z` removed
from `H`.

The **refined** prices behind 312.8M, 313.215M, 533.15M, 534.295M and 671.09M need two further
geometric inputs on top of BranchRegular:

- the Gauss-graph pole height `(6b+2)Wm`, with its sparse-volume and blow-up refinements
  (`gauss-polar-section-heights.md`, `half-sparse-gauss-window.md`,
  `half-blowup-gauss-window.md`);
- plane-curve reflexivity and Bézout for the Veronese dual-degree test (`m > s(s−1)` ⇒ the
  pulled-back determinant curve is coprime to `F`, `tangent-polar-windows.md`).

**Classification.** These bounds remain *written results with Lean certificates*. No
`epsMCA` theorem at these counts can be kernel-checked until `NonlinearComponentCap` is
discharged for the corresponding price.

## 3. Algebraic replacement routes considered and rejected

- **Triple-intersection (third-moment) Johnson.** Without tangent data, three sections on a
  nonlinear `F` that do not lie on one affine head share at most `d` sites. Any affine head
  carries at most `m` sections of `F`. The resulting bound is
  `M ≲ m n³ /(t³ − d n²)`. It needs `t/n > (d/n)^{1/3}`, which fails at all three target
  windows: `0.709 < 0.794` at half rate, `0.503 < 0.630` at quarter rate and
  `0.375 < 0.500` at eighth rate. A higher-moment substitute for the tangent argument therefore
  cannot reach these counts.
- **Multiplicity-one regular agreement without derivations.** At a site where `F(x,Z,Y)` has
  the received line as a simple factor with nonzero cofactor, `V_z(x) = u₁(x)` follows directly
  from `F_Y ≠ 0`. The interpolants force `F` to vanish to order `i_x ≥ 2` along many received
  lines, however. There, every section has `F_Y = 0`, so the derivation-lifting theorem
  (BranchRegular) is unavoidable for input (b).
