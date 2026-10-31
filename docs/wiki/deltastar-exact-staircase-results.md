# The exact δ\* staircase below Johnson — consolidated results (paper seed)

> Status: 2026-06-12. Consolidates the #357 campaign's machine-checked exact-threshold
> results for smooth-domain Reed–Solomon codes into one citable map — the write-up seed
> for the staircase paper. Everything in §1–§4 is a Lean theorem on `main`, axiom-clean
> (`propext, Classical.choice, Quot.sound`), zero `sorry`, behind the repo's
> anti-laundering gates. §5 is the honest boundary of knowledge.

Throughout: `C = RS[F, μ_n, k]`, smooth domain `μ_n` (`n = 2^μ` in production), distance
`d = n − k + 1`, band `b` = radii with `δ·n ∈ [b−1, b)`, error budget `e = b − 1`,
`q = |F|`. `ε_mca` is the ABF26 Definition-4.3 mutual-correlated-agreement error
(`Errors.lean`); `δ*(C, ε*) = sup{δ : ε_mca(C,δ) ≤ ε*}` (`MCAThresholdLedger`).

## 1. The three-regime law (per band, exact where stated)

For a band `b`, the value of `ε_mca·q` as a function of the distance is given below,
subject to the guards in each row. The strip lower bounds (`strip_eps_ge`) need
`(b−1) ∣ n`. Bands with `(b−1) ∤ n` have no strip lower bound here.

| distance regime | value | sides | artifacts |
|---|---|---|---|
| `d ≥ 3b−2` (deep) | `= b` | both | `UniversalStaircaseCollapse`, `UniversalSpikeFloor`, `MCAStaircaseExact/RS` |
| `d = 3b−3` (top strip row) | `= n/(b−1)` for `(b−1) ∣ n`, `(b−1)(2b−3) ≤ n` | both | `StripSupExactness.rs_topStrip_epsMCA_eq` ⊕ `MonomialStripExplosion.strip_eps_ge` |
| `d = 3b−4` (second strip row) | `≥ n/(b−1)` for `(b−1) ∣ n`; `≤ n` | bracket | `strip_eps_ge` ⊕ `BoundarySupExactness.nearTop_epsMCA_le` |
| `2b ≤ d ≤ 3b−5` (lower strip) | `≥ n/(b−1)` for `(b−1) ∣ n` | lower only | `strip_eps_ge`; sup side OPEN |
| `b+1 ≤ d ≤ 2b−1` (boundary), `b ∣ n` | `≥ n` | lower | `CosetCliqueBoundary.clique_eps_ge` |
| `d = 5`, `b = 3`, `3 ∣ n` | `= n` | both | ⊕ `BoundarySupExactness.rs_boundary_epsMCA_eq` |
| `d = 5`, `b = 3`, `3 ∤ n` | `≤ n−1`; `= n−1` at `n = 8` | both at `n=8` | `BoundaryDefectBound` ⊕ `DeltaStarSecondPinF17Maximal` |

Structural readings:
- The thresholds `3b−2 / 3b−3 / 2b−1` are exactly the supports-union thresholds: triples
  (resp. pairs) of error supports can/cannot carry a codeword; the proofs are support-
  geometry dichotomies (frame absorption + no-joint escape vs disjoint tiling; the clump
  induction at `d = 3e−1`).
- **Production form**: `n = 2^μ` has `3 ∤ n`, and `b ∣ n` exactly when `b` is a power of 2.
  The boundary rows recur at every halving of the distance budget with cap `n−1` (defect
  form, `BoundaryDefectBound`). The strip explosions (`strip_eps_ge`, which needs
  `(b−1) ∣ n`) fire only on the bands `b = 2^j + 1`. On a fixed dyadic domain they do **not**
  fire at every band: `b = 4` would need `3 ∣ 2^μ`. Strip sharpness at the remaining bands is
  not established by this construction.

## 2. Exact δ\* (closed forms on `ε*`-bands)

- **Granularity ladder** (`mcaDeltaStar_eq_granularity`, `MCAStaircaseDeltaStar`):
  `δ*(C, ε*) = j/n` for `ε* ∈ [j/q, (j+1)/q)`, any linear code with the collapse+spike
  budgets — `δ* = ⌊ε*q⌋/n` below the strip.
- **Strip-edge pins** (`StripEdgeDeltaStar.mcaDeltaStar_eq_strip_edge`): `δ* = g/n` on
  the widened band `ε* ∈ [g/q, (n/g)/q)` at the strip dimensions.
- **Strip-interior pin** (`StripSupExactness.mcaDeltaStar_eq_strip_interior`):
  `δ* = 3/n` on `ε* ∈ [(n/2)/q, n/q)` for `4 ∣ n`, `k = n−5` — the first pin whose good
  side is an explosion value; with the strip-edge pin, these codes are exact on all of
  `[2/q, n/q)`.
- **Boundary pins** (`CosetCliqueBoundary.mcaDeltaStar_eq_boundary`): `δ* = (b−1)/n` on
  `ε* ∈ [(b−1)/q, n/q)` at boundary dimensions, `b ≤ 4`, `b ∣ n` — spanning `n−2`
  granularity steps at `b = 3`.
- **Production floor** (`MCADeltaStarProductionFloor.mcaDeltaStar_rs_ge_at_secpar`): at
  `ε* = 2⁻¹²⁸`, `δ* ≥ (⌊(n−k)/3⌋+1)/n ≈ (1−ρ)/3` unconditionally for every smooth RS
  instance at production shape (`n/q ≤ ε*`).
- **Multi-window curves** (`VVectorN16`): five consecutive exact windows at `n = 16`,
  rate 1/4 — the first machine-checked δ\*(ε\*) curve.

## 3. The window brackets (what bounds δ\* inside `(1−√ρ, 1−ρ)`)

- **Upper (ceiling)**: KKH26 family — `kkh26_mcaDeltaStar_le`: `δ* ≤ 1 − r/2^μ`
  (+ in-repo improvements: stratified spread, Parseval threshold halving — `s = 64` rows
  unconditional; `s ≥ 128` gated on `TZPrimeSupply`).
- **Lower**: Johnson side — regimes I+II of `InteriorCeiling` reduce to the BCIKS20-class
  `JohnsonLineCloseBound` (`RegimeIIBridge`); the Hab25 discharge chain is reduced to
  `CellPackageSupply` (one named residual) with the repaired cleared recursion
  (`ClearedRecursion`) replacing the divergent in-tree (A.1) form
  (`Finding14Countermodel`).
- **The split**: `KKH26RegimeSplit` welds: JohnsonDischarge covers `δ < 1−√ρ−o(1)` only;
  the pin needs `RegimeIIIGoodness` on `[gs_johnson, 1 − r/2^μ)` — the named open core.

## 4. Method inventory (reusable, all in-tree)

Bracket engine (`MCAThresholdLedger`, `MCAExactPin` combinators) · syndrome reduction +
two-ball-point exhaustive pencil enumeration (probe-grade, word-level-validated;
`probe_strip_sup_exactness.py`) · frame absorption / no-joint escape dichotomy
(`StripSupExactness`) · maximal-witness canonicalization + clump induction
(`BoundarySupExactness`) · mod-3 strict induction (`BoundaryDefectBound`) · equivariance
/ orbit reduction (`EquivariancePin`) · interleaving exactness transfer
(`InterleavingStabilityMCA`) · LD⇔MCA dictionary both directions (incl.
`ReverseDictionary`) · fold-tower transport (`TowerMonotonicityRS`).

## 5. The honest boundary (what the paper must state as open)

1. **Regime III** (`(1−√ρ, 1−ρ−Θ(1/log n))` for the deployed asymptotic): equivalent via
   the CS25 coupling to beyond-Johnson list decoding of explicit smooth-domain RS — open
   ~25 years. Five toolkit no-gos are machine-checked or rigorously argued (dossier
   §§17,20,23,25,26); 27 attack hypotheses disposed (`DISPROOF_LOG`). The Fourier-side
   open input `N ≪ |G|^{3/2}` (HBK) is true, partially formalized, and **average-side
   only** — no in-tree implication reaches the worst-case pin (audit, 2026-06-11).
2. `b ≥ 4` lower strip rows (sup side) and boundary rows `d ≤ 2b−2`: the absorption
   inequality fails below `d = 3e−1`; wt-`d` deviation chains are the open mechanism.
3. The general `3 ∤ n` boundary certificate family (`n−1` lower bound; probe-exact,
   in-tree at `n = 8` only).
4. `TZPrimeSupply` (analytic NT), the paper-interface residuals
   (`CapacityBoundsProofs`), and the conditional census programme
   (`docs/wiki/census-programme.md`) — quarantined behind named surfaces.

**Paper shape (proposed):** §1 the staircase law (this page §1–§2) — the first exact
MCA thresholds for any code family, machine-checked; §2 the window brackets and the
regime split (§3); §3 methods (§4); §4 the open core, stated through the named-surface
architecture so any future breakthrough lands as one lemma. The prize claim requires
item 5.1 and only item 5.1.
