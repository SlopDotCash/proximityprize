# The Ethereum Proximity Prize δ\* — the two open problems, v2, stated for an analytic number theorist (#466, after 20 rounds)

**This supersedes `deltastar-466-two-open-problems-expert-statement-2026-07-04.md`.** Rounds 15–20
(2026-07-07) restructured Problem B: the raw all-offset form was refuted (a structural diagonal
spike), the corrected off-diagonal form acquired an unconditional partial theorem, an exact rung
bookkeeping, a two-sided tower⟺sup equivalence at depth, and a machine-checked reduction of its
r=2 rung to one classical formalization gap (Hasse for elliptic curves). Every claim below has
been re-verified against the Lean source (theorem names greppable in
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/`); discrepancies found during verification are
flagged inline and collected in §5.

Notation throughout: `F = F_q` (`q = p` prime at the prize instance), `μ_n ⊊ F_p^×` the order-`n`
dyadic subgroup (`n = 2^μ ≈ 2^30`, `p ≈ n^4`, β = log_n p ≈ 4; index `m = (p−1)/n ≈ 2^128`),
Gauss periods `η_b = Σ_{x∈μ_n} e_p(bx)`, `M = max_{b≠0}‖η_b‖`, `H ≤ F_p^×` the far-coset
hyperplane subgroup of index `deg`, incidence field `I_H(s₀) = Σ_{b∈H} conj(η_b)·ψ(b·s₀)`,
`Σ := Σ_{b∈H}‖η_b‖²`, diagonal set `D = {0} ∪ μ_n`, away moments
`S_r^D = Σ_{s∉D} ‖I_H(s)‖^{2r}`.

---

## 0. The machine-checked reduction chain (including the round 15–20 B-side story)

```
δ*-floor  ⟺ (outer iff, BOTH directions axiom-clean: _TwoSidedCapstone.lean, round 14)
WorstCaseIncidenceBounded C δ E        (∀ stacks u, #bad-scalars(u) ≤ E ≈ q·ε* ≈ n)
   ⟸ (one-directional named glue `IncidenceFromWallGlue`, _TwoSidedCapstone.lean:249)
Problem A (WallHolds)  ∧  corrected Problem B
```

and, new since round 15, corrected Problem B itself has a machine-checked internal structure:

```
corrected B  (OffDiagonalHyperplaneCancellation, _R16OffDiagonalHyperplaneCancellation.lean:102)
   ⟸ (moment bridge, √(2e·ln q) loss: _R15IncidenceMomentInterchange + _R16DiagonalExactValue)
diagonal-subtracted Wick tower  (WickAwayAtWithConstant … r … C, all rungs r ≤ ⌈ln q⌉)
   ⟺ (TWO-SIDED, constant 3, at rungs r ≥ log₃ q — which contains the prize depth
       r ≈ ln q ≈ 0.91·log₃ q:  tower_of_awaySupBound (_R19RungRecursion.lean:265) forward;
       supSplit_reverse_three_at_depth (_R20SupSplitReverse.lean:396) reverse.
       Below depth log₃ q the magnitude-only reverse is REFUTED
       (magnitudeOnly_reverse_unbounded, _R20SupSplitReverse.lean:253): head rungs are PHASE-DEEP)
AwaySupBound C   (sup_{s∉D} ‖I_H(s)‖² ≤ C·Σ,  _R19RungRecursion.lean:257)

rung r=0,1: PROVEN unconditional.
rung r=2:   ⟸ FourthMomentTwistBound (_R17QuadrupleWeilRung.lean:202)
            ⟸ QuarticWeilInput per χ (_R18FourthMomentTwist.lean:137;
               fourthMomentTwistBound_of_quarticWeilInput, line 385)
            — QUADRATIC face (χ = quadraticChar): ⟸ LegendreCubicHasse ALONE
               (quarticWeilInput_of_legendreCubicHasse, _R20MobiusDischarge.lean:255 — the
               Möbius t = d + 1/s discharge covers ALL n⁴ tuples, no cross-ratio machinery)
            ⟸ CubicStepanovUpper (_R20StepanovScaffold.lean:212;
               legendreCubicHasse_of_stepanovUpper, line 219 — one-sided suffices by the
               twist-negation halving, line 191). Higher-order-χ faces of QuarticWeilInput: OPEN.
rungs 3 ≤ r < log₃ q: THE PHASE-DEEP HEAD — the genuinely open analytic zone.
```

Every arrow marked proven is axiom-clean (`#print axioms ⊆ {propext, Classical.choice,
Quot.sound}`, no `sorryAx`) and survived a real locked build. Problems A and B remain
**independent** (round 13: A ⇏ B; round 14: B ⇏ A, `_R14SupNormWeakerThanWall.lean`).

*Concurrent-session note.* A parallel session (dossier §30 "grand consolidation") landed a
Jacobi-coefficient ladder normal form (`_R19JacobiFourierExpansion` → … → `_R27FullTowerCollapse`,
all in-tree): `Σ_{s≠0}‖T(s)‖^{2r} = (q−1)·Σ_c ‖(J^{∗r})(c)‖²` exactly, every r. It is the same
tower in Jacobi coordinates; its calibrated open core is `TripleConvEnergyBound` (r=3) and
`IterConvEnergyWick` at deep depth — coordinates of the same open surface described here.

---

## 1. Problem A — unchanged (WallHolds)

> **PROBLEM A.** For every `r ≤ ⌈ln q⌉ ≈ 89`, the DC-subtracted moment obeys Wick:
> `A_r := q·E_r − n^{2r} ≤ q·(2r−1)‼·n^r` (equivalently the wraparound count
> `W_r ≤ n^{2r}/p`, with `W_r ≥ 0` a nonnegative integer count — an unsigned counting
> inequality, not an oscillatory bound).

Lean: `WallHolds G := ∀ r, DCEnergyBound G r` (`_WallCapstone.lean:88`; restated verbatim at
`_MomentOptimizedSupNorm.lean:222` to avoid an import cycle — the two definitions are identical).
Machine-checked consequence: `WallHolds ⟹ M ≤ √(2e·n·(ln q + 1))`
(`eta_le_of_wallHolds`, `_MomentOptimizedSupNorm.lean`). Status, evidence, and the no-go
cartography are unchanged since round 12 (see the v1 statement §1, §3 and dossier §0–§24):
fixed-`r` closes at every accessible scale; the entire residual is the joint limit `r ≈ ln q`
at `n = 2^30`; the char-0 analogue is a theorem (Lam–Leung/Bessel); raw (un-subtracted) Wick is
FALSE past the DC crossover; thinness `n ≤ p^{1/4}` must be load-bearing.

---

## 2. Problem B — CORRECTED (the off-diagonal AwaySupBound form)

### 2.1 The correction (round 15–16, machine-checked)

The v1 all-offset statement `‖I_H(s₀)‖ ≤ √|H|·M` for the *worst* `s₀` is **FALSE** — not for a
deep reason: for any subgroup `G` stabilizing `H`, `I_H(s₀ ∈ G) = Σ/|G|` **exactly**
(`incidenceSum_diag_exact`, `_R16DiagonalExactValue.lean` — pure reindexing, zero analytic
content), a structural χ₀/diagonal spike of size ≈ `|H|` at every `s₀ ∈ μ_n`. Round 13's
"worst-case reaches the `|H|·M` scale" was exactly this spike. Additionally, the raw
Wick-with-constant-`(2r−1)‼` away-tower is **refuted as a universal statement** (float128
countermodels at low β and thin H, tag `466-r16-away-wick-refuted-diag-exact`), and constant-2 at
r=2 is refuted in the β=4 bulk for deg ≥ 8 (the deg-plateau law `1 − c/deg`, explained exactly as
variance depletion in `_R18PlateauLaw.lean`). Constant-3 survives every probe at β ≥ 2.7.

> **PROBLEM B (corrected, the fixed point of the tower).** With `D = {0} ∪ μ_n`:
> ```
>     AwaySupBound C :   sup_{s₀ ∉ D} ‖I_H(s₀)‖² ≤ C · Σ_{b∈H} ‖η_b‖²
> ```
> with `C = O(polylog q)`. (Lean Prop: `_R19RungRecursion.lean:257`, restated
> `_R20SubWickInterpolation.lean:94`.) Measured `C = Λ ∈ [1.7, 12.4]` in all probed cells,
> `Λ/√q → 0.024` at the Fermat cell. Equivalently (per-offset normalized form,
> `OffDiagonalHyperplaneCancellation`): `‖I_H(s₀∉μ_n)‖ ≤ C·√|H|·M`, measured
> `C ∈ [0.61, 1.61]` at all accessible scales.

This is a *reformulation of the campaign Prop*, not a refutation of BCHKS 1.12 — the corrected
form is the honest content of the BCHKS-shaped input. (Prop-layer audit finding, verified: the v1
name `HyperplaneCancellation` **was never a Lean `Prop`** — it was docstring-only; nothing
machine-checked consumed the false all-offset form. `_R16OffDiagonalHyperplaneCancellation.lean`.)

### 2.2 What is now PROVEN about corrected B (all axiom-clean unless flagged)

- **Unconditional partial bound `n√q`**: `‖I_H(s₀ ∉ G)‖ ≤ |G|·((m−1)√q+1)/m ≤ n√q` for every
  thick index-m subgroup (`exists_thick_subgroup_incidence_bound`,
  `_R16UnconditionalIncidenceBound.lean:160`; glued from the R15 Gauss-sum resummation + the #407
  `ConstantIndexGaussSumBound`). Beats the trivial `|H|·M` budget by `n^{3/2}/deg` at prize scale.
  The deg=2 per-shift bound is tight.
- **The exact diagonal**: `I_H(s₀∈G) = Σ/|G|`, `I_H(0) = conj(Σ_{b∈H}η_b)`, exact μ_n-orbit
  invariance (`_R16DiagonalExactValue.lean`).
- **Rungs r = 0, 1 of the tower**: unconditional (`_R16DiagonalExactValue.lean`,
  `awayMoment_one_le` in `_R16IncidenceR2Rung.lean:163`).
- **The r=2 rung modulo Stepanov-formalization**: the chain of §0. Concretely:
  `wickAwayAt_two_of_weil` (`_R17Deg2WeilRung.lean:1050`) closes deg=2 at constant 1 for
  `√q ≥ 16n²` conditional only on `WeilQuarticPairs` (Weil 1948); the general-deg lattice runs
  through `FourthMomentTwistBound ⟸ QuarticWeilInput` (`fourthMomentTwistBound_of_quarticWeilInput`,
  `_R18FourthMomentTwist.lean:385`), whose **quadratic face is now LegendreCubicHasse alone**
  (round 20 Möbius discharge — the quartic `∏(t²−u)(t²−v)` splits by `t = d + 1/s` into a
  perfect-square scale times the Legendre cubic; `quartic_even_bound_of_cubicHasse`,
  `_R19HasseAudit.lean`, gives the integer-clean `Q² ≤ 9p` transfer). `LegendreCubicHasse F`
  (`_R19HasseAudit.lean:191`) is `|a_p(E)| ≤ 2√p` for `y² = s(s−u)(s−v)` — **verbatim absent
  from Mathlib**; `CubicStepanovUpper` (`_R20StepanovScaffold.lean:212`) is the pinned one-sided
  Stepanov statement that implies it (`legendreCubicHasse_of_stepanovUpper`; one-sided suffices
  by twist-negation halving), estimated ~1500–2500 self-contained lines, all Mathlib ingredients
  present, in-tree Stepanov engines reusable (`StepanovPointCountEngine.lean`,
  `HasseMultiplicityBridge.lean`, `StepanovHasseInterface.lean`). This is a *formalization* gap,
  not open mathematics.
- **The two-sided tower⟺sup equivalence at depth**: forward `tower_of_awaySupBound`
  (`AwaySupBound C ⟹ S_{r+2}^D ≤ (C·Σ)^r·S₂^D`, every r); reverse
  `supSplit_reverse_three_at_depth` (`_R20SupSplitReverse.lean:396`): at every rung
  `r+1 ≥ log₃ N` (N = away count ≤ q, so all rungs ≥ log₃ q — containing the prize depth
  `r ≈ ln q ≈ 0.91·log₃ q`) the sup-split constant `ρ ≤ 3` is an unconditional theorem, making
  **tower ⟺ AwaySupBound genuinely two-sided with constant 3 at depth**. Below `log₃ q` the
  magnitude-only reverse is refuted (`magnitudeOnly_reverse_unbounded`): the head rungs carry
  phase information no magnitude bookkeeping recovers.
- **Exact averaging identities (zero slack)**: `Σ_{s₀}‖I_H‖² = q·Σ` (round 13); cross-χ and
  cross-offset second moments exactly Wick-flat (`_R17TchiMomentIdentities.lean`); the second
  moment `Σ W² = n(q−n)` and `Σ W = 0` at deg=2 (`_R17Deg2WeilRung.lean`); the exact Jacobi
  bridge `g·W = 2·I_QR + n` off-diagonal makes corrected B at deg 2 **two-sidedly equivalent**
  to Karatsuba's shifted-thin-subgroup Legendre sup problem (`_R18Deg2FaceConverse.lean`).
- **hSig discharged**: energy equidistribution `nq ≤ 2mΣ` proven for `q ≥ 16m²n²`
  (`_R18SigmaEquidistribution.lean`); ChiDecompositionOff + GaussSumSizeBound proven
  (`_R19ChiDecomposition.lean`) — the r=2 rung is ONE named input away.

### 2.3 The constants (verified provenance)

- **Depleted-Wick r=2**: the named open Prop is `DepletedWickR2 ψ G H C`
  (`_R18PlateauLaw.lean:433`): `S₂^D·(q−1−|G|) ≤ C·(S₁^D)²`. Probe-measured `C = 0.93–1.10 × 3`,
  flat in deg (the plateau law is exactly the statement that this constant is flat); `C ≥ 1`
  forced. `DepletedWickR2 3` ⟹ the constant-3 r=2 rung with explicit positive margin (the R18
  bridge). ⚠️ **Provenance flag (FINDING F1)**: the dossier §29 phrase "C∞ = 3 exactly" is
  *probe/Gaussian-limit prose, not a Lean theorem* — `_R19DepletedConstant.lean` explicitly states
  it does NOT derive C = 3 (its route yields `K ≈ 32(C₄+1)·m`), and `DepletedWickR2` remains open.
  Treat "3" as the calibrated target constant, exactly matching the Gaussian limit, unproven.
- **Off-diagonal B constant**: measured `∈ [0.61, 1.61]` across all accessible scales (r15
  probes, no |H|-growth over ×1000).
- **Two-sided equivalence constant**: 3, and this one IS a theorem at depth ≥ log₃ q (r20).
- **Family quartic**: `FamilyQuarticCubicBound C₄` (`_R19DepletedConstant.lean:346`) probe-flat at
  `C₄ = 1.5`; its paired diagonal is proven at the stronger `|X|²` level; the `m`-uniform
  (`|X|²`-total) constant is **probe-refuted for every absolute-mass route** — recovering `|X|²`
  requires signed cross-quadruple cancellation (the wall's signature move at the family level).

### 2.4 Magnitude no-gos (what cannot work, proven)

- Magnitude-only reversal below depth `log₃ q`: refuted (`_R20SupSplitReverse.lean:253`).
- Per-tuple Weil at rungs r ≥ 3 in the gap β ∈ (4,6) ∋ prize: provably insufficient (each rung r
  needs a factor `n^{r−2}` beyond square-root cancellation; r=2 is the LAST Weil-closable rung).
- Tower welding with Problem A's banked energies: refuted — the banked `E₃(μ_n)` slice is
  ≤ 1e-4 of Wick; the dominant rung-3 mass is cross-coset self-referential
  (`_R18RungThreeDecomposition.lean`).
- Uniform Wick constant 1, and constant 2 at r=2 in the bulk: refuted with countermodels
  (r16/r17). The `|X|²` absolute-mass family bound: probe-refuted (r19).
- Depth-independence of the sup-split fixed point: no-go (`fixedPoint_depth_independent`,
  `_R20SubWickInterpolation.lean:253`). Sub-Wick monotonicity (`W_{r+1}-type ratio` decreasing)
  is NOT implied by the tower — the r20 "two-way collapse" claim was corrected by the skeptic to
  one-way; it stands as an independent live conjecture (log-convexity + ratio monotonicity of
  `S_r^D` are proven, `rungMoment_ratio_mono`).

---

## 3. What an expert must supply now (sharper than v1)

Problem A: as before — short (`≤ 2 ln q`-term) ±1-relations of `2^μ`-th roots of unity vanishing
mod p, within `K^r` of the Wick rate uniformly to `r ≈ ln q`, at `n = 2^30`, `p ≈ n^4`.

Problem B: **either** of the following now suffices (machine-checked bridges in place):

1. **`AwaySupBound C` directly with `C = O(polylog q)`** — a sup bound on the off-diagonal
   incidence field `sup_{s∉{0}∪μ_n} ‖Σ_{b∈H} conj(η_b)ψ(bs)‖² ≤ C·Σ‖η_b‖²`. By the two-sided
   depth theorem this is *equivalent* to the whole deep tower (constant 3); nothing more is
   needed.
2. **The head rungs `r ∈ [3, log₃ q)` of the diagonal-subtracted Wick tower**
   (`WickAwayAtWithConstant`, constant O(1) per rung). Each rung is a χ-twisted `2r`-tuple
   square-root-cancellation statement over the thin subgroup — rung 3 is a *family* cancellation
   across the genus-2 Weil sums `{∏_{i≤6}(s−y_i)}_{y⃗∈μ_n^6}` (vertical Sato–Tate flavor; the
   sixth moment sits AT the Wick main term empirically while per-tuple Weil is vacuous). These
   rungs are phase-deep: magnitude-only methods are provably insufficient below depth `log₃ q`.

Plus one pure formalization task (not open math): discharge `CubicStepanovUpper` (~2k lines of
Stepanov, in-tree engines available) to make the r=2 rung fully axiom-clean, and its
higher-order-χ analogue faces of `QuarticWeilInput` (open formalization + possibly Weil for
higher-genus quotients).

The deg=2 face of the whole problem is exactly Karatsuba's shifted-thin-subgroup problem
(two-sided bridge, explicit constants): nothing published beats √p at `n = p^{1/4}` worst-shift
(r17 literature sweep, web-verified).

---

## 4. Status table of every named Prop (verified against source, 2026-07-07)

| Named Prop / theorem | File (Frontier/) | Status |
|---|---|---|
| `WallHolds` | `_WallCapstone.lean:88` (= `_MomentOptimizedSupNorm.lean:222`, identical) | **OPEN** (Problem A) |
| `WorstCaseIncidenceBounded` + outer ⟺ | `_TwoSidedCapstone.lean` | proven (both directions) |
| `IncidenceFromWallGlue` | `_TwoSidedCapstone.lean:249` | named one-directional glue |
| `HyperplaneCancellation` (v1) | — | **never was a Lean Prop** (docstring-only; audited sound: no consumer) |
| `OffDiagonalHyperplaneCancellation` | `_R16OffDiagonalHyperplaneCancellation.lean:102` | **OPEN** (corrected B, per-offset form) |
| `AwaySupBound C` | `_R19RungRecursion.lean:257` (restated `_R20SubWickInterpolation.lean:94`) | **OPEN** — THE fixed point; = prize at `C = O(polylog q)` |
| `tower_of_awaySupBound` | `_R19RungRecursion.lean:265` | proven |
| `supSplit_reverse_three_at_depth` | `_R20SupSplitReverse.lean:396` | proven (⟹ two-sided const 3 at r ≥ log₃ q) |
| `magnitudeOnly_reverse_unbounded` | `_R20SupSplitReverse.lean:253` | proven refutation (head rungs phase-deep) |
| `WickForIncidenceAwayAt` (const `(2r−1)‼`) | `_R15IncidenceMomentInterchange.lean:425` | **REFUTED** as universal (r16 countermodels) |
| `WickAwayAtWithConstant` | `_R16DiagonalExactValue.lean:226` | **OPEN** at rungs 3..⌈ln q⌉ (r=0,1 proven; r=2 see below) |
| `StrongR2Rung` | `_R16IncidenceR2Rung.lean:258` | **REFUTED** at const 2 in β=4 bulk deg ≥ 8 (retained as strong interface) |
| r=2 rung, deg=2: `wickAwayAt_two_of_weil` | `_R17Deg2WeilRung.lean:1050` | proven modulo `WeilQuarticPairs` (classical) |
| `FourthMomentTwistBound` | `_R17QuadrupleWeilRung.lean:202` | **OPEN**; ⟸ `QuarticWeilInput` (proven bridge, `_R18FourthMomentTwist.lean:385`) |
| `QuarticWeilInput` (per χ) | `_R18FourthMomentTwist.lean:137` | quadratic face ⟸ `LegendreCubicHasse` **proven** (`_R20MobiusDischarge.lean:255`); **higher-order-χ faces OPEN** |
| `LegendreCubicHasse` | `_R19HasseAudit.lean:191` | **OPEN in Lean only** (Hasse genus 1 — absent from Mathlib; classical math) |
| `CubicStepanovUpper` | `_R20StepanovScaffold.lean:212` | **OPEN in Lean only** (pinned Stepanov formalization, ~2k lines; ⟹ `LegendreCubicHasse` proven, one-sided suffices) |
| `DepletedWickR2` | `_R18PlateauLaw.lean:433` | **OPEN** (target C = 3; C=3 ⟹ const-3 r=2 rung, proven bridge) |
| `FamilyQuarticCubicBound` | `_R19DepletedConstant.lean:346` | **OPEN** (probe-flat C₄ = 1.5; `|X|²` version probe-refuted) |
| sub-Wick monotonicity | `_R20SubWickInterpolation.lean` (log-convexity/ratio-mono proven) | **OPEN** independent conjecture (two-way-collapse claim corrected to one-way) |
| `n√q` unconditional partial B | `_R16UnconditionalIncidenceBound.lean:160` | proven |
| `incidenceSum_diag_exact` | `_R16DiagonalExactValue.lean` | proven (kills all-offset B) |

## 5. Findings from source verification (discrepancies vs. dossier prose)

- **F1 (substantive).** Dossier §29 "C∞ = 3 exactly" for the depleted constant is not backed by
  any Lean declaration; `_R19DepletedConstant.lean` explicitly disclaims deriving C = 3, and
  `DepletedWickR2` is open. The "3" is the probe-flat/Gaussian-limit calibration.
- **F2 (bookkeeping).** The dossier has duplicate section numbers (two §26, two §27, two §28,
  two §30) from the two concurrent 2026-07-07 sessions; cross-references by section number are
  ambiguous — cite DISPROOF tags instead.
- **F3 (minor).** `WallHolds` and `AwaySupBound` are each defined twice (identical statements,
  different namespaces: `_WallCapstone`/`_MomentOptimizedSupNorm`,
  `_R19RungRecursion`/`_R20SubWickInterpolation`). No unsoundness; consumers should prefer the
  capstone/R19 originals.
- **F4 (historical).** The v1 statement called `HyperplaneCancellation` a "named open `Prop`";
  the r16 audit shows it never existed as a Lean `Prop` — the v1 language overstated its
  formalization status (the audit also confirms nothing unsound consumed it).

## 6. Honesty contract

"Proven" above means: axiom-clean Lean (`#print axioms ⊆ {propext, Classical.choice,
Quot.sound}`, no `sorryAx`) surviving a real locked build, verified by grep against the named
files on branch `land-exhaust` (2026-07-07). Probes are labeled as probes; calibrated constants
are labeled as calibrations. Problem A (`WallHolds`) and corrected Problem B (`AwaySupBound` /
the head rungs) are named open `Prop`s. `CubicStepanovUpper` and `LegendreCubicHasse` are
classical mathematics with pinned formalization gaps — closing them closes the r=2 rung only.
**CORE OPEN, ON-BGK. No fabricated closure.**

<sub>🤖 #466 round 21 consolidation lane, 2026-07-07. Supersedes the 2026-07-04 v1 statement.
Dossier: `docs/kb/deltastar-DOSSIER-v3-2026-07-01.md` §25–§30; DISPROOF tags `466-r15-*` …
`466-r20-*`.</sub>
