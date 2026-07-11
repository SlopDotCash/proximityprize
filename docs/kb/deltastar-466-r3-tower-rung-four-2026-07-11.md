# #466 r=3 R309: the r=4 extension — curve-Weil lag machinery BREAKS at
# depth 2 AND the uniform two-character input is contradicted at depth 1;
# the diagonal-separated lag ENDGAME lands anyway (two lag-sup inputs at
# measured scales ⟹ absolute-C rung) (2026-07-11)

Thirteenth brick, closing the R297 → R309 arc.  Coordinator target: extend
R144's split-budget machinery from r ≤ 3 to r = 4.

## 1. Where r enters (read from R30/R31/R35/R144, then measured)

The r=2 route: conv/lag Parseval `E₂ = Σ_t‖lag₁(t)‖²`; the R30 identity
collapses each off-zero lag into per-(u,t) TWO-character sums with ONE free
F_q-variable; `TwoCharacterWeilInput` prices each at `C√q`.  Two structural
facts found:

* **R35/R144's budgets lump lag-0 into `L`**: since `lag₁(0) = Σ‖J‖² ≈ mq`,
  their budget forces the selfconv constant ≥ ~2m² (tower C ~ m) — the
  stated hypotheses cannot be met at absolute constants; the sharp form
  needs the diagonal separated (this file's consumers).
* **The uniform `TwoCharacterWeilInput` is CONTRADICTED** (probe): measured
  `sup_{t≠0}‖lag₁(t)‖` has q-exponent 1.02–1.05 (Θ(q), not √q); implied C
  grows like √q.  Mechanism: `|J_j|² = q` makes `lag₁(t) = q·Σ_j e^{iΔθ}`,
  and the two-character family contains DEGENERATE members (the rational
  function becomes an m-th power) contributing Θ(q) each.  Honest classical
  content: Weil on nondegenerate members + exact counting of degenerates ⇒
  `L ≈ c·√m·q`, c = O(1) (measured c ∈ [1, 3.2] ≈ √m at m = 9, 12; H-coset
  shifts are the SMALLEST lags — no HD spike).

## 2. The r=4 refutation (the coordinator's step-2 question)

Depth-2 lags `lag₂(t) = Σ_c W_{c+t}·conj(W_c)` (`W = S⋆S`): measured
q-exponent **2.0–2.1** — pure Gaussian-random `~m^{3/2}q²`; neither curve
(1/2) nor surface-Deligne (1) rigidity.  Mechanism: the depth-2 lag is
quartic in J; linearization needs two free F_q-variables and the family
degenerates — each depth doubles the character degree, and only depth 1
collapses to one-variable curve sums.  **A `FourCharacterWeilInput`-style
r=4 extension is FALSE at any sub-random scale; none is named.**

Bonus rigidity finding: at fixed m, q ≫ m³, `K₄ ↓ toward (1−2/m)²` and
`K₈ ↓ ~1` — the Gaussian values (2, 24) are small-q artifacts; at prize
scale the moment constants are SMALLER than Gaussian (Weil-rigid averages,
rare per-character spikes).

## 3. The endgame (landed) — why it survives both refutations

The diagonal-separated consumers have `√m` of slack against the measured
scales:

* `fourthMomentBound_of_offZeroLag`: `OffZeroLagBound L` + `L² ≤ K·m·q²`
  (measured L ≈ c√m·q ⇒ K = c²) ⟹ `FourthMomentBound (1 + K)`;
* `eighthMomentBound_of_offZeroLags`: + `OffZeroQuadLagBound L₂` +
  `L₂² ≤ K'·m³·q⁴` (measured L₂ ≈ c'm^{3/2}q² ⇒ K' = c'²) ⟹
  `EighthMomentBound ((1+K)² + K')`;
* **ENDGAME** `distStratum_absoluteC_of_offZeroLags`:
  `E_DIST ≤ (3·√((1+K)((1+K)² + K')) + 1215)·m³·q³` — absolute-C from two
  lag-sup inputs, each a `√m`-saving over its trivial bound.
* Identities formalized: `hatF_autocorr`, `fourthMoment_eq_lag_energy`
  (generic lag Parseval; applied at f = S and f = W = S⋆S it yields the 4th
  and 8th moments; probe L1/L2 machine-precision).

## 4. FINAL DEPENDENCY GRAPH of the absolute-C r=3 rung (arc close-out)

Three equivalent-strength two-input routes (interchangeable via R307/R308
identities): lag pair {OffZeroLagBound, OffZeroQuadLagBound} ⟺ moment pair
{FourthMomentBound, EighthMomentBound} ⟺ tower pair {IterConvEnergyWick@2,
@4}.  Downstream: `DistStratumEnergyBound C ⟹ TripleConvEnergyBound
(2C + 288)` (R300).  REFUTED as sources across the arc: absolute pointwise
flatness (Gumbel, R305); per-variety Weil–Deligne at any order (R304);
uniform TwoCharacterWeilInput at O(1) (R309); depth-2 curve/surface lag
rigidity (R309); cyclotomic closed forms (R301); m²q² fourth-moment scale
(R303).  Every open input is a `√m`-saving cancellation statement about the
Jacobi angle family, measured Gaussian-or-better to m = 1200 / q = 36000.

## 5. Formal kernel and probe

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R309TowerRungFour.lean`
— axiom-clean (`[propext, Classical.choice, Quot.sound]`, manual reads on
all six, no sorryAx), pg-iterate 6s.  Theorems: `hatF_autocorr`,
`fourthMoment_eq_lag_energy`, `norm_autocorr_zero_le`,
`OffZeroLagBound`/`OffZeroQuadLagBound` (named inputs),
`fourthMomentBound_of_offZeroLag`, `eighthMomentBound_of_offZeroLags`,
`distStratum_absoluteC_of_offZeroLags`.

Probe: `scripts/probes/probe_466_r3_tower_rung_four.py`
(`scripts/probes/_out_466_r3_tower_rung_four.txt`).

CORE OPEN, ON-BGK.  No fabricated closure.

DISPROOF tag: `466-r3-tower-rung-four-lag-endgame`.
