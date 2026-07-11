# #466 r=3 R305: FullDFTFlat at scale — ABSOLUTE-K REFUTED (Gumbel growth
# measured to m = 1200); corrected quasi-flat ladder landed (cubed-loss law
# E ≤ 9B³·m³q³) (2026-07-11)

Ninth brick of the r=3 arc (R297 → R305).  Coordinator question: is
`FullDFTFlat K = O(1)` true?  Answer: **NO** — and the corrected, honest,
growth-tolerant ladder is now formalized.

## 1. Theory (done before measuring, then confirmed)

`Ŝ(a) = m·T₋ₐ + 1`, `m·T_α = ∑_e ζ^{−eα}J_e`: a DFT over exactly **m modes**
of the m Jacobi angles.  Under Katz vertical equidistribution the angles are
iid-uniform-like ⇒ each mode ≈ complex Gaussian of variance `mq`, modes
asymptotically independent ⇒ `K := sup_a‖Ŝ(a)‖²/(mq)` ≈ max of m Exp(1)-like
variables ⇒ **K ~ log m + Gumbel, independent of q**.  (No `log q`: the sup
ranges over the m modes, not over `q/m` coset residues.)

## 2. Measurement (probe `probe_466_r3_fulldftflat_scaling.py`, validated
   against the R302 exact values; m ∈ {9,…,1200}, 5 primes × 3 characters
   per m; O(q) per sample via direct coset sums, no FFT needed)

* `K_med`: 1.61 (m=9) → 2.74 (m=24) → 3.60 (m=108) → 4.57 (m=240) → 5.40
  (m=1200): **monotone growth** — `FullDFTFlat` with absolute K REFUTED.
* `K_med / log m ∈ [0.66, 0.91]`, no trend — consistent with the Gumbel law
  at slope ≈ 0.79 (fit `K = −0.11 + 0.79·log m`, resid sd 0.35).  A power
  fit `1.12·m^{0.235}` is statistically comparable at this range; either
  form is genuine growth.  Distinguishing log vs m^ε would need m ≫ 10⁴.
* Fixed-m q-scans (m = 60, 120; q to 4201): fluctuation band, NO q-trend —
  confirming the no-log-q prediction.
* Extremal-mode structure: argmax at a = 0 frequency → 0 as m grows —
  the max is attained at a GENERIC mode (random-extreme structure, no
  structured resonance to exploit or to fear).

## 3. Consumer tolerance and the corrected ladder (formalized)

R302's reduction is K-parametric, so nothing collapses — it recalibrates.
With the squared budget `B := K²`-scale input
`FullDFTFlatSq B : ∀a, ‖Ŝ(a)‖² ≤ B·m·q`:

* **cubed-loss law** (`distStratumEnergyBound_of_flatSq_cubed`): for `B ≥ 9`,
  `FullDFTFlatSq B ⟹ DistStratumEnergyBound (9·B³)` — the exact tolerance
  arithmetic in one theorem.  Absolute C ⟺ bounded B (now known false);
  `B = A(1+log m)` ⟹ `C ≤ 9A³(1+log m)³` (quasi-flat, sub-polynomial);
  `K = m^{1/6}` (B = m^{1/3}) ⟹ `C ~ 9m` ⟹ `E ≤ 9m⁴q³` — does NOT fit the
  strict absolute-C target.
* Corrected named input `FullDFTFlatLog A` (Gumbel-consistent) with consumer
  `distStratumEnergyBound_of_flatLog`: `E ≤ 9·(A(1+log m))³·m³·q³`.
  Probe calibration: A ≈ 0.9 covers all medians; A ≈ 2 covers all maxima
  sampled.

**Strategic consequence (recorded honestly):** the strict absolute-C form of
the DIST rung provably cannot come from pointwise flatness alone — the sup is
genuinely log-inflated.  Any route to absolute C must exploit cancellation in
the a-AVERAGE beyond the sup, i.e. the moment ladder (R303 `FourthMomentBound`
/ R304 `OffDiagQuadrupleBound`, both still O(1)-consistent in the probes, and
NOT contradicted by the Gumbel sup: a log-heavy single mode contributes only
`(log m)³·m²q³ ≪ m³q³` to the sextic sum).  The moment route is now the ONLY
candidate for the absolute-constant rung; the flatness route is settled as
quasi-flat (log³ loss).

## 4. Formal kernel and probe

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R305FullDFTFlatCalibration.lean`
— axiom-clean (`[propext, Classical.choice, Quot.sound]`, manual reads on all
five, no sorryAx), pg-iterate 5s.  Theorems: `fullDFTFlat_of_sq`,
`distStratumEnergyBound_mono`, `distStratumEnergyBound_of_flatSq`,
`distStratumEnergyBound_of_flatSq_cubed`, `distStratumEnergyBound_of_flatLog`.

Probe: `scripts/probes/probe_466_r3_fulldftflat_scaling.py`
(`scripts/probes/_out_466_r3_fulldftflat_scaling.txt`).

CORE OPEN, ON-BGK.  No fabricated closure.

DISPROOF tag: `466-r3-fulldftflat-absolute-k-refuted`.
