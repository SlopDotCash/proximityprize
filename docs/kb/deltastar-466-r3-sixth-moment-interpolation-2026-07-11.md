# #466 r=3 R306: the LOG-ONLY rung — FullDFTFlatLog ∧ FourthMomentBound ⟹
# DistStratum within (1+log m); direct sixth moment machine-checked CIRCULAR;
# K₆ measured FLAT at the Gaussian value (2026-07-11)

Tenth brick of the r=3 arc (R297 → R306).  Coordinator target: SixthMomentBound.

## 1. Circularity (resolved first, machine-checked)

`sixthMoment_eq_tripleConv_energy` (Lean, generic over ZMod N):
`∑_a‖f̂(a)‖⁶ = N·∑_c‖(f⋆f⋆f)(c)‖²` — the sixth moment of the DFT **is** the
full triple-convolution energy, i.e. at `f = Sfun J` the r=3 core object
itself (R23 `TripleConvEnergyBound`, zero-removed).  Probe M3 confirms
numerically (machine precision, m = 9/12/15).  So a "SixthMomentBound" is an
INTERFACE, not an input; its only honest sources are strictly lower-order.

## 2. The log-only rung (formalized)

Hölder: `∑‖Ŝ‖⁶ ≤ (sup‖Ŝ‖²)·∑‖Ŝ‖⁴`.  Composing the R305 Gumbel-consistent
flatness (`FullDFTFlatSq B`, truth `B ≈ 0.8·log m`) with the R303/R304
quartic input (`FourthMomentBound K₄`, truth `K₄ → 2`):

* `sixthMomentBound_of_flatSq_and_fourth` : `SixthMomentBound (B·K₄)`;
* `distStratumEnergyBound_of_sixthMoment` : `K₆ ⟹ C = 3K₆ + 1215`;
* **headline** `distStratumEnergyBound_of_flatLog_and_fourthMoment`:
  `FullDFTFlatLog A ∧ FourthMomentBound K₄ ⟹
   E_DIST ≤ (3·A·K₄·(1+log m) + 1215)·m³·q³` — **LOG-ONLY loss**, improving
  both the R303 `√m` route and the R305 `log³` route.

## 3. The decisive measurement (probe `probe_466_r3_sixth_moment.py`, m ≤ 1200)

* `K₆ := ∑‖Ŝ‖⁶/(m⁴q³)` directly: median rises and SATURATES at 4.7–5.4,
  tracking the complex-Gaussian prediction `6·((m−2)/m)³ → 6` from below;
  max ≤ 9.4, no growth trend at large m.  Simultaneously `K₄_med → 1.85` vs
  Gaussian `2·((m−2)/m)² → 2`.  **The averages are Gumbel-immune and match
  the equidistribution model QUANTITATIVELY** — the r=3 core truth has an
  absolute constant `C_core ≈ 3·K₆ ≈ 15–20` (cf. R23's calibration comment
  "C = 40 comfortable": now explained as ≈ 3·E|G|⁶ + slice terms).
* Composed-route waste `(B·K₄)/K₆`: 1.19 (m=9) → 2.10 (m=1200) — exactly the
  `~0.8·log m / const` sup-inflation, as predicted.  The Hölder chain is
  tight up to that log; no further slack hides in the composition.

## 4. Downstream tolerance (checked in-tree) and precise status

`TripleConvEnergyBound` and its full consumer chain (R23 → R27:
`sextic_moment_of_tripleConvEnergyBound`, `sup_pureFace_of_…`, R26 pointwise
targets) all take `C` as a FREE parameter — formally log-tolerant.  At any
fixed prize modulus the `(1+log m)` factor is a concrete number
(log 2³⁰ ≈ 20.8), giving a composed constant `≈ O(10³)` with probe-calibrated
`A ≈ 1–2, K₄ ≈ 2`.

**PRECISE STATUS OF THE r=3 RUNG (end of R297 → R306 arc):**
* CLOSED MODULO two named inputs at a `(1+log m)` loss:
  `FullDFTFlatLog A ∧ FourthMomentBound K₄` (both probe-calibrated with
  matching Gaussian-model predictions; both strictly weaker than the core);
* the ABSOLUTE-constant form remains open and is now precisely located:
  it is the interface `SixthMomentBound O(1)` = the core verbatim
  (circularity theorem), whose only non-circular decomposition known pays
  the Gumbel log through the sup.  Removing that log = replacing the sup by
  an a-average in the Hölder step = genuine new cancellation between the
  heavy modes of `‖Ŝ‖²` and `‖Ŝ‖⁴` — the sharpest remaining open question
  of the lane.

## 5. Formal kernel and probe

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R306SixthMomentInterpolation.lean`
— axiom-clean (`[propext, Classical.choice, Quot.sound]`, manual reads on all
four, no sorryAx), pg-iterate 7s.  Theorems: `sixthMoment_eq_tripleConv_energy`,
`SixthMomentBound` (interface), `sixthMomentBound_of_flatSq_and_fourth`,
`distStratumEnergyBound_of_sixthMoment`,
`distStratumEnergyBound_of_flatLog_and_fourthMoment`.

Probe: `scripts/probes/probe_466_r3_sixth_moment.py`
(`scripts/probes/_out_466_r3_sixth_moment.txt`).

CORE OPEN, ON-BGK.  No fabricated closure.

DISPROOF tag: `466-r3-sixth-moment-log-only-rung`.
