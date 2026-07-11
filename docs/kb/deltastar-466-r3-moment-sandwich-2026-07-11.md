# #466 r=3 R307: the moment sandwich — the ABSOLUTE-C rung from two a-average
# inputs (no sup, no log); K₈ measured flat; sandwich tight to 3–12%
# (2026-07-11)

Eleventh brick, capstone of the r=3 arc (R297 → R307).

## 1. The mechanism

R305: the sup carries a Gumbel `log m` — pointwise flatness can never give
absolute C.  R306: Hölder pays that log.  R307 removes the sup entirely by
Cauchy–Schwarz in the MODE variable:

  `∑_a‖Ŝ‖⁶ = ∑_a‖Ŝ‖²·‖Ŝ‖⁴ ≤ √(∑_a‖Ŝ‖⁴)·√(∑_a‖Ŝ‖⁸)`

— both factors are a-averages, Gumbel-immune.  With `FourthMomentBound K₄`
(r=2-class) and the new `EighthMomentBound K₈` (`∑‖Ŝ‖⁸ ≤ K₈·m⁵·q⁴`):

  **`E_DIST ≤ (3·√(K₄·K₈) + 1215)·m³·q³`** — ABSOLUTE constant
  (`distStratum_absoluteC_of_fourth_and_eighth`).

## 2. Gaussian bookkeeping and measurement (probe
   `probe_466_r3_moment_sandwich.py`, m ≤ 1200)

Modes ~ complex Gaussian variance `s²q` (`s² = m−2`): `E‖G‖^{2k} = k!·var^k`
⇒ predictions `K₄ → 2`, `K₆ → 6`, `K₈ → 4! = 24` (× `((m−2)/m)^k`).
Measured medians: `K₄ → 1.85`, `K₆ → 4.7–5.4`, `K₈ → 14–19` — all FLAT in m
(sub-Gaussian, consistent ceilings), `K₈` max noisy (up to 58) but trendless.
Sandwich tightness `√(K₄K₈)/K₆ ∈ [1.03, 1.12]` — the Cauchy–Schwarz step
loses only 3–12%.  Composed absolute constant ≈ 1220–1233 (dominated by the
slice-term 1215; the moment part contributes `3√(K₄K₈) ≈ 16`).

## 3. Honest tower position

`eighthMoment_eq_quadConv_energy` (formalized, generic):
`∑_a‖f̂‖⁸ = N·∑_c‖(f⋆f⋆f⋆f)(c)‖²` — the octic input is the **r = 4 rung of
the R27 `IterConvEnergyWick` ladder** in DFT coordinates (its Wick factor
`4! = 24` is exactly the Gaussian prediction; `IterConvEnergyWick` at r=4
with constant `C` gives `K₈ = 24·C⁴` up to zero-removal bookkeeping).  The
sandwich SHIFTS the open content — r=3 pinched between r=2-class and the
r=4 average — rather than closing it.  The shift is structurally decisive:
the REFUTED sup-shaped input is replaced by rungs of the existing tower
whose averages are measured Gaussian-flat, and the Gumbel mechanism (the
only refutation engine the arc found on the moment side) provably inflates
only sups, never averages.

## 4. FINAL HONEST LADDER of the r=3 rung (arc summary R297 → R307)

Named inputs (all instantiation-pinned, probe-calibrated, Gumbel-immune
unless noted):
* `FourthMomentBound K₄` (r=2-class; truth ≈ 2; sources:
  `OffDiagQuadrupleBound K ⟹ K₄ = 2+K`, R304);
* `EighthMomentBound K₈` (r=4 tower rung; truth ≈ 15–24);
* `FullDFTFlatLog A` (sup-shaped, Gumbel-calibrated, A ≈ 1–2);
* interface: `SixthMomentBound` = the core verbatim (R306 circularity).

Rungs:
* **ABSOLUTE-C**: `K₄ ∧ K₈ ⟹ C = 3√(K₄K₈) + 1215` (this brick);
* log-only: `FullDFTFlatLog ∧ K₄ ⟹ C = 3AK₄(1+log m) + 1215` (R306);
* √m: `K₄` alone (R303); log³: `FullDFTFlatLog` alone (R305).

Refuted with mechanism: absolute pointwise flatness (R305 Gumbel);
per-variety Weil–Deligne at any order (R304 — Möbius kills the mains, errors
q^{3/2} above signal); cyclotomic closed forms (R301); the m²q² fourth-moment
scale (R303).  Exact identities formalized: slice/Newton mode identity
(R302), 4th = r=2 quadruple energy (R303), 6th = triple-conv energy = core
(R306), 8th = quad-conv energy = r=4 rung (R307), Fermat fiber products
(R304, probe).

**The r=3 rung's open content is now exactly two Wick-average statements
about the Jacobi angle family (r=2-class and r=4-class), both measured
Gaussian-exact to m = 1200, feeding an absolute-constant machine-checked
pipeline.**  CORE OPEN, ON-BGK.  No fabricated closure.

## 5. Formal kernel and probe

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R307MomentSandwich.lean`
— axiom-clean (`[propext, Classical.choice, Quot.sound]`, manual reads on all
four, no sorryAx), pg-iterate 5s.  Theorems: `sixthMoment_sandwich`,
`eighthMoment_eq_quadConv_energy`, `EighthMomentBound` (named input),
`sixthMomentBound_of_fourth_and_eighth`,
`distStratum_absoluteC_of_fourth_and_eighth`.

Probe: `scripts/probes/probe_466_r3_moment_sandwich.py`
(`scripts/probes/_out_466_r3_moment_sandwich.txt`).

DISPROOF tag: `466-r3-moment-sandwich-absolute-c`.
