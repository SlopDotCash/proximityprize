# #466 r=3 R303: fourth-moment interpolation — the DIST rung within √m of ONE
# O(1)-calibrated moment bound; m²q² target refuted-by-scale; Möbius spares the
# diagonal (2026-07-10)

Seventh brick of the r=3 session (R297 → R303), successor to the R302 trace
formula.  Coordinator target: `∑_a‖Ŝ(a)‖⁴ ≤ K₄·m²·q²` + main-term/Weil split +
interpolated rung.

## 1. Scale correction (refutation of the m²q² target, with mechanism)

`∑_a‖Ŝ(a)‖² ≈ m²q` (R302 Parseval, exact up to the ≤2 degenerate rungs), so
power-mean forces `∑_a‖Ŝ‖⁴ ≥ (m²q)²/m = m³q²`; the EXACT diagonal
({j₁,j₂} = {k₁,k₂} additive quadruples) contributes `2(1−2/m)²·m³q²` — probe
measures the diagonal share at `≈ 1.12·m³q²` for m = 9 rising toward 2.  The
correct flat scale is **K₄·m³·q²**.

## 2. Möbius at the 4th moment (the coordinator's question, resolved positively)

Unlike the sextic (R302: `∑_{d∣m}μ(m/d) = 0`, pure error term), the 4th-moment
diagonal has ratio exactly `1 ∈ (F_q^*)^d` for every `d∣m`, so its Möbius
weight is `∑_{d∣m} d·μ(m/d) = φ(m) ≠ 0` — **the main term survives**.  The
error term is the off-diagonal additive-quadruple sum; measured off/diag share
∈ [−0.4, +1.0], no growth in q.

## 3. The exact identity (F1) and the honest input

`∑_a‖Ŝ(a)‖⁴ = m·∑_c‖(Sfun J ⋆ Sfun J)(c)‖²` — the fourth moment IS the r=2
zero-removed self-convolution (additive-quadruple Jacobi) energy.  Probe:
machine-precision at m = 9, 12, 15, 18, all primes ≤ 1200, every character.
Each off-diagonal quadruple term has modulus EXACTLY q², so there is no
per-tuple Weil saving (checked against the refuted per-tuple class in
DISPROOF_LOG — we name NO such input); the honest named input is the moment
bound itself:

  `FourthMomentBound K₄ : ∑_a‖Ŝ(a)‖⁴ ≤ K₄·m³·q²`

Measured: `K₄ ∈ [0.67, 3.2]` across m = 9/12/15/18, per character and
Galois-max, flat in q.  Hierarchy (Lean): `FullDFTFlat K ⟹ K₄ = K⁴`
(strictly weaker input); unconditional calibration `K₄ = m`.

## 4. The interpolated rung (main theorem, axiom-clean)

`distStratumEnergyBound_of_fourthMoment`:
  `FourthMomentBound K₄ ⟹ DistStratumEnergyBound ((3·K₄·√K₄ + 1215)·√m)`,
i.e. `E_DIST ≤ C(K₄)·√m·m³·q³` — the full r=3 DIST rung within a `√m` loss
from one O(1)-calibrated quadratic-moment bound.  Route: ℓ³-vs-ℓ² interpolation
`∑f³ ≤ √(∑f²)·∑f²` (`sum_cube_le_sqrt_mul`) applied to `f = ‖Ŝ‖²` inside the
R302 mode identity, with the slice terms priced unconditionally as before.
With the unconditional `K₄ = m` the theorem recovers an `m^{5/2}`-scale
envelope — strictly between the trivial `m²`-loss baseline and the lossless
`FullDFTFlat` route.  The rung ladder of inputs is now:

  `FullDFTFlat K (pointwise, lossless)  ⟹  FourthMomentBound K⁴ (√m loss)
    ⟹ unconditional (K₄ = m, ~m^{5/2} loss)`

## 5. Formal kernel and probe

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R303FourthMomentInterpolation.lean`
— axiom-clean (`[propext, Classical.choice, Quot.sound]`, no sorryAx),
pg-iterate 16s.  Theorems: `hatF_conv2`, `fourthMoment_eq_selfConv_energy`,
`FourthMomentBound` (named input), `fourthMomentBound_of_fullDFTFlat`,
`fourthMomentBound_unconditional`, `sum_cube_le_sqrt_mul`,
`distStratumEnergyBound_of_fourthMoment`.

Probe: `scripts/probes/probe_466_r3_fourth_moment.py`
(`scripts/probes/_out_466_r3_fourth_moment.txt`).

## 6. Status and next

The r=3 open core now has a graded input ladder living entirely inside
finite-Fourier land: 2nd moment (closed, Parseval) → 4th moment (open,
O(1)-calibrated, = r=2 quadruple energy with surviving main term) → pointwise
flatness (open, lossless).  Natural next probe: the off-diagonal quadruple sum
directly (its Galois average is again Möbius-weighted point counts on the
3-fold fiber product of Fermat curves — a FIXED variety family where the
diagonal main term survives, so a genuine main+error split exists; the open
question is whether its error admits a uniform-in-m Weil/monodromy treatment).
CORE OPEN, ON-BGK.  No fabricated closure.

DISPROOF tag: `466-r3-fourth-moment-interpolation`.
