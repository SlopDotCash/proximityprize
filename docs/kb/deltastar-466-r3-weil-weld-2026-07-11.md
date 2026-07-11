# #466 r=3 R308: the Weil weld — the moment stack IS the R27 tower (master
# identity, all r); FourthMomentBound DISCHARGED modulo the ladder's existing
# TwoCharacterWeilInput; absolute-C r=3 reduces to the r=4 tower rung ALONE
# (2026-07-11)

Twelfth brick, closing the R297 → R308 arc's dependency graph.

## 1. YES — the proven-mod-Weil r=2 machinery discharges FourthMomentBound

The coordinator's precision question, answered by an exact object match:

* `iterConv J 1 = Sfun J` (`iterConv_one_eq_sfun`) — R27's iterated
  convolution is the convolution powers of the zero-removed ladder;
* `hatF_iterConv`: `(J^{∗r})^(a) = Ŝ(a)^r` (DFT diagonalizes the recursion);
* **master identity** (`evenMoment_eq_iterConv_energy`, all r, probe-exact
  at r = 1..4): `∑_a‖Ŝ(a)‖^{2r} = m·∑_c‖(J^{∗r})(c)‖²` — the R302–R307
  moment stack and the R27 `IterConvEnergyWick` ladder are the SAME objects,
  Wick factor `r!` = complex-Gaussian `E‖G‖^{2r} = r!·var^r`.
* welds: `IterConvEnergyWick@2 C₂ ⟹ FourthMomentBound (2C₂²)`;
  `IterConvEnergyWick@4 C₄ ⟹ EighthMomentBound (24C₄⁴)`.
* In-tree source: R144's
  `iterConvEnergyWick_two_of_twoCharacterWeilInput_and_coeffEnvelope_splitBudget`
  derives the r=2 rung for the Jacobi ladder from the NAMED classical
  `TwoCharacterWeilInput` under explicit cap/budget hypotheses.  Hence:
  **`TwoCharacterWeilInput (+ caps) ⟹ FourthMomentBound (2C²)`** — the
  quartic input is classical-modulo-caps, not a new open object.

## 2. The reconciliation with R304's per-tuple refutation (exact mechanism)

The incidence r=2 rung (`wickAwayAt_two_of_weil`, needs `√q ≥ 16n²`) and the
ladder r=2 rung (R144, needs the split-budget caps) succeed because their
fourth-moment expansions retain a FREE F_q-variable — a length-q complete
character sum per tuple, Weil-boundable on curves, with the regime condition
letting the q-average beat the tuple count.  R304's obstruction was about a
DIFFERENT decomposition of the same object: the ℤ/m-mode average, where the
per-quadruple terms are Jacobi products of modulus exactly q² with no free
F_q-variable.  Both statements are correct; the Weil strategy transfers
through the t-variable expansion, not through the mode expansion.  At r = 4
the two-character route has no in-tree discharge (R144 stops at r ≤ 3) and
the depth bookkeeping worsens; r=4 remains open.

## 3. Headline and final dependency graph

`distStratum_absoluteC_of_towerRungs`:
  `IterConvEnergyWick J q 2 C₂ ∧ IterConvEnergyWick J q 4 C₄ ⟹
   DistStratumEnergyBound (3·√(2C₂²·24C₄⁴) + 1215)` — absolute constant.

**Final graph of the absolute-C r=3 DIST rung:**

  absolute-C r=3 ⟸ TwoCharacterWeilInput (classical, named, capped — R144)
                    ∧ IterConvEnergyWick@4 (the SINGLE remaining open average)

Probe (`probe_466_r3_weil_weld.py`): master identity exact at r = 1..4;
implied tower constants `C₂: 0.68 → 0.96`, `C₄: 0.52 → 0.89` over
m = 9 → 1200 — both sub-Gaussian, rising toward the Gaussian value 1.  The
open r=4 rung is calibrated at `C₄ ≈ 0.9` (Wick constant ≈ 1), i.e. the
remaining open statement is "the 4-fold self-convolution of the Jacobi
ladder is Wick-flat", the exact r=4 analogue of what R144 proves mod Weil
at r=2.

## 4. Formal kernel and probe

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_R308FourthMomentWeilWeld.lean`
— axiom-clean (`[propext, Classical.choice, Quot.sound]`, manual reads on all
seven, no sorryAx), pg-iterate 6s.  Theorems: `iterConv_one_eq_sfun`,
`iterConv_succ_eq_conv2`, `hatF_iterConv`, `evenMoment_eq_iterConv_energy`,
`fourthMomentBound_of_iterConvWick_two`,
`eighthMomentBound_of_iterConvWick_four`, `distStratum_absoluteC_of_towerRungs`.

Probe: `scripts/probes/probe_466_r3_weil_weld.py`
(`scripts/probes/_out_466_r3_weil_weld.txt`).

CORE OPEN, ON-BGK (the wall is now r=4-shaped for this lane).
No fabricated closure.

DISPROOF tag: `466-r3-weil-weld-fourth-moment-classical`.
