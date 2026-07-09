/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonListBound

/-!
# B2 — curve decodability ([GG25] Def 3.1) → [Jo26] curve-decodability half (#334)

**Target.** Formalize **[GG25] Definition 3.1 (curve decodability)** from scratch, then use
it to prove the [Jo26] curve-decodability half of the generator-factor bound. This is its own
**multi-brick project**: (1) the definition (a code is curve-decodable if low-degree curves
through close words are themselves close, with controlled list size), (2) the basic closure
lemmas, (3) the [Jo26] consumer.

**Reference.** [GG25] ePrint 2025/2054 Def 3.1; [Jo26] ePrint 2026/891 (the curve half of
Thm 4.2). The affine-line *exact* case is already in-tree as `epsMCA_interleaved_eq`
(`InterleavingStabilityMCA.lean`) — B2 generalizes lines to higher-degree curves.

**Substrate to consume.** `JohnsonListBound` (the up-to-Johnson list-size side),
`epsMCA_interleaved_eq` (the line base case), `MCAThresholdLedger` (the bracket engine).

**STATUS (2026-06-14, wf407/B2-curve).** This scaffold is SUPERSEDED — the B2 lane is far
along. The canonical work is NOT here; locate declarations by name (`git grep -il curvedecodab`):

* `ProximityGap/GG25CurveDecodability.lean` — `def CurveDecodable` ([GG25] Def 3.1 / [Jo26]
  Def 2.7), `curveCloseSet`, monotonicity, non-vacuity. (axiom-clean)
* `ProximityGap/CurveDecodability.lean` — the full [Jo26] §5 marked-variant + interleaving
  transfer (`markedCurveDecodable_interleaved`, Lemma 5.2 interpolation, Thm 5.5 equivalence).
* `ProximityGap/GG25MCAFromCurveDecodability.lean` — [GG25] Thm 3.3: curve-decodability ⟹
  all-seeds-close (the MCA spread).
* `ProximityGap/MCACurveEvent.lean` — the curve MCA error `mcaEventCurve` / `epsMCACurve`
  (the prize-relevant `ε_mca` object), with `epsMCACurve_two_eq_epsMCA` (L=2 ↦ affine line).
* `Frontier/WF407_B2-curve.lean` — **the seam between the two**: codeword stacks are MCA-clean
  (`mcaEventCurve_false_of_rows_mem`, `epsMCACurve_term_codewordStack_eq_zero`), the negation
  characterization (`not_mcaEventCurve_iff_stackAgrees`), and the curve-decodability-facing
  sufficient condition (`not_mcaEventCurve_of_full_stackAgrees`). All axiom-clean.

What remains open is NOT a missing definition: it is the *quantitative* `epsMCACurve` bound for
explicit smooth-domain plain RS (the δ* core — GG25 supplies curve-decodability only for
folded/multiplicity/random-RS/subspace-design codes), unchanged by this lane.

**Honesty.** Definitions are free; each derived bound is a named obligation until proven.
-/

-- Superseded scaffold; canonical declarations live in the files listed above.
example : True := trivial
