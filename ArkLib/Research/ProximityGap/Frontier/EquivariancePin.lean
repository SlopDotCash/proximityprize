/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessSpread

/-!
# A5 — the Lean equivariance pin for the n=12 orbit-reduced εMCA profile (#334)

**Target.** The `probe_epsmca_orbit_exact_n12.py` probe computes the EXACT worst-case bad-γ
profile of `RS[F₁₃,12,6]` by orbit reduction (validated numerically against the n=4/n=6
ladder). The remaining *stretch* item is to **pin the orbit reduction in Lean**: prove the
group action (affine `x ↦ ax+b` on the evaluation domain, + scalar on codewords) leaves the
bad-γ count invariant, so the per-orbit representative count IS the worst-case count. This
turns the probe's exact numbers into a machine-checked statement.

**Reference.** Issue #334 A5 (the n=12 exact profile: δ=0→1, δ=0.083→2, δ=0.167→3, δ=0.25→12,
δ≥1/3→13). The probe is exact, not sampled; the Lean pin is the formal capstone.

**Substrate to consume.** `MCAWitnessSpread.unique_bad_gamma_common_witness` (the structural
obstruction the count must respect), `MCAThresholdLedger` (bracket engine), the evaluation-code
defs in `KKH26WitnessSpread.lean` (`evalCode`).

**Plan.** Define the affine action, prove bad-γ-count invariance (a `Finset.card` equality
under a bijection), then state the orbit-representative count = worst-case count as the pin.
Equivariance proofs are concrete finite-group / `Equiv`-on-`Finset` arguments.

**Honesty.** The equivariance lemma is a genuine `Finset` bijection result; no shortcuts.
-/

-- DISCHARGED (2026-06-11, #357 S3): the equivariance engine lives in
-- `ProximityGap.MCAEquivariance` (translation/scaling/γ-shift/permutation invariances,
-- probability transfer, `epsMCA_eq_iSup_subtype_of_reps`, and the RS rotation instance
-- `mcaEvent_rs_rotate`), with the strictly more general diagonal-twisted form in
-- `ProximityGap.MCAMonomialEquivariance` (`mcaEvent_monomial` — needed for the GRS-duality
-- twist `u(x) ↦ x·u(1/x)`, which merges the two extremal orbits at the exact-pin instance;
-- see DISPROOF_LOG O135). The n = 12 numeric capstone consumes these lemmas.
example : True := trivial
