/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ50WitnessRealizability

/-!
# SYZ52 — lift test of the SYZ50 band-realizable interior `ι = 2` witnesses

## Where this sits

SYZ50 established that at rate `1/2` the balanced-interior region **meets** the band-realizable
polytope, the smallest realizable balanced `(4,4,4)`, `t = 2` config lives on `μ₁₄ ⊂ 𝔽₂₉`, and that
config carries **357** genuine constant-syzygy on-domain `ι = 2` witnesses.  SYZ50 relocated the
open gate to the **over-budget-stack lift**: does the `ι = 2` syzygy let a stack beat the pencil
accounting via extra scalar coincidences?

SYZ52 runs that lift test numerically (`probe_syz52_witness_lift.py`, over the *actual*
`μ₁₄ ⊂ 𝔽₂₉` domain so the cyclotomic syzygy is realized) and isolates the mechanism.  This file
proves the **structural core** of the verdict.

## The decisive numerical verdict (probe, exact word-level, both `mcaEvent` clauses)

* **Cross-validation.**  The same machinery reproduces the SYZ32 crack *exactly*: on the SYZ31
  near-duplicate cluster (`n = 16`, `k = 8`, `s = 11`) the merge holds on `1000/1000` stacks, every
  stack is `mca`-correlated, and the max `mca`-bad count is `0` (raw pool `18`) — the SYZ32
  stack-vacuous verdict, verbatim.
* **The `μ₁₄` interior witnesses behave oppositely.**  Deficiency `d = 1`, the three cores
  **never merge** (`merge_tested = 0`), **no** stack is `mca`-correlated, and the max `mca`-bad
  scalar count reaches **`≥ 19`** across the 357 witnesses — far *above* the SYZ22 pencil budget
  `n − 1 = 13`, the pencil-yield ceiling `∑(n − sᵢ) = 3·(14 − 10) = 12`, *and* `n = 14`.
* **Control.**  Random pencil stacks at the same `n = 14`, `k = 7`, `s = 10` have max non-`mca`
  bad count `6` (mean `1.07`, p95 `3`): the strip's small-bad-set behaviour holds generically, so
  the witness stacks' `≥ 19` is a genuine effect of the `ι = 2` general-position geometry, **not** a
  small-field artifact.  (Radius `δ = 4/14 = 2/7 ≈ 0.286` sits right at the Johnson edge
  `1 − √(1/2) ≈ 0.293`, where large proximity-gap bad-sets are theory-consistent — so this defeats
  the *merge/yield accounting*, it is not a proof of strip falsification.)

## The mechanism — why the shields diverge (this file)

The SYZ32 protection was **RS-uniqueness merge**: cores overlapping in `≥ k` points carry a single
local codeword, so the cluster is *yield-degenerate* and its bad scalars are `mca`-correlated.  Two
band cores that share the pairwise region `S_ij` and the triple `T` overlap in exactly
`|S_ij| + t` points.  For a **balanced realizable** profile `(d,d,d)` at rate `1/2` the budget cap
`max(a,b,c) + 1 + t ≤ k` forces

  `pairwise core overlap  =  d + t  ≤  k − 1  <  k`,

so the overlap is **strictly below** the RS-uniqueness threshold `k`: **the SYZ32 merge is
structurally unavailable** on *every* band-realizable interior witness.  (Concretely `μ₁₄`:
`d + t = 4 + 2 = 6 < 7 = k`, matching the probe's `merge_tested = 0`; contrast the SYZ32 crack's
`10 ≥ 8 = k`.)  The interior witnesses sit in **general position** — no two cores are forced equal —
so the yield-degeneracy that collapsed the SYZ32 cluster to one pencil cannot fire, and the pencil
accounting is not merge-protected.  This is the first structural trace of the `ι = 2` geometry
mattering at the stack level.

## Honest status

The interior witnesses are **NOT** stack-harmless by the SYZ22/SYZ32 accounting: the merge shield
is provably unavailable (`overlap < k`, proven below), and the observed lift **blows past** the
SYZ22 pencil budget `n − 1 = 13`, the pencil-yield ceiling `12`, *and* `n = 14` — the max `mca`-bad
count reaches `≥ 19`, versus a random-pencil non-`mca` baseline of `6`.  So the `ι = 2`
general-position geometry **defeats the merge/yield accounting route** SYZ32 used: any valid shield
must invoke the genuine near-Johnson proximity-gap list bound, not the pencil-yield/merge
combinatorics.  This is **not** a strip falsification (radius `2/7` sits at the Johnson edge, where
large bad-sets are theory-consistent), but it does close off the SYZ22/SYZ32 counting route for the
band-realizable interior witnesses.  CORE remains OPEN / ON-BGK, with the accounting route now
pinned as inadequate.

## What is proved here (axiom-clean, pure `ℕ`)
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.SYZ52

open ArkLib.ProximityGap.SYZ50 (Realizable)

/-! ## 1. Pairwise core overlap in the band Venn model -/

/-- **Pairwise core overlap.**  Two band cores share exactly the pairwise-exclusive region they
have in common (size `r`, one of `a,b,c`) together with the triple region `T` (size `t`).  So their
intersection has `r + t` points. -/
def coreOverlap (r t : ℕ) : ℕ := r + t

/-- **RS-uniqueness merge threshold.**  Two `RS[n,k]` local codewords agreeing on `≥ k` points are
equal (SYZ32.`rs_merge`); a core pair *merges* precisely when its overlap reaches `k`. -/
def MergeApplies (r t k : ℕ) : Prop := k ≤ coreOverlap r t

/-! ## 2. The band budget forces every core pair BELOW the merge threshold -/

/-- **Overlap is strictly sub-`k` on balanced realizable configs.**  The SYZ50 budget cap
`max + 1 + t ≤ k`, at a balanced profile `(d,d,d)`, reads `d + 1 + t ≤ k`, hence the pairwise
core overlap `d + t` satisfies `d + t < k`.  Field-independent, pure counting. -/
theorem overlap_lt_k_of_realizable {d t k : ℕ} (h : Realizable d d d t k) :
    coreOverlap d t < k := by
  obtain ⟨_, _, _, _, hbud, _⟩ := h
  simp only [coreOverlap, Nat.max_self] at *
  omega

/-- **The SYZ32 merge shield is STRUCTURALLY UNAVAILABLE on band-realizable interior witnesses.**
No pairwise core overlap of a balanced realizable profile reaches the RS-uniqueness threshold `k`,
so the merge that collapsed the SYZ32 near-duplicate cluster to a single pencil cannot fire here:
the three cores are in general position.  This is the mechanism separating the SYZ32 stack-vacuous
crack (overlap `≥ k`, merges, `mca`-bad `= 0`) from the SYZ50/52 interior witnesses (overlap `< k`,
never merge, `mca`-bad `> n − 1`). -/
theorem merge_unavailable_of_realizable {d t k : ℕ} (h : Realizable d d d t k) :
    ¬ MergeApplies d t k := by
  have := overlap_lt_k_of_realizable h
  simp only [MergeApplies]; omega

/-! ## 3. The two worked configurations, verbatim (matching the probe) -/

/-- **The `μ₁₄` interior witness: overlap `6 < 7 = k` — cores never merge.**  `(d,t,k) = (4,2,7)`:
`coreOverlap = 4 + 2 = 6 < 7`.  Matches the probe's `merge_tested = 0` (fewer than two cores ever
decode a common local codeword). -/
theorem mu14_overlap_lt_k : coreOverlap 4 2 < 7 := by decide

/-- The `μ₁₄` witness config is band-realizable (SYZ50) *and* its cores fail to merge — the two
facts that place it outside the SYZ32 shield. -/
theorem mu14_realizable_and_nonmerging :
    Realizable 4 4 4 2 7 ∧ ¬ MergeApplies 4 2 7 :=
  ⟨SYZ50.witness_realizable_n14, merge_unavailable_of_realizable SYZ50.witness_realizable_n14⟩

/-- **Contrast — the SYZ32 crack cluster: overlap `10 ≥ 8 = k` — cores DO merge.**  The SYZ31
near-duplicate cluster has pairwise overlap `10` at `k = 8`, so `MergeApplies`; that is exactly why
it is yield-degenerate and stack-vacuous (`mca`-bad `= 0`).  The band budget forbids this regime for
interior witnesses. -/
theorem syz32_crack_merges : MergeApplies 10 0 8 := by
  simp only [MergeApplies, coreOverlap]; decide

/-- **The separation, as one statement.**  There is a band-realizable balanced interior config whose
cores do NOT merge (`μ₁₄`), while the SYZ32 crack cluster DOES merge — so the merge-based
stack-vacuity of SYZ32 cannot be transported to the SYZ50 interior witnesses. -/
theorem shield_does_not_transport :
    (Realizable 4 4 4 2 7 ∧ ¬ MergeApplies 4 2 7) ∧ MergeApplies 10 0 8 :=
  ⟨mu14_realizable_and_nonmerging, syz32_crack_merges⟩

end ArkLib.ProximityGap.SYZ52

-- Honesty audit:
#print axioms ArkLib.ProximityGap.SYZ52.overlap_lt_k_of_realizable
#print axioms ArkLib.ProximityGap.SYZ52.merge_unavailable_of_realizable
#print axioms ArkLib.ProximityGap.SYZ52.mu14_overlap_lt_k
#print axioms ArkLib.ProximityGap.SYZ52.mu14_realizable_and_nonmerging
#print axioms ArkLib.ProximityGap.SYZ52.syz32_crack_merges
#print axioms ArkLib.ProximityGap.SYZ52.shield_does_not_transport
