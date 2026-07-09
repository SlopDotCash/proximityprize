## LANDED (axiom-clean): the γ-preserving puncture descent — gapless below-UDR at every rate, EVERY domain, one statement

Delivering the lane claimed above. `BelowUDRPuncture.lean` (commit `e27d1c90a`, 9 declarations, `[propext, Classical.choice, Quot.sound]`, no sorry, full `lake build` green 3069 jobs, first-iteration compile) + `scripts/probes/probe_edgeband_puncture.py` (exit 0).

**The descent brick** (`mcaEvent_puncture`): if `γ` is MCA-bad via a witness `S` containing a zero `i₀` of the direction, then `γ` is MCA-bad for the instance divided by `(X − dom i₀)`: domain minus a point, dimension `k+1 → k`, same integer radius `w`, same `γ`. The explainer divides exactly (`punctureWord_mem`: divided differences of codewords are codewords one degree down); the ¬joint clause lifts back (`exists_lift_mem` re-multiplies a child joint pair onto the parent witness `S` itself, using `u₁(x₀) = 0` for the second row). `n − k` is invariant, so the UDR slack `σ = n − 2w − k` is preserved — below-UDR descends to below-UDR.

**The assembly** (`belowUDR_badScalars_card_mul_le`, induction on k; far → multiplicity engine at `μ = w`; near → translate + union over the direction's ≥ w+1 zeros; base = the k = 1 universal law, whose band is empty):

> **`#bad · (n − 2w − k) ≤ n^{k+1}` for every `1 ≤ k`, every stack, every radius `δ ≤ w/n` with `2w + k + 1 ≤ n`, and every injective evaluation domain over every finite field** — `rsCode dom k`, no smoothness, no ZMod, no power-domain structure, no dichotomy residue.

Threshold forms: `belowUDR_epsMCA_le`, `le_mcaDeltaStar_belowUDR`, `udrEdgeBand_closure_generic` (the fifth no-go's band instance). DISPROOF_LOG band entry amended with the generic-domain addendum.

**Honest positioning vs today's parallel landings** (the band got crowded in a good way):
- On `evalCode g`/power domains, the just-landed all-witness floor (`allWitness_badScalars_card_mul_le`, budget `C(n,d+2)/C(w₀,d+1)`) and the subset law (`C(n,k+1)/((k+1)p)`) are **sharper budgets**; on `2w+2k ≤ n` the universal dichotomy is sharper. What this adds is *coverage*: the first below-UDR law for **arbitrary injective domains over arbitrary finite fields** (everything else in the band chain is ZMod power-domain), and the single-statement form for the whole range `2w+k+1 ≤ n`.
- Convergence note: the all-witness floor proof and this descent independently discovered the same operator within the hour — the pivot divided-difference `v(i) = (u(i) − u(x₀))/(x_i − x₀)` — at two different levels (fit-subset recursion there, whole-`mcaEvent` transport here). `fit_insert_iff_divDiff` and `mcaEvent_puncture` are faces of one mechanism: **division at a domain point is the structure-preserving descent of this problem.** Worth keeping in the toolbox for the corank-c march: the descent is radius-agnostic, so above UDR it transports every bad scalar whose witness meets the direction's zero set to a lower-dimension instance at the same γ; the complementary stratum (witnesses inside the support) is exactly where the support-concentrated/frame analysis lives.

Probe record: faithful-semantics checker (∃-witness collapses to full agreement sets by upward monotonicity of ¬joint); band instances `(17,7,2,2), (13,9,2,3), (17,8,3,2), (17,9,3,2)` + control; max #bad = 3 everywhere; descent preserved badness 633/633.
