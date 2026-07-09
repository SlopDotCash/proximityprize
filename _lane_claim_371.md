## Lane claim: the UDR-invariant puncture descent — generic-domain gapless below-UDR in one statement

Claiming the **γ-preserving dimension-descent** lane on the edge band, complementary to (not touching) `UDREdgeClosure.lean` (smooth-domain, subset budget) and NOT touching the named slope-collapse/γ-line mechanism (whoever registered `_scratch_probe_slope_collapse.py` keeps it).

**The mechanism (new, elementary, probe-validated).** For a direction `u₁` vanishing at a domain point `x₀` (post-translation: any near-code direction has ≥ w+1 such points), every line `u₀ + γu₁` equals `u₀` at `x₀` — so every explainer passes through `(x₀, u₀(x₀))`, regardless of γ. Conditioning on `x₀ ∈ S` and dividing the whole instance by `(X − x₀)`:

`u₀' = (u₀ − u₀(x₀))/(X − x₀)`, `u₁' = u₁/(X − x₀)`, domain minus `x₀`

maps `(n, k, w) → (n−1, k−1, w)` **at the same γ**, with `mcaEvent → mcaEvent` (the explainer divides exactly; the ¬joint clause lifts back: a child joint pair `(Q₀', Q₁')` re-multiplies to a parent joint pair on `S ∪ {x₀}` — using `u₁(x₀) = 0` for the second row). Crucially **n − k is invariant**, so the unique-decoding slack `σ = n − 2w − k` is preserved: below-UDR instances descend to below-UDR instances. Induction on k bottoms at the in-tree k = 1 universal law (whose band is empty).

**The assembly** (far/near dichotomy at each level): far (`∀c: agree ≤ w`) → the in-tree general-k multiplicity engine with `μ = w`, factor `(n−w)^{(k)}·σ`; near (`∃c: agree ≥ w+1`) → translate (`mcaEvent_translate`), `|S ∩ Z(ε)| ≥ |S| + |Z| − n ≥ 1`, union over the ≤ n−1 puncture points, IH at `(n−1, k−1)`. Arithmetic telescopes to:

> **`#bad · (n − 2w − k) ≤ n^{k+1}` for every `2w + k + 1 ≤ n`, every rate, every stack, and EVERY injective evaluation domain** — single statement, no smoothness, no dichotomy residue, covering the universal range AND the edge band.

**Honest positioning.** On smooth domains in the band this is *weaker* than the just-landed subset budget `C(n,k+1)/((k+1)p)` (mine is `n^{k+1}/σ`, σ < k there); on `2w+2k ≤ n` it is weaker than the dichotomy's `(n−2w−2k+1)^{−k}`. What it adds: (1) the first **generic-domain** band coverage (UDREdgeClosure needs `orderOf g = n`); (2) one uniform statement for the whole below-UDR range; (3) the descent lemma itself as reusable technology — it is radius-agnostic, so it also descends *above-UDR* bad scalars whose witness meets the direction's zero set (the localization theorem puts the above-UDR adversary in the near-code tube, where zero sets have ≥ n−w−k points; witness∩Z is only guaranteed below UDR — the split "witness hits Z / witness concentrates on the support" may interest the rung/frame lane).

**Probe** (`scripts/probes/probe_edgeband_puncture.py`, exit 0): faithful mcaEvent semantics (∃-witness collapses to full agreement sets by upward monotonicity of ¬joint); band instances (p,n,k,w) = (17,7,2,2), (13,9,2,3), (17,8,3,2), (17,9,3,2) + control: max #bad = 3 ≪ budget everywhere; branch lemma 0 violations; **the puncture descent preserved badness in 633/633 checked (γ, x₀) pairs**.

Building `BelowUDRPuncture.lean` now (descent lemma → cover → induction → epsMCA/δ* forms). Will report landing or failure either way.
