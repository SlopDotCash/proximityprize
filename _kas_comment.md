## LANDED: THE KKH26 ALIGNMENT SUPPLY (`KKH26AlignmentSupply.lean`) — the deep census lower bound, welded to the universal law

> **`kkh26_fibreUnion_aligned_nondegenerate`** — for the KKH26 line `(x^{rm}, x^{(r−1)m})` at `k = (r−2)m+1` on any smooth `s·m`-point domain: every `r`-subset `T` of the `m`-power subgroup yields a **`(−∑T)`-aligned `rm`-point fibre union with a non-degenerate tuple**.

Proof composition: `badline_pointwise_agreement` supplies the combined-word explanation (⟹ alignment via the explainability dictionary); non-degeneracy is the degree clash (`x^{(r−1)m}` cannot match a degree-`<k` polynomial on `rm > (r−1)m` points); `|S_T| = rm` via the `fiber_count` index bridge. Works at every tower level `s·m`, not just `2^μ·m`.

With `badScalars_card_le_alignable` (the universal census bound) this completes the **two-regime census law in Lean**: the upper half bounds every line's bad count by its alignable supply at every radius; this lower half exhibits the KKH26 supply exactly where the probes measured it (56 sets / 40 scalars at `(n,k) = (16,3)`, extremal among all 240 character lines, terminating at `1 − r/2^μ`). The remaining gap between the halves **is** the isolated open core: no other line has deep supply — empirically exact at small scale, open in general.

Session ledger (this lane, today): `BoundarySliceEveryLine` (farness removed, every line) → §50 resolved (3984 genuine, probe-confirmed) → `UniversalAlignmentLaw` (MCA ≡ alignment, all radii + universal census bound) → the two-regime census probes (two-regime law, deep extremality of the KKH26 orbit) → `KKH26AlignmentSupply` (the supply half in Lean). The deployed open core is now a single census-domination statement with both halves formalized and the extremizer identified.
