## LANDED: THE UNIVERSAL ALIGNMENT LAW (`UniversalAlignmentLaw.lean`) — MCA ≡ residual-pencil alignment at EVERY radius, every line

The boundary-slice programme closes into one statement covering **all radii**. Four theorems, axiom-clean:

> **`mcaEvent_iff_aligned_subset`** — for any agreement threshold `a ≥ k+1` (`a−1 < (1−δ)n ≤ a`) and **every** stack `(u₀,u₁)`:
> `γ` is MCA-bad **⟺** some `a`-point set `S` is **`γ`-aligned** — every injective `(k+1)`-tuple of `S` satisfies `e_t(u₀) + γ·e_t(u₁) = 0` — with at least one non-degenerate tuple.

Supporting dictionary, of independent use:
- **`explainableOn_iff_forall_residual`** — a word extends to an `rsCode` codeword on `S` **iff** every tuple residual vanishes (Lagrange + the snoc-glue through `k` shared nodes — the level-`a` extraction).
- **`pairJointAgreesOn_iff_forall_residual`** — joint explanation ⟺ both component residuals vanish on every tuple.
- **`Aligned.gamma_eq`** — an aligned set with a non-degenerate tuple pins its scalar, hence:
- **`badScalars_card_le_alignable`** — **`#bad(δ) ≤ #{γ-alignable a-sets}`** at every radius: THE UNIVERSAL CENSUS BOUND.

**Reading.** The whole MCA object is now the alignment geometry of one pencil `{e_•(u₀) + γ·e_•(u₁)}` over `(k+1)`-tuples: at the boundary (`a = k+1`) alignment is a single-tuple condition and the law specializes to the ratio image (`BoundarySliceEveryLine`, both landed laws consistent); one band deeper (`a = k+2`) alignment = "all `k+2` sub-tuple ratios collide" — the ratio-collision census; at the ceiling band of the deployed pin, `InteriorCeiling` **is** the statement `#{alignable (rm+1)-sets} ≤ ε*q` fibred over the pinned scalar. The §49 isolated inequality now has an exact combinatorial normal form with no MCA/witness language left in it.

**Next in lane:** the `a = k+2` ratio-collision specialization (aligned ⟺ the `k+2` sub-tuple ratios are equal — connects to the wide-circuit/quartet census machinery), and the alignment-census formulation of the deployed threshold radius (the deepest `a` with an alignable-set supply above `ε*q`).
