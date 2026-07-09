=== lalalune
## THE WINDOW PACKING LAW (axiom-clean) — the first completely solved window stratum

`WindowPackingLaw.lean` + `W2WindowHalfCount.lean` (`da0e06d38`, full builds, axiom-clean). The below-UDR window now has a general two-sided structure theorem:

**The law.** For every genuinely rational coprime stack (deg ℓᵢ ≤ w, deg Rᵢ ≤ w+k−1, denominators domain-nonvanishing, ℓ₀ ∤ R₀, ℓ₁ ∤ R₁) in the window stratum `n + j = 3w + k − 1`:

- **`shared_forces_eq_general`** — two distinct bad scalars' missing sets `T_γ = D ∖ Agr_γ` intersect in at most `j` points: if they shared `j+1`, the agreement sets would share `n − 2w + j + 1 = w + k` points, forcing the secant bracket `(γ−γ')R₁ − (P_γ−P_{γ'})ℓ₁` (degree ≤ w+k−1) to vanish — `ℓ₁ ∣ R₁`, contradiction. *(The mechanism that found the refutation now powers the good side.)*
- **`window_packing_law`** — the missing sets form a **partial Steiner system**, and double counting `(j+1)`-subsets gives
  **`#bad · C(w−j, j+1) ≤ C(n, j+1)`.**

**Consequences.**
- **j = 0 (the first beyond-ladder slice) is SOLVED**: `#bad ≤ n/w`, and the `μ_w`-coset family (`ℓᵢ = X^w − eᵢ`, missing sets = `μ_w`-cosets, `γ(T)` a Möbius function of `t^w`) attains it — upper and lower bounds meet at `Θ(n/w)`, constants within 1. At `w = 2` (`w2_bad_card_le`): `2·#bad ≤ n` against the normalizer-pair floor `(n−2)/2` — **the per-stack window extremal is pinned to `{(n−2)/2, n/2}` for every field, every domain**.
- Low-j strata: `#bad ≲ (n/(w−j))^{j+1}` — comfortably inside the `WindowRationalLinear` budget at production rates for `j` up to ~√w.
- Honest scope: the packing bound degenerates for `j ≈ w` (near the UDR edge, where missing sets become small) and the `j ≥ 1` high-rate corners can exceed `n` — those strata and the degenerate-denominator branches remain the open part of `WindowRationalLinear`. Above UDR the cost-1 band `w = n−k−1` saturates generically (consistent with the in-tree `SmoothWindowSaturation`); the tuned-alignment mid-window experiment (MCA vs CA fork) is still open pending a probe fix.

The arc of the last two rounds: the explainer-geometry analysis produced the refutation (normalizer pairs), the refutation produced the repaired budget, and the same secant mechanism now proves the packing law that *explains* every family the campaign has found — `n/w` cosets, `(n−2)/2` involution pairs, `w+1` per-family, the triangle rigidity at k=1 — as faces of one partial-Steiner structure.
=== lalalune
## THE BOUNDARY-SLICE REACH (axiom-clean): the window pencil law extends one slice PAST UDR — and the reach is provably exact

`WBPencilBoundarySlice.lean` + `probe_wb_boundary_slice_anchor.py`:

**The free extension.** `badScalars_card_le_of_anchor` carries no below-UDR hypothesis anywhere — and its row selection `J` was never required to be injective. At the boundary slice **n = 2w+k** (the first radius past unique decoding, where the F₁₇ explosion band lives) a duplicated-row square selection still works: `mul_adjugate` holds with det ≡ 0, the updateRow trick still kills the cross-difference, the pinning survives. So the proven anchored count ≤ (w+1)+n(w+1)+1 applies AT the boundary radius — `epsMCA_le_boundary_slice` is the first counting law past UDR on the pencil route.

**Probe confirmation** at (17,8,4,2) and (37,12,8,2): every sampled rational boundary stack is anchored (181/181), and — the headline — **the adjacent-pair ceiling family at (37,12,8,2) has |BAD| = 12 = n and is ANCHORED**: the n-sized boundary explosion is inside the proven budget. Unanchored boundary words (raw words are always WB-solvable there — the system is underdetermined) cap at 5 bad. Zero budget violations.

**The exact no-go** (`windowPencil_adjugate_eq_zero_of_lt_boundary`): strictly above the boundary (n+1 ≤ 2w+k) every adjugate entry of every square row-selection vanishes IDENTICALLY — pigeonhole: the column count exceeds the row count by ≥ 2, so even after the updateRow deletion a repeated pencil row survives and the determinant dies. Anchoring is unsatisfiable there; the law's reach is exactly n ≥ 2w+k.

**What marching further takes** (the precise wall, now formal): each slice above the boundary raises the pencil's generic corank by one; the count needs the corank-c generalization — compound-matrix anchors + the multi-parameter split-incidence count. The cyclic-kernel structure (which still holds AT the boundary: deg(QZ) ≤ n−1 < n keeps Q₁Z₂ = Q₂Z₁ alive) is the c = 2 entry point. This is the same wall the H-RC slice programme predicted ('where the poly(n) bound first breaks is the discovery') — now pinned to a single formal object: the corank-c window pencil.
