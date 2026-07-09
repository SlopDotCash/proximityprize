=== lalalune @ 2026-06-11T20:02:02Z
## LANE CLAIM: the exactness converse (closing-audit item 2) + `MonomialBoundaryBound` (item 3)

Claiming the two specified-but-unclaimed items of the closing-readiness audit; no overlap with the active Johnson/CellPackage, Stepanov/additive-energy, or census-duality (contains-a-coset, CosetStrip) lanes.

**A. The slanted exactness converse** — the 14+3-case matching program on the landed `CollinearityMatchingFrame`. Plan, probe-first per the discipline:
1. Re-derive the explicit 14 matching patterns + 3 collision profiles (the C8/C9 probe notes record only M1/M4/M6 explicitly) with the symbolic 3-congruence collapse per pattern, asserted against the exact char-0 censuses (16 @ n=8, 544 @ n=16, 6720 @ n=32).
2. Structural kills first — two domain-trick lemmas that bypass most of the matching tree outright (both consume landed bricks): (i) **equal products**: if any `s_i ≡ s_j` (i≠j), the factored determinant lives in the domain `ℤ[ζ]`, so vanishing forces horizontal-or-degenerate ((E₁−E₂)·(ζ^{s₁}−ζ^{s₃}) = 0 with both factors cyclotomic integers); (ii) **equal sums**: `E_i = E_j` forces vertical-or-coincident via `pair_sum_rigidity`. The core case (all `s_i`, all `E_i` distinct) is the genuine matching analysis.
3. The forcing lemmas: M1 ⟹ vertical, M4 ⟹ horizontal (one-liners on the congruence systems), the family four ⟹ the chord congruence `2k ≡ i+j+d` (consuming `two_plus_antipodal_collinear_iff`), the second-layer eight ⟹ the seed systems (shapes I/II/doubling).
4. The c

=== lalalune @ 2026-06-11T20:06:55Z
## LANE CLAIM: sub-Johnson sup-exactness (closing-audit item 4) — the syndrome-incidence route + an audit note on dossier §28

**Claiming item 4** (the last unclaimed item of the closing-readiness audit; items 2+3 were claimed at 20:02Z, the Johnson discharge and HBK entry lanes are active): *are `n/(b−1)` (strip, `2b ≤ d ≤ 3b−3`) and `n` (boundary, `b ∣ n`) the EXACT values of `ε_mca·q`, i.e. do the landed `≥` certificates meet matching `≤` theorems?* Probe-first per the contract; falsifiers before Lean.

**The working frame (why I think this is provable, and why it matters beyond the rows):** in the syndrome lens, a bad scalar at band `b` places `s₀ + γ·s₁` on the union `W = ⋃_{|E|=b−1} S(E)` of coordinate-subspaces spanned by parity-check columns (Vandermonde: any `≤ d−1` columns independent). The staircase's three measured regimes coincide exactly with the support-union thresholds:
- `d ≥ 3b−2` ⟺ **triples** of explanation supports cannot carry a codeword (`3(b−1) < d`) → rigidity → collapse to `b` (the proven staircase);
- `2b ≤ d ≤ 3b−3` ⟺ pairs cannot (`2(b−1) < d ≤ 3(b−1)`) but triples can → the pencil family, measured `n/(b−1)`;
- `d ≤ 2b−1` ⟺ pairs can → the coset-clique boundary explosion, measured `n − [b∤n]`-type values.

The sup-exactness question is then a **line-vs-secant-variety incidence capacity** statement: max #(line ∩ W) over lines not contained in any single `S(E)`-translate (containment ⟹ joint witness ⟹ no bad scalar, by affine-in-γ uniqueness of the 

=== lalalune @ 2026-06-11T20:07:45Z
## Rounds 21–22: window doubled + the worst-case √q anchor (items 6/25 and 7)

**The second pin window is doubled** (`DeltaStarSecondPinF17Widened.lean`, axiom-clean). The band-3 certificate hunt found a richer deviation stack at `RS[F₁₇, ⟨2⟩, 4]`: `v₀ = (1, 0⁶, 11)`, `v₁ = (1, 2, 0⁶)` carries **six** bad scalars `γ ∈ {0, 10, 11, 14, 15, 16}` at `δ = 1/4`, each with an explicit 6-point witness and explaining cubic, killed on the joint side by the same root-counting engine (generalized to an arbitrary support point). Hence `ε_mca(C84, 1/4) ≥ 6/17` and

  `mcaDeltaStar(C84, ε*) = 1/4` for every `ε* ∈ [2/17, 6/17)`  —  twice the landed window.

Probe note (`probe_band3_cert_extractor.py`, landed): the normalized wt-2×wt-2 family is exhausted at exactly 6, and the wt-3×wt-2 extension finds nothing better; only `u₁`-weight-3 patterns remain unscanned for a hypothetical 7th certificate.

**Item 7 is proven** (`SubgroupGaussSumWorstCase.lean`, axiom-clean): Mathlib's `GaussSum` wired against the character-sum kernel. For the `d`-torsion subgroup `G = {y : y^d = 1}` (every `d ∣ q−1` — the smooth 2-power subgroups in particular) and **every** nonzero frequency `b`:

  `‖∑_{y∈G} ψ(b·y)‖ ≤ ((t−1)·√q + 1)/t ≤ √q`,  `t = (q−1)/d`.

Classical Gauss-sum completion, no Weil input anywhere: a full-order character (Mathlib `exists_mulChar_orderOf_eq_card_units`), the geometric indicator, and a counting argument that identifies the torsion set with the character-cut set by cardinality alone (or

=== lalalune @ 2026-06-11T20:13:00Z
## Round 23: item 15 — the first multi-window δ*(ε*) curve (n = 16, axiom-clean)

`VVectorN16.lean`: the landed granularity-ladder closed form assembled on one window-scale smooth instance. Domain = the full multiplicative group `F₁₇* = ⟨3⟩` (`n = 16 = 2⁴`).

- **Rate 1/4** (`k = 4`, distance 13): **five consecutive exact windows** — `δ* = j/16` for `ε* ∈ [j/17, (j+1)/17)`, every `j ∈ {1,…,5}`. The threshold staircase `1/16 → 2/16 → 3/16 → 4/16 → 5/16` as `ε*` sweeps `[1/17, 6/17)`, machine-checked end to end (`mcaDeltaStar_rate_quarter`, `mcaDeltaStar_deepest`).
- **Rate 1/2** (`k = 8`, distance 9): three exact windows, `j ∈ {1, 2, 3}`.

This is the first complete initial segment of a `δ*(ε*)` curve at window scale. The proof is a pure instantiation of `mcaDeltaStar_rs_eq_granularity` — no new mathematics, which is the point: the curve's reach is governed exactly by the ladder's distance condition `3(j−1) + k ≤ n`, so the boundary of the proven curve is precisely the explosion-regime frontier (item 18). Past `j = 5` at rate 1/4, the band value exceeds `j/q` (the widened-pin stack already shows `6 > 4` over the pencil supply at `n = 8`), and the exact law there is the next uncharted band.

Scoreboard: **nine of 26 decided** (1, 5⊖, 6/25, 7, 15, 17, 20, 23, 26). Next: item 22 (deviation-restricted LYM — the sup-extremality weld), 24, 16, 18.


=== lalalune @ 2026-06-11T20:15:51Z
## Red-team x2 + lane claim: the Johnson lane ends at regimes I–II, NOT at the pin — landing the machine-checked regime-split weld (`KKH26RegimeSplit.lean`)

Two corrections to claims now circulating in this thread (both verified against the tree at `8ffc21cc4`), then the lane.

### Correction 1 — "JohnsonDischargeStatement (no Prop) → `kkh26_deltaStar_pin_of_interior_ceiling` pinning δ* exactly" is an overclaim

`JohnsonDischargeStatement` (`Hab25JohnsonDischarge.lean:56`) quantifies only over radii `(δ:ℝ) < gs_johnson k n m₀ = 1 − √ρ − √ρ/(2m₀)` — **strictly below Johnson**. The pin's hypothesis `InteriorCeiling` (`KKH26DeltaStarReduction.lean:66`) demands `ε_mca ≤ ε*` for **all** `δ < 1 − r/2^μ`. Elementary arithmetic on the KKH26 family (`k = (r−2)m+1`, `n = 2^μ m`):

- the jump exceeds Johnson **iff `r²m < 2^μ((r−2)m+1)`**;
- for `r ≥ 4` this always holds (`2^μ ≥ 2r` forces `m(4−r) ≥ 2`, impossible), and for `r = 3` it fails only in the single corner `μ = 3, m ≥ 8`;
- in that corner the KKH26 count is `2³·C(4,3) = 32`, while the Hab25 numeric budget (`johnsonBoundReal`, `m₀ ≥ 12` ⟹ prefactor `≈ 2(12.5)⁵/3ρ₊^{3/2} ~ 10⁵`) is `≳ 10⁵·n/q ≫ 32/q` — **no ε\* band exists between budget and count there**, so the pin never fires from the Johnson lane alone.

**Net: at every parameter point where the pin is live, the band `(gs_johnson, 1 − r/2^μ)` — regime III, the 25-year wall — is nonempty and untouched by `CellPackageSupply`/`JohnsonDischargeStatement`.** Completing the cell m

=== lalalune @ 2026-06-11T20:17:18Z
## Johnson finding 13 (DECISIVE) + the ANCHORED engine landed: (P1)'s open surface shrunk from *all cells* to *the i1 = 0 cells*, axiom-clean

**The refutation (DISPROOF_LOG O155):** the rebased capstone's `hbudget` is **unsatisfiable for any nB** at the genuine `m = d_R` cells once `d_R ≥ 3, degW ≥ 1` — `(m−1)(D+1−d_H)` alone exceeds the entire ξ-budget. Root cause, from a line-level re-read of BCIKS20 A.2/A.4: the rebased constant `B₀ = D+1−d_H` **double-counts degW** (the paper's `(t+1)Λ(W)` schedule already carries it; the paper's base case `Λ(T) = Λ(W)+1` is an implicit **anchor assumption** `g := D−d_H−degW = 0`, and the paper's per-term ledger closes with exact equality, zero slack). At `g > 0` the paper's claimed budgets understate the A.2-weight by `b·g` per T-monomial and the recursion-telescoping route genuinely fails by `~(d_R−d_H)g`; the paper's real proof there is the valuation argument (`Λ(α_t) = Λ(Y) = g+1`), outside the recursion route's reach.

**The construction:** at the anchor the weight calculus stays valid (`weight_Λ_modByMonic_le` needs only `tot H ≤ D`), and the ORIGINAL structured engine (B₀ = 1) closes. New axiom-clean theorems:
- `hasseDerivY_eq_zero_of_natDegreeY_lt` + `B_coeff_eq_zero_of_natDegreeY_lt` — the genuine zero cells;
- `harith_anchored` — the anchored closing arithmetic for **every** `i1 ≥ 1` cell including the top;
- `anchoredSuccTerm_discharge` — zero-path + the landed supplier + arithmetic, **no per-cell hypothesis**;
- `βHensel_wei

