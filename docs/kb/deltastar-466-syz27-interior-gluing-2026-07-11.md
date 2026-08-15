# δ\* / #466 — SYZ27: local-to-global gluing in the rate-1/2 interior band 1/4 < δ < 1/3

Date: 2026-07-11
File: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ27InteriorGluing.lean`
Probe: `scripts/probes/probe_syz27_interior_gluing.py`
Branch: `codex/syz27-interior-gluing` (off `fork/research/proximity-prize` @ 389072c14)

## Context

SYZ26 closed the clean end of the rate-1/2 strip: core size `s ≥ 3n/4` (δ ≤ 1/4) has pairwise
overlap `2s−n ≥ k`, forcing incremental-≥k-orderability (SYZ25 S1), hence generation `⨆ Aᵢ = W`,
hence deficiency `d = 0`. On the excluded boundary δ = 1/3 (`s = ⌈2n/3⌉`) a field-independent
`d = 1` over-budget cover exists. SYZ26 reported the **open interior band** `2n/3 < s < 3n/4`
(`1/4 < δ < 1/3`) as deficiency-free by exhaustive random probe, but only sampled **over-budget**
full covers — leaving a real question about what actually couples deficiency to cover shape there.

## Resolved picture (the point of SYZ27)

Probe `probe_syz27_interior_gluing.py`, `k=n/2`, band `2n/3 < s < 3n/4`, `n ∈ {16,20,24,28,32}`,
~40k random distinct full covers each, field-independent `d`:

| family | budget | deficiency d |
|---|---|---|
| D = 2 full cover | **always under-budget** | `d = k − (2s−n) > 0`, field-independent (=2 in tests) |
| D = 3 over-budget | over-budget | `d = 0` except a **rare** coplanar shape (`d ≤ 1`) |
| D ≥ 4 over-budget | over-budget | **`d = 0` in every one of tens of thousands of trials** |

Sharp readout across all n: over-budget d>0 counts collapse as D grows — D=4/5/6 over-budget gave
**zero** deficient covers in ~20k trials each per n. The band's genuine deficiency lives entirely
in the **under-budget D=2 regime** (and rarely D=3), which SYZ26 never sampled. This dissolves the
apparent tension: SYZ26's "interior is deficiency-free" was a statement about over-budget covers,
and it holds — the deficiency that does exist is under-budget, carrying too few bad scalars to
loosen the SYZ22 budget `|U| ≤ n−1`.

Arithmetic cause (proven): for a full 2-cover at rate 1/2, over-budget ⟺ core size `s ≥ 3n/4`
(δ ≤ 1/4). So a deficient D=2 band cover (`s < 3n/4`) is *necessarily* under-budget. Over-budget in
the band forces D ≥ 3.

## Proven verbatim (all axiom-clean: propext/Classical.choice/Quot.sound only; no sorry/native_decide)

1. `card_inter3_ge_of_large` — three cores of size ≥ s in ground set size |G| meet in
   `≥ 3s − 2|G|` common points (inclusion–exclusion chained twice).
2. `triple_inter_nonempty` — if `2|G| < 3s` (s > 2n/3, interior band) any three cores have
   **nonempty** common intersection. The geometric hallmark of the band.
3. `two_cover_under_budget_of_band` — full 2-cover, `n = 2k`, both sizes `< 3n/4`
   (`2sᵢ < 3k`) ⟹ `(s₁−k)+(s₂−k) < n−k`. Pure arithmetic.
4. `over_budget_forces_three_cores` — full cover, `n = 2k`, cores of size `≤ s` with `2s < 3k`,
   total excess `≥ n−k` ⟹ `D ≥ 3` (via `interval_cases D`/omega).
5. `two_line_deficient_under_budget` — abstract avatar: two distinct lines `⟨e₀⟩,⟨e₁⟩ ≤ ℚ³`,
   `∑ finrank = 2 < 3 = finrank W`, `⨆ ≠ W`. Shadow of the under-budget D=2 band deficiency
   (contrast SYZ25/26 `overbudget_not_imp_*` which needs three coplanar lines to *reach* the count).
6. Concrete witnesses (n=16, k=8, interior 11-cores, δ=5/16):
   - `syz27TwoCoverWitness` `{{0..10},{5..15}}`: full cover, `∑excess = 6 < 8 = |U|−k`
     (`two_under_budget`), overlap `2s−n = 6 < k`; probe `d = 2` field-independent.
   - `syz27FourCoverWitness` (4 × 11-cores): full cover (`four_full_cover`), over-budget
     `∑excess = 12 ≥ 8` (`four_over_budget`); probe `d = 0` field-independent — generation forced.
7. `generation_realizes_budget` — generation ⟹ span attains ceiling `finrank W` (SYZ25/26 pipe).

## Residual (honest, now pinned to minimal form)

The general **`D ≥ D₀`-over-budget ⟹ `d = 0`** polynomial-gluing law remains the named residual —
but SYZ27 pins it: it is needed *only* in the over-budget `D ≥ 3` regime, never for the
(under-budget) `D = 2` deficiency. Probe evidence is overwhelming that `D ≥ 4` over-budget band
covers always generate; a Lean cocycle/gluing proof from the triple-intersection substrate (§1) is
not yet in hand. Unconditional δ\* status untouched; strip not falsified.

## Reuse hooks

- The triple inclusion–exclusion floor (`card_inter3_ge_of_large`) generalizes SYZ26's pairwise
  `card_inter_ge_of_large`; both are omega proofs off `Finset.card_union_add_card_inter`.
- Budget arithmetic `over-budget(2-cover) ⟺ s ≥ 3n/4` is the exact bridge tying the D=2 deficiency
  regime to the SYZ26 δ ≤ 1/4 clean-gluing threshold.
- `two_line_deficient_under_budget` reuses SYZ25.ceA/cePlane/ce3 avatars at D=2.
