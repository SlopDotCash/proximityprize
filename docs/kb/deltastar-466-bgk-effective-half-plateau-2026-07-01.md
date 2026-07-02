# #466 Tier-1 item 5 CLOSED: the effective-BGK 1/2-push at β=4 is quantified-dead

Date: 2026-07-01. Lane: dossier v3 §6 Tier-1 item 5 ("di Benedetto sum-product pushed to an
effective 1/2 exponent at β=4 — announced 2026-06-27, never run"). Brick:
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_BGKEffectiveHalfPlateau.lean` (compiles
axiom-clean, `pg-iterate` 51s). Parallel session note: this session ran Tier-1 items 5 and 3
while the concurrent #466 session ran lanes L1/L2/P1–P3 (its round-1 plan); the two file sets
are disjoint.

## What was run

The "push" = determine whether ANY explicit-constant instantiation of the sum-product corpus
reaches cancellation exponent 1/2 (i.e. `M(μ_n) ≤ n^{1/2+o(1)}`) at the prize aspect ratio
`p = n^4`. The corpus has exactly two explicit mechanisms:

1. **Trilinear (depth-3) machinery** — di Benedetto et al. 2003.06165 Thm 3.1, saving
   `(10 − 2t₃ − t₂/2)/72` in the energy exponents. The in-tree ceiling
   (`diBenedettoSaving_le_ceiling`, `_DiBenedettoNearSidonImprovement.lean`) already pins the
   input-slot cap at **1/24** (diagonal energy floors `t₂ ≥ 2`, `t₃ ≥ 3` are information-
   theoretic, not knowledge gaps).

2. **Iterated sum-product (BGK)** — sharpest EXPLICIT form per Kowalski's exposition
   (arXiv:2401.04756, Rem. 1.2(3)): **Shkredov arXiv:1705.09703 Cor. 16**:
   `max_{ξ≠0}|Γ̂(ξ)| ≪ |Γ|·p^{−δ/2^{7+2/δ}}` for `|Γ| ≥ p^δ`, proof structure
   `k = ⌈2 log p/log|Γ|⌉ + 4` squaring iterations → `|Γ|`-saving exactly `1/2^{k+2}`, under
   applicability condition `2^{64k}C∗⁴ ≤ |Γ|` (Rem. 13: droppable, same shape; the
   `(C∗log|Γ|)^{k−1}` penalty washes out under the `2^{k+1}`-th root). Verbatim quotes
   verified against the PDF (local copy fetched; matches
   `docs/references/proximity-gap-paley-spectrum/subgroup-expsum-2401.04756.pdf` Rem. 1.2(3)).

## The verdict (all machine-checked, exact rationals)

At β = 4 (`k = 12` iterations, energy depth `2^12 = 4096`):

| quantity | value | vs prize (1/2) |
|---|---|---|
| iterated-explicit n-saving | `1/16384` | 8192× short |
| iterated-explicit p-saving ν | `1/65536` | gate needs `ν ≥ 1/8` (`pSaving_misses_prize_beta_four`) |
| trilinear ceiling (in-tree) | `1/24` | 12× short |
| trilinear / iterated ratio | `> 682×` | iteration COLLAPSES, does not amplify |
| clean Cor. 16 applicability floor | `|Γ| ≥ 2^768` | prize `n = 2^30` is `2^738` below it |
| Wick saving at the depth the method consumes (4096) | `4093/8192 ≈ 0.4996` | conversion inefficiency `> 4000×` |

Kill theorems: `shkredov_explicit_misses_prize`, `trilinear_ceiling_dominates`,
`half_unreachable_at_any_depth` (`1/2^{k+2} < 1/2` for EVERY k; ≤ 1/64 in the method's range —
Shkredov Rem. 17: constants improvable "but not the constant C in (31)", the `2^k` collapse is
structural), `prize_scale_below_cor16Floor`, `depth_efficiency_gap`.

## Why this is the wall again (the depth-inefficiency reading)

The iterated method consumes additive-energy depth `2^k = 4096` — 46× the wall depth
`r ≈ ln q ≈ 89` — and converts it into saving `1/16384`. The (OPEN) Gaussian/Wick bound at the
SAME depth would give `≈ 1/2` (`wickSaving 4096 = 4093/8192`); even at wall depth 89 it gives
`43/89 ≈ 0.483`. So the sum-product cascade is an L²-energy method paying wall-currency (moment
depth) at a doubly-exponential exchange rate — squarely inside `MetaTheoremSecondOrderCap`'s
jurisdiction, now with the exchange rate an exact rational. The residue of Tier-1 item 5 is (as
forecast by the tool-shape principle) the CORE itself; no new attack surface opened.

## Status updates this induces

- Dossier v3 §6 Tier-1 item 5: **CLOSED (refutation-with-exact-constants)** — remove from the
  live frontier; the un-run flag is discharged.
- The `_SubgroupExpSumPSavingGate` (`ν ≥ 1/8` at β=4) now has its first explicit-corpus
  instantiation showing the sharpest known explicit ν misses by 8192×.
- CORE unchanged: OPEN, ON-BGK. (This brick is exponent bookkeeping on cited shapes; no
  analytic content, nothing silently discharged.)
