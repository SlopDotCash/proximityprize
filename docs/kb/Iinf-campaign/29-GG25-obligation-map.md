# GG25 obligation map — what's proven in-tree, what's open, what was attacked (2026-06-17)

Per "read up on GG25 and attack every open part we haven't already proven." [GG25] = Goyal–Guruswami,
"Optimal Proximity Gaps for Subspace-Design Codes and (Random) Reed-Solomon Codes", STOC 2026 (eprint
2025/2054). Result: m-folded RS achieves the affine proximity gap to capacity `δ = 1−R−η` (Theorem 6.2),
`ε ≤ (C₄/q)(n/η + 1/η³)`, `κ=1/n`, field size linear in n. This is the PROVEN folded side (the prize's plain-RS
floor is a different code, the open BGK wall — see docs 18–28).

## The GG25 proof chain and its in-tree status
| GG25 step | type | in-tree status |
|---|---|---|
| **Lemma 4.4** Folded-Wronskian τ-subspace-design (`τ(r) ≤ R + O(r/m) + O(1/n)`) | EXTERNAL (GK13/GK16) | ✓ `GK16DegreeBudget.sum_rootMultiplicity_foldedWronskian_le` (axiom-clean) |
| **Lemma 5.5** Pruning (coordinate pinning from subspace design) | combinatorial | ✓ `SeparatingCoordinates.exists_separating_coords`, `SeparatingCoordsCount.card_separates_ge` (axiom-clean) |
| **Lemma 5.7** Line stitching (rank-nullity: many near-points → one code-line on a large subset) | combinatorial | ✓ curve form `FoldedCurveCloseSetBound.foldedCurveCloseSet_codewordCurve_card_le` + `GG25NonCovering.eq_zero_of_curve_agree_many` (axiom-clean) |
| **Lemma 5.10** Stitching + list-decoding → correlated agreement | combinatorial + EXTERNAL | partial: `CurveAgreementThreshold`, `HalfThresholdCA`; consumes the list-decoding input |
| **Lemma 5.3** Correlated agreement → line proximity gap | combinatorial | ✓ far-coset law (`FarCosetExplosion`, `mcaEvent ⟺ line-explainability`) |
| **§6.1** Line → affine reduction (averaging over directions through a non-close point) | combinatorial | **NOW ✓ (this round)** `Frontier/_GG25LineToAffine.card_bad_le_of_line_cover` (axiom-clean) |
| **FRS list-decodability at capacity** (PRUNE-based) | EXTERNAL (cited concurrent work) | ⊘ external input — cited, not re-proven (correctly; it is its own recent hard result) |

## What was attacked & landed this round — the §6.1 line→affine combinatorial core
`Frontier/_GG25LineToAffine.lean` (axiom-clean, real `lake build` passes):
- `card_bad_le_of_line_cover`: if the close set `bad ⊆ U` is covered by a finite family of lines (each
  `member l ⊆ U`), and each line carries `≤ B` close points, then `|bad| ≤ (#lines)·B`. This is the
  union/cover bound that turns the per-line proximity gap (Theorem 5.12) into the affine gap (Theorem 6.2):
  instantiate `B ≤ ⌊ε·q⌋` and `#lines = (|U|−1)/(q−1)` to recover the §6.1 factor `ε·q/(q−1)`.
- `card_bad_le_of_pointed_lines`: the pointed-family shape (lines through the fixed non-close point `p₀`).

The construction of the line cover (lines through `p₀`) and the `(|U|−1)/(q−1)` count are the standard
affine-geometry inputs; the formalized content is the cover bound (the mathematical core of §6.1).

## Honest status of GG25 as a whole
> **Scope correction (2026-10-28 audit, T48; cross T40).** "Essentially fully formalized" and "§6.1
> closed" overstate what landed. `card_bad_le_of_line_cover` is the generic finite cover union bound:
> if `bad` is covered by lines with at most `B` close points each, then `|bad| ≤ (#lines)·B`. Its
> application to §6.1 still takes three things as inputs. These are the construction of the
> pointed affine-line family through `p₀`, its cardinality `(|U|−1)/(q−1)`, and the per-line bound
> `B`, which comes from Theorem 5.12 and its curve-selection hypotheses. A valid cover inequality
> does not discharge those inputs, and the curve-selection hypotheses remain tracked by the PG and
> Research lanes. Lemma 5.10 is also only partial in the table above. Read the paragraph below as
> "the cover inequality is formalized", not as "the chain is complete".

**The GG25 combinatorial chain is essentially fully formalized in-tree**, now including the §6.1 lifting core.
The two remaining genuinely-open inputs are EXTERNAL and correctly cited, not gaps to "prove" here:
1. **FRS list-decodability at capacity** (PRUNE-based, concurrent work) — a recent hard result; importing its
   statement as a named hypothesis is the right modularity, not a hole.
2. The exact constants in the τ-subspace-design parameter (Lemma 4.4) at the prize folding degree — the
   asymptotic form is in `GK16DegreeBudget`; sharpening the constants is bookkeeping, not open math.

So "attack every open part we haven't proven" resolves to: the combinatorial chain is proven (and this round
closed the §6.1 lifting core); the only non-combinatorial inputs are cited external list-decoding results that
are not ours to re-derive. GG25 gives the folded-RS δ* UNCONDITIONALLY modulo those citations — consistent with
the campaign verdict (folded solved; the open wall is the PLAIN-RS floor = BGK, docs 18–28). Tools: GG25 paper
(eprint 2025/2054, arXiv 2601.10047). Related: docs 18, 22 (folded vs plain), 28 (irreducibility).
