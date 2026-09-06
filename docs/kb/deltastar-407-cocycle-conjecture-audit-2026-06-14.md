# Issue #407 cocycle conjecture audit — 2026-06-14

## Scope

This note records the current strongest closed-form conjectural route for issue #407 after reading:

- GitHub issue #407 and comments through `4700438400`.
- `Research/ProximityPrize/AGENTS.md`.
- `docs/kb/deltastar-357-compiled-knowledge.md`.
- `docs/kb/prize-core-distilled.md`.
- The local frontier files `_DyadicCocycleLargeDeviation.lean`,
  `_DyadicPhaseChainingSubmaxRefuted.lean`, `QRWorstCaseIncompleteSum.lean`, and
  `ConstantIndexGaussSumBound.lean`.

It is deliberately an audit note, not a proof claim. The prize core remains open.

## Five papers fetched for this pass

Saved under `~/papers/arklib/issue407/`:

| Paper | Local file | Role |
|---|---|---|
| Kowalski, *Exponential sums over small subgroups, revisited* | `arxiv-2401.04756-Kowalski-small-subgroups.pdf` | Clean modern statement of the BGK/sum-product barrier for small multiplicative subgroups. |
| di Benedetto et al., subgroup exponential-sum bounds | `arxiv-2003.06165-diBenedetto-KST-subgroups.pdf` | Best explicit power-saving line near `n > p^{1/4}`; still far from square-root cancellation. |
| Kopparty, *Recovering polynomials over finite fields from noisy character values* | `arxiv-2601.07137-Kopparty-noisy-character-values.pdf` | Modern Stepanov/pseudopolynomial technique adjacent to the thin-subgroup sum problem. |
| Kalmynin, *On additive irreducibility of multiplicative subgroups* | `arxiv-2504.10202-Kalmynin-additive-irreducibility.pdf` | Structural information about additive decompositions of multiplicative subgroups. |
| Hegyvári, *On the distribution of additive energy revisited* | `arxiv-2602.01781-Hegyvari-additive-energy-revisited.pdf` | Distributional/additive-energy companion to the moment side of the residual. |

## Reproducible checks run

`python3 scripts/probes/probe_gp_sota_gap_asymptotic.py`

- At `β = 4`, the explicit di Benedetto/KST exponent is `0.9892` in `n`, while the prize floor
  requires `1/2 + o(1)`.
- For `β > 4`, the explicit theorem is outside its stated `p^{1/4} < n < p^{1/2}` range.
- The missing gain is a power of `n`, not a constant or logarithm.

`python3 scripts/probes/probe_local_aligned_child_submaximality.py`

- The one-step `LocalAlignedChildSubmaximality` input is refuted.
- The concrete measured descent ratios include `M(i+1)/M(i) = 1.5618 > sqrt(2)` at
  `n = 2048 -> 4096`, `p = 4005889`.
- The local Lean refutation is already in `_DyadicPhaseChainingSubmaxRefuted.lean`.

`python3 scripts/probes/probe_cocycle_worst_path.py`

- Individual cocycle steps can approach `2`, so uniform one-step descent is the wrong target.
- The realized sup-norm cocycle geometric mean stayed in `[1.5043, 1.5384]` across the probed primes.
- The top-level ratios `M / sqrt(n * log(q/n))` stayed in `[1.337, 1.453]`, consistent with the
  floor envelope but not proving it.

## Surviving conjecture

Let `n = 2^μ`, `p` prime with `p ≡ 1 mod n`, and `n = p^{1/β}` with `β ∈ [4,5]`. Let
`μ_n ⊂ F_p^*` and

```text
M(n,p) = max_{b != 0} |sum_{x in μ_n} exp(2πi b x / p)|.
```

**Cocycle large-deviation conjecture.**

There is an absolute constant `C` such that

```text
M(n,p) <= C * sqrt(n * log(p/n))
```

through the prize tower. Equivalently, for the dyadic split cocycle

```text
S_b(μ_{2^{j+1}}) = S_b(μ_{2^j}) + S_{bz}(μ_{2^j}),
```

no single frequency has persistent near-`2` alignment down the whole tower:

```text
sum_j log(r_j / sqrt(2)) = O(log log p),
```

where `r_j` is the realized alignment-growth factor along the worst path.

Scores:

| Criterion | Score | Reason |
|---|---:|---|
| Novelty | 9 | The path/Lyapunov form avoids the refuted one-step phase lemma and states the residual as a tower-wide large-deviation law. |
| Insightfulness | 9 | It connects the MCA/list-decoding threshold, Gaussian-period sup norm, and 2-adic phase recursion in one quantitative object. |
| Prize proximity | 10 | It is exactly the proper-subgroup, constant-rate, `β ≈ 4..5`, worst-case regime of issue #407. |
| Feasibility | 6 | The deterministic consumer is formalized, but proving the bound would require a new BGK-strength-to-square-root theorem. |

Because feasibility is below 9, this is **not** a closed prize solution. It is the strongest surviving
candidate after the current refutations.

## What is already formalized

- `_DyadicCocycleLargeDeviation.lean` proves the deterministic path consumer:
  `CocycleGeometricMeanLaw -> floor_of_cocycleGeometricMeanLaw`.
- `_DyadicPhaseChainingSubmaxRefuted.lean` proves the one-step local submaximality target is equivalent
  to uniform `sqrt(2)` descent and gives a concrete countermodel.
- `QRWorstCaseIncompleteSum.lean` proves the index-2 special case via classical quadratic Gauss sums.
- `ConstantIndexGaussSumBound.lean` proves the same style of square-root cancellation for constant
  index subgroups, stopping exactly before the prize index `m ≈ 2^128`.

## Honest closure status

I did not find a complete proof of `δ*`. Every route that would make the conjecture closed still needs
the same missing analytic input:

```text
max_{b != 0} |sum_{x in μ_n} exp(2πi b x / p)| <= C * sqrt(n * log(p/n)).
```

Current literature gives BGK-type power savings or explicit bounds near/outside `n > p^{1/4}`, not the
required square-root cancellation in the prize regime. Claiming the prize solved from the present
material would fabricate exactly the open step that issue #407 identifies.
