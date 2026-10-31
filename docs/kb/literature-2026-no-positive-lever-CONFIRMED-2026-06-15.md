# Literature sweep (fresh, 2026-06-15): the 2026 activity is ALL ceiling/failure; NO positive lever for the floor

> **Source-scope corrections (2026-10-28 audit, T48; cross T62/T87).** This is a historical search
> report, not proof that contemporary mathematics lacks a positive route, and the audit check below
> was a primary-abstract check, not a complete new literature search or a full audit of the papers.
> - **Failure constructions keep their hypotheses.** Primary abstracts confirm that ePrint
>   2026/782 and arXiv:2604.09724 are failure constructions. Their code-family and radius
>   hypotheses cannot be erased when applying a ceiling to other codes or radii.
> - **Date.** arXiv:2604.09724 was submitted on 9 April 2026, not 1 April.
> - **Rank-2 GAP paper.** arXiv:2509.07765 has a January 2026 revision. Its proper-GAP domain does
>   not itself supply the desired subgroup bound.
> - **The addendum overreaches.** A decreasing correlation with one chosen fixed-arc proxy, at
>   `n = 16, 32, 64`, cannot show that every interval or discrepancy inequality, or every moment
>   method, is insufficient. "Every single-scale tool … is therefore structurally insufficient" is
>   withdrawn as a general claim.

## What the directive asked: find new papers / a new lever for the core M(n) ≤ C√(n log m)

Fresh web search (June 2026). Decisive, honest finding: **the only 2026 papers on the exact prize object
prove the FAILURE/CEILING direction (δ* ≤ capacity − Θ(1/log n)); NONE provides a positive cancellation
bound (the floor = the open prize).**

### The two 2026 papers on the exact object — both CEILING (negative), confirming what we have
- **Haböck–Krachun–Kazanin, "Failure of proximity gaps close to capacity," ePrint 2026/782** (20 Apr
  2026). Proves proximity gaps FAIL near capacity for RS over multiplicative subgroups of prime fields,
  via "a new additive-combinatorics lemma on sums of roots of unity." This is the CEILING (the easy
  negative direction). PDF Cloudflare-403-blocked to WebFetch — pull via institutional access for the
  exact lemma, but the abstract confirms it is the failure direction. Does NOT prove the floor.
- **Kambiré, "Proximity Gaps Conjecture Fails Near Capacity over Prime Fields," arXiv:2604.09724**
  (1 Apr 2026). Proves proximity gaps fail at radii O(1/log n) below capacity for a specific RS family.
  Explicitly a NEGATIVE result; no positive cancellation / upper bound on δ*; no character-sum technique.

Both CONFIRM the in-tree ceiling (`kkh26_mcaDeltaStar_le_capacity_sub_log`) — δ* ≤ capacity − Θ(1/log n).
Neither touches the FLOOR (that δ* reaches that ceiling, i.e. M(n) ≤ C√(n log m)).

### The positive direction (the floor / the prize) — NO 2026 lever
Search for 2026 character-sum / Paley-graph / Burgess / thin-subgroup √-cancellation positive results:
the most recent positive-direction work is pre-2026 (Burgess refinements arXiv:1711.10582; rank-2 GAP
Burgess arXiv:2509.07765 Sep-2025; BGK-era small-subgroup sums arXiv:0705.4573). SOTA for thin 2-power
subgroups at β=4 stays the di Benedetto–Garaev line (n^{1−31/2880}=n^{0.989}, needs β<4; collapses to
n^{0.99998} at exactly β=4). NO paper crosses n^{0.989} → n^{0.5} at the Burgess barrier.

## Net (honest, definitive for this session)
The prize floor M(n) ≤ C√(n log m) at β=4 has NO new lever as of June 2026. The 2026 community activity
is entirely on the ceiling (failure) direction — which AGREES with this campaign's proven ceiling and
does NOT advance the floor. Combined with: every classical route eliminated (§8), 6 fresh domains
refuted (bold-conjecture-assault), cube-Fourier reduced to EVT, bilinear collapsing at β=4 — the floor
is the recognized open BGK/Paley wall, and no external math currently exists to apply. The structural
necessary condition (b-sensitive + deterministic-archimedean + genuinely L∞) stands as the constraint
any future positive result must satisfy.

Sources: eprint.iacr.org/2026/782, arxiv.org/abs/2604.09724, eprint.iacr.org/2025/2110 (Haböck MCA note).

## ADDENDUM: M(n) is NOT single-arc subgroup discrepancy — it is the full Fourier L∞ (sharper necessary condition)
Tested the constructive reading of the necessary condition: is M(n) the L∞ discrepancy of b·μ_n in a
single short arc (the Burgess / subgroup-in-interval object)? NUMERIC (n=16,32,64, β=4, worst b exact):
the correlation corr(|η_b|, max single-arc concentration) DECREASES with n (0.52 → 0.24 → 0.16), and the
worst-b for |η_b| is NOT the most arc-concentrated b (conc@argM falls to 5 vs maxconc 12 at n=64). So
**M(n) is NOT reducible to single-interval subgroup discrepancy** — even Burgess-type interval results do
not directly give it. The worst-b alignment is a GLOBAL multi-scale phase-coherence (consistent with the
cube-Fourier "energy spreads to middle Walsh weights = random-like" finding): M(n) is the genuine FULL
FOURIER L∞ sup-norm of the subgroup-indicator's transform, strictly harder than any single-scale count.
This SHARPENS the necessary condition's third clause: "genuinely L∞" = full-Fourier-L∞ (sup over all
frequencies' coherent contribution), not single-arc. Every single-scale tool (intervals, energy, moments)
is therefore structurally insufficient — confirming why the wall is irreducible to the standard toolkit.
