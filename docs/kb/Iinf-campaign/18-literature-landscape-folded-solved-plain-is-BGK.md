# The proximity-prize literature landscape (2025–2026): folded codes proved (GG25), plain RS open (BGK wall)

Researched the recent literature on exactly what the prize reduces to (the hook's instruction: find recent
papers on the reduced forms). The picture: **Goyal–Guruswami (STOC 2026) prove optimal proximity gaps to
capacity for folded RS / univariate multiplicity (subspace-design) codes and random RS, under those papers'
code, parameter and curve-decodability hypotheses — the N6 route. The pinned challenge (DOSSIER §1.1:
`C := RS[F, L, k]`, plain RS on a smooth domain) is EXPLICIT PLAIN RS on a fixed smooth `μ_n`, which those
theorems do not cover; we call its open core the BGK wall.** This reconciles my own N6 finding
(curve-decodability is the one non-reducing object, inert for `μ_n` RS) with the published SOTA.

> **Scope correction (2026-10-28 audit, T126; evidence
> `docs/audits/repository-review-2026-10-28/kb42-literature-scope-checks.json`, abstract-level checks only).**
> *Code folding* (a folded-RS code with its own alphabet, metric and subspace-design property) is not the same as
> *protocol folding* (FRI/STIR's challenge-dependent folding of an original scalar RS codeword). A protocol that
> folds does not thereby instantiate the folded-code capacity theorem: the code, metric and curve-decodability
> hypotheses, the parameters, and a security-composition theorem for the deployed protocol would all have to be
> supplied. The naive folded→plain list transfer is machine-refuted in-tree
> (`ArkLib/Data/CodingTheory/ProximityGap/FoldingTransferNoGo.lean`). Claims below that deployed FRI/STIR are
> "in the SOLVED column" are withdrawn; the per-paper guards are restated in the reading list.

## Reading list (the 5 key recent papers, for download)
1. **ABF26 — "Open Problems in List Decoding and Correlated Agreement"** (eprint 2026/680, Arnon–Boneh–Fenzi).
   THE grand-challenge statement (Grand-MCA + Grand-list-decoding). The prize's definition of success.
2. **Goyal–Guruswami — "Optimal Proximity Gaps for Subspace-Design Codes and (Random) Reed-Solomon Codes"**
   (eprint 2025/2054, STOC 2026). **Closes the proximity gap to capacity `1−R−η` for folded RS, univariate
   multiplicity codes (subspace-design), and RANDOM RS** — via the **curve-decodability** property. Field size
   only LINEAR in block length. This is the published version of the N6 route. (Note: arXiv:2601.10047, a
   competing FRS proof, was WITHDRAWN as subsumed by this.)
   Guards: the theorem is about those specified code families under their stated hypotheses; it is not an
   automatic statement about a protocol that folds a plain RS codeword (see the scope correction above).
3. **Jo, "Interleaving Stability for MCA and Curve Decodability"** (eprint 2026/891). Row-wise interleaving
   imposes no linear loss on generator-MCA: exact transfer when the seed-set size is `≤ q`; the
   curve-decodability transfer carries a separate condition `binom(a,b) ≤ q`. Addresses the affine-line MCA
   interleaving-loss open problem from ABF26. Strengthens the curve-decodability toolkit.
4. **"All Polynomial Generators Preserve Distance with MCA"** (eprint 2025/2051). States a general MCA result
   for polynomial generators over linear codes, with a Reed–Solomon specialization in the **Johnson range**. It
   is not an automatic capacity-range result for every explicit RS code.
5. **Crites–Stewart, "On Reed–Solomon Proximity Gaps Conjectures"** (eprint 2025/2046). Refutes selected RS
   proximity-gap / correlated-agreement conjectures in the near-capacity regime and gives a **one-way**
   implication: small-error correlated agreement implies list decoding. It does not establish a universal
   equivalence with any specific spectral target, and it does not by itself locate `δ*`; the window-edge form
   `1−ρ−Θ(1/log n)` is the project's working target, not a consequence of this paper.
   (Plus Habock 2025/2110: RS-MCA exactly up to Johnson, vacuous AT Johnson.)

## The landscape, precisely
| code | proximity gap / MCA to capacity | status |
|---|---|---|
| Folded RS, univariate multiplicity (subspace-design) codes | YES, `1−R−η`, under GG25's hypotheses | **Proved for these codes** (GG25, curve decodability) |
| Random RS | YES, to capacity, under the papers' parameters | **Proved for random RS** (BGM STOC'23 + GG25) |
| **Explicit PLAIN RS on a fixed smooth `μ_n` (FRI) domain** — the pinned challenge code | working target `1−ρ−Θ(1/log n)` | **OPEN** (the prize; open core called the BGK wall here) |
| Deployed FRI/STIR protocols (protocol folding of plain RS) | not instantiated by the folded-code theorem | **Not resolved by these results**; needs code/metric/parameter transfer + composition |

The mechanism split is exactly my N6 finding: **curve decodability** (subspace-design / strong list-recovery)
is the beyond-Johnson engine, and it WORKS — for codes that have the subspace-design property (folded /
multiplicity / random). Explicit plain RS on the deterministic `μ_n` domain **lacks** it (proven in-tree
`RadiusOneExact`: `B=I`), so its δ* is governed by the thin-2-power Gauss-period sup-norm = BGK.

## What this means for the prize (honest, and genuinely useful)
1. **WITHDRAWN (T126): "deployed FRI/STIR are in the SOLVED column".** FRI/STIR fold *as a protocol step*,
   but their committed code is the original scalar RS code on a smooth domain. GG25's theorem is about folded
   codes and other subspace-design families under specified hypotheses; it does not, without an explicit
   encoding, parameter and metric transfer plus a security-composition theorem, give deployed FRI/STIR
   soundness at capacity. The in-tree `FoldingTransferNoGo` shows the naive folded→plain transfer fails.
   The deployed question therefore stays tied to the plain-RS problem below.
2. **The prize's open grand challenge is the harder, specific case: explicit PLAIN RS on a fixed smooth
   domain at the window edge.** That is the irreducible BGK/Paley thin-2-power-subgroup √-cancellation wall,
   which my 14-attack sweep + #444 + the sibling fleet (71 non-BGK refuted) all confirm is open, with no
   standard-conjecture close (GRH structurally inert), best bound `n^{1−o(1)}`.
3. **The one genuinely-different direction is therefore real and published, not a dead lead:** it is the
   curve-decodability / subspace-design route (GG25, 2026/891). It does not solve plain RS. The challenge
   definition is **not** an open project-control question: the pinned statement (DOSSIER §1.1, from
   proximityprize.org + ABF26) fixes `C := RS[F, L, k]` with smooth evaluation domain `L`, i.e. plain RS. A
   folded-RS capacity theorem therefore does not answer it; using GG25 would require a proved transfer from the
   folded code to that plain code, which the naive route does not give (`FoldingTransferNoGo`).

## Verdict
No closure of the plain-RS core (open; the "irreducible by current methods / exact missing input = effective
horizontal cyclotomic Sato-Tate" framing is this campaign's assessment, not a theorem). The literature research
records: **optimal proximity gaps to capacity are proved for subspace-design/folded codes and random RS via curve
decodability (GG25 STOC 2026), under those papers' hypotheses; the pinned challenge code is explicit plain RS on
`μ_n`, which those results do not cover; and protocol folding in FRI/STIR is not an instantiation of the
folded-code theorem.** Reading list of 5 papers banked for download. Related: docs 16,17 (the 14-attack
no-escape verdict); #444 §0.0.
