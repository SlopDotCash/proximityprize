# δ* sweep A27 — conditional LD ⟹ MCA collapse with `q/(q−1)` loss (PARTIAL/reduction)

**Date:** 2026-06-14 · **Actionable:** A27 (mergedFrom 334-T08) · **Type:** lean-brick (pure assembly)
**Status:** landed conditional reduction (axiom-clean), open antecedent unchanged.

## What A27 asked

Compose three *landed* in-tree ingredients into the forward conditional LD ⟹ MCA collapse
with explicit `O(1)` loss (ABF26 §5 "list-form" face of the prize):

1. `ProximityGap.Jo26Gen.epsMCAGen_interleaved_le_factor` — [Jo26] Thm 4.2: interleaved
   generator-MCA ≤ `(qˢ−1)/(qˢ−qˢ⁻¹)` · base generator-MCA.
2. `ProximityGap.Jo26Gen.epsMCAGen_pairGen_eq_epsMCA` — affine-line bridge to the in-tree
   `ProximityGap.epsMCA` (+ `ProximityGap.epsMCA_interleaved_eq`).
3. `ProximityGap.CurveDecodable` / `GG25Lemma32.all_seeds_relClose_of_curveDecodable`
   ([GG25] Thm 3.3) — the mechanism that *delivers* a good base MCA bound.

## What was actually landed

**Artifact:** `ArkLib/Data/CodingTheory/ProximityGap/Frontier/Sweep_A27_CondLDtoMCA.lean`
(axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorryAx`).

The **one missing arithmetic step** (everything else was already proven in-tree) is the
collapse of the seed-dependent Jo26 factor to the clean, `s`-uniform loss `q/(q−1)`:

> `jo26_factor_le_qratio` :  `(qˢ − 1)/(qˢ − qˢ⁻¹) ≤ q/(q − 1)` in `ℝ≥0∞`, every `q ≥ 2`, `s ≥ 1`.

Proof = the cross-multiplied ℕ fact `(qˢ−1)·(q−1) ≤ qˢ·(q−1) = q·(qˢ−qˢ⁻¹)` transported to
`ℝ≥0∞` via `ENNReal.le_div_iff_mul_le` + `ENNReal.div_le_iff` (no nonexistent `div_le_div_iff`).

Composed theorems:
- `epsMCAGen_interleaved_le_qratio` — the `q/(q−1)` collapse, **any** generator:
  `ε^gen_mca(G, C^⋈s, δ) ≤ (q/(q−1))·ε^gen_mca(G, C, δ)`, uniformly in `s`.
- `epsMCAGen_interleaved_le_qratio_of_base_le` — forward conditional (general generator).
- `epsMCA_interleaved_le_qratio` — affine-line specialization on the repo's prize surface
  `ProximityGap.epsMCA` (via the pair-generator bridge).
- `epsMCA_interleaved_le_qratio_of_base_le` — `epsMCA(C,δ) ≤ eps ⟹ epsMCA(C^⋈s,δ) ≤ (q/(q−1))·eps`.
- `BaseMCAFromCurveDecodable` (named `Prop`, the open antecedent = "a curve-decodability /
  good-interleaved-list-bound profile of `C` yields base MCA error `eps`") +
  `epsMCA_interleaved_le_qratio_of_curveDecodable` — the full A27 chain.
- Non-vacuity `example` over `⊥ : Submodule (ZMod 5) (Fin 3 → ZMod 5)`.

## Numerical evidence

**Probe:** `scripts/probes/sweep_A27_condldmca.py` — 2800 exact-rational checks, **0 violations**.
- `factor(q,s) ≤ q/(q−1)` for q ∈ {2,3,…,2⁶¹−1, prize stand-ins n·2¹²⁸+1, n=2²⁵..2⁴⁰}, s ≤ 200.
- `factor(q,1) = 1` always; factor is **increasing** in `s`, sup = `q/(q−1)` (approached, never
  attained). So `q/(q−1)` is the tight `s`-free constant; any fixed `s` is even better.
- At prize scale `q ≈ n·2¹²⁸` the loss `q/(q−1) − 1 = 1/(q−1) ≈ 2⁻¹⁵³..2⁻¹⁶⁸`, i.e. the
  collapse is **essentially lossless** in the prize regime.

## Honest scope (what is NOT closed)

This is a **conditional reduction with explicit `O(1)` (in fact `1 + 2⁻¹²⁸`) loss**, NOT a prize
closure. The loss factor and interleaving stability are fully proven; the *input* —
`BaseMCAFromCurveDecodable`, a good base MCA / curve-decodability bound for explicit
smooth-domain RS in the gap `(1−√ρ, 1−ρ−Θ(1/log n))` — is the **open core** and is never
discharged here (named `Prop`, per the §6 modularity convention). GG25 supplies
curve-decodability only for folded / multiplicity / random / subspace-design RS, *not* explicit
plain smooth-domain RS; the δ* open core is untouched.

Note also: on the affine line, `epsMCA(C^⋈s,δ)` is in fact *exactly* invariant under
interleaving (`epsMCA_interleaved_eq`), so the `q/(q−1)` bound is loose there — the value of the
result is the **seed-set-agnostic** `O(1)` loss for arbitrary generators (curves), placed on the
prize surface.

## References
- [ABF26] ePrint 2026/680 §5, Def 4.3. · [Jo26] ePrint 2026/891 Thm 4.2. · [GG25] ePrint
  2025/2054 Def 3.1, Thm 3.3.
