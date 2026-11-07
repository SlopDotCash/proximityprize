# Definitive result: 72 invented theorems for RS-list-decoding-past-Johnson over μ_{2^a} → 0 closures (#407/#444)

> **Scope correction (2026-10-28 audit, T48).** This is a record of one generative search: 72
> candidates, screened. It is not a theorem about mathematics.
> - "No accessible route exists", "does NOT reduce to proven math by ANY route" and "beyond all
>   current technique" do not follow from 72 failed candidates. They describe this search only.
> - The six "equivalent open quantities" are distinct unproved estimates. Some are linked by one-way
>   sufficient conditions; no equivalence among all six is established.
> - The Ramanujan-scale target `B ≤ 2√n` is strictly **stronger** than the prize-scale bound
>   `B ≲ √(n log q)`, and the two are not established to be equivalent. Proving the prize-scale
>   bound would not prove the Ramanujan property, and the prize may not need it.
>
> The individual refutations (for example the `3504 ≫ 16` char-0 incidence) remain valid finite
> results.

**2026-06-15. The most thorough generative assault possible: 88 agents, 3.3M tokens, 12 angle-families
(normal→insightful→crazy→cross-domain), adversarially screened + deep-dived + the one self-claimed closer
computationally refuted.**

## Tally
- 72 candidate CLOSED theorems generated (5-6 each across 12 families: GS-interpolation, exact-higher-MDS,
  circulant/DFT-Siegel, FRI-fold, Galois-descent, exact-2-power-additive-comb, AG/Drinfeld, Stepanov/Wronskian,
  cyclic/BCH/trace, spectral/Ramanujan/random-matrix, 2-adic/Newton-polygon, wildcard tropical/SoS/rigidity/Minkowski).
- 66 screened: **33 moves-to-open · 17 refuted-false · 16 only-Johnson-or-trivial · 0 closes.** (6 died on transient API errors.)
- 8 deep-dives: all confirmed moves-to-open; C-DFT-5's "list≤n/2" cap REFUTED by exact probe (real list=148 > n/2=8 past Johnson).
- 6 unscreened recovered manually: **AG-4 (the ONLY self-claimed closer) REFUTED by direct computation** —
  it claims far-line incidence ≤ n at s=k+1 via Lam-Leung collapse, but char-0 incidence at n=16,s=5 = **3504 ≫ 16**
  (n=8,s=3 = 40 > 8). Lam-Leung bounds coincidence TYPES not the distinct-γ count. The other 5 are moves-to-open.

## The gate map (every moves-to-open funnels into ONE cluster of 6 equivalent open quantities)
| count | open quantity |  facet |
|---|---|---|
| 19 | additive-energy / sumset (BCHKS Conj 1.12) | additive |
| 16 | the list-size itself | coding |
| 11 | higher-order-MDS / explicit≈generic | coding |
| 11 | Gauss-period B=max\|Σ_{x∈μ_n}e_p(bx)\| (Paley-graph spectral radius) | analytic |
| 8 | equidistribution / Sato-Tate (uniform Katz) | analytic |
| 6 | Kelley / general-position vanishing-subsum count | additive |
These are the SAME problem in different clothes: B≤2√n ⟺ Cay(F_q,μ_n) Ramanujan ⟺ Paley Graph Conjecture for
thin 2-power multiplicative subgroups (n=p^0.19). Best PROVEN bound: BGK n^{1-o(1)}, off by n^{0.4}. OPEN.

## Structural pattern (identical across all 12 families)
Every candidate has a GENUINELY PROVEN, axiom-clean, in-tree SPINE that reaches Johnson / sub-Johnson
(DFT block-diag, antipodal even/odd descent, Sidon energy, GS/Sudan list, Plotkin, Minkowski λ_1=n-k+1,
Hoffman-Wielandt) — then needs EXACTLY ONE of the 6 quantities to cross Johnson, where it re-leaks the
p-DEPENDENT past-Johnson content (the p-independent cyclotomic invariants are all structured-prime-blind
and stop at the p-blind Sudan/Johnson radius; the prize lives in the p-dependent part).

## Conclusion (definitive, overdetermined)
After the most exhaustive generative campaign feasible, **explicit-RS list-decoding past Johnson over μ_{2^a}
does NOT reduce to proven math by ANY route** — it IS the open core (Paley-graph / thin-subgroup Gauss-period
bound), in one of six equivalent forms. No closed δ* proof exists among accessible mathematics. The prize
requires a genuine analytic-NT advance (√n cancellation for thin 2-power subgroup character sums) that is
beyond all current technique. This is not a failure of effort or imagination — 72 diverse bold attempts,
adversarially verified — it is the mathematical reality.
