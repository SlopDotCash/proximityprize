# Root-number residual attack — RESULT: an EXACT new reduction + the correct conditional (subconvexity, NOT GRH), 2026-06-15

> **Correction (2026-10-28 audit, T48).**
> - **An identity is not an equivalence.** The shift-autocorrelation identity for `|A(h)|` is
>   useful. But "prize-flatness residual ⟺ bounding the short multiplicative sum" and "the prize IS
>   the Paley Graph Conjecture" promote it to an equivalence with the additive spectral maximum
>   `M(n)`. That would need a bound covering all Fourier phases and coefficients in the transform,
>   which is not supplied. A proposed shifted-character estimate should be stated as a hypothesis,
>   and its implication to `M(n)` proved, before it is called an established conditional
>   implication.
> - **Correlation does not show irrelevance.** A measured Pearson correlation of `0` between
>   `arg ε(χ)` and `|L(1/2, χ)|` cannot prove that GRH is logically irrelevant. "Proven irrelevant" is
>   withdrawn; GRH is simply not the hypothesis this route uses.
> - The conjugate-symmetry correction (correction 1 below) stands.

Attacked the named residual (effective fixed-q equidistribution of the root-number phase sequence) from
10 directions + an all-other sweep. NO unconditional path (wall re-confirmed), but a genuine clean output.

## The clean NEW exact reduction (machine-verified to 1e-15, independently twice)
The max-shift autocorrelation of the root-number phase sequence collapses EXACTLY to a SHORT MULTIPLICATIVE
CHARACTER SUM over the subgroup-shift 1+μ_n:
  **|A(h)| = (m/√p)·|Σ_{ζ∈μ_n} χ₁^h(1+ζ)|**   (χ₁ = generator of H⊥).
(My equivalent derivation: A(h)=(g(χ_h)/q)Σ_k J(χ_{k+h},χ_{−k}), fixed product χ_h; the workflow simplified
the Jacobi-sum sum to the short character sum over 1+μ_n.) So the prize-flatness residual ⟺ bounding the
short multiplicative character sum `max_χ |Σ_{ζ∈μ_n} χ(1+ζ)| ≤ C√(n log m)`.

## Honest verdict: this is the MULTIPLICATIVE DUAL of M(n) — circular for unconditional, but the right object
`Σ_{ζ∈μ_n}χ(1+ζ)` is the multiplicative-character dual of the additive Gauss period `M(n)=max|Σ_{x∈μ_n}e_p(bx)|`
— SAME WALL, new name (the additive↔multiplicative Fourier involution). It is NOT unconditionally bounded:
no geometric-progression/van-der-Corput structure (phase increments std≈2 rad), NOT Sidon (difference
multiplicity ≈m), and the only standard theorem (Weil √p on the Jacobi average) is VACUOUS by √(m/log m)
which DIVERGES (3.0→8.8 in-probe) — the Burgess barrier n≈p^{1/4}; at the prize β≥4, n≤p^{1/4}, Burgess
itself vacuous.

## LEGITIMATE conditional result (fixed-q, exact, Lean-formalizable)
**Subconvexity / a Burgess-beyond-p^{1/4} bound for `max_χ|Σ_{ζ∈μ_n}χ(1+ζ)| ≤ C√(n log m)` — equivalently
the PALEY GRAPH CONJECTURE for Cay(F_q, μ_n) — ⟹ the prize M(n)≤C√(n log m) ⟹ fixed-q root-number L∞
flatness.** The reduction is exact and attaches to in-tree GeneralizedPaleyRamanujan.lean /
WorstCaseIncompleteSumBound. This is the right named conjecture (the prize IS the Paley Graph Conjecture
for this graph, now reached via the root-number/multiplicative-dual route too).

## Two CORRECTIONS to this session's prior claims (honesty)
1. The real-DFT brick's hypothesis is the **conjugate-symmetry s_{m−k}=conj(s_k)** (which the Lean brick
   ArchimedeanPhaseRealDFT.lean correctly used) — NOT the additive "θ_{−k}=−θ_k" as a literal real-number
   identity (arg branch-cuts make that fail numerically at ~2.0). The Lean brick is correct as written
   (it uses s(−k)=conj(s k)); only the prose description is corrected.
2. **GRH is the WRONG conditional hypothesis** — proven irrelevant: Pearson(arg ε(χ), |L(1/2,χ)|)=0.0000;
   the root number is the functional-equation CONSTANT, orthogonal to GRH zero data. **Subconvexity /
   Paley Graph Conjecture is the correct hypothesis.**

## Net
The archimedean-phase/root-number directive, pursued exhaustively, yields: the cleanest exact reduction
(prize = short multiplicative character sum over 1+μ_n = Paley Graph Conjecture), the correct conditional
hypothesis (subconvexity, not GRH), the axiom-clean real-DFT brick, and an honest re-confirmation that the
unconditional core is the Burgess-barrier wall. In-tree corroboration: _RootNumberAutocorrelation.lean,
_GrossKoblitzPhaseNoGo.lean, _DyadicJacobiCocycleNonContraction.lean. Full synthesis:
rootnumber-residual-attack-2026-06-15.md.
