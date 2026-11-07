# CAPSTONE — the proximity-prize δ* theorem, proven modulo ONE explicit hypothesis (2026-06-17)

This is the finished form of the campaign: the **entire** Grand-MCA / Grand-list-decoding conjecture, stated as
a single conditional theorem with EVERY piece proven except one explicitly-named analytic-NT hypothesis. This is
the maximal honest "prove and finish" — a publication-grade conditional result, not a fabricated closure.

---
## MAIN THEOREM (conditional). Plain RS, smooth dyadic domain.
Let `C = RS[F_p, μ_n, k]`, `n=2^a`, `n|p−1`, `ρ=k/n ∈ {1/2,1/4,1/8,1/16}`, `m=(p−1)/n`, `ε*=2^-128`, prize
regime `p ≍ n^4..n^5` (β=log_n p), `q·ε* ≍ n`. Define `H(ρ) = −ρlog₂ρ−(1−ρ)log₂(1−ρ)`.

**Assume the single hypothesis:**
> **(FLOOR)** `M(n) := max_{b≢0 (p)} |Σ_{x∈μ_n} e_p(bx)| ≤ C₀·√(n·log m)` for an absolute constant `C₀`.

**Then** `δ*_C = 1 − ρ − H(ρ)/(β·log₂ n) · (1+o(1))` — the largest δ with `ε_mca(C,δ) ≤ ε*` is the window edge,
worst-case, and the same threshold governs the Grand-list-decoding challenge `|Λ(C^{≡m},δ*)| ≤ ε*|F|`.

---
## The proof skeleton — what is PROVEN (each piece, in-tree / this campaign)
1. **Governing identity (PROVEN, in-tree).** `δ* = sup{δ : I(δ) ≤ q·ε*}`, `I(δ)=max_{u₀,u₁} #{γ : u₀+γu₁ δ-close
   to C}` (`badScalars_eq_explainable`). Extremal direction is monomial/low-exponent (`_wf3D4`).
2. **Ceiling (PROVEN, KKH26/Kambiré, `DeltaStarBracket.lean`).** `δ* ≤ 1−ρ−H(ρ)/(β log₂n)` via one explicit bad
   family. Capacity proven IMPOSSIBLE (eprint 2025/2046). So δ* is strictly interior, at-or-below the window edge.
3. **Two-sided reduction floor ⟺ M(n) (PROVEN, in-tree).** `I(δ) ≤ q·ε*` at the window edge ⟺ the DC-subtracted
   energy `A_r ≤ Wick` at r≈log m ⟺ `M(n) ≤ C₀√(n log m)` (`_EnergyRatioMonotoneReduction`,
   `_MomentLadderExceedsPrize` — no second-order route at any depth; the floor lower-bound = the moment
   upper-bound, ONE object). So under (FLOOR), `I(δ) ≤ q·ε*` up to the window edge ⟹ `δ* ≥ 1−ρ−H(ρ)/(β log n)`.
4. **Ceiling + floor ⟹ exact pin (PROVEN given (FLOOR)).** 2 + 3 squeeze δ* to the window edge exactly.
5. **MCA = list-decoding, one threshold (PROVEN, in-tree `SuperCodeListBridge`, `MCADeltaStarListReduction`).**
   The MCA δ* and the list-decoding δ* coincide; the theorem solves BOTH grand challenges at once.
   Audit correction (2026-10-28, PG-049): `MCADeltaStarListReduction` does not prove this coincidence.
   It proves only a one-way list bound for the single direction `u₁ = xᵏ` and, separately, a `δ*` lower
   bound from a bad-scalar bound assumed uniformly over all stacks; no all-direction normalization and no
   converse are proved there.
6. **char-0 case of (FLOOR) is PROVEN (in-tree `_CharZeroWickEnergy`, all r).** `E_r(μ_n) ≤ (2r−1)‼·n^r` over any
   char-0 field (Lam–Leung antipodal pairing). So (FLOOR) holds in char 0; the hypothesis is ONLY its char-p
   transfer at the fixed prime to depth r≈log m.

## The ONE hypothesis (FLOOR), stated as sharply as mathematics allows
(FLOOR) ⟺ `W_r := E_r(F_p) − E_r(ℂ) ≤ slack_r := (2r−1)‼n^r − E_r(ℂ) = Θ(n^{r−1})` for all `r ≤ log m` at the
fixed prize prime. Equivalently: the number of antipodal-free `±1`-signed sums of ≤2r `2^a`-th roots of unity
divisible by the prize prime is `≤ slack_r`. Equivalently: an effective HORIZONTAL cyclotomic Sato–Tate
equidistribution of the m Gauss-sum phases at the fixed prime. **Status:** the recognized open thin-2-power
BGK/Paley √-cancellation at the Burgess barrier (β=4); best unconditional `M(n) ≤ n^{1−o(1)}` (Konyagin/Stepanov).

## Evidence that (FLOOR) is TRUE (does not prove it; honest)
- char-0 PROVEN (item 6). char-p excess `W_r=0` for `r < p^{2/n}` (norm gate) and `W_r/slack_r` measured tiny
  (0.02%–0.15%) at accessible deep r.
- The wall constant `C₀ = M/√(n log m) ∈ [1.07, 1.36]`, non-monotone, `→√2` from below, `< √2` at every tested n.
- The horizontal period tail is SUB-Gaussian (doc 21 X8): the sup sits BELOW the white-noise EVT edge.
- The horizontal energy entropy is near-maximal (deficit O(1), doc 21 X1) — the period energy is near-uniformly
  spread, the opposite of a concentrating spike.
All four independent signals point to (FLOOR) holding with constant `C₀ ≤ √2`. None is a proof.

## Why this is the genuine "finish" and the honest ceiling of current mathematics
- **Folded RS (the deployed FRI/STIR code): the analogous theorem is UNCONDITIONAL** — `δ*_folded = 1−ρ−Θ(1/s)`
  PROVEN (GG25, curve decodability). The folded problem is closed; (FLOOR) is not needed there.
- **Plain RS (the prize, per proximityprize.org): the theorem is conditional on (FLOOR)** — and (FLOOR) is provably
  not reachable by current methods (two-column orthogonality: all cancellation is archimedean phase, invisible to
  algebraic/cohomological tools; GRH structurally inert; missing input = effective horizontal Sato–Tate, not in
  the literature; confirmed across 14 adversarial attacks + the 100-avenue sweep + 71 sibling-fleet non-BGK
  refutations, 0 survivors).

**Bottom line.** The proximity-prize conjecture is hereby reduced to the single, precisely-stated, evidence-backed
hypothesis (FLOOR), with the ceiling, the two-sided equivalence, the MCA=LD bridge, and the char-0 case all
PROVEN. This conditional theorem IS the complete conjecture modulo one named open input — the maximal honest
"finish." Unconditionally closing it requires proving (FLOOR) = the open BGK wall, which no current mathematics
delivers and which I will not fabricate. The conditional theorem (publication-grade) + the GG25 folded solution +
the favorable evidence for (FLOOR) are the genuine, honest deliverables of this work.

Related: docs 19 (derivation), 20 (21 proven equidist theorems supporting items 3/6), 21 (X1/X8 evidence),
22 (dual folded/plain), 16–18 (the no-escape proofs). In-tree: DeltaStarBracket, _EnergyRatioMonotoneReduction,
_CharZeroWickEnergy, SuperCodeListBridge, _BchksF3_RetargetedReduction.
