# δ* Master Synthesis — 3-workflow assault + solo findings (2026-06-27)

Consolidates the session "prove δ* exactly / attack from every angle": **3 adversarial workflows
(48 distinct surfaces)** + solo number theory. Companion docs:
`deltastar-OPEN-MATHEMATICS-2026-06-27` (problem statement),
`deltastar-464-char0-energy-exact-closed-form`, `deltastar-464-wraparound-lattice-onset`,
`deltastar-464-bprocess-gauss-phase-duality`.

## Bottom line (strict-honest)

The δ* floor in the prize window **is** the Paley Graph Conjecture for `μ_n` (`B = max_{b≠0}|Σ_{y∈μ_n}
e_p(by)| ≤ √(2n ln p)`). Across **48 fresh surfaces in 3 workflows**, every angle either
`REDUCES_TO_PALEY` or is independent-but-already-reduced analytic NT; **no genuine bypass survived
adversarial verification.** This extends the campaign's ~60 prior confirmations. The wall is **not
closed** and will not be by known mathematics. What this session *did* produce: the char-0 half
closed in exact closed form (landed in Lean), two novel exact reformulations of the wall (lattice,
B-process), and the complete end-to-end dependency map pinpointing every remaining obligation.

## The end-to-end pin — dependency map (from WF2, verified against in-tree)

| node | what | state | Paley? |
|---|---|---|---|
| **N1** ceiling `δ*≤1−r/2^μ` (KKH26) | `kkh26_mcaDeltaStar_le` | **PROVEN** | indep |
| N2 `InteriorCeiling` (explicit bad line) | KKH26 Lemma1/Thm1 | reduced-to-input | indep |
| N3 `TZPrimeSupply` (U1) | window prime count | reduced; concrete to n=32768 | **indep** (analytic NT) |
| N4 poly field size (U2, Linnik) | `p≤C·n^β` | reduced-to-input | indep |
| **N5** floor consumer | `worstCaseIncidence_pin` | **PROVEN** | indep |
| **N6** `WorstCaseIncidenceBounded` | THE OPEN CORE, 4 faces | **DEEP-OPEN** | **= PALEY** |
| N6c-1 char-0 energy ceiling `≤Wick` | exact, r=2..9 + general | **PROVEN** (incl. my brick) | indep (shadow) |
| N6c-2 char-p transfer (DC-subtracted) | `S_r≤p·Wick`, r≈ln q | **DEEP-OPEN** | **= PALEY** |
| N8 `canonicalRatioBadPrimes` finite | resultant factors | **PROVEN** | indep |
| N9 good-prime supply | pigeonhole vs TZ | reduced; concrete to n~2^15 | indep |
| N10 width-4 refuter | `e2BadScalarSet` budget | **PROVEN** | indep |
| **N11 universal-domination bridge** | `StackDominates C δ (canonicalWitness)` | **DEEP-OPEN, ABSENT** | **= PALEY** |

**Two crisp takeaways from the map:**
1. The **entire ceiling (N1–N4)** and the floor *consumer* (N5) are proven or reduced to
   **Paley-independent** analytic NT (Thorner–Zaman, Linnik). The prize's hard core is **only** N6.
2. **N11 is the precise gap in the `land-exhaust` program.** The width-four lane reaches N9/N10
   (good prime ⟹ no width-4 collision ⟹ *one* bad-set predicate fails) but there is **zero** in-tree
   link from `canonicalRatioBadPrimes`/width-four to `StackDominates`/`WorstCaseIncidenceBounded`
   (grep-verified). Bounding the true stack-maximizer = bounding the sup-norm = **is Paley**.
   `FloorNecessaryNotSufficient.lean` already proves a one-direction bound is not the all-directions
   bound. So the land-exhaust route is honest substrate, not a floor proof — exactly as its own docs say.

## The five genuine findings this session

1. **Exact char-0 additive energy (LANDED).** `V_{2r}=Σ(2r)!/∏(mₖ!)²=C(2r,r)·Σmultinomial²=
   (2r)!·[tʳ]I₀(2√t)^{n/2} ≤ Wick`, verified 3 ways. `CharZeroEnergyMultinomial.lean` (the
   "remaining combinatorial half" the project flagged). WF1 independently reproduced E₃,E₄ exacts and
   a slicker `Q(x)⪯eˣ` power-series proof. ⟹ floor = exact statement about wraparound `W_r` only.

2. **Lattice onset characterization (novel).** Roots = signed basis vectors of `ℤ[ζ_n]=ℤ^{n/2}`;
   wraparound onset `r₀(p)=⌈ℓ₁-min(L_p)/2⌉`, `L_p={v:Σvᵢωⁱ≡0 mod p}` (covol p). Minkowski ⟹ generic
   onset `≈n/4≈2²⁸ ≫ ln p≈110`: **good primes abundant with exponential margin**; bad = sparse
   anomalously-short-ℓ₁ primes (= resultant factors). Converges with WF1's `|Norm(α)|≥p` lemma.

3. **Lattice↔resultant unification.** `BadPrimes(n,≤r)=⋃_{‖v‖₁≤2r} primeFactors(Res(Φ_n,P_v))`;
   the canonical width-four resultant is the special case of one relation `v`. Verified: every shortest
   `v` has `P_v(ω)≡0 mod p`.

4. **B-process Gauss-phase duality (novel, the sharpest reformulation).** `η(c)=(1/d)·DFT_d(τ)`,
   `|τ_s|=√p` **exactly** (verified 1e-14). So `B=(√p/d)·max_c|D(c)|`, `D=DFT` of a **unit** Gauss-phase
   sequence ⟹ the floor is a **pure-phase problem** that *structurally removes the phase-blind floor*
   (constant magnitude). Prize bound ⟺ Gauss-sum phases equidistribute (DFT `~√(2d ln d)`), a named
   problem in the **Katz / Fouvry–Kowalski–Michel "sums of products"** framework. Still the wall, but
   the correct target for any phase-aware attack and the one with proven deep technology.

5. **Complete dependency map** (above) — every node tagged, N11 identified as the land-exhaust gap.

## Workflow verdicts (48 surfaces)

- **WF1 (15 Paley angles):** ALL reduce. Confirmed clean bricks: near-Sidon `c₂(t)≤2` (μ_n is B₂[2]);
  `|Norm(α)|≥p`; Gauss-period inversion `m·η_b=Σχ̄τ` & `B=(1/m)‖DFT_m(τ)‖_∞`; E₃/E₄ exacts.
- **WF2 (20 end-to-end surfaces):** the dependency map; N11 the key gap. R1 (LD⇒MCA), R2 (curve-decod),
  R3 (universal domination), R4 (probabilistic) all open-research-or-Paley. Radical (subconvexity, RMT
  universality, LP/SDP, transfer-to-solved, motivic, containers) — none survived.
- **WF3 (13 novel angles):** Weil/metaplectic, Kurlberg–Rudnick cat-maps, Duke–Waldspurger, MacWilliams
  floor-ceiling duality, Newton-polygon, ultraproduct/pseudofinite — all `REDUCES_TO_PALEY` (confirmed).
  mixing-time/canonical-paths `DEAD_END`. Only **bombieri-iwaniec** `PARTIAL` = the B-process duality
  (finding #4), verified here.

## What is landable in Lean (ranked)

1. ✅ `CharZeroEnergyMultinomial` (DONE) — char-0 Wick bound.
2. **B-process duality** `η(c)=(1/d)Στ_s ζ^{−sc}`, `|τ_s|=√p`, `B=(1/d)‖DFT_d(τ)‖_∞` — pins floor to a
   constant-magnitude DFT sup; needs Mathlib `gaussSum` + `|τ(χ)|=√p`.
3. **`|Norm(α)|≥p`** (Lemma B) — `Int.le_of_dvd` + ideal-norm multiplicativity.
4. **Near-Sidon `c₂(t)≤2`** — Finset cardinality lemma (μ_n is B₂[2], modulo r=2 no-wraparound).
5. **E₃/E₄ exact** `=15n³−45n²+40n`, `=105n⁴−630n³+1435n²−1155n` — mirror `REnergyTwoExact`.
6. **Lattice→resultant bridge** `v∈L_p ⟹ p|Res(Φ_n,P_v)` — generalizes the width-four gate.

## Honest residual

The prize floor remains: **prove the prize prime (or a usable window prime) is lattice-non-anomalous /
its Gauss-sum phases equidistribute to depth ln p.** Equivalent forms: N6 / N6c-2 / N11 / Paley graph
conjecture / B-process Jacobi-phase moment. No known technique closes any of them. The contribution is
a sharper, multiply-cross-validated map of *exactly* where the one wall sits and the two best dual
coordinate systems (lattice ℓ₁-min; Gauss-phase DFT) for a future phase-aware attack.
