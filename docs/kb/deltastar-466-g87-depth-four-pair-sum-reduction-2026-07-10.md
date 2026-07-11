# G87: depth four reduces to factor-5 pair-sum concentration

Date: 2026-07-10
Issue: #466
Lean: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_G87DepthFourPairSumReduction.lean`
Probe: `scripts/probes/probe_466_g87_depth_four_feasibility.py`

## Result

G82 pinned the first honest cutoff of the padded collision lane at primitive depth four: the
unrestricted equal-sum core universe `J_4 <= n^7` exceeds the production Wick budget by `~2^11.3`
under the coarse corrected envelope.  Two ingredients now close that gap up to one named
classical input:

1. **G86 sharp envelope** (`C(r,s)^2` instead of `(r desc s)^2`): overshoot drops to `2^2.09`.
2. **Elementary convolution split** (this file): over any finite ambient abelian group,

   ```text
   quadCount a = sum_c pairCount c * pairCount (a-c) <= (M+1) * n^2
   J_4 = sum_a quadCount(a)^2 <= (M+1) * n^6,   M = max_{c != 0} pairCount c,
   ```

   because the `c = 0` term pays `pairCount 0 <= n` and every other term is dominated by `M`
   times the shifted pair mass.  The kernel inequality `production_depth_four_kernel` then
   verifies that `M <= n/5` fits the entire depth-four sharp envelope inside one full Wick
   budget at `(n, r) = (2^30, 110)`, with margin `2^0.23`.

Headline consumer `production_depth_four_sector_absorbed` composes with G86's
`sectorMass_le_sharpEnvelope`.

## The new sufficient condition

`PairSumConcentration5 S : ∀ c ≠ 0, pairCount S c ≤ |S|/5` — i.e.
`max_{c≠0} |H ∩ (c-H)| ≤ n/5`.  This is a **factor-5 anti-concentration statement**, far below
square-root cancellation, additive energy, or any Fourier-shaped input.  For a multiplicative
subgroup with `n ≤ p^{2/3}`, the classical Stepanov-method bound (Garcia–Voloch 1988;
Heath-Brown–Konyagin 2000) gives `~4·n^{2/3} ≈ 2^22` against the required `2^27.7` — enormous
room.  It is recorded as a named hypothesis, not proved in Lean; a Stepanov formalization is an
elementary polynomial-method project of finite size, and is now the cheapest way to make the
whole depth-four sector unconditional.

## Honest residuals

- The histogram-to-tuple bridge `orderedCoreCount ≤ equalSumQuadPairs` is consumed as a
  hypothesis; the concurrent G84 decoder-surjectivity lane owns that correspondence.
- **Depth five stays genuinely open**: even at Stepanov strength `M ~ n^{2/3}`, the analogous
  chain (`r_5 ≤ M·n^3 + …`) is `~2^26` over budget.  Depth five is where per-fiber
  concentration stops sufficing and collective cancellation across fibers becomes necessary —
  a sharp, quantitative statement of where the lane rejoins the wall.
- Nothing here touches the ON-BGK core.  CORE remains OPEN.

## Verification

Probe: cutoff table exact; kernel inequality exact; convolution identity, fiber bound, and
`J_4` bound exhaustive at `mu_4 ⊂ F_13` and `mu_6 ⊂ F_31`.  Lean: `pg-iterate` pass with
axiom audit (see DISPROOF_LOG entry for the final axiom report).
