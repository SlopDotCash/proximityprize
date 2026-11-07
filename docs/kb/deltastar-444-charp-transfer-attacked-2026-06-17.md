# Attacking the char-`p` transfer from every angle — the full reduction chain (#444)

> **Later status (linked 2026-10-28, audit T48).** The positive-gap observations below
> ("`G_p > 0` throughout", "`|L| ≤ G_0` (growing margin)", "margin GROWING") have been retracted.
> They rested on an incorrect char-0 energy, a naive integer lift that is wrong at `r ≥ 4`.
> `Research/ProximityPrize/Frontier/_CharPStepRatioMonotoneFails.lean` exhibits negative char-`p`
> gaps for exact energy triples at `n = 32, p = 786433, r = 3` and `n = 64, p = 2752513, r = 2`.
> The Lean file kernel-checks the gap arithmetic, and the audit re-computed the supplied energies.
> So the dominance hypothesis `G_0 + L ≥ 0` fails at concrete cells, and the char-`p` step-ratio
> monotonicity is not an open input. The decomposition `G_p = G_0 + L + Q` and the conditional
> transfer lemmas remain valid as implications.

The last open wall: the **char-`p` transfer** of the step-ratio monotonicity (`G_p(r) ≥ 0`, equivalently
`E_r(F_p) ≤ (2r−1)‼·n^r` at deep `r ≈ log p`). Every angle attacked directly + machine-tested (no
sub-agents — weekly-capped).

## The reduction chain (where each link is PROVEN vs OPEN)
```
prize  ⟺  char-p Wick  E_r(F_p) ≤ (2r−1)‼·n^r  (r ≤ log p)              [the wall]
   ⟸  char-p step-ratio antitone  G_p(r) ≥ 0   + base case             [_StepRatioMonotone, LANDED]
   ⟸  G_0(r) + L(r) ≥ 0   AND   Q(r) ≥ 0                                [_CharPTransferDecomposition, LANDED]
        where G_p = G_0 + L + Q  (exact ring identity, gap_decompose)
        · G_0 = char-0 gap            ✅ PROVEN ≥ 0  (_CharZeroStepRatioMonotone, r=2..5)
        · L   = linear wraparound     — machine: L<0 but |L|≤G_0 (growing margin)   [OPEN input A]
        · Q   = wraparound log-conv.  — machine: Q>0 (wraparound self-sub-Gaussian) [OPEN input B]
```
**So the wall is now: (A) the proven char-0 gap dominates the linear wraparound perturbation, and (B) the
wraparound sequence `W_r` is itself log-convex-monotone.** Both are sharper and more structured than
"bound a character sum at every depth", and both are machine-confirmed at prize primes (`G_p > 0`
throughout, `W_r/slack_r ≤ 0.02`, margin growing at deep `r`).

## Angles attacked on the transfer
- **[★ DECOMPOSITION, LANDED] `G_p = G_0 + L + Q`** (`gap_decompose`, ring identity; `charP_transfer_of_dominance`):
  isolates the char-0 backbone (proven) from the two wraparound terms. The key structural advance.
- **[MACHINE] the three signs:** `G_0 > 0` (dominant, proven), `L < 0` (wraparound hurts linearly),
  `Q > 0` (wraparound is self-sub-Gaussian) — and `G_0` dominates `|L+Q|` at every depth, margin GROWING.
- **[the wraparound recursion] `W_{r+1} = n·W_r + Δcross_r`** (from `E_{r+1}=nE_r+cross_r`): clean, but
  the wraparound grows FASTER than the Wick rate (`W_5/W_4 = 652 > 144 = (2r+1)n`), so it does NOT give
  `E_r ≤ Wick` by itself — the char-0 slack absorbs it (`W_r ≤ slack_r`, the real condition).
- **[the slack framing] `E_r(F_p) ≤ Wick ⟺ W_r ≤ slack_r = Wick_r − E_r^0`:** `slack_r ~ (r²/2n)·Wick_r`
  GROWS while `W_r/Wick_r` SHRINKS (data) ⟹ the bound gets EASIER at deep `r` (margin growing). The
  cleanest single form of the open input; the asymptotic (`n=2^30, r=log p`) is the wall.
- **[REDUCES — input B] `Q ≥ 0` (wraparound monotonicity):** the same shape as the original gap but for
  `W_r` — a self-similar char-`p` sub-problem (no closed form for `W_r`, so the `(n−4)`-basis proof that
  worked for char-0 does not apply). Reduces to a wraparound-structure statement.
- **[the divisibility core] `W_r = #{(x,y): p | Σx−Σy ≠ 0}`:** the wraparound is mod-`p` vanishing sums of
  `2^μ`-th roots; bounding it is the char-`p` Evertse–Schlickewei–Schmidt / `S`-unit problem (N5/N25),
  rank-`n/2` obstruction. The irreducible analytic input.

## Honest status
The char-`p` transfer is **reduced, axiom-clean, to two localized wraparound-control inequalities** (A & B),
with the **char-0 backbone PROVEN** (`G_0 ≥ 0`, r=2..5). This is the sharpest the wall has been: it is no
longer "bound the sup-norm/energy" but "the wraparound perturbation is dominated by the proven char-0
monotonicity gap." Both open inputs are machine-favorable (`G_p > 0`, growing margin). The remaining
irreducible core is the wraparound count `W_r` = mod-`p` vanishing sums = the rank-independent char-`p`
`S`-unit bound — the one genuine open analytic-NT input. NO fabricated closure; the prize stays open, but
the formalized reduction chain now bottoms out at this single, precisely-structured wraparound bound.

> Machine: `probe_charp_transfer.py`. Lean LANDED: `_CharPTransferDecomposition` (decomposition + sufficient
> condition), `_CharZeroStepRatioMonotone` (G_0≥0, r=2..5), `_StepRatioMonotone` (antitone+base ⟹ Wick).
