# #466 P5: windowed SumsetExtremal is REFUTED at n=16 — replicated at generic primes (2026-07-01)

Closes the caveat left open in `deltastar-466-round1-outcomes-2026-07-01.md` (P5) and completes
the round-1 verdict on dossier v3 §6 **Tier-1 item 1** (the "windowed SumsetExtremal crux",
previously ranked the sharpest open surface).

## The runs

`scripts/probes/probe_466_windowed_extremal.py --stage n16 --q16 {65617, 65633}` (the Fermat
run used q = 65537), n = 16, k = 4, ρ = 1/4, q ≥ n⁴, window δ ∈ (1−√ρ, 1−ρ) = (0.5, 0.75),
agreement levels a ∈ {5, 6, 7} (δ = 11/16, 10/16, 9/16 — all interior). The Fermat-run winning
spread pairs (7,13), (4,8), (4,14) were forced into the replication's direction set. Outputs:
`_out_466_windowed_extremal_q65617.txt`, `_out_466_windowed_extremal_q65633.txt`.

## The result — replicated across three primes, two v₂ classes

| level | δ | q=65537 (Fermat, v₂=16) | q=65617 (v₂=4) | q=65633 (v₂=5) |
|---|---|---|---|---|
| a=5 | 0.6875 | spread 4277 vs mono 4267 | spread 4293 vs mono 4272 | spread 4274 vs mono 4264 |
| a=6 | 0.625  | TIE 89 | TIE 89 | TIE 89 |
| a=7 | 0.5625 | **spread 14 vs mono 9** | **spread 13 vs mono 9** | **spread 13 vs mono 9** |

At the deepest genuinely-discriminating interior level (a = 7; recall a = k+1 = 5 is
direction-blind per the round-1 (D) analysis, so its ~0.3% margins carry little weight), a
2-Fourier-component direction (`sp2_4_14_c1` = x⁴ + c·x¹⁴ shape; at Fermat also `sp2_7_13_c1`)
**strictly beats every monomial direction's worst-offset bad-scalar count by ~45%**, at all
three primes. Winning-direction component gaps (10, 6) avoid the antipodal-correlated class
(gap ≠ n/2 = 8); witnesses brute-force verified over all γ; the monomial value is exactly 9 at
all three primes (stable — plausibly the true monomial optimum at this level).

## Verdict

**The windowed SumsetExtremal conjecture — "in the prize window, no spread direction beats
every pure monomial" — is FALSE at n = 16 as stated.** The window guard
(`SumsetExtremalityGuard.lean`) repaired the below-window degeneracy (`not_sumsetExtremal`) but
does not rescue the statement in-window at accessible scales.

Honest caveats (why this is a probe verdict, not a theorem): (i) the worst-u₀ search is
heuristic for both classes and the spread class received more refinement rounds — but the
spread values are TRUE lower bounds (brute-verified) and the monomial plateau at exactly 9 is
prime-independent; (ii) n = 16 is small; an asymptotic (n → ∞) version of the conjecture is
untested — but there is now zero positive evidence for it at any honest scale, and the margin
is a constant factor (~1.45×), not a vanishing artifact.

## Consequences (dossier §6 re-ranking)

1. **The guard-cell catalogue route dies as designed.** `mcaDeltaStar_pin_of_finsetGuardCover`
   awaited a catalogue certifying monomial dominance per cell; there is no such dominance.
2. **The monomial-extremality ansatz is a false simplification in-window.** Anything that
   quantified only over monomial directions (the "extremal lines are monomial directions"
   heuristic attached to the master-gap identity's m\*-computation) must re-quantify over all
   directions. The PROVEN bracket theorems are unaffected (they never assumed it); the
   ATTACK-plan simplification is what dies.
3. **Constant-factor, not order-of-growth.** The spread advantage is ~1.45×; nothing here
   moves δ\* across the window — the incidence ceiling changes by a constant, the
   `m* = Θ(n/log n)` ceiling and the wall are untouched. The finding kills a lemma-shape, not
   the bracket.
4. **New object for round 2:** the winning class is sparse-pair directions `x^j + c·x^{j'}`
   with mid-range gaps. A 2-component direction's line is a PENCIL of 2-dim RS-coset
   geometry — the right replacement conjecture is a **bounded spread-excess law**:
   `worst_spread ≤ C·worst_mono` with an absolute constant `C ≤ 2` (measured: ≤ 1.56 at all
   levels/scales so far, incl. n=8 ties). That form is still a per-cell catalogue INPUT
   (a weaker one suffices for the weld's far-line budget: budgets need only a constant), and
   it is testable/refutable the same way.

DISPROOF_LOG tag: `466-r1-windowed-extremal-spread-beats`.
