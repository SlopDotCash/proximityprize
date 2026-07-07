# #466 L4(B): the I031 entropy reduction cancels at the TAIL too — union-over-cosets ≡ the quotient moment bound (2026-07-01)

**Verdict: KILL — the I031 lead is fully closed.** DISPROOF tag `466-r4-i031-tail-cosmetic`.
Probe `scripts/probes/probe_466_i031_tail.py` → `_out_466_i031_tail.txt` (deterministic,
no RNG; independently re-run 2026-07-02, byte-identical). Completes the round-1 moment-side
kill `i031_chaining_cosmetic` (`Frontier/_AssaultV2_I031Chaining.lean`).

## Question

`|η_b|` is exactly μ_n-dilation invariant, so `M = max` over `m = (p−1)/n` orbit reps. Round 1
proved the quotient entropy reduction cosmetic at the MOMENT input (the 1/n cancels under the
2r-th root). Untested variant: is it exploitable at the Lamzouri-style TAIL/union input —
is union-over-m-reps with the correct per-rep tail sharper than the moment route at matched
input strength?

## Findings

1. **PART 0 — exact identity (the decision core).** At matched input strength (per-rep
   moments to depth r), the best derivable tail is Markov, and
   `inf{t : m·μ_{2r}/t^{2r} < 1} = (m·μ_{2r})^{1/2r}` — the union route is **arithmetically
   identical** to the quotient moment bound. Verified by independent bisection vs closed form
   (max rel dev 9.3e-16) plus one exact-integer instance (m = 4096, r = 8, σ² = 16: both
   routes gate at the same integer `t^{2r} > 709316941310853120`).
2. **PART 1 — finite Wick arithmetic** (μ = 4..32, β ∈ {3,4,6}): the moment route at optimal
   integer depth converges to the Gaussian-tail union output from above
   (t_mom/t_gauss = 1.16 → 1.02 as μ grows). The quotient/full factor is the SAME constant in
   both routes — `√(ln m/ln p) = √(1−1/β)` (0.8165/0.8660/0.9129 at β = 3/4/6), i.e. the
   `log(p/n)/log(p)` exponent factor is REAL but bounded (a fixed constant at fixed β,
   `≥ √((β−1)/β)`) — cosmetic in the exponent. Depth relocation only: r*_quot/r*_full ≈
   (β−1)/β; the required input remains the SAME open per-rep Wick object at depth ~ ln m.
3. **PART 2 — real data, n = 16, generic primes 65617/65633** (orbit invariance ≤ 7e-15;
   `A₁/Wick₁ = 1` exact): even the STRONGEST tail input — the true per-rep Gaussian tail —
   undershoots the deterministic truth: `M/[σ√(ln m)] = 1.1525 / 1.2072 > 1` (the known I031
   constant creep), and the empirical per-rep tail exceeds the Gaussian tail at every
   threshold (e.g. 9 reps above the union threshold vs 1.01 predicted). So no tail-input
   variant can close the constant either; the per-rep moment wall `A_r/Wick` creeps to ≈ 6.8
   (p=65617) / 8.2 (p=65633) by r ≈ 9–10.

## Verdict

The dilation-quotient entropy reduction is cosmetic at BOTH recognized inputs — the moment
(round 1) and the tail/union (this probe, by exact identity). Do NOT re-attempt: Lamzouri
union-bound variants, per-coset tail bootstraps, or any repackaging that consumes per-rep
moments — they are the quotient moment bound by identity. The open object remains the
per-rep Wick/subgaussian input at depth ~ ln m, which is the wall itself.

Composes with: `i031_chaining_cosmetic`, `466-r4-tsang-levels-vacuous` (the other L4 half),
`deltastar-464-i031-subgaussian-tail-falsifier-2026-06-26.md`.
