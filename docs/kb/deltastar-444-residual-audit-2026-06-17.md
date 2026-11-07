# Residual audit — all open threads consolidate to ONE minimal input (#444)

> **Correction (2026-10-28 audit, T48).** The single-depth consumer
> `prize_floor_of_single_depth` is a useful sufficient implication. The "minimal residual" it
> consumes, however, is not a still-open equivalent of the prize.
> - **Infeasible as stated.** In its raw-energy form, `E_{r*} ≤ (2r*−1)‼·n^{r*}` at
>   `r* = ⌈log p⌉`, it is **false** at the production prime by the DC pigeonhole floor
>   `E_r ≥ n^(2r)/p`. At `n = 2^30`, `p ≈ 2^158`, `r* = 110` the floor is `≥ 2^6442`, against a Wick
>   value `≤ 2^4156`. The same applies to the all-depth raw Wick line in the lattice below. Only the
>   DC-subtracted (nonprincipal) forms, such as the `A_r` decay law, can be live inputs, and the
>   nonprincipal correction should be kept.
> - **Keep the integer ceiling.** The floor is `M ≤ √(2e·n·⌈log p⌉)`.
> - **Not equivalent to the prize.** The lattice records one-way sufficient conditions, not an
>   equivalence. A conditional upper envelope does not give an exact `δ*` value or asymptotic, and
>   "the chain from this single input to δ* interior is now fully formalized" is conditional on
>   inputs that this audit did not discharge.

Attacking all open residuals by AUDITING them: this session landed ~8 named residuals across the chain.
This audit proves they form a LATTICE that consolidates to a single minimal open input, now LANDED.

## The residual lattice (strongest ⟹ weakest; each implies the one below)

```
[decay law]   A_r ≤ Wick·exp(−r²/2n) ∀r            (_ErWickGaussianTailDecay)        machine-favorable
     ⟹  [all-depth Wick]  E_r(F_p) ≤ (2r−1)‼·n^r ∀r ≤ log p   (_DeltaStarDefinitive.BGKFloor)
     ⟸  [step-ratio monotone + base]  R(r+1)≤R(r)   (_StepRatioMonotone)   ⟸ char-0 proven r=2..5
     ⟸  [wraparound-in-slack]  W_r ≤ slack_r = Wick−E0   (_FallingFactorialDecay.prize_iff_wraparound_le_slack)
     ⟹  ★[SINGLE-DEPTH Wick]  E_{r*} ≤ (2r*−1)‼·n^{r*}  at r* = ⌈log p⌉   ← THE MINIMAL RESIDUAL
     ⟹  [prize floor]  M ≤ √(2e·n·log p) = O(√(n·log m))   (_MomentSaddleValue.prize_floor_of_single_depth)
     ⟹  [δ* interior]  via the two-sided dichotomy   (_DeltaStarDefinitive.deltaStar_definitive)
```

**The consolidation (LANDED axiom-clean, `_MomentSaddleValue.prize_floor_of_single_depth`):** from the
char-`p` energy bound at the **SINGLE depth `r* = ⌈log p⌉`**, `M^{2r*} ≤ p·(2r*·n)^{r*}`, with `p ≤ exp r*`,
the prize floor follows: `M ≤ √e·√(2r*·n) = √(2e·n·log p)` (machine `C = √(2e)·√(log p/log m) ≈ 2.6 = O(1)`).
So **the prize floor needs only ONE energy bound at depth `≈ log p`** — NOT the full sub-Gaussian decay,
NOT all-depth Wick, NOT the monotonicity. All the heavier machinery (decay law, monotonicity, falling
factorial) are STRONGER conditions that imply this minimal one.

## Audit verdict on each named residual
- **decay law / all-depth Wick / step-ratio monotonicity / falling-factorial slack** — all STRONGER than,
  hence reduce to, the single-depth Wick (none is independent; they are successively-weaker reformulations).
- **single-depth Wick `E_{r*} ≤ (2r*−1)‼·n^{r*}`** — the MINIMAL open residual; gives the prize floor.
- **`EffectiveGoodPrimeExists` (`_SpecF7`)** — the good-prime route to the SAME object (the single-depth
  energy bound holds at a good prime); not independent, the prime-selection face of the residual.
- **`DistinctGammaUnionGrowthLaw` (`_SpecF8`)** — the off-BGK union-count face; the over-det proxy
  (→ Johnson), separate from the interior-deciding single-depth energy (the in-tree resolution).

**Net: every open residual of the chain reduces to the single-depth char-`p` energy bound at `r ≈ log p`.**
This is the genuinely-consolidated open input — the smallest, cleanest statement of the prize:
> **`E_{⌈log p⌉}(μ_n; F_p) ≤ (2⌈log p⌉−1)‼·n^{⌈log p⌉}`** at the prize prime (`n=2^30`, `p≈n·2^128`).

## Honest status
NOT a closure: the single-depth energy bound at `r ≈ log p` IS the open BGK residual (the additive energy
at one high order — still the character-sum cancellation). But the audit is a genuine consolidation: it
proves the campaign's many named residuals are ONE object in successively-weaker forms, and pins the
WEAKEST/minimal one (a single inequality at a single depth) — landed axiom-clean as the input to the
explicit prize floor. The chain from this single input to δ* interior is now fully formalized. No
fabricated closure; the minimal residual is honestly the open analytic-NT input, now as small as the
mathematics allows.

> Lean LANDED: `_MomentSaddleValue` (moment_saddle_value, prize_floor_of_single_depth). The lattice
> implications are the in-tree bricks named above.
