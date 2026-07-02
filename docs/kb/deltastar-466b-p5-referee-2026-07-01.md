# #466 round 2 P5REF: referee re-verification of the windowed-SumsetExtremal kill — CONFIRMED and STRENGTHENED (2026-07-01)

Independent referee audit (lane P5REF) of the round-1 + replication claim
(`deltastar-466-p5-replication-2026-07-01.md`): *"windowed SumsetExtremal is REFUTED at
n = 16: at n=16, k=4, a=7 (window-interior δ = 9/16), the 2-Fourier-component direction
x⁴ + c·x¹⁴ strictly beats every monomial direction's worst-offset bad-scalar count,
13–14 vs exactly 9, at q ∈ {65537, 65617, 65633}"*.

Probe: `scripts/probes/probe_466b_p5_referee.py` →
`scripts/probes/_out_466b_p5_referee.txt` (runs at q = 65617 and q = 65633).
Independent code (original probe read only to fix conventions); the accelerated engine is
self-tested against full-enumeration ground truth at n=8 (30/30 exact matches), and every
decision number below is brute-verified by enumerating ALL q scalars γ against all
C(16,4) = 1820 interpolants.

## Verdict on the claim AS STATED: **CONFIRMED — and the margin was UNDERSTATED**

| item | their claim | referee finding |
|---|---|---|
| spread worst (x⁴+x¹⁴, a=7, q=65617) | 13 | **≥ 21** (brute-verified witness; independent quick run also found 22) |
| spread worst (q=65633) | 13 | **≥ 21** (brute-verified) |
| monomial max (both primes) | exactly 9 (heuristic) | 9 again, for ALL 8 eligible monomials at q=65617 (twice, independent rng paths) and for the 65633 sweep, under an identical class-blind search with a larger per-direction budget than theirs; best witness brute-verified = 9 |
| direction eligibility | agreemax(x⁴+x¹⁴) = 6 < 7 | confirmed independently (own generator choice) |
| correlated-direction exclusion | gap ≠ n/2 | confirmed: components (4,14), gap 10 ≡ 6 mod 16, ≠ 8 |
| window arithmetic | a=7 ⟺ δ = 9/16 ∈ (0.5, 0.75) | confirmed (interior) |
| caveats honestly scoped? | — | YES: both their output headers and the note flag the worst-u₀ search as heuristic/lower-bound and disclose the spread-favoring refinement asymmetry (`n_ref_m=2` vs `n_ref_s=4` in their source) |

So the windowed SumsetExtremal conjecture is refuted at n=16 with margin ≥ 21 vs 9
(≥ 2.3×), not the reported ~1.45×. A machine-checked kill, now double-checked.

## The refutation is now CONSTRUCTIVE (no search needed)

The mechanism, exposed by the referee run: at all tested primes, u₁ = x⁴ + x¹⁴ on μ₁₆
agrees with RS₄ codewords on **seven distinct 6-sets** S\* (each antipode-symmetric,
S\* = S₀ ∪ (S₀+8), forced by u₁(−x) = u₁(x): both exponents even). The seven position
sets are IDENTICAL at q=65617 and q=65633 (different generators): agreemax = 6 is
prime-independent mod-16 exponent combinatorics, not an accident of one field. Given any such
(S\*, h) and any codeword c₀, set u₀ = c₀ on S\* and
u₀_l = c₀_l − γ_l·(u₁_l − h_l) off S\* with 10 distinct γ_l: then u₀ + γ_l·u₁ agrees
with the codeword c₀ + γ_l·h on S\* ∪ {l}, i.e. 7 points. **Every one of the 10 chosen
scalars is bad — a deterministic floor of n − agreemax = 10 > 9.** The probe confirms
each structural seed scores exactly 10 before any hill-climbing; climbing on top of it
reaches 21–22.

Referee reframing: the win is not about "spreadness" per se — it is that directions with
**elevated code-agreement (agreemax = a−1)** get base a−1 for free and need only ONE
extra matched point per scalar (floor n−(a−1)), while generic directions
(agreemax = k = 4, all eligible monomials) need 3-fold γ-coincidences. "Spread beats
monomial" = "near-code-but-still-eligible beats generic". Any re-guarded conjecture must
decide whether agreemax = a−1 directions are in scope; excluding them is an untested
rescue, and at n=16 the witnessing direction sits at distance 10/16 from the code —
itself inside the prize window, so the exclusion would not be innocent.

## Consequence for the round-1 replacement conjecture (their note, item 4)

The proposed **bounded spread-excess law** `worst_spread ≤ C·worst_mono` with
`C ≤ 2 (measured ≤ 1.56)` is **already in trouble at its stated constant**: the measured
pair is now (≥ 21, 9), ratio ≥ 2.33. C ≤ 2 survives only if every search so far (theirs
+ two independent referee searches, all 8 monomials, several-thousand exact evaluations
each) missed a monomial offset with ≥ 11 bad scalars. Either the constant must be
re-measured upward (referee data suggests C is governed by
(n − agreemax_max)/worst_mono, not a universal small constant), or the law must be
restated per-agreemax-class. Do NOT carry "C ≤ 2" into the weld's far-line budget
without re-derivation.

## Honesty audit

- Their "13/14" values: honest lower bounds (their own framing), just undersearched;
  their brute-verification of witnesses is real and my independent brute agrees with the
  convention (`lineBadScalars`-style count: #{γ : some RS₄ codeword agrees with u₀+γu₁ on
  ≥ a points of μ₁₆}).
- Their "monomial = 9, plausibly the true optimum": now supported by three independent
  search stacks; still not a theorem (u₀-space is q¹⁶ — exhaustion impossible).
- Nothing in the claim as stated needs retraction; only the item-4 calibration
  (C ≤ 2 / 1.56) is superseded by the deeper spread search.

Referee witnesses (a=7, 21 bad scalars each, brute-verified — full vectors + bad-γ lists
in the output file): q=65617 (ω = 53618): `u0 = [25656, 44374, 59038, 3941, 58382,
47640, 51124, 29110, 28119, 21170, 43636, 8561, 8283, 4550, 62531, 29135]`;
q=65633 (ω = 5013): `u0 = [54319, 48416, 51545, 58549, 34857, 15544, 17216, 32984,
28127, 64688, 13955, 11542, 36322, 62969, 8859, 22086]`; both against u₁ = x⁴ + x¹⁴
on μ₁₆. An earlier shakedown run (same probe, `--quick`, different rng path) found a
22-scalar witness at q=65617, so even 21 is not the ceiling.

DISPROOF_LOG tags: confirms `466-r1-windowed-extremal-spread-beats`; adds
`466b-r2-p5-referee-confirmed-constructive-floor`.
