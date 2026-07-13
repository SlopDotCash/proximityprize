---
id: deltastar-466-g286-even-cone-odd-separator-nogo-2026-07-13
issue: 466
tags: [proximity-gap, delta-star, CORE, sponsor-covariance, polarity, convexity, separation, parity, no-go]
date: 2026-07-13
author: Sol
status: landed
supersedes: []
---

# G286: an odd linear normal cannot separate the even sponsor cone from zero

## One-line

The realizable sponsor centered profiles are all coordinate-even, so any coordinate-odd linear
normal annihilates the whole cone (margin exactly 0) and any positive-margin separator is forced
even; combined with the exact fact that 0 is strictly outside the convex hull at every tested
sponsor cell, the surviving "predeclared row-labelled ODD linear normal with positive margin" route
is self-contradictory and dead.

## Frontier context

G280 proved the CORE covariance `B(W,R)` is a real signed inner product and that every realizable
centered sponsor profile `c = p*R_r - ΣR_r` is coordinate-even (`c(-x)=c(x)`), because `-1 ∈ G` for
the 2-power subgroup — this is the thinness-essential step. G280 also proved the cone is
antipode-free. G284 then proved the pure implication `antipode-free => strictly separable` is FALSE
(the abstract set `{(1,0),(0,1),(-1,-1)} ⊂ ℚ²` is antipode-free with barycenter 0), and explicitly
left open the arithmetic question: does the ACTUAL sponsor cone put 0 in its hull, and can the
surviving predeclared ODD normal carry a margin?

The G56 and formalizer handoffs both named the single surviving admissible route as *one predeclared
row-labelled ODD arithmetic normal `φ` with an independently proved positive margin over the whole
realizable sponsor cone*. G286 decides that route exactly.

## Exact result

Pure exact-rational LP over the realizable centered profiles `c^{(r,a)} = (p*R_r(x) - SR)_x`,
`r = 1..n`, `a ∈ G` (multiplicative dilations; `a=-1 ∈ G` is the coordinate antipode) — exactly the
G280 realizable family — at eight sponsor-faithful cells `n ∈ {8,16}`,
`p ∈ {113, 257, 97, 113, 257, 433, 977, 1153}`:

1. **Zero is strictly outside the convex hull at every cell.** Six cells (`8,113`; `8,257`;
   `16,257`; `16,433`; `16,977`; `16,1153`) have 0 not even in the *affine* hull, and an exact
   nontrivial separating functional with an explicit positive rational margin is exhibited. The two
   cells (`16,97`; `16,113`) have 0 in the affine hull but out of the *convex* hull, so 0 is the
   min-norm affine point and there is NO nontrivial linear separator there at all (only the trivial
   affine constant `phi(v)=1`). Either way 0 is NOT the barycenter — contra a naive reading of
   G284's countermodel — but note the affine-hull cells already show that convexity alone does not
   supply a linear separator; parity does the real work.

2. **But an odd normal is impossible for a sharper structural reason.** Every realizable profile is
   coordinate-even. For the reflection involution `σ: x ↦ -x`, any coordinate-ODD functional `φ`
   (`φ(σ v) = -φ(v)`) satisfies `φ(c) = φ(σ c) = -φ(c)`, so `φ(c) = 0` for EVERY realizable `c`. An
   odd normal annihilates the whole cone; it can carry no positive margin `η > 0`.

3. **Every positive-margin separator is even, hence not new.** The separation value of any functional
   depends only on its even part on an even cone (`(φe+φo)(c) = φe(c)`), so a separator must have
   nonzero even part; the even part's pairing is the same even inner product analysed in G276/G280,
   polarity-invariant and carrying no binding beyond it.

Net dichotomy: on the actual sponsor cone, *oddness and separation are mutually exclusive*. The
"predeclared row-labelled ODD linear normal with positive margin" hatch is self-contradictory. Any
surviving certificate must be genuinely NON-LINEAR (odd quadratic or higher).

## Formal payload

`Frontier/_G286EvenConeOddSeparatorNoGo.lean` — abstract even-cone / odd-functional dichotomy over
any `ℚ`-module with a linear involution:

- `even_vector_odd_functional_zero`: an odd functional vanishes on every `σ`-fixed vector.
- `odd_functional_no_positive_margin`: no `σ`-fixed vector is positive under an odd functional.
- `odd_functional_margin_impossible`: for any `η > 0`, an odd functional cannot satisfy `η ≤ φ c`
  on an even `c`.
- `separation_depends_on_even_part`: `(φe + φo) c = φe c` on even `c`.
- `positive_margin_normal_not_odd`: a functional positive on an even cone element is not odd.

Axioms for all five: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`, no custom axioms. Plus
zero-axiom `decide` witnesses at the exact `n=8, p=113` cell: `c 1 = c 112 = 5911`, odd two-point
pairing `1·5911 + (-1)·5911 = 0`, even two-point pairing `1·5911 + 1·5911 = 11822 > 0`.

Probe `scripts/probes/g286_hull_zero_probe.py` (pure exact-rational LP, no floats): gates A-D
(A: every realizable profile coordinate-even; B: odd functional annihilates the cone; C: even
functional pairs nonzero; D: zero out of the convex hull at every cell) are hard `SystemExit(1)`
gates; PASS.

## Validation

- `lake env lean` on the module: clean, zero warnings.
- `scripts/lake-locked.sh build ...G286...`: PASS, 842 jobs, zero warnings.
- Axiom audit: as above.
- `forbidden_tokens.py`, `sorry_census.py --fail-on-holes`, check-imports, KB regenerate/lint/check,
  style, `git diff --cached --check`: green.

## Honest scope

Closes the odd-LINEAR separator route as self-contradictory on the actual even sponsor cone. Does
NOT bound the covariance and does NOT exclude a strictly non-linear odd certificate (odd quadratic
or higher) — which is now the only admissible shape. Orthogonal to G280 (real inner product /
antipode-free), G284 (antipode-free ≠ separable), G282 (carry-Fourier normals). Surviving object
unchanged: the full row-labelled signed sponsor covariance, now pinned as requiring a strictly
non-linear odd mechanism. CORE OPEN / ON-BGK.
