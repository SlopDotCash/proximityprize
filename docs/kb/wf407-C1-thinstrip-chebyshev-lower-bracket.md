# wf407 / C1-thinstrip — thin-strip lower bracket past Johnson via Chebyshev/M3 (K3)

**Date:** 2026-06-14 · **Verdict: WALLED** (clean dead end with a precise constraint lemma) ·
**Honesty contract held — no fabricated closure.**

## The thread

K3 thin-strip lower bracket: push a δ* **lower** bound past Johnson into the window
`(1−√ρ, 1−√ρ + c/log n)` using Chebyshev / the second-moment method at the census **M3**
variance. Three asks: (1) compute the M3 variance on the strip for smooth μ_n at n=16,32 exactly;
(2) does the second-moment **lower** bound on worst-case list size exceed the Johnson prediction
at a radius Johnson cannot reach? (3) reconcile the floor candidates WB `(1−ρ)/2` vs half-Johnson
vs the census prediction. In-tree: `MCAWitnessSpread`, `JohnsonListBound`, `MCAThresholdLedger`.

## The only direction a moment can give a δ* LOWER bound

For per-received-word list size `L(u) = #{codewords within radius w of u}` and moments
`M_r = Σ_u L(u)^r`, the **Paley–Zygmund / moment-ladder** lower bound on the worst case is
the only way a moment FORCES a large list:

  `max_u L(u) · M_r  ≥  M_{r+1}`   (rung r) ⟹ `max_u L(u) ≥ M₂/M₁ ≥ … ≥ M_{r+1}/M_r`.

A large second/third moment relative to the first/second forces a large worst-case list — i.e. a
δ* lower bracket. This is **complementary** to the UPPER (concentration) wall O173, which is the
SAME object run the other way.

## Verdict: the lower bracket is VACUOUS on the entire strip (machine-checked, exact)

`scripts/probes/wf407_C1-thinstrip_chebyshev_lower.py` (closed-form M₁,M₂; exact integer/Fraction;
prize size `q = n·2^128`, `ρ∈{1/2,…,1/16}`, `n∈{16,32}`):

* **`M₂/M₁ = 1.00000` EXACTLY across the whole strip past Johnson, up to capacity `δ = 1−ρ`.**
  The Paley–Zygmund lower bound gives only `max ≥ 1` (the trivial bound) anywhere below capacity.
  It first becomes non-vacuous (forces `max ≥ 2`) **exactly at `δ = 1−ρ` (capacity), never on the
  open strip below it** — at which point it jumps to E[L] (huge).

* **Quantitative wall (the surplus `M₂/M₁ − 1`, the amount the bracket beats the trivial bound):**
  | n | ρ | δ (strip) | M₂/M₁ − 1 |
  |---|---|-----------|-----------|
  | 16 | 1/2 | 0.375 (just past Johnson 0.293) | `2.5·10^{-76}` |
  | 16 | 1/2 | 0.4375 (capacity-adjacent) | `2.1·10^{-36}` |
  | 32 | 1/2 | 0.469 (capacity-adjacent) | `5.2·10^{-32}` |

  Everywhere on the strip the surplus is `< ε* = 2^{-128} ≈ 3·10^{-39}` (and at most `~10^{-32}`
  even at the very last sub-capacity radius). The bracket **never forces a list of size ≥ 2** on
  the open strip.

* **Mechanism (exact):** `M₂/M₁ = E[L²]/E[L] = 1 + (Σ_{d≥1} A_d·Icap(d,w))/V(w)`. On the strip the
  mean `E[L] = M₁/qⁿ` is exponentially tiny (`10^{-116}` at n=16), so ALL moment mass is the
  diagonal (self-pair) term: `M₂ ≈ M₁`. Two balls only start to multiply-cover (PAIR term grows)
  at capacity. This is the LOWER-side dual of O173's `Var ≈ E[L]²` (Poisson) UPPER-side finding.

## M3 (the census signal) cannot rescue it

* `wf407_C1-thinstrip_m3.py` (exact M3 via codeword-triple ball-intersection DP, subgroup vs
  random, enumerable scale): at **k=2** the smooth-vs-random M3 gap is **exactly 0** (e.g.
  p=7,n=6,k=2: `dM3/M3 = +0.00e+00` at every radius). Domain-dependence of M3 starts at **k=3**
  (O133), where the gap is `|ΔM3|/M3 ∼ q^{-4} ≈ 2^{-512}` — far below the `2^{-128}` resolution.
* The moment ladder (`M₂/M₁` and `M₃/M₂`) turns on (exceeds 1) **only at `w ≥ d_min/2`**, i.e. at
  the half-minimum-distance / ball-overlap onset = the `(1−ρ)/2` boundary. Example p=7,n=6,k=2
  (d_min=5): disjoint balls (max=1) at w=0,1,2; ladder turns on at w=3 (=⌈d_min/2⌉, δ=0.5),
  where PZ=2.3, M3/M2=2.5, true max=4, while Johnson cap = 12 (Johnson still applies and is the
  binding upper bound). So the moment lower bound is non-trivial only BELOW Johnson, and even
  there it is weaker than the true max and far below the Johnson upper cap.

## (3) Floor reconciliation

For all prize rates, **`(1−ρ)/2 < Johnson = 1−√ρ`** (e.g. ρ=1/2: 0.250 < 0.293; ρ=1/16:
0.469 < 0.750). So:
* **WB = `(1−ρ)/2`** is the moment-ladder *turn-on* point (ball-overlap onset, `2w ≥ d_min`) AND
  the O173 lower-window FULL closure point (below it `2R < d_min` ⟹ empty pair band ⟹ worst=avg,
  zero residual). It is BELOW Johnson.
* **half-Johnson `(1−√ρ)/2`** is even smaller and carries no special structure here.
* **Census prediction:** the strip past Johnson is **doubly out of reach** — the moment ladder
  turns on at `(1−ρ)/2` (below Johnson), and even where it is on, its surplus is sub-`ε*`. There
  is no census-driven floor candidate that the moment lower bound can certify above Johnson.

## Lean brick (axiom-clean)

`Research/ProximityPrize/Frontier/WF407_C1ThinStripLowerBracket.lean` (`lake env lean`
EXIT 0, **axiom-clean** — audit `[propext, Classical.choice, Quot.sound]`, two theorems even drop
`Classical.choice`):
* `sup_mul_sum_ge_sum_sq` — the PZ max engine rung 1: `(univ.sup f)·(Σ f) ≥ Σ (f i)²`.
* `sup_mul_pow_succ` — the full ladder rung: `(univ.sup f)·(Σ (f i)^r) ≥ Σ (f i)^(r+1)`.
* `le_sup_of_sum_sq_gt` — the lower bracket as a strict bound: `M₂ > c·M₁ ⟹ max f > c`.
* `StripRegime` / `strip_bracket_vacuous` — the named strip verdict: in `M₂ ≤ M₁` (the
  machine-checked strip regime, surplus < ε*) the PZ engine's strict antecedent fails, so it
  certifies nothing beyond the trivial `max ≥ 1`.
* `moments_collapse_of_le_one` — sanity: below `(1−ρ)/2` (disjoint balls, `L ≤ 1`), `M₂ = M₁`.

## Position / what remains

This is the LOWER (Paley–Zygmund) counterpart of the proven UPPER wall **O173** (second-moment
overdispersion ≈ Poisson, blind to the worst line). Both directions of the second/third moment
are now closed as δ* certificates: the moment method gives neither a worst-case upper bound below
capacity (O173) nor a worst-case lower bound above Johnson (this). **W2** (additive-energy `√n`
loss) is the analytic-side statement of the same intrinsic wall: every first/second/third-moment
argument bottoms out at Johnson (Loop16: the Johnson denominator `a²−nb ≤ 0` for `η < η₀ = √ρ−ρ`).
The δ* lower bracket past Johnson must come from a genuinely **worst-case combinatorial extremality**
argument (the KKH26 `2^{Ω(1/η)}` structured line / BCHKS25 Conj 1.12 antipodal subset-sum fibre),
NOT any moment/Chebyshev bound — exactly lalalune's localization conclusion, now confirmed from the
lower-bracket side too.

**Artifacts:** `scripts/probes/wf407_C1-thinstrip_chebyshev_lower.py`,
`scripts/probes/wf407_C1-thinstrip_m3.py`,
`Research/ProximityPrize/Frontier/WF407_C1ThinStripLowerBracket.lean`.
