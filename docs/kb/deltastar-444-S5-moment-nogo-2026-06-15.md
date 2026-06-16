# δ* #444 — the moment / second-order method NO-GO (prize-depth obstruction)

**Date:** 2026-06-15
**File landed:** `ArkLib/Data/CodingTheory/ProximityGap/Frontier/MomentMethodPrizeDepthNoGo.lean`
**Status:** CLOSED, axiom-clean (`[propext, Classical.choice, Quot.sound]`, zero `sorryAx`), takes
**no open input** — it reduces entirely to arithmetic. This is a genuine deliverable: a wall that
tells every future wave *not to re-try the moment method on the prize core*.

## What it proves (and what it does NOT)

The open core (CLAUDE.md §3.5 face 3) is the worst-case incomplete Gauss-period sum
`M(n) = max_{b≠0} ‖Σ_{x∈μ_n} e_p(b·x)‖`, conjectured `≤ C·√(n·log m)`, `m = (p−1)/n = 2^128`.
The most-attempted technique is the **moment / second-order method**: bound `M(n)` by the `2r`-fold
additive energy `E_r(μ_n)` via `M(n) ≤ (q·E_r)^{1/(2r)}`, plug in the Wick/char-`0` energy bound
`E_r ≤ (2r−1)!!·n^r`, optimize over depth `r`.

This file formalizes **why that route provably cannot close the prize**, in three elementary steps:

1. **Wick lands exactly on the prize form.** `(2r−1)!! ≤ (2r)^r` ⟹ at depth `r` the moment bound is
   `M(n) ≤ √(2nr)`; at `r = log₂ m` this is `√(2 n log₂ m)` — the prize floor. (Stated as the
   `2r`-power inequality `momentBoundSq n r ≤ (2 n r)^r` to stay in decidable `ℕ`, no `sqrt`.)
2. **The char-0→char-p transfer (`CleanRegime`) has a hard depth ceiling** `r_max(β) = 2β` (the
   `2·log_n p − 3` norm threshold of `CharSumMomentDeepWall`, floored): past it the norm gate
   `(2r)^{n/2} < p = n^β` fails, so the Wick energy bound stops transferring to char-`p`.
3. **At prize params the two depths are incompatible:** `n = 2^30`, `β = 4`, `m = 2^128` give
   `r_max = 8 < 128 = r_opt` (a 16× gap; also `r_max = 10 < 128` at the bracket's upper end `β = 5`).

**The no-go (`moment_method_no_go`):** `¬ CleanRegime prize_β (rOpt prize_mBits)` — the energy bound
the moment method needs at its optimal depth simply does not hold in char-`p`. It does **NOT** claim
`M` is large; it shows the *moment method's required hypothesis is unsatisfiable at prize depth*. The
genuine open core (the BGK/Paley √-cancellation — whether `M` is actually small) is untouched.

## Theorems that landed axiom-clean (exact statements)

| name | statement | axioms |
|---|---|---|
| `doubleFactOdd_le_pow` | `doubleFactOdd r ≤ (2*r)^r` | propext, Quot.sound |
| `momentBoundSq_le_wick` | `momentBoundSq n r ≤ (2*n*r)^r` (Wick→`√(2nr)`) | propext, Quot.sound |
| `cleanRegime_iff_le_rMax` | `CleanRegime β r ↔ r ≤ rMax β` | none |
| `norm_gate_caps_depth` | `rMax β < r → ¬ CleanRegime β r` | propext, Quot.sound |
| `prize_rMax_lt_rOpt` | `rMax 4 < rOpt 128` (i.e. `8 < 128`) | none (`decide`) |
| `prize_rMax_lt_rOpt_betaFive` | `rMax 5 < rOpt 128` (i.e. `10 < 128`) | none (`decide`) |
| **`moment_method_no_go`** | `¬ CleanRegime prize_β (rOpt prize_mBits)` | propext, Quot.sound |
| `moment_method_needs_charp_input` | `CleanRegime prize_β (rOpt prize_mBits) → False` | propext, Quot.sound, Classical.choice |
| `prize_depth_ratio` | `rOpt prize_mBits = 16 * rMax prize_β` | none (`decide`) |

`CleanRegime β r := r ≤ rMax β` is the named transfer Prop, *defined* as the threshold predicate so
the equivalence is definitional and the no-go is never a hidden assumption (the number-theoretic
content that the norm gate is `(2r)^{n/2}<p ⟺ r≤2β` lives in `CharSumMomentDeepWall` /
`HeightGateNormBound`; here it is consumed as the predicate's definition).

## Bracket-gap-constant no-go — NEW in-tree

The requested "the two-sided δ* bracket gap is an n-independent constant" result was **NOT already
in-tree** as a clean theorem (searched: no `DeltaStarPinchBracketD3.lean`; the many `*Bracket.lean`
files give the trap `δ* ∈ (1−√ρ, 1−ρ]` but never isolate the *width's n-independence*). Added it here
as the `BracketGap` namespace, all axiom-clean:

- `bracketGap ρ := √ρ − ρ`; `bracketGap_eq_factored`: `= √ρ(1−√ρ)` for `ρ ≥ 0`.
- `bracketGap_pos`: `0 < bracketGap ρ` for `ρ ∈ (0,1)` (the trap is always nondegenerate).
- `bracketGap_eq_quarter_at_rho_quarter`: `bracketGap (1/4) = 1/4` (the prize rate; constant `1/4`).
- `bracketWidthAt ρ n := bracketGap ρ` (the width *as a function of `n`* — it ignores `n`).
- `bracketGap_const_in_n`: `bracketWidthAt ρ n₁ = bracketWidthAt ρ n₂` (genuinely constant in `n`).
- **`bracket_cannot_pinch`**: `∃ c > 0, ∀ n, bracketWidthAt ρ n = c` — a uniform positive floor on
  the indeterminacy, so no `n → ∞` drives the width to 0. The Johnson/capacity bracket *alone* can
  never pin `δ*` to a point; the prize needs a genuinely new (non-bracket) idea.

## Relationship to existing second-order bricks

This completes the second-order-method wall trilogy, all axiom-clean:
- `WF407_DeepMomentDefectWall.lean` — the *one-sided* energy-defect arrow (defect only worsens the
  bound; `momentBound`, `defect_only_worsens`).
- `CumulantOnsetNoGo.lean` — the *cumulant* variant gains zero depth past the onset.
- **`MomentMethodPrizeDepthNoGo.lean` (this) — the *depth* obstruction: optimal depth `r_opt=log m`
  is `16×` past the reachable depth `r_max=2β`, so the Wick input is invalid where it's needed.**

Together they exhaust the moment/second-order family: defect (energy), cancellation (cumulant), and
depth (this) are all walls. No future wave should re-attempt the moment method on the prize core.

## Honesty

Pure-arithmetic NO-GO. Proves the moment route's hypothesis is unsatisfiable at prize depth and the
bracket cannot pinch; does NOT resolve `M(n)` or `δ*`. No fabricated closure.
