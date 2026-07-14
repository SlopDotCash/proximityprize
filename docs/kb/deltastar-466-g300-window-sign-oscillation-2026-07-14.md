# [466-G300] The in-window CORE covariance sign genuinely oscillates: an interior sign change forbids any monotone / single-band certificate at the in-window prize depth (2026-07-14)

## Summary

G299 (`_G299PrizeDepthInWindow.lean`) corrected G296's "escape prose" and proved, kernel-checked,
that at the campaign's own production parameters (`q = 2^158`, subgroup order `n = 2^30`, ledger deep
sup-control depth `r* ≈ 89`) the prize rank and its palindromic reflection `n+1-r*` BOTH lie *inside*
the low-rank window `[2, n-1]`. That reopens an obvious shortcut hope: if the covariance sequence
`A_r` were sign-definite on the window, or rank-monotone on the reps half, or a single central sign
band, then the in-window placement of `r*` would immediately hand you the sign of the CORE covariance
at the prize depth from cheap boundary data, with no arithmetic of the deep row required.

G300 kills that hope. The centered covariance sequence

```text
A_r = p · ∑ₓ W_G(x) R_r(x) - (∑ W_G)(∑ R_r),   R_r = dp_r ⋆ dp_{r-1},
```

is NOT sign-constant on the window. On the exact sponsor cell `(p, n) = (113, 8)`,
`G = ⟨15⟩ = {1,15,18,44,69,95,98,112} ≤ F₁₁₃^*` (order 8):

```text
A = [A_1, …, A_7] = [392, 128, -7240, -13128, -13128, -7240, 128]
    signs          = [ + ,  + ,   -  ,    -  ,    -  ,   -  ,  + ]
```

`A_2 = 128 > 0` (a shallow rank), `A_4 = -13128 < 0` (a deeper rank), `A_7 = 128 > 0` (the deepest
in-window rank `n-1`). The sign flips positive → negative → positive strictly inside the window
`[2, n-1] = [2, 7]`. So on this single cell the covariance is not sign-definite, not rank-monotone on
the reps half (`A_2 > 0 > A_4` with `2, 4 ∈ reps 8` and `|A_2| < |A_4|`), and not a single-sign band.

## Why this is the right no-go for the G299 in-window observation

Because the covariance sign changes with the *rank* inside the window, the value of the covariance at
the in-window prize depth `r*` cannot be read off from a boundary datum or from any
monotonicity/unimodality/single-band assumption. A signing certificate must consult the arithmetic of
the specific row `R_{r*}` at genuine depth — exactly the BGK/Paley wall. This is the precise
mechanism by which G299's "in-window" placement is not a shortcut to closure: in-window does not mean
sign-readable.

The oscillation is not a small-cell artifact. On `(p, n) = (257, 32)` the sign sequence is the
period-4 profile

```text
+ + + + + - - + + - - + + - - + + - - + + - - + + - - + + + +
```

with eleven strictly-interior sign changes at ranks `r ∈ {5,7,9,11,13,15,17,19,21,23,25}` (probe
check 3). The interior oscillation is governed by the sponsor prime's arithmetic, not by depth alone.

## Relation to the ledger

* G295: the exact palindrome identity `A_r = A_{n+1-r}` (a rank-coupling symmetry). Sound; G300 does
  not touch it. G300 shows that *within* the symmetry-reduced half `[2, ⌊(n+1)/2⌋]` the sign is still
  not fixed by rank.
* G296: the census cardinality collapse `|census| ≤ (n-2)/2`. Sound; orthogonal.
* G298: the depth-1 endpoint value `A_1 = p·T₃ - n³` and its thinness-sign no-go. G300 is the
  in-window *interior* analogue: the sign is not fixed by rank either.
* G299: the in-window placement of the prize rank. G300 is its load-bearing follow-up: in-window is
  not sign-readable.
* Orthogonal to G289/G291/G293 (rank-blind feature no-gos).

## Formal payload

`Frontier/_G300WindowSignOscillation.lean`:
* `centeredCov` (matches G295/G298).
* `sum_zmod_eq_range` : kernel-cheap reindexing `∑_{x:ZMod 113} g x.val = ∑_{i∈range 113} g i` via
  `Fin.sum_univ_eq_sum_range`, so `decide` reduces a plain `range`-sum of integers rather than
  enumerating `ZMod`/`Fin` modular arithmetic (necessary at `p = 113`).
* Exact marginals `sumW113 = 64`, `sumR2_113 = 224`, `sumR4_113 = 3920`, `dotW_R2 = 128`,
  `dotW_R4 = 2104`.
* `A2_113 : centeredCov 113 W113 R2_113 = 128` (`A2_pos`), `A4_113 : … = -13128` (`A4_neg`).
* `R7_eq_R2` + `A7_eq_A2` : the reflection row `R_7` equals `R_2` as a residue table on this cell,
  so `A_7 = A_2` (palindrome consistency, `rfl`).
* Headline `window_sign_oscillates : A_2 > 0 ∧ A_4 < 0 ∧ A_7 > 0` — the interior sign change.

Axioms exactly `[propext, Classical.choice, Quot.sound]`; no sorryAx / native_decide / custom axioms
/ `: True`. Exact probe `scripts/probes/g300_window_sign_oscillation.py` (palindrome on all sponsor
cells; exact `(113,8)` witness + marginals + reflection-row equality; `(257,32)` ≥ 8 interior sign
changes; mixed-sign window existence; hard `SystemExit(1)`; PASS).

## Scope

An exact interior-sign-change no-go on the covariance sequence, closing the "in-window ⇒
sign-readable" shortcut opened by G299. NOT a Jacobi estimate, NOT a prize-depth bound, NOT a
closure. CORE OPEN / ON-BGK.
