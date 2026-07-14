# δ*/#466 G295 — the low-rank CORE covariance is a rank-palindrome `A_r = A_{n+1-r}`, and prize depth escapes it

Date: 2026-07-13. Lane: direct Opus 4.8 CORE (cron). Branch `research/proximity-prize` only (#499);
`main` untouched. Commit: see DISPROOF entry `[466-G295-rank-reflection-symmetry]`.

## Object

Sponsor gate, adjacent-rank row, CORE covariance (frontier surrogate, G228..G293):

```
W_G(x) = #{(y,z) ∈ G² : 2y - z = x},   G = order-n multiplicative subgroup of F_p^*
R_r(x) = (dp_r ⋆ dp_{r-1})(x)
A_r    = p · Σ_x W_G(x) R_r(x) − (Σ W_G)(Σ R_r)      (exact integer)
```

## Result

For `n` even (the sponsor 2-power regime — the only prize-relevant case), the covariance sequence is
an **exact palindrome in the rank**:

```
A_r = A_{n+1-r}     for all r ∈ [2, n-1].
```

At the two live prize ranks: `A_5 = A_{n-4}` and `A_6 = A_{n-5}`. The low prize rank is pinned to a
HIGH near-complementary rank. Verified exactly on production cells:

```
n=16 p=1297:  A_5 = A_12 = 324135568,   A_6 = A_11 = 949261584
n=32 p=193:   A_5 = A_28 = -29432000,   A_6 = A_27 = -100975808
n=16 p=97:    A_5 = A_12 = -6285008,    A_6 = A_11 = -14107248
```

## Mechanism (a genuine rank-coupling, not a rank-blind feature)

`n` even ⟹ `-1 ∈ G` (the order-2 element lives in the 2-power tower) and `σ = ΣG = 0` in `F_p`
(a nontrivial multiplicative subgroup sums to zero). Subset complementation `A ↦ G∖A` gives

```
dp_r(x) = dp_{n-r}(-x)       ⟹     R_{n+1-r}(x) = R_r(-x).
```

Because `-1 ∈ G`, the gate is even: `W_G(-x) = W_G(x)`. The centered covariance is a bilinear pairing
of `W_G` against the row; reflecting the row by `x ↦ -x` while `W_G` is even leaves the pairing (and
the row's total mass) invariant. Hence `A_{n+1-r} = A_r`. This is an exact identity *between two
different ranks* `r` and `n+1-r` through the complementation involution — not another rank-blind
functional (contrast G289/G291 dimension-forced no-gos and G293's rank-blind label list).

## Why it moves the frontier (information content)

1. **Census degrees of freedom collapse.** Every exact finite-cell census the campaign runs (G266
   four-quadrant, G267 thinness separation, G289/G291 counting-mirage floor, G293 rank-blind label
   list) lives at fixed low ranks `r ∈ {5,6}` on cells `n ∈ {8,16,32}`. This theorem shows those
   rank-5,6 covariances are NOT independent data: they are *identical* to the rank `n-4, n-5`
   covariances. Any "sign freedom" or "thinness bias" observed at the prize rank is literally the
   same number as at the near-full complementary rank.

2. **Prize depth escapes the palindrome.** At the true prize depth `r ≈ log p`, on a thin sponsor
   cell `n ≈ p^{1/5.27}` one has `r > n`, so `n+1-r < 2` — the reflection is VACUOUS. The palindrome
   governs exactly the low-rank window `[2, n-1]` where all exact computation lives, and says nothing
   at prize depth. No low-rank (`r < n`) exact-census argument can even *reach* the prize rank as an
   independent object: it is reflected onto a high rank, while the genuine prize rank leaves the
   window entirely.

Consequence for the surviving object: the missing certificate must live at depth `r ≳ n` (beyond the
palindrome), against the rank-labelled row directly — the BGK/Paley wall — and cannot be extracted
from any finite low-rank census, whose two prize ranks are pinned to their complementary partners.

## Scope (honest)

Structural rank-coupling identity, NOT a Jacobi covariance estimate and NOT a prize closure. It does
not bound the covariance at production primes; it constrains the *shape* of the covariance-vs-rank
sequence and locates the prize regime outside the computable low-rank window. CORE OPEN / ON-BGK.

## Formal payload

`Frontier/_G295RankReflectionSymmetry.lean`:
- `neg_involutive_sum` — reindex a `ZMod p` sum by `x ↦ -x`.
- `centeredCov` — the centered covariance pairing.
- `centeredCov_reflect_of_even` — **the mechanism**: `W` even and `R' x = R (-x)` ⟹
  `centeredCov p W R' = centeredCov p W R`.
- `W17_even`, `reflectR_3_6` — exact `ZMod 17` sponsor witness (`n=8, p=17`, `G=⟨9⟩`, `σ=0`).
- `A17_3_eq_A17_6` — the prize-adjacent identity `A_3 = A_6` from the mechanism, exact integers.

This file does NOT claim the production δ* statement (CORE OPEN / ON-BGK, issue #466). Axioms: all
theorems `[propext, Classical.choice, Quot.sound]`; no `sorryAx`, no custom axioms, no `native_decide`.

Probe `scripts/probes/g295_rank_reflection_symmetry.py`: (1) even-n mechanism + palindrome on 8 cells,
(2) exact prize-rank pins `A_5=A_{n-4}`, `A_6=A_{n-5}`, (3) the exact `ZMod 17` Lean witness. Pure
integer arithmetic; hard `SystemExit(1)` on any violation; PASS.

Orthogonal to G289/G291 (dimension-forced canonical-feature no-gos) and G293 (rank-blind label list):
those close rank-blind certificates; G295 is a rank-COUPLING identity that reorganizes the low-rank
census and locates the prize regime beyond it.
