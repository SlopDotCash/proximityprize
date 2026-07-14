# [466-G299] The production prize depth lies inside the palindrome census window, refuting G296's escape prose (2026-07-13)

## Summary

The G295/G296 files proved sound, unconditional structural identities about the CORE covariance
sequence `A_r` on the sponsor 2-power regime: the rank palindrome `A_r = A_{n+1-r}` (G295) and the
low-rank census collapse `|census| ≤ (n-2)/2` on the window `W = Icc 2 (n-1)` (G296). But the G296
docstring, its KB note, and its DISPROOF entry all carried a **frontier inference that is false**:

> "the genuine prize rank `r ≈ log p` on a thin cell `n ≈ p^{1/5.27}` satisfies `r > n` so
> `n+1-r < 2` (outside the window) … it escapes the window entirely. The certificate must live at
> depth `r ≳ n`."

G299 is the kernel-checked correction. At the campaign's own production parameters — field scale
`q = 2^158`, subgroup order `n = 2^30` (`BadPrimeNormBound.lean`: `q = n·2^128 = 2^158`), and the
ledger deep sup-control / EVT depth `r* ≈ 89` (`CumulantOrderThreshold.lean`: `log_n q ≈ 5.27`) —

```text
2 ≤ 89 < 2^30,          σ(2^30, 89) = 2^30 + 1 - 89 = 2^30 - 88  ≥ 2,
```

so the prize depth and its reflection both lie **deep inside** the window `[2, n-1]`, not outside
it. The asymptotic prose is reversed for the same reason: for a fixed base, `log_n q` grows far
slower than `n`, so `r ≈ log_n q` is eventually much smaller than `n`, never larger.

## Why this is r-uniform frontier content, not a fixed-depth island

The correction is not about one number. It repositions the entire prize-rank scale relative to the
census window. The general integer statement is:

```text
q < n^n  ⟹  Nat.log n q ≤ n        (natLog_le_of_lt_pow)
```

so for ANY prize scale below `n^n`, the log rank `⌊log_n q⌋` is bounded by `n` and cannot escape the
window. At production `q = 2^158 ≪ (2^30)^(2^30) = 2^(30·2^30)` by an astronomical exponent margin
(`log₂` gap `≈ 3.2·10^10`), and the exact value is `Nat.log (2^30) (2^158) = 5`. The contrapositive
escape criterion `n < Nat.log n q ⟹ n^n ≤ q` (`escape_would_need_pow`) shows an escaping rank would
require `q ≥ (2^30)^(2^30)`, unreachable at the prize point.

## Consequence for the frontier

The G295 palindrome and G296 census-collapse theorems are untouched and remain valid symmetry /
compression identities on the low-rank window. What G299 removes is the incorrect claim that they
imply low-rank methods are irrelevant at production depth. The prize rank `r* ≈ 89` sits squarely
inside the palindrome window, so it is subject to the same reflection `A_{r*} = A_{n+1-r*}`; the
palindrome and census bound are structural facts *about* the prize regime, not evidence that it
lives elsewhere. The surviving CORE object is unchanged and correctly located: the row-labelled
covariance at the in-window depth `r* ≈ 89` against the rank-labelled row (the BGK/Paley wall). CORE
remains OPEN / ON-BGK (issue #466).

Independently flagged as false by the Fable referee (2026-07-14 03:15 UTC) and the G56 lane
(2026-07-14 04:20 UTC); G299 is the kernel-checked version of that correction.

## Formal payload

`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_G299PrizeDepthInWindow.lean` (reuses G296's
`window` and `sigma`):

- `prizeDepth_lt_order` : `89 < 2^30` (negation of the escape premise `r > n`).
- `prizeDepth_mem_window` : `89 ∈ window (2^30)`.
- `prizeDepth_reflection_eq` : `σ (2^30) 89 = 2^30 - 88` (in particular `≥ 2`, NOT `< 2`).
- `prizeDepth_reflection_mem_window` : the reflection is also in the window.
- `not_escape_window` : `¬ (2^30 < 89 ∧ σ (2^30) 89 < 2)` — the direct refutation.
- `natLog_prize_eq_five` : `Nat.log (2^30) (2^158) = 5`.
- `natLog_prize_lt_order` : `Nat.log (2^30) (2^158) < 2^30`.
- `natLog_le_of_lt_pow` : general `q < n^n ⟹ Nat.log n q ≤ n`.
- `natLog_prize_le_order` : production instance.
- `escape_would_need_pow` : `n < Nat.log n q ⟹ n^n ≤ q` (escape criterion, unreachable at prize).

Axioms exactly `[propext, Classical.choice, Quot.sound]` (reflection_eq fewer); no
sorryAx / custom axiom / native_decide / vacuous `: True`. Probe
`scripts/probes/g299_prize_depth_in_window.py` (pure integer, exponent-only comparisons — never
materializes `n^n`; hard `SystemExit(1)` on any failure; PASS). DISPROOF entry
`[466-G299-prize-depth-in-window]`.

## References

- `CumulantOrderThreshold.lean` (`log_n q ≈ 5.27` at the prize point).
- `BadPrimeNormBound.lean` (`q = n·2^128 = 2^158`, `n = 2^30`).
- `_G295RankReflectionSymmetry.lean`, `_G296PalindromeCensusCollapse.lean` (the palindrome/census
  identities being reclassified).
- Fable referee note 2026-07-14 03:15; G56 lane report 2026-07-14 04:20. Issue #466.
