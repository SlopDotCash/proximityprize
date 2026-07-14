# [466-G296] The rank palindrome collapses the low-rank CORE census to at most `(n-2)/2` values (2026-07-13)

## Summary

G295 proved the exact per-cell rank palindrome for the sponsor 2-power CORE covariance (`n` even):
`A_r = A_{n+1-r}` for all `r ∈ [2, n-1]`. G296 upgrades this pointwise identity into a **census
information bound**. The reflection `σ r = n + 1 - r` is a fixed-point-free involution of the
low-rank window `W = Icc 2 (n-1)`, partitioning its `n-2` slots into exactly `(n-2)/2` two-element
orbits. Any palindromic sequence is constant on each orbit, so

```text
(W.image A).card ≤ (n - 2) / 2.
```

The production `n = 16` cells saturate this bound (7 distinct covariance values over the 14-slot
window on `p ∈ {97,193}`; 3 over the 6-slot window at `n = 8, p = 17`). Hence the `n-2` census
numbers the campaign computes at every sponsor cell carry at most `(n-2)/2` — and empirically exactly
`(n-2)/2` — independent data points.

## Why it is new r-uniform content, not a wrapper or fixed-depth island

- **r-uniform**: the collapse is driven by the single involution `σ` acting on the whole rank window
  `[2, n-1]` simultaneously, and the bound grows with `n`. It is not pinned to one rank pair; it is a
  statement about the total information content of the census as a function of the cell size.
- **Genuine consumer of G295, not a restatement**: G295 supplies only the pointwise identity
  `A_r = A_{n+1-r}` and one witness. G296's load-bearing new lemmas — the fixed-point-free involution
  (`sigma_no_fixed_point`), the orbit-representative decomposition (`window_eq_reps_union_image`),
  and the cardinality collapse (`palindrome_image_card_le`) — do not appear in G295.
- **Quantitative sharpening of the surviving object**: the census on `[2, n-1]` has only `(n-2)/2`
  degrees of freedom. Per G295, the genuine prize rank `r ≈ log p` on a thin cell `n ≈ p^{1/5.27}`
  has `r > n`, so `n+1-r < 2` lies OUTSIDE the window. Thus no low-rank census argument can supply an
  independent value at the prize rank: it is either reflected onto a complementary in-window rank or
  escapes the window entirely. The certificate must live at depth `r ≳ n` against the rank-labelled
  row — the BGK/Paley wall.

## Formal payload

`Frontier/_G296PalindromeCensusCollapse.lean` (15 theorems, all axiom-clean):
- `sigma_maps_window`, `sigma_involutive_on`, `sigma_no_fixed_point` — `σ` is a fixed-point-free
  involution of the window (`n` even).
- `rep_or_sigma_rep`, `window_eq_reps_union_image` — orbit-representative decomposition of the
  window via the lower-half representatives `reps n = {r ∈ W : 2r ≤ n+1}`.
- `palindrome_image_card_le` — the general collapse: `(W.image A).card ≤ (reps n).card` for any
  palindromic `A`.
- `reps_eq_Icc`, `reps_card_eq` — for EVERY even `n ≥ 4`, `reps n = Icc 2 (n/2)` and
  `(reps n).card = (n - 2) / 2` (the general orbit count, not just hard-coded cells).
- `palindrome_census_card_le_half` — THE HEADLINE bound: for even `n ≥ 4`, any palindromic census
  sequence on `[2, n-1]` has `((window n).image A).card ≤ (n - 2) / 2`.
- `reps_card_8 = 3`, `reps_card_16 = 7`, `palindrome_image_card_le_8` — production window sizes
  (corollaries).
- `census17` + `census17_palindromic`, `census17_card_le`, `census17_card_eq` — the exact
  `ZMod 17`, `n = 8` sponsor cell (`A_2=A_7=-600`, `A_3=A_6=-1344`, `A_4=A_5=-1728`) has census image
  of cardinality exactly `3 = (8-2)/2`, so the bound is SATURATED (tight, not slack).

Axioms for all twelve theorems: exactly `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, no
`native_decide`, no custom axioms; the `decide`-closed facts are pure kernel decisions.

## Validation

- `lake env lean`: clean, zero warnings, exit 0.
- Locked build `scripts/lake-locked.sh build ..._G296PalindromeCensusCollapse`: PASS, 3298 jobs,
  exit 0.
- Axiom audit (12 theorems): `[propext, Classical.choice, Quot.sound]` only.
- `forbidden_tokens.py` (scoped): clean, 0 residual axioms. `sorry_census.py --fail-on-holes`: 0
  holes. `check-imports.sh`: up to date.
- Companion probe `scripts/probes/g296_palindrome_census_collapse.py`: PASS — verifies the
  fixed-point-free involution / orbit count for `n ∈ {6,8,10,16,32}`, recomputes the exact covariance
  palindrome float-free on cells `(p,n) ∈ {(17,8),(97,16),(193,16)}`, and confirms the census image
  has exactly `(n-2)/2` distinct values on each.

## Honest scope

Structural census-information bound. Does NOT bound the covariance at production primes, does NOT
exclude a depth-`r ≳ n` certificate. Orthogonal to G289/G291/G293 (rank-blind no-gos) and a
quantitative sharpening of G295. CORE OPEN / ON-BGK (issue #466).
