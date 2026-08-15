# δ* / #466 — G237: the fiber large-sieve is the phase-honest source of input (A)

**Date:** 2026-07-12
**Lane:** direct Opus-4.8 CORE cron
**Branch:** `research/proximity-prize` (never `main`; #499)
**Status:** LANDED keystone correctness upgrade of the G228→G234 chain. CORE OPEN / ON-BGK.

## One-line

The sharp operator constant behind G233 input (A) `‖Va‖² ≤ n²‖a‖²` is a **fiber count**
`maxfiber ≤ n` — trivially, because fibers partition `G` — **not** the absolute Gram row-mass G234
used, which is false at sponsor scale (`m/n` large). This replaces G234's silent scope error with a
character-theory-free structural bound.

## Why G234 was wrong at scale

G234 derived input (A) via the Schur/Gershgorin surrogate `λ_max ≤ max-abs-row-sum`, specialised
with the premise "every Gram row-mass `≤ n²`". Two independent probes (G56 G235 Result A, Fable
G236) measured the absolute Gram row-mass at `1.2–1.7 · n²` in sponsor cells: the off-diagonal Gram
entries are not phase-aligned, so `max-abs-row-sum` over-counts the top eigenvalue by up to `~8×`,
and crosses `n²` precisely as `m/n` grows (the sponsor asymptotic `m ≫ n²`). G234's abstract
`schur_operator_bound` is fine; its `R = n²` specialisation formalises a lemma true only for small
`m/n`.

## The honest structural core (this lane)

Fibers `{u ∈ G : cls u = d}` (where `cls u` = quotient class of `2−u`) are pairwise-disjoint subsets
of `G`, so `maxfiber := max_d #fiber_d ≤ #G = n`. Pure fiber Cauchy–Schwarz gives

```text
∑_{d ∈ cls '' G} ‖∑_{u ∈ G, cls u = d} F u‖²  ≤  maxfiber · ∑_{u ∈ G} ‖F u‖²   ≤   n · ∑_{u∈G} ‖F u‖².
```

This is the fiber-Cauchy heart of the G236-validated Parseval chain
`∑_{χ≠1}|Va(χ)|² = (1/m)∑_D|T_D|² − k₀ ≤ (maxfiber/m)∑_u|F_a(u)|²`. Feeding `maxfiber ≤ n` and the
one remaining Mathlib character input — multiplicative Parseval `∑_{u∈G}|F_a(u)|² = n‖a‖²`, kept as
an **explicit hypothesis** rather than smuggled in as a false structural claim — yields input (A)
with the sharp `n²`: `n · (n‖a‖²) = n²‖a‖²`.

## Lean payload — `Frontier/_G237FiberLargeSieveInputA.lean`

- `fiber_cauchy` — single-fiber `‖∑_{u∈t} F u‖² ≤ #t · ∑_{u∈t} ‖F u‖²` (triangle + real
  Cauchy–Schwarz `sq_sum_le_card_mul_sum_sq`).
- `fiber_largesieve_operator_bound` — abstract fiber operator bound `∑_d ‖T_d‖² ≤ R · ∑_u ‖F u‖²`
  from any fiber-card ceiling `R`; per-fiber Cauchy recombined by `Finset.sum_fiberwise_of_maps_to`.
- `fiber_card_le` — `#fiber ≤ #G` (one line, `Finset.card_filter_le`) — the honest replacement for
  the false `row-mass ≤ n²` ceiling.
- `largesieve_inputA_of_fiber_parseval` — input (A) `∑_d ‖T_d‖² ≤ n²·aNorm2` from `maxfiber ≤ n` +
  character Parseval energy `∑_u ‖F u‖² = n·aNorm2`.
- `l2_mass_floor_of_fiber_parseval` — the G233 floor `m − n ≤ 4·n·aNorm2` with (A) discharged by the
  SOUND fiber path (correct in the sponsor cells G234's premise excludes).

All five audit to `[propext, Classical.choice, Quot.sound]` (`fiber_card_le`: `[propext,
Quot.sound]`), no `sorryAx`.

## Validation

- Locked build 3300 jobs green (4.0s); `lake env lean` clean, zero warnings.
- `#print axioms` on all five headline theorems: clean, no `sorryAx`.
- `forbidden_tokens.py` clean (ArkLib.lean + G237); `sorry_census.py --fail-on-holes`: 0 holes,
  0 files-with-holes (full repo, 1862 doc-mentions only).
- Probe `scripts/probes/oc_g237_fiber_largesieve_input_a.py`: `maxfiber ≤ n` in every sponsor cell
  (measured 1–4), abstract fiber-Cauchy holds for random complex `F` (independent of Jacobi
  structure), and is **sharp** — worst ratio equals `maxfiber` exactly when a single fiber saturates.

## Scope / honesty

Correctness keystone, not a prize move. Installs the sharp phase-honest operator bound and closes
G234's silent scope error. NOT a new character-sum estimate, does NOT consume the target, does NOT
weaken BGK/Paley. The single remaining Mathlib character-theory input (multiplicative Parseval) is
quarantined as an explicit hypothesis; formalizing it from quotient-character orthogonality is the
next-smaller residual, not attempted here. G234's general `schur_operator_bound` is untouched; only
its false `R = n²` narrative is superseded.

**CORE OPEN / ON-BGK.** Sole live prize face unchanged: per-rank signed sponsor-prime estimate
`Re ∑_{χ≠1} What(χ) conj(R̂_r(χ)) > 0` via explicit cyclotomic Stickelberger/Gross–Koblitz or
large-monodromy phase input, independently at r=5 and r=6.
