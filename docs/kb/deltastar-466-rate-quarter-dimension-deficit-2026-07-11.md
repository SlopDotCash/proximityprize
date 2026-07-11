# δ* #466 — Dimension deficit round: the pure degree argument is REFUTED as universal (Bezout escape class); forced-coincidence theorem + symmetric-escape exclusion + conditional three-pencil composition landed (2026-07-11)

**Lane:** P1 rate-quarter — executes the "formalize the dimension count" round on top
of `deltastar-466-rate-quarter-pencil-harvest-cap-2026-07-11.md`.
**Probe:** `scripts/probes/probe_rate_quarter_p1_dimension_deficit.py` (exact).
**File:** `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_P1RateQuarterDimensionDeficit.lean`
(pg-iterate OK 14s; 7 theorems; full axiom lists read manually via `lake env lean`:
6 exactly `[propext, Classical.choice, Quot.sound]`, 1 `[propext]`; no sorryAx).
Build note: `_P1RateQuarterPencilHarvestCap` olean built once via
`lake-locked.sh build` so this file can import it.

## The round's honest core finding

The proposed route — "`z₁₂ρ + z₂₃σ = z₁₃τ` with `3k − Σ|ov| < k` forces
`ρ = σ = τ = 0` by a pure degree argument" — is **FALSE as a universal statement**:

* **Toy escape (exact, probe §A)**: `k = 3, q = 17`, sets `X=(0,1), Y=(2,3),
  Z=(7,14)`, `λ = 3`: solution dimension **1** at `Σ = 2k` where the generic count
  says 0.  Mechanism: fiber coincidences of the rational map `z_X/z_Y` (two points
  with equal value), i.e. a rank drop of the evaluation conditions.
* So the dimension formula `max(0, 2k − Σ)` is a GENERIC-rank fact.  Any kernel proof
  of the three-pencil margin must exclude the **Bezout escape class**: nonzero
  deg `< k` triples `a + b = c` with root sets `⊇ (ov₁₂, ov₂₃, ov₁₃)` inside the
  evaluation window.

## Escape-class reconnaissance (probe, exact)

* **μ_256 subgroup escape fails by an exact squeeze**: order-64 multiplicative
  cosets in `F₂₅₇` split `x^64 − s` completely over the domain and DO satisfy the
  Bezout identity (verified exactly) — but the polynomial degree is `64 = k`,
  exceeding the deg `< k` row budget **by exactly one**; order-32 cosets fit the
  degree but undershoot the coverage floor (`3·32 = 96 < 167`).  Exact solution
  dimension at deg `< k` on coset-subsets `(56,56,55)`: **0**.
* Window contrast (`q = 1031`, domain `[0,256)` a small window): dim 0 for
  contiguous/AP/random geometries — the prize situation (`[0, 2^30) ⊂ F_P` is a
  `~2^{-128}` fraction of the field; subgroup cosets intersect it negligibly).
  The nonexistence at the prize window is **BGK/Paley-type and open** — the wall,
  precisely localized.

## Kernel-checked (prize shape)

* `bonferroni_three` — three-set inclusion-exclusion lower bound in `Fin N`.
* `fullyAligned_triple_pairwise_overlap_ge` — **forced coincidence**: any
  pairwise-distinct pencil triple with all alignments `≥ T−1` forces EVERY pairwise
  aligned-overlap `≥ 3(T−1) − N − 2(k−1) = 167772161` — two distinct codeword pairs
  agreeing simultaneously with the stack on `≥ 1.67·10⁸` common coordinates.  This
  is the structure any escape must realize.
* `symmetric_escape_excluded` — the all-overlaps-equal escape is IMPOSSIBLE
  (`3(T−1) = 1778384895 > N + 2(k−1) = 1610612734`): first unconditional exclusion
  inside the escape class.
* `FullyAlignedTripleFree dom u₀ u₁` — the **named residual** (margin form of the
  dimension deficit): every pairwise-distinct pencil triple has some pencil
  5-under-aligned.  Not a tautology (toy escape); probe-pinned generically with
  forced margin `≈ 5.6·10⁷ ≫ 5`.
* `stall_budget_of_three_pencil_cover_of_tripleFree` — **the composition**:
  `FullyAlignedTripleFree` ⟹ every bad family covered by three pairwise-distinct
  pencils obeys the `StallResidual` budget `#bad ≤ N` (any-position margin, via the
  harvest-cap theorem with permuted covers).
* `generic_alignment_threshold` (`t = 55924054` exactly), `mu256_coset_squeeze`,
  `forced_coincidence_ledger` — arithmetic rungs.

## Honesty

* The coordinator's step (1) is **refuted, not landed** — documented with an
  explicit exact counterexample; the margin hypothesis was NOT converted into an
  unconditional theorem.  The conversion is achieved CONDITIONALLY on
  `FullyAlignedTripleFree`, which carries exactly the open Bezout-escape content.
* Also still open: cover-by-few-pencils (residual (iii)); m-pencil compounding
  margins.  `StallResidual` itself remains open.  No δ* movement; bracket
  `3/8 ≤ δ* ≤ 43/96 + 1/(3·2^30)` untouched.

## Next target

Two independent hardenings of `FullyAlignedTripleFree`:
1. Quantify the coincidence: the forced-overlap theorem puts `≥ 167772161` common
   points per pair; a deg `< k` nonzero polynomial has `≤ k−1 = 268435455` roots
   TOTAL — so each difference row is within `≈ 10⁸` of being fully split over the
   window.  "No deg `< k` codeword has `≥ 167772161` roots in `[0, 2^30)`" is FALSE
   (products of linears), but the CONJUNCTION with the Bezout identity may pin the
   root sets to near-subgroup structure (Stepanov/Weil territory — the in-tree
   Stepanov weld from the r=2 rung is the natural tool).
2. Enumerate the escape classes at μ scales exhaustively (the toy shows they are
   fiber-coincidence configurations; classify which survive both rows
   simultaneously and whether any is realizable as actual aligned sets).
