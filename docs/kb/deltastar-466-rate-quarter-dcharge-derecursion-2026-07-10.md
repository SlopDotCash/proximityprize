# Rate-quarter predecessor: the D-charge derecursion — exact boundary `F₀ = 75018133`, small-pool closure, and the stall taxonomy

## Status

Executes the derecursion round on the global-consistency charge.  **Verdict:
the flow does NOT close the pin — it stalls at a sharp, exactly computed
boundary.**  Below the boundary the branch is closed (probe-pinned greedy
optimum well under budget); above it the escaping configuration is pinned to a
sub-Johnson-on-`Z` direction swarm with a two-regime pool-code taxonomy.

Formal kernel (pg-iterate ✅ OK 20s, 9 audited theorems, all on
`[propext, Classical.choice, Quot.sound]`, no `sorry`/`axiom`):

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_P1RateQuarterDChargeDerecursion.lean
```

Probe: `scripts/probes/probe_rate_quarter_p1_dcharge_derecursion.py` (exact
boundary arithmetic, greedy ledger optimum for all `F ≤ F₀`, stall-window
widths, and 100-instance μ_256/F_257 verification of the level-0 identity and
level-1 flow inclusion — all OK).

## 1. The flow, made precise

* **Level 0 — collapse to directions.**  Through-base pencils have determined
  first row `w₀ = p₀ − γ₀·w₁` and aligned region EXACTLY `{D=0} ∩ {w₁ = u₁}`
  (`alignedSet_eq_Dzero_inter_dirAgreement`): pencil alignment = direction
  agreement with `u₁` on `Z`.  The pair problem is a single-word problem on
  `Z`.  Also: `riders ≤ F` unconditionally (`riders_card_le_pool` — every
  rider casts a pool vote) and `T − A > F ⟹` no riders
  (`sterile_of_deep_subalignment`).
* **Level 1 — the flow map.**  `bad_maps_to_direction_agreement`: every rider
  `γ ≠ γ₀` maps injectively via `s = (γ−γ₀)⁻¹` to a scalar whose line
  `u₁ − s·D` its direction matches on `≥ T` coordinates.  So the bad family
  maps into a correlated-agreement family of the NEW stack `(u₁, −D)` at the
  **same parameters** `(N, T, k)` — the descent is structural, not parametric
  (the coordinator's `(N−F, T−F)` shrink intuition realizes as: agreement
  splits into `agr_Z` (binding) + pool votes (free), which is where `N−F, T−F`
  appear).
* **Level 2 — the ledger.**  `#bad ≤ 1 + Σ_w F/(T − agr_Z(w,u₁))` over
  directions `w` with `agr_Z ≥ T − F`, Johnson-packable on `Z` (pairwise
  `≤ k−1`).

## 2. The exact dichotomy

The contributing range `[T−F, T]` clears the `Z`-Johnson radius iff
`(T−F)² > (N−F)(k−1)` iff `F ≤ F₀ = 75018133` — both sides kernel-pinned
(`derecursion_boundary`; monotone below the boundary via
`johnson_condition_of_le_boundary`, a subtraction-free `2a·d` vs `(k−1)·d`
growth comparison).

* **`F ≤ F₀`: CLOSED.**  Exact greedy layer optimum of the ledger (probe,
  exact integers, maximized over all `F ≤ F₀`; worst case exactly at `F₀`):
  `882722755 ≤ N = 1073741824`.  The Lean assembly of the `Z`-relative Johnson
  layer-cake is layer-cake-style engineering (arithmetic pinned; honest gap:
  not yet formalized).
* **`F ≥ F₀ + 1`: STALL.**  The window `[T−F, ⌊√((N−F)(k−1))⌋]` is nonempty;
  at the three-heavy pool `F = 100663294` it is `[492131672, 511085881]`,
  width `18954209` (`stall_window_at_heavy_pool`).

## 3. The stall taxonomy (pool-code regimes)

`pool_code_regimes`: the stall range `[F₀+1, N−T+1 = 480946859]` splits at
`F = k = 2^28`:

* `F < k`: RS punctured to the pool is the FULL space — the pool is
  algebraically free; ALL remaining structure is the direction list on `Z`
  (a list-size question at sub-Johnson agreement).
* `k ≤ F ≤ 480946859`: the pool carries a **nontrivial MDS code of dimension
  `k`** — fresh algebra is available on the pool in this regime.  (An
  initially drafted claim that the whole stall range is below `k` was FALSE —
  `N−T+1 > k` — and is corrected here; the MDS sub-regime is real and is the
  natural next attack surface.)

## 4. The minimal residual

`StallResidual`: budget (`G.card ≤ N`) for bad families ALL of whose base
scalars carry stalling pools `F ≥ 75018134`.  If ANY base scalar of the family
has `F ≤ F₀`, the small-pool ledger closes that family.  The stall
configuration is exactly: unboundedly many directions at `Z`-agreement in the
stall window, each with `≤ F/(T−A)` riders realized as pool votes against the
affine stack family `s ↦ u₁ − s·D`.

## 5. Next targets (ranked)

1. **MDS-pool regime** (`F ≥ k`): the punctured code on the pool has dimension
   `k` on `F ≥ 2^28` points — rate `k/F ≤ 1` with genuine distance; the
   direction pins `w = u₁ − sD` on vote coords are now CODE-constrained; a
   second D-charge inside the pool may fire.
2. **Free-pool regime** (`F₀ < F < k`): pure direction-list question on `Z` at
   agreement `[T−F, JohnsonZ]`; needs non-counting input (list-size lower
   bound constructions here would instead push toward refuting the approach).
3. Assemble the `Z`-relative Johnson layer-cake in Lean to convert the
   probe-pinned small-pool closure into a kernel theorem.

## 6. Honesty

No delta-star change; the operational bracket
`3/8 ≤ mcaDeltaStar ≤ 43/96 + 1/(3·2^30)` is untouched.  The small-pool
closure is probe-pinned arithmetic on top of kernel-checked structural lemmas;
its full Lean assembly is an explicitly named engineering gap, not a
mathematical one.
