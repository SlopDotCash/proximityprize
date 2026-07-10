# Rate-quarter predecessor: the pencil-count charge — exact rider caps, the ten-rider Johnson crossover, and the two-pencil boundary

## Status

Successor of
`deltastar-466-rate-quarter-shared-fresh-triple-p1-refuted-2026-07-10.md`.
With per-coordinate escape charges dead, this rung builds the exact
per-pencil ledger for bad scalars at the P1 predecessor and reduces the
uniform count to a single named inequality on pencils through a base scalar.

Formal kernel (compiles clean, 15 audited theorems all
`[propext, Classical.choice, Quot.sound]`, no `sorry`, no `axiom`):

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_P1RateQuarterPencilCountCharge.lean
```

Probe: `scripts/probes/probe_rate_quarter_p1_pencil_count_charge.py`.

## 1. The vote partition (exact)

Scalar `γ` *rides* pencil `(w₀,w₁)` when its witness codeword is `w₀+γw₁`;
then `(w₀−u₀) = γ(u₁−w₁)` on the witness set.  With
`A = #aligned = #{i : w₀ i = u₀ i ∧ w₁ i = u₁ i}`:

* each non-aligned coordinate votes for ≤ 1 rider (`voteSet_disjoint`);
* the non-joint clause forces ≥ 1 vote per rider — a witness inside the
  aligned region would be jointly explained by the pencil itself
  (`voteSet_nonempty_of_rides`);
* hence `riders·(T−A) ≤ N−A` for `A ≤ T` (`riders_card_mul_le`),
  `riders ≤ N−A` (`riders_card_le_compl`), and the **uniform cap**
  `riders ≤ N−T+1 = 480946859` (`riders_card_le_uniform`);
* **alignment ladder** (`riders_mul_threshold_le`):
  `riders·T ≤ N + (riders−1)·A` — heavily ridden pencils are heavily
  aligned.  This generalizes the two-cover/collinear-boost floor: `m` riders
  force `A ≥ ⌈(mT−N)/(m−1)⌉`.

## 2. The ten-rider Johnson crossover (exact constant)

`alignment_floor_of_ten_riders`: 10 riders force `A ≥ 539356427`, and
`539356427² > N(k−1)` (`ten_rider_floor_beats_johnson`) while the nine-rider
floor `532676609` has `532676609² ≤ N(k−1)`
(`nine_rider_floor_below_johnson`).  Since distinct pencils' aligned regions
pairwise intersect in `< k` coordinates (`alignedSet_inter_card_lt_k`, via
`predecessor_sep`), pencils with ≥ 10 riders form a Johnson-packable joint
family; pencils with ≤ 9 riders live below the Johnson denominator and are
not list-bounded.  Ten is the exact boundary of the heavy/light dichotomy at
the P1 parameters.

## 3. Fiber reduction and the surviving residual

Fix a base scalar `γ₀` and map every other bad scalar to the
divided-difference pencil of the pair.  Fibers partition the family; each
fiber has ≤ `N−T` members (`fiber_card_le`, via the step bound
`(riders−1)·(T−A) ≤ N−T`).  Hence (`badFamily_card_le_one_add_pencilImage`)

```text
#bad ≤ 1 + P·(N−T),   P = #distinct pencils through the base witness.
```

* `P ≤ 2` closes the prize budget: `1 + 2·(N−T) = 961893717 ≤ N`
  (`badFamily_card_le_N_of_image_card_le_two`).
* Over-budget therefore forces `P ≥ 3` through **every** base scalar
  (`three_pencils_of_overBudget`).
* Named residual `BasePencilImageCap` (OPEN): image cap 2, with global
  consumer `badFamily_card_le_N_of_basePencilImageCap`.

Boundary status from the probe: a genuine bad family at the P1 shape
(`μ_256/F_257`, `k = 64`, `T = 142`) attains exactly **two** pencils through
the base — base scalar 1 riding `(x^16, 1)` with partner 2 and
`(x^16−x^8+1, x^8)` with partner 3, coset-blocked stack, all clauses
verified.  So the cap is tight; the open question is excluding a third.

## 4. Any four witnesses share a triple point

`four_witnesses_triple_overlap`: `4T > 2N`, so any four threshold witnesses
have a coordinate covered by at least three of them (sum-free proof:
`(S₁∩S₂)`, `(S₃∩S₄)`, `(S₁∪S₂)∩(S₃∪S₄)` are pairwise disjoint when no triple
point exists, forcing `4T ≤ 2N`).  Consequences: pairwise-only three-pencil
designs are impossible — a third pencil through the base must create triple
overlaps, where the landed triple machinery (pencil rigidity at overlap
`≥ k`, collinear boost at `⌈(3T−N)/2⌉ ≥ k`, absorption dichotomy) applies.
This is the designated attack surface for `BasePencilImageCap`.

The honest weighted form of the residual is
`Σ_π (N−T)/(T−A_π) ≤ N−1` over the base's pencils; the cap-2 form is its
crudest sufficient version.

## 5. Lean pitfalls recorded

* `set x := e with h` does **not** rewrite later `have`-obtained hypotheses;
  omega then sees desynchronized product atoms — rewrite each obtained
  hypothesis with `← h` (or state bounds with explicit expressions).
* `rw [this]` where `this : m = (m−1)+1` also rewrites inside `m−1`;
  use `obtain ⟨r, hr⟩ : ∃ r, m = r+1` and rewrite with `hr` instead.
* A `simp_rw [Finset.card_filter]` + `Finset.sum_comm` proof of the
  four-witness pigeonhole hung the elaborator (>20 min) at `Fin 2^30`; the
  card-identity proof compiles in seconds.

## 6. What this is not

No delta-star change; the bracket
`3/8 ≤ mcaDeltaStar ≤ 43/96 + 1/(3·2^30) < 1/2` is untouched, and the
predecessor uniform count remains open, now concentrated in
`BasePencilImageCap` (or its weighted refinement) plus the previously landed
`PredecessorStructuredFloorResidual` route.
