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

## 3. Fiber reduction and the cap-2 residual (now refuted)

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
* The former named residual `BasePencilImageCap` asserted image cap 2, with
  global consumer `badFamily_card_le_N_of_basePencilImageCap`.

The original boundary probe found a genuine bad family at the P1 shape
(`μ_256/F_257`, `k = 64`, `T = 142`) attains exactly **two** pencils through
the base — base scalar 1 riding `(x^16, 1)` with partner 2 and
`(x^16−x^8+1, x^8)` with partner 3, coset-blocked stack, all clauses
verified.  Subsequently
`_P1RateQuarterThirdPencilExclusion.lean` constructed **three** distinct
pencils at the literal P1 domain and formally proved
`basePencilImageCap_canonicalDomain_refuted`.  Thus the cap-2 route is dead;
only a weighted/layered summation can survive.

## 4. Any four witnesses share a triple point

`four_witnesses_triple_overlap`: `4T > 2N`, so any four threshold witnesses
have a coordinate covered by at least three of them (sum-free proof:
`(S₁∩S₂)`, `(S₃∩S₄)`, `(S₁∪S₂)∩(S₃∪S₄)` are pairwise disjoint when no triple
point exists, forcing `4T ≤ 2N`).  Consequences: pairwise-only three-pencil
designs are impossible — a third pencil through the base must create triple
overlaps, where the landed triple machinery (pencil rigidity at overlap
`≥ k`, collinear boost at `⌈(3T−N)/2⌉ ≥ k`, absorption dichotomy) applies.
This remains an attack surface for the weighted light-pencil summation, but
does not restore the refuted cap-2 statement.

The honest weighted form of the residual is
`Σ_π (N−T)/(T−A_π) ≤ N−1` over the base's pencils; the cap-2 form is its
crudest sufficient version.

## 5. Cross-pencil reuse and the exact prize-scale load spike

Formal kernel:

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_P1RateQuarterCrossPencilVoteReuse.lean
```

The local vote partitions cannot simply be summed: distinct pencils may
reuse coordinates.  The new kernel isolates exactly what such reuse means.

* `witnessVotePetal` is the chosen witness outside its pencil's aligned
  region; non-jointness makes it nonempty.
* Pairwise-private petals support at most `N` assignments, so an over-budget
  family must have genuine cross-pencil witness overlap outside both
  alignments.
* Below alignment `532676609`, every threshold witness has at least
  `T−532676609 = 60118357` petal coordinates.
* After fixing one base in an exact `N+1` family, there are `N` partners, so
  some coordinate has petal load at least `60118357`.
* `witnessVotePetal_commonBase_eq` identifies each partner petal exactly as
  `S_partner ∩ baseMismatchSet`: at a partner agreement coordinate, the
  divided-difference pencil is aligned iff the base codeword agrees there.
  Hence `exists_baseMismatch_hit_by_60118357_of_N_partners` says the base
  misses one coordinate hit by at least **60,118,357** partners.
* At such a base-missed coordinate the direction has the exact local formula
  `d_γ(x) = u₁(x) + (γ−γ₀)⁻¹·(u₀(x)+γ₀u₁(x)−p₀(x))`.  The mismatch factor is
  nonzero, so evaluation at this single coordinate injectively separates all
  partner directions and hence all pencil keys
  (`commonBase_pencilDir_ne_of_baseMismatch`,
  `commonBase_pencilKey_ne_of_baseMismatch`).  This Möbius parameterization is
  a compact algebraic interface for determinant or rational-curve attacks on
  the explosion branch.
* The companion base formula is
  `b_γ(x)=u₀(x)−γ(γ−γ₀)⁻¹e(x)`, with
  `e(x)=u₀(x)+γ₀u₁(x)−p₀(x)`.  Hence two distinct partners have exact centered
  minor
  `(γ'−γ)(γ−γ₀)⁻¹(γ'−γ₀)⁻¹e(x)²`, which is nonzero at a base mismatch
  (`commonBase_centeredMinor_eq`, `commonBase_centeredMinor_ne_zero`).  Thus
  every shared high-load coordinate supplies explicit local Vandermonde
  minors, directly linking this lane to the maximal-minor/tensor route.
  The packaged endpoint
  `commonBase_subNine_exists_centeredMinorClique_60118357` selects one
  base-missed coordinate and a hit set of at least **60,118,357** partners on
  which every distinct pair has such a nonzero minor—a literal maximal-minor
  clique rather than only a cardinality statement.
  This still is not a one-coordinate contradiction: the explicit affine
  projective-line model `j ↦ (−j,1)` supplies a pairwise-nonzero-minor clique
  of size `60,118,357` over the literal prize field
  (`prizeField_supports_projectiveMinorClique_60118357`).  Any successful
  maximal-minor argument must therefore use compatibility across multiple
  coordinates or the degree-`<k` codeword constraint; projective capacity at
  one coordinate is far too large.
* Transposing the petal incidence matrix gives the next multi-coordinate
  target.  The kernel-checked inequalities
  `C(N,2)·2912711 < N·C(55924056,2)` and
  `C(N,2)·3366001 < N·C(60118357,2)` show that the exact Johnson-light branch
  forces a pair of coordinates jointly hit by at least **2,912,712**
  partners, while the sub-nine branch forces **3,366,002**.  The first
  rounding is sharp (`N·C(55924056,2) ≤ C(N,2)·2912712`).  These arithmetic
  certificates are intended to plug into the existing Bonferroni
  coordinate-pair identity without overlapping the active FSMA secant-line
  partition lane.
  This plug is now formalized:
  `exists_two_coordinates_commonPetalLoad_ge_2912712` proves the transpose
  extraction for arbitrary `N` Johnson-light petals, and
  `commonBase_johnsonLight_exists_twoCoordinateMinorClique_2912712`
  specializes it to the pencil geometry.  The latter produces two distinct
  base-missed coordinates and at least **2,912,712** common partners, with
  every distinct partner pair having a nonzero centered Vandermonde minor at
  **both** coordinates.  However the cross-coordinate audit finds an exact
  rank-one degeneracy: direction deviations are proportional to the base
  mismatch vector, and the two-partner/two-coordinate direction-deviation
  minor is identically zero
  (`commonBase_directionDeviation_crossCoordinate`,
  `commonBase_twoPartner_directionDeviation_minor_eq_zero`).  Thus the
  second-moment lift is a useful incidence certificate but still does not by
  itself constrain degree-`<k` codewords; closure needs witness-membership
  variation across more coordinates or a minor not forced rank-one by the
  common Möbius denominator.
  The degeneracy persists at every moment, not only for a selected pair of
  coordinates: on the whole partner witness,
  `d_γ−u₁ = (γ−γ₀)⁻¹·e`, and two partners become identical after multiplying
  their deviations by their respective denominators on the entire witness
  intersection (`commonBase_directionDeviation_on_witness`,
  `commonBase_twoPartner_directionDeviation_proportional_on_inter`).  Thus
  merely extracting triples, quadruples, or larger common coordinate tuples
  will never create direction-deviation rank; new information must come from
  how witness memberships change between tuples.  The base components do
  not escape: the full centered pair factors on every witness coordinate as
  `(b_γ−u₀,d_γ−u₁)=(γ−γ₀)⁻¹e(x)·(−γ,1)`
  (`commonBase_centeredPencilEval_factorization_on_witness`), so its
  cross-coordinate minors also vanish.  This is an exact outer-product/tensor
  factorization, closing the entire fixed-common-witness local-minor route.
* Riders sharing one divided-difference pencil have disjoint vote sets, so
  at any fixed coordinate at most one rider from each pencil can contribute.
  Consequently `commonBase_distinctPencils_ge_60118357` upgrades the load
  spike to a **pencil explosion**: the sub-nine branch of an exact prize-scale
  family has at least **60,118,357 distinct pencils through the chosen base**.
  This is vastly stronger than the earlier three-pencil consequence and is
  the sharp new interface for a global Johnson/degree argument.
* The exact Johnson-boundary version is now also formalized.  Since
  `536870911² > N·(k−1)` and `T−536870910 = 55924056`, every chosen base obeys
  `commonBase_johnsonHeavy_or_distinctPencils_ge_55924056`: either some
  base-partner pencil is genuinely Johnson-heavy (alignment at least
  `536,870,911`), or the base emits at least **55,924,056 distinct
  Johnson-light pencils**.  Unlike the earlier `532,676,610` split, this
  dichotomy has no ambiguous middle band.
  The strongest packaged form,
  `commonBase_johnsonHeavy_or_centeredMinorClique_55924056`, replaces the
  light-pencil cardinality alternative by an explicit certificate: one
  base-missed coordinate and a hit set of at least **55,924,056** partners
  whose every distinct pair has a nonzero centered Vandermonde minor.
* Arithmetic warning: the first Johnson-heavy integer is only one unit above
  the square barrier:
  `536870911² − N·(k−1) = 1`.  Its ordinary Johnson ratio is therefore
  `288230376151711744`, larger than the whole `N`-partner family and hence
  vacuous.  At the ten-rider floor `539356427`, the same ratio is `108`.
  Thus the exact Johnson-or-explosive dichotomy is a structural reduction,
  not yet a count: closure must exploit rider multiplicity/alignment layers,
  not merely apply Johnson at the first square-crossing integer.
* The layer-cake countermodel's extremal `A=T−1`, full-fiber case is now
  rigid rather than merely numerically admissible.  If a pencil has
  `N−T+1` riders, every rider vote set is a singleton; those singleton votes
  partition the entire complement of the aligned core; and each threshold
  witness is exactly `aligned core ∪ its private singleton`
  (`saturatedFullFiber_voteSet_card_eq_one`,
  `saturatedFullFiber_votes_partition_complement`,
  `saturatedFullFiber_witness_eq_aligned_union_vote`).  Therefore the
  minimal three-heavy obstruction must be three near-complete cores, each
  carrying a bijective scalar-to-complement-coordinate labeling.  This is a
  substantially sharper RS-algebraic target than the raw layer-cake ledger.

This is not yet a contradiction.  It is the precise surviving residual for
the sub-nine alignment layer: algebra must exclude or classify tens of
millions of distinct common-base pencils (equivalently, the enormous
common-base hit concentration producing them).  Pure private-petal counting
and sparse pair-overlap arguments cannot solve that layer.  For `N+1` partners (one
more than the exact rebased prize family), the load improves to `60118358`;
the formal kernel keeps this stronger but non-prize-scale variant separate.

## 6. Lean pitfalls recorded

* `set x := e with h` does **not** rewrite later `have`-obtained hypotheses;
  omega then sees desynchronized product atoms — rewrite each obtained
  hypothesis with `← h` (or state bounds with explicit expressions).
* `rw [this]` where `this : m = (m−1)+1` also rewrites inside `m−1`;
  use `obtain ⟨r, hr⟩ : ∃ r, m = r+1` and rewrite with `hr` instead.
* A `simp_rw [Finset.card_filter]` + `Finset.sum_comm` proof of the
  four-witness pigeonhole hung the elaborator (>20 min) at `Fin 2^30`; the
  card-identity proof compiles in seconds.

## 7. What this is not

No delta-star change; the bracket
`3/8 ≤ mcaDeltaStar ≤ 43/96 + 1/(3·2^30) < 1/2` is untouched, and the
predecessor uniform count remains open, now concentrated in
the weighted light-pencil refinement plus the previously landed
`PredecessorStructuredFloorResidual` route; `BasePencilImageCap` itself is
formally refuted.
