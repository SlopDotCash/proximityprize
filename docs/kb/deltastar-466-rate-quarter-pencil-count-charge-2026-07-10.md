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
  The labeling is explicit: every complement coordinate has nonzero
  denominator `w₁−u₁` and its unique rider is
  `γ=(u₀−w₀)/(w₁−u₁)` (`voteRatio`,
  `saturatedFullFiber_existsUnique_rider_at_complement`,
  `saturatedFullFiber_unique_rider_eq_voteRatio`).  Hence the three-heavy
  obstruction is equivalently three rational functions inducing bijections
  from their respective core complements onto their rider fibers—a concrete
  cross-pencil algebraic comparison target.
  The bijection claim is literal in Lean:
  `saturatedFullFiber_voteRatio_image_eq` proves the complement image is
  exactly the rider set, and `saturatedFullFiber_voteRatio_injOn` proves
  injectivity on that complement.
  For pencils through the same base, every vote further obeys the shared-
  numerator identity
  `(γ−γ₀)(w₁−u₁)=u₀+γ₀u₁−p₀`.  Therefore if the same non-base rider votes at
  a coordinate on two pencils, their direction codewords agree there.  RS
  root rigidity gives the first degree-sensitive comparison between the
  three bijections: for distinct directions, the same-rider cross-vote
  intersection has size at most `k−1`
  (`commonBase_sameRider_crossVote_card_le_k_sub_one`).
* More importantly, the shared **base** rider collapses the layer-cake's
  minimal countermodel.  For every common-base pencil the base codeword's
  agreement set is exactly `aligned core ∪ base-vote set`.  In a saturated
  full fiber the latter is one point, so every `T−1` aligned core is the same
  fixed threshold-size base agreement set with one point removed.  Any two
  such cores therefore overlap on at least `T−2 = 592,794,964` coordinates,
  far above the distinct-pencil cap `k−1 = 268,435,455`.  Consequently
  `two_saturatedFullFiber_commonBase_pencils_eq` proves that two saturated
  full fibers through one base are necessarily the **same pencil**.  The
  probe's three-`T−1`/full-fiber over-budget configuration is thus
  counting-admissible but RS-algebraically impossible.  This does not yet
  close all layer profiles, but it removes the minimal extremal obstruction
  identified by `_P1RateQuarterLayerCakeBudget.lean`.
  In fact saturation is unnecessary.  For every common-base pencil,
  disjoint nonempty votes imply the shared-base cap
  `|R_π| ≤ N−|B|+1`, where `B` is the fixed base codeword agreement set.
  Two distinct cores aligned on at least `T−1` coordinates force
  `|B| ≥ 2(T−1)−(k−1) = 917,154,475`, so every such fiber has at most
  `156,587,350` riders.  The packaged consumer
  `three_distinct_commonBase_nearThreshold_fibers_sum_le_N` gives
  `1+Σ_i(|R_i|−1) ≤ N` for three distinct near-threshold pencils; numerically
  their maximum is only **469,762,048** slots.  Thus the entire three-heavy
  `A≥T−1` channel—not only its full-fiber endpoint—is closed.  Remaining
  layer-cake profiles must drop below `T−1` or mix more alignment levels.
* Successor module `_P1RateQuarterSharedBaseLayerClosure.lean` begins the
  full ten-rider-layer closure.  `johnson_inside_finset` proves the exact-
  diagonal Johnson inequality using the shared base agreement set `B` as
  the universe, rather than all `N` coordinates.  The literal arithmetic
  consumer `heavy_sharedBase_arithmetic` proves that for every
  `2 ≤ M ≤ 108`, this inside-`B` inequality plus the shared-base fiber cap
  forces `1+M(N−|B|) ≤ N`.  `heavy_family_slots_le_N` now carries the generic
  structural wiring too: any finite family of at most 108 heavy cores inside
  `B`, with pair intersections at most `k−1` and fiber cap `N−|B|+1`, has
  total scalar slots at most `N`.  The remaining work is only the concrete P1
  adapter that forms this family from the ten-rider pencil fibers; the
  combinatorics, arithmetic, and abstract slot consumer are all proved.
  The optimized envelope is stronger:
  `heavy_family_slots_le_893823171` leaves exactly `179,918,653` slots below
  `N`.  Since a Johnson-light pencil has at most eight non-base riders, this
  absorbs up to **22,489,831 light pencils**; one more crosses the budget.
  `heavyEnvelope_add_lightSlots_le_N` packages the mixed-layer arithmetic.
  The remaining light-side target in the presence of a nontrivial heavy
  family is therefore an explicit pencil-count cap `≤22,489,831`, much
  smaller than the earlier 55.9-million explosion threshold.
  The inside-carrier audit also locates its hard floor exactly.  At the most
  favorable carrier size `|B|=T`, the two- and three-rider alignment floors
  remain below the Johnson square, while the four-rider floor crosses it
  (`minimalCarrier_lowRider_johnson_boundary`).  In particular the
  three-rider Johnson denominator is zero.  Therefore no refinement of this
  positive Johnson packing can bound the 2–3-rider pencil population; that
  population is the genuine remaining algebraic/light-explosion residue.
  The new identity
  `commonBase_alignedSet_eq_baseAgree_inter_directionAgree` sharpens this
  diagnosis: for a common-base pencil its aligned core is exactly the shared
  base agreement set intersected with the agreement set of the pencil's
  direction codeword.  Thus the surviving 2–3-rider population is literally
  a punctured Reed–Solomon list-decoding problem on the fixed carrier `B`,
  below the range where the positive Johnson argument has any slack.
  `_P1RateQuarterBelowJohnsonLocatorListRefuted.lean` shows that this is a
  genuine no-go for any direction-only repair, not just a weakness of Johnson.
  For every coordinate set `A` with `|A|<k`, the scalar multiples of its
  locator polynomial give exactly `|F|` distinct dimension-`k` RS codewords,
  all agreeing with zero throughout `A` (`fieldSized_locatorList`).  Since the
  literal two-rider floor is `111,848,108 < k=268,435,456`, even a full
  field-sized direction list can share the required aligned core.  A successful
  light-layer argument must therefore retain the discarded rider/vote
  equations or couple several alignment levels; punctured direction agreement
  by itself cannot yield the required pencil-count cap.
  Retaining the vote equations does recover a new positive band.  Every
  non-base rider vote lies outside the fixed base agreement carrier `B`.
  Hence, if two common-base pencils share a non-base rider and their two vote
  sets have size at least `s`, inclusion--exclusion inside `Bᶜ` forces the
  directions equal as soon as `|Bᶜ|+k ≤ 2s`
  (`commonBase_sharedRider_directions_eq_of_complement_packing`).  At P1 scale,
  `s=T-A` and `|B|≥T`, so this holds throughout the exact alignment band
  `A≤218,103,809`.  This band contains the two-rider floor `111,848,108` but
  ends before the three-rider floor `352,321,537`.  Thus low-alignment
  two-rider pencils can be charged injectively to their non-base riders; the
  genuinely hard light residue is narrowed to the upper two-rider band plus
  the three-rider layer.
  Complement Johnson extends this charging statement quantitatively.  For a
  fixed non-base rider, its vote sets across distinct pencils all lie in
  `Bᶜ`, have pair intersections at most `k−1`, and therefore form a constant-
  weight packing on at most `N−T` coordinates.  At `A≤230,000,000`, the forced
  vote size is at least `362,794,966`, and the exact arithmetic plus generic
  packing consumer `sharedRider_family_card_le_18` bounds rider multiplicity
  by **18**.  The positive complement-Johnson denominator has exact endpoint
  `A=233,485,644` and vanishes at `233,485,645`; hence this method cannot reach
  the three-rider floor.  This is both a useful extension of the injective
  band and a sharp barrier: the remaining upper two-rider/three-rider channel
  needs multi-rider coupling rather than another one-rider packing estimate.
  The first genuine two-rider invariant is now formalized as
  `commonBase_twoRider_matchingOverlap_card_le_k_sub_one`: for any two fixed
  non-base labels, the **union** of their matching overlaps across two distinct
  pencils has size at most `k−1`.  The two labels share one RS root budget; the
  bound is not the weaker `2(k−1)`.  At the saturated three-rider endpoint the
  two non-base vote sets partition `Bᶜ`, so pencils become balanced binary
  labelings whose pairwise Hamming distance is at least
  `(N−T)−(k−1)=212,511,403` (balance later rounds this to `212,511,404`).
  Exact arithmetic also records the raw obstruction: twice the unrounded
  distance is still `55,924,052` below the binary block length
  `N−T=480,946,858`.  Therefore ordinary binary Plotkin remains subcritical.
  The saturated residue is now sharply reframed as a structured binary-code
  problem with an RS-realizability constraint; closing it requires exploiting
  that constraint, not only the induced binary distance.
  A weighted complement-capacity theorem further clarifies when this binary
  model is forced.  `commonBase_nonbase_riders_mul_voteFloor_le_compl_agreeSet`
  proves
  `|R|(T−A) ≤ |Bᶜ|` whenever every rider is non-base.  The carrier premise is
  now produced rather than assumed:
  `commonBase_agreeSet_card_ge_threshold_of_baseWitness` embeds the global
  threshold witness explained by `p₀` into `B`, proving `|B|≥T`.  Consequently
  three non-base riders force
  `A≥432,479,347`, exactly the four-rider alignment floor
  (`threeNonbase_capacity_forces_fourRiderAlignment`).  The endpoint is sharp:
  at `A=432,479,346` the three vote sets overflow `Bᶜ`, while at
  `432,479,347` they fit arithmetically.  Consequently, throughout the lower
  three-rider band, the global base witness forces the base scalar to be one
  of the riders and hence reduces the complement to the two-label binary
  model.  This full adapter is packaged as
  `commonBase_threeRiders_lowerBand_base_mem`; the former conditional
  `|B|≥T` gap is closed.
  At the minimal three-rider alignment `A=352,321,537`, removing the now-forced
  base rider leaves exactly two non-base riders.  Their combined forced demand
  is
  `2(T−A)=480,946,858=N−T`.  Applying weighted capacity to this erased rider
  family gives `|B|≤T`, while the global base witness gives `|B|≥T`; hence
  `commonBase_threeRider_minimal_agreeSet_card_eq_threshold` proves the exact
  rigidity `|B|=T`.  The saturated binary reduction's block length `N−T` is
  therefore derived from the actual pencil hypotheses, not a numerical model
  assumption.
  Finally, `rides_voteSet_card_ge_threshold_sub_aligned` packages the uniform
  lower bound `|V_γ|≥T−A`, and
  `commonBase_threeRider_minimal_nonbaseVotes_partition_complement` proves the
  exact set identity
  `(R.erase γ₀).biUnion V = Bᶜ`.  Since vote sets for distinct scalars are
  disjoint and there are exactly two erased riders, the minimal three-rider
  endpoint is now a literal two-color partition of `Bᶜ`, not merely an
  analogy or cardinal estimate.  The remaining saturated question is exactly
  the RS-realizability bound for this family of binary labelings.
  The partition is exactly balanced:
  `commonBase_threeRider_minimal_nonbaseVote_card_eq` proves that each of the
  two non-base vote classes has `240,473,429=(N−T)/2` coordinates.  Hence the
  final endpoint object is a constant-weight binary code of length
  `480,946,858`, weight `240,473,429`, and minimum distance at least
  `212,511,404`, subject to the additional RS direction-realizability law.
  Balance also halves the matching budget exactly.  The generic identity
  `balanced_binary_matching_card_eq_two_inter` proves that two half-carriers
  have total matching agreement `2|S∩T|`; therefore the RS matching cap
  `≤k−1` yields the sharp integer intersection bound
  `|S∩T|≤134,217,727=k/2−1`.  This strengthening still does not activate
  constant-weight Johnson: its natural denominator
  `240473429²−480946858·134217727` truncates to zero.  Thus even the fully
  balanced constant-weight abstraction is insufficient; the next theorem
  must use the fact that each labeling is realized by a degree-`<k` direction
  through the common mismatch quotient.
  `_P1RateQuarterBinaryVandermondeDivisibility.lean` turns that realizability
  into a direct polynomial constraint.  For any three binary-realizable
  direction polynomials `p₁,p₂,p₃`, at every carrier coordinate two values
  coincide, so the carrier locator divides
  `(p₁−p₂)(p₁−p₃)(p₂−p₃)`
  (`carrierLocator_dvd_vandermondeThree_of_binary`).  Consequently, whenever
  the carrier has more than `3(k−1)` points, two of the three directions must
  be equal (`two_eq_of_binary_of_three_mul_lt_card`).  Literal P1 does not meet
  this raw cubic root threshold: `480,946,858 < 3·268,435,455`.  A follow-up
  audit formally retires the naive polynomial-abc suggestion.  Mason--Stothers
  would compare a difference degree at most `268,435,455` with a radical whose
  carrier contribution alone has `480,946,858` roots, so its inequality is
  already satisfied (`p1_mason_carrier_radical_inequality_already_satisfied`).
  The cubic budget is also literally the sum of the three pairwise RS budgets
  (`p1_vandermonde_budget_eq_three_pair_budgets`): locator divisibility by
  itself merely repackages pairwise separation.  Any strengthening must retain
  the common mismatch quotient on the cross-label coordinates, not only the
  binary equality pattern or radical of the Vandermonde product.  The in-tree
  search also confirms there is no general RS list-recovery primitive that can
  be instantiated here; existing subspace-design results concern folded/design
  codes and leave their own list-recovery inputs explicit.
  Weighted capacity also resolves base inclusion for the *entire* two-rider
  range.  If both riders were non-base, their demand would satisfy
  `2(T−A)≤N−T`; exact arithmetic shows this first becomes possible at
  `A=352,321,537`, the three-rider floor.  Therefore every two-rider pencil
  with `A≤352,321,536` contains `γ₀`
  (`commonBase_twoRiders_belowThreeFloor_base_mem`) and has exactly one
  non-base rider.  The crossover is certified independently by
  `twoNonbase_capacity_exact_crossover`.  Consequently all genuine two-rider
  pencils admit a canonical charge to their unique non-base scalar; only the
  multiplicity of that charge in the upper alignment band remains to bound.
  The minimal two-rider endpoint is completely rigid as well.  At
  `A=111,848,108`, the unique non-base rider requires
  `T−A=480,946,858=N−T` votes.  The global base witness and weighted capacity
  force `|B|=T`
  (`commonBase_twoRider_minimal_agreeSet_card_eq_threshold`), and the unique
  non-base vote set is exactly all of `Bᶜ`
  (`commonBase_twoRider_minimal_nonbaseVotes_eq_complement`).  Hence at this
  endpoint the common mismatch quotient determines the direction on every
  off-carrier coordinate; the unresolved reuse phenomenon can occur only
  after moving upward from the minimal two-rider alignment.
  For two pencils reusing the same charged rider, the valid second matching
  contribution comes from their aligned cores (not their base-vote sets).
  `commonBase_alignedAndSameRider_matching_card_le_k_sub_one` proves that the
  union of aligned-core overlap and same-rider vote overlap has one shared
  `k−1` RS root budget.  The generic complementary-carrier calculation
  `twoCarrier_matching_floor` gives its forced floor.  Since each pencil has
  `A+(T−A)=T`, that floor is alignment-independent:
  `2T−N=111,848,108`.  Unfortunately this remains `156,587,347` below `k−1`
  (`twoRider_matching_floor_rootBudget_slack`).  Thus aligned-plus-vote
  inclusion--exclusion is a genuine coupling improvement, but it cannot by
  itself bound reuse in the upper band; the cross-label mismatch equations
  remain necessary if one reasons only pairwise.  The family-level view is
  much stronger.  For a fixed charged rider define
  `W_π = alignedCore_π ∪ voteSet_{π,γ}`.  The witness inclusion theorem
  `rides_alignedUnionVote_card_ge_threshold` gives `|W_π|≥T`.  Because aligned
  cores lie in `B` and non-base votes in `Bᶜ`, cross terms in
  `W_π∩W_π'` vanish; the full intersection is therefore capped by `k−1`
  (`commonBase_alignedUnionSameRider_inter_card_le_k_sub_one`).  Johnson on
  these full-`N` combined sets has positive denominator
  `T²−N(k−1)=63,175,496,636,971,236`.  Exact arithmetic rules out six members,
  and `combinedTwoRider_family_card_le_five` proves that **one non-base rider
  can be reused by at most five two-rider pencils**, uniformly across the
  entire alignment band.  This closes the upper-band multiplicity problem
  left by the one-rider complement Johnson analysis even if witnesses are
  allowed to vary.  The actual construction is sharper because `Sf γ` is
  fixed globally.  If two common-base pencils carry the same non-base rider,
  that same threshold set `Sf γ` lies inside both combined sets, making their
  intersection at least `T>k−1`.  The overlap cap then forces equal directions
  (`commonBase_sameFixedWitnessRider_directions_eq`), hence the same pencil.
  Thus charged-rider reuse is **exactly injective (multiplicity one)** in the
  fixed-witness campaign; the cap five remains a robust varying-witness
  fallback.  Together with forced base inclusion, this closes the complete
  two-rider pencil channel structurally.  The object-level adapter
  `commonBase_sameFixedWitnessRider_pencils_eq` packages equality of the full
  `(pencilBase,pencilDir)` pair: through `(γ₀,p₀)`, equal directions force equal
  bases by the defining formula `p₀−γ₀·direction`.  Downstream fiber arguments
  can therefore consume literal pencil equality without reconstructing it
  from the slope theorem.
  The family-level form is now explicit:
  `commonBase_distinctPencils_nonbaseRiders_disjoint` proves that distinct
  common-base pencils have disjoint rider sets after erasing `γ₀`.
  `disjointErasedFibers_sum_le_global(_sub_one)` packages the corresponding
  summation bound: all erased fibers together consume at most `|G|−1` global
  non-base scalars.  This is the exact adapter required by layer-budget sums,
  and applies equally to two-, three-, and heavier fixed-witness fibers.
  That disjointness is a partition input, not by itself the missing absolute
  budget.  A genuinely cross-fiber bridge is now also formalized.  For any two
  distinct scalars, the intersection of their fixed witnesses is contained in
  the agreement set of their divided-difference direction with `u₁`
  (`fixedWitness_inter_subset_pencilDir_agreeSet`).  Since both witnesses have
  size at least `T`, this direction agrees on at least
  `2T−N=111,848,108` coordinates
  (`fixedWitness_pencilDir_agreeSet_card_ge_111848108`).  The count is below
  unique decoding but applies to every cross-fiber pair, making it the proper
  input for a second-moment/Johnson argument across different pencils rather
  than another within-fiber layer identity.
  Composing with the independently landed integral five-set overlap theorem
  gives a sharper extraction:
  `fiveFixedWitnesses_exists_pencilDir_agreeSet_card_ge_k` proves that among
  any five distinct fixed scalars, some witness pair has a secant direction
  agreeing with `u₁` on at least `k=268,435,456` coordinates.  This is exactly
  the interpolation threshold, so that direction is pinned by the received
  values on the extracted overlap.  The remaining global step is to turn the
  abundance of these pinned secants into repeated directions/large pencil
  fibers (or a contradiction), rather than merely extracting one edge per
  five vertices.  `exists_pinnedSecant_of_five_le_card` supplies the direct
  finite-family interface: any `G` with `5≤|G|` yields two named members of
  `G` and their interpolation-pinned secant, with no `Fin 5` indexing exposed
  to downstream Turán or greedy-extraction code.

- The sharp four-part Turán count now has an exact endpoint concentration
  lemma.  For `m = N + 1`, twice the guaranteed edge floor is strictly larger
  than `m * (k - 1)`; the handshake identity therefore forces a vertex of
  degree at least `k`.  Thus an exactly over-budget overlap graph contains one
  scalar incident to at least `k` interpolation-pinned secants.  This is a
  concentration interface, not yet a proof that those secants share a source
  pencil or direction.

- The obvious next inference from that star is now sharply audited.  A formal
  sunflower `degreeKStarCore` supplies `k` distinct cores of size `k`, with
  every pair meeting in exactly `k-1`; all of them fit inside a single
  threshold-sized base agreement universe.  Therefore degree `k`, the
  pairwise RS cap, and the base agreement cardinality alone cannot force a
  repeated source line.

- There is nevertheless extra polynomial rigidity at the extremal common-core
  boundary.  `direction_sub_eq_locator_mul_C_of_commonCore` proves that two
  degree-`<k` directions agreeing on a `(k-1)`-set differ by a scalar multiple
  of its monic locator.  Its affine packaging shows that every direction in a
  genuine common-core sunflower lies on one affine line in `F[X]`.  The next
  viable closure target is consequently a constraint on these locator
  coefficients and endpoint scalars, rather than another set-incidence bound.

- The locator coefficients now have a direct incidence interpretation.  At an
  off-locator coordinate, three agreeing affine-locator neighbors force their
  parameter points `(a,a*c)` to be collinear.  The denominator-cleared endpoint
  theorem then transports this parameter collinearity to a common polynomial
  source secant.  This bridge is unconditional once the neighbors share the
  same `(k-1)` locator.

- The accompanying star charge is numerically overwhelming and fully
  formalized.  Remove at most four exceptional lines of at most `215` neighbors
  each.  Every remaining core below `590558003` contributes at least `2236964`
  off-base coordinates, and
  `215*(N-T) < (k-4*215)*2236964`.  Hence
  `lowCoreStar_load_216_forced` produces an off-base coordinate carried by at
  least `216` remaining neighbors.

  The honest remaining weld is structural, not arithmetic: a generic
  degree-`k` overlap star need not yet share one `(k-1)` locator.  One must
  either extract a sufficiently large common-locator substar or prove a
  cross-coordinate matching theorem that upgrades the forced load-`216`
  coordinate to one polynomial source line.  The current theorem does not
  silently assume that upgrade.

- A degree-one countermodel now rules out that upgrade from one coordinate:
  `parabolaEndpoint gamma = gamma^2 * X`.  Every endpoint evaluates to zero at
  `X=0`, so a coordinate can have arbitrary load, while any three distinct
  parameters fail the denominator-cleared polynomial collinearity identity.
  Evaluation-line incidence is therefore strictly weaker than source-line
  incidence even at degree one.

- The exact cross-coordinate repair is proven.  If the *same triple* of
  degree-`<k` endpoints is evaluation-collinear on at least `k` injected
  coordinates, its denominator-cleared collinearity polynomial has degree
  `<k`, vanishes identically, and the triple lies on one polynomial source
  line (`source_collinear_of_eval_collinear_on_k`).  The remaining target is
  thus a repeated-triple matching theorem, not a high-load theorem.

- Plain third-moment averaging does not reach that target.  The formal numeric
  audit `uniformTripleMoment_below_crossCoordinate_budget` shows that even the
  forced average load `1248534` on every off-base coordinate leaves the raw
  triple-incidence lower benchmark far below the `(k-1)` recurrence capacity
  of all regular triples.  Any successful repeated-triple argument must use
  the polynomial/cross-coordinate structure rather than an unstructured
  convexity estimate.

- The third-incidence constraint is now available globally rather than only as
  a per-triple statement.  `sum_choose_three_support_eq_sum_tripleContainment`
  proves the exact double count
  `sum_x choose(load(x),3) = sum_{|U|=3} |commonCoords(U)|`.
  Consequently `sum_choose_three_support_le_of_triple_cap` turns the
  non-source-collinear root cap `|commonCoords(U)| <= k-1` into a global
  hypergraph moment bound.  This is designed as an input to the distributed
  block-Vandermonde/GM-MDS rank lane: the upper side is now axiom-clean; the
  missing ingredient is a structured lower bound stronger than ordinary
  convexity at the literal P1 constants.

- This census is now wired to `BadScalarRichPointFamily`, rather than left as
  an abstract set-system interface.  `richFamilySupport` is the coordinate-side
  support hypergraph, and its three-label containment coordinates are exactly
  the intersection of the corresponding three `fullAgreement` sets.
  `richFamilyTripleCoords_card_le_k_pred_of_not_sourceCollinear` uses the
  selected polynomials' decoded degree bounds to prove the `k-1` cap for every
  triple failing the polynomial source-collinearity identity.  Thus the upper
  side of the global third-incidence argument no longer requires a separately
  supplied combinatorial or rigidity hypothesis.

- The fully quantified consumer is now packaged as
  `richFamily_exists_sourceCollinear_of_thirdMoment_gt`: if the actual rich
  family exceeds `choose(|G|,3)*(k-1)` triple incidences, three distinct decoded
  points lie on one polynomial source line.  Conversely,
  `richFamily_thirdMoment_le_of_no_sourceCollinear` supplies the exact global
  cap when no such triple exists.

- Literal arithmetic shows why this still does not close from degree data
  alone.  For `|G|=N+1`, the balanced distribution of `(N+1)T` mandatory
  incidences has load `T+1` on `T` coordinates and `T` on the rest.  The exact
  theorem `uniformFullFamily_thirdMoment_below_sourceCollinear_capacity` proves
  its third moment is strictly below `choose(N+1,3)*(k-1)` (the capacity is
  about `1.486` times the balanced floor).  Thus the remaining lower bound must
  certify substantial nonuniformity or correlated support structure; support
  cardinalities and ordinary convexity cannot do so.

- The rank-two/source-pencil branch now has a direct terminal consumer.
  A denominator-cleared collinearity identity with one fixed distinct anchor
  pair puts the third decoded point on the anchors' canonical `secantParameter`.
  If the identity holds for every selected point, `pointsOn` equals the whole
  rich family and the existing line-core packing inequality gives `|G| <= N`
  (`richFamily_card_le_N_of_anchorCrossProducts`).  The family-wide wrapper
  `richFamily_card_le_N_of_allTriplesSourceCollinear` shows it suffices that
  every three distinct selected points be polynomial-source-collinear.  Thus a
  future distributed-rank theorem concluding rank at most two now plugs into
  the exact prize budget without another geometric residual.

- Taking the contrapositive gives a concrete rank-three seed for every
  over-budget family: `exists_nonSourceCollinearTriple_of_N_lt_richFamily_card`
  produces three distinct decoded points failing the source-collinearity
  identity.  Three-set Bonferroni at the literal threshold further forces one
  of their pairwise agreement cores to have size at least `234881025`.
  `exists_nonSourceCollinearTriple_with_largePairCore` packages both facts.
  This core is exactly `33554431` coordinates short of `k`, so the new seed is
  near the interpolation boundary but does not falsely claim that the pair
  already determines joint agreement.  It is a concrete starting minor for
  distributed-rank amplification.

- Choosing the anchors before the third point sharpens this substantially.
  Exact constant-weight Plotkin at `|G|>N` forces a pair intersection of at
  least `327272221`; every fixed distinct pair then has a noncollinear third,
  since otherwise the fixed-anchor closure would give `|G|<=N`.
  `exists_nonSourceCollinearTriple_with_interpolationPinnedAnchor` packages
  the result.  Its anchor core exceeds `k` by `58836765`, but is also exactly
  one coordinate below the established saturation-overlap ceiling
  `327272222`.  This one-coordinate boundary is honest and potentially useful:
  ordinary constant-weight averaging cannot improve it at the minimal
  `N+1` trigger, so the missing `+1` must come from noncollinearity or the
  divided-difference specialization rather than another Plotkin pass.

- Line-core packing now turns that seed into a clean structural split.
  `three_pointsOn_force_core_ge_352321537` proves that any relevant line with
  three selected threshold points has core at least `352321537`, the exact
  floor `ceil((3T-N)/2)`.  Its contrapositive wrapper proves that below this
  floor a relevant line contains exactly two points.  Hence the pinned anchor
  line either jumps another `25049316` coordinates above the Plotkin-extracted
  core, or it is an isolated two-point secant and every other selected point is
  off that line.  Both branches are concrete inputs for further rank/core
  amplification; neither is silently identified with closure.

- The next multiplicity rung is also exact: four selected points on a relevant
  line force core at least `432479347 = ceil((4T-N)/3)`; below that floor the
  line carries at most three points.  The packaged alternatives
  `relevantLine_core_ge_352321537_or_card_eq_two` and
  `relevantLine_core_ge_432479347_or_card_le_three` expose the ladder directly
  to downstream K4/high-core code.  The already known five-point floor is
  `472558252`, so the anchor branch is now localized into narrow two-, three-,
  four-, and saturated-line regimes rather than one undifferentiated high-core
  case.

- The three-line determinant route has been audited separately in
  `_P1RateQuarterRankThreeDeterminantAudit.lean`.  Determinant multiplicity
  requires total core mass at least `1610612735`.  Three-set Bonferroni supplies
  only `704643074` (deficit `905969661`), while the pinned anchor plus two
  universal pair floors supplies `550968437` (deficit `1059644298`).  Thus the
  determinant theorem is an amplifier, not a consequence of the current seed.
  After paying the `327272221` anchor, the other two cores must sum to
  `1283340514`, forcing one to reach `641670257`.  This exact threshold is the
  honest core-growth target for any determinant-collapse continuation.

- The isolated two-point anchor branch now has a P1-specific reduced-universe
  increment in `_P1RateQuarterPinnedAnchorPetalGrowth.lean`.  The anchor core
  leaves at most `746469603` coordinates; every outsider has at least
  `T-(k-1)=324359511` fresh agreements there.  The exact Rankin budget
  `746469603*140942232 <= 324359511^2-1` forces two outsiders with secant petal
  at least `140942233`.  That petal lies in a distinct relevant secant core of
  the same size.  Thus the isolated anchor does not merely leave an
  unstructured outside population: it generates a second, quantitatively
  large core, though still below the half-domain/high-core regime.

- The recursive two-core supply is now formalized as well.  The anchor line
  has two points and the second line has core at least `140942233`, so at least
  `140942232` selected points lie off both lines.  Every such point retains at
  least `T-2(k-1)=55924056` agreements outside the two-core union.  The two
  certified disjoint contributions leave at most `605527370` coordinates.
  Exact constant-weight arithmetic refutes a pair cap `5164919` for this
  population/weight/universe triple, identifying `5164920` as the next forced
  fresh-intersection target.  The supply and arithmetic are proven; the
  remaining work is the reduced-subtype Plotkin extraction that turns them
  into a named third secant core.

- That subtype weld is now closed.  The off-both fresh sets are trimmed to
  weight `55924056`, transported into the complement subtype without changing
  cardinalities or intersections, and fed to exact constant-weight Plotkin.
  `exists_outsideBoth_secantPetal_card_ge_5164920` produces two off-both
  points whose canonical secant contributes `5164920` genuinely new
  coordinates outside both earlier cores.  The geometric wrapper produces a
  third relevant line, distinct from the anchor and second line, carrying that
  new core petal.  The isolated-anchor branch therefore yields a certified
  three-line core-growth chain with disjoint increments
  `327272221`, `140942233`, and `5164920`.

- Exact line packing has now been fused into this chain.  Each of the second
  and third lines either reaches the three-point high-core floor `352321537`
  or contains exactly two selected points.  Hence the isolated-anchor branch
  terminates in a genuine high-core jump, or produces three pairwise-distinct
  isolated secants with the certified disjoint increments above.  This is the
  next recursion interface: high-core machinery handles the first outcome;
  another reduced-universe pass can continue from the three-isolated-line
  outcome.

- The complementary high-core branch now has its own P1 increment.  At core
  `352321537`, a line below the four-point floor carries at most three points;
  its complement has at most `721420287` coordinates, while every outsider
  again has `324359511` fresh agreements.  Reduced Rankin forces an outsider
  secant petal of size `145836060`.  The packaged continuation says: a
  `352321537` core either jumps to `432479347`, or emits that petal.  Conversely,
  the three-isolated-line recursion cannot be extended by naive subtraction:
  `T-3(k-1)=0`.  Any fourth-line step must therefore use determinant/petal
  overlap structure rather than another independent root cap.
  The cross-label information discarded by the binary abstraction is now
  retained explicitly.  Writing
  `E(x)=u₀(x)+γ₀u₁(x)−p₀(x)`, a coordinate labelled `γ` in one pencil and `δ`
  in another satisfies
  `(γ−γ₀)(δ−γ₀)(d₁−d₂)=(δ−γ)E`; reversing the labels reverses the sign
  (`commonBase_crossVote_directionDiff_identity` and its reverse).  Squaring
  removes the orientation and gives one common mismatch-square law on both
  cross classes (`commonBase_crossVote_directionDiff_square_identity`).  This
  is strictly richer than the equality-pattern/Vandermonde reduction.  Its
  current limitation is equally precise: `E` is an arbitrary received-word
  mismatch, not a degree-bounded polynomial, so the square identity is not by
  itself eligible for polynomial root counting.  A successful continuation
  must eliminate `E²` across several pencils or derive a low-degree model for
  it on a sufficiently large union of cross-label coordinates.

This is not yet a contradiction.  It is the precise surviving residual for
the sub-nine alignment layer: algebra must exclude or classify tens of
millions of distinct common-base pencils (equivalently, the enormous
common-base hit concentration producing them).  Pure private-petal counting
and sparse pair-overlap arguments cannot solve that layer.  For `N+1` partners (one
more than the exact rebased prize family), the load improves to `60118358`;
the formal kernel keeps this stronger but non-prize-scale variant separate.

### One-line petal recursion no-go (2026-07-11)

An exact recursion audit rules out repeatedly applying the reduced Plotkin
step as the missing amplifier.  With fresh size
`A = T-(k-1) = 324359511`, the guaranteed next-core map is
`P(c) = floor((A^2-1)/(N-c))+1`.  Machine-checked arithmetic gives
`P(145836060)=113383381` and the exact integer fixed point
`P(109061044)=109061044`; this is below the universal pair-intersection floor
`2T-N=111848108`.  Thus independent petal recursion loses the high-core gain
and returns below information already supplied by inclusion--exclusion.  The
missing input must be genuinely cross-line: weighted overlap, determinant
multiplicity, or common-coordinate charge.

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
