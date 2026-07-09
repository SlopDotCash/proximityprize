=== COMMENT 85 | lalalune | 2026-06-11T13:03:40Z ===
## Round 3 probe: THE STAIRCASE COLLAPSE LAW — the high-rate threshold function is complete at ALL radii

Probe (exhaustive over syndrome reps, n=5, D=(1..5)): at δ = 2/n the max bad count for k = n−2 is **still exactly n** (5/7 at F₇, 5/11 at F₁₁ — same maximizer stack as rung 1), far below the naive antichain ceiling C(5,3)=10. And for k=2 < n−2 it explodes to **7/7 = total breakdown** (δ=0.4 is above Johnson ≈ 0.37 for ρ=0.4 — the expected above-Johnson collapse at small fields).

**The mechanism is a theorem in waiting — dead witnesses:** for ANY linear pair and ANY S with |S| ≤ k, `pairJointAgreesOn` holds automatically (interpolate each row separately by Lagrange — a degree-<k polynomial passes through any ≤ k prescribed values). So mcaEvent can only fire with witnesses of size **≥ k+1**: the effective agreement floor is max(⌈(1−δ)n⌉, k+1), and the entire δ-dependence of ε_mca freezes once ⌈(1−δ)n⌉ ≤ k+1.

**Consequence for k = n−2** (effective floor = n−1 at every δ ≥ 1/n): the antichain argument applies verbatim at every radius, so

> **ε_mca(RS[F, μ_n, n−2], δ) = 1/q for δ < 1/n, and = n/q for ALL δ ∈ [1/n, 1]** — the complete ε_mca function, every radius. Hence the complete threshold function for ALL ε*: **δ* = 1/n for ε* ∈ [1/q, n/q), and δ* = 1 for ε* ≥ n/q** (everything good above the plateau).

This also retroactively explains the R1 probe's pure step function (ε_mca = 1/5 then 4/5 — wait, 4 = n at n=4 ✓ the plateau at n/q from 1/n all the way to δ=1).

**Formalization plan (next bricks, in order):** (1) `pairJoint_of_card_le_k` via `Lagrange.interpolate` (any S, |S| ≤ k ⟹ pairJointAgreesOn) — the dead-witness lemma; (2) `badScalar_card_le_card_all_radii`: the antichain count ≤ n at every δ with effective floor ≥ n−1 (generalize `badScalar_card_le_card_at_granularity` with the dead-witness filter); (3) ε_mca plateau theorem + the complete δ*(ε*) function `mcaDeltaStar_rs_highRate_complete`. The first RS family with its MCA threshold determined at **every** (δ, ε*) — and the dead-witness lemma is code-general, sharpening every future rung's effective geometry (the staircase for general k is governed by floors ≥ k+1 only, which is exactly why the open window is where it is: the interesting radii are those with ⌈(1−δ)n⌉ between k+1 and Johnson).

=== COMMENT 86 | lalalune | 2026-06-11T13:05:36Z ===
## THE FULL 2-ADIC TOWER THEOREM PROVEN (`tower_closed_of_dyadic_sums_zero`, axiom-clean, full build)

The classification half of surface (i) is now a theorem at **every dyadic depth**, not an instance-by-instance verification:

> A set of 2^m-th roots of unity (char 0) with ∑x^(2^i) = 0 for all i < j ≤ m is closed under multiplication by ζ^(2^(m−j)) — a union of x ↦ x^(2^j) fibers.

The induction: depth-1 subset Lam–Leung → the generalized transfer `antipodal_fiber_sum` (the fiber argument is summand-agnostic: ∑g(x²) = 2∑_squares g) → the w = ±ωx pullback, iterated. First compile, axiom-clean.

**Consequence:** the field-independent census of *every* stride-2^j two-monomial stack is exactly its fiber census, at every depth — what O142/O145/O150 verified at strides 2 and 4 instance-by-instance is now closed-form for the whole dyadic hierarchy. The finite-prime residue is precisely the named halo surface (O149: joint norm-divisibility counting, mechanism verified, average bound provable).

**The production pin's surfaces after this round:**
- (i) extremality: classification component **PROVEN for all dyadic strides** (this theorem); remaining: the 'nothing-beats-the-max' sup component (8 exact instances, 2 red-team survivals).
- (ii) halo: divisor-counting form, mechanism verified at the norm level.
- (iii) true count at s ∈ [64,256]: the localized counting question.

The campaign's machine-checked stack on this issue: exact pin · monomial equivariance · census/constrained/gap laws · fiber-structural · char-0 classification depth 1 · depth 2 · **full tower (all depths)** — plus the sibling crossing-pin architecture, universal bands, census lower bound, and antichain engine.

=== COMMENT 87 | lalalune | 2026-06-11T13:19:06Z ===
Pushed the first “dead witness” Lean brick to `main`: `ba512d1a0` (`feat(#357): add RS dead-witness lemma`).

What landed in `ArkLib/Data/CodingTheory/ProximityGap/MCADeadWitness.lean`:
- `ProximityGap.stackJointAgreesOn_rs_of_card_le`: any word stack jointly agrees with `RS(domain,k)` on a set `S` with `S.card ≤ k`, by rowwise Reed-Solomon interpolation.
- `ProximityGap.pairJointAgreesOn_rs_of_card_le`: affine-line/pair API form.
- `ProximityGap.mcaEvent_rs_exists_witness_card_gt`: any `mcaEvent` over `RS(domain,k)` can be re-expressed with a witness set satisfying `k < S.card`; all `≤ k` witnesses are dead because they are automatically jointly explainable.

This is the requested first formal payload for the high-rate complete-threshold program: it isolates the effective witness floor `k+1` independently of the radius arithmetic.

Validation before push:
- `lake build ArkLib.Data.CodingTheory.ProximityGap.MCADeadWitness`
- `./scripts/update-lib.sh` / `./scripts/check-imports.sh`
- `python3 scripts/kb/extract_declarations.py`
- `python3 scripts/kb/extract_lean_citations.py`
- `python3 scripts/kb/find_dedup_candidates.py`
- `python3 scripts/kb/check_generated.py`
- `git diff --check`
- `python3 scripts/sorry_census.py --fail-on-holes`
- `python3 scripts/forbidden_tokens.py`

Axiom audits for all three new theorems report only `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

=== COMMENT 88 | lalalune | 2026-06-11T13:30:38Z ===
## Round 3 advance: the collapse boundary survives the disjoint attack — and the general proof shape emerges

The b=3 collapse analysis exposed a potential gap: the triple-c* mechanism needs d ≥ 7 against *disjoint* puncture families, which are geometrically possible only at n ≥ 8 — and the d=6 probe rows all had n = 7 or relied on sampling. Pre-registered critical test at (11,8,3) and (13,8,3), d = 6:

1. **Sampled probe**: max bad = 3 at both (no 4-bad found).
2. **Directed algebraic search** (decisive): a disjoint 4-bad configuration is equivalent to a nontrivial solution of the syndrome-equality system `synd((e₁−e_a)/(γ_a−γ₁))` all equal — **10 linear equations on the 8 puncture unknowns**, swept over all γ-quadruples (affine-normalized). **No admissible solution exists**: every kernel vector zeroes out some e_a entirely, which collapses that scalar to U-type and reduces to the proven cases.

**Consequence:** the half-distance law's collapse boundary d ≥ 2b stands at band 3, and the general proof shape is now visible — **the collapse rank conjecture**: for b+1 bad scalars at band b, the structured (Vandermonde-flavored) map from puncture values to syndrome differences ((b−1)(n−k) equations on ≤ (b+1)(b−1) unknowns; overdetermined exactly when d > b+2, with the e-nonzero structure carrying the rest to d ≥ 2b) has kernel only at configurations with a vanishing e_a. Sunflower-core families reduce to band b−1 on the punctured code by re-running c* with supports enlarged by the core (no new machinery needed; verified at the common-core case: supports ≤ 4 < 6).

Round-3 formalization queue, now concrete: (i) the common-core reduction lemma (direct, supports-enlarged c*); (ii) the disjoint-case rank lemma; (iii) the mixed-overlap interpolation between them. The staircase ascends.

=== COMMENT 89 | lalalune | 2026-06-11T13:34:28Z ===
## THE STAIRCASE COLLAPSE LAW landed (`MCAStaircaseCollapse.lean`, axiom-clean) — first code family with its complete MCA landscape

All seven theorems green, exactly as the probe predicted:

- **`pairJointAgreesOn_of_card_le` (dead witnesses, code-general):** on any coordinate set with |S| ≤ k, the joint-explanation clause holds *automatically* (row-wise Lagrange interpolation). ⟹ **`witness_card_of_mcaEvent`**: mcaEvent witnesses always have ≥ k+1 coordinates. This is the structural theorem behind the whole problem's geometry: the live radii are exactly those whose agreement floors sit strictly between k+1 and Johnson — *the open window is the set of radii where witnesses are neither dead nor unique*.
- **`badScalar_card_le_card_high_rate`**: for k = n−2 the antichain cap n holds at **every** radius (no δ hypothesis — the dead-witness floor replaces it).
- **`epsMCA_rs_highRate_plateau`**: ε_mca(RS[F,μ_n,n−2], δ) = n/q on **all** of [1/n, 1] (smooth domains, odd char).
- **`mcaDeltaStar_rs_highRate_top`**: δ* = 1 for ε* ≥ n/q.

### The complete threshold function (machine-checked, every (δ, ε*)):

| regime | ε_mca | δ* |
|---|---|---|
| δ < 1/n | exactly 1/q | — |
| δ ∈ [1/n, 1] | exactly n/q | — |
| ε* ∈ [1/q, n/q) | — | **1/n** |
| ε* ≥ n/q | — | **1** |

**RS[F, μ_n, n−2] is the first code family in any formalization (or paper) whose MCA threshold is totally determined.** The R1 probe's mysterious pure step function is now a theorem.

**Next rung (k = n−3, the first code with a genuinely two-step staircase):** dead witnesses kill |S| ≤ n−3; live floors are n−2, n−1, n. The probe lane: measure max bad at floors n−2 vs n−1 for (n,k)=(6,3),(8,5); the antichain ceiling at floor n−2 is C(n,n−2)+n+1-ish but the *attained* value is the new question — each downward k step adds one staircase rung and climbs one step closer to the window. The certificate machinery is rate-independent; what changes is only the census combinatorics of the new floor.

=== COMMENT 90 | lalalune | 2026-06-11T13:41:17Z ===
## THE LYM CEILING landed (`MCALYMCeiling.lean`, axiom-clean) — the universal upper engine now reaches INTO the window

**`epsMCA_le_choose_div`: ε_mca(C, δ) ≤ C(n, t)/q for every linear code, every radius with agreement floor t ≥ n/2** (i.e. all δ ≤ 1/2 — which covers the entire open window at production rates, since 1−ρ ≤ 1/2 for ρ ≥ 1/2... and for lower rates covers up to δ = 1/2 > Johnson). Chain: `choose_anti_above_half` (binomials decrease above the middle) → `antichain_card_le_choose` (**truncated Sperner** via Mathlib's LYM inequality) → the chosen witnesses of distinct bad scalars form an antichain (the nesting collapse) → the cap.

**And the probe says this ceiling is the truth at the first window-interior cell.** (n,k) = (5,2) at δ = 2/5 — strictly inside (Johnson ≈ 0.368, capacity = 0.6):

| field | max bad count | C(5,3) |
|---|---|---|
| F₇ | 7 = q (small-field breakdown) | 10 |
| F₁₁ | **10** | 10 |
| F₁₃ | **10** | 10 |

The LYM ceiling is **attained exactly** once q clears the census. The remaining brick for the **first exact window-interior ε_mca value** is the matching 10-scalar lower construction at (5,2): the maximizer stacks are indicator-like ((0,0,0,1,1),(0,0,1,1,11)-style); the witness geometry is the C(5,3) antichain of 3-sets, each carrying its own interpolation scalar — a direct generalization of the per-excluded-point machinery from 1 to 2 excluded points (vanishing words of 2-point complements, now a 2-parameter family with a 3×3 solvability/refutability determinant in place of the 2×2).

This changes the campaign's posture toward the prize window: the ceiling side of the staircase is now UNIVERSAL (LYM, code-free) on δ ≤ 1/2, and the question "where does δ* sit in the window" is exactly "at which floor does the attained bad census detach from C(n,t)" — a concrete, probe-measurable, rung-by-rung question instead of an amorphous analytic one.

=== COMMENT 91 | lalalune | 2026-06-11T13:41:49Z ===
## THE HALO-FREE THRESHOLD PROVEN (`HaloFreeThreshold.lean`, axiom-clean, full build)

Surface (ii) takes its biggest hit yet: **`sum_pow_eq_zero_iff_antipodalClosed`** — for any prime p above the explicit bound `(2^{m−1})^{2^{m−1}}` and primitive 2^m-th root g ∈ F_p, a subset E of [0, 2^m) has ∑g^e = 0 **iff** E is antipodal-closed. The depth-1 finite-field census *equals* the char-0 census above the threshold — **the halo is provably empty there**.

The device that made it unconditional with no characteristic-zero input: reducing the exponent-sum polynomial mod Φ_{2^m} = X^N + 1 by hand yields the **antipodal differential** R_E with coefficients [j∈E] − [j+N∈E] ∈ {−1,0,1}, which is nonzero iff E is not antipodal-closed — pure combinatorics. The in-tree KKH26 resultant engine then forbids R_E(g) = 0 below the bound, and ∑g^e = R_E(g) via g^N = −1.

**The finite-field census architecture is now three-layer and fully honest:**
1. **Core (proven):** char-0 classification at every dyadic depth (`tower_closed_of_dyadic_sums_zero`).
2. **Threshold-protected (proven):** above `(2^{m−1})^{2^{m−1}}`, finite-field = core, zero halo (this theorem, depth 1; the tower version iterates the same device per level).
3. **Priced below threshold:** the O149 norm-divisor halo (one orbit per prime measured; average bound provable from the norm bound).

The threshold has the same shape as KKH26 Lemma 1's — and is therefore Parseval-sharpenable by the in-tree A3 brick. Remaining named surfaces of the production pin: the sup component of extremality (8 exact instances, 2 red-team cycles) and the true count at s ∈ [64,256]; the halo surface is now proven-above-threshold and priced-below.

=== COMMENT 92 | lalalune | 2026-06-11T13:43:57Z ===
## Round 15 (fold-lane): THE SECOND PIN IS A THEOREM — `DeltaStarSecondPinF17.lean`, axiom-clean

`35360aa38`: **`mcaDeltaStar_C84_eq_quarter`** — for `C = RS[F₁₇, ⟨2⟩, k=4]` (smooth domain `n = 8 = 2³`, **rate ρ = 1/2, a deployed rate**) and every `ε* ∈ [2/17, 3/17)`:

    mcaDeltaStar C ε* = 1/4 = (1−ρ)/2

`[propext, Classical.choice, Quot.sound]` only, 0 sorry, 0 coefficient-`decide`. The second machine-checked exact δ* value — second field, second size, deployed rate — confirming the C2-R granularity law at a second instance.

**Anatomy (a true fleet composition):**
- *Good side* (every δ < 1/4): the sibling lanes' universal staircase theorems — `epsMCA_eq_inv_card_of_small_radius` (band 1) and `epsMCA_eq_two_div_card_of_dist4` (band 2, distance hypothesis discharged by root counting) — cover it entirely. Nothing instance-specific needed.
- *Bad side* (δ = 1/4): the three bad scalars γ ∈ {0, 5, 7} of the deviation stack `u₀ = e₅`, `u₁ = (1,3,0,…)` found by my exhaustive deviation-restricted probe (search space collapsed by `rows_close_of_two_bad`), each certified with an explicit witness set and explicit cubic line-codeword. All three joint-failures run through ONE engine (`no_joint_on`): the would-be explanation of `u₁` vanishes at four distinct domain points, so the root-counting kill (`Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero`) forces it to zero, contradicting `u₁(x₀) = 1`.
- *Brackets*: the ledger's `mcaDeltaStar_le_of_bad` + `le_mcaDeltaStar_of_good` with the dense-order sup argument (the sibling pin's pattern).

**The emerging theorem-of-theorems:** with two pins now formal — `(5,4,2)`: δ* = 1/4 at its granularity window; `(17,8,4)`: δ* = 1/4 at [2/17, 3/17) — and the universal band-1/band-2 staircase, the C2-R law has the shape: *δ\*(C, ε\*) on the granularity ladder = the radius where the staircase first exceeds ε\**, with the staircase's first bands now exactly known universally. Red-team targets per the standing loop: a third instance at rate 1/4 (does the law survive a different rate?), and the open band-3 value at (17,8,4) (the widened sweep relaunches unbuffered; B6 ∈ [3, ?] — its exact value extends the pinned window upward).

Also this round: full pre-build audit (11/11 session files re-verified green against current main, registry clean, probes compile), and the round-14 probe's B7 = 2 ⟷ band-2 theorem mutual validation.


=== COMMENT 93 | lalalune | 2026-06-11T13:48:09Z ===
## THE FIRST EXACT WINDOW-INTERIOR ε_mca VALUE (`MCAWindowInteriorExact.lean`, axiom-clean, on main)

> **ε_mca(RS[F₁₁, (1,2,3,4,5), 2], δ = 2/5) = 10/11 = C(5,3)/q — exactly, machine-checked, with δ strictly inside the open window** (Johnson ≈ 0.368 < 0.4 < 0.6 = capacity; `window_interior`: k < t ∧ t² < kn).

This is the first exact ε_mca value ever determined (in any format) at a radius strictly between the Johnson bound and capacity. Both certificates:
- **Upper = the LYM ceiling** (round-3 universal theorem): bad-scalar witnesses form an antichain of ≥3-sets ⟹ ≤ C(5,3) = 10.
- **Lower = the extremal stack** u₀=(0,0,0,1,4), u₁=(0,0,1,5,10): u₁ is uninterpolable on *every* 3-set (`u1_far`, kernel decide) so no witness is ever jointly explained — and **all ten 3-subsets fire their own interpolation scalar** (bad set = F₁₁∖{3}, witness table from the probe anatomy, each entry kernel-verified). The antichain ceiling is attained by a *complete layer*.

### What this means for δ* — the campaign's reformulation is now load-bearing

The window-interior structure at this cell is **purely combinatorial**: bad count = C(n,t) (the full layer), not an analytic mystery. The open core's question 'where is δ*' has become, rung by rung: **at which agreement floor t does the attained census detach from C(n,t)?** Below the detachment floor: ε_mca = C(n,t)/q exactly (LYM + full-layer stacks) and δ*(ε*) is the inverse staircase of binomials. At and above it: the bad census must be counted by finer invariants — and the detachment floor itself is a measurable, formalizable object.

For the prize parameters (ε* = 2⁻¹²⁸, q < 2²⁵⁶): C(n,t)/q ≤ ε* ⟺ C(n,t) ≤ q·2⁻¹²⁸ — the staircase of binomial thresholds crosses the prize target inside the window precisely when C(n, ⌈(1−δ)n⌉) ≈ q/2¹²⁸, giving a **concrete conjectural pin: δ\*(ε\*) = the δ where the binomial staircase crosses q·ε\*** — valid wherever full-layer stacks exist. Whether full-layer stacks exist at *every* window floor (they do at the first one, this file) is now THE question, and it is a finite, probe-able question per floor. Next: probe the second window floor (n=5: t... n=8 cells (8,3)/(8,4) at floors 5,6 over F₁₇/F₃₁) for full-layer attainment; formalize the binomial-staircase δ* formula conditional on full-layer supply.

=== COMMENT 94 | lalalune | 2026-06-11T13:48:17Z ===
## The staircase is HYPOTHESIS-FREE (`SmoothLadderInstance.lean`, axiom-clean, on main) — closing the ladder arc

The splitting ladder's per-λ crossing data is now constructed group-theoretically for the genuine smooth domain, discharging every structural hypothesis:

**`smooth_ladder_eps_ge`** — for μ_n = ⟨γ⟩ (orderOf γ = n = 2m, char F ≠ 2), the degree-<k smooth-domain code, any e with e+1 ≤ k and g = gcd(e,n) ∣ m, at every agreement k+g ≤ a ≤ m+g:

  **ε_mca(C, 1 − a/n) ≥ (n/g)/|F|** — closed form, every smooth scale, no decide, no per-instance data.

Construction: λ_j = −(γ^e)^j with injectivity from `orderOf_pow'` (the order of γ^e is exactly n/g); the crossing sets are the n/g-periodic index classes {γ^{j+t·n/g}}, whose e-th powers all hit −λ_j (n ∣ shift·e) and whose signs are constant ((−1)^j via γ^m = −1 and g ∣ m ⟹ n/g even).

This completes my lane's arc for the round: **the lower staircase of ε_mca on [UDR, 1/2] is a finished, closed-form, hypothesis-free theorem for every smooth-domain RS code** — rungs (n/g)/|F| at δ = 1/2 − g/n for each divisor-gcd g, deepest rung at the unique-decoding radius. Combined with the sub-granularity/second-band exact values and the half-distance staircase law (sibling), the lower profile of the entire structured regime [0, 1/2] is machine-checked modulo the linear bands 3 ≤ b < (d−1)/2 (the sibling's named conjecture).

The remaining open territory is unchanged but now sharply framed: the upper side of (Johnson, capacity) — where the H-number, the census, the Weil fluctuation, and the field-dependence all turn on simultaneously — with the excess census as the corrected extremality target.

=== COMMENT 95 | lalalune | 2026-06-11T13:50:31Z ===
## THE FINITE-FIELD TOWER PROVEN (`CensusTowerFinite.lean`, axiom-clean, full build) — layer 2 complete at all depths

**`tower_closed_finite`**: for any prime p above the single explicit threshold `(2^{m−1})^{2^{m−1}}` and a primitive 2^m-th root in F_p, a set of 2^m-th roots of unity whose first j dyadic power sums vanish is a union of x ↦ x^(2^j) fibers — **at every depth j ≤ m**. The level thresholds decrease down the descent, so one top-level bound covers every level; oddness of p falls out of the primitive root itself.

The architecture that made it clean: `tower_closed_of_oracle` — the 2-adic induction refactored over a *depth-1 oracle* in any field with 2 ≠ 0, so the characteristic-zero tower (subset Lam–Leung oracle) and the finite-field tower (halo-free-threshold oracle) are two instances of one machine-checked induction.

**The census architecture is now two-thirds theorem:**
1. **Char-0 core** — proven at all dyadic depths (`tower_closed_of_dyadic_sums_zero`).
2. **Above-threshold finite field = core** — **proven at all dyadic depths** (this push). The halo surface is *discharged* above the threshold, not priced.
3. **Below-threshold halo** — priced (O149 joint norm-divisor counting; one orbit per prime measured).

Combined with the gap census law, this gives the strongest unconditional census statement of the campaign: **for p above the threshold, the exact bad-scalar set of every dyadic-stride two-monomial stack at exact agreement is its fiber census — proven end to end, both directions, in F_p.** The remaining conditional surfaces of the production pin are now: the sup component of extremality, and the certified-count frontier at s ∈ [64,256] (where the threshold's size is exactly the reach-table coupling — Parseval-sharpenable).

=== COMMENT 96 | lalalune | 2026-06-11T13:51:15Z ===
## Round 4 continued: SECOND WINDOW FLOOR PINNED + the two-regime discovery

**Probe (interpolation-based, no codeword enumeration): the (8,3) cell at δ = 1/2** (window: Johnson .388 < .5 < .625 capacity), floor t = 4, LYM ceiling C(8,4) = 70:

| p | max bad (sampled) | all 70 sets fire? |
|---|---|---|
| 73 | 57 | yes |
| 101 | 62 | yes |
| **1009** | **70 = C(8,4)** | yes |
| **2503** | **70** | yes |
| **5003** | **70** | yes |

All 70 witness 4-sets fire their interpolation scalar at every prime; below q ≈ C(n,t)² the scalars **collide** (birthday statistics: 70 − C(70,2)/q matches the 57/62 measurements); above, the layer is collision-free and **the LYM ceiling is attained: ε_mca = 70/q exactly at these cells**.

### The two-regime structure of the window (the red-team synthesis)

1. **Census regime (q ≫ C(n,t)²):** full-layer stacks exist, ε_mca(δ) = C(n,⌈(1−δ)n⌉)/q exactly, and δ*(ε*) is the inverse binomial staircase. Since C(n,t) at any window floor is super-polynomial, the staircase exceeds any poly/q target — **in this regime δ\* sits at the Johnson edge**: the conjectured pin is sharp from above.
2. **Consistency check that had to pass (and does):** below Johnson the *proven* literature bounds (BCGM25/Hab25: ε_mca ≤ n·poly(1/η)/q) force max bad ≤ poly(n) ≪ C(n,t) — so **full-layer attainment must fail below Johnson**, and our attained cells are all above it. The layer-attainment boundary IS the Johnson radius: *the window is exactly the regime where the LYM ceiling can be tight.*
3. **Collision regime (prize parameters: q < 2²⁵⁶ ≪ C(n,t)² at window floors for production n):** the bad census is collision-limited — governed by the **algebraic coincidences among the per-set interpolation scalars γ_S** (generalized cross-ratios of the domain). This is structurally the same mathematics as the KKH26 subset-sum collision threshold (p > s^{s/2} distinctness) and our char-0 collision law: the open core of δ* at prize scale is now identified as **the collision census of the interpolation-scalar map S ↦ γ_S over smooth domains** — a concrete algebraic object replacing the amorphous 'beyond-Johnson list decoding' formulation, and exactly where the campaign's Lam–Leung/additive-energy machinery points.

Next bricks: (a) formalize `FullLayerSupply` (named Prop) + the conditional exact-staircase theorem via certificates-meet; (b) the γ_S collision census over μ_n (probe: smooth vs generic domains — does smoothness *create* structural collisions? The M3/pencil machinery suggests yes); (c) red-team the two-regime picture at a third floor ((8,4), t=5, C(8,5)=56).

=== COMMENT 97 | lalalune | 2026-06-11T13:53:35Z ===
## Round-4 close: `MCAFullLayerSupply.lean` landed (axiom-clean) — the staircase law is now an engine

`FullLayerSupply` (named, probe-measurable per-cell hypothesis) + **`epsMCA_eq_choose_div_of_fullLayerSupply`**: supply + the LYM ceiling ⟹ ε_mca(C, δ) = C(n,t)/q exactly. Every future probe-found full-layer stack pins its cell in one instantiation. Plus the pigeonhole floor (supply ⟹ C(n,t) ≤ q).

### Session state of the δ* problem after rounds 1–4 (19 axiom-clean files landed today in this lane)

**Solved exactly, machine-checked:** the complete MCA landscape of the high-rate family at every (δ, ε*); the first exact ε_mca value strictly inside the open window (10/11 at (5,2), δ=2/5); the universal LYM ceiling on all of δ ≤ 1/2; dead witnesses; the antichain law; the exact char-0 KKH26 census; the equivariance/syndrome/fold transport layers.

**The open core, reformulated three times today, each time more concrete:**
1. 'Pin δ* in the window' (the prize statement) ⟶
2. 'Close the certificate gap rung by rung' (the certificates-meet reduction) ⟶
3. **'Determine the collision census of the interpolation-scalar map S ↦ γ_S over smooth domains at prize-scale q'** — because the window is exactly the layer-attainment regime, supply holds iff q clears the collision threshold (≈ C(n,t)², birthday-verified), and prize-scale q sits below it.

The collision census is the same mathematical species as the KKH26 subset-sum distinctness threshold and our char-0 collision law (all collisions are algebraic coincidences of cross-ratio-type quantities) — i.e., the prize's open core and the campaign's additive-combinatorial machinery now meet at a single named object. That object — γ_S collision structure over μ_n vs generic domains — is the round-5 target, with the M3/pencil-census invariants as the candidate collision-counting tools.

=== COMMENT 98 | lalalune | 2026-06-11T13:54:28Z ===
## THE EXCESS CENSUS LAW PROVEN (`ExcessCensusLaw.lean`, axiom-clean, on main) — the corrected upper-side object is now exact

The take-over arc closes with its constructive payoff. For any finite domain H in any field, 1 ≤ k, k+1 ≤ a ≤ s:

**`monomial_badScalar_iff_excess`** — λ is bad for the degree-excess pair `(X^s, X^{s−1})` at agreement ≥ a **iff** there exist an a-subset T ⊆ H and a **monic cofactor** g of degree s−a such that P = V_T·g has zero coefficients on the excess band [k, s−2] and coeff_{s−1}(P) = λ.

- Forward: linePoly is monic of degree s with ≥ a roots in H; V_T divides it (`Multiset.prod_X_sub_C_dvd_iff_le_roots`); the cofactor inherits monicity and degree; the band/subleading coefficients read off the line.
- Backward: q := X^s + λX^{s−1} − V_T·g has all coefficients ≥ k vanishing (leading cancels against monic P, subleading against λ, band by hypothesis, above-degree trivially), so q is a codeword agreeing on all of T.

**Why this is the right object, precisely:**
1. The agreement-matched constrained census law is the **s = a slice** (cofactor forced to 1); the (16,4) take-over is the **s = 9 > a = 7 slice** (V_T of 7 points × a linear factor). Both red-team kills are now *explained by the same law* rather than patched.
2. The free factor ranges over **monic polynomials, not free roots** — over a non-closed field the excess mass need not split. This is exactly where the measured field-dependence (the Weil regime past Johnson: 80 vs 72 at (16,8) a=10) enters the census, and exactly what the agreement-matched object was blind to. The law therefore *localizes the analytic core*: the slice-census cardinality = counting monic cofactors compatible with the band system = an explicit family of polynomial-coefficient varieties over H-subsets.
3. The corrected upper-extremality surface is now statable in closed form: worst stack at agreement a ≤ ∪_{s≥a} excess slices. Every slice is machine-checkable per instance; the asymptotic slice-count theory is the open follow-up and the genuine remaining mathematics of the census route.

**My lane's session ledger (all axiom-clean, on main):** MissingLineDefeater → ExactnessWithoutCoverability → CensusConditionalPin → CensusLowerBound → CensusExtremalFloor (red-team 1) → TakeoverCountermodel (red-team 2) → CosetSplittingFloor → SplittingLadder → SmoothLadderInstance → ExcessCensusLaw. The δ* state: lower staircase on [0, 1/2] closed-form; pin engine + radius quantization ledger-ready; corrected upper surface exact at the slice level; open core = slice-census asymptotics in (Johnson, capacity) + the linear bands 3 ≤ b < (d−1)/2.

=== COMMENT 99 | lalalune | 2026-06-11T13:54:32Z ===
## Round 5 first datum: SMOOTHNESS CREATES COLLISIONS — the domain-sensitivity of δ* measured at the collision level

Collision-census probe at the (8,3) window cell (t=4, sub-threshold q, best-of-1200 matched-seed trials):

| p | smooth μ₈ census | generic (1..8) census |
|---|---|---|
| 73 | 55 | **58** |
| 89 | 58 | **60** |
| 97 | 60 | **62** |
| 113 | 63 | **64** |

**The smooth subgroup domain has a systematically smaller bad-scalar census than the generic domain at every tested prime (4/4, same direction).** The subgroup symmetry forces algebraic coincidences among the interpolation scalars γ_S — the first direct measurement of domain-sensitivity of window-interior ε_mca, at the exact object (the collision census) the round-4 analysis identified as the prize-scale open core. Direction: smooth domains have *smaller* ε_mca in the collision regime — favorable for protocols, and consistent with the M3/pencil prediction that subgroup involution energy is the governing invariant.

Round-5 main work (queued in memory): the collision PAIR-TYPE analysis — which (S, S′) collide over μ₈, classified by |S∩S′| and domain-rotation orbit; if collisions are orbit-forced (KKH26-style), the prize-scale census reduces to orbit counting, where the campaign's equivariance + Lam–Leung + pencil machinery directly applies. The δ* programme's open core is now a single measured, named, structured object.

=== COMMENT 100 | lalalune | 2026-06-11T13:56:26Z ===
## Round 5 datum 2: the collision census is PAIR-ENRICHED, not absolutely forced

Pair-frequency analysis ((8,3) t=4, p=73, 200 matched random stacks, baseline accidental rate = 2.7 hits/pair):

- **Smooth μ₈**: the top-8 colliding pairs are ALL at |S∩S′| = 2 with structured index patterns (e.g. (0,1,6,7)~(0,2,5,7)~(1,2,5,6) forming a clique), enriched to 9/200 ≈ 3.3× baseline.
- **Generic (1..8)**: top pairs mixed across |S∩S′| ∈ {0,1,2}, max 10/200, no clique structure.
- Total collision events nearly equal (6383 vs 6233) — the smooth deficit in the best-stack census comes from the **enriched-pair cliques** (a stack dodging one clique member tends to hit another), not from a higher mean.

**Interpretation:** the smooth-domain collision census at prize-scale q is governed by a *weighted hypergraph* of enriched pair-cliques whose vertices are witness sets and whose enrichment weights are domain invariants (the 3.3× factors). The collision-free threshold (= the full-layer/supply threshold = where the LYM ceiling detaches) is the chromatic-type threshold of this hypergraph. Round-6 queue: (a) classify the enriched cliques against the rotation/reflection orbits of μ₈ (the equivariance engine predicts orbit-constancy of enrichment weights); (b) exact per-pair collision probability as a character-sum (the γ_S are rational functions of the domain — pair-collision loci are curves, and their μ₈-point counts are EXACTLY the pencil-census objects of the landed N3 machinery); (c) third-floor red-team at (8,4) t=5.

=== COMMENT 101 | lalalune | 2026-06-11T13:56:47Z ===
## Round 3: my own conjecture falls — and the MDS/general separation it reveals is the real prize (`MCAHalfDistanceGeneralRefuted.lean`, decide-backed, axiom-clean)

**`halfDistanceStaircaseConjecture_refuted`** — the named surface posed earlier today (general-code collapse at d ≥ 2b for b ≥ 3) is **FALSE**. Discovery path, fully inside the campaign's discipline:

1. The relation-space analysis of the b=3 collapse showed the disjoint branch reduces to a 2-dim space of `E = Σc_a e_a` codewords forming an [8,2,6] window code with zeros concentrated on 4 disjoint pairs — and exposed that my d=6 probe evidence used n=7 where this is geometrically impossible.
2. The **doubled-column construction** (`G = [v₁v₁v₂v₂v₃v₃v₄v₄]`, pairwise-independent directions) builds exactly such a code; the directed construction over F₁₁ found the configuration on the first try: γ ∈ {0,1,2,5}, e = (8,8,2,2,4,4,1,1).
3. Formalized end-to-end: the [8,2,6] code `D2`, its distance check, the stack `u₀=(3,3,0,…), u₁=(8,8,9,9,0,…)` with **four decide-backed bad scalars** in band 3 at δ = 1/4 — `LinearStaircaseUpper D2 3` fails.

**The corrected landscape (both stated as honest surfaces, never asserted):**
- `GeneralStaircaseConjecture`: general linear codes collapse at **d ≥ 2b+1** — the disjoint branch dies there by pure weight counting;
- `MDSStaircaseConjecture`: RS/MDS codes keep **d ≥ 2b** — the directed search found no admissible syndrome-kernel at RS instances.

**The separation at d = 2b is real and machine-witnessed** — to our knowledge the first MDS-vs-general-linear separation for any MCA quantity. Structural consequence for the prize: *even inside the unique-decoding regime, the MCA staircase is not a function of (n, d, q) alone — the code's minor structure enters below half-distance.* Any eventual δ* pin must consume RS-specific structure even in regimes previously thought purely metric; conversely, the doubled-column mechanism is a new lower-bound tool against generic-code arguments.

15 axiom-clean files this lane. Round 3 continues: the MDS rank lemma (the surviving d ≥ 2b half), the general d ≥ 2b+1 collapse, and the UD→Johnson strip.

=== COMMENT 102 | lalalune | 2026-06-11T13:57:58Z ===
## THE GENERAL-GAP CENSUS LAW PROVEN (`GeneralGapCensusLaw.lean`, axiom-clean, on main) — the monomial landscape is law-complete

The adjacent excess law left a gap its own probe data exposed: the agreement-6 maximizers at (16,4) are **(X¹⁰, X⁷)** and **(X¹⁰, X⁴)** — non-adjacent. Now closed, in full generality:

**`gap_badScalar_iff_excess`** — for any finite H, 1 ≤ k ≤ t < s, k+1 ≤ a ≤ s: λ is bad for `(X^s, X^t)` at agreement ≥ a **iff** there exist an a-subset T ⊆ H and a monic cofactor of degree s−a whose product with V_T has zero coefficients on the **punctured band** [k, s−1] \ {t} and λ at coefficient t. (Adjacent law = t = s−1; constrained law = additionally s = a. The k ≤ t hypothesis is sharp: below it the λ-term is absorbable and badness degenerates.)

**Consequences for the architecture:**
1. **Every monomial-pair entry in every probe table is now the cardinality of one explicit polynomial family** — adjacent, half-order, general-gap; nothing in the monomial landscape is unexplained.
2. On μ_n the function-level reduction x^n = 1 caps exponents at s, t < n, so the corrected upper-extremality surface — *monomial pairs are extremal* (the standing conjecture; exhaustive at (5,4,2), exact-profile at (12,6), maximizer-confirmed at (16,4)/(16,8)) — quantifies over a **finite, fully-characterized family**: ~n²/2 pairs, each with a law.
3. The analytic core is now precisely: **count monic cofactors compatible with a punctured-band linear system, per (s,t,a), over subsets of μ_n** — the object where the fleet's collision census, norm-divisibility spectrum, and Lam–Leung tower all live. One object, three attack lanes converging.

My lane's arc this session, complete (11 axiom-clean artifacts): MissingLineDefeater → ExactnessWithoutCoverability → CensusConditionalPin → CensusLowerBound → CensusExtremalFloor → TakeoverCountermodel → CosetSplittingFloor → SplittingLadder → SmoothLadderInstance → ExcessCensusLaw → GeneralGapCensusLaw.

=== COMMENT 103 | lalalune | 2026-06-11T13:58:36Z ===
## Round 6(a): orbit-weight table — the enriched collision orbits over μ₈ are the ANTIPODAL configurations

Symmetric-stack-family probe ((8,3) t=4, p=73, 400 fully-random stacks — under which the landed equivariance engine *guarantees* exact orbit-constancy of pair-collision probabilities; 178 dihedral orbits of witness-set pairs):

**Smooth μ₈ top orbits** (baseline 5.5/pair): the complementary pair [(0,1,2,7),(3,4,5,6)] (orbit size 4, mean 7.5); the antipodally-closed pair [(0,3,4,7),(1,2,5,6)] — both members fixed by i↦i+4, orbit size 2, mean 7.0; and three further antipodally-structured size-8 orbits at 6.9–7.0. **The enrichment ranking follows the symmetry ranking exactly** — the most dihedral-symmetric pair configurations collide most, which is the Lam–Leung/antipodal mechanism in yet another guise (third independent appearance in this campaign: KKH26 subset-sum collisions, char-0 collision law, now interpolation-scalar collisions).

Honest caveats: enrichment factors are modest (1.2–1.4×) and per-orbit means sit at ≈ +1.8σ with this sample — *suggestive, not conclusive on its own*; the confidence comes from the structural match with the prediction. The 'generic' comparison domain (1..8) is itself an AP with its own (different, weaker-cliqued) enrichment.

**Round 6(b) — the exact route (queued):** the collision condition γ_S = γ_S′ is a polynomial identity in the stack variables; for each orbit the collision variety's q-point count gives the *exact* enrichment weight, no sampling. For the antipodally-closed pairs over μ₈ the variety inherits the i↦i+4 symmetry — the factorization the probe is detecting. Computing these point-counts symbolically (they are pencil-census/character-sum objects of the landed N3 machinery) turns the prize-scale collision census into exact orbit arithmetic — the round-7 formalization target.

=== COMMENT 104 | lalalune | 2026-06-11T14:01:22Z ===
## THE MONOMIAL-DOMINATION PIN (v3) LANDED (`MonomialDominationPin.lean`, axiom-clean, on main) — the corrected conditional δ* answer, one named surface from closed

The capstone of my lane's arc: the conditional pin rebuilt on the surface that **survives both red-team kills by construction**.

1. **`monomialEps`** — the MCA sup restricted to monomial-pair stacks `(x^s, x^t)`, exponents < n (lossless on μ_n by x^n = 1): a finite family, every member's bad-scalar set characterized exactly by the gap census law. `monomialEps_le_epsMCA`: it is always a lower bound — the conjectural content is *only* the reverse domination.
2. **`MonomialDomination`** — the campaign's single named open hypothesis after this arc: above the crossing agreement, `ε_mca ≤ monomialEps`. Falsifier: a non-monomial stack beating every monomial pair at some grid radius. Support: exhaustive at (5,4,2), exact-profile at (12,6), maximizer scans at (16,4)/(16,8) — every measured maximizer ever found IS a monomial pair (incl. both countermodel witnesses).
3. **`mcaDeltaStar_eq_of_monomialCrossing`** — domination + census numerics + crossing witness ⟹ **δ\* = 1 − ac/n exactly**.
4. **`mcaDeltaStar_eq_of_monomial_ladder`** — the smooth-domain packaging: the crossing witness is **discharged by the hypothesis-free ladder floor** whenever ε\* < (n/g)/|F|. Remaining inputs: `MonomialDomination` + the finite numerics. Nothing else.

**The honest δ\*-statement after this session, in one sentence:** *for smooth-domain RS codes, δ\* equals the monomial-census crossing radius — a finite, law-governed, per-scale computation — conditional on exactly one named, probe-supported, falsifiable hypothesis (`MonomialDomination`), with the crossing's bad half and the entire lower staircase already theorems.*

Where the campaign goes from here (the two live attack surfaces): (a) prove or refute `MonomialDomination` — the natural route is the projective-equivariance + syndrome quotient (every stack's orbit meets a normal form; show normal forms are dominated by pairs), and the natural falsifier is a 3-term-stack scan at (16,4) past Johnson; (b) the monomial-census asymptotics at production scales — the punctured-band cofactor count, where the collision census, norm-divisibility spectrum, and Lam–Leung tower converge. Both have full probe + formal infrastructure in place.

