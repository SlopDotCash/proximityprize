# δ* (#444): on-BGK vs off-BGK — decisive synthesis (2026-06-16)

**Question.** Pin δ* (MCA = list-decoding threshold) for explicit smooth RS, domain
μ_n = order-n subgroup of F_p* (n = 2^μ, n | p−1, PROPER), prize p ≈ n·2^128
(β = log_n p ∈ [4,5], m = (p−1)/n = 2^128, budget q·ε* ≈ n, n ~ 2^30), window interior
`(1−√ρ, 1−ρ−Θ(1/log n))`. **Is the binding object the p-DEPENDENT under-determined char
sum (BGK/Paley wall), or the p-INDEPENDENT over-determined distinct-γ count D* with its own
growth law?**

This note is the honest synthesis of four propose→verify attacks (two AROUND-the-wall, two
WALL-IS-REAL), each landed as an axiom-clean Lean brick and cross-checked against in-tree
anchors. Honesty contract (CLAUDE.md §6) holds throughout: nothing below is claimed proven
that is not axiom-clean (`⊆ {propext, Classical.choice, Quot.sound}`, no `sorryAx`); the one
open object is named precisely and never silently discharged.

---

## (a) THE VERDICT — the prize is ON-BGK. The wall is real.

**The window-interior δ* is governed by the p-DEPENDENT character-sum (BGK/Paley) wall, not
by a p-independent combinatorial count.** Both off-BGK horns were attacked head-on and both
collapse — but for *different* reasons, and reconciling them is the whole content of the
verdict.

### Reconciling line 401 / line 4338 / line 451 definitively

The three contested comments are each *locally correct about a different object*; the apparent
contradiction dissolves once you separate "what the over-determined count IS" from "what it
DOES to the budget" from "where the crossing lands."

- **l4338 is right about the count's nature, wrong about its consequence.** The
  over-determined distinct-γ union count D* *is* p-independent **as a char-0 census** — I
  independently reproduced D*(16,3) = 97 identical across four primes spanning
  786433…3.2·10⁹, and the orbit identity D* = (n/d)·O_P + [γ=0] digit-for-digit. So "D* is a
  combinatorial orbit count, not the BGK char sum" is an honest fact. But it does NOT follow
  that δ* routes through it off-BGK.

- **l451 is right that the count exceeds budget.** The p-independent over-determined census is
  *super-budget* strictly inside the window. PROVEN at the r=3 band bottom:
  D*(n,3) = n·C(n/4,2) + 1 = Θ(n³), crossing budget n already at the shallowest band and
  overshooting by the unbounded factor O_P(n,3) = C(n/4,2) → ∞ (≈ 3.6·10¹⁶ at n = 2³⁰). So the
  over-determined union does NOT fit the budget and cannot, by itself, close the prize.

- **l401 is right that the over-determined / worst-direction incidence collapses to Johnson.**
  Because the over-determined census overshoots budget everywhere inside the window, it can
  pin δ* only at the *window edge* δ = 1−√ρ (Johnson). The window-INTERIOR value therefore
  cannot be supplied by the over-determined contribution; it must come from the
  under-determined (s−k ≤ 1) contribution — and that contribution *is* the char sum
  M(n) ≤ C√(n log m). The wall is real.

**Net mechanism (the reconciliation).** The binding count is the in-tree
`boundary_slice_ladder_badSet_card_eq` value `#{∑_{i∈S} dom i : |S| = k+1}` — and the sum is
taken **in F = F_p**. Two distinct cyclotomic (char-0) subset sums collide in F_p exactly when
their difference is divisible by p. So the *actual* binding object factors as

> binding count = (char-0 distinct-subset-sum count) − (mod-p collision defect).

The char-0 part is super-budget inside the window (census 464, 4512, … ≫ n). The ONLY way
δ* can sit in the window interior is for the **mod-p collision defect** to drag the count down
to ≤ budget n — and that defect is an additive-coincidence / character-sum cancellation
quantity: it **is** the BGK/Paley wall. This is confirmed empirically: the binding count is
p-DEPENDENT at small primes (n=16 incidence 32/48/16 across q = 97/193/257; 48 exceeds the
char-0 ceiling 16 = char-p energy inflation at an anomalous prime), settling to the char-0
value only at clean/large primes. So the over-determined census over-shoots, the binding is
the p-dependent defect, and the **off-BGK route is CLOSED, not alive.**

**mStarLaw reconciliation.** m* = s−k is the LINEAR object (≈ n/4 at the Johnson edge down to
~n/log n near capacity), p-independent, over-determined — and *because* it stays ≥ 2 through
the window it is exactly the over-determined contribution that l401 collapses to Johnson. The
"log₂ n + O(1)" reading is a DIFFERENT object: the ω-tower descent depth log₂(m*) (equivalently
the moment depth r* ~ log m), not m* itself. The two laws measure different things; neither
makes the over-determined count binding in the interior.

**Confidence: medium.** The r=3 band-bottom collapse is Lean-proven; the window-interior
extension rests on the growth law D* = Θ(n^r) (probe-supported, not Lean-proven for general r)
and on the subset-sum-defect = char-sum-cancellation identification (proven in structure,
measured in magnitude). The verdict direction (wall-is-real) is robust because the collapse
*strengthens* with depth: if the shallowest band already overshoots budget by C(n/4,2)→∞, the
deeper window bands overshoot astronomically.

---

## (b) Axiom-clean bricks that landed (exact theorem names)

All four files verified axiom-clean (`#print axioms` ⊆ {propext, Classical.choice, Quot.sound},
no sorryAx); D*-growth and the two floor files confirmed by real `lake build` EXIT 0.

**1. D* growth law** — `Frontier/_DstarGrowthLaw.lean`
(`namespace ArkLib.ProximityGap.DstarGrowthLaw`):
- `dStar3_eq_n_mul_orbit` : D*(n,3) = 4g·C(g,2) + 1 = n·C(n/4,2) + 1 (orbit identity, n = 4g).
- `dStar3_gt_budget` : budget n < D*(n,3) for every n = 4g ≥ 16 (budget crossed at band bottom).
- `orbit_count_unbounded` : O_P(n,3) = C(n/4,2) is unbounded — excess factor Θ(n²), not constant.
- `dStar3_ge_budget_mul_orbit`, `offBGK_overdet_caps_below_window` (packaged verdict).
- Numerical rungs `rung_n16/32/64` (97/897/7681) match in-tree `DeepBandR3Bound`.
Wires to the proven in-tree r=3 closed form (`DeepBandR3Bound.deepBandBadCount`). Committed.

**2. O_P single-orbit refutation** — `Frontier/_OPSingleOrbit.lean`:
- `OP_single_orbit_refuted` : O_P ≥ 3 > 1 at n=32 (m=16) via three genuine binding configs
  {0,1,2,9}, {0,2,4,10}, {0,3,6,11} (each e₂=0, e₁≠0, full orbit size 16, distinct shift orbits).
- Supporting `decide` lemmas `base{1,2,3}_e2vanish/_e1nz/_orbit_full`, `bases_distinct_orbits`.
- Refutes the off-BGK far-horn closure hope O_P=1: exact growth law O_P = n/8−1 (= m/4−1), so
  O_P=1 holds ONLY at n=16. Binding #bad = (m/4−1)·m + 1 ~ n²/8 blows budget n for all n ≥ 32.
  Scratch (`_`-prefixed countermodel); not committed.

**3. Floor lower bound (resonance)** — `Frontier/FloorResonanceLowerBound.lean`
(`namespace …FloorResonance`) + `Frontier/FloorResonanceEnergyBridge.lean`
(`namespace …FloorResonanceBridge`):
- Engine (genuine): `resonator_lower_bound`, `resonator_ratio_le_max`, `resonator_ratio_ge_min`
  (resonance sandwich min ≤ ratio ≤ max), `flat_resonator_eq_mean`, `moment_resonator_numerator`
  (moment resonator R = a^{k−1} ⟹ ratio = P_k/P_{k−1}).
- Bridge (genuine, load-bearing): `worst_period_sq_ge_of_energyRatioGrowth` —
  `EnergyRatioGrowth ψ G r T` ⟹ ∃ b≠0, T ≤ ‖η_b‖²; chains the in-tree axiom-clean
  `WorstPeriodMomentRatioLower.exists_period_sq_ge_moment_ratio`. `energyRatioGrowth_fails_of_no_floor`
  (contrapositive). Committed 07eabb4ec.
- CAVEAT (honesty): three lemmas in FloorResonanceLowerBound are thin packaging tautologies
  with no content — `structureBlind_resonator_le_mean := hblind` (P→P), `beats_mean_implies_correlated
  := not_le.mpr hbeat`, `floor_reduces_to_energy_ratio` (flat_resonator_eq_mean + passed
  hypothesis). They inflate the theorem count; the GCD/Bondarenko-Seip no-go CONTENT lives only
  in the probe (`probe_floor_resonance_gcd.py`), not in a theorem. NOT closure-laundering (no
  theorem claims to discharge the open core), but the prose overstates what the Lean proves.

**4. Equivalence pin** — `Frontier/PrizeEquivalencePin.lean`
(`namespace …PrizeEquivalencePin`):
- KEEP (genuine, axiom-clean, reusable reduction skeleton):
  - `mcaThreshold_eq_iff` — airtight two-sided pin over the in-tree governing law
    mcaDeltaStar = sSup{good radii}: for δ₀ ∈ (0,1), threshold = δ₀ IFF the binding count
    brackets budget exactly at δ₀ (strict-left/le-right csSup bracket).
  - `prizeFloor_eq_value_iff_bindingCount_brackets` — same, prize-named (price = count/q,
    budget = q·ε*).
  - `no_second_order_route` / `moment_certificate_impossible` — method-necessity companion
    (r_opt = log₂ m = 128 > r_max = 2β = 10): no order-r moment/L² certificate reaches the floor.
  - `prizeFloor_from_growthLaw` — reduction assembled from the single named open `Prop`.
- DISCARD (definitional-fiat laundering of the one contested point — see (a)):
  `off_BGK_route`, `pDependent_neq_pIndependent`, `Dstar_pIndependent`. These take
  `Dstar : ℕ → ℕ` (a function of n ONLY) and ENCODE p-independence as `(fun n _ => Dstar n)`,
  then observe `Dstar_pIndependent := fun _ _ _ => rfl` — they ASSUME the p-independence they
  purport to establish. The actual binding object (boundary_slice_ladder_badSet_card_eq, sums
  in F_p) is p-DEPENDENT; the attacker's own probes (n=16: 32/48/16) refute the narrative.

---

## (c) Was the floor lower bound M(n) ≥ c√(n log m) PROVEN? — NO. Sharpened + reduced only.

**Not two-sided-proven.** What stands:
- PROVEN unconditionally (in-tree, axiom-clean): the Parseval/4th-moment floor M(n) ≥ √n
  (`WorstPeriodLowerBound.exists_period_sq_ge`, `GaussPeriodParsevalFloor`), and in the clean
  k=2 regime M² /n → 3 i.e. M ≥ √(3n) (a constant gain over Parseval, NO log m).
- NUMERICALLY REAL but UNPROVEN: M ≥ c√(n log m). Sweep of m at fixed n shows M²/n vs log m has
  positive slope 1.1–1.95 and the band M/√(n log m) ∈ [1.0,1.6] is non-decaying
  (`probe_floor_resonance.py`). This is *measured*, not proven.
- REDUCED (the new contribution): the resonance method's only route past the Parseval mean is
  the moment resonator, whose certified bound is EXACTLY the consecutive energy ratio
  P_k/P_{k−1} = (qE_k − n^{2k})/(qE_{k−1} − n^{2(k−1)}). Reaching n·log m forces depth k ~ log m,
  i.e. a LOWER bound on E_{log m}(μ_n) — the SAME Bourgain–Shkredov additive-energy wall (W4)
  that gates the UPPER bound. Floor and moment-method upper bound are DUAL on E_{log m}. The
  structure-blind GCD/Bondarenko–Seip shortcut is measured to fail (single additive char sum,
  no multiplicative correlation in the coset index), so resonance gives NO shortcut around the
  wall — it re-derives the wall from below.

So: the floor lower bound was **reduced to the energy-ratio growth law, not proven**. The wall
is two-sided in structure (both directions live on E_{log m}) but only one-sidedly *proven*; the
matching lower factor √(log m) remains measured.

---

## (d) The single sharpest open statement — on the face the prize lives

Everything reduces to ONE object. Naming it precisely:

> **THE OPEN CORE.** Let `D*_p(δ) = #{∑_{i∈S} dom i (in F_p) : |S| = k+1}` be the binding
> far-line subset-sum count at radius δ (in-tree `boundary_slice_ladder_badSet_card_eq`), with
> k = ⌊(1−δ)n⌋. Its char-0 part is super-budget through the window interior. The prize floor
> δ* sits in the interior `(1−√ρ, 1−ρ−Θ(1/log n))` IFF the **mod-p collision defect**
> `Δ_p(δ) := (char-0 distinct count) − D*_p(δ)` drags D*_p(δ) down to ≤ budget n at the
> interior crossing point. That defect is the additive-energy / character-sum cancellation
> quantity, equivalently the lower bound
>
> > **`E_r(μ_n) / E_{r−1}(μ_n) ≥ c·r` at r ≈ log m`**  (`EnergyRatioGrowth ψ μ_n r T`,
> > `Frontier/FloorResonanceEnergyBridge.lean`),
>
> i.e. the char-p transfer to r ≈ ln q of the Lam–Leung char-0 energy bound
> `E_r(μ_n) ≤ (2r−1)‼·n^r` — the SAME single object as faces 3↔4 of the §3.5 open core. It is
> PROVEN in char-0 (Lam–Leung) and for n < 2 log q / log log q ≈ 40 (norm gate
> q > (2r)^{n/2}); OPEN for the prize n = 2³⁰ (whether short ≤ 2 ln q-term ±1 relations of
> 2^μ-th roots vanish mod the prize prime).

This is the BGK/Paley √-cancellation wall, restated as a clean two-sided dual: it lower-bounds
the worst Gauss period (the floor, via `worst_period_sq_ge_of_energyRatioGrowth`) and
upper-bounds it (the deep-moment route), and it equals the mod-p subset-sum collision defect
that decides the window-interior δ*. Method-necessity is proven against it from below
(`no_second_order_route`: r_opt = 128 ≫ r_max = 10, no L²/moment shortcut) and in-tree
(`MomentMethodPrizeDepthNoGo`). **No prize closure. The wall is the single remaining open
object, on the ON-BGK (char-p, under-determined) face.**

---

## Honest caveats (do not overclaim downstream)

1. `moment_ladder_exceeds_prize` / `_MomentLadderExceedsPrize` cited in the PrizeEquivalencePin
   prose exists ONLY as a scratch file + docs, NOT as a landed `.lean` theorem. The landed
   method-necessity content is `PrizeEquivalencePin.no_second_order_route` and in-tree
   `MomentMethodPrizeDepthNoGo`. Citation imprecision; does not affect the lower-direction Lean.
2. The PrizeEquivalencePin `off_BGK_route` narrative is definitional-fiat and is DISCARDED; the
   `mcaThreshold_eq_iff` / `prizeFloor_*` / `no_second_order_route` skeleton is kept as a genuine
   reusable reduction.
3. The window interior is EMPTY for n ≤ 64 (Johnson and capacity collide; C(256,128) ~ 10⁷⁵
   undecidable by enumeration), so the interior extension is structural/probe-supported, not
   enumerated. The r=3 band-bottom collapse is the only fully Lean-proven slice.

## Artifacts (absolute paths)

- `C:/Users/Administrator/arklib/ArkLib/Data/CodingTheory/ProximityGap/Frontier/_DstarGrowthLaw.lean`
- `C:/Users/Administrator/arklib/ArkLib/Data/CodingTheory/ProximityGap/Frontier/_OPSingleOrbit.lean`
- `C:/Users/Administrator/arklib/ArkLib/Data/CodingTheory/ProximityGap/Frontier/FloorResonanceLowerBound.lean`
- `C:/Users/Administrator/arklib/ArkLib/Data/CodingTheory/ProximityGap/Frontier/FloorResonanceEnergyBridge.lean`
- `C:/Users/Administrator/arklib/ArkLib/Data/CodingTheory/ProximityGap/Frontier/PrizeEquivalencePin.lean`
- In-tree anchors: `LadderSchurReduction.boundary_slice_ladder_badSet_card_eq`,
  `WorstPeriodMomentRatioLower.exists_period_sq_ge_moment_ratio`,
  `DeepBandR3Bound.deepBandBadCount`, `WorstPeriodLowerBound.exists_period_sq_ge`,
  `MomentMethodPrizeDepthNoGo`.
- Probes: `_probe_444_dstar_growth.py`, `_probe_444_dstar_polestructure.py`,
  `_probe_444_OP_e2vanish_tower.py`, `_probe_444_OP_field_descent.py`,
  `probe_floor_resonance{,_construction,_gcd,_dual}.py`,
  `_probe_444_pindep_defect.py`, `_probe_444_prize_equiv_binding.py`,
  `probe_monomial_incidence_qindependence.py`.
