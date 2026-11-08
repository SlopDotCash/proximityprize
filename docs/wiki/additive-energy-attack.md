# The additive-energy attack on the Proximity Prize (#232)

This page documents the machine-checked ingredients of the additive-energy route to the Ethereum
Proximity Prize (issue #232, [ABF26]): Gauss-sum moment identities, the subgroup-tower descent, and
the exact Sidon-mod-negation energy formula for the **smooth `2^k`-multiplicative subgroup**. It is a
historical route map. It does **not** reduce the prize to one energy hypothesis: the links marked
*missing* below have no in-tree theorem (see [What a second-energy bound does not
give](#what-a-second-energy-bound-does-not-give)).

> **Status correction (2026-10-28 audit, T48; consolidates PG-006, PG-064, PG-070, PG-113, PG-144).**
> An earlier version of this page said the prize was reduced to a single second-energy /
> Sidon-mod-negation input and that the supporting chain was "now complete". That is withdrawn. A
> second-energy (fourth-moment) bound, even the exact minimal value `E(G) = 3|G|(|G|−1)`, does not
> supply the deep-moment or worst-case MCA bound the prize needs, and the bridge from spectral bounds
> to worst-case MCA bad-scalar counts is itself missing. The proved lemmas listed below remain
> correct, including the representation lemma `additiveEnergy_le_three_of_repTwo`, whose hypothesis
> (`repCount G t ≤ 2` for `t ≠ 0`) correctly excludes the zero fiber. These are stale status
> descriptions of a conditional route, not failed Lean proofs.

> Scope reminder: the prize itself is **open research** and **not closeable by this repo** (see the
> issue body and `docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md`). Everything
> below is honest formalization of individual steps; it is not a complete reduction.

## The route (proved steps are axiom-clean: `propext, Classical.choice, Quot.sound`)

The arrows are a route map, not a chain of proved implications.

```
prize (pin δ* in (1−√ρ, 1−ρ))
  → MCA / ε_mca bad-event count                    (#141 surfaces; conditional)
  → subset-sum concentration of the smooth subgroup G ⊆ F_q^×
        [missing: census laws cover specific stack families; worst-case extremality is open]
  → coordinate descent down the 2-power subgroup tower
  → Gauss-sum moments  (proved: ∑_b ‖η_b‖⁴ = q · E(G), all b including b = 0)
        [missing: the descent needs a worst-case period bound or deep moments of order
         r ≈ log q with the DC term n^(2r) subtracted; the 4th moment does not give either]
  → additive energy  E(G) = #{(a,b,c,d) ∈ G⁴ : a+b = c+d}
  → [OPEN, and not sufficient] is E(G) minimal (char-0 value) for the explicit 2^k-subgroup?
```

## Where each step lives

| Step | File(s) | Key result |
|---|---|---|
| Subgroup-tower descent (general `d`) | `SubgroupPowerHalvingGeneral` | `image_pow_eq_quotient`: `(μ_{dm}).image(·^d) = μ_m` (index-`d` subgroup), any `d,m≥1`. Special cases: `SubgroupSquaresHalvingRecursion` (d=2), `SubgroupQuarticHalvingRecursion` (d=4). |
| Coordinate descent (Finset model) | `SubsetSumQuarticDescent` (d=4), `SubsetSumSquaringBijection` (d=2) | surviving symmetric coordinate `∑x^d` reduces to a subset-sum over the `d`-th-power image. |
| Gauss-sum moments | `SubgroupGaussSum{Second,Fourth}Moment` | `subgroup_gaussSum_fourthMoment : ∑_b ‖η_b‖⁴ = q · addEnergy G`; heavy-frequency / no-go's in `ListSizeMoments`, `MomentCollisionTower`, `JohnsonFourthMomentNoGo`. |
| Energy bound from representations | `AdditiveEnergyRepBound` | `additiveEnergy_le_three_of_repTwo : repCount ≤ 2 ⟹ E ≤ 3|G|²`. `repCount ≤ 2` is **false** over small `F_q` (`SubgroupRepCountFiniteFieldCounterexample`). |
| **Sharp energy (equality)** | `AdditiveEnergySidonModNeg` | `additiveEnergy_eq_of_sidonModNeg : E(G) = 3|G|² − 3|G| = 3|G|(|G|−1)` for any **Sidon-mod-negation** set (negation-closed; only trivial/zero-sum additive coincidences). Sharpens the `≤ 3|G|²` bound by exactly `3|G|`. |
| Definition bridge | `AdditiveEnergyBridge` | `additiveEnergy_eq_addEnergy`: the rep-count `additiveEnergy` (above) equals the quadruple-count `SubgroupGaussSumFourthMoment.addEnergy`; hence `addEnergy = 3|G|(|G|−1)` for Sidon-mod-neg, feeding the fourth-moment identity. |
| Concrete data / validation | `SubgroupAdditiveEnergyTowerF17`, `SubgroupAdditiveEnergyFermat257`, `SubgroupAdditiveEnergyFermat65537`, `AdditiveEnergyFullGroupClosedForm`, `SidonModNegValidationFermat257` | exact `decide` energies; general `E(F_p^×) = (p−1)²+(p−1)(p−2)²`; end-to-end theorem validation; `SidonModNeg` threshold located. |

## Two empirical facts (finite checks; the order-8 energies are verified by `decide`)

1. **Anti-concentration in the checked instances.** For a *small* subgroup in a *large* field
   (`|G| ≪ q`), the checked instances have the characteristic-0 energy: `E(order-8) = 168 = 3·8·7`
   for `q ∈ {257, 65537}`. These are finite checks, not a `q`-independence theorem. For fixed `n`
   only primes dividing finitely many nonzero cyclotomic norms can add coincidences, so the char-0
   value holds above an `n`-dependent threshold. That threshold is not `q ~ |G|`: the proper
   subgroup `μ₃₂ ⊆ F₃₂₉₉₃` (`p > n³`) has `E = 3744 > 2976 = 3n² − 3n` (PG-113; exact pair-sum
   count). So the `repCount = 3 > 2` failures are not only a small-`q` artifact.
2. **The crossover is field-arithmetic-dependent — no clean law in `q`.** The order at which
   `E > 3|G|²` first occurs is `~8, ~16, ~32` for `q = 2^4+1, 2^8+1, 2^16+1`; across 15 fields it
   fits neither `√q` nor `2·log₂q`. (A `√q` claim was posted and **retracted** — see #232 comments;
   recorded here so it is not re-attempted.)

## The energy question (an open input, not the prize root)

Whether `SidonModNeg` holds (equivalently, whether `E(G) = 3|G|(|G|−1)`, the minimal value) for the
**explicit** smooth `2^k`-subgroup as `|G|, q → ∞` is a field-arithmetic-dependent sum-product
question of Weil / Heath-Brown–Konyagin type. It is decidable per concrete instance and open in the
asymptotic regime. A positive answer would **not** by itself pin `δ*`.

## What a second-energy bound does not give

- **No worst-case period bound.** The fourth moment is an average. Since `η_b` is constant on the
  cosets of `G`, the nonzero identity `∑_{b≠0} ‖η_b‖⁴ = q·E(G) − n⁴` gives at best
  `max_{b≠0} ‖η_b‖ ≤ ((q·E(G) − n⁴)/n)^{1/4} ≈ (3qn)^{1/4}` at the minimal energy. That is trivial
  (`≥ n`) once `q ≥ n³/3`, and far above the square-root target scale in the prize regime.
- **No deep-moment bound.** The square-root scale needs moments of growing order `r ≈ log q`. The
  principal (DC) term forces `E_r ≥ n^(2r)/q`, and at the intended growing-depth prize parameters
  this exceeds the Wick value `(2r−1)!!·n^r`, so a raw-energy Wick bound is false there. (This is a
  statement about that regime, not about every fixed finite `n, q`; `n = 1` is an immediate
  exception.) The usable object is the DC-subtracted nonzero moment
  `∑_{b≠0} ‖η_b‖^(2r) = q·E_r − n^(2r)`. Because `G = −G` makes every period real, renaming the even
  moment as a "signed energy" does not remove that term (PG-144). A second-energy value does not
  imply bounds on `E_r` for `r ≥ 3`.
- **No MCA bridge.** Even a square-root bound on every nonzero period would still need an in-tree
  bridge to the worst-case MCA bad-scalar count over all stacks. The census laws cover specific stack
  families, and worst-case extremality is a separate open surface (PG-006, PG-070; see also
  [`census-programme.md`](census-programme.md)).
- **Conditional consumers stay conditional.** `WeilRegimeClosure` and the other energy-to-list
  consumers take their energy estimate and extra inequalities as hypotheses. They prove neither
  the estimate nor a `δ*` statement.

## Lessons for future agents

- The proximity frontier is driven by a fast multi-agent swarm pushing to `main` (~1 file/min). Solo
  value is reliably **(a) fix fresh build breakage** and **(b) land the brick one step past the
  swarm**, then verify against `upstream/main` *before* building — a `git ls-tree`/grep check is not
  enough (the swarm sometimes pushes red commits).
- Apply the apophenia gate hard: assert a scaling law only after many witnesses (the `√q` retraction).
- `decide` over `∀ a ∈ G` for `G : Finset (ZMod p)` blows up to `p^k` if the def is unfolded into a
  Fintype quantifier; use `Finset.decidableBAll` (keep `G` a Finset) or `fin_cases`.

## References
- [ABF26] Arnon, Boneh, Fenzi, *Open Problems in List Decoding and Correlated Agreement*, ePrint 2026/680.
- Issue #232; `docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md`.
