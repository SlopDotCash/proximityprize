# Rate-quarter predecessor: small-pool assembly — Z-relative Johnson, pinned ledger, dichotomy glue, and the terminal lane retrospective

## Status

Final file of the P1 charge arc (session 2026-07-10).  Lands the staged
upgrade of the small-pool branch: the `Z`-relative Johnson machinery is now
kernel theorems, every number of the closure ledger is kernel-pinned, and the
predecessor pin's open content is packaged as exactly
`SmallPoolClosure ∧ StallResidual` via a proved glue theorem.

Formal kernel (pg-iterate ✅ OK 15s, 7 audited theorems, all on
`[propext, Classical.choice, Quot.sound]`, no `sorry`/`axiom`):

```text
ArkLib/Data/CodingTheory/ProximityGap/Frontier/_P1RateQuarterSmallPoolAssembly.lean
```

## 1. Stage (a): `Z`-relative Johnson (new machinery)

* `card_attach_filter`: transport of subsets of an ambient `Finset` to its
  attached subtype preserves cardinalities.
* `johnson_core_rel`: the in-tree exact-diagonal `R15Bracket.johnson_core`,
  instantiated at the subtype `{x // x ∈ Z}` — the Johnson double count runs
  over `Z.card` instead of the whole domain.  This is the piece that makes the
  derecursion's small-pool branch countable at all (full-domain Johnson dies
  below `536870911`, while the boundary level `T − F₀ = 517776833` clears the
  `Z`-relative radius).
* `dirFamily_johnson_on_Dzero`: through-base pencil families, packed by their
  aligned regions inside `{D = 0}` (sink lemma + in-tree `< k` overlaps).

## 2. Stage (b): the pinned ledger

Ledger identity (probe-exact): each direction `w` contributes
`⌊F/(T−A_w)⌋ = #{m : T−A_w ≤ F/m}` riders, so

```text
#bad ≤ 1 + Σ_{m=1}^{F} L_Z(T − ⌊F/m⌋).
```

* `boundary_count_pinned`: at the worst pool (`|{D=0}| = 998723691`), the
  level-`517776833` direction count is `≤ 657668325` — the `m = 1` term,
  pinned by `657668326·378645484 = 249023141609739784 > 249023141355186198`.
* `ledger_histogram_le_N`: the exact histogram at `F₀`
  (`{657668325×1, 7×1, 5×1, 4×27, 3×(F₀−30)}`) sums to `882722755 ≤ N` —
  matching the greedy probe to the unit.
* `ledger_uniform_caps_le_N`: with the probe-swept uniform caps (valid for ALL
  `F ≤ F₀`: `m=2` term `≤ 7`, `m ≥ 3` terms `≤ 5`), the closed bound
  `1 + 657668325 + 7 + 5·(F₀−2) = 1032758988 ≤ N` still fits — the closure is
  robust, not knife-edge.

## 3. Stage (c): the dichotomy glue

* `SmallPoolClosure` (honest named Prop): bad families with SOME base scalar
  of pool `≤ F₀` respect the budget.  Everything numeric is discharged; what
  remains open in Lean is ONLY the marginal-partition wiring of the fiber
  ledger over the per-`m` Johnson caps, uniformly in `F ≤ F₀` — engineering of
  the `_P1RateQuarterLayerCakeBudget` kind.
* `predecessor_budget_of_smallPool_and_stall` (proved):
  `SmallPoolClosure ∧ StallResidual ⟹` every bad family has `G.card ≤ N`.
  The P1 predecessor pin's open content is now EXACTLY these two Props.

## 4. Terminal lane retrospective — the charge cone is complete

Six landed files, session 2026-07-10, all axiom-clean:

1. `_P1RateQuarterTwoCoverWindow` — the two-cover window REALIZED at literal
   P1 (cyclotomic Davenport triple, period-128 residue construction).
2. `_P1RateQuarterGlobalConsistencyCharge` — the global `D`-charge: heavy
   three-pencil over-budget CLOSED (`≤ 301989883 ≤ N`); the realized geometry
   carries no riders (geometric ≠ population realizability).
3. `_P1RateQuarterDChargeDerecursion` — the flow made precise; exact dichotomy
   boundary `F₀ = 75018133`; small pool closed (arithmetic), stall taxonomy
   with pool-code regimes.
4. `_P1RateQuarterMDSPoolSecondCharge` — the second charge instantiates
   literally, shrinks once, then the threshold collapses below `k − 1`:
   permanent double-stall; charge iteration terminal at depth 2.
5. This file — `Z`-relative Johnson, pinned ledger, dichotomy glue.

**Three branches**: heavy CLOSED (kernel); small-pool CLOSED at arithmetic
level (counting-glue = `SmallPoolClosure`); stall band = sub/beyond-Johnson
MDS agreement families.  **The stall band is the prize wall**: the P1 counting
cone provably converges to the same beyond-Johnson obstruction as the B-side
(BGK/Paley) — important meta-knowledge: no lane artifact, and no further
Johnson/charge/counting iteration can help.  Next genuinely new inputs:
beyond-Johnson list structure, or the structured-floor route
(`PredecessorStructuredFloorResidual`).

**Unchanged**: the operational bracket
`3/8 ≤ mcaDeltaStar ≤ 43/96 + 1/(3·2^30) < 1/2`.

## 5. Reusable engineering (this file)

* `(x : α)` ascriptions inside subtype-`filter` binders elaborate as a
  monadic `Finset` coercion (`do let a ← Z.attach; pure ↑a`) and silently
  change the set — use `x.1` projections, never ascriptions, when filtering
  `Z.attach`.
* `Finset.card_bij'` direction: prove `S.card = filter.card` with the subtype
  constructor as the forward map and `.symm` the result.
* Beta-unreduced lambda applications (`(fun i => …) i`) in `johnson_core`
  hypothesis goals block `rw` — open each subgoal with a `show` in the
  reduced form.
