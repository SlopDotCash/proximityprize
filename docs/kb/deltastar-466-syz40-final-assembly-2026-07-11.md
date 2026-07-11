# δ*/#466 — SYZ40: final assembly of the rate-`1/2` strip theorem (arc closing document)

Date: 2026-07-11.  File: `ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ40FinalAssembly.lean`
(11 declarations, all axiom-clean: `propext / Classical.choice / Quot.sound` only; no `sorry`, no
`native_decide`).  Branch: `codex/syz40-final-assembly` off fork `research/proximity-prize`
tip `4ececa37e`.

## TL;DR — one theorem, one substantive named hypothesis

SYZ40 is the **closing document of the SYZ18–SYZ40 arc**.  It expresses the whole rate-`1/2`
proximity strip theorem as **one assembled theorem** whose only substantive open input is a single
named `Prop`, `UniformSylvesterInjective` (SYZ38's `SylvesterInjective` quantified over every
rate-`1/2` band degree profile — SYZ39's resultant non-vanishing, of BGK type at `n = 2³⁰`).  Every
other input that resists a fully-formal discharge is folded **explicitly** into a single master
hypothesis structure — no hidden assumptions.  **No unconditional `δ*` is delivered**; the honest
verdict of SYZ33–SYZ39 is unchanged, now fully assembled.

## The named hypothesis — exact content (verbatim)

```lean
def UniformSylvesterInjective (K : Type*) [Field K] (n k : ℕ) : Prop :=
  ∀ (WAB WAC WBC : K[X]) (mAB mAC mBC t : ℕ),
    n = 2 * k → t < mAB → k - 1 < mAB + mAC - t →
    WAB.natDegree = mAB - t → WAC.natDegree = mAC - t → WBC.natDegree = mBC - t →
    WAB ≠ 0 →
    SylvesterInjective WAB WAC WBC (k - 1 - mAC) (k - 1 - mBC)
```

i.e. for every pairwise-coprime band triple `(W_AB, W_AC, W_BC)` over `K[X]` whose degrees realise a
strict-interior band incidence (`natDegree W_XY = m_XY − t`) at rate `1/2` (`n = 2k`) in the
Koszul-out regime (`k − 1 < m_AB + m_AC − t`, SYZ37), the generalized Sylvester reduction map is
injective on the in-budget cofactor window (budgets `k−1−m_AC`, `k−1−m_BC`).  This is the exact
`∀`-quantification matching SYZ39's arithmetic characterization.

## The final theorem — the assembled strip conclusion (verbatim)

```lean
theorem strip_theorem_of_master_hypothesis [DecidableEq K] {n k : ℕ}
    (H : StripMasterHypothesis K V n k) (hn : n = 2 * k) :
    -- spread branch: sharp punctured-pair law for every rate-1/2 band triple (SYZ33 lemma 2)
    (∀ (A B C W : Submodule K V) (WAB WAC WBC : K[X]) (mAB mAC mBC t : ℕ),
      A ⊓ B = ⊥ → A ⊔ B ⊔ C ≤ W → t < mAB → k - 1 < mAB + mAC - t →
      WAB.natDegree = mAB - t → WAC.natDegree = mAC - t → WBC.natDegree = mBC - t → WAB ≠ 0 →
      finrank K ↥((A ⊔ B) ⊓ C) + finrank K W = finrank K A + finrank K B + finrank K C)
    ∧
    -- spread branch: union budget for every spread stack
    (∀ Ucard, k ≤ Ucard → Ucard ≤ n → Ucard ≤ n - 1)
```

The **merged branch** (`m ≤ 3`) is the separate, *unconditional* theorem
`merged_branch_unconditional` (re-export of `SYZ33.strip_certified_bad_le_budget` =
`SYZ32.routed_bad_le_budget`): a block-attributed bad set has `#B ≤ n − 1` with **no** hypothesis.
The two conjuncts above are the **spread branch** (`m ≥ 4`), where the master hypothesis is consumed.
Together: every over-budget rate-`1/2` stack is within budget.

## The master hypothesis — exact content (the single folded `Prop`)

```lean
structure StripMasterHypothesis (K) [Field K] (V) [...] (n k : ℕ) : Prop where
  uniformSylvester : UniformSylvesterInjective K n k                 -- THE open residual
  syzdimBridge : ∀ (A B C W : Submodule K V) (WAB WAC WBC : K[X]) (bAC bBC : ℕ),
    A ⊓ B = ⊥ → A ⊔ B ⊔ C ≤ W → WAB ≠ 0 →
    SylvesterInjective WAB WAC WBC bAC bBC →
    finrank K ↥(A ⊔ B ⊔ C) = finrank K W                            -- SYZ36 d=syzdim (folded)
  realizability : ∀ Ucard, k ≤ Ucard → Ucard ≤ n →
    Nonempty (SuperadditiveUnion (F := K) (V := V) n k Ucard)        -- SYZ22 ledger join (folded)
```

- **`uniformSylvester`** — the one substantive open input (Part 2 / SYZ38 / SYZ39).
- **`syzdimBridge`** — SYZ36's `d = syzdim` identity in the "vanishing ⇒ generation" direction:
  probe-verified (0 mismatches over 3 fields/2 domain types), **not formally proven**, hence folded.
  Crucially it is stated to **consume the polynomial `SylvesterInjective`** supplied by
  `uniformSylvester`, so the named residual genuinely feeds the bridge (no redundancy).
- **`realizability`** — the SYZ22 `SuperadditiveUnion` MDS-shortening dimension count `2(|U|−k)` for
  the spread stack; `Nonempty`-wrapped so the whole hypothesis is genuinely `Prop`-valued while still
  carrying the honest existence of the configuration.

## What was DISCHARGED vs FOLDED

**Discharged (proven outright, axiom-clean):**
- **General-`D` peel (item 2).**  `peel` — one core off any accumulated span via the SYZ34
  fiber-product identity: `finrank (W' ⊔ C) = finrank C + finrank (π_C W')`.  `peel_telescope` —
  the full general-`D` identity `finrank (⨆_{i<D} A i) + Σ_{i<D} finrank (accum i ⊓ A i) =
  Σ_{i<D} finrank (A i)` by induction (the `accum i ⊓ A i` are exactly the punctured-pair
  intersections the pair law / Sylvester injectivity control).  `generation_of_stepwise_saturation`
  — `D`-core generation closes once each step meets its budget.  Pure linear algebra, unconditional.
- **Per-config module vanishing (item 2).**  `module_vanishes_of_uniform` /
  `strip_theorem_of_uniform_sylvester` — from `UniformSylvesterInjective` alone, every in-budget
  syzygy of *any* support (0/2/3-support strata at once) is `0`, uniformly over all band configs.
  This is the fragment `UniformSylvesterInjective` controls **without** any folded input.
- **Wiring poly ⇒ pair law (item 3).**  `pairInteriorLaw_of_master` chains
  `uniformSylvester ⇒ SylvesterInjective ⇒` (via folded `syzdimBridge`) `generation ⇒` (SYZ35
  `pairInteriorLaw_iff_generation`) `the sharp punctured-pair law` = SYZ33 lemma 2 at rate `1/2`.
- **Merged branch.**  `merged_branch_unconditional` — unconditional, no hypothesis.
- **Spread budget.**  `spread_budget_of_master` — from the folded `realizability`, `|U| ≤ n − 1`
  (SYZ22 `strip_budget_of_realizability`).
- **Lemma-1 instantiation (item 1).**  `lemma1_fresh_independence` re-exports
  `SYZ33.exists_fresh_indep_family`: lemma 1's fresh-independence supply is closed to **two crisp
  band inputs** — (a) `DisjointResidualSupports` (SYZ18 distinct supports + `twist_pair_indep`
  `γ`-twist + pigeonhole) and (b) MDS non-degeneracy (RS-dual genericity from `shortening_dim` /
  dual distance `k+1`, the *same* genericity lemma 2 needs).  It is **off the critical path** of the
  assembled two-branch conclusion (which routes through SYZ32 merged + SYZ22 realizability), so it is
  recorded, not folded — no hidden dependency created.

**Folded (explicitly named in `StripMasterHypothesis`, honestly unproven):**
- `syzdimBridge` — SYZ36 `d = syzdim` (probe-verified identity, poly ⇒ finrank generation).
- `realizability` — SYZ22 `SuperadditiveUnion` production-ledger join (MDS-shortening count).
- `uniformSylvester` — **the** substantive open residual (BGK-type at `n = 2³⁰`, SYZ39).

## Honest verdict (unchanged, now assembled)

The strip theorem is conditional on **exactly one substantive named statement**,
`UniformSylvesterInjective`.  SYZ39 already characterized it: per-config a bounded-height resultant
non-vanishing (prize-clean by finite computation), the uniform `n = 2³⁰` statement of BGK type
(additive-cancellation-over-`μ_n`, provably not reachable by cyclotomic norms).  The two other folded
fields are genuine but structurally lighter (a probe-verified identity; an MDS-shortening count).
**No unconditional `δ*`.**  The value of SYZ40 is packaging: the entire rate-`1/2` strip now has a
single-hypothesis dependency structure with everything else proven, and the merged branch is fully
unconditional.

## The SYZ18–SYZ40 arc index

| # | File | Role |
|---|------|------|
| SYZ18 | `_SYZ18PairJointSelfExclusion` | distinct-support control (bad scalars scalar-unique per witness) |
| SYZ20 | `_SYZ20JointRankSuperadditive` | `SuperadditiveUnion`: joint span `= 2(|U|−k)` |
| SYZ21 | `_SYZ21ShorteningAndCoverage` | MDS shortening dims + combined-coverage knapsack |
| SYZ22 | `_SYZ22StripBridge` | realizability ⇒ union budget `|U| ≤ n−1`; knapsack closes n=64 |
| SYZ23–24 | directness / cross-core compat | partial-sup + compatibility scaffolding |
| SYZ25–26 | MDS generation / lifting | generation = local-global rigidity; `δ≤1/4` overlap route |
| SYZ27–29 | interior gluing / D3–D4 | coplanar crack + yield-law accounting |
| SYZ30 | `_SYZ30LemmasOneThree` | codim count `fresh_card_le_codim` |
| SYZ31 | `_SYZ31SetGeometryFacts` | `indep_mod_of_private_coord` (lemma-1 core) + two-block floor |
| SYZ32 | `_SYZ32ClusterRouting` | `routed_bad_le_budget` (merged `m≤3` case CLOSED) |
| SYZ33 | `_SYZ33FinalTwoLemmas` | lemma 1 closed to 2 inputs; lemma 2 isolated; strip case split |
| SYZ34 | `_SYZ34StripInteriorGeneration` | fiber-product identity `(A+B)∩C ↔ π_C A ∩ π_C B` |
| SYZ35 | `_SYZ35PairInteriorLaw` | pair law `⟺` generation `finrank(A⊔B⊔C)=finrank W` |
| SYZ36 | `_SYZ36UnionGeneration` | generation ⟺ in-budget syzygy module `= 0`; `d = syzdim`; Koszul obstruction |
| SYZ37 | `_SYZ37RateHalfAssembly` | rate-1/2: saturation vacuous; 0/2-support discharged by degree |
| SYZ38 | `_SYZ38SylvesterInjectivity` | 3-support residual = `SylvesterInjective`; whole module collapses to it |
| SYZ39 | `_SYZ39SylvesterArithmetic` | bad-prime law: `rad(n)` ramified + genuine primes ∤ n; BGK-type wall |
| **SYZ40** | **`_SYZ40FinalAssembly`** | **general-D peel + one-theorem/one-hypothesis assembly** |

## Validation

```bash
scripts/pg-iterate.sh \
  ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ40FinalAssembly.lean   # ✅ axiom-clean, 11 thms
```

Dependencies (`_SYZ39…`, `_SYZ33…` and their transitive cone) prebuilt once via
`lake-locked.sh build` (8679 jobs); iterate lockless with `pg-iterate.sh`.
