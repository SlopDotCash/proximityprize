# SYZ41 — the `d = syzdim` bridge, proven concretely (2026-07-11)

Issue #466 (proximity strip, rate-`1/2`). File:
`ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ41SyzdimBridge.lean`.

## What this removes

SYZ40's `StripMasterHypothesis` had **three** folded fields:
`uniformSylvester`, `syzdimBridge`, `realizability`. The middle one, `syzdimBridge`, was the
SYZ36 `d = syzdim` identity ("in-budget syzygy module vanishes ⇒ the cores generate the union
shortening"), carried as **probe-verified, not formally proven**. As literally stated it also
quantified over **arbitrary** abstract subspaces `A,B,C,W` with *no formal link* to the polynomial
data `(W_AB,W_AC,W_BC)` — an ill-posed catch-all that can never be discharged (take `W` strictly
larger than `A⊔B⊔C` and any vacuously-injective triple: the conclusion is false), because it
silently bundled the whole SYZ25/SYZ34 subspace⟷cochain *dictionary* together with the syzygy-space
logic.

SYZ41 proves the **syzygy-space logic** fully and axiom-clean at the concrete univariate-cochain
level (where it is well posed), from pieces already in tree (SYZ36 `reduce_by_VT` / `cocycle_identity`
/ `vanish_cofactor_lt`; SYZ38 `module_vanishes_of_sylvester_injective`). The result: a strengthened
**two-field** master hypothesis `StripMasterHypothesis'` with `syzdimBridge` **removed**.

## The concrete bridge (proven, axiom-clean)

A deficiency element (function locally `deg<k` on each core, not globally polynomial) is recorded by
its three pairwise mismatches `q_AB,q_AC,q_BC`, a cocycle (`q_AB − q_AC + q_BC = 0`). Each `q_XY`
factors through the SYZ36 reduction `q_XY = V_T · W_XY · r_XY` with in-budget `deg r_XY`. The map
`(q_·) ↦ (r_·)` is `K`-linear, lands in the in-budget syzygy space, and is injective on the
non-glued part (nonzero mismatch ⇒ nonzero reduced component). Hence **deficiency ≤ syzdim**, so
**syzdim = 0 ⇒ deficiency 0** — the direction SYZ40 consumes.

Verbatim key theorem:

```
theorem rigidity_of_module_vanishes
    (VT WAB WAC WBC rAB rAC rBC qAB qAC qBC : K[X]) (bAC bBC : ℕ)
    (hVT : VT ≠ 0) (hWAB : WAB ≠ 0)
    (hfAB : qAB = VT * WAB * rAB) (hfAC : qAC = VT * WAC * rAC) (hfBC : qBC = VT * WBC * rBC)
    (hcocycle : qAB - qAC + qBC = 0)
    (hbAC : rAC ≠ 0 → rAC.natDegree ≤ bAC)
    (hbBC : rBC ≠ 0 → rBC.natDegree ≤ bBC)
    (hInj : SYZ38.SylvesterInjective WAB WAC WBC bAC bBC) :
    qAB = 0 ∧ qAC = 0 ∧ qBC = 0
```

Chain: `reduced_is_syzygy` (cancel `V_T` via SYZ36 `reduce_by_VT`) ⇒
`SYZ38.module_vanishes_of_sylvester_injective` (`r_· = 0`) ⇒ each `q_XY = V_T·W_XY·r_XY = 0`.
`generation_of_module_vanishes` is the `∀`-quantified packaging (the form the bridge needs).
`factor_ne_zero` + `nontrivial_reduced_of_nontrivial_cocycle` give the injectivity/kernel
("deficiency ≤ syzdim") step (`q ≠ 0 ⇒ r ≠ 0`, since `q = V_T·W·r`).

## The strengthened master hypothesis

```
structure StripMasterHypothesis' (n k : ℕ) : Prop where
  uniformSylvester : SYZ40.UniformSylvesterInjective K n k
  realizability : ∀ Ucard, k ≤ Ucard → Ucard ≤ n →
    Nonempty (SYZ20JointRankSuperadditive.SuperadditiveUnion (F := K) (V := V) n k Ucard)
```

`StripMasterHypothesis'.ofSYZ40` shows it is a strict weakening of SYZ40's three-field hypothesis
(drop the now-proven field). `strip_theorem_of_master_hypothesis'` delivers the full strip
conclusion from the two fields: the **spread branch is stated concretely** (every in-budget reduced
syzygy vanishes = `strip_theorem_of_uniform_sylvester`, from `uniformSylvester` alone) plus the union
budget `|U| ≤ n−1` (from `realizability`). No bridge field is consumed.

## What still needs a (strictly lighter, named) hypothesis

The abstract-*subspace* pair-law restatement (`finrank(A⊔B⊔C) = finrank W`) still needs the
SYZ25/SYZ34 duality dictionary, isolated as the light `def SyzdimDictionary` and consumed only by
`pairInteriorLaw_of_master'`. It carries **no** syzygy content (pure
`generation_iff_dualAnnihilator` + fiber-product transport), so it is honestly weaker than the old
catch-all. It is **not** a field of `StripMasterHypothesis'` — the concrete strip does not need it.

## Field-list delta

- SYZ40 `StripMasterHypothesis`: `{ uniformSylvester, syzdimBridge, realizability }`.
- SYZ41 `StripMasterHypothesis'`: `{ uniformSylvester, realizability }` (syzdimBridge REMOVED).
- Optional abstract-form recovery: `+ SyzdimDictionary` (light duality transport), used only by
  `pairInteriorLaw_of_master'`.

## Axiom audit

All 8 declarations: `[propext, Classical.choice, Quot.sound]` only — no `sorryAx`, no
`native_decide`. Built via `lake env lean` on the file (deps: SYZ25/35/36/40 oleans).

## Honest status

The `d = syzdim` bridge is reduced from a probe-verified black box to **proven syzygy logic + a
named light duality dictionary**. The concrete strip (spread branch = module vanishing) is on **two**
fields. No unconditional `δ*`; the sole substantive open input remains `UniformSylvesterInjective`
(SYZ39, BGK type at `n = 2³⁰`).
