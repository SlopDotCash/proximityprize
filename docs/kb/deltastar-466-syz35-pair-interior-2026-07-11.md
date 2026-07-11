# SYZ35 — the punctured-pair interior law is equivalent to union-generation

Date: 2026-07-11.  Issue #466, rate-`1/2` proximity strip theorem.  Scope: the SYZ34 residual
`SYZ34PairInteriorLaw` (the punctured-pair `−2k` closed form), interior band `1/4 < δ < 1/3`.

## Verdict — PARTIAL

SYZ35 does **not** close the interior-generation gate.  It **localises** the residual: the sharp
punctured-pair closed form is proved to be *equivalent* (both directions) to the union-generation
statement `D_{Cᴬ} ⊔ D_{Cᴮ} ⊔ D_{Cᶜ} = D_{Cᴬ∪Cᴮ∪Cᶜ}`, and every surrounding inequality — the exact
reduction, the lower bracket, and the closed-form arithmetic — is discharged unconditionally and
axiom-clean.  The one missing direction (the sharp *upper* bound, i.e. generation itself) is now the
single named residual, unchanged in difficulty but pinned to a clean subspace-generation fact.

Landed, axiom-clean (`[propext, Classical.choice, Quot.sound]`, no `sorry`, no new axiom):

```text
Frontier/_SYZ35PairInteriorLaw.lean          (4 theorems)
scripts/probes/probe_syz35_generation_equiv.py
```

## The key structural fact

Write `obj := finrank ((A ⊔ B) ⊓ C)` for the fiber-product object of SYZ34 (`= finrank (π_C A ⊓ π_C
B)` under the SYZ23 disjointness hypotheses).  With `A ⊓ B = ⊥` alone (no coding hypotheses),

```text
obj + finrank (A ⊔ B ⊔ C) = finrank A + finrank B + finrank C        (finrank_pairInf_add_finrank_sup)
```

so `obj = finrank A + finrank B + finrank C − finrank (A ⊔ B ⊔ C)`, a **symmetric** function of the
three cores.  Two consequences:

* **Lower bracket** (`target_le_finrank_pairInf`): for any ceiling `finrank (A ⊔ B ⊔ C) ≤ u`,
  `finrank A + finrank B + finrank C ≤ obj + u`.  With `u = finrank D_{union}` and the SYZ21 MDS
  shortening dims `finrank A = |Cᴬ| − k` etc., the RHS budget gives the probe closed form
  `obj ≥ |Cᴬ∩Cᴮ| + |Cᴬ∩Cᶜ| + |Cᴮ∩Cᶜ| − |triple| − 2k` — the **always-true** direction.

* **Generation equivalence** (`pairInteriorLaw_iff_generation`): under `A ⊓ B = ⊥` and a ceiling
  subspace `A ⊔ B ⊔ C ≤ W`, the sharp law `obj + finrank W = finrank A + finrank B + finrank C`
  holds **iff** `finrank (A ⊔ B ⊔ C) = finrank W`.  I.e. the exact closed-form value of the punctured
  pair is **exactly as hard as** union-generation (`W = D_union` ⇒ deficiency `0`).  The `−2k` sharp
  bound is *not* a separable arithmetic fact — every reformulation (support injection, symmetric
  puncturing, fiber-product iteration) collapses back to `A ⊔ B ⊔ C = D_union`.

* **Closed-form arithmetic** (`closedForm_eq`): over `ℤ`, with the SYZ21 substitutions and
  inclusion–exclusion `|union| = Σ|Cᵢ| − Σ_pair + |triple|`, the abstract generation value
  `(finrank A + finrank B + finrank C) − finrank W` equals
  `|Cᴬ∩Cᴮ| + |Cᴬ∩Cᶜ| + |Cᴮ∩Cᶜ| − |triple| − 2k`.

## Why the sharp upper bound is the whole gate

`obj = Σ finrank Cᵢ − finrank (A ⊔ B ⊔ C)` and `finrank (A ⊔ B ⊔ C) ≤ finrank D_union` (subset)
give `obj ≥ target` for free (lower bracket).  Equality `obj = max(0, target)` forces
`finrank (A ⊔ B ⊔ C) = finrank D_union`, i.e. the three shortenings **generate** the union
shortening.  That generation is the open interior-band gate.  So:

```text
prove the sharp punctured-pair law   ⟺   prove  D_{Cᴬ} ⊔ D_{Cᴮ} ⊔ D_{Cᶜ} = D_{Cᴬ∪Cᴮ∪Cᶜ}
```

This is confirmed by probe: the support-injection route yields only the one-`k` bound
`obj ≤ |Cᴬ∩(Cᴮ∪Cᶜ)| − k`; sharpening it to `−2k` requires exactly the missing generation
surjectivity `A ∩ D_{Cᴮ∪Cᶜ} ↠ D_{Cᴮ∪Cᶜ} / (B + C)`, whose deficiency `k − |Cᴮ∩Cᶜ|` is precisely the
gap between the two `k` budgets.

## D = 3 generation / general D

* **D = 3 generation:** NOT closed.  Reduced (SYZ34 + SYZ35) to the single fact
  `finrank (A ⊔ B ⊔ C) = finrank D_union`; the lower bracket and all arithmetic are proved, the
  upper bound is the residual.
* **General D:** the `m`-core gate is `A₁ ⊔ … ⊔ A_m = D_{⋃Cᵢ}`.  SYZ35's reduction is the natural
  inductive statement (peel one core, the residual pairwise-disjointness holds post-merge), but the
  induction still bottoms out on the same subspace-generation fact.  NOT formalised.

## Honesty note

This is a localisation, not a closure.  The named residual survives — renamed conceptually from
"the `−2k` closed form" to "union-generation `A ⊔ B ⊔ C = D_union`", which is strictly cleaner (no
truncated arithmetic, a single subspace equality) and is the right target for the general-`D` peel.
Nothing here touches the Paley/BGK sup-norm wall.

## Validation

```bash
scripts/lake-locked.sh build ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ34StripInteriorGeneration
scripts/pg-iterate.sh ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ35PairInteriorLaw.lean
python3 scripts/probes/probe_syz35_generation_equiv.py   # 3 fields, n≤30, ~14k triples, 0 violations
```

Four declarations, axioms `[propext, Classical.choice, Quot.sound]`, no `sorry`, no new axiom.
```

## Scoreboard (rate-1/2 interior strip)

| brick | statement | status |
|-------|-----------|--------|
| SYZ34 fiber-product | `obj = finrank (π_C A ⊓ π_C B)` (disjoint hyps) | LANDED |
| SYZ35 reduction | `obj + finrank(A⊔B⊔C) = Σ finrank Cᵢ` | LANDED |
| SYZ35 lower bracket | `obj ≥ target` (union ceiling) | LANDED |
| SYZ35 gen-equiv | sharp law ⟺ `finrank(A⊔B⊔C)=finrank W` | LANDED |
| SYZ35 closed-form arith | value = `Σ_pair − triple − 2k` | LANDED |
| **union-generation** | `A⊔B⊔C = D_union` (D=3, in-band) | **OPEN (residual)** |
| general-D peel | `⨆Aᵢ = D_union` | OPEN |
