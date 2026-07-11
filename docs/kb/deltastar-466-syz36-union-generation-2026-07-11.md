# SYZ36 — union-generation for band triples, reduced to a univariate syzygy

Date: 2026-07-11.  Scope: the last open gate of the rate-`1/2` proximity strip theorem, localised
by SYZ35 to a subspace-generation fact for three shortened RS duals on band cores.

## Verdict

SYZ36 does **not** close the strip.  It does two honest things:

1. **Reduces union-generation to an exact univariate-polynomial-syzygy law** (probe-verified, `0`
   mismatches over three fields and both domain types), and formalizes the reduction chain
   axiom-clean.
2. **Refutes the naive gate**: "band geometry ⟹ generation" is **false**.  There is an explicit,
   field-independent Koszul obstruction inside the stated band.  Generation holds robustly only in a
   tight sub-band (rate `≤ 1/2`, saturated overlaps).

## The object (recap of SYZ35 / SYZ25)

For `RS[n,k]` with dual distance `k+1`, three cores `Cᴬ, Cᴮ, Cᶜ` in the band (sizes
`s ∈ (2n/3, 3n/4)`, pairwise overlaps `m_XY = |C_X∩C_Y| ∈ [2s−n, k−1]`), let `A,B,C` be the
shortened duals.  SYZ35: the closed-form value of the punctured pair holds **iff**
`finrank(A ⊔ B ⊔ C) = finrank D_{Cᴬ∪Cᴮ∪Cᶜ}` (the cores generate the union shortening).  SYZ25: this
is local-to-global polynomial rigidity — every `p : U → F` that is `deg < k` on each core is globally
`deg < k`.

## The reduction chain (formalized in `Frontier/_SYZ36UnionGeneration.lean`)

Let `p` be `deg < k` on each core, `p_X = p|_{C_X}`, mismatches `q_XY := p_X − p_Y`.

1. **Cocycle identity** `q_AB − q_AC + q_BC = 0` (`cocycle_identity`, `ring`).  Rigidity fails iff
   the `q_XY` are not all zero.
2. **Degree-drop factorization** (`vanish_factor_natDegree`, `vanish_cofactor_lt`): `q_XY` vanishes
   on the `m_XY` overlap points, so `q_XY = V_XY · s_XY` with `natDegree s_XY + m_XY < k`
   (Mathlib `Finset.prod_dvd_of_coprime` + `pairwise_coprime_X_sub_C`, exact degree add in the
   domain `K[X]`).
3. **`V_T`-cancellation** (`reduce_by_VT`): factor the triple-vanishing `V_T` out of every `V_XY`
   (`V_XY = V_T · W_XY`, `deg V_T = |T|`, `W` pairwise coprime), cancel `V_T ≠ 0` in the domain, and
   obtain the **reduced syzygy**
   `W_AB r_AB − W_AC r_AC + W_BC r_BC = 0`, `deg r_XY < k − m_XY`.

So union-generation `⟺` the reduced syzygy module (with per-pair degree budgets `k − 1 − m_XY`) is
trivial.

## The exact law (probe `probe_syz36_union_generation.py`)

```
finrank D_{⋃Cᵢ} − finrank(A ⊔ B ⊔ C)
    =  dim { (r_AB,r_AC,r_BC) : W_AB r_AB − W_AC r_AC + W_BC r_BC = 0,
                                 deg r_XY ≤ k−1−m_XY }
```

Verified with **0 mismatches** (`d == syzdim`) over `p ∈ {31, 101, 65537}`, generic domain `{1..n}`
and roots-of-unity domain, thousands of band triples per `(n,k)`.  This is the concrete μ-basis
realization of SYZ25's duality: union-generation is *exactly* a univariate syzygy-triviality
question.

## The Koszul obstruction — the wall is FALSE as a band statement

The triple `(r_AB, r_AC, r_BC) = (W_AC, W_AB, 0)` is always a syzygy (`koszul_syzygy`,
`W_AB·W_AC − W_AC·W_AB + 0 = 0`), nonzero when `W_AB,W_AC ≠ 0`, of pair-degrees `m_AC − |T|`,
`m_AB − |T|`.  It is **in budget** (`koszul_in_budget`) — a genuine extra cocycle, so generation
**fails** — exactly when

```
m_AB + m_AC − |T|  ≤  k − 1     (some vertex).
```

Probe confirms the Koszul certificate is *sound*: `koszul_but_generates = 0` in every tested
`(n,k,p,domain)`.  Consequently the band admits explicit generation counterexamples; the smallest
robust family (fails over generic **and** roots-of-unity, `p=31,101,65537`, MDS representation) is

```
n=10, k=6,  cores of size s=7,  pairwise overlaps 4..5.
```

Diagnostic (`diag.py`): the failing triples persist for **MDS** roots-of-unity representations at
large fields (`n=14,k=9 @ p=211`: 385/400 fail with MDS = True), so failures are **genuine**, not
non-MDS Vandermonde coincidences.  Only a thin residual is truly field-dependent (`n=13,k=7`: 10
fails at `p=31`, 0 at `p=101`) — those are `resultant`-vanishing coincidences beyond the Koszul
count.

### Rate dependence

- **Rate `= 1/2`** (`n=10,k=5`; `n=14,k=7`): generation holds on **every** band triple.  There the
  overlaps `m_XY ≥ 2s−n` are so large that every budget `k − m_XY ≤ 0`: all `r_XY = 0` are forced
  (`saturated_cofactor_zero`) and rigidity is automatic — SYZ35's gate closes unconditionally.
- **Rate `> 1/2`** (`k > n/2`): massive band-generation failures, Koszul-forced plus degree-count
  forced.

## What was proven verbatim (axiom-clean, `_SYZ36UnionGeneration.lean`)

`cocycle_identity`, `vanish_factor_natDegree`, `natDegree_prod_X_sub_C`, `vanish_cofactor_lt`,
`reduce_by_VT`, `koszul_syzygy`, `koszul_syzygy_ne_zero`, `koszul_in_budget`,
`saturated_cofactor_zero`.  All nine `#print axioms` show only `propext, Classical.choice,
Quot.sound`.  No `sorry`, no `native_decide`.

## Literature verdict

- **μ-basis theory (Cox–Sederberg–Chen; Song–Goldman; Hong–Hoon–Yao arXiv:1603.04813,
  arXiv:2011.10924).**  Directly on point: the syzygy module of a coprime univariate triple
  `(f,g,h)` is a *free* `K[X]`-module of rank `2`, with a μ-basis whose two generator degrees
  `µ₁ ≤ µ₂` are determined a priori and satisfy `µ₁ + µ₂ = deg`.  This is the exact classical tool
  governing whether an in-budget syzygy exists; the Koszul relation here is one such generator.
- **Higher-order MDS / GM-MDS (Brakensiek–Dhar–Gopi arXiv:2310.12888; Lovett ECCC-2018-047;
  Brakensiek–Gopi–Makam arXiv:2107.10822).**  The union-generation question is the
  represented-uniform-matroid / higher-order-MDS statement (cores = flats of `U(k,n)`).  For
  *generic* polynomial-code columns higher-order MDS holds, but these results do **not** discharge
  the fixed Vandermonde / roots-of-unity specialization at the prescribed band incidence, and — as
  the probe shows — the specialization genuinely *fails* for `k > n/2`.  So the literature confirms
  the vocabulary and the freeness/degree structure but supplies no closure of the band gate.
- **Generalized Hamming weights / subcode support weights of MDS codes** (Wei; and recent
  SSWD determinations): give `finrank A_i = |C_i| − k` and the union ceiling `|U| − k`, i.e. the
  *counts*, but not the *incidence* (generation), consistent with SYZ25's "generation is strictly
  stronger than the count".

## Final form of the wall

> Union-generation for a band triple `⟺` the vanishing polynomials `W_AB, W_AC, W_BC` of the
> pairwise-exclusive overlap regions admit **no** nonzero syzygy
> `W_AB r_AB − W_AC r_AC + W_BC r_BC = 0` with `deg r_XY ≤ k − 1 − m_XY`.

This is a univariate μ-basis / resultant condition.  It is **false** in the stated band whenever a
Koszul pair fits budget (`m_AB + m_AC − |T| ≤ k − 1` for some vertex) — a field-independent
counterexample.  It is **true** in the saturated sub-band (all budgets `≤ 0`, rate `≤ 1/2` with
maximal overlaps), where the SYZ35 gate closes unconditionally.  Closing any regime strictly between
these — where no Koszul pair fits yet budgets are positive — is the residual: a
Vandermonde-specific resultant-nonvanishing statement, open beyond the saturated sub-band.

## Validation

```bash
scripts/pg-iterate.sh \
  ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ36UnionGeneration.lean   # ✅ axiom-clean
python3 scripts/probes/probe_syz36_union_generation.py                        # d==syzdim, 0 mismatches
```
