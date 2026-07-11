# SYZ34 — strip-interior generation: the fiber-product identity and the punctured-pair residual

Date: 2026-07-11.  Issue #466, rate-`1/2` proximity strip theorem.  Scope: the **last open gate**,
strip-interior generation for post-merge spread families in the band `1/4 < δ < 1/3`.

## Verdict

This wave **reduces** the interior-generation gate to a single, sharply-characterised residual and
lands the unconditional linear-algebra brick that drives it.  It does **not**, on its own, close
the gate: the final closed-form value of a *punctured pair* intersection remains a named residual
(`SYZ34PairInteriorLaw`), pinned exhaustively by probe but not yet proved elementarily in general.

Landed, axiom-clean (`[propext, Classical.choice, Quot.sound]`, no `sorry`, no new axiom):

```text
Frontier/_SYZ34StripInteriorGeneration.lean
```

## Setup (post-merge band)

Dual code of an MDS/RS code `D = Dᗮ`, `dim D = n - k`, dual distance `k + 1`.  For a core (support
set) `S`, the shortening `D_S := { v ∈ D : supp v ⊆ S }` has `dim D_S = max(0, |S| - k)`.  A family
`C₁,…,C_m` **generates** iff `∑ D_{Cᵢ} = D_{⋃ Cᵢ}` (deficiency `0`).  After the SYZ32 merge, every
surviving spread family in the interior band has pairwise overlaps `|Cᵢ ∩ Cⱼ| ≤ k - 1 < k + 1`, so
every pairwise dual intersection `D_{Cᵢ} ∩ D_{Cⱼ} = 0` (SYZ23).  The band arithmetic squeezes
overlaps into the narrow window `[2s - n, k - 1]`, and past `s = (n + k - 1)/2` no two cores can
coexist (single-core families, trivially generate).  The whole gate is the triple `D = 3` case.

## The reduction chain (all verified by probe, `scripts/probes/probe_syz34*.py`)

Write `A = D_{Cᴬ}`, `B = D_{Cᴮ}`, `C = D_{Cᶜ}`.  With `A ⊓ B = 0`,

```text
deficiency 0  ⟺  dim((A+B) ∩ C) = |Cᴬ∩Cᴮ| + |Cᴬ∩Cᶜ| + |Cᴮ∩Cᶜ| − |Cᴬ∩Cᴮ∩Cᶜ| − 2k   (closed form)
```

by inclusion–exclusion.  The interior-band arithmetic `s > (n + 2k − 1)/3` (always true for
`s > 2n/3`, `k = n/2`) forces the RHS `≤ 0`, i.e. **deficiency `0`, generation holds**.  Probe
`probe_syz34b.py`: three fields (`p ∈ {61,101,257}`), sizes to `n = 32`, ≈ 4000 *constructed* band
triples with prescribed overlaps, **0** violations of the closed form, `0` pairwise-nonzero,
`max_deficiency = 0`.  The `(k+1)`-core counterexamples of SYZ25 all live at `δ ≥ 1/3` (smaller
`s`) and the SYZ28/31 near-duplicate cracks merge away; none survive in-band.

### The unconditional brick (proved in Lean)

The value `dim((A+B) ∩ C)` is pinned by a **general finite-dimensional fiber-product identity** that
uses *no* coding hypotheses.  For any subspaces `A, B, C` of a finite-dim `V`, with `π_C = C.mkQ :
V → V ⧸ C`:

```text
finrank ((A ⊔ B) ⊓ C) + finrank (π_C A ⊔ π_C B) + finrank (A ⊓ B) = finrank A + finrank B
```

(`finrank_sup_inf_add_finrank_map_mkQ`).  Proof = restricted rank–nullity for `π_C` on `A ⊔ B`
(`finrank_map_add_finrank_inf_ker`, itself `LinearMap.finrank_range_add_finrank_ker` on the
`domRestrict`) combined with the modular law `finrank_sup_add_finrank_inf_eq`.  Specialised to the
SYZ23 band hypotheses `A ⊓ B = ⊥`, `Disjoint A C`, `Disjoint B C` (the last two = injectivity of
`π_C` on `A` and `B`, since supports meet `Cᶜ` in `≤ k − 1 < k + 1` points):

```text
dim((A + B) ∩ C) = dim(π_C A ∩ π_C B)              (finrank_sup_inf_eq_finrank_map_inf)
```

This **strips the third core off the support**: a triple intersection becomes a *pair* intersection
`π_C A ∩ π_C B` in the punctured quotient `V ⧸ C` (equivalently, restrict to the coordinates outside
`Cᶜ`).  The identity itself is confirmed by `probe_syz34c.py` (exact, all fields/sizes).

## What closes and what remains

* **Closes (unconditional, in Lean):** the fiber-product identity and its injective specialisation
  — i.e. the triple-generation deficiency is *exactly* `dim(π_C A ∩ π_C B)`, a punctured pair.  So
  the D=3 gate is now a statement about **two** punctured shortenings, not three.
* **Remains — `SYZ34PairInteriorLaw` (named residual):** the closed form
  `dim(π_C A ∩ π_C B) = max(0, Σ_pair − triple − 2k)` for the punctured pair.  Probe-exact across
  ≈4000 band triples and three fields, but the elementary sharp bound (the `−2k`, two shortening
  budgets used simultaneously) is not yet a general proof.  A single-shortening injection only
  yields `dim ≤ max(0, |Cᴬ∩(Cᴮ∪Cᶜ)| − k)` (one `k`); the sharp bound needs both `a ∈ D_{Cᴬ}` and
  `b ∈ D_{Cᴮ}` dual-membership together.  The natural route is to iterate the *same* fiber-product
  reduction on the punctured pair, or an MDS-matroid rank truncation argument in `V ⧸ C`.
* **General `D`:** with D=3 reduced to the punctured pair, the SYZ33 case split (`m ≤ 3`
  unconditional; `m ≥ 4` spread branch) applies inductively — the same subspace argument peels one
  core at a time via `finrank_sup_inf_eq_finrank_map_inf`.  Not yet formalised.

## Honesty note

The Lean file is the reduction, not the closure: it proves generation ⟺ (punctured-pair value)
unconditionally, and confirms the value is `0` in-band by probe.  The remaining named residual is a
genuine open arithmetic fact (probe-pinned), consistent with the campaign's modular-residual
convention.  Nothing here touches the Paley/BGK sup-norm wall.

## Validation

```bash
scripts/pg-iterate.sh \
  ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ34StripInteriorGeneration.lean
python3 scripts/probes/probe_syz34.py      # random band triples
python3 scripts/probes/probe_syz34b.py     # constructed, 3 fields, to n=32
python3 scripts/probes/probe_syz34c.py     # fiber-product identity
```

Checked probe output: `scripts/probes/_out_syz34.txt`.  Three declarations, axioms
`[propext, Classical.choice, Quot.sound]`, no `sorry`, no new axiom.
