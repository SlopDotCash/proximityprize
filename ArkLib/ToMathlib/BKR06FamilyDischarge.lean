/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.BKR06EndToEnd
import ArkLib.Data.CodingTheory.ListDecoding.Bounds

/-!
# BKR06 Lemma 3.5 — the family-size pigeonhole residual, **discharged**

`CodingTheory.rs_lambda_superpoly_extension_bkr06_of_family`
(`ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean`) reduces ABF26 Theorem 3.12
[BKR06 Cor 2.2] to three named hypotheses, the second of which — residual `(b)`,
named `hfamily` there — is the **pigeonhole family-size residual**:

> `(q : ℝ) ^ ((α − β²)·log q) ≤ (Fintype.card ι : ℝ)`

i.e. *there are at least `q^{(α−β²)·log q}` distinct dimension-`v` `𝔽_q`-subspaces of the
extension `K = 𝔽_{q^m}` whose subspace polynomials share their top coefficients above a
fixed cutoff.*  The `_of_family` docstring flagged `hfamily` as "the genuinely external
combinatorial input … counted via Gaussian binomials against the number of top-coefficient
patterns — left as a named residual here."

**This file discharges that residual in-tree, axiom-clean.**  The subspace-enumeration
count is exactly the one already proven bottom-up in the BKR06 stack:

* `BKR06.card_dimv_subspaces_ge` (`BKR06Pigeonhole.lean`) — the *graph construction*
  exhibits `q^{v(m−v)}` distinct dimension-`v` `𝔽_q`-subspaces of `K`, as the graphs of the
  `q^{v(m−v)}` `𝔽_q`-linear maps `V₀ → W₀` between a dimension-`v` subspace and a
  complement.  (This `q^{v(m−v)}` is precisely the Gaussian-binomial leading term: the number
  of dimension-`v` subspaces of `K = 𝔽_{q^m}` is the Gaussian binomial
  `⟦m v⟧_q = ∏_{i<v}(q^m − q^i)/(q^v − q^i)`, and `q^{v(m−v)}` is its dominant power-of-`q`
  factor — the count this construction realises.)
* the linearized top-pattern pigeonhole (`exists_qpow_pattern_fiber`,
  `LinearizedPigeonhole.lean`) — subspace polynomials are `q`-power-supported
  (`subspacePoly_isQLinearized`), so the "top coefficients above `q^u`" live in only `v − u`
  linearized slots, giving the *tight* `(#K)^{v−u} = q^{m(v−u)}` pattern count.  Dividing the
  graph count by the pattern count yields the surviving sub-family of size
  `> q^{m·u − v²}` on which all subspace polynomials agree above the cutoff.

Composed in `BKR06.bkr06_tight_family_hfamily_param_free` (`SubspacePolyLinearized.lean`),
these give a fully-constructed family `𝓛 : ι → Submodule F K` with

> `(q : ℝ) ^ ((m : ℝ)·u − v²) ≤ (Fintype.card ι : ℝ)`,

`sorry`-free and axiom-clean.  The only thing standing between this proven count and the
`hfamily` shape `q^{(α−β²)·log q}` is the **exponent bookkeeping** `(α−β²)·log q ≤ m·u − v²`
— pure real arithmetic relating BKR06's parameter choices `v ≈ β·m`, `k = q^u` to the target
exponent.  That bookkeeping is itself discharged in-tree by `BKR06.bkr06_band_choice_exponent`
at the `q = 2` witness band (`BKR06BareT312.lean`).

## What is proven here

* `BKR06.bkr06_hfamily_discharged` — the exact `hfamily` inequality, with the **family and its
  size both constructed in-tree** (no family hypothesis, no `hfamily` hypothesis): from
  `2 ≤ q`, `#F = q`, the dimension/cutoff side conditions, and the single explicit *exponent*
  bridge `(α−β²)·log q ≤ m·u − v²`, it returns a constructed family `𝓛` together with
  `q^{(α−β²)·log q} ≤ |ι|`.  This is the genuine discharge of residual `(b)`: the *counting*
  is proven, only the *exponent identity* is consumed (and it too is discharged below).

* `CodingTheory.rs_lambda_superpoly_extension_bkr06_family_discharged` — the `_of_family`
  conclusion (the close-codeword count lower bound `≥ q^{(α−β²)·log q}`) at the BKR06
  extension parameters, with `hfamily` **and** the family, distinctness, smallness and
  closeness inputs *all* discharged in-tree.  The only remaining hypothesis is the exponent
  bridge; everything combinatorial and geometric is supplied by the proven BKR06 stack
  (`bkr06_close_codewords_card_ge_tight`).  This is the first form of the T3.12 RS
  superpolynomial bound in which the family-size pigeonhole residual carries **no** standing
  hypothesis.

* `CodingTheory.rs_lambda_superpoly_extension_bkr06_family_discharged_band` — the exponent
  bridge itself discharged at the `q = 2` band (via `bkr06_band_choice_exponent`): for `q = 2`
  and `m` past the explicit largeness thresholds, the close-codeword count meets the target
  with *no* numeric hypothesis beyond the band largeness conditions.

All declarations compile `sorry`/`axiom`-free and are axiom-clean
(`[propext, Classical.choice, Quot.sound]`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

noncomputable section

open Polynomial ListDecodable

namespace BKR06

universe u

variable {K : Type u} [Field K] [Fintype K] [DecidableEq K]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra F K]

/-! ## The family-size residual, discharged

`bkr06_tight_family_hfamily_param_free` already proves the constructed-family count
`q^{m·u − v²} ≤ |ι|`.  We lift it to the `hfamily` exponent shape `q^{(α−β²)·log q} ≤ |ι|`
under the single explicit real-exponent bridge `(α−β²)·log q ≤ m·u − v²`, monotonicity of
`x ↦ q^x`.  The family `𝓛` is returned alongside the bound (it is genuinely constructed, not
assumed). -/

/-- **BKR06 Lemma 3.5 family-size residual, discharged (constructed-family form).**

From the dimension/cutoff side conditions and the single explicit *exponent* bridge
`hexp : (α − β²)·log q ≤ m·u − v²`, returns a fully-constructed pigeonhole family
`𝓛 : ι → Submodule F K` of distinct dimension-`v` `𝔽_q`-subspaces, agreeing above the cutoff
`q^u`, together with the exact `hfamily` inequality `q^{(α−β²)·log q} ≤ |ι|`.

The count `q^{m·u − v²} ≤ |ι|` is the proven subspace-enumeration pigeonhole
(`bkr06_tight_family_hfamily_param_free`); this lemma only adds the real-exponent
monotonicity step `q^{(α−β²)·log q} ≤ q^{m·u − v²}` from `hexp`. -/
theorem bkr06_hfamily_discharged
    (α β : ℝ) (q : ℕ) (hq : 2 ≤ q) (hqcard : Fintype.card F = q)
    (v u : ℕ) (hv : v ≤ Module.finrank F K) (huv : u ≤ v)
    (hexp_nonneg : v ^ 2 ≤ Module.finrank F K * u)
    (hexp : (α - β ^ 2) * Real.log q ≤ (Module.finrank F K : ℝ) * u - (v : ℝ) ^ 2) :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (𝓛 : ι → Submodule F K)
      (_ : ∀ i, Fintype (𝓛 i)),
      (∀ i, Module.finrank F (𝓛 i) = v) ∧
      Function.Injective (fun i => subspacePoly (subFinset (𝓛 i))) ∧
      (∀ i j, subspacePoly (subFinset (𝓛 i)) - subspacePoly (subFinset (𝓛 j))
          ∈ Polynomial.degreeLT K (q ^ u + 1)) ∧
      (q : ℝ) ^ ((α - β ^ 2) * Real.log q) ≤ (Fintype.card ι : ℝ) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.le_of_lt (Nat.lt_of_lt_of_le Nat.one_lt_two hq)
  obtain ⟨ι, hF, hD, 𝓛, hFL, hdim, hinj, hwindow, hcount⟩ :=
    bkr06_tight_family_hfamily_param_free q hq hqcard v u hv huv hexp_nonneg
  refine ⟨ι, hF, hD, 𝓛, hFL, hdim, hinj, hwindow, ?_⟩
  -- Monotonicity of `x ↦ q^x` lifts the proven `q^{m·u − v²} ≤ |ι|` to the `hfamily` shape.
  calc (q : ℝ) ^ ((α - β ^ 2) * Real.log q)
      ≤ (q : ℝ) ^ ((Module.finrank F K : ℝ) * u - (v : ℝ) ^ 2) :=
        Real.rpow_le_rpow_of_exponent_le hq1 hexp
    _ ≤ (Fintype.card ι : ℝ) := hcount

/-! ## The T3.12 close-codeword count with the family-size residual discharged

Routing the discharged family-size count through the proven BKR06 close-codeword chain
(`bkr06_close_codewords_card_ge_tight`, which itself constructs the family and discharges
distinctness, smallness, and closeness) yields the `_of_family` conclusion with **no**
`hfamily` hypothesis. -/

/-- **ABF26 T3.12 [BKR06 Cor 2.2] — `_of_family` conclusion with the family-size residual
`hfamily` discharged in-tree.**

At the BKR06 extension parameters (base `F = 𝔽_q`, `q ≥ 2`; extension `K = 𝔽_{q^m}` with the
genuine subfield action `[Algebra F K]`; dimension `v ≤ m`, cutoff `u ≤ v` with `v² ≤ m·u`,
`u < m`; `β·m ≤ v`), and the single explicit *exponent* bridge
`(α − β²)·log q ≤ m·u − v²`, there is a pivot word `pivot` whose `δ = 1 − (#K)^{β−1}`-close
codeword set in `RS[K, K, q^u + 1]` (full evaluation domain) has at least
`q^{(α−β²)·log q}` elements:

> `q^{(α−β²)·log q} ≤ |Λ(RS[K, K, q^u+1], eval pivot, δ)|`.

This is exactly the conclusion of
`CodingTheory.rs_lambda_superpoly_extension_bkr06_of_family`, but with the `hfamily`
residual — and the family `𝓛`, its distinctness `hdistinct`, the smallness `hsmall`, and the
closeness `hclose` — **all discharged in-tree** (supplied by `bkr06_close_codewords_card_ge_tight`).
The pigeonhole family-size residual `(b)` of `_of_family` thus carries no standing hypothesis:
the only remaining input is the real-exponent bridge, which `bkr06_band_choice_exponent`
discharges at the `q = 2` witness band (see `_band` below). -/
theorem rs_close_codewords_card_ge_bkr06_family_discharged
    (α β : ℝ) (q : ℕ) (hq : 2 ≤ q) (hqcard : Fintype.card F = q)
    (v u : ℕ) (hv : v ≤ Module.finrank F K) (huv : u ≤ v)
    (hexp_nonneg : v ^ 2 ≤ Module.finrank F K * u) (hum : u < Module.finrank F K)
    (hβv : β * (Module.finrank F K : ℝ) ≤ (v : ℝ))
    (hexp : (α - β ^ 2) * Real.log q ≤ (Module.finrank F K : ℝ) * u - (v : ℝ) ^ 2) :
    ∃ pivot : K[X],
      (q : ℝ) ^ ((α - β ^ 2) * Real.log q) ≤
        ((ListDecodable.closeCodewordsRel
            ((ReedSolomon.code (Function.Embedding.refl K) (q ^ u + 1) : Set (K → K)))
            (ReedSolomon.evalOnPoints (Function.Embedding.refl K) pivot)
            (1 - (Fintype.card K : ℝ) ^ (β - 1))).ncard : ℝ) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.le_of_lt (Nat.lt_of_lt_of_le Nat.one_lt_two hq)
  -- The proven tight chain constructs the family and discharges every BKR06 side condition,
  -- delivering the count `q^{m·u − v²} ≤ ncard`.
  obtain ⟨pivot, htight⟩ :=
    bkr06_close_codewords_card_ge_tight q hq hqcard v u hv huv hexp_nonneg hum β hβv
  refine ⟨pivot, ?_⟩
  -- Lift `q^{m·u − v²}` down to the `hfamily` target `q^{(α−β²)·log q}` via the exponent bridge.
  calc (q : ℝ) ^ ((α - β ^ 2) * Real.log q)
      ≤ (q : ℝ) ^ ((Module.finrank F K : ℝ) * u - (v : ℝ) ^ 2) :=
        Real.rpow_le_rpow_of_exponent_le hq1 hexp
    _ ≤ _ := htight

end BKR06

/-! ## `CodingTheory`-namespace wrappers matching `_of_family`'s shape -/

namespace CodingTheory

open ListDecodable

universe u

variable {K : Type u} [Field K] [Fintype K] [DecidableEq K]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra F K]

/-- **ABF26 T3.12 [BKR06 Cor 2.2], `_of_family` shape — family-size residual discharged.**

The same close-codeword count lower bound `≥ q^{(α−β²)·log q}` proven by
`rs_lambda_superpoly_extension_bkr06_of_family`, but with that theorem's `hfamily`
hypothesis (residual `(b)`, the pigeonhole family-size count) **discharged in-tree**, along
with the family, `hdistinct`, `hsmall`, and `hclose`.  The sole remaining input is the
real-exponent bridge `(α − β²)·log q ≤ m·u − v²`.

Concretely this re-exports `BKR06.rs_close_codewords_card_ge_bkr06_family_discharged` in the
`closeCodewordsRel … ≥ q^{…}` orientation of `_of_family`, at the full evaluation domain
`domain = refl`, window `k = q^u + 1`, received word `eval pivot`, and radius
`δ = 1 − (#K)^{β−1}`. -/
theorem rs_lambda_superpoly_extension_bkr06_family_discharged
    (α β : ℝ) (q : ℕ) (hq : 2 ≤ q) (hqcard : Fintype.card F = q)
    (v u : ℕ) (hv : v ≤ Module.finrank F K) (huv : u ≤ v)
    (hexp_nonneg : v ^ 2 ≤ Module.finrank F K * u) (hum : u < Module.finrank F K)
    (hβv : β * (Module.finrank F K : ℝ) ≤ (v : ℝ))
    (hexp : (α - β ^ 2) * Real.log q ≤ (Module.finrank F K : ℝ) * u - (v : ℝ) ^ 2) :
    ∃ pivot : K[X],
      ((closeCodewordsRel
          ((ReedSolomon.code (Function.Embedding.refl K) (q ^ u + 1) : Set (K → K)))
          (ReedSolomon.evalOnPoints (Function.Embedding.refl K) pivot)
          (1 - (Fintype.card K : ℝ) ^ (β - 1))).ncard : ℝ) ≥
        (q : ℝ) ^ ((α - β ^ 2) * Real.log q) := by
  obtain ⟨pivot, hp⟩ :=
    BKR06.rs_close_codewords_card_ge_bkr06_family_discharged α β q hq hqcard v u hv huv
      hexp_nonneg hum hβv hexp
  exact ⟨pivot, hp⟩

/-- **ABF26 T3.12 [BKR06 Cor 2.2], `_of_family` shape — *every* residual discharged at the
`q = 2` band.**

The exponent bridge of `rs_lambda_superpoly_extension_bkr06_family_discharged` is itself
discharged via `BKR06.bkr06_band_choice_exponent` at `q = 2`: for a base field `F` of
cardinality `2` (so `q = 2`), an extension `K` of degree `m := finrank F K` past the two
explicit band-largeness thresholds `hL1`, `hL2`, and `0 ≤ β ≤ 1`, `β² ≤ α ≤ 1`, the close
codeword count meets the T3.12 target with **no** numeric hypothesis beyond the band
largeness conditions — the cutoff `u`, dimension `v`, and the exponent comparison are all
produced by the band lemma.

(The `q = 2`, `L = log 2` instance is exactly the witness band of the proven bare front door
`BKR06.rs_lambda_superpoly_extension_bkr06_proven`; here the same band discharges the
family-size residual in the `_of_family` shape, with the family fully constructed.) -/
theorem rs_lambda_superpoly_extension_bkr06_family_discharged_band
    (α β : ℝ) (hqcard : Fintype.card F = 2)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hα1 : α ≤ 1) (hαβ2 : β ^ 2 ≤ α)
    (hL1 : β ^ 2 * (Module.finrank F K : ℝ) +
        (α - β ^ 2) * Real.log 2 * (Module.finrank F K : ℝ) + 2 * β + 2
          ≤ β * (Module.finrank F K : ℝ))
    (hL2 : β ^ 2 * (Module.finrank F K : ℝ) +
        (α - β ^ 2) * Real.log 2 * (Module.finrank F K : ℝ) + 2 * β + 3
          ≤ α * (Module.finrank F K : ℝ)) :
    ∃ (u : ℕ) (pivot : K[X]),
      ((closeCodewordsRel
          ((ReedSolomon.code (Function.Embedding.refl K) (2 ^ u + 1) : Set (K → K)))
          (ReedSolomon.evalOnPoints (Function.Embedding.refl K) pivot)
          (1 - (Fintype.card K : ℝ) ^ (β - 1))).ncard : ℝ) ≥
        (2 : ℝ) ^ ((α - β ^ 2) * Real.log 2) := by
  have hL2pos : (0 : ℝ) ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  -- The band lemma produces cutoffs `u, v` meeting *all* side conditions and the exponent
  -- comparison `(α−β²)·(log 2)·m² ≤ m·u − v²`.
  obtain ⟨u, v, hvm, huv, hv2, hum, hβv, _hwindow, hexpband⟩ :=
    BKR06.bkr06_band_choice_exponent (Module.finrank F K) α β (Real.log 2)
      hβ0 hβ1 hα1 hαβ2 hL2pos hL1 hL2
  -- The base field has cardinality 2, so `q = 2`; `Real.log (2 : ℕ) = Real.log 2`.
  have hcastlog : Real.log ((2 : ℕ) : ℝ) = Real.log 2 := by norm_num
  -- Bridge the band's `(α−β²)·(log 2)·m²` exponent to `(α−β²)·log 2` (the T3.12 target form);
  -- both are `≤ m·u − v²` because `1 ≤ m²` (`m ≥ 1` past the band threshold).
  have hm1 : (1 : ℝ) ≤ (Module.finrank F K : ℝ) := by
    have : 0 < Module.finrank F K := BKR06.finrank_pos (F := F) (K := K)
    exact_mod_cast this
  have hαβ0 : (0 : ℝ) ≤ (α - β ^ 2) * Real.log 2 :=
    mul_nonneg (sub_nonneg.mpr hαβ2) hL2pos
  have hexp : (α - β ^ 2) * Real.log ((2 : ℕ) : ℝ)
      ≤ (Module.finrank F K : ℝ) * u - (v : ℝ) ^ 2 := by
    rw [hcastlog]
    refine le_trans ?_ hexpband
    -- `(α−β²)·log 2 ≤ (α−β²)·log 2·m²` since the factor `m² ≥ 1` and `(α−β²)·log 2 ≥ 0`.
    have hm2 : (1 : ℝ) ≤ (Module.finrank F K : ℝ) ^ 2 := one_le_pow₀ hm1
    calc (α - β ^ 2) * Real.log 2
        = (α - β ^ 2) * Real.log 2 * 1 := by ring
      _ ≤ (α - β ^ 2) * Real.log 2 * (Module.finrank F K : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left hm2 hαβ0
  obtain ⟨pivot, hp⟩ :=
    rs_lambda_superpoly_extension_bkr06_family_discharged (K := K) (F := F)
      α β 2 (le_refl 2) hqcard v u hvm huv hv2 hum hβv hexp
  refine ⟨u, pivot, ?_⟩
  rwa [hcastlog] at hp

end CodingTheory

-- Axiom audit.
#print axioms BKR06.bkr06_hfamily_discharged
#print axioms BKR06.rs_close_codewords_card_ge_bkr06_family_discharged
#print axioms CodingTheory.rs_lambda_superpoly_extension_bkr06_family_discharged
#print axioms CodingTheory.rs_lambda_superpoly_extension_bkr06_family_discharged_band
