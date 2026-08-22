/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# LANE OC-EQUI (#466, 2026-07-10): Galois equidistribution of unweighted embedding incidences

## The seam this closes

OC-PIECEB (`_OCPieceBHeightNormCeiling.lean`) capped the naive ideal-stacking route and left
exactly ONE seam open: *"a genuinely transversal multiplicity invariant across distinct prime
ideals, should the census ever be shown to force `Ω(n)` DISTINCT embeddings"*. Its probe measured
embedding coverage "concentrating at the census-building embedding `a = 1`" (87/94, 59/63, 4/4)
and read that as the census failing to supply transversal relations.

This lane resolves the unweighted marginal-count version of the seam:

1. **The concentration was search bias, not mathematics.** The FULL candidate pool (all
   support-≤6 height-1 negacyclic relations) is stable under the Galois action
   `σ_c : r(X) ↦ r(X^c)`, and incidence is EQUIVARIANT: `r` vanishes at embedding `a·c` iff
   `σ_c r` vanishes at embedding `a` (because `(σ_c r)(w^a) = r(w^{ac})`). Hence the
   per-embedding vanishing count of the full pool is EXACTLY the same at every embedding.
   Probe `probe_466_oc_galois_embedding_equidistribution.py` confirms this exactly:
   `n = 32, p = 1153`: 512 vanishing relations at EVERY one of the 16 embeddings
   (total `8192 = 16 · 512`); `p = 1217`: 160 at every embedding; `n = 16` cells: 0 everywhere.
   The measured `a = 1` concentration in OC-PIECEB was an artifact of counting ORBIT
   REPRESENTATIVES found by a search seeded at `a = 1`.

2. **Therefore unweighted embedding coverage is contentless as a route.** Coverage of distinct
   embeddings is ALL-OR-NOTHING: if any relation in the pool vanishes at any embedding, then at
   EVERY embedding some (conjugated) relation vanishes. "Forcing `Ω(n)` distinct embeddings" is
   automatic the moment one primitive relation exists — and it buys nothing, because the total
   incidence count factors EXACTLY as `(number of embeddings) × (stacking count at one
   embedding)`. This does not control weighted first-incidence mass, joint incidence patterns,
   or correlations between distinct relation orbits; those remain possible cross-embedding
   levers.

   Moreover the multi-relation determinant escape is not forced either: covering the `n`
   embeddings by the `n` Galois conjugates of ONE relation gives the product certificate
   `∏_c N(σ_c r) = ±N(r)^n` (norms are Galois-invariant) — no new `p`-power — and a
   permutation zero-pattern in an integer matrix forces NO `p`-divisibility of its determinant
   at all (unit-determinant witness below).

## What is proved (all axiom-clean, `[propext, Classical.choice, Quot.sound]`)

Concrete setting: `M = 2m` (the negacyclic index), candidates `v : ZMod M → ℤ` (coefficient
vectors), evaluation `evalAt w a v = ∑ j, v j · w^{(a·j).val}` at a fixed base element `w` of an
arbitrary field `F` (for the arithmetic instantiation, `w` is the fixed `2m`-th root of unity
mod `𝔭`; the engine needs NO hypothesis on `w`), Galois action `galAct c v = v ∘ (c⁻¹ • ·)`.

* `evalAt_galAct` : the exact equivariance `evalAt a (galAct c v) = evalAt (a·c) v`.
* `galAct_galAct` / `galAct_one` / `galAct_injective` : the action laws and injectivity.
* `vanishCount_mul_right` : for any Galois-stable pool, `count(a·c) = count(a)`.
* `vanishCount_eq` : per-embedding counts are constant — a Galois-stable pool CANNOT
  concentrate coverage at any embedding.
* `not_poolCoverageConcentrates` : genuine negation (`→ False`) of the concentration seam.
* `total_vanishCount_eq_card_mul` : total unweighted incidence `= (#embeddings) · count(1)`.
* `coverage_all_or_nothing` : one incidence anywhere ⟹ coverage at every embedding.
* `galAct_heightOne` / `galAct_support_card` : the concrete support-≤s height-1 pool is
  Galois-stable (so the hypotheses above are MET by the census pool, not vacuous).
* `wpow_add` : with `w^M = 1`, the evaluation base is a genuine character (the arithmetic
  bridge to `r(w^a)` in `𝔽_p`).
* `permutation_zero_pattern_det_unit` : the determinant witness — a permutation zero pattern
  coexists with determinant `±1`, so multi-embedding zero patterns force no `p`-divisibility.

## Honest scope

Structural collapse of the **unweighted marginal-count** seam, not a closure of CORE. The theorem
does not bound weighted first-incidence mass or joint orbit correlations. Those are precisely the
stronger forms still allowed by issue #505. CORE remains OPEN / ON-BGK.

Issue #466. Axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false


open Finset

namespace ArkLib.ProximityGap.Frontier.OCGaloisEmbeddingEquidistribution

variable {F : Type*} [Field F] [DecidableEq F] {M : ℕ} [NeZero M]

/-- Power of the base element `w` by a residue exponent. For the arithmetic instantiation
`w` is the fixed primitive `2m`-th root of unity mod `𝔭`; the equidistribution engine itself
needs no hypothesis on `w`. -/
def wpow (w : F) (e : ZMod M) : F := w ^ e.val

/-- With `w^M = 1`, `wpow` is a genuine character of `ZMod M` — the bridge identifying
`evalAt` with the negacyclic embedding evaluation `r(w^a)`. -/
theorem wpow_add (w : F) (hw : w ^ M = 1) (e f : ZMod M) :
    wpow w (e + f) = wpow w e * wpow w f := by
  simp only [wpow]
  have hx : w ^ (e.val + f.val) = w ^ ((e.val + f.val) % M) := by
    conv_lhs => rw [← Nat.mod_add_div (e.val + f.val) M]
    rw [pow_add, pow_mul, hw, one_pow, mul_one]
  rw [ZMod.val_add, ← pow_add, hx]

/-- Evaluation of the coefficient vector `v` at the embedding indexed by the unit `a`:
`∑ j, v j · w^{(a·j).val}` (the negacyclic evaluation `r(w^a)` once `w^M = 1`). -/
def evalAt (w : F) (a : (ZMod M)ˣ) (v : ZMod M → ℤ) : F :=
  ∑ j : ZMod M, ((v j : ℤ) : F) * wpow w ((a : ZMod M) * j)

/-- The Galois action `σ_c` on coefficient vectors: `(σ_c v) j = v (c⁻¹ · j)`
(so that `σ_c` of the polynomial `r(X)` is `r(X^c)` on exponents). -/
def galAct (c : (ZMod M)ˣ) (v : ZMod M → ℤ) : ZMod M → ℤ :=
  fun j => v ((c⁻¹ : (ZMod M)ˣ) • j)

/-- **Exact Galois equivariance of embedding evaluation**: `σ_c v` vanishes at embedding `a`
iff `v` vanishes at embedding `a·c` — as an identity of field elements. -/
theorem evalAt_galAct (w : F) (a c : (ZMod M)ˣ) (v : ZMod M → ℤ) :
    evalAt w a (galAct c v) = evalAt w (a * c) v := by
  simp only [evalAt, galAct]
  refine (Fintype.sum_equiv (MulAction.toPerm c)
    (fun i => ((v i : ℤ) : F) * wpow w (((a * c : (ZMod M)ˣ) : ZMod M) * i))
    (fun j => ((v ((c⁻¹ : (ZMod M)ˣ) • j) : ℤ) : F) * wpow w ((a : ZMod M) * j))
    (fun i => ?_)).symm
  simp only [MulAction.toPerm_apply]
  change ((v i : ℤ) : F) * wpow w (((a * c : (ZMod M)ˣ) : ZMod M) * i) =
    ((v (c⁻¹ • (c • i)) : ℤ) : F) * wpow w ((a : ZMod M) * (c • i))
  rw [inv_smul_smul]
  congr 2
  change ((a : ZMod M) * (c : ZMod M)) * i = (a : ZMod M) * ((c : ZMod M) * i)
  exact mul_assoc _ _ _

/-- Composition law of the Galois action. -/
theorem galAct_galAct (c d : (ZMod M)ˣ) (v : ZMod M → ℤ) :
    galAct c (galAct d v) = galAct (c * d) v := by
  funext j
  unfold galAct
  rw [mul_inv_rev, mul_smul]

/-- The identity acts trivially. -/
theorem galAct_one (v : ZMod M → ℤ) : galAct (1 : (ZMod M)ˣ) v = v := by
  funext j
  unfold galAct
  rw [inv_one, one_smul]

/-- The Galois action is injective on coefficient vectors. -/
theorem galAct_injective (c : (ZMod M)ˣ) : Function.Injective (galAct (M := M) c) := by
  intro u v huv
  funext j
  have h := congrFun huv (c • j)
  simpa [galAct] using h

section Pool

variable (w : F) (Pool : Finset (ZMod M → ℤ))
  (hstab : ∀ (c : (ZMod M)ˣ) (v : ZMod M → ℤ), v ∈ Pool → galAct c v ∈ Pool)

/-- Number of pool relations vanishing at the embedding `a`. -/
def vanishCount (a : (ZMod M)ˣ) : ℕ :=
  (Pool.filter (fun v => evalAt w a v = 0)).card

/-- The concentration seam named by OC-PIECEB: some embedding strictly out-covered by
another within a Galois-stable pool. -/
def poolCoverageConcentrates : Prop :=
  ∃ a b : (ZMod M)ˣ, vanishCount w Pool b < vanishCount w Pool a

include hstab

/-- The vanishing fiber at embedding `a` is the `σ_c`-image of the fiber at `a·c`. -/
theorem vanishFilter_eq_image (a c : (ZMod M)ˣ) :
    Pool.filter (fun v => evalAt w a v = 0) =
      (Pool.filter (fun v => evalAt w (a * c) v = 0)).image (galAct c) := by
  ext u
  simp only [mem_image, mem_filter]
  constructor
  · intro ⟨hu, hz⟩
    refine ⟨galAct c⁻¹ u, ⟨hstab _ _ hu, ?_⟩, ?_⟩
    · rw [evalAt_galAct, mul_assoc, mul_inv_cancel, mul_one]
      exact hz
    · rw [galAct_galAct, mul_inv_cancel, galAct_one]
  · rintro ⟨v, ⟨hv, hz⟩, rfl⟩
    exact ⟨hstab _ _ hv, by rw [evalAt_galAct]; exact hz⟩

/-- Right-translation invariance of the vanishing count on a Galois-stable pool. -/
theorem vanishCount_mul_right (a c : (ZMod M)ˣ) :
    vanishCount w Pool (a * c) = vanishCount w Pool a := by
  unfold vanishCount
  rw [vanishFilter_eq_image w Pool hstab a c,
    Finset.card_image_of_injective _ (galAct_injective c)]

/-- **Equidistribution**: the per-embedding vanishing count of a Galois-stable pool is the
same at EVERY embedding — a Galois-stable pool cannot concentrate coverage. -/
theorem vanishCount_eq (a b : (ZMod M)ˣ) :
    vanishCount w Pool a = vanishCount w Pool b := by
  have h := vanishCount_mul_right w Pool hstab a (a⁻¹ * b)
  rw [mul_inv_cancel_left] at h
  exact h.symm

/-- Genuine negation of the concentration seam: it is IMPOSSIBLE for the full Galois-stable
pool to concentrate embedding coverage. The OC-PIECEB measurement was orbit-representative
search bias. -/
theorem not_poolCoverageConcentrates : ¬ poolCoverageConcentrates w Pool := by
  rintro ⟨a, b, hlt⟩
  rw [vanishCount_eq w Pool hstab a b] at hlt
  exact lt_irrefl _ hlt

/-- **Unweighted marginal-count collapse**: total incidence over all embeddings factors exactly
as `(#embeddings) · (single-embedding count)`. This does not concern weighted first incidences or
joint incidence patterns. -/
theorem total_vanishCount_eq_card_mul :
    ∑ a : (ZMod M)ˣ, vanishCount w Pool a =
      Fintype.card (ZMod M)ˣ * vanishCount w Pool 1 := by
  rw [Finset.sum_congr rfl (fun a _ => vanishCount_eq w Pool hstab a 1)]
  rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]

/-- **All-or-nothing coverage**: one vanishing relation at one embedding produces a vanishing
relation at EVERY embedding. "Forcing `Ω(n)` distinct embeddings" is automatic, hence not a
route. -/
theorem coverage_all_or_nothing {a : (ZMod M)ˣ}
    (h : ∃ v ∈ Pool, evalAt w a v = 0) (b : (ZMod M)ˣ) :
    ∃ v' ∈ Pool, evalAt w b v' = 0 := by
  obtain ⟨v, hv, hz⟩ := h
  refine ⟨galAct (b⁻¹ * a) v, hstab _ _ hv, ?_⟩
  rw [evalAt_galAct, mul_inv_cancel_left]
  exact hz

end Pool

section ConcretePool

/-- Height-1 candidates: every coefficient is `-1`, `0`, or `1`. -/
def heightOne (v : ZMod M → ℤ) : Prop := ∀ j, |v j| ≤ 1

/-- Support-bounded candidates: at most `s` nonzero coefficients. -/
def supportLE (s : ℕ) (v : ZMod M → ℤ) : Prop :=
  (Finset.univ.filter (fun j => v j ≠ 0)).card ≤ s

/-- The Galois action preserves heights (it only permutes coefficients). -/
theorem galAct_heightOne {v : ZMod M → ℤ} (c : (ZMod M)ˣ) (hv : heightOne v) :
    heightOne (galAct c v) := fun _ => hv _

/-- The Galois action preserves the support cardinality exactly. -/
theorem galAct_support_card (c : (ZMod M)ˣ) (v : ZMod M → ℤ) :
    (Finset.univ.filter (fun j => galAct c v j ≠ 0)).card =
      (Finset.univ.filter (fun j => v j ≠ 0)).card := by
  have himg : Finset.univ.filter (fun j => galAct c v j ≠ 0) =
      (Finset.univ.filter (fun j => v j ≠ 0)).image (fun i => (c : (ZMod M)ˣ) • i) := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro hj
      exact ⟨(c⁻¹ : (ZMod M)ˣ) • j, hj, smul_inv_smul c j⟩
    · rintro ⟨i, hi, rfl⟩
      show v ((c⁻¹ : (ZMod M)ˣ) • ((c : (ZMod M)ˣ) • i)) ≠ 0
      rwa [inv_smul_smul]
  rw [himg, Finset.card_image_of_injective _ (MulAction.injective c)]

/-- The concrete census pool (support ≤ s, height 1) is Galois-stable: the equidistribution
hypotheses are met by the actual r369 candidate pool, not vacuous. -/
theorem galAct_supportLE {s : ℕ} {v : ZMod M → ℤ} (c : (ZMod M)ˣ) (hv : supportLE s v) :
    supportLE s (galAct c v) := by
  unfold supportLE at hv ⊢
  rwa [galAct_support_card]

end ConcretePool

/-- **Determinant witness**: an integer matrix whose zero pattern is a (nontrivial)
permutation pattern can have determinant `-1` — a unit. Multi-embedding vanishing patterns
(zeros at permutation positions mod `𝔭`) force NO `p`-divisibility of a stacked determinant:
the last conceivable transversality amplifier is not forced. -/
theorem permutation_zero_pattern_det_unit :
    Matrix.det !![(0 : ℤ), 1; 1, 0] = -1 := by
  rw [Matrix.det_fin_two_of]
  norm_num

end ArkLib.ProximityGap.Frontier.OCGaloisEmbeddingEquidistribution

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.OCGaloisEmbeddingEquidistribution.evalAt_galAct
#print axioms
  ArkLib.ProximityGap.Frontier.OCGaloisEmbeddingEquidistribution.vanishCount_eq
#print axioms
  ArkLib.ProximityGap.Frontier.OCGaloisEmbeddingEquidistribution.not_poolCoverageConcentrates
#print axioms
  ArkLib.ProximityGap.Frontier.OCGaloisEmbeddingEquidistribution.total_vanishCount_eq_card_mul
#print axioms
  ArkLib.ProximityGap.Frontier.OCGaloisEmbeddingEquidistribution.coverage_all_or_nothing
#print axioms
  ArkLib.ProximityGap.Frontier.OCGaloisEmbeddingEquidistribution.galAct_supportLE
#print axioms
  ArkLib.ProximityGap.Frontier.OCGaloisEmbeddingEquidistribution.wpow_add
#print axioms
  ArkLib.ProximityGap.Frontier.OCGaloisEmbeddingEquidistribution.permutation_zero_pattern_det_unit
