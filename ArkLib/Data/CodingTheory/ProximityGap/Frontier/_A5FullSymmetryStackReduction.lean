/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._StackOrbitRepresentativeReduction

/-!
# The A5 equivariance pin: the FULL symmetry group as a count-level invariance, and the
exact orbit-representative reduction of universal stack domination (R3)

`_StackOrbitRepresentativeReduction.lean` proved that the *affine-rotation* group
(`stackBadCount_affine_rotate`: code-rotation `σ` plus the `2×2` affine reparametrization
`(u₀,u₁) ↦ (a•u₀∘σ + b•u₁∘σ, c•u₁∘σ)`) preserves the actual bad-scalar count `StackBadCount`
exactly, and packaged the orbit-quotient collapse
`worstCaseIncidenceBounded_iff_representativeStacksBounded`.

**The missing generator.** `MCAEquivariance.lean` proves codeword translation invariance only at
the *probability* level (`prob_mcaEvent_translate`).  The count-level analogue
`stackBadCount_translate` — translating the stack by a codeword pair `(u₀,u₁) ↦ (u₀+c₀, u₁+c₁)`,
`c₀,c₁ ∈ C`, preserves `StackBadCount` — was absent.  This is the generator that drives the
*decisive* collapse: with it the orbit count of the symmetry group on the stack space drops from
`Θ(q^{2n−3}/n)` to the **`q`-independent** syndrome-space count `Θ(q^{2m−3}/n)`, `m = n−k`
(numerically verified: full-group orbit count is constant in `p` for fixed `(n,k)` — 4/10 across
`p=5,7,11,13`, `n=4`, `k=2` — and grows only with `m`: 7,27,121,891 at `m=2,3,4,5`,
`probe_orbit_cover.py`/`probe_m_scaling.py`).

This file:

1. proves `stackBadCount_translate` (the missing count-level invariance) from the proven
   per-`γ` event invariance `mcaEvent_translate`;
2. defines the **full symmetry transform** `fullSymStack` = affine-rotation ∘ codeword
   translation, and proves `stackBadCount_fullSym` (it preserves `StackBadCount` exactly);
3. packages the full symmetry as a `StackCountInvariantRel` (`fullSymRel`,
   `stackCountInvariantRel_fullSymRel`), so the existing quotient engine applies verbatim;
4. records the **exact R3 reduction** `worstCaseIncidenceBounded_iff_fullSymRepresentativeBound`:
   under a finite full-symmetry representative cover, the universal floor input
   `WorstCaseIncidenceBounded` (the open core N6) is *equivalent* to bounding the representatives,
   and `deltaStar_pin_of_fullSymRepresentativeBound` feeds the delta-star lower pin from a bounded
   representative cover.

## Honest scope (does this bypass the Paley wall?)

**No.**  This is a `cross-cutting` *reduction-of-the-quantifier*, not a bound.  The equivariance
pin reduces "bound every stack" to "bound one representative per full-symmetry orbit".  The
number of orbits is `q`-independent but grows like `q^{2m−3}/n`; at the prize instance
`m = n−k = Θ(n)`, `n = 2³⁰`, this is astronomically many representatives.  Bounding even one
true global-maximizer representative is still exactly `WorstCaseIncidenceBounded` = Face 3 = the
generalized-Paley sup-norm = the wall (`FloorNecessaryNotSufficient`: a one-direction bound is not
a worst-case bound without a maximizer proof).  What the pin *does* genuinely buy: it makes the
floor input `p`-uniform (one proof handles all primes carrying the period) and pins the residual
to the syndrome geometry, the right home for an `m`-induction.

## References
- [ABF26] ePrint 2026/680, §4.5 `mcaConjecture`.  Issue #334 A5 (orbit-reduced exact profile).
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code
open ProximityGap.MCAEquivariance

namespace ArkLib.ProximityGap.Frontier.A5FullSymmetryStackReduction

open ArkLib.ProximityGap.Frontier.StackOrbitRepresentativeReduction

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## The missing generator: count-level codeword-translation invariance -/

/-- **Codeword translation preserves the actual bad-scalar count.** Translating a stack by a pair
of codewords `(u₀,u₁) ↦ (u₀+c₀, u₁+c₁)`, `c₀,c₁ ∈ C`, leaves `StackBadCount` unchanged.  This is
the count-level analogue of `prob_mcaEvent_translate`; it was the one symmetry generator absent at
the count level in `_StackOrbitRepresentativeReduction.lean`. -/
theorem stackBadCount_translate
    (C : Submodule F (ι → F)) (δ : ℝ≥0)
    (u₀ u₁ : ι → F) {c₀ c₁ : ι → F} (hc₀ : c₀ ∈ C) (hc₁ : c₁ ∈ C) :
    StackBadCount F (C : Set (ι → F)) δ ![u₀ + c₀, u₁ + c₁]
      = StackBadCount F (C : Set (ι → F)) δ ![u₀, u₁] := by
  classical
  unfold StackBadCount
  congr 1
  ext γ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  exact mcaEvent_translate C hc₀ hc₁ γ

/-! ## The full symmetry transform: affine-rotation composed with codeword translation -/

/-- The full symmetry transform: a code-preserving permutation `σ`, an upper-triangular affine
reparametrization `(a,b,c)` with `a,c ≠ 0`, and a codeword translation `(c₀,c₁)`. -/
def fullSymStack (σ : Equiv.Perm ι) (a b c : F) (c₀ c₁ : ι → F)
    (u : WordStack F (Fin 2) ι) : WordStack F (Fin 2) ι :=
  ![a • (u 0 ∘ ⇑σ) + b • (u 1 ∘ ⇑σ) + c₀, c • (u 1 ∘ ⇑σ) + c₁]

/-- **The full symmetry transform preserves the actual bad-scalar count.** Combines
`stackBadCount_affine_rotate` (code rotation + affine reparametrization) with the new
`stackBadCount_translate` (codeword translation), so the entire symmetry group of `mcaEvent`
acts on `StackBadCount` by the identity. -/
theorem stackBadCount_fullSym
    (C : Submodule F (ι → F)) (δ : ℝ≥0)
    (u : WordStack F (Fin 2) ι) (σ : Equiv.Perm ι)
    (hσ : ∀ w ∈ C, w ∘ ⇑σ ∈ C) (hσ' : ∀ w ∈ C, w ∘ ⇑σ⁻¹ ∈ C)
    {a c : F} (ha : a ≠ 0) (hc : c ≠ 0) (b : F)
    {c₀ c₁ : ι → F} (hc₀ : c₀ ∈ C) (hc₁ : c₁ ∈ C) :
    StackBadCount F (C : Set (ι → F)) δ (fullSymStack σ a b c c₀ c₁ u)
      = StackBadCount F (C : Set (ι → F)) δ u := by
  classical
  -- the affine-rotated stack
  set v₀ : ι → F := a • (u 0 ∘ ⇑σ) + b • (u 1 ∘ ⇑σ) with hv₀
  set v₁ : ι → F := c • (u 1 ∘ ⇑σ) with hv₁
  have hbase :
      StackBadCount F (C : Set (ι → F)) δ ![v₀, v₁]
        = StackBadCount F (C : Set (ι → F)) δ u := by
    have h := stackBadCount_affine_rotate C δ u σ hσ hσ' ha hc b
    simpa only [affineRotateStack, hv₀, hv₁] using h
  calc
    StackBadCount F (C : Set (ι → F)) δ (fullSymStack σ a b c c₀ c₁ u)
        = StackBadCount F (C : Set (ι → F)) δ ![v₀ + c₀, v₁ + c₁] := by
          rw [hv₀, hv₁]; rfl
    _ = StackBadCount F (C : Set (ι → F)) δ ![v₀, v₁] :=
          stackBadCount_translate C δ v₀ v₁ hc₀ hc₁
    _ = StackBadCount F (C : Set (ι → F)) δ u := hbase

/-! ## The full symmetry as a count-invariant relation, ready for the quotient engine -/

/-- The full symmetry relation on stacks: `u ~ v` iff `v` is the image of `u` under some full
symmetry transform.  Its reflexivity (identity transform) is built in. -/
def fullSymRel (C : Submodule F (ι → F))
    (u v : WordStack F (Fin 2) ι) : Prop :=
  ∃ (σ : Equiv.Perm ι) (a b c : F) (c₀ c₁ : ι → F),
    (∀ w ∈ C, w ∘ ⇑σ ∈ C) ∧ (∀ w ∈ C, w ∘ ⇑σ⁻¹ ∈ C) ∧
      a ≠ 0 ∧ c ≠ 0 ∧ c₀ ∈ C ∧ c₁ ∈ C ∧
      v = fullSymStack σ a b c c₀ c₁ u

/-- **The full symmetry relation preserves the bad-scalar count.** This is the count-invariance
hypothesis (`StackCountInvariantRel`) consumed by the existing orbit-quotient engine, now for the
*entire* symmetry group of `mcaEvent` (the missing translation generator included). -/
theorem stackCountInvariantRel_fullSymRel
    (C : Submodule F (ι → F)) (δ : ℝ≥0) :
    StackCountInvariantRel (F := F) (A := F) (C : Set (ι → F)) δ (fullSymRel C) := by
  intro u v hrel
  obtain ⟨σ, a, b, c, c₀, c₁, hσ, hσ', ha, hc, hc₀, hc₁, rfl⟩ := hrel
  exact (stackBadCount_fullSym C δ u σ hσ hσ' ha hc b hc₀ hc₁).symm

/-! ## The exact R3 orbit-representative reduction of the open floor core -/

/-- **The A5 equivariance pin reduces R3 (universal domination) to representatives — equivalence
form.** Under a finite full-symmetry representative cover `R` of the stack space, the open floor
core `WorstCaseIncidenceBounded C δ B` (the all-stacks bound, equivalently universal stack
domination within budget) is *equivalent* to the finite check that every representative in `R`
has bad-scalar count at most `B`.  The forward direction is automatic; the reverse uses the
proven full-symmetry count-invariance to lift each stack's bound from its representative.

This is the precise statement asked of the A5 node: the Galois/cyclic-shift action on stacks
(here the cyclic domain rotation `σ`, bundled with the affine reparametrization and codeword
translation) commutes with the bad-scalar predicate (`stackBadCount_fullSym`), reducing the
universal domination quantifier to one bound per orbit representative. -/
theorem worstCaseIncidenceBounded_iff_fullSymRepresentativeBound
    (C : Submodule F (ι → F)) (δ : ℝ≥0) (B : ℕ)
    {R : Finset (WordStack F (Fin 2) ι)}
    (hcover : StackRelRepresentativeCover R (fullSymRel C)) :
    ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := F) (C : Set (ι → F)) δ B
      ↔ RepresentativeStacksBounded (F := F) (A := F) (C : Set (ι → F)) δ R B :=
  worstCaseIncidenceBounded_iff_representativeStacksBounded
    (C : Set (ι → F)) δ B (stackCountInvariantRel_fullSymRel C δ) hcover

/-- **The delta-star lower pin from a bounded full-symmetry representative cover.** If a finite set
`R` of stacks covers every full-symmetry orbit and every representative is within budget `B` with
`B/q ≤ ε*`, then `δ ≤ mcaDeltaStar C ε*`.  This is the R3 floor route expressed through the A5
equivariance pin: a floor proof now needs only (i) a finite orbit transversal `R`, (ii) the
budget bound on `R`. -/
theorem deltaStar_pin_of_fullSymRepresentativeBound
    (C : Submodule F (ι → F)) (εstar : ℝ≥0∞) {δ : ℝ≥0} {B : ℕ}
    (hδ : δ ≤ 1)
    {R : Finset (WordStack F (Fin 2) ι)}
    (hcover : StackRelRepresentativeCover R (fullSymRel C))
    (hR : RepresentativeStacksBounded (F := F) (A := F) (C : Set (ι → F)) δ R B)
    (hbudget : (B : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    δ ≤ ProximityGap.MCAThresholdLedger.mcaDeltaStar
        (F := F) (A := F) (C : Set (ι → F)) εstar :=
  deltaStar_pin_of_representativeStacksBounded
    (C : Set (ι → F)) εstar hδ (stackCountInvariantRel_fullSymRel C δ) hcover hR hbudget

/-- **Exact failure certificate.** Under a full-symmetry representative cover, the open floor core
fails at budget `B` *exactly* when some listed representative exceeds budget.  This is the honest
guardrail: the equivariance pin removes the quantifier over all stacks, but the residual is still
an above-budget representative — i.e. the worst-case incidence (Paley) bound on the transversal. -/
theorem not_worstCaseIncidenceBounded_iff_exists_fullSymRepresentative_budget_lt
    (C : Submodule F (ι → F)) (δ : ℝ≥0) (B : ℕ)
    {R : Finset (WordStack F (Fin 2) ι)}
    (hcover : StackRelRepresentativeCover R (fullSymRel C)) :
    (¬ ProximityGap.OpenCoreConditionalPin.WorstCaseIncidenceBounded
        (F := F) (A := F) (C : Set (ι → F)) δ B)
      ↔ ∃ r : WordStack F (Fin 2) ι, r ∈ R ∧
          B < StackBadCount F (C : Set (ι → F)) δ r :=
  not_worstCaseIncidenceBounded_iff_exists_representative_budget_lt_of_invariantRel_cover
    (C : Set (ι → F)) δ B (stackCountInvariantRel_fullSymRel C δ) hcover

/-! ## Axiom audit -/
#print axioms stackBadCount_translate
#print axioms stackBadCount_fullSym
#print axioms stackCountInvariantRel_fullSymRel
#print axioms worstCaseIncidenceBounded_iff_fullSymRepresentativeBound
#print axioms deltaStar_pin_of_fullSymRepresentativeBound
#print axioms not_worstCaseIncidenceBounded_iff_exists_fullSymRepresentative_budget_lt

end ArkLib.ProximityGap.Frontier.A5FullSymmetryStackReduction
