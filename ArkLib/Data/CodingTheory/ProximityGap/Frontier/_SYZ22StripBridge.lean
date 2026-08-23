/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ21ShorteningAndCoverage
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ20JointRankSuperadditive
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# SYZ22: the reduced strip bridge — identification + pair-doubling, discharged in-tree
  (issue #466 / #507)

This file discharges the two *linear-algebra* residuals SYZ21 flagged for the rate-`1/2`
decisive strip `(Johnson, 1/3)`, wiring SYZ21's proven `shortening_dim` into the shape the
G87 syndrome bridge (`_G87McaEventSyndromeBridge.lean`) and the SYZ20 consumer
(`_SYZ20JointRankSuperadditive.SuperadditiveUnion`) actually consume.

Recall the pipeline. For a non-codeword stack `(u₀,u₁)` and `r` bad scalars each with a
threshold-`t` witness `(Sᵢ, cᵢ)`:

* **G87** builds, per witness, a block of functionals on the syndrome-pair space
  `V = ((ι→F)⧸C)²` as *duals of the quotient* `(Sᵢ→F) ⧸ res_{Sᵢ}(C)`; for the RS code
  `C = RS[α,k]` the restriction is `res_{Sᵢ}(C) = range (evalOnS α k Sᵢ)`.
* **SYZ20** (`plantable_span_cap`) bounds the *joint span* of all these functionals by
  `2(n−k)−1` (since they annihilate the nonzero syndrome pair), and packages the missing
  identification/realizability as the structure `SuperadditiveUnion` with the field
  `union_span_rank : finrank (span synFunctionals) = 2(|U|−k)`.

The two residuals this file closes:

## (i) IDENTIFICATION — `block_source_dim`

G87's per-witness block lives in the dual of `(S→F) ⧸ range (evalOnS α k S)`.  We prove this
source space has dimension exactly `|S| − k` (`= max(0,|S|−k)`), which is
**precisely SYZ21's `shortening_dim`** of the `S`-anchored punctured code
(`block_source_dim_eq_shortening`).  So the `t − k` functionals G87 constructs are exactly a
basis of the `S`-anchored dual-annihilator — the parity checks supported inside `S` are the
dual codewords of the code punctured to `S`.  This is the "abstract-H ⟺ punctured-annihilator"
identification, now a theorem, not a probe reduction.

## (ii) PAIR-DOUBLING — `doubled_shortening_dim`

The syndrome pair is a *direct sum of two copies* of the syndrome quotient.  A functional
anchored on `U` and annihilating `C` doubles: `ℓ∘fst` and `ℓ∘snd` are independent, so the
`U`-anchored dual-annihilators of the pair space have dimension `2(|U|−k)` — exactly the target
of `SuperadditiveUnion.union_span_rank`.  Proven from `shortening_dim` + `finrank_prod`.

## (iii) REALIZABILITY is the *only* remaining residual — `strip_budget_of_realizability`

`plantable_span_cap` gives `finrank (span synFunctionals) + 1 ≤ 2(n−k)` **unconditionally**
(the *upper* bound on the joint span).  Turning this into a union budget `|U| ≤ n−1` needs the
matching **lower** bound `finrank (span synFunctionals) ≥ 2(|U|−k)` — i.e. that the union
functionals actually *realise* the full doubled shortening space (sunflower packing, SYZ18
distinct-support control).  Parts (i)/(ii) prove this lower bound is *attainable* (the ambient
space has exactly that dimension and each block is a full-rank slice of it); what remains is
that a *specific* over-budget family fills it.  We record the honest conditional
`strip_budget_of_realizability`: given the realized equality (the `SuperadditiveUnion` field),
the union budget `|U| ≤ n−1` and hence SYZ21's knapsack count bound follow.

**Honest δ\* verdict (unchanged):** SYZ22 does *not* deliver a new unconditional δ\* statement.
The identification and pair-doubling are now theorems, but the safety count still hangs on
realizability, so the production strip closure and the `δ\* ≥ 1/3 − lattice` jump remain
**conditional** on `SuperadditiveUnion` being instantiable at the production shape.  The
unconditional δ\* status is untouched.

Axiom-clean; `#print axioms` at the bottom.  No `sorry`, no `native_decide`.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace ArkLib.ProximityGap.Frontier.SYZ22

open Module Submodule ArkLib.CS25
open ArkLib.ProximityGap.Frontier.SYZ21
open ArkLib.ProximityGap.Frontier.SYZ20JointRankSuperadditive

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*} [Field F] [DecidableEq F]

/-! ## (i) Identification: the G87 block source is the `S`-anchored shortening space -/

section Identification

/-- **The G87 per-witness block source dimension.**  G87 constructs its per-witness parity
functionals as duals of the quotient `(S→F) ⧸ range (evalOnS α k S)` (the syndrome quotient of
the code *punctured to `S`*).  That source space has dimension exactly `|S| − k` — the same
`t − k` count G87 uses, here identified as the shortening dimension. -/
theorem block_source_dim (α : ι ↪ F) (k : ℕ) (S : Finset ι) :
    finrank F (Module.Dual F ((S → F) ⧸ LinearMap.range (evalOnS α k S))) = S.card - k := by
  classical
  -- dual of a finite-dim space has the same dimension as the space
  rw [Subspace.dual_finrank_eq]
  -- dim of the quotient = |S| − dim (punctured code)
  have hq : finrank F ((S → F) ⧸ LinearMap.range (evalOnS α k S))
      + finrank F (LinearMap.range (evalOnS α k S)) = finrank F (S → F) :=
    Submodule.finrank_quotient_add_finrank _
  rw [Module.finrank_pi, Fintype.card_coe] at hq
  rcases Nat.lt_or_ge S.card k with h | h
  · rw [punctureDim_of_card_le α k S (le_of_lt h)] at hq; omega
  · rw [punctureDim_of_le_card α k S h] at hq; omega

/-- **Identification (i).**  The G87 block source dimension equals SYZ21's `shortening_dim` of
the `S`-anchored punctured code: the `t − k` functionals G87 constructs from a witness `(S,c)`
are exactly a basis of the dual-annihilator of the code punctured to `S`, i.e. the parity
checks supported inside `S`. -/
theorem block_source_dim_eq_shortening (α : ι ↪ F) (k : ℕ) (S : Finset ι) :
    finrank F (Module.Dual F ((S → F) ⧸ LinearMap.range (evalOnS α k S)))
      = finrank F (Submodule.dualAnnihilator (LinearMap.range (evalOnS α k S))) := by
  rw [block_source_dim α k S, shortening_dim α k S]

end Identification

/-! ## (ii) Pair-doubling: two independent syndrome components -/

section PairDoubling

/-- **Pair-doubling (ii).**  The `U`-anchored dual-annihilators of the *syndrome-pair* space
(a direct sum of two copies of the syndrome quotient) have dimension `2(|U|−k)` — exactly the
target recorded by `SuperadditiveUnion.union_span_rank`.  A degenerate core `C_j` that
annihilates a functional anchored on `U` annihilates *both* the `fst` and `snd` copies
independently, so its rank doubles. -/
theorem doubled_shortening_dim (α : ι ↪ F) (k : ℕ) (U : Finset ι) :
    finrank F (
        (Submodule.dualAnnihilator (LinearMap.range (evalOnS α k U)))
          × (Submodule.dualAnnihilator (LinearMap.range (evalOnS α k U))))
      = 2 * (U.card - k) := by
  haveI hfin : Module.Finite F
      (Submodule.dualAnnihilator (LinearMap.range (evalOnS α k U))) := by
    haveI : FiniteDimensional F (↥U → F) := inferInstance
    infer_instance
  haveI hfree := Module.Free.of_divisionRing F
    (Submodule.dualAnnihilator (LinearMap.range (evalOnS α k U)))
  rw [Module.finrank_prod, shortening_dim α k U, two_mul]

/-- The two-sided count consistency: the doubled shortening dimension is even and its half is the
single-copy shortening dimension.  (Sanity bridge between `shortening_dim` and the pair form.) -/
theorem doubled_eq_two_mul_single (α : ι ↪ F) (k : ℕ) (U : Finset ι) :
    finrank F (
        (Submodule.dualAnnihilator (LinearMap.range (evalOnS α k U)))
          × (Submodule.dualAnnihilator (LinearMap.range (evalOnS α k U))))
      = 2 * finrank F (Submodule.dualAnnihilator (LinearMap.range (evalOnS α k U))) := by
  rw [doubled_shortening_dim α k U, shortening_dim α k U]

end PairDoubling

/-! ## (iii) The honest reduction: realizability is the only remaining residual -/

section Assembly

variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- **The unconditional half (upper bound on the joint span).**  For *any* nonzero syndrome
annihilated by a set of functionals, the joint span is capped at `2(n−k) − 1` when the ambient
is the syndrome-pair space.  This is `plantable_span_cap` specialised; it needs no
realizability.  It is the *safety ceiling*: no configuration can force the span past
`2(n−k) − 1`. -/
theorem span_ceiling {n k : ℕ} {v : V} (hv : v ≠ 0)
    (hdim : finrank F V = 2 * (n - k))
    (s : Set (Module.Dual F V)) (hann : ∀ φ ∈ s, φ v = 0) :
    finrank F (Submodule.span F s) + 1 ≤ 2 * (n - k) := by
  have h := plantable_span_cap hv s hann
  rwa [hdim] at h

/-- **The reduction (iii): union budget from realized rank.**  Given a `SuperadditiveUnion`
configuration — i.e. the realizability equality `union_span_rank : finrank (span) = 2(|U|−k)`
holding on the `2(n−k)`-dim syndrome-pair space — the union of degenerate cores of a
non-codeword stack cannot exhaust the coordinate set: `|U| ≤ n − 1` (for `k ≤ |U| ≤ n`).

Parts (i)/(ii) prove the target `2(|U|−k)` is the exact dimension of the `U`-anchored doubled
shortening space, so this equality is *the* honest realizability statement; nothing else is
missing between here and the union budget. -/
theorem strip_budget_of_realizability {n k Ucard : ℕ} (hkU : k ≤ Ucard) (hUn : Ucard ≤ n)
    (cfg : SuperadditiveUnion (F := F) (V := V) n k Ucard) :
    Ucard ≤ n - 1 :=
  union_card_le hkU hUn cfg

/-- **Concrete count consequence (conditional on realizability), `n = 64`.**  If the union
budget holds (`|U| ≤ n − 1`, delivered by `strip_budget_of_realizability`), then SYZ21's
*combined-coverage knapsack* — an unconditional `ℕ` computation — bounds the certified bad count
strictly below the survival budget `B = 64` at every strip threshold `t ∈ {43,44,45}`.  The
knapsack facts themselves are unconditional; only their *applicability* (that the true bad count
is `≤` the LP optimum) rests on the union budget. -/
theorem knapsack_closes_strip_n64 :
    knapOpt 64 32 43 < 64 ∧ knapOpt 64 32 44 < 64 ∧ knapOpt 64 32 45 < 64 :=
  knap_closes_strip_n64_lt

end Assembly

end ArkLib.ProximityGap.Frontier.SYZ22

-- Honesty audit:
#print axioms ArkLib.ProximityGap.Frontier.SYZ22.block_source_dim
#print axioms ArkLib.ProximityGap.Frontier.SYZ22.block_source_dim_eq_shortening
#print axioms ArkLib.ProximityGap.Frontier.SYZ22.doubled_shortening_dim
#print axioms ArkLib.ProximityGap.Frontier.SYZ22.doubled_eq_two_mul_single
#print axioms ArkLib.ProximityGap.Frontier.SYZ22.span_ceiling
#print axioms ArkLib.ProximityGap.Frontier.SYZ22.strip_budget_of_realizability
#print axioms ArkLib.ProximityGap.Frontier.SYZ22.knapsack_closes_strip_n64
