/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G80LEnergyRefinedConsumer

/-!
# G80H: the k-fold multiplicative-energy engine

G80L proves the `k = 2` Cauchy--Schwarz consumer used by the first energy-refined interval
bound.  This file proves the exact finite combinatorial statement at every depth `k`.

For `A : Finset ℕ`, let `Eₖ(A)` count ordered pairs of `k`-tuples with the same integer
product.  Then

```text
  |A|^(2k) ≤ |A^(k products)| * Eₖ(A).
```

The proof partitions the tuple cube into product fibers and applies Cauchy--Schwarz to their
cardinalities.  There are no number-theoretic hypotheses.  The remaining prize-facing work is
to cap the product image by the subgroup size in the no-wrap range and to estimate `Eₖ(A)`
uniformly as `k` grows.  Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G80HKFoldProductEnergy

open Finset Fintype

/-- The integer product of a `k`-tuple. -/
def tupleProduct {k : ℕ} (x : Fin k → ℕ) : ℕ := ∏ i, x i

/-- The set of integer products represented by `k`-tuples from `A`. -/
def productImage (A : Finset ℕ) (k : ℕ) : Finset ℕ :=
  (piFinset fun _ : Fin k => A).image tupleProduct

/-- The k-fold integer multiplicative energy of `A`: the number of ordered pairs of
`k`-tuples from `A` having equal product. -/
def kMulEnergy (A : Finset ℕ) (k : ℕ) : ℕ :=
  #(((piFinset fun _ : Fin k => A) ×ˢ (piFinset fun _ : Fin k => A)).filter
    fun q => tupleProduct q.1 = tupleProduct q.2)

/-- The k-fold energy is the sum of the squares of the product-fiber sizes. -/
theorem kMulEnergy_eq_sum_sq_fibers (A : Finset ℕ) (k : ℕ) :
    kMulEnergy A k =
      ∑ y ∈ productImage A k,
        (#((piFinset fun _ : Fin k => A).filter fun x => tupleProduct x = y)) ^ 2 := by
  classical
  let X : Finset (Fin k → ℕ) := piFinset fun _ : Fin k => A
  let P : Finset ℕ := productImage A k
  let R : ℕ → Finset (Fin k → ℕ) := fun y => X.filter fun x => tupleProduct x = y
  have hsplit :
      ((X ×ˢ X).filter fun q => tupleProduct q.1 = tupleProduct q.2) =
        P.biUnion fun y => R y ×ˢ R y := by
    ext ⟨x, z⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_biUnion, P, R, X,
      productImage, Finset.mem_image]
    constructor
    · rintro ⟨⟨hx, hz⟩, heq⟩
      exact ⟨tupleProduct x, ⟨x, hx, rfl⟩, ⟨⟨hx, rfl⟩, ⟨hz, heq.symm⟩⟩⟩
    · rintro ⟨y, _, ⟨⟨hx, hxy⟩, ⟨hz, hzy⟩⟩⟩
      exact ⟨⟨hx, hz⟩, hxy.trans hzy.symm⟩
  rw [kMulEnergy, show piFinset (fun _ : Fin k => A) = X from rfl, hsplit,
    Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun y _ => ?_
    simp only [R, X, Finset.card_product, sq]
  · intro y _ y' _ hyy'
    refine Finset.disjoint_left.mpr ?_
    rintro ⟨x, z⟩ hm hm'
    simp only [R, Finset.mem_product, Finset.mem_filter] at hm hm'
    exact hyy' (hm.1.2.symm.trans hm'.1.2)

/-- **Generic k-fold Cauchy--Schwarz consumer.** The square of the tuple-cube cardinality is
bounded by the product-image cardinality times k-fold multiplicative energy. -/
theorem card_pow_two_mul_le_productImage_mul_kMulEnergy (A : Finset ℕ) (k : ℕ) :
    A.card ^ (2 * k) ≤ (productImage A k).card * kMulEnergy A k := by
  classical
  let X : Finset (Fin k → ℕ) := piFinset fun _ : Fin k => A
  let P : Finset ℕ := productImage A k
  let r : ℕ → ℕ := fun y => #(X.filter fun x => tupleProduct x = y)
  have hsum : A.card ^ k = ∑ y ∈ P, r y := by
    rw [← Fintype.card_piFinset_const A k]
    change X.card = _
    dsimp [P, productImage, r]
    exact Finset.card_eq_sum_card_image tupleProduct X
  have henergy : kMulEnergy A k = ∑ y ∈ P, r y ^ 2 := by
    rw [kMulEnergy_eq_sum_sq_fibers]
  have hcs : (∑ y ∈ P, r y) ^ 2 ≤ P.card * ∑ y ∈ P, r y ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  calc
    A.card ^ (2 * k) = (A.card ^ k) ^ 2 := by rw [Nat.mul_comm 2 k, pow_mul]
    _ = (∑ y ∈ P, r y) ^ 2 := by rw [hsum]
    _ ≤ P.card * ∑ y ∈ P, r y ^ 2 := hcs
    _ = (productImage A k).card * kMulEnergy A k := by rw [← henergy]

end ArkLib.ProximityGap.Frontier.G80HKFoldProductEnergy

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G80HKFoldProductEnergy.kMulEnergy_eq_sum_sq_fibers
#print axioms
  ArkLib.ProximityGap.Frontier.G80HKFoldProductEnergy.card_pow_two_mul_le_productImage_mul_kMulEnergy
