/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin

/-!
# Higher-order (`r`-fold) additive energy

Mathlib's `Finset.addEnergy s t` is the number of quadruples `(a₁, a₂, b₁, b₂) ∈ s × s × t × t`
with `a₁ + b₁ = a₂ + b₂` — the **`2`-fold** additive energy. This file introduces the
**`r`-fold additive energy**

  `addREnergy r s = #{(v, w) ∈ sʳ × sʳ : ∑ᵢ vᵢ = ∑ᵢ wᵢ}`,

the number of pairs of `r`-tuples drawn from `s` with equal sum. It is the basic quantity behind the
`2r`-th moment method for exponential sums and the sum-product / Bourgain–Glibichuk–Konyagin
character-sum estimates. We record its elementary properties, all upstreamable to Mathlib.

The deep content — a *sub-trivial* bound `addREnergy r s ≤ #s ^ (2r-1-κ)` for multiplicative
subgroups (the sum-product theorem) — is NOT here; it requires incidence geometry (Rudnev) absent
from Mathlib. This file is the elementary scaffold those estimates build on.
-/

open Finset Fintype
open scoped BigOperators

namespace Finset

variable {α : Type*} [AddCommMonoid α] [DecidableEq α] {r : ℕ} {s t : Finset α}

/-- The **`r`-fold additive energy** of a finset `s`: the number of pairs of `r`-tuples
`(v, w) ∈ sʳ × sʳ` with `∑ᵢ vᵢ = ∑ᵢ wᵢ`. For `r = 2` this is `Finset.addEnergy s s`. -/
noncomputable def addREnergy (r : ℕ) (s : Finset α) : ℕ :=
  #{x ∈ (piFinset fun _ : Fin r => s) ×ˢ (piFinset fun _ : Fin r => s) |
      ∑ i, x.1 i = ∑ i, x.2 i}

lemma addREnergy_def (r : ℕ) (s : Finset α) :
    addREnergy r s
      = #{x ∈ (piFinset fun _ : Fin r => s) ×ˢ (piFinset fun _ : Fin r => s) |
          ∑ i, x.1 i = ∑ i, x.2 i} := rfl

/-- The `r`-fold additive energy is monotone in the set. -/
@[gcongr]
lemma addREnergy_mono (hst : s ⊆ t) : addREnergy r s ≤ addREnergy r t := by
  unfold addREnergy
  apply card_le_card
  intro x hx
  have hx' := mem_filter.1 hx
  have hxp := mem_product.1 hx'.1
  refine mem_filter.2 ⟨mem_product.2 ⟨?_, ?_⟩, hx'.2⟩
  · exact mem_piFinset.2 (fun i => hst (mem_piFinset.1 hxp.1 i))
  · exact mem_piFinset.2 (fun i => hst (mem_piFinset.1 hxp.2 i))

/-- **Diagonal lower bound:** the `r`-fold additive energy is at least `#s ^ r`, witnessed by the
"diagonal" pairs `(v, v)`. -/
lemma card_pow_le_addREnergy (r : ℕ) (s : Finset α) :
    #s ^ r ≤ addREnergy r s := by
  calc #s ^ r = #(piFinset fun _ : Fin r => s) := (card_piFinset_const s r).symm
    _ ≤ addREnergy r s := by
        unfold addREnergy
        apply card_le_card_of_injOn (fun v => (v, v))
        · intro v hv
          exact mem_filter.2 ⟨mem_product.2 ⟨hv, hv⟩, rfl⟩
        · intro a _ b _ hab
          simpa using congrArg Prod.fst hab

/-- Positivity for nonempty `s`. -/
lemma addREnergy_pos (hs : s.Nonempty) : 0 < addREnergy r s :=
  (pow_pos hs.card_pos r).trans_le (card_pow_le_addREnergy r s)

end Finset

namespace Finset

variable {α : Type*} [AddCommGroup α] [DecidableEq α] {r : ℕ} {s : Finset α}

/-- **Fiber bound (successor form).** The number of `(k+1)`-tuples drawn from `s` with a *fixed*
sum `d` is at most `#s ^ k`: the tuple is determined by its first `k` coordinates, because the last
coordinate is forced by the sum equation. (This is where subtraction — the group structure — is
used.) -/
lemma addREnergy_fiber_succ_le (k : ℕ) (s : Finset α) (d : α) :
    #{v ∈ (piFinset fun _ : Fin (k + 1) => s) | ∑ i, v i = d} ≤ #s ^ k := by
  classical
  rw [← card_piFinset_const s k]
  apply card_le_card_of_injOn (fun v => fun j : Fin k => v j.castSucc)
  · intro v hv
    have hp := mem_piFinset.1 (mem_filter.1 hv).1
    exact mem_piFinset.2 (fun j => hp j.castSucc)
  · intro a ha b hb hab
    have hsa : ∑ i, a i = d := (mem_filter.1 ha).2
    have hsb : ∑ i, b i = d := (mem_filter.1 hb).2
    have hinit : ∀ j : Fin k, a j.castSucc = b j.castSucc := fun j => congrFun hab j
    have hsum_eq : ∑ j : Fin k, a j.castSucc = ∑ j : Fin k, b j.castSucc :=
      Finset.sum_congr rfl (fun j _ => hinit j)
    have ea := Fin.sum_univ_castSucc (fun i => a i)
    have eb := Fin.sum_univ_castSucc (fun i => b i)
    rw [hsa] at ea
    rw [hsb] at eb
    have hlast : a (Fin.last k) = b (Fin.last k) := by
      have h : (∑ j : Fin k, a j.castSucc) + a (Fin.last k)
             = (∑ j : Fin k, b j.castSucc) + b (Fin.last k) := by rw [← ea, ← eb]
      rw [hsum_eq] at h
      exact add_left_cancel h
    funext i
    refine Fin.lastCases ?_ ?_ i
    · exact hlast
    · intro j; exact hinit j

/-- **Trivial upper bound:** the `r`-fold additive energy is at most `#s ^ (2r-1)` (`r ≥ 1`). The
`r` coordinates of `w` and the first `r-1` of `v` are free; the last coordinate of `v` is forced by
`∑ v = ∑ w`. Proven by fibering over `w` and applying `addREnergy_fiber_succ_le`. -/
lemma addREnergy_le (hr : 1 ≤ r) (s : Finset α) :
    addREnergy r s ≤ #s ^ (2 * r - 1) := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  rw [addREnergy_def]
  have hcard :
      #{x ∈ (piFinset fun _ : Fin (k + 1) => s) ×ˢ (piFinset fun _ : Fin (k + 1) => s) |
          ∑ i, x.1 i = ∑ i, x.2 i}
        = ∑ w ∈ (piFinset fun _ : Fin (k + 1) => s),
            #{v ∈ (piFinset fun _ : Fin (k + 1) => s) | ∑ i, v i = ∑ i, w i} := by
    rw [Finset.card_filter, Finset.sum_product, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [Finset.card_filter]
  rw [hcard]
  calc ∑ w ∈ (piFinset fun _ : Fin (k + 1) => s),
          #{v ∈ (piFinset fun _ : Fin (k + 1) => s) | ∑ i, v i = ∑ i, w i}
      ≤ ∑ _w ∈ (piFinset fun _ : Fin (k + 1) => s), #s ^ k :=
        Finset.sum_le_sum (fun w _ => addREnergy_fiber_succ_le k s (∑ i, w i))
    _ = #s ^ (k + 1) * #s ^ k := by
        rw [Finset.sum_const, card_piFinset_const, smul_eq_mul]
    _ = #s ^ (2 * (k + 1) - 1) := by rw [← pow_add]; congr 1; omega

end Finset

-- Axiom audit (expected: propext, Classical.choice, Quot.sound)
#print axioms Finset.addREnergy_mono
#print axioms Finset.card_pow_le_addREnergy
#print axioms Finset.addREnergy_pos
#print axioms Finset.addREnergy_fiber_succ_le
#print axioms Finset.addREnergy_le
