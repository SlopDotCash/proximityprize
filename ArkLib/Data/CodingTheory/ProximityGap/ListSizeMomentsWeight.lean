/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ListSizeMoments

/-!
# Direction A, endpoint: the list-size second moment is determined by the weight enumerator

`ListSizeMoments.lean` proves `second_moment_linear` (`Σ_f |Λ(C,r,f)|² = |C| · Σ_{v∈C} N(v,r)`) and
`pairBall_weight` (over a field, `N(v,r)` depends only on `wt(v) = hammingNorm v`). This file draws the
final consequence — the exact sense in which direction A (Issue #232) reduces the second moment to the
weight enumerator:

* `second_moment_grouped_by_weight` — `Σ_f |Λ|² = |C| · Σ_w Σ_{v∈C, wt v = w} N(v,r)`, the explicit
  weight-grouped form.
* `second_moment_eq_of_weightEnum` — two linear codes with the same cardinality and the same weight
  distribution have the **same** list-size second moment. Since `N` is weight-only, the within-weight
  fibers contribute equally; this is precisely "the second moment is a function of the weight
  enumerator `A_w`". For an MDS / Reed–Solomon code `A_w` is a known closed form, so the second moment
  is then exactly computable. (The remaining gap to the prize is the average-`f`→worst-`f` step.)

`sorry`-free, axiom-clean.
-/

namespace ArkLib.CodingTheory.ListMoments

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Fintype F] [DecidableEq F] [Field F]

/-- `hammingNorm v ≤ |ι|`: the support has at most `|ι|` coordinates. -/
private lemma hammingNorm_le_card (v : ι → F) : hammingNorm v ≤ Fintype.card ι := by
  unfold hammingNorm
  rw [← Finset.card_univ]
  exact Finset.card_filter_le _ _

/-- **Second moment grouped by weight.** For a linear code, the list-size second moment is `|C|` times
a sum over weights `w` of the within-fiber sums of `N` — exhibiting the dependence on the weight
distribution explicitly. -/
theorem second_moment_grouped_by_weight {C : Finset (ι → F)}
    (hadd : ∀ a ∈ C, ∀ b ∈ C, a + b ∈ C) (hsub : ∀ a ∈ C, ∀ b ∈ C, a - b ∈ C) (r : ℕ) :
    ∑ f : ι → F, (lam C r f).card ^ 2
      = C.card • ∑ w ∈ Finset.range (Fintype.card ι + 1),
          ∑ v ∈ C.filter (fun v => hammingNorm v = w),
            (Finset.univ.filter
              (fun g => hammingDist (0 : ι → F) g ≤ r ∧ hammingDist v g ≤ r)).card := by
  rw [second_moment_linear hadd hsub]
  congr 1
  have hmaps : ∀ v ∈ C, hammingNorm v ∈ Finset.range (Fintype.card ι + 1) := by
    intro v _
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact hammingNorm_le_card v
  exact (Finset.sum_fiberwise_of_maps_to hmaps _).symm

/-- **The list-size second moment is determined by the weight enumerator.** Two linear codes with the
same cardinality and the same weight distribution have the same second moment. Since `N(v,r)` depends
only on `wt(v)` (`pairBall_weight`), the within-weight fibers contribute equally — the exact sense in
which direction A reduces the linear-code second moment to the weight enumerator `A_w`. -/
theorem second_moment_eq_of_weightEnum {C C' : Finset (ι → F)}
    (hadd : ∀ a ∈ C, ∀ b ∈ C, a + b ∈ C) (hsub : ∀ a ∈ C, ∀ b ∈ C, a - b ∈ C)
    (hadd' : ∀ a ∈ C', ∀ b ∈ C', a + b ∈ C') (hsub' : ∀ a ∈ C', ∀ b ∈ C', a - b ∈ C')
    (hcard : C.card = C'.card)
    (hwe : ∀ w, (C.filter (fun v => hammingNorm v = w)).card
                = (C'.filter (fun v => hammingNorm v = w)).card)
    (r : ℕ) :
    ∑ f : ι → F, (lam C r f).card ^ 2 = ∑ f : ι → F, (lam C' r f).card ^ 2 := by
  rw [second_moment_grouped_by_weight hadd hsub, second_moment_grouped_by_weight hadd' hsub', hcard]
  congr 1
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rcases (C.filter (fun v => hammingNorm v = w)).eq_empty_or_nonempty with hE | ⟨v0, hv0⟩
  · have hE' : (C'.filter (fun v => hammingNorm v = w)) = ∅ :=
      Finset.card_eq_zero.mp (by rw [← hwe w, hE, Finset.card_empty])
    simp only [hE, hE', Finset.sum_empty]
  · have hw0 : hammingNorm v0 = w := (Finset.mem_filter.mp hv0).2
    have hconst : ∀ (D : Finset (ι → F)), (∀ v ∈ D, hammingNorm v = w) →
        (∑ v ∈ D, (Finset.univ.filter
            (fun g => hammingDist (0 : ι → F) g ≤ r ∧ hammingDist v g ≤ r)).card)
          = D.card • (Finset.univ.filter
            (fun g => hammingDist (0 : ι → F) g ≤ r ∧ hammingDist v0 g ≤ r)).card := by
      intro D hD
      rw [← Finset.sum_const]
      exact Finset.sum_congr rfl
        (fun v hv => pairBall_weight (by rw [hD v hv, hw0]) r)
    rw [hconst _ (fun v hv => (Finset.mem_filter.mp hv).2),
        hconst _ (fun v hv => (Finset.mem_filter.mp hv).2), hwe w]

end ArkLib.CodingTheory.ListMoments
