/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Disjoint-pair (signed-support) count (issue #232)

The engine of the exact characteristic-0 subgroup subset-sum formula `N₀(m, r)` (research note
`06-AVERAGED-PA.md` Theorem A; DISPROOF_LOG O11‴): an ε-pattern on `m2 = m/2` basis pairs is a
disjoint pair `(P, N)` of supports (positive/negative picks), and the number of patterns with
total support `s` is `C(m2, s)·2^s` — choose the support, then the sign pattern. Summing over
admissible `s` (with the both-placement fiber `C(m2−s, (r−s)/2)`, which is `card_powersetCard`)
yields `N₀(m, r) = Σ_s C(m2, s)·2^s` — the formula verified exactly at m = 8, 16 and the
production primes (ledger O11⁗⁺⁺).
-/

open Finset

namespace ArkLib.SmoothDomain

/-- **Disjoint-pair count**: the number of disjoint pairs `(P, N)` of subsets of `Fin m2` with
`|P| + |N| = s` is `C(m2, s) · 2^s` (choose the support, then the sign pattern). -/
theorem disjoint_pair_count (m2 s : ℕ) :
    (((univ : Finset (Finset (Fin m2))) ×ˢ (univ : Finset (Finset (Fin m2)))).filter
      (fun pn => Disjoint pn.1 pn.2 ∧ pn.1.card + pn.2.card = s)).card
      = m2.choose s * 2 ^ s := by
  classical
  have hset :
      (((univ : Finset (Finset (Fin m2))) ×ˢ (univ : Finset (Finset (Fin m2)))).filter
        (fun pn => Disjoint pn.1 pn.2 ∧ pn.1.card + pn.2.card = s))
      = ((univ : Finset (Fin m2)).powersetCard s).biUnion
          (fun S => S.powerset.image (fun P => (P, S \ P))) := by
    ext ⟨P, N⟩
    simp only [mem_filter, mem_product, mem_univ, true_and, mem_biUnion, mem_powersetCard,
      mem_image, mem_powerset]
    constructor
    · rintro ⟨hdisj, hcard⟩
      refine ⟨P ∪ N, ⟨subset_univ _, ?_⟩, P, subset_union_left, ?_⟩
      · rw [card_union_of_disjoint hdisj]; exact hcard
      · rw [union_sdiff_cancel_left hdisj]
    · rintro ⟨S, ⟨-, hScard⟩, Q, hQS, heq⟩
      injection heq with h1 h2
      rw [← h1, ← h2]
      refine ⟨disjoint_sdiff, ?_⟩
      have hc : (S \ Q).card = S.card - (Q ∩ S).card := card_sdiff
      rw [inter_eq_left.mpr hQS] at hc
      have hle : Q.card ≤ S.card := card_le_card hQS
      omega
  rw [hset, card_biUnion]
  · have himg : ∀ S ∈ (univ : Finset (Fin m2)).powersetCard s,
        (S.powerset.image (fun P => (P, S \ P))).card = 2 ^ s := by
      intro S hS
      rw [card_image_of_injective _ (fun a b h => by injection h)]
      rw [card_powerset, (mem_powersetCard.mp hS).2]
    rw [Finset.sum_congr rfl himg, sum_const, card_powersetCard, card_univ,
      Fintype.card_fin]
    simp
  · intro S hS T hT hST
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    rintro ⟨P, N⟩ hPS hPT
    simp only [mem_image, mem_powerset] at hPS hPT
    obtain ⟨Q, hQS, heq⟩ := hPS
    obtain ⟨Q', hQT, heq'⟩ := hPT
    apply hST
    injection heq with e1 e2
    injection heq' with e1' e2'
    have hS' : S = P ∪ N := by rw [← e1, ← e2, union_sdiff_of_subset hQS]
    have hT' : T = P ∪ N := by rw [← e1', ← e2', union_sdiff_of_subset hQT]
    rw [hS', hT']


/-! ## The assembled N₀ pattern count -/


/-- Admissibility of a support size `s` for total pick-count `r` over `m2` pairs. -/
def AdmissibleSupport (m2 r s : ℕ) : Prop :=
  s ≤ r ∧ (r - s) % 2 = 0 ∧ r - s ≤ 2 * (m2 - s)

instance (m2 r s : ℕ) : Decidable (AdmissibleSupport m2 r s) := by
  unfold AdmissibleSupport; infer_instance

/-- **The assembled N₀ count**: disjoint signed-support pairs with admissible support size
number `Σ_s C(m2,s)·2^s` over admissible `s` — the characteristic-0 subset-sum image count. -/
theorem n0_pattern_count (m2 r : ℕ) :
    (((univ : Finset (Finset (Fin m2))) ×ˢ (univ : Finset (Finset (Fin m2)))).filter
      (fun pn => Disjoint pn.1 pn.2 ∧ AdmissibleSupport m2 r (pn.1.card + pn.2.card))).card
      = ∑ s ∈ Finset.range (r + 1),
          if AdmissibleSupport m2 r s then m2.choose s * 2 ^ s else 0 := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun pn : Finset (Fin m2) × Finset (Fin m2) => pn.1.card + pn.2.card)
    (t := Finset.range (r + 1))
    (fun pn hpn => Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Finset.mem_filter.mp hpn).2.2.1))]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  by_cases hadm : AdmissibleSupport m2 r s
  · rw [if_pos hadm, ← disjoint_pair_count m2 s]
    congr 1
    ext pn
    constructor
    · intro h
      have h1 := Finset.mem_filter.mp h
      have h2 := Finset.mem_filter.mp h1.1
      exact Finset.mem_filter.mpr ⟨h2.1, h2.2.1, h1.2⟩
    · intro h
      have h1 := Finset.mem_filter.mp h
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨h1.1, h1.2.1, h1.2.2 ▸ hadm⟩, h1.2.2⟩
  · rw [if_neg hadm, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro pn hmem
    have h1 := Finset.mem_filter.mp hmem
    have h2 := Finset.mem_filter.mp h1.1
    exact hadm (h1.2 ▸ h2.2.2)


end ArkLib.SmoothDomain

#print axioms ArkLib.SmoothDomain.disjoint_pair_count

#print axioms ArkLib.SmoothDomain.n0_pattern_count
