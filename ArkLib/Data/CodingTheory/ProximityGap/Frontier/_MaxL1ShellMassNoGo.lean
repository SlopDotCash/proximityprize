/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R320KernelRelationL1Sparsity
import Mathlib.Data.Fintype.CardEmbedding

/-!
# Maximal-L1 shell mass: a no-go for support/L1-only summation

The R321 relation weight is the depth-`2r` signed-walk histogram `NR(d)`.  R322's
factorial envelope makes an individual endpoint small when its `L1` length is large.
This file records the compensating entropy exactly enough to delimit that route.

At depth `L`, consider tuples whose `L` underlying coordinates in `Fin m` are distinct;
the signs are arbitrary.  There are

```text
  2^L * m.descFactorial L
```

such tuples, and every one ends on the maximal shell `shadowL1(d) = L`.  Consequently

```text
  2^L * m.descFactorial L
    <= sum_{shadowL1(d)=L} NR(2m,m,L,d).
```

Thus support and `L1` decay alone cannot provide the missing `1/q` selection: when
`L << sqrt(m)`, the maximal shell already carries almost all `(2m)^L` walks.  A winning
weighted recurrence argument must use the finite-field kernel condition inside the shell,
not merely the universal coefficient sparsity `shadowL1(d) <= L`.

Issue #466.  Axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.MaxL1ShellMassNoGo

open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor
open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.R320KernelRelationL1Sparsity

/-- Decompose a signed-basis index into its sign and its underlying coordinate. -/
def signedDecompose (m : ℕ) : Fin (2 * m) ≃ Fin 2 × Fin m :=
  finProdFinEquiv.symm

/-- The underlying unsigned coordinate of a signed-basis index. -/
def signedCoordinate (m : ℕ) (a : Fin (2 * m)) : Fin m :=
  (signedDecompose m a).2

/-- The sign bit of a signed-basis index. -/
def signedPolarity (m : ℕ) (a : Fin (2 * m)) : Fin 2 :=
  (signedDecompose m a).1

/-- The integer sign represented by a polarity bit. -/
def polarityValue (s : Fin 2) : ℤ :=
  if s = 0 then 1 else -1

/-- Signed-product indexing is exactly the signed standard basis used by `vecOf`. -/
theorem vecOf_finProdFinEquiv (m : ℕ) (s : Fin 2) (i j : Fin m) :
    vecOf (2 * m) m (finProdFinEquiv (s, i)) j =
      if i = j then polarityValue s else 0 := by
  fin_cases s <;> simp [vecOf, polarityValue, finProdFinEquiv] <;> omega

/-- Every signed-basis vector has exactly unit `L1` mass. -/
theorem shadowL1_vecOf_eq_one (m : ℕ) (a : Fin (2 * m)) :
    shadowL1 (vecOf (2 * m) m a) = 1 := by
  let s := signedPolarity m a
  let i := signedCoordinate m a
  have ha : finProdFinEquiv (s, i) = a := by
    exact (signedDecompose m).symm_apply_apply a
  rw [← ha]
  unfold shadowL1
  rw [Fintype.sum_eq_single i]
  · rw [vecOf_finProdFinEquiv, if_pos rfl]
    by_cases hs : s = 0 <;> simp [polarityValue, hs]
  · intro j hji
    rw [vecOf_finProdFinEquiv, if_neg]
    · simp
    · exact Ne.symm hji

/-- If at most one summand is nonzero, `natAbs` commutes with the finite sum. -/
theorem natAbs_sum_eq_sum_natAbs_of_atMostOne {L : ℕ} (f : Fin L → ℤ)
    (h : ∀ i k, i ≠ k → f i ≠ 0 → f k = 0) :
    (∑ i, f i).natAbs = ∑ i, (f i).natAbs := by
  classical
  by_cases hex : ∃ i, f i ≠ 0
  · obtain ⟨i, hi⟩ := hex
    rw [Fintype.sum_eq_single i]
    · rw [Fintype.sum_eq_single i]
      intro k hki
      rw [h i k (Ne.symm hki) hi]
      simp
    · intro k hki
      exact h i k (Ne.symm hki) hi
  · have hzero : ∀ i, f i = 0 := by
      intro i
      by_contra hi
      exact hex ⟨i, hi⟩
    simp_rw [hzero]
    simp

/-- Distinct underlying coordinates prevent all cancellation, so the tuple reaches the
maximal possible `L1` shell. -/
theorem shadowL1_tupleVec_eq_depth_of_signedCoordinate_injective
    (m L : ℕ) (t : Fin L → Fin (2 * m))
    (ht : Function.Injective (fun i ↦ signedCoordinate m (t i))) :
    shadowL1 (tupleVec (2 * m) m L t) = L := by
  unfold shadowL1 tupleVec
  calc
    (∑ j : Fin m, (∑ i : Fin L, vecOf (2 * m) m (t i) j).natAbs)
        = ∑ j : Fin m, ∑ i : Fin L, (vecOf (2 * m) m (t i) j).natAbs := by
          refine Finset.sum_congr rfl (fun j _ ↦ ?_)
          apply natAbs_sum_eq_sum_natAbs_of_atMostOne
          intro i k hik hi
          let si := signedPolarity m (t i)
          let ci := signedCoordinate m (t i)
          let sk := signedPolarity m (t k)
          let ck := signedCoordinate m (t k)
          have hti : finProdFinEquiv (si, ci) = t i :=
            (signedDecompose m).symm_apply_apply (t i)
          have htk : finProdFinEquiv (sk, ck) = t k :=
            (signedDecompose m).symm_apply_apply (t k)
          have hcij : ci = j := by
            rw [← hti, vecOf_finProdFinEquiv] at hi
            split at hi
            · assumption
            · simp at hi
          rw [← htk, vecOf_finProdFinEquiv]
          rw [if_neg]
          intro hckj
          apply hik
          apply ht
          exact hcij.trans hckj.symm
    _ = ∑ i : Fin L, ∑ j : Fin m, (vecOf (2 * m) m (t i) j).natAbs := by
      rw [Finset.sum_comm]
    _ = ∑ _i : Fin L, 1 := by
      refine Finset.sum_congr rfl (fun i _ ↦ ?_)
      exact shadowL1_vecOf_eq_one m (t i)
    _ = L := by simp

/-- Tuples with no repeated underlying coordinate. -/
noncomputable def distinctCoordinateTuples (m L : ℕ) :
    Finset (Fin L → Fin (2 * m)) :=
  (Finset.univ : Finset (Fin L → Fin (2 * m))).filter
    (fun t ↦ Function.Injective (fun i ↦ signedCoordinate m (t i)))

/-- A distinct-coordinate signed tuple is equivalently an embedding of coordinates plus
an independent sign choice at every time. -/
def distinctCoordinateTupleEquiv (m L : ℕ) :
    {t : Fin L → Fin (2 * m) //
        Function.Injective (fun i ↦ signedCoordinate m (t i))} ≃
      (Fin L ↪ Fin m) × (Fin L → Fin 2) where
  toFun t :=
    (⟨fun i ↦ signedCoordinate m (t.1 i), t.2⟩,
      fun i ↦ signedPolarity m (t.1 i))
  invFun p :=
    ⟨fun i ↦ finProdFinEquiv (p.2 i, p.1 i), by
      intro i j hij
      exact p.1.injective (by
        simpa [signedCoordinate, signedDecompose] using hij)⟩
  left_inv t := by
    apply Subtype.ext
    funext i
    exact (signedDecompose m).symm_apply_apply (t.1 i)
  right_inv p := by
    apply Prod.ext
    · ext i
      simp [signedCoordinate, signedDecompose]
    · funext i
      simp [signedPolarity, signedDecompose]

/-- Exact number of distinct-coordinate signed tuples. -/
theorem distinctCoordinateTuples_card (m L : ℕ) :
    (distinctCoordinateTuples m L).card = m.descFactorial L * 2 ^ L := by
  classical
  unfold distinctCoordinateTuples
  rw [← Fintype.card_subtype
    (fun t : Fin L → Fin (2 * m) ↦
      Function.Injective (fun i ↦ signedCoordinate m (t i)))]
  rw [Fintype.card_congr (distinctCoordinateTupleEquiv m L)]
  simp [Fintype.card_embedding_eq]

/-- The maximal-`L1` endpoint shell at depth `L`. -/
noncomputable def maxL1Shell (m L : ℕ) : Finset (Fin m → ℤ) :=
  (keysR (2 * m) m L).filter (fun v ↦ shadowL1 v = L)

/-- Every maximal-shell endpoint already obeys the strongest universal support bound. -/
theorem support_card_le_depth_of_mem_maxL1Shell
    (m L : ℕ) {v : Fin m → ℤ} (hv : v ∈ maxL1Shell m L) :
    (shadowSupport v).card ≤ L := by
  have hvL1 : shadowL1 v = L := (Finset.mem_filter.mp hv).2
  exact (shadowSupport_card_le_l1 v).trans_eq hvL1

/-- At positive depth the maximal shell contains no zero relation. -/
theorem zero_not_mem_maxL1Shell (m L : ℕ) (hL : 0 < L) :
    (0 : Fin m → ℤ) ∉ maxL1Shell m L := by
  intro hzero
  have hL1 : shadowL1 (0 : Fin m → ℤ) = L := (Finset.mem_filter.mp hzero).2
  simp [shadowL1] at hL1
  omega

/-- Tuples whose endpoint lies on the maximal-`L1` shell. -/
noncomputable def maxL1Tuples (m L : ℕ) : Finset (Fin L → Fin (2 * m)) :=
  (Finset.univ : Finset (Fin L → Fin (2 * m))).filter
    (fun t ↦ shadowL1 (tupleVec (2 * m) m L t) = L)

/-- Restricting the histogram to a shell exactly counts the tuples landing on it. -/
theorem sum_NR_maxL1Shell_eq_card_maxL1Tuples (m L : ℕ) :
    ∑ v ∈ maxL1Shell m L, NR (2 * m) m L v = (maxL1Tuples m L).card := by
  classical
  symm
  rw [Finset.card_eq_sum_card_fiberwise
    (t := maxL1Shell m L) (f := tupleVec (2 * m) m L) (fun t ht ↦ ?_)]
  · refine Finset.sum_congr rfl (fun v hv ↦ ?_)
    unfold NR maxL1Tuples
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨_hshell, ht⟩
      exact ht
    · intro ht
      refine ⟨?_, ht⟩
      rw [ht]
      exact (Finset.mem_filter.mp hv).2
  · have ht' : shadowL1 (tupleVec (2 * m) m L t) = L := by
      simpa [maxL1Tuples] using ht
    have hkey : tupleVec (2 * m) m L t ∈ keysR (2 * m) m L :=
      Finset.mem_image_of_mem _ (Finset.mem_univ t)
    simpa [maxL1Shell] using And.intro hkey ht'

/-- Distinct-coordinate tuples are contained in the maximal-`L1` tuple shell. -/
theorem distinctCoordinateTuples_subset_maxL1Tuples (m L : ℕ) :
    distinctCoordinateTuples m L ⊆ maxL1Tuples m L := by
  intro t ht
  unfold distinctCoordinateTuples at ht
  unfold maxL1Tuples
  rw [Finset.mem_filter] at ht ⊢
  exact ⟨Finset.mem_univ t,
    shadowL1_tupleVec_eq_depth_of_signedCoordinate_injective m L t ht.2⟩

/-- **MAXIMAL-SHELL MASS LOWER BOUND.**  The pointwise factorial/L1 decay is exactly
offset by the entropy of coordinate and sign choices on a large shell. -/
theorem signed_descFactorial_le_sum_NR_maxL1Shell (m L : ℕ) :
    m.descFactorial L * 2 ^ L ≤
      ∑ v ∈ maxL1Shell m L, NR (2 * m) m L v := by
  rw [sum_NR_maxL1Shell_eq_card_maxL1Tuples, ← distinctCoordinateTuples_card]
  exact Finset.card_le_card (distinctCoordinateTuples_subset_maxL1Tuples m L)

/-- A convenient elementary lower bound: if `L ≤ m`, the maximal shell mass is at least
`2^L * (m+1-L)^L`. -/
theorem signed_pow_sub_le_sum_NR_maxL1Shell (m L : ℕ) (_hL : L ≤ m) :
    2 ^ L * (m + 1 - L) ^ L ≤
      ∑ v ∈ maxL1Shell m L, NR (2 * m) m L v := by
  calc
    2 ^ L * (m + 1 - L) ^ L
        ≤ 2 ^ L * m.descFactorial L :=
          Nat.mul_le_mul_left _ (Nat.pow_sub_le_descFactorial m L)
    _ = m.descFactorial L * 2 ^ L := Nat.mul_comm _ _
    _ ≤ ∑ v ∈ maxL1Shell m L, NR (2 * m) m L v :=
      signed_descFactorial_le_sum_NR_maxL1Shell m L

/-- **CLEARED-DC NO-GO.**  Under the displayed elementary size condition, the universal
maximal-`L1` shell already has at least the `1/q` share of total walk mass required by the
DC term.  Hence summing an `L1`/support-only envelope over all admissible endpoints cannot
prove a strict saving at the prize scale; the kernel arithmetic must select roughly a
`1/q` fraction from inside this shell. -/
theorem total_walk_mass_le_field_mul_sum_NR_maxL1Shell
    (m L q : ℕ) (hL : L ≤ m)
    (hsize : m ^ L ≤ q * (m + 1 - L) ^ L) :
    (2 * m) ^ L ≤
      q * ∑ v ∈ maxL1Shell m L, NR (2 * m) m L v := by
  have hshell := signed_pow_sub_le_sum_NR_maxL1Shell m L hL
  calc
    (2 * m) ^ L = 2 ^ L * m ^ L := by rw [mul_pow]
    _ ≤ 2 ^ L * (q * (m + 1 - L) ^ L) := Nat.mul_le_mul_left _ hsize
    _ = q * (2 ^ L * (m + 1 - L) ^ L) := by ring
    _ ≤ q * ∑ v ∈ maxL1Shell m L, NR (2 * m) m L v :=
      Nat.mul_le_mul_left q hshell

end ArkLib.ProximityGap.Frontier.MaxL1ShellMassNoGo

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.MaxL1ShellMassNoGo.shadowL1_tupleVec_eq_depth_of_signedCoordinate_injective
#print axioms
  ArkLib.ProximityGap.Frontier.MaxL1ShellMassNoGo.distinctCoordinateTuples_card
#print axioms
  ArkLib.ProximityGap.Frontier.MaxL1ShellMassNoGo.sum_NR_maxL1Shell_eq_card_maxL1Tuples
#print axioms
  ArkLib.ProximityGap.Frontier.MaxL1ShellMassNoGo.signed_descFactorial_le_sum_NR_maxL1Shell
#print axioms
  ArkLib.ProximityGap.Frontier.MaxL1ShellMassNoGo.signed_pow_sub_le_sum_NR_maxL1Shell
#print axioms
  ArkLib.ProximityGap.Frontier.MaxL1ShellMassNoGo.total_walk_mass_le_field_mul_sum_NR_maxL1Shell
