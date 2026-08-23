/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.FoldedSumThreshold
import ArkLib.Data.CodingTheory.ProximityGap.BalancedFourLaw

/-!
# The pair-sums wiring: `e2Folded = 0 ⟺ multiset balance ⟺ antipodal geometry`

Campaign #357. This file welds the three layers of the depth-1 census machinery into one
machine-checked chain:

1. the **arithmetic layer** — `e2Folded m A = 0` (characteristic-zero vanishing of the
   folded `e₂` polynomial, the object of the two-sided depth-1 dictionary
   `depthOne_badScalar_iff_char0`);
2. the **counting layer** — fiberwise antipodal balance of the pair-sum multiset of the
   exponent set reduced into `ZMod (2^m)` (`Balanced`, the object of the balanced-set
   toolkit);
3. the **geometric layer** — at `|A| = 4`, the complete structure law
   (`balanced_pairSums_iff_zmod`): the exponents form an antipodal pair plus a couple
   symmetric about it.

Headlines:
* `count_pairSums_cast` — the pair-sum multiset of the reduced exponents counts exactly
  the `upperPairs` census fibers (the bridge between `Multiset.count` and the
  `Finset.filter` cards of the folded-sum engine);
* `balanced_pairSums_cast_iff` — multiset balance over `ZMod (2^m)` ⟺ the fiberwise
  ℕ-filter balance of `foldedSum_eq_zero_iff_balanced`;
* **`e2Folded_eq_zero_iff_balanced_cast`** — layer 1 ⟺ layer 2, any size;
* **`e2Folded_eq_zero_iff_structured`** — layer 1 ⟺ layer 3 at `|A| = 4`: the census
  subset qualifies **iff** its reduction is `{x, x+h, y, 2x−y}`. Composed with
  `depthOne_badScalar_iff_char0`, the chain *bad scalar ⟺ char-0 census ⟺ antipodal
  geometry* is now machine-checked end to end.

## References

* Probe O145; `probe_balanced_four_law.py`; issue #357.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial Finset
open ArkLib.ProximityGap.KKH26

namespace ArkLib.ProximityGap.WindowTwoLayer

/-! ## The `upperPairs` insertion decomposition -/

/-- Inserting a fresh element adds one pair per old element, oriented by order. -/
theorem upperPairs_insert {a : ℕ} {A : Finset ℕ} (ha : a ∉ A) :
    upperPairs (insert a A)
      = upperPairs A ∪ A.image (fun i => if a < i then (a, i) else (i, a)) := by
  ext q
  simp only [upperPairs, Finset.mem_union, Finset.mem_filter, Finset.mem_product,
    Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro ⟨⟨h1 | h1, h2 | h2⟩, hlt⟩
    · omega
    · exact Or.inr ⟨q.2, h2, by rw [if_pos (h1 ▸ hlt), ← h1]⟩
    · refine Or.inr ⟨q.1, h1, ?_⟩
      rw [if_neg (by omega), ← h2]
    · exact Or.inl ⟨⟨h1, h2⟩, hlt⟩
  · rintro (⟨⟨h1, h2⟩, hlt⟩ | ⟨i, hi, hq⟩)
    · exact ⟨⟨Or.inr h1, Or.inr h2⟩, hlt⟩
    · by_cases hcmp : a < i
      · rw [if_pos hcmp] at hq
        exact ⟨⟨Or.inl (by rw [← hq]), Or.inr (by rw [← hq]; exact hi)⟩,
          by rw [← hq]; exact hcmp⟩
      · rw [if_neg hcmp] at hq
        have hne : i ≠ a := fun hc => ha (hc ▸ hi)
        exact ⟨⟨Or.inr (by rw [← hq]; exact hi), Or.inl (by rw [← hq])⟩,
          by rw [← hq]; simp only; omega⟩

theorem upperPairs_insert_disjoint {a : ℕ} {A : Finset ℕ} (ha : a ∉ A) :
    Disjoint (upperPairs A) (A.image (fun i => if a < i then (a, i) else (i, a))) := by
  rw [Finset.disjoint_left]
  rintro q hq hq'
  obtain ⟨hmem, _⟩ := Finset.mem_filter.mp hq
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp hmem
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hq'
  by_cases hcmp : a < i
  · rw [if_pos hcmp] at hi
    exact ha (by rw [← hi] at h1; exact h1)
  · rw [if_neg hcmp] at hi
    exact ha (by rw [← hi] at h2; exact h2)

/-! ## The count bridge -/

/-- **The pair-sum multiset counts the census fibers.** For any modulus and any target,
the multiplicity of `s` among the pairwise sums of the reduced exponents equals the size
of the `upperPairs` fiber over `s`. -/
theorem count_pairSums_cast {n : ℕ} (A : Finset ℕ) (s : ZMod n) :
    (pairSums (A.val.map (Nat.cast : ℕ → ZMod n))).count s
      = ((upperPairs A).filter (fun q => ((q.1 + q.2 : ℕ) : ZMod n) = s)).card := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [pairSums, upperPairs]
  | insert a A ha ih =>
    rw [Finset.insert_val_of_notMem ha, Multiset.map_cons, pairSums_cons,
      Multiset.count_add, ih, Multiset.map_map]
    have hmap : A.val.map ((fun x => ((a : ℕ) : ZMod n) + x) ∘ (Nat.cast : ℕ → ZMod n))
        = A.val.map (fun i => ((a + i : ℕ) : ZMod n)) :=
      Multiset.map_congr rfl fun i _ => by simp [Nat.cast_add]
    rw [hmap, Multiset.count_map]
    -- the new-pair contribution equals the filtered-element count
    have hnew : Multiset.card
          (Multiset.filter (fun i => s = ((a + i : ℕ) : ZMod n)) A.val)
        = ((A.image (fun i => if a < i then (a, i) else (i, a))).filter
            (fun q => ((q.1 + q.2 : ℕ) : ZMod n) = s)).card := by
      rw [← Finset.filter_val, ← Finset.card_def]
      rw [Finset.filter_image]
      rw [Finset.card_image_of_injOn]
      · congr 1
        refine Finset.filter_congr fun i _ => ?_
        by_cases hcmp : a < i
        · simp [hcmp, eq_comm]
        · simp [hcmp, Nat.add_comm i a, eq_comm]
      · intro i hi j hj hij
        by_cases hci : a < i <;> by_cases hcj : a < j <;>
          simp only [hci, hcj, if_true, if_false, Prod.mk.injEq] at hij <;> omega
    rw [hnew, upperPairs_insert ha, Finset.filter_union,
      Finset.card_union_of_disjoint (Finset.disjoint_filter_filter
        (upperPairs_insert_disjoint ha))]

/-! ## Balance transfer: `ZMod` multiset balance ⟺ ℕ fiber balance -/

/-- Multiset balance of the reduced pair sums is the fiberwise filter balance consumed by
the folded-sum engine. -/
theorem balanced_pairSums_cast_iff {m : ℕ} (hm : 1 ≤ m) (A : Finset ℕ) :
    Balanced ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        (pairSums (A.val.map (Nat.cast : ℕ → ZMod (2 ^ m))))
      ↔ ∀ t < 2 ^ (m - 1),
          ((upperPairs A).filter (fun q => (q.1 + q.2) % 2 ^ m = t)).card
            = ((upperPairs A).filter
                (fun q => (q.1 + q.2) % 2 ^ m = t + 2 ^ (m - 1))).card := by
  haveI : NeZero (2 ^ m) := ⟨pow_ne_zero _ (by norm_num)⟩
  have hsplit : 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
    have h := pow_succ 2 (m - 1)
    rw [Nat.sub_add_cancel hm] at h
    omega
  -- casting condition ⟺ residue condition
  have hcond : ∀ (x t : ℕ), t < 2 ^ m →
      (((x : ℕ) : ZMod (2 ^ m)) = ((t : ℕ) : ZMod (2 ^ m)) ↔ x % 2 ^ m = t) := by
    intro x t ht
    constructor
    · intro h
      have := congrArg ZMod.val h
      rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt ht] at this
    · intro h
      rw [← ZMod.natCast_mod x (2 ^ m), h]
  constructor
  · -- multiset balance ⟹ fiber balance at every t < 2^(m−1)
    intro hbal t ht
    have hb := hbal ((t : ℕ) : ZMod (2 ^ m))
    rw [count_pairSums_cast, count_pairSums_cast] at hb
    have hcast : ((t : ℕ) : ZMod (2 ^ m)) + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        = ((t + 2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by push_cast; ring
    rw [hcast] at hb
    calc ((upperPairs A).filter (fun q => (q.1 + q.2) % 2 ^ m = t)).card
        = ((upperPairs A).filter
            (fun q => ((q.1 + q.2 : ℕ) : ZMod (2 ^ m)) = ((t : ℕ) : ZMod (2 ^ m)))).card := by
          congr 1
          exact (Finset.filter_congr fun q _ => (hcond _ t (by omega)).symm)
      _ = ((upperPairs A).filter
            (fun q => ((q.1 + q.2 : ℕ) : ZMod (2 ^ m))
              = ((t + 2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)))).card := hb
      _ = ((upperPairs A).filter
            (fun q => (q.1 + q.2) % 2 ^ m = t + 2 ^ (m - 1))).card := by
          congr 1
          exact Finset.filter_congr fun q _ => hcond _ (t + 2 ^ (m - 1)) (by omega)
  · -- fiber balance ⟹ multiset balance at every s
    intro hfib s
    rw [count_pairSums_cast, count_pairSums_cast]
    set t : ℕ := s.val with hts
    have htlt : t < 2 ^ m := ZMod.val_lt s
    have hs : s = ((t : ℕ) : ZMod (2 ^ m)) := by rw [hts, ZMod.natCast_zmod_val]
    by_cases hhalf : t < 2 ^ (m - 1)
    · -- lower-half fiber: directly the hypothesis at t
      have hcast : s + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
          = ((t + 2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) := by
        rw [hs]; push_cast; ring
      rw [hcast]
      calc ((upperPairs A).filter
            (fun q => ((q.1 + q.2 : ℕ) : ZMod (2 ^ m)) = s)).card
          = ((upperPairs A).filter (fun q => (q.1 + q.2) % 2 ^ m = t)).card := by
            congr 1
            refine Finset.filter_congr fun q _ => ?_
            rw [hs]
            exact hcond _ t htlt
        _ = ((upperPairs A).filter
              (fun q => (q.1 + q.2) % 2 ^ m = t + 2 ^ (m - 1))).card := hfib t hhalf
        _ = ((upperPairs A).filter
              (fun q => ((q.1 + q.2 : ℕ) : ZMod (2 ^ m))
                = ((t + 2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)))).card := by
            congr 1
            exact (Finset.filter_congr fun q _ =>
              (hcond _ (t + 2 ^ (m - 1)) (by omega)).symm)
    · -- upper-half fiber: the hypothesis at t − 2^(m−1), read backwards
      set t' : ℕ := t - 2 ^ (m - 1) with ht's
      have ht'lt : t' < 2 ^ (m - 1) := by omega
      have hteq : t = t' + 2 ^ (m - 1) := by omega
      have hcast : s + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)) = ((t' : ℕ) : ZMod (2 ^ m)) := by
        rw [hs, hteq, ← Nat.cast_add, add_assoc, hsplit, Nat.cast_add, ZMod.natCast_self,
          add_zero]
      rw [hcast]
      calc ((upperPairs A).filter
            (fun q => ((q.1 + q.2 : ℕ) : ZMod (2 ^ m)) = s)).card
          = ((upperPairs A).filter
              (fun q => (q.1 + q.2) % 2 ^ m = t' + 2 ^ (m - 1))).card := by
            congr 1
            refine Finset.filter_congr fun q _ => ?_
            rw [hs, hteq]
            exact hcond _ (t' + 2 ^ (m - 1)) (by omega)
        _ = ((upperPairs A).filter (fun q => (q.1 + q.2) % 2 ^ m = t')).card :=
            (hfib t' ht'lt).symm
        _ = ((upperPairs A).filter
              (fun q => ((q.1 + q.2 : ℕ) : ZMod (2 ^ m)) = ((t' : ℕ) : ZMod (2 ^ m)))).card := by
            congr 1
            exact (Finset.filter_congr fun q _ => (hcond _ t' (by omega)).symm)

/-! ## The headlines -/

/-- **Layer 1 ⟺ layer 2**: characteristic-zero vanishing of the folded `e₂` polynomial is
multiset balance of the reduced pair sums — any exponent-set size. -/
theorem e2Folded_eq_zero_iff_balanced_cast {m : ℕ} (hm : 1 ≤ m) (A : Finset ℕ) :
    e2Folded m A = 0 ↔
      Balanced ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))
        (pairSums (A.val.map (Nat.cast : ℕ → ZMod (2 ^ m)))) := by
  rw [e2Folded_eq_foldedSum, foldedSum_eq_zero_iff_balanced,
    balanced_pairSums_cast_iff hm A]

/-- **THE END-TO-END CHAIN AT `a = 4`**: a four-element exponent set qualifies for the
depth-1 census (its folded `e₂` polynomial vanishes in characteristic zero) **iff** its
reduction mod `2^m` is an antipodal pair plus a couple symmetric about it. Composed with
`depthOne_badScalar_iff_char0`: *bad scalar ⟺ char-0 census ⟺ antipodal geometry*,
machine-checked end to end. -/
theorem e2Folded_eq_zero_iff_structured {m : ℕ} (hm : 1 ≤ m) (A : Finset ℕ)
    (h4 : A.card = 4) :
    e2Folded m A = 0 ↔
      ∃ x y z, A.val.map (Nat.cast : ℕ → ZMod (2 ^ m))
          = {x, x + ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m)), y, z} ∧ y + z = x + x := by
  rw [e2Folded_eq_zero_iff_balanced_cast hm A]
  have hcard : Multiset.card (A.val.map (Nat.cast : ℕ → ZMod (2 ^ m))) = 4 := by
    simp [h4]
  obtain ⟨a', b', c', d', hM⟩ := Multiset.card_eq_four.mp hcard
  rw [hM]
  exact balanced_pairSums_iff_zmod hm a' b' c' d'

/-! ## Source audit -/

#print axioms count_pairSums_cast
#print axioms balanced_pairSums_cast_iff
#print axioms e2Folded_eq_zero_iff_balanced_cast
#print axioms e2Folded_eq_zero_iff_structured

end ArkLib.ProximityGap.WindowTwoLayer
