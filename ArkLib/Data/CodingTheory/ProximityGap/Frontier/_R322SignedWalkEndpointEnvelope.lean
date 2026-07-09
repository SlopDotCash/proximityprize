/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R321ShadowAutocorrelationDoubling
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# LANE B2 (#466 round 322): factorial envelope for signed-walk endpoints

For a depth-`2r` signed-basis walk ending at `d`, put `ell = ‖d‖₁` and
`s = (2r-ell)/2`.  Splitting the positive and negative multiplicities into the mandatory
`|d_j|` steps and `s` canceling pairs gives the envelope

```text
NR(2m,m,2r,d) * s! * ∏ j, |d_j|! <= (2r)! * m^s.
```

This file first proves the weighted-composition inequality driving that estimate.
-/

set_option autoImplicit false

open Finset

namespace ArkLib.ProximityGap.Frontier.R322SignedWalkEndpointEnvelope

open ArkLib.ProximityGap.Frontier.R306Depth3CharZeroFloor
open ArkLib.ProximityGap.Frontier.R308DepthUniformShadowFloor
open ArkLib.ProximityGap.Frontier.R314KernelRelationMassDecomposition
open ArkLib.ProximityGap.Frontier.R321ShadowAutocorrelationDoubling

theorem countPerms_eq_multinomial {A : Type*} [DecidableEq A] (M : Multiset A) :
    M.countPerms = Nat.multinomial M.toFinset (fun a => M.count a) := by
  rw [Multiset.countPerms,
    ← Finsupp.multinomial_of_support_subset (s := M.toFinset) (d := M.toFinsupp)
      (by rw [Multiset.toFinsupp_support])]
  rfl

theorem countPerms_erase_eq_multinomial {A : Type*} [DecidableEq A]
    (M : Multiset A) (a : A) :
    (M.erase a).countPerms =
      Nat.multinomial M.toFinset (fun b => (M.erase a).count b) := by
  rw [countPerms_eq_multinomial]
  apply Nat.multinomial_congr_of_sdiff
    (s := (M.erase a).toFinset) (t := M.toFinset)
  · exact Multiset.toFinset_subset.mpr (Multiset.erase_subset _ _)
  · intro b hb
    rw [Finset.mem_sdiff, Multiset.mem_toFinset, Multiset.mem_toFinset] at hb
    rw [Multiset.count_eq_zero]
    exact hb.2
  · intro b _
    rfl

theorem count_mul_countPerms {A : Type*} [DecidableEq A]
    (M : Multiset A) (a : A) (ha : a ∈ M) :
    M.count a * M.countPerms = M.card * (M.erase a).countPerms := by
  have haf : a ∈ M.toFinset := Multiset.mem_toFinset.mpr ha
  set P := ∏ b ∈ M.toFinset.erase a, (M.count b).factorial with hP
  have hprodM : ∏ b ∈ M.toFinset, (M.count b).factorial =
      (M.count a).factorial * P :=
    (Finset.mul_prod_erase M.toFinset (fun b => (M.count b).factorial) haf).symm
  have hprodE : ∏ b ∈ M.toFinset, ((M.erase a).count b).factorial =
      ((M.count a) - 1).factorial * P := by
    rw [← Finset.mul_prod_erase M.toFinset
      (fun b => ((M.erase a).count b).factorial) haf, Multiset.count_erase_self]
    congr 1
    refine Finset.prod_congr rfl fun b hb => ?_
    rw [Finset.mem_erase] at hb
    rw [Multiset.count_erase_of_ne hb.1]
  have specM := Nat.multinomial_spec M.toFinset (fun b => M.count b)
  have specE := Nat.multinomial_spec M.toFinset (fun b => (M.erase a).count b)
  rw [Multiset.toFinset_sum_count_eq, hprodM, ← countPerms_eq_multinomial] at specM
  have hsumE : ∑ b ∈ M.toFinset, (M.erase a).count b = (M.erase a).card := by
    rw [← Multiset.toFinset_sum_count_eq (M.erase a)]
    refine (Finset.sum_subset
      (Multiset.toFinset_subset.mpr (Multiset.erase_subset _ _)) ?_).symm
    intro b _ hb
    rw [Multiset.mem_toFinset] at hb
    rw [Multiset.count_eq_zero]
    exact hb
  rw [hsumE, hprodE, ← countPerms_erase_eq_multinomial] at specE
  have hca : 1 ≤ M.count a := Multiset.one_le_count_iff_mem.mpr ha
  have hcard : (M.erase a).card + 1 = M.card := Multiset.card_erase_add_one ha
  have hfa : (M.count a).factorial = M.count a * ((M.count a) - 1).factorial :=
    (Nat.mul_factorial_pred (Nat.one_le_iff_ne_zero.mp hca)).symm
  have hfcard : M.card.factorial = M.card * (M.erase a).card.factorial := by
    rw [← hcard, Nat.factorial_succ]
  have hpos : 0 < ((M.count a) - 1).factorial * P := by positivity
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc
    ((M.count a - 1).factorial * P) * (M.count a * M.countPerms)
        = (M.count a * (M.count a - 1).factorial * P) * M.countPerms := by ring
    _ = (M.count a).factorial * P * M.countPerms := by rw [hfa]
    _ = M.card.factorial := specM
    _ = M.card * (M.erase a).card.factorial := hfcard
    _ = M.card * (((M.count a) - 1).factorial * P * (M.erase a).countPerms) := by
      rw [specE]
    _ = ((M.count a - 1).factorial * P) *
        (M.card * (M.erase a).countPerms) := by ring

/-- Value-erasure recursion for `countPerms`, generalized from natural-valued multisets to
an arbitrary decidable alphabet. -/
theorem countPerms_eq_sum_erase {A : Type*} [DecidableEq A]
    (M : Multiset A) (hM : M ≠ 0) :
    M.countPerms = ∑ a ∈ M.toFinset, (M.erase a).countPerms := by
  have hcard : 0 < M.card := Multiset.card_pos.mpr hM
  apply Nat.eq_of_mul_eq_mul_left hcard
  rw [Finset.mul_sum]
  calc
    M.card * M.countPerms
        = (∑ a ∈ M.toFinset, M.count a) * M.countPerms := by
          rw [Multiset.toFinset_sum_count_eq]
    _ = ∑ a ∈ M.toFinset, M.count a * M.countPerms := by rw [Finset.sum_mul]
    _ = ∑ a ∈ M.toFinset, M.card * (M.erase a).countPerms :=
      Finset.sum_congr rfl fun a ha =>
        count_mul_countPerms M a (Multiset.mem_toFinset.mp ha)

/-- The unordered multiplicity multiset of a finite tuple. -/
def tupleMultiset {A : Type*} {L : ℕ} (t : Fin L → A) : Multiset A :=
  List.ofFn t

/-- The number of tuples with a prescribed multiplicity multiset is its multinomial
coefficient `countPerms`. -/
theorem tupleMultiset_fiber_card_eq_countPerms
    {A : Type*} [Fintype A] [DecidableEq A] :
    ∀ (L : ℕ) (M : Multiset A), M.card = L →
      ((Fintype.piFinset (fun _ : Fin L => (Finset.univ : Finset A))).filter
        (fun t => tupleMultiset t = M)).card = M.countPerms := by
  classical
  intro L
  induction L with
  | zero =>
      intro M hM
      rw [Multiset.card_eq_zero] at hM
      subst M
      simp [tupleMultiset, Multiset.countPerms_zero]
  | succ L ih =>
      intro M hM
      have hMne : M ≠ 0 := by
        intro h
        subst M
        simp at hM
      let U := Fintype.piFinset (fun _ : Fin (L + 1) => (Finset.univ : Finset A))
      let Q := U.filter (fun t => tupleMultiset t = M)
      have hmaps : (↑Q : Set (Fin (L + 1) → A)).MapsTo
          (fun t => t 0) (↑M.toFinset : Set A) := by
        intro t ht
        change t ∈ Q at ht
        simp only [Q, Finset.mem_filter] at ht
        rw [Finset.mem_coe, Multiset.mem_toFinset]
        have hhead : t 0 ∈ tupleMultiset t := by
          unfold tupleMultiset
          rw [List.ofFn_succ]
          simpa using Multiset.mem_cons_self (t 0)
            (List.ofFn (Fin.tail t) : Multiset A)
        rwa [ht.2] at hhead
      rw [show ((Fintype.piFinset (fun _ : Fin (L + 1) =>
        (Finset.univ : Finset A))).filter (fun t => tupleMultiset t = M)).card = Q.card from rfl]
      rw [Finset.card_eq_sum_card_fiberwise hmaps,
        countPerms_eq_sum_erase M hMne]
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [Multiset.mem_toFinset] at hv
      have hcard : (M.erase v).card = L := by
        rw [Multiset.card_erase_of_mem hv, hM]
        simp
      rw [← ih (M.erase v) hcard]
      apply Finset.card_bij'
        (i := fun (t : Fin (L + 1) → A) _ => Fin.tail t)
        (j := fun (u : Fin L → A) _ => Fin.cons (α := fun _ => A) v u)
      · intro t ht
        simp only [Finset.mem_filter, Q] at ht
        change (t ∈ U ∧ tupleMultiset t = M) ∧ t 0 = v at ht
        rw [Finset.mem_filter]
        change Fin.tail t ∈ Fintype.piFinset
          (fun _ : Fin L => (Finset.univ : Finset A)) ∧
            tupleMultiset (Fin.tail t) = M.erase v
        refine ⟨by simp, ?_⟩
        have htuple := ht.1.2
        have hzero := ht.2
        unfold tupleMultiset at htuple ⊢
        rw [List.ofFn_succ] at htuple
        have : (v ::ₘ (List.ofFn (Fin.tail t) : Multiset A)).erase v = M.erase v := by
          rw [← hzero, ← htuple]
          simp [Fin.tail_def]
        simpa using this
      · intro u hu
        rw [Finset.mem_filter] at hu
        change u ∈ Fintype.piFinset
          (fun _ : Fin L => (Finset.univ : Finset A)) ∧
            tupleMultiset u = M.erase v at hu
        simp only [Finset.mem_filter, Q]
        change (Fin.cons (α := fun _ => A) v u ∈ U ∧
          tupleMultiset (Fin.cons (α := fun _ => A) v u) = M) ∧
          Fin.cons (α := fun _ => A) v u 0 = v
        refine ⟨⟨by simp [U], ?_⟩, by simp⟩
        unfold tupleMultiset at hu ⊢
        rw [List.ofFn_cons]
        change v ::ₘ (List.ofFn u : Multiset A) = M
        rw [hu.2]
        exact Multiset.cons_erase hv
      · intro t ht
        simp only [Finset.mem_filter, Q] at ht
        change (t ∈ U ∧ tupleMultiset t = M) ∧ t 0 = v at ht
        rw [← ht.2]
        exact Fin.cons_self_tail t
      · intro u hu
        exact Fin.tail_cons (α := fun _ => A) v u

/-- The total multinomial mass of weak `m`-part compositions of `s` is `m^s`. -/
theorem sum_multinomial_piAntidiag (m s : ℕ) :
    ∑ c ∈ piAntidiag (Finset.univ : Finset (Fin m)) s,
      Nat.multinomial Finset.univ c = m ^ s := by
  have h := Finset.sum_pow_eq_sum_piAntidiag
    (Finset.univ : Finset (Fin m)) (fun _ => (1 : ℕ)) s
  simpa using h.symm

/-- Summing a pointwise `C * multinomial` envelope over all weak compositions costs exactly
the factor `m^s`.  This is the arithmetic summation step in the endpoint bound. -/
theorem sum_composition_weight_le
    (m s C : ℕ) (w : (Fin m → ℕ) → ℕ)
    (hw : ∀ c ∈ piAntidiag (Finset.univ : Finset (Fin m)) s,
      w c ≤ C * Nat.multinomial Finset.univ c) :
    ∑ c ∈ piAntidiag (Finset.univ : Finset (Fin m)) s, w c ≤ C * m ^ s := by
  calc
    ∑ c ∈ piAntidiag (Finset.univ : Finset (Fin m)) s, w c
        ≤ ∑ c ∈ piAntidiag (Finset.univ : Finset (Fin m)) s,
            C * Nat.multinomial Finset.univ c := Finset.sum_le_sum hw
    _ = C * ∑ c ∈ piAntidiag (Finset.univ : Finset (Fin m)) s,
          Nat.multinomial Finset.univ c := by rw [Finset.mul_sum]
    _ = C * m ^ s := by rw [sum_multinomial_piAntidiag]

/-! ## Signed multiplicity profiles -/

/-- A cancellation profile `c` with mandatory positive/negative multiplicities `a,b`. -/
def signedProfile {m : ℕ} (c a b : Fin m → ℕ) : Fin m × Fin 2 → ℕ
  | (j, e) => if e = 0 then c j + a j else c j + b j

/-- The canonical signed-basis indexing: `(j,0) ↦ j`, `(j,1) ↦ j+m`. -/
def signedIndexEquiv (m : ℕ) : Fin m × Fin 2 ≃ Fin (2 * m) :=
  (Equiv.prodComm (Fin m) (Fin 2)).trans finProdFinEquiv

@[simp] theorem signedIndexEquiv_zero {m : ℕ} (j : Fin m) :
    signedIndexEquiv m (j, 0) = ⟨j, by omega⟩ := by
  apply Fin.ext
  simp [signedIndexEquiv, finProdFinEquiv]

@[simp] theorem signedIndexEquiv_one {m : ℕ} (j : Fin m) :
    signedIndexEquiv m (j, 1) = ⟨(j : ℕ) + m, by omega⟩ := by
  apply Fin.ext
  simp [signedIndexEquiv, finProdFinEquiv]

/-- The multiset with a prescribed finite multiplicity function. -/
noncomputable def multiplicityMultiset {A : Type*} [Fintype A]
    (q : A → ℕ) : Multiset A :=
  Finsupp.toMultiset (Finsupp.equivFunOnFinite.symm q)

@[simp] theorem count_multiplicityMultiset {A : Type*} [Fintype A] [DecidableEq A]
    (q : A → ℕ) (x : A) :
    (multiplicityMultiset q).count x = q x := by
  simp [multiplicityMultiset]

theorem card_multiplicityMultiset {A : Type*} [Fintype A] [DecidableEq A]
    (q : A → ℕ) :
    (multiplicityMultiset q).card = ∑ x : A, q x := by
  classical
  rw [multiplicityMultiset, Finsupp.card_toMultiset]
  simp [Finsupp.sum_fintype]

theorem countPerms_multiplicityMultiset {A : Type*} [Fintype A] [DecidableEq A]
    (q : A → ℕ) :
    (multiplicityMultiset q).countPerms = Nat.multinomial Finset.univ q := by
  rw [Multiset.countPerms, multiplicityMultiset,
    Finsupp.toMultiset_toFinsupp,
    ← Finsupp.multinomial_of_support_subset
      (s := (Finset.univ : Finset A)) (d := Finsupp.equivFunOnFinite.symm q) (by simp)]
  rfl

/-- Ordered signed tuples with one prescribed profile are counted by its multinomial. -/
theorem signedProfile_tuple_fiber_card {m : ℕ} (c a b : Fin m → ℕ) :
    ((Fintype.piFinset (fun _ : Fin (∑ x : Fin m × Fin 2, signedProfile c a b x) =>
        (Finset.univ : Finset (Fin m × Fin 2)))).filter
      (fun t => tupleMultiset t = multiplicityMultiset (signedProfile c a b))).card =
      Nat.multinomial Finset.univ (signedProfile c a b) := by
  rw [tupleMultiset_fiber_card_eq_countPerms,
    countPerms_multiplicityMultiset]
  exact card_multiplicityMultiset _

theorem sum_tuple_indicator_eq_count {A : Type*} [DecidableEq A]
    {L : ℕ} (t : Fin L → A) (x : A) :
    (∑ i : Fin L, if t i = x then 1 else 0) = (tupleMultiset t).count x := by
  induction L with
  | zero => simp [tupleMultiset]
  | succ L ih =>
      rw [Fin.sum_univ_succ, tupleMultiset]
      rw [List.ofFn_succ]
      rw [show (∑ i : Fin L, if t i.succ = x then 1 else 0) =
          (tupleMultiset (Fin.tail t)).count x by
        have hi := ih (Fin.tail t)
        change (∑ i : Fin L, if t i.succ = x then 1 else 0) =
          (tupleMultiset (Fin.tail t)).count x at hi
        exact hi]
      simp only [tupleMultiset, Fin.tail_def, Multiset.coe_count]
      rw [List.count_cons]
      split_ifs <;> simp_all <;> omega

theorem sum_tuple_indicator_int_eq_count {A : Type*} [DecidableEq A]
    {L : ℕ} (t : Fin L → A) (x : A) :
    (∑ i : Fin L, if t i = x then (1 : ℤ) else 0) =
      ((tupleMultiset t).count x : ℤ) := by
  exact_mod_cast sum_tuple_indicator_eq_count t x

/-- A canonical signed index contributes `+e_j` on side zero and `-e_j` on side one. -/
theorem vecOf_signedIndex {m : ℕ} (j k : Fin m) (e : Fin 2) :
    vecOf (2 * m) m (signedIndexEquiv m (j, e)) k =
      if e = 0 then (if j = k then 1 else 0) else -(if j = k then 1 else 0) := by
  fin_cases e <;> simp [vecOf] <;> split_ifs <;> simp_all <;> omega

/-- Encode a canonical signed tuple in ArkLib's first-half/second-half root indexing. -/
def encodeSignedTuple {m L : ℕ} (t : Fin L → Fin m × Fin 2) : Fin L → Fin (2 * m) :=
  fun i => signedIndexEquiv m (t i)

/-- Decode ArkLib's root indexing into the canonical signed alphabet. -/
def decodeSignedTuple {m L : ℕ} (t : Fin L → Fin (2 * m)) : Fin L → Fin m × Fin 2 :=
  fun i => (signedIndexEquiv m).symm (t i)

@[simp] theorem encodeSignedTuple_decodeSignedTuple {m L : ℕ}
    (t : Fin L → Fin (2 * m)) :
    encodeSignedTuple (decodeSignedTuple t) = t := by
  funext i
  simp [encodeSignedTuple, decodeSignedTuple]

@[simp] theorem decodeSignedTuple_encodeSignedTuple {m L : ℕ}
    (t : Fin L → Fin m × Fin 2) :
    decodeSignedTuple (encodeSignedTuple t) = t := by
  funext i
  simp [encodeSignedTuple, decodeSignedTuple]

/-- The endpoint of an arbitrary canonical signed tuple is positive-count minus negative-count. -/
theorem tupleVec_encodeSignedTuple_eq_counts {m L : ℕ}
    (t : Fin L → Fin m × Fin 2) :
    tupleVec (2 * m) m L (encodeSignedTuple t) = fun k =>
      ((tupleMultiset t).count (k, 0) : ℤ) -
        ((tupleMultiset t).count (k, 1) : ℤ) := by
  funext k
  unfold tupleVec encodeSignedTuple
  calc
    (∑ i : Fin L, vecOf (2 * m) m (signedIndexEquiv m (t i)) k)
        = ∑ i : Fin L,
            ((if t i = (k, 0) then (1 : ℤ) else 0) -
              (if t i = (k, 1) then (1 : ℤ) else 0)) := by
          apply Finset.sum_congr rfl
          intro i _
          obtain ⟨j, e⟩ := t i
          rw [vecOf_signedIndex]
          fin_cases e <;> simp
    _ = (∑ i : Fin L, if t i = (k, 0) then (1 : ℤ) else 0) -
          ∑ i : Fin L, if t i = (k, 1) then (1 : ℤ) else 0 := by
          rw [Finset.sum_sub_distrib]
    _ = ((tupleMultiset t).count (k, 0) : ℤ) -
          ((tupleMultiset t).count (k, 1) : ℤ) := by
          rw [sum_tuple_indicator_int_eq_count, sum_tuple_indicator_int_eq_count]

/-- The cancellation count at a coordinate is the overlap of its positive and negative
multiplicities. -/
def tupleCancellationProfile {m L : ℕ} (t : Fin L → Fin m × Fin 2) : Fin m → ℕ :=
  fun j => min ((tupleMultiset t).count (j, 0)) ((tupleMultiset t).count (j, 1))

@[simp] theorem card_tupleMultiset {A : Type*} {L : ℕ} (t : Fin L → A) :
    (tupleMultiset t).card = L := by
  simp [tupleMultiset]

/-- A tuple with profile `(c,a,b)` recovers `c` as its cancellation profile whenever the
mandatory positive and negative parts have disjoint support. -/
theorem tupleCancellationProfile_eq_of_profile {m L : ℕ}
    (c a b : Fin m → ℕ) (t : Fin L → Fin m × Fin 2)
    (hdisj : ∀ j, a j = 0 ∨ b j = 0)
    (ht : tupleMultiset t = multiplicityMultiset (signedProfile c a b)) :
    tupleCancellationProfile t = c := by
  funext j
  unfold tupleCancellationProfile
  rw [ht, count_multiplicityMultiset, count_multiplicityMultiset]
  change min (c j + a j) (c j + b j) = c j
  rcases hdisj j with ha | hb <;> omega

/-- **Unique profile classification.** If `a,b` have disjoint coordinate support and a tuple
ends at `a-b`, then its multiplicity multiset is exactly the signed profile with cancellation
vector `min(positiveCount,negativeCount)`. -/
theorem tupleMultiset_eq_profile_of_endpoint {m L : ℕ}
    (a b : Fin m → ℕ) (t : Fin L → Fin m × Fin 2)
    (hdisj : ∀ j, a j = 0 ∨ b j = 0)
    (hend : tupleVec (2 * m) m L (encodeSignedTuple t) =
      fun j => (a j : ℤ) - (b j : ℤ)) :
    tupleMultiset t = multiplicityMultiset
      (signedProfile (tupleCancellationProfile t) a b) := by
  ext x
  obtain ⟨j, e⟩ := x
  let p := (tupleMultiset t).count (j, 0)
  let q := (tupleMultiset t).count (j, 1)
  have hdiff : (p : ℤ) - (q : ℤ) = (a j : ℤ) - (b j : ℤ) :=
    congrFun ((tupleVec_encodeSignedTuple_eq_counts t).symm.trans hend) j
  fin_cases e
  · rw [count_multiplicityMultiset]
    change p = min p q + a j
    rcases hdisj j with ha | hb <;> omega
  · rw [count_multiplicityMultiset]
    change q = min p q + b j
    rcases hdisj j with ha | hb <;> omega

theorem sum_signedProfile {m : ℕ} (c a b : Fin m → ℕ) :
    ∑ x : Fin m × Fin 2, signedProfile c a b x =
      ∑ j : Fin m, (2 * c j + a j + b j) := by
  rw [← Finset.univ_product_univ, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro j _
  rw [Fin.sum_univ_two]
  simp [signedProfile]
  omega

/-- Every tuple with signed profile `(c,a,b)` has endpoint `a-b`; the cancellation profile
`c` disappears exactly. -/
theorem tupleVec_encodeSignedTuple_of_profile {m L : ℕ}
    (c a b : Fin m → ℕ) (t : Fin L → Fin m × Fin 2)
    (ht : tupleMultiset t = multiplicityMultiset (signedProfile c a b)) :
    tupleVec (2 * m) m L (encodeSignedTuple t) =
      fun j => (a j : ℤ) - (b j : ℤ) := by
  funext k
  unfold tupleVec encodeSignedTuple
  calc
    (∑ i : Fin L, vecOf (2 * m) m (signedIndexEquiv m (t i)) k)
        = ∑ i : Fin L,
            ((if t i = (k, 0) then (1 : ℤ) else 0) -
              (if t i = (k, 1) then (1 : ℤ) else 0)) := by
          apply Finset.sum_congr rfl
          intro i _
          obtain ⟨j, e⟩ := t i
          rw [vecOf_signedIndex]
          fin_cases e <;> simp
    _ = (∑ i : Fin L, if t i = (k, 0) then (1 : ℤ) else 0) -
          ∑ i : Fin L, if t i = (k, 1) then (1 : ℤ) else 0 := by
          rw [Finset.sum_sub_distrib]
    _ = ((tupleMultiset t).count (k, 0) : ℤ) -
          ((tupleMultiset t).count (k, 1) : ℤ) := by
          rw [sum_tuple_indicator_int_eq_count, sum_tuple_indicator_int_eq_count]
    _ = ((signedProfile c a b (k, 0) : ℕ) : ℤ) -
          ((signedProfile c a b (k, 1) : ℕ) : ℤ) := by
          rw [ht, count_multiplicityMultiset, count_multiplicityMultiset]
    _ = (a k : ℤ) - (b k : ℤ) := by
          simp [signedProfile]

/-- Canonical signed tuples of length `L` ending at `a-b`. -/
def canonicalEndpointTuples (m L : ℕ) (a b : Fin m → ℕ) :
    Finset (Fin L → Fin m × Fin 2) :=
  (Fintype.piFinset (fun _ : Fin L => (Finset.univ : Finset (Fin m × Fin 2)))).filter
    (fun t => tupleVec (2 * m) m L (encodeSignedTuple t) =
      fun j => (a j : ℤ) - (b j : ℤ))

/-- **Exact endpoint-profile partition.** At length
`L = 2s + Σ(a_j+b_j)`, the endpoint count is the sum of the exact profile multinomials over
all cancellation vectors of mass `s`. -/
theorem card_canonicalEndpointTuples_eq_sum_multinomial
    (m L s : ℕ) (a b : Fin m → ℕ)
    (hdisj : ∀ j, a j = 0 ∨ b j = 0)
    (hL : L = 2 * s + ∑ j : Fin m, (a j + b j)) :
    (canonicalEndpointTuples m L a b).card =
      ∑ c ∈ piAntidiag (Finset.univ : Finset (Fin m)) s,
        Nat.multinomial Finset.univ (signedProfile c a b) := by
  classical
  let Q := canonicalEndpointTuples m L a b
  let C := piAntidiag (Finset.univ : Finset (Fin m)) s
  have hmaps : (↑Q : Set (Fin L → Fin m × Fin 2)).MapsTo
      tupleCancellationProfile (↑C : Set (Fin m → ℕ)) := by
    intro t ht
    change t ∈ Q at ht
    simp only [Q, canonicalEndpointTuples, Finset.mem_filter] at ht
    have hprofile := tupleMultiset_eq_profile_of_endpoint a b t hdisj ht.2
    have hcard := congrArg Multiset.card hprofile
    rw [card_tupleMultiset, card_multiplicityMultiset, sum_signedProfile] at hcard
    rw [Finset.mem_coe, Finset.mem_piAntidiag]
    constructor
    · have hsum :
          (∑ j : Fin m,
              (2 * tupleCancellationProfile t j + a j + b j)) =
            2 * (∑ j : Fin m, tupleCancellationProfile t j) +
              ∑ j : Fin m, (a j + b j) := by
          calc
            (∑ j : Fin m,
                (2 * tupleCancellationProfile t j + a j + b j)) =
                ∑ j : Fin m,
                  (2 * tupleCancellationProfile t j + (a j + b j)) := by
                    apply Finset.sum_congr rfl
                    intro j _
                    omega
            _ = (∑ j : Fin m, 2 * tupleCancellationProfile t j) +
                ∑ j : Fin m, (a j + b j) := Finset.sum_add_distrib
            _ = 2 * (∑ j : Fin m, tupleCancellationProfile t j) +
                ∑ j : Fin m, (a j + b j) := by rw [Finset.mul_sum]
      rw [hsum] at hcard
      exact Nat.mul_left_cancel (by norm_num)
        (Nat.add_right_cancel (hcard.symm.trans hL))
    · intro j hj
      exact Finset.mem_univ j
  rw [show (canonicalEndpointTuples m L a b).card = Q.card from rfl]
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [Finset.mem_piAntidiag] at hc
  have hprofileSum :
      (∑ x : Fin m × Fin 2, signedProfile c a b x) = L := by
    rw [sum_signedProfile]
    have hsum : (∑ j : Fin m, (2 * c j + a j + b j)) =
        2 * (∑ j : Fin m, c j) + ∑ j : Fin m, (a j + b j) := by
      calc
        (∑ j : Fin m, (2 * c j + a j + b j)) =
            ∑ j : Fin m, (2 * c j + (a j + b j)) := by
              apply Finset.sum_congr rfl
              intro j _
              omega
        _ = (∑ j : Fin m, 2 * c j) + ∑ j : Fin m, (a j + b j) :=
          Finset.sum_add_distrib
        _ = 2 * (∑ j : Fin m, c j) + ∑ j : Fin m, (a j + b j) := by
          rw [Finset.mul_sum]
    rw [hsum, hc.1, hL]
  have hset : Q.filter (fun t => tupleCancellationProfile t = c) =
      (Fintype.piFinset (fun _ : Fin L =>
        (Finset.univ : Finset (Fin m × Fin 2)))).filter
          (fun t => tupleMultiset t = multiplicityMultiset (signedProfile c a b)) := by
    ext t
    simp only [Finset.mem_filter, Q, canonicalEndpointTuples]
    constructor
    · rintro ⟨⟨htU, hend⟩, hcanc⟩
      refine ⟨htU, ?_⟩
      rw [← hcanc]
      exact tupleMultiset_eq_profile_of_endpoint a b t hdisj hend
    · rintro ⟨htU, hprof⟩
      exact ⟨⟨htU, tupleVec_encodeSignedTuple_of_profile c a b t hprof⟩,
        tupleCancellationProfile_eq_of_profile c a b t hdisj hprof⟩
  rw [hset, tupleMultiset_fiber_card_eq_countPerms,
    countPerms_multiplicityMultiset]
  rw [card_multiplicityMultiset]
  exact hprofileSum

theorem prod_factorial_signedProfile {m : ℕ} (c a b : Fin m → ℕ) :
    ∏ x : Fin m × Fin 2, (signedProfile c a b x).factorial =
      ∏ j : Fin m, ((c j + a j).factorial * (c j + b j).factorial) := by
  rw [← Finset.univ_product_univ, Finset.prod_product]
  apply Finset.prod_congr rfl
  intro j _
  rw [Fin.prod_univ_two]
  simp [signedProfile]

/-- Coordinatewise factorial domination for the mandatory and cancellation parts. -/
theorem prod_factorial_parts_le_profile {m : ℕ} (c a b : Fin m → ℕ) :
    (∏ j : Fin m,
        (c j).factorial * (c j).factorial * ((a j).factorial * (b j).factorial))
      ≤ ∏ j : Fin m,
        ((c j + a j).factorial * (c j + b j).factorial) := by
  apply Finset.prod_le_prod'
  intro j _
  have hca : (c j).factorial * (a j).factorial ≤ (c j + a j).factorial :=
    Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add _ _)
  have hcb : (c j).factorial * (b j).factorial ≤ (c j + b j).factorial :=
    Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add _ _)
  calc
    (c j).factorial * (c j).factorial * ((a j).factorial * (b j).factorial)
        = ((c j).factorial * (a j).factorial) *
          ((c j).factorial * (b j).factorial) := by ring
    _ ≤ (c j + a j).factorial * (c j + b j).factorial :=
      Nat.mul_le_mul hca hcb

/-- The exact denominator-cleared multinomial envelope for one signed multiplicity profile. -/
theorem multinomial_signedProfile_envelope {m : ℕ} (c a b : Fin m → ℕ) :
    Nat.multinomial Finset.univ (signedProfile c a b) *
          (∑ j : Fin m, c j).factorial *
          (∏ j : Fin m, (a j).factorial * (b j).factorial)
      ≤ (∑ x : Fin m × Fin 2, signedProfile c a b x).factorial *
          Nat.multinomial Finset.univ c := by
  let CP := ∏ j : Fin m, (c j).factorial
  let AB := ∏ j : Fin m, (a j).factorial * (b j).factorial
  let QD := ∏ x : Fin m × Fin 2, (signedProfile c a b x).factorial
  let MQ := Nat.multinomial Finset.univ (signedProfile c a b)
  let MC := Nat.multinomial Finset.univ c
  have hspecQ := Nat.multinomial_spec Finset.univ (signedProfile c a b)
  have hspecC := Nat.multinomial_spec Finset.univ c
  change QD * MQ = _ at hspecQ
  change CP * MC = _ at hspecC
  have hdenStrong : CP * CP * AB ≤ QD := by
    dsimp [QD]
    rw [prod_factorial_signedProfile]
    calc
      CP * CP * AB = ∏ j : Fin m,
          (c j).factorial * (c j).factorial *
            ((a j).factorial * (b j).factorial) := by
        simp only [CP, AB, ← Finset.prod_mul_distrib]
      _ ≤ ∏ j : Fin m,
          ((c j + a j).factorial * (c j + b j).factorial) :=
        prod_factorial_parts_le_profile c a b
  have hCP : 1 ≤ CP := by
    dsimp [CP]
    exact Finset.one_le_prod (fun _ _ => Nat.factorial_pos _)
  have hden : CP * AB ≤ QD := by
    calc
      CP * AB = CP * AB * 1 := by omega
      _ ≤ CP * AB * CP := Nat.mul_le_mul_left (CP * AB) hCP
      _ = CP * CP * AB := by ring
      _ ≤ QD := hdenStrong
  change MQ * (∑ j : Fin m, c j).factorial * AB ≤
    (∑ x : Fin m × Fin 2, signedProfile c a b x).factorial * MC
  calc
    MQ * (∑ j : Fin m, c j).factorial * AB
        = MQ * (CP * MC) * AB := by rw [hspecC]
    _ = (CP * AB) * MQ * MC := by ring
    _ ≤ QD * MQ * MC := by
      simpa [mul_assoc] using Nat.mul_le_mul_right (MQ * MC) hden
    _ = (∑ x : Fin m × Fin 2, signedProfile c a b x).factorial * MC := by
      rw [hspecQ]

/-- **Canonical signed-walk endpoint envelope.** The full endpoint fiber satisfies the
denominator-cleared factorial bound before transport to ArkLib's `NR`. -/
theorem card_canonicalEndpointTuples_factorial_envelope
    (m L s : ℕ) (a b : Fin m → ℕ)
    (hdisj : ∀ j, a j = 0 ∨ b j = 0)
    (hL : L = 2 * s + ∑ j : Fin m, (a j + b j)) :
    (canonicalEndpointTuples m L a b).card * s.factorial *
        (∏ j : Fin m, (a j).factorial * (b j).factorial)
      ≤ L.factorial * m ^ s := by
  rw [card_canonicalEndpointTuples_eq_sum_multinomial m L s a b hdisj hL]
  calc
    (∑ c ∈ piAntidiag (Finset.univ : Finset (Fin m)) s,
        Nat.multinomial Finset.univ (signedProfile c a b)) * s.factorial *
          (∏ j : Fin m, (a j).factorial * (b j).factorial)
        = ∑ c ∈ piAntidiag (Finset.univ : Finset (Fin m)) s,
            (Nat.multinomial Finset.univ (signedProfile c a b) * s.factorial *
              (∏ j : Fin m, (a j).factorial * (b j).factorial)) := by
          rw [Finset.sum_mul, Finset.sum_mul]
    _ ≤ ∑ c ∈ piAntidiag (Finset.univ : Finset (Fin m)) s,
          L.factorial * Nat.multinomial Finset.univ c := by
          apply Finset.sum_le_sum
          intro c hc
          rw [Finset.mem_piAntidiag] at hc
          have hsum : (∑ x : Fin m × Fin 2, signedProfile c a b x) = L := by
            rw [sum_signedProfile]
            have hsplit : (∑ j : Fin m, (2 * c j + a j + b j)) =
                2 * (∑ j : Fin m, c j) + ∑ j : Fin m, (a j + b j) := by
              calc
                (∑ j : Fin m, (2 * c j + a j + b j)) =
                    ∑ j : Fin m, (2 * c j + (a j + b j)) := by
                      apply Finset.sum_congr rfl
                      intro j _
                      omega
                _ = (∑ j : Fin m, 2 * c j) + ∑ j : Fin m, (a j + b j) :=
                  Finset.sum_add_distrib
                _ = 2 * (∑ j : Fin m, c j) + ∑ j : Fin m, (a j + b j) := by
                  rw [Finset.mul_sum]
            rw [hsplit, hc.1, ← hL]
          simpa [hc.1, hsum] using multinomial_signedProfile_envelope c a b
    _ = L.factorial * ∑ c ∈ piAntidiag (Finset.univ : Finset (Fin m)) s,
          Nat.multinomial Finset.univ c := by rw [Finset.mul_sum]
    _ = L.factorial * m ^ s := by rw [sum_multinomial_piAntidiag]

/-- The canonical endpoint count is exactly ArkLib's characteristic-zero histogram `NR`. -/
theorem NR_eq_card_canonicalEndpointTuples
    (m L : ℕ) (a b : Fin m → ℕ) :
    NR (2 * m) m L (fun j => (a j : ℤ) - (b j : ℤ)) =
      (canonicalEndpointTuples m L a b).card := by
  classical
  unfold NR canonicalEndpointTuples
  apply Finset.card_bij'
    (i := fun (t : Fin L → Fin (2 * m)) _ => decodeSignedTuple t)
    (j := fun (u : Fin L → Fin m × Fin 2) _ => encodeSignedTuple u)
  · intro t ht
    rw [Finset.mem_filter] at ht ⊢
    refine ⟨by simp, ?_⟩
    simpa using ht.2
  · intro u hu
    rw [Finset.mem_filter] at hu ⊢
    refine ⟨by simp, ?_⟩
    simpa using hu.2
  · intro t ht
    exact encodeSignedTuple_decodeSignedTuple t
  · intro u hu
    exact decodeSignedTuple_encodeSignedTuple u

/-- **NR factorial envelope in positive/negative endpoint coordinates.** -/
theorem NR_factorial_envelope_of_sub
    (m L s : ℕ) (a b : Fin m → ℕ)
    (hdisj : ∀ j, a j = 0 ∨ b j = 0)
    (hL : L = 2 * s + ∑ j : Fin m, (a j + b j)) :
    NR (2 * m) m L (fun j => (a j : ℤ) - (b j : ℤ)) * s.factorial *
        (∏ j : Fin m, (a j).factorial * (b j).factorial)
      ≤ L.factorial * m ^ s := by
  rw [NR_eq_card_canonicalEndpointTuples]
  exact card_canonicalEndpointTuples_factorial_envelope m L s a b hdisj hL

/-- Positive and negative natural parts of an integer coefficient. -/
def intPositivePart (z : ℤ) : ℕ := z.toNat
def intNegativePart (z : ℤ) : ℕ := (-z).toNat

theorem intPositivePart_eq_zero_or_intNegativePart_eq_zero (z : ℤ) :
    intPositivePart z = 0 ∨ intNegativePart z = 0 := by
  cases z <;> simp [intPositivePart, intNegativePart]

theorem intPositivePart_cast_sub_intNegativePart_cast (z : ℤ) :
    (intPositivePart z : ℤ) - (intNegativePart z : ℤ) = z := by
  cases z <;> simp [intPositivePart, intNegativePart] <;> omega

theorem intPositivePart_add_intNegativePart (z : ℤ) :
    intPositivePart z + intNegativePart z = z.natAbs := by
  cases z <;> simp [intPositivePart, intNegativePart]

theorem factorial_parts_mul_eq_natAbs_factorial (z : ℤ) :
    (intPositivePart z).factorial * (intNegativePart z).factorial =
      z.natAbs.factorial := by
  cases z <;> simp [intPositivePart, intNegativePart]

/-- The coefficient `L1` norm of an integer endpoint. -/
def endpointL1 {m : ℕ} (d : Fin m → ℤ) : ℕ :=
  ∑ j : Fin m, (d j).natAbs

theorem endpointL1_pos_of_ne_zero {m : ℕ} {d : Fin m → ℤ} (hd : d ≠ 0) :
    0 < endpointL1 d := by
  by_contra h
  push Not at h
  have hzero : endpointL1 d = 0 := Nat.eq_zero_of_le_zero h
  apply hd
  funext j
  unfold endpointL1 at hzero
  have hj : (d j).natAbs = 0 := by
    have hjle : (d j).natAbs ≤ ∑ x : Fin m, (d x).natAbs :=
      Finset.single_le_sum (s := (Finset.univ : Finset (Fin m)))
        (f := fun x => (d x).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    rw [hzero] at hjle
    omega
  exact Int.natAbs_eq_zero.mp hj

/-- Every signed-basis tuple has the required parity decomposition of its length. -/
theorem exists_length_eq_two_mul_add_endpointL1_of_tuple
    (m L : ℕ) (t : Fin L → Fin (2 * m)) :
    ∃ s : ℕ, L = 2 * s + endpointL1 (tupleVec (2 * m) m L t) := by
  let u := decodeSignedTuple t
  let d := tupleVec (2 * m) m L t
  let a : Fin m → ℕ := fun j => intPositivePart (d j)
  let b : Fin m → ℕ := fun j => intNegativePart (d j)
  let c := tupleCancellationProfile u
  have hdisj : ∀ j, a j = 0 ∨ b j = 0 := fun j =>
    intPositivePart_eq_zero_or_intNegativePart_eq_zero (d j)
  have hend : tupleVec (2 * m) m L (encodeSignedTuple u) =
      fun j => (a j : ℤ) - (b j : ℤ) := by
    rw [show encodeSignedTuple u = t from encodeSignedTuple_decodeSignedTuple t]
    funext j
    exact (intPositivePart_cast_sub_intNegativePart_cast (d j)).symm
  have hprofile := tupleMultiset_eq_profile_of_endpoint a b u hdisj hend
  have hcard := congrArg Multiset.card hprofile
  rw [card_tupleMultiset, card_multiplicityMultiset, sum_signedProfile] at hcard
  refine ⟨∑ j : Fin m, c j, ?_⟩
  have hsplit : (∑ j : Fin m, (2 * c j + a j + b j)) =
      2 * (∑ j : Fin m, c j) + endpointL1 d := by
    calc
      (∑ j : Fin m, (2 * c j + a j + b j)) =
          ∑ j : Fin m, (2 * c j + (a j + b j)) := by
            apply Finset.sum_congr rfl
            intro j _
            omega
      _ = (∑ j : Fin m, 2 * c j) + ∑ j : Fin m, (a j + b j) :=
        Finset.sum_add_distrib
      _ = 2 * (∑ j : Fin m, c j) + ∑ j : Fin m, (a j + b j) := by
        rw [Finset.mul_sum]
      _ = 2 * (∑ j : Fin m, c j) + endpointL1 d := by
        congr 1
        unfold endpointL1
        apply Finset.sum_congr rfl
        intro j _
        exact intPositivePart_add_intNegativePart (d j)
  rw [hsplit] at hcard
  exact hcard

/-- Every nonempty histogram fiber automatically has the parity witness required by the
factorial envelope. -/
theorem exists_length_eq_two_mul_add_endpointL1_of_NR_pos
    (m L : ℕ) (d : Fin m → ℤ) (hpos : 0 < NR (2 * m) m L d) :
    ∃ s : ℕ, L = 2 * s + endpointL1 d := by
  unfold NR at hpos
  obtain ⟨t, ht⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at ht
  obtain ⟨s, hs⟩ := exists_length_eq_two_mul_add_endpointL1_of_tuple m L t
  exact ⟨s, by rwa [ht.2] at hs⟩

/-- **R322 HEADLINE: sharp signed-walk endpoint envelope.** For an endpoint `d` reachable
at length `L = 2s + ‖d‖₁`, its characteristic-zero histogram obeys

`NR(d) * s! * ∏ |d_j|! ≤ L! * m^s`.
-/
theorem NR_factorial_envelope
    (m L s : ℕ) (d : Fin m → ℤ)
    (hL : L = 2 * s + endpointL1 d) :
    NR (2 * m) m L d * s.factorial *
        (∏ j : Fin m, (d j).natAbs.factorial)
      ≤ L.factorial * m ^ s := by
  let a : Fin m → ℕ := fun j => intPositivePart (d j)
  let b : Fin m → ℕ := fun j => intNegativePart (d j)
  have hdisj : ∀ j, a j = 0 ∨ b j = 0 := fun j =>
    intPositivePart_eq_zero_or_intNegativePart_eq_zero (d j)
  have hendpoint : (fun j => (a j : ℤ) - (b j : ℤ)) = d := by
    funext j
    exact intPositivePart_cast_sub_intNegativePart_cast (d j)
  have hmass : L = 2 * s + ∑ j : Fin m, (a j + b j) := by
    rw [hL]
    congr 2
    unfold endpointL1
    apply Finset.sum_congr rfl
    intro j _
    exact (intPositivePart_add_intNegativePart (d j)).symm
  have h := NR_factorial_envelope_of_sub m L s a b hdisj hmass
  rw [hendpoint] at h
  have hprod : (∏ j : Fin m, (a j).factorial * (b j).factorial) =
      ∏ j : Fin m, (d j).natAbs.factorial := by
    apply Finset.prod_congr rfl
    intro j _
    exact factorial_parts_mul_eq_natAbs_factorial (d j)
  rwa [hprod] at h

/-- R321 consumer: each realized kernel relation's finite-field collision mass inherits the
sharp factorial endpoint envelope. -/
theorem shadowRelationMass_factorial_envelope
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r s : ℕ) {d : Fin m → ℤ}
    (hd : d ∈ shadowKernelRelations g (2 * m) m r)
    (hdepth : r + r = 2 * s + endpointL1 d) :
    shadowRelationMass g (2 * m) m r d * s.factorial *
        (∏ j : Fin m, (d j).natAbs.factorial)
      ≤ (r + r).factorial * m ^ s := by
  rw [shadowRelationMass_eq_NR_double g m r hd]
  exact NR_factorial_envelope m (r + r) s d hdepth

/-- Every realized kernel relation has a nonempty doubled-depth characteristic-zero fiber. -/
theorem NR_double_pos_of_shadowKernelRelation
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r : ℕ) {d : Fin m → ℤ}
    (hd : d ∈ shadowKernelRelations g (2 * m) m r) :
    0 < NR (2 * m) m (r + r) d := by
  classical
  rw [shadowKernelRelations, Finset.mem_image] at hd
  obtain ⟨p, hp, hpd⟩ := hd
  have hoff := (Finset.mem_filter.mp hp).1
  have hp1 := (Finset.mem_offDiag.mp hoff).1
  have hp2 := (Finset.mem_offDiag.mp hoff).2.1
  rw [keysR, Finset.mem_image] at hp1 hp2
  obtain ⟨t, _htU, ht⟩ := hp1
  obtain ⟨u, _huU, hu⟩ := hp2
  rw [← tuplePairDifferenceCount_eq_NR]
  unfold tuplePairDifferenceCount
  rw [Finset.card_pos]
  refine ⟨(t, u), ?_⟩
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [ht, hu]
  exact hpd

/-- **Hypothesis-free realized-relation envelope.** Every realized relation owns a parity
witness `s` and satisfies the corresponding sharp factorial collision-mass bound. -/
theorem exists_shadowRelationMass_factorial_envelope
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r : ℕ) {d : Fin m → ℤ}
    (hd : d ∈ shadowKernelRelations g (2 * m) m r) :
    ∃ s : ℕ,
      r + r = 2 * s + endpointL1 d ∧
      shadowRelationMass g (2 * m) m r d * s.factorial *
          (∏ j : Fin m, (d j).natAbs.factorial)
        ≤ (r + r).factorial * m ^ s := by
  obtain ⟨s, hs⟩ := exists_length_eq_two_mul_add_endpointL1_of_NR_pos
    m (r + r) d (NR_double_pos_of_shadowKernelRelation g m r hd)
  exact ⟨s, hs, shadowRelationMass_factorial_envelope g m r s hd hs⟩

/-- A realized nonzero relation necessarily has strictly fewer than `r` cancellation pairs. -/
theorem exists_lt_shadowRelationMass_factorial_envelope
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r : ℕ) {d : Fin m → ℤ}
    (hd : d ∈ shadowKernelRelations g (2 * m) m r) :
    ∃ s < r,
      r + r = 2 * s + endpointL1 d ∧
      shadowRelationMass g (2 * m) m r d * s.factorial *
          (∏ j : Fin m, (d j).natAbs.factorial)
        ≤ (r + r).factorial * m ^ s := by
  obtain ⟨s, hs, hbound⟩ := exists_shadowRelationMass_factorial_envelope g m r hd
  have hdne := (shadowKernelRelation_ne_zero_and_evalVec_eq_zero
    g (2 * m) m r hd).1
  have hl1 := endpointL1_pos_of_ne_zero hdne
  refine ⟨s, ?_, hs, hbound⟩
  omega

/-- Coarser but convenient consequence: every realized nonzero relation saves at least one
full power of `m` relative to the central `m^r` scale. -/
theorem shadowRelationMass_le_factorial_mul_pow_pred
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (g : F) (m r : ℕ) (hm : 0 < m) {d : Fin m → ℤ}
    (hd : d ∈ shadowKernelRelations g (2 * m) m r) :
    shadowRelationMass g (2 * m) m r d ≤ (r + r).factorial * m ^ (r - 1) := by
  obtain ⟨s, hsr, _hs, hbound⟩ :=
    exists_lt_shadowRelationMass_factorial_envelope g m r hd
  let D := s.factorial * ∏ j : Fin m, (d j).natAbs.factorial
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have honeD : 1 ≤ D := Nat.succ_le_iff.mpr hD
  have hmass : shadowRelationMass g (2 * m) m r d ≤
      shadowRelationMass g (2 * m) m r d * D := by
    simpa using Nat.mul_le_mul_left (shadowRelationMass g (2 * m) m r d) honeD
  have hsle : s ≤ r - 1 := by omega
  have hpowers : m ^ s ≤ m ^ (r - 1) :=
    pow_le_pow_right' (Nat.succ_le_iff.mpr hm) hsle
  calc
    shadowRelationMass g (2 * m) m r d
        ≤ shadowRelationMass g (2 * m) m r d * D := hmass
    _ ≤ (r + r).factorial * m ^ s := by
      simpa [D, mul_assoc] using hbound
    _ ≤ (r + r).factorial * m ^ (r - 1) :=
      Nat.mul_le_mul_left (r + r).factorial hpowers

end ArkLib.ProximityGap.Frontier.R322SignedWalkEndpointEnvelope

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.R322SignedWalkEndpointEnvelope.countPerms_eq_sum_erase
#print axioms
  ArkLib.ProximityGap.Frontier.R322SignedWalkEndpointEnvelope.tupleMultiset_fiber_card_eq_countPerms
#print axioms
  ArkLib.ProximityGap.Frontier.R322SignedWalkEndpointEnvelope.sum_multinomial_piAntidiag
#print axioms
  ArkLib.ProximityGap.Frontier.R322SignedWalkEndpointEnvelope.sum_composition_weight_le
#print axioms
  ArkLib.ProximityGap.Frontier.R322SignedWalkEndpointEnvelope.prod_factorial_parts_le_profile
#print axioms
  ArkLib.ProximityGap.Frontier.R322SignedWalkEndpointEnvelope.multinomial_signedProfile_envelope
#print axioms
  ArkLib.ProximityGap.Frontier.R322SignedWalkEndpointEnvelope.tupleVec_encodeSignedTuple_eq_counts
#print axioms
  ArkLib.ProximityGap.Frontier.R322SignedWalkEndpointEnvelope.tupleMultiset_eq_profile_of_endpoint
#print axioms
  ArkLib.ProximityGap.Frontier.R322SignedWalkEndpointEnvelope.tupleCancellationProfile_eq_of_profile
#print axioms
  ArkLib.ProximityGap.Frontier.R322SignedWalkEndpointEnvelope.card_canonicalEndpointTuples_eq_sum_multinomial
#print axioms
  ArkLib.ProximityGap.Frontier.R322SignedWalkEndpointEnvelope.card_canonicalEndpointTuples_factorial_envelope
#print axioms
  ArkLib.ProximityGap.Frontier.R322SignedWalkEndpointEnvelope.NR_factorial_envelope_of_sub
#print axioms
  ArkLib.ProximityGap.Frontier.R322SignedWalkEndpointEnvelope.NR_factorial_envelope
#print axioms
  ArkLib.ProximityGap.Frontier.R322SignedWalkEndpointEnvelope.shadowRelationMass_factorial_envelope
#print axioms
  ArkLib.ProximityGap.Frontier.R322SignedWalkEndpointEnvelope.exists_shadowRelationMass_factorial_envelope
#print axioms
  ArkLib.ProximityGap.Frontier.R322SignedWalkEndpointEnvelope.exists_lt_shadowRelationMass_factorial_envelope
#print axioms
  ArkLib.ProximityGap.Frontier.R322SignedWalkEndpointEnvelope.shadowRelationMass_le_factorial_mul_pow_pred
