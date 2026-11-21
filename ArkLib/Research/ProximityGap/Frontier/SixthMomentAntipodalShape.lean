/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Antipodal structure of sixth-moment relations

The three additive hypotheses in this module concern restricted four-term relations
in a sign-symmetric set. They imply that a non-pairable zero sum with six entries
has no opposite entries and at most one double, with no multiplicity above two.
Multipliers of dyadic order act freely on its support. The last two theorems
give the exact numerical sixth-moment orbit budget at the two production primes.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.SixthMomentAntipodalShape

variable {F : Type*} [Field F]

/-- A pair of opposite entries, with their multiplicities. -/
def pair (x : F) : Multiset F := {x} + {-x}

/-- A multiset partitioned into three opposite pairs. -/
def Pairable (s : Multiset F) : Prop :=
  ∃ a b c : F, s = pair a + pair b + pair c

/-- All four-term conditions used to eliminate repeated entries. -/
structure FourTermConditions (H : Set F) : Prop where
  neg_mem : ∀ a ∈ H, -a ∈ H
  ne_neg : ∀ a ∈ H, a ≠ -a
  sidon : ∀ a ∈ H, ∀ b ∈ H, ∀ c ∈ H, ∀ d ∈ H,
    a + b = c + d → a + b = 0 ∨ a = c ∨ a = d
  triple : ∀ a ∈ H, ∀ b ∈ H, ∀ c ∈ H, ∀ d ∈ H,
    3 * a = b + c + d → a = b
  doubles : ∀ a ∈ H, ∀ b ∈ H, ∀ c ∈ H, ∀ d ∈ H,
    2 * (a + b) = c + d → a + b = 0

private theorem pair_le_of_mem [DecidableEq F] {s : Multiset F} {a : F}
    (ha : a ∈ s) (hna : -a ∈ s) (hne : a ≠ -a) : pair a ≤ s := by
  apply Multiset.le_iff_count.mpr
  intro x
  by_cases hx : x = a
  · subst x
    simpa [pair, hne, Ne.symm hne] using Multiset.one_le_count_iff_mem.mpr ha
  by_cases hnx : x = -a
  · subst x
    simpa [pair, hne, Ne.symm hne] using Multiset.one_le_count_iff_mem.mpr hna
  simp [pair, hx, hnx]

/-- An opposite pair in a six-term zero sum forces the residual four entries to pair. -/
theorem pairable_of_opposites {H : Set F} (h : FourTermConditions H)
    {s : Multiset F} (hcard : s.card = 6) (hsum : s.sum = 0)
    (hs : ∀ x ∈ s, x ∈ H) {a : F} (ha : a ∈ s) (hna : -a ∈ s) :
    Pairable s := by
  classical
  obtain ⟨t, rfl⟩ := Multiset.le_iff_exists_add.mp
    (pair_le_of_mem ha hna (h.ne_neg a (hs _ ha)))
  have ht : t.card = 4 := by simpa [pair] using hcard
  obtain ⟨b, c, d, e, rfl⟩ := Multiset.card_eq_four.mp ht
  have hb := hs b (by simp)
  have hc := hs c (by simp)
  have hd := hs d (by simp)
  have he := hs e (by simp)
  simp [pair] at hsum
  have hbc : b + c = (-d) + (-e) := by linear_combination hsum
  rcases h.sidon b hb c hc (-d) (h.neg_mem d hd) (-e) (h.neg_mem e he) hbc with h0 | hh | hh
  · have hcb : c = -b := by linear_combination h0
    have hed : e = -d := by linear_combination hsum - h0
    subst c
    subst e
    refine ⟨a, b, d, ?_⟩
    simp only [pair, Multiset.insert_eq_cons, ← Multiset.singleton_add]
    ac_rfl
  · have heb : d = -b := by linear_combination hh
    have hec : e = -c := by linear_combination hsum - hh
    subst d
    subst e
    refine ⟨a, b, c, ?_⟩
    simp only [pair, Multiset.insert_eq_cons, ← Multiset.singleton_add]
    ac_rfl
  · have heb : e = -b := by linear_combination hh
    have hdc : d = -c := by linear_combination hsum - hh
    subst e
    subst d
    refine ⟨a, b, c, ?_⟩
    simp only [pair, Multiset.insert_eq_cons, ← Multiset.singleton_add]
    ac_rfl

/-- A non-pairable six-term zero sum has multiplicities bounded by two, and only
one distinct value can attain two. Its support contains no opposite pair. -/
theorem nonpairable_multiplicities [DecidableEq F] {H : Set F} (h : FourTermConditions H)
    {s : Multiset F} (hcard : s.card = 6) (hsum : s.sum = 0)
    (hs : ∀ x ∈ s, x ∈ H) (hnp : ¬Pairable s) :
    (∀ a ∈ s, -a ∉ s) ∧ (∀ a, s.count a ≤ 2) ∧
    (∀ a b, 2 ≤ s.count a → 2 ≤ s.count b → a = b) := by
  have hn : ∀ a ∈ s, -a ∉ s :=
    fun _ ha hna => hnp (pairable_of_opposites h hcard hsum hs ha hna)
  refine ⟨hn, ?_, ?_⟩
  · intro a
    by_contra! hc
    obtain ⟨t, ht⟩ := Multiset.le_iff_exists_add.mp
      (Multiset.le_count_iff_replicate_le.mp (show 3 ≤ s.count a by omega))
    have h3 : t.card = 3 := by simpa [ht] using hcard
    obtain ⟨b, c, d, rfl⟩ := Multiset.card_eq_three.mp h3
    rw [ht] at hs hsum hn
    have ha := hs a (by simp)
    have hb := hs b (by simp)
    have hc := hs c (by simp)
    have hd := hs d (by simp)
    simp at hsum
    have he : 3 * a = -b + -c + -d := by linear_combination hsum
    have hab := h.triple a ha (-b) (h.neg_mem _ hb) (-c) (h.neg_mem _ hc)
      (-d) (h.neg_mem _ hd) he
    exact hn b (by simp) (by rw [← hab]; simp)
  · intro a b hca hcb
    by_contra hab
    have hsub : ({a} + {a} + {b} + {b} : Multiset F) ≤ s := by
      apply Multiset.le_iff_count.mpr
      intro x
      by_cases hxa : x = a
      · subst x
        simpa [hab, Ne.symm hab] using hca
      by_cases hxb : x = b
      · subst x
        simpa [hab, Ne.symm hab] using hcb
      simp [hxa, hxb]
    obtain ⟨t, ht⟩ := Multiset.le_iff_exists_add.mp hsub
    have h2 : t.card = 2 := by simpa [ht] using hcard
    obtain ⟨c, d, rfl⟩ := Multiset.card_eq_two.mp h2
    rw [ht] at hs hsum hn
    have ha := hs a (by simp)
    have hb := hs b (by simp)
    have hc := hs c (by simp)
    have hd := hs d (by simp)
    simp at hsum
    have he : 2 * (a + b) = -c + -d := by linear_combination hsum
    have hzero := h.doubles a ha b hb (-c) (h.neg_mem _ hc) (-d) (h.neg_mem _ hd) he
    have hba : b = -a := by linear_combination hzero
    exact hn a (by simp) (by rw [← hba]; simp)

private theorem countPerms_of_nodup {α : Type*} [DecidableEq α] {s : Multiset α}
    (hs : s.Nodup) : s.countPerms = s.card.factorial := by
  rw [Multiset.countPerms, Finsupp.multinomial, ← Finsupp.card_toMultiset,
    Multiset.toFinsupp_toMultiset, Finsupp.prod]
  have hprod : (∏ a ∈ s.toFinsupp.support, (s.toFinsupp a).factorial) = 1 := by
    apply Finset.prod_eq_one
    intro a ha
    have hmem : a ∈ s := by simpa using ha
    simp [Multiset.toFinsupp_apply, Multiset.nodup_iff_count_eq_one.mp hs a hmem]
  rw [hprod, Nat.div_one]

/-- The two possible support sizes and their exact numbers of ordered representatives. -/
theorem nonpairable_shapes [DecidableEq F] {H : Set F} (h : FourTermConditions H)
    {s : Multiset F} (hcard : s.card = 6) (hsum : s.sum = 0)
    (hs : ∀ x ∈ s, x ∈ H) (hnp : ¬Pairable s) :
    (s.toFinset.card = 5 ∧ s.countPerms = 360) ∨
      (s.toFinset.card = 6 ∧ s.countPerms = 720) := by
  obtain ⟨_, hm, hu⟩ := nonpairable_multiplicities h hcard hsum hs hnp
  by_cases hdup : ∃ a, 2 ≤ s.count a
  · obtain ⟨a, ha⟩ := hdup
    obtain ⟨t, ht⟩ := Multiset.le_iff_exists_add.mp
      (Multiset.le_count_iff_replicate_le.mp ha)
    have hc : t.card = 4 := by simpa [ht] using hcard
    have hnt : a ∉ t := by
      have hm' := hm a
      simp [ht] at hm'
      simpa using hm'
    have hnodup : t.Nodup := by
      apply Multiset.nodup_iff_count_le_one.mpr
      intro b
      by_cases hba : b = a
      · simp [hba, Multiset.count_eq_zero_of_notMem hnt]
      by_contra! hb
      have hb' : 2 ≤ s.count b := by simpa [ht, hba] using (show 2 ≤ t.count b by omega)
      exact hba (hu b a hb' ha)
    have hf : t.filter (a ≠ ·) = t := Multiset.filter_eq_self.mpr (by
      intro x hx he
      exact hnt (he ▸ hx))
    left
    constructor
    · rw [ht, Multiset.toFinset_add]
      simpa [hnt, Multiset.toFinset_card_of_nodup hnodup] using hc
    · rw [Multiset.countPerms_filter_ne a s, hcard]
      have hca : s.count a = 2 := le_antisymm (hm a) ha
      rw [hca, ht, Multiset.filter_add, hf]
      have hrep : (Multiset.replicate 2 a).filter (a ≠ ·) = 0 := by
        apply Multiset.filter_eq_nil.mpr
        intro b hb
        simpa using (Multiset.eq_of_mem_replicate hb).symm
      rw [hrep, zero_add, countPerms_of_nodup hnodup, hc]
      decide
  · have hn : s.Nodup := by
      apply Multiset.nodup_iff_count_le_one.mpr
      intro a
      have hna : ¬2 ≤ s.count a := fun ha => hdup ⟨a, ha⟩
      omega
    right
    exact ⟨(Multiset.toFinset_card_of_nodup hn).trans hcard,
      by rw [countPerms_of_nodup hn, hcard]; decide⟩

/-- A dyadic root preserving a nonempty antipode-free support is the identity. -/
theorem eq_one_of_preserves_support {S : Set F} (hS : S.Nonempty)
    (hn : ∀ a ∈ S, -a ∉ S) {c : F} (hacts : ∀ a ∈ S, c * a ∈ S)
    {k : ℕ} (hc : c ^ (2 ^ k) = 1) : c = 1 := by
  obtain ⟨a, ha⟩ := hS
  have hpow (j : ℕ) : c ^ j * a ∈ S := by
    induction j with
    | zero => simpa using ha
    | succ j ih => simpa only [pow_succ', mul_assoc] using hacts _ ih
  induction k with
  | zero => simpa using hc
  | succ k ih =>
    rw [pow_succ, pow_mul] at hc
    rcases sq_eq_one_iff.mp hc with hp | hp
    · exact ih hp
    · exact (hn a ha (by simpa [hp] using hpow (2 ^ k))).elim

/-- The orbit of a non-pairable multiset under a finite set of dyadic roots
has one distinct multiset for each multiplier. -/
theorem card_scaled_multisets [DecidableEq F] {H : Set F} (h : FourTermConditions H)
    {s : Multiset F} (hcard : s.card = 6) (hsum : s.sum = 0)
    (hs : ∀ x ∈ s, x ∈ H) (hnp : ¬Pairable s)
    (C : Finset F) {k : ℕ} (hC : ∀ c ∈ C, c ^ (2 ^ k) = 1) :
    (C.image (fun c => s.map (c * ·))).card = C.card := by
  have hn := (nonpairable_multiplicities h hcard hsum hs hnp).1
  obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < s.card)
  apply Finset.card_image_iff.mpr
  intro c hc d hd he
  change s.map (c * ·) = s.map (d * ·) at he
  have hdn : d ≠ 0 := by
    intro hzero
    simpa [hzero] using hC d hd
  have hmul : ∀ x ∈ s, c / d * x ∈ s := by
    intro x hx
    have hcx : c*x ∈ s.map (d * ·) := by
      rw [← he]
      exact Multiset.mem_map.mpr ⟨x, hx, rfl⟩
    obtain ⟨y, hy, heq⟩ := Multiset.mem_map.mp hcx
    have hxy : c / d * x = y := by
      field_simp
      linear_combination -heq
    rwa [hxy]
  have hone := eq_one_of_preserves_support (S := {x | x ∈ s}) ⟨a, ha⟩ hn hmul
    (k := k) (by rw [div_pow, hC c hc, hC d hd, div_one])
  exact (div_eq_one_iff_eq hdn).mp hone

/-- The three antipodal multiplicity patterns, written using the number of pairs. -/
theorem pairable_polynomial (k : ℚ) :
    20 * k + 180 * k * (k - 1) + 120 * k * (k - 1) * (k - 2) =
      15 * (2*k)^3 - 45 * (2*k)^2 + 40 * (2*k) := by ring

/-- Exact integral budget at the first named prime after substituting the orbit identity. -/
theorem first_prime_budget (t : ℕ) :
    let n : ℤ := 2^30
    let p : ℤ := 365375409332725729550921208179070755120141565953
    p * (15*n^3 - 45*n^2 + 40*n + 360*n*t) - n^6 ≤ 15*p*n^3 ↔ t ≤ 2^27-1 := by
  dsimp
  norm_num
  omega

/-- Exact integral budget at the second named prime after substituting the orbit identity. -/
theorem second_prime_budget (t : ℕ) :
    let n : ℤ := 2^30
    let p : ℤ := 730750818665451459101842416358141509841924915201
    p * (15*n^3 - 45*n^2 + 40*n + 360*n*t) - n^6 ≤ 15*p*n^3 ↔ t ≤ 2^27-1 := by
  dsimp
  norm_num
  omega

#print axioms pairable_of_opposites
#print axioms nonpairable_multiplicities
#print axioms nonpairable_shapes
#print axioms eq_one_of_preserves_support
#print axioms card_scaled_multisets
#print axioms pairable_polynomial
#print axioms first_prime_budget
#print axioms second_prime_budget

end ArkLib.ProximityGap.Frontier.SixthMomentAntipodalShape
