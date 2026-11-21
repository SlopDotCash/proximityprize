/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.SixthMomentAntipodalShape

/-!
# Signature checks for triples contained in subgroup cosets

A triple containing an opposite pair sums to its remaining entry. Other triples
are recorded up to a common root-of-unity multiplier. If the nth powers of the
representative sums are nonzero, avoid one and distinguish representatives, then
equal sums in two covered triples force three opposite pairs after negating the
second triple. Their supports also meet. The carrier sets need only have a common
collection of representative signatures satisfying the three tests.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.SingleCosetTripleSignatures

open SixthMomentAntipodalShape (pair Pairable)
variable {F : Type*} [Field F]

/-- Multiply every entry by the given scalar, preserving its multiplicity. -/
def scale (a : F) (T : Multiset F) : Multiset F := T.map (a * ·)

@[simp] private theorem sum_scale (a : F) (T : Multiset F) :
    (scale a T).sum = a*T.sum := by
  induction T using Multiset.induction with
  | empty => simp [scale]
  | cons x t ih => simpa [scale, mul_add] using congrArg (a*x + ·) ih

private theorem scale_scale (a b : F) (T : Multiset F) :
    scale a (scale b T) = scale (a*b) T := by
  simp [scale, Multiset.map_map, mul_assoc]

/-- A triple recorded by deleting an opposite pair or by scaling a representative. -/
def Covered (n : ℕ) (R : Set (Multiset F)) (T : Multiset F) : Prop :=
  (∃ x y : F, y^n = 1 ∧ T = pair x + {y}) ∨
    ∃ V ∈ R, ∃ a : F, a^n = 1 ∧ T = scale a V

/-- The three tests on the normalized representative list. -/
structure TagChecks (n : ℕ) (R : Set (Multiset F)) : Prop where
  nonzero : ∀ T ∈ R, T.sum^n ≠ 0
  ne_one : ∀ T ∈ R, T.sum^n ≠ 1
  injective : R.InjOn (fun T => T.sum^n)

/-- Coverage of an unscaled carrier by the representatives for triples without an opposite pair. -/
def CarrierCover (n : ℕ) (K : Set F) (R : Set (Multiset F)) : Prop :=
  ∀ T : Multiset F, T.card = 3 → (∀ x ∈ T, x ∈ K) →
    (¬∃ x y : F, T = pair x + {y}) →
    ∃ V ∈ R, ∃ k : F, k^n = 1 ∧ T = scale k V

/-- The carrier certificate covers every common root-of-unity translate. -/
theorem covered_of_single_carrier {n : ℕ} {K : Set F} {R : Set (Multiset F)}
    (hK : ∀ x ∈ K, x^n = 1) (hcover : CarrierCover n K R)
    {T : Multiset F} (hc : T.card = 3) (ht : ∀ x ∈ T, x ∈ K)
    {a : F} (ha : a^n = 1) : Covered n R (scale a T) := by
  by_cases h : ∃ x y : F, T = pair x + {y}
  · obtain ⟨x,y,rfl⟩ := h
    left
    refine ⟨a*x, a*y, ?_, ?_⟩
    · rw [mul_pow, ha, hK y (ht y (by simp)), one_mul]
    · simp [scale, pair, mul_neg]
  · obtain ⟨V,hV,k,hk,rfl⟩ := hcover T hc ht h
    exact Or.inr ⟨V,hV,a*k,by rw [mul_pow, ha, hk, one_mul], scale_scale _ _ _⟩

/-- Equal sums of covered triples force identical triples or common uncancelled singletons. -/
theorem equal_or_common_singleton {n : ℕ} (hn : 0 < n) {R : Set (Multiset F)}
    (h : TagChecks n R) {S T : Multiset F} (hS : Covered n R S) (hT : Covered n R T)
    (he : S.sum = T.sum) :
    S = T ∨ ∃ x y z : F, S = pair x + {z} ∧ T = pair y + {z} := by
  rcases hS with ⟨x,z,hz,rfl⟩ | ⟨A,hA,a,ha,rfl⟩ <;>
    rcases hT with ⟨y,w,hw,rfl⟩ | ⟨B,hB,b,hb,rfl⟩
  · have hzw : z = w := by simpa [pair] using he
    subst w
    exact Or.inr ⟨x,y,z,rfl,rfl⟩
  · have e := congrArg (·^n) he
    have hbin : 1 = B.sum^n := by simpa [pair, hz, mul_pow, hb] using e
    exact (h.ne_one B hB hbin.symm).elim
  · have e := congrArg (·^n) he
    have hbin : A.sum^n = 1 := by simpa [pair, hw, mul_pow, ha] using e
    exact (h.ne_one A hA hbin).elim
  · have e := congrArg (·^n) he
    have hbin : A.sum^n = B.sum^n := by simpa [mul_pow, ha, hb] using e
    obtain rfl := h.injective hA hB hbin
    have hB0 : A.sum ≠ 0 := by
      intro hz
      exact h.nonzero A hA (by rw [hz, zero_pow hn.ne'])
    have hab : a = b := mul_right_cancel₀ hB0 (by simpa using he)
    exact Or.inl (hab ▸ rfl)

/-- Negating the second triple turns an equal-sum collision into a pairable sextuple. -/
theorem pairable_of_equal_sum {n : ℕ} (hn : 0 < n) {R : Set (Multiset F)}
    (h : TagChecks n R) {S T : Multiset F} (hc : S.card = 3)
    (hS : Covered n R S) (hT : Covered n R T) (he : S.sum = T.sum) :
    Pairable (S + T.map (- ·)) := by
  rcases equal_or_common_singleton hn h hS hT he with rfl | ⟨x,y,z,rfl,rfl⟩
  · obtain ⟨a,b,c,rfl⟩ := Multiset.card_eq_three.mp hc
    refine ⟨a,b,c,?_⟩
    simp only [pair, Multiset.insert_eq_cons, ← Multiset.singleton_add, Multiset.map_add,
      Multiset.map_singleton]
    ac_rfl
  · refine ⟨x, -y, z, ?_⟩
    simp only [pair, Multiset.map_add, Multiset.map_singleton, neg_neg]
    ac_rfl

/-- Equal-sum covered triples have a common actual field element. -/
theorem common_entry_of_equal_sum {n : ℕ} (hn : 0 < n) {R : Set (Multiset F)}
    (h : TagChecks n R) {S T : Multiset F} (hc : S.card = 3)
    (hS : Covered n R S) (hT : Covered n R T) (he : S.sum = T.sum) :
    ∃ x ∈ S, x ∈ T := by
  rcases equal_or_common_singleton hn h hS hT he with rfl | ⟨x,y,z,rfl,rfl⟩
  · obtain ⟨x,hx⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < S.card)
    exact ⟨x,hx,hx⟩
  · exact ⟨z,by simp,by simp⟩

/-- The multiset of vertices at exponents zero, a and a+b. -/
def gapTriple (g : F) (a b : ℕ) : Multiset F := {1} + {g^a} + {g^(a+b)}

/-- The least of the three cyclic rotations. Comparing all three entries resolves a tied minimum. -/
def leastRotation (a b c : ℕ) : Prop := a ≤ b ∧ a ≤ c ∧ (c = a → b = a)

/-- The rows and the tie and antipode exclusions in the finite scanner. -/
def gapRepresentatives (g : F) (m : ℕ) : Set (Multiset F) :=
  {T | ∃ a b c : ℕ, a+b+c = m ∧ a ≤ m/3 ∧ a ≤ b ∧ b ≤ m-2*a ∧
    ¬(c=a ∧ a<b) ∧ a ≠ m/2 ∧ b ≠ m/2 ∧ c ≠ m/2 ∧ T = gapTriple g a b}

private theorem rotate_gap {g : F} {a b c m : ℕ} (hs : a+b+c=m) (hm : g^m=1) :
    scale (g^a) (gapTriple g b c) = gapTriple g a b := by
  have hc : g^a*g^(b+c) = 1 := by rw [← pow_add, ← Nat.add_assoc, hs, hm]
  simp only [scale, gapTriple, Multiset.map_add, Multiset.map_singleton, mul_one, hc, ← pow_add]
  ac_rfl

private def IsGapTranslate (n : ℕ) (g : F) (T : Multiset F) (a b : ℕ) : Prop :=
  ∃ z : F, z^n=1 ∧ T=scale z (gapTriple g a b)

private theorem rotate_translate {g : F} {n m a b c : ℕ} (hg : g^n=1) (hm : g^m=1)
    (hs : a+b+c=m) {T : Multiset F} (hT : IsGapTranslate n g T a b) :
    IsGapTranslate n g T b c := by
  obtain ⟨z,hz,rfl⟩ := hT
  refine ⟨z*g^a, ?_, ?_⟩
  · rw [mul_pow, ← pow_mul, Nat.mul_comm a n, pow_mul, hg, one_pow, hz, one_mul]
  · rw [← rotate_gap hs hm, scale_scale]

private theorem least_translate {g : F} {n m a b c : ℕ} (hg : g^n=1) (hm : g^m=1)
    (hs : a+b+c=m) {T : Multiset F} (hT : IsGapTranslate n g T a b) :
    ∃ u v w, u+v+w=m ∧ leastRotation u v w ∧ IsGapTranslate n g T u v := by
  by_cases h0 : leastRotation a b c
  · exact ⟨a,b,c,hs,h0,hT⟩
  have h1 := rotate_translate hg hm hs hT
  have hs' : b+c+a=m := by omega
  by_cases hrot : leastRotation b c a
  · exact ⟨b,c,a,hs',hrot,h1⟩
  refine ⟨c,a,b,by omega,?_,rotate_translate hg hm hs' h1⟩
  unfold leastRotation at *
  omega

private theorem no_half_gap {g : F} {n m a b c : ℕ} (hm : m=2*(m/2))
    (hneg : g^(m/2)=-1) (hs : a+b+c=m) {T : Multiset F}
    (hT : IsGapTranslate n g T a b) (hclean : ¬∃ x y : F, T = pair x + {y}) :
    a ≠ m/2 ∧ b ≠ m/2 ∧ c ≠ m/2 := by
  obtain ⟨z,_,rfl⟩ := hT
  simp only [scale, gapTriple, Multiset.map_add, Multiset.map_singleton, mul_one] at hclean
  refine ⟨?_, ?_, ?_⟩
  · intro ha
    apply hclean
    refine ⟨z,z*g^(a+b),?_⟩
    simp only [ha, hneg, mul_neg_one, pair]
  · intro hb
    apply hclean
    refine ⟨z*g^a,z,?_⟩
    simp only [pow_add, hb, hneg, mul_neg, pair]
    ac_rfl
  · intro hc
    have he : a+b=m/2 := by omega
    apply hclean
    refine ⟨z,z*g^a,?_⟩
    simp only [he, hneg, mul_neg_one, pair]
    ac_rfl

private theorem sorted_exponents (g : F) {m : ℕ} (i j k : ℕ)
    (hi : i < m) (hj : j < m) (hk : k < m) :
    ∃ a b c : ℕ, a≤b ∧ b≤c ∧ c < m ∧
      ({g^i}+{g^j}+{g^k} : Multiset F) = {g^a}+{g^b}+{g^c} := by
  rcases le_total i j with h | h <;> rcases le_total i k with h' | h' <;>
    rcases le_total j k with h'' | h''
  all_goals first
    | exact ⟨i,j,k,by omega,by omega,hk,by ac_rfl⟩
    | exact ⟨i,k,j,by omega,by omega,hj,by ac_rfl⟩
    | exact ⟨j,i,k,by omega,by omega,hk,by ac_rfl⟩
    | exact ⟨j,k,i,by omega,by omega,hi,by ac_rfl⟩
    | exact ⟨k,i,j,by omega,by omega,hj,by ac_rfl⟩
    | exact ⟨k,j,i,by omega,by omega,hi,by ac_rfl⟩

/-- Every clean three-element multiset on the actual cyclic carrier is covered by the scanner's
gap rows, including triples with repeated elements. -/
theorem carrierCover_of_gaps [DecidableEq F] {g : F} {m n : ℕ} (hm : m=2*(m/2))
    (hhalf : g^(m/2)=-1) (hfull : g^m=1) (hambient : g^n=1) :
    CarrierCover n ((Finset.range m).image (g ^ ·) : Finset F) (gapRepresentatives g m) := by
  intro T hcard ht hclean
  obtain ⟨x,y,z,rfl⟩ := Multiset.card_eq_three.mp hcard
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp (ht x (by simp))
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp (ht y (by simp))
  obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp (ht z (by simp))
  obtain ⟨i',j',k',hij,hjk,hkm,hord⟩ := sorted_exponents g i j k
    (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) (Finset.mem_range.mp hk)
  simp only [Multiset.insert_eq_cons, ← Multiset.singleton_add, ← add_assoc] at hclean ⊢
  let a := j'-i'
  let b := k'-j'
  let c := m+i'-k'
  have hsum : a+b+c=m := by dsimp [a,b,c]; omega
  have hT : IsGapTranslate n g ({g^i}+{g^j}+{g^k}) a b := by
    refine ⟨g^i', by rw [← pow_mul, Nat.mul_comm i' n, pow_mul, hambient, one_pow], ?_⟩
    rw [hord]
    simp only [scale, gapTriple, Multiset.map_add, Multiset.map_singleton, mul_one, ← pow_add]
    rw [show i'+a = j' by dsimp [a]; omega, show i'+(a+b)=k' by dsimp [a,b]; omega]
  obtain ⟨u,v,w,huvw,hmin,hrep⟩ := least_translate hambient hfull hsum hT
  obtain ⟨hu,hv,hw⟩ := no_half_gap hm hhalf huvw hrep hclean
  obtain ⟨h1,h2,h3⟩ := hmin
  exact ⟨gapTriple g u v, ⟨u,v,w,huvw,by omega,h1,by omega,by omega,hu,hv,hw,rfl⟩,hrep⟩

/-- The scanner's three checks imply that equal sums of triples from any two translated
carrier cosets have an actual common entry and give a pairable signed sextuple. -/
theorem single_coset_collision [DecidableEq F] {g a b : F} {m n : ℕ} (hn : 0 < n)
    (hm : m = 2 * (m / 2)) (hhalf : g ^ (m / 2) = -1) (hfull : g ^ m = 1)
    (hambient : g ^ n = 1) (ha : a ^ n = 1) (hb : b ^ n = 1)
    (htags : TagChecks n (gapRepresentatives g m))
    {S T : Multiset F} (hcS : S.card = 3) (hcT : T.card = 3)
    (hS : ∀ x ∈ S, x ∈ (Finset.range m).image (g ^ ·))
    (hT : ∀ x ∈ T, x ∈ (Finset.range m).image (g ^ ·))
    (he : (scale a S).sum = (scale b T).sum) :
    Pairable (scale a S + (scale b T).map (- ·)) ∧
      (∃ x ∈ scale a S, x ∈ scale b T) := by
  have hK : ∀ x ∈ (Finset.range m).image (g ^ ·), x ^ n = 1 := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    rw [← pow_mul, Nat.mul_comm i n, pow_mul, hambient, one_pow]
  have hcover := carrierCover_of_gaps hm hhalf hfull hambient
  have hs := covered_of_single_carrier hK hcover hcS hS ha
  have ht := covered_of_single_carrier hK hcover hcT hT hb
  have hc : (scale a S).card = 3 := by simpa [scale] using hcS
  exact ⟨pairable_of_equal_sum hn htags hc hs ht he, common_entry_of_equal_sum hn htags hc hs ht he⟩

#print axioms single_coset_collision

/-- Production arithmetic for the clean orbit count after deleting opposite-pair triples. -/
theorem production_necklace_arithmetic :
    ((65538 : ℕ).choose 3 - 65536^2/2)/65536 = 715827883 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel

#print axioms production_necklace_arithmetic
#print axioms carrierCover_of_gaps

#print axioms covered_of_single_carrier
#print axioms equal_or_common_singleton
#print axioms pairable_of_equal_sum
#print axioms common_entry_of_equal_sum

end ArkLib.ProximityGap.Frontier.SingleCosetTripleSignatures
