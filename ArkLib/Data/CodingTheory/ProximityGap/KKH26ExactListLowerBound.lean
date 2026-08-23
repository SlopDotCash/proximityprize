/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26WitnessSpread
import ArkLib.Data.CodingTheory.ProximityGap.GranularityLadderRS

/-!
# The EXACT sub-Johnson list LOWER bound for smooth-domain RS codes (#389)

The smooth-domain Reed–Solomon sub-Johnson list size is the ABF26 "grand list-decoding
challenge" (the Ethereum proximity-prize core): pin `max_w |{codewords agreeing with w on
≥ a points}|` for `w` a non-codeword and `a` below the Johnson radius.  KKH26 give a
counterexample (a super-polynomial lower bound); the matching upper bound is open.

This file lands the **achievability (lower-bound) half**, sharpened to the exact
subset-sum fibre value of `TwoPowerFibreValue.lean`, and **unconditionally** (no
generic-prime hypothesis):

> **`monomial_list_card_ge`** — for the explicit smooth domain `H = ⟨g⟩ ⊆ F_p^×` of order
> `n = 2^μ·m`, the RS code of degree `≤ (r−2)m` (dimension `(r−2)m+1`), and the **monomial
> word** `w(x) = x^{rm}` (`r` even, `2 ≤ r ≤ 2^{μ−1}`), the list at agreement `rm` has
>
>   `|{ codewords c : agreement(c, w) ≥ rm }| ≥ C(2^{μ−1}, r/2)`.

`C(2^{μ−1}, r/2) = N_fib(2^μ, r)` is exactly the maximal subset-sum fibre of `μ_{2^μ}`
(`TwoPowerFibreValue`).  The construction realizes it by the **antipodal fibre family**:
for each `(r/2)`-subset `D ⊆ {0,…,2^{μ−1}−1}` of half-system indices, the `r`-set
`T_D = {±ω^j : j ∈ D}` (`ω = g^m`, `ω^{2^{μ−1}} = −1`) has `Σ T_D = 0`, so the bad-line
codeword `q_{T_D}` (in-tree `badline_pointwise_agreement`) agrees with `x^{rm}` on the
`rm`-point fibre `S_{T_D}`.  The map `D ↦ q_{T_D}` is injective: equal codewords force
`X^{rm} − q` to vanish on `S_{T_D} ∪ S_{T_{D'}}` (`≥ m(r+1) > rm` points) while its degree
is `rm` — a contradiction unless `T_D = T_{D'}`.

The matching UPPER bound (no word beats this) is the recognized wall: it is equivalent to
a small-set Szemerédi–Trotter / additive-energy bound on `μ_n`, and at sub-generic primes
(`p ≤ s^{s/2}`) words DO beat `N_fib` (extra small-integer collisions).  So this is the
exact value of the list for the witnessed word, and an unconditional lower bound on the
maximum.  Issue #389.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open Polynomial Finset
open ProximityGap.SpikeFloor

namespace ArkLib.ProximityGap.KKH26

variable {p : ℕ} [Fact p.Prime]

/-! ## The half-system over `F_p`: `ω = g^m`, `ω^{2^{μ−1}} = −1` -/

/-- `ω = g^m` has order `2^μ` when `g` has order `2^μ·m`. -/
lemma omega_orderOf {μ m : ℕ} {g : ZMod p} (hm : 1 ≤ m) (hg : orderOf g = 2 ^ μ * m) :
    orderOf (g ^ m) = 2 ^ μ := by
  have hg0 : g ≠ 0 := by
    rintro rfl
    have h1 : (0 : ZMod p) ^ (2 ^ μ * m) = 1 := by rw [← hg]; exact pow_orderOf_eq_one 0
    rw [zero_pow (by positivity)] at h1
    exact zero_ne_one h1
  have h1 : (g ^ m) ^ (2 ^ μ) = 1 := by
    rw [← pow_mul, mul_comm m (2 ^ μ), ← hg]; exact pow_orderOf_eq_one g
  have h2 : orderOf (g ^ m) ∣ 2 ^ μ := orderOf_dvd_of_pow_eq_one h1
  have h3 : g ^ (m * orderOf (g ^ m)) = 1 := by
    rw [pow_mul]; exact pow_orderOf_eq_one (g ^ m)
  have h4 : 2 ^ μ * m ∣ m * orderOf (g ^ m) := hg ▸ orderOf_dvd_of_pow_eq_one h3
  rw [mul_comm (2 ^ μ) m] at h4
  have h5 : 2 ^ μ ∣ orderOf (g ^ m) := (Nat.mul_dvd_mul_iff_left (by omega : 0 < m)).mp h4
  exact Nat.dvd_antisymm h2 h5

/-- The half-power of `ω` is `−1` (the unique order-2 element of `F_p^×`). -/
lemma omega_pow_half {μ m : ℕ} (hμ : 1 ≤ μ) {g : ZMod p} (hm : 1 ≤ m)
    (hg : orderOf g = 2 ^ μ * m) :
    (g ^ m) ^ (2 ^ (μ - 1)) = -1 := by
  have hord := omega_orderOf hm hg
  have hsq : ((g ^ m) ^ (2 ^ (μ - 1))) ^ 2 = 1 := by
    rw [← pow_mul]
    have : 2 ^ (μ - 1) * 2 = 2 ^ μ := by
      rw [← pow_succ]; congr 1; omega
    rw [this, ← hord]; exact pow_orderOf_eq_one _
  have hne1 : (g ^ m) ^ (2 ^ (μ - 1)) ≠ 1 := by
    intro hc
    have hdvd : orderOf (g ^ m) ∣ 2 ^ (μ - 1) := orderOf_dvd_of_pow_eq_one hc
    rw [hord] at hdvd
    have hlt : (2 : ℕ) ^ (μ - 1) < 2 ^ μ := by
      apply Nat.pow_lt_pow_right (by norm_num); omega
    exact absurd (Nat.le_of_dvd (by positivity) hdvd) (by omega)
  rw [pow_two] at hsq
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · exact absurd h hne1
  · exact h

/-! ## The antipodal fibre family `T_D = {±ω^j : j ∈ D}` -/

/-- The antipodal `r`-set indexed by an `(r/2)`-subset `D` of half-system indices. -/
def antiSet (ω : ZMod p) (D : Finset ℕ) : Finset (ZMod p) :=
  D.image (fun j => ω ^ j) ∪ D.image (fun j => -(ω ^ j))

variable {ω : ZMod p} {s half : ℕ}

/-- `ω`-powers are injective below the order (manual, via field cancellation). -/
lemma omega_pow_injOn (hω : orderOf ω = s) :
    Set.InjOn (fun j => ω ^ j) (Set.Iio s) := by
  intro i hi j hj heq
  simp only [Set.mem_Iio] at hi hj
  have hω0 : ω ≠ 0 := by
    rintro rfl
    have h1 : (0 : ZMod p) ^ s = 1 := by rw [← hω]; exact pow_orderOf_eq_one 0
    rw [zero_pow (by omega)] at h1; exact zero_ne_one h1
  have main : ∀ a b, a ≤ b → b < s → ω ^ a = ω ^ b → a = b := by
    intro a b hab hb heqab
    have h2 : ω ^ a * ω ^ (b - a) = ω ^ a * 1 := by
      rw [mul_one, ← pow_add, show a + (b - a) = b from by omega, heqab]
    have h3 : ω ^ (b - a) = 1 := mul_left_cancel₀ (pow_ne_zero a hω0) h2
    have h4 : s ∣ b - a := hω ▸ orderOf_dvd_of_pow_eq_one h3
    have h5 : b - a = 0 := Nat.eq_zero_of_dvd_of_lt h4 (lt_of_le_of_lt (Nat.sub_le b a) hb)
    omega
  rcases le_total i j with hle | hle
  · exact main i j hle hj heq
  · exact (main j i hle hi heq.symm).symm

/-- `−ω^j = ω^{j+half}` on the half-system. -/
lemma neg_omega_pow (hωhalf : ω ^ half = -1) (j : ℕ) :
    -(ω ^ j) = ω ^ (j + half) := by
  rw [pow_add, hωhalf, mul_neg_one]

/-- The positive half is injective on `D`. -/
lemma pos_injOn (hω : orderOf ω = s) {D : Finset ℕ} (hD : D ⊆ range half)
    (hs : s = 2 * half) : Set.InjOn (fun j => ω ^ j) (D : Set ℕ) := by
  intro a ha b hb hab
  simp only [Finset.mem_coe] at ha hb
  exact omega_pow_injOn hω
    (by have := mem_range.mp (hD ha); simp only [Set.mem_Iio]; omega)
    (by have := mem_range.mp (hD hb); simp only [Set.mem_Iio]; omega) hab

/-- The negative half is injective on `D`. -/
lemma neg_injOn (hω : orderOf ω = s) {D : Finset ℕ} (hD : D ⊆ range half)
    (hs : s = 2 * half) : Set.InjOn (fun j => -(ω ^ j)) (D : Set ℕ) := by
  intro a ha b hb hab
  simp only [Finset.mem_coe] at ha hb
  simp only [neg_inj] at hab
  exact omega_pow_injOn hω
    (by have := mem_range.mp (hD ha); simp only [Set.mem_Iio]; omega)
    (by have := mem_range.mp (hD hb); simp only [Set.mem_Iio]; omega) hab

/-- The two halves are disjoint as finsets. -/
lemma anti_disjoint (hω : orderOf ω = s) (hωhalf : ω ^ half = -1) {D : Finset ℕ}
    (hD : D ⊆ range half) (hs : s = 2 * half) :
    Disjoint (D.image (fun j => ω ^ j)) (D.image (fun j => -(ω ^ j))) := by
  rw [Finset.disjoint_left]
  intro x hx1 hx2
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx1
  obtain ⟨b, hb, hb2⟩ := Finset.mem_image.mp hx2
  rw [neg_omega_pow hωhalf] at hb2
  have ha' := mem_range.mp (hD ha); have hb' := mem_range.mp (hD hb)
  have := omega_pow_injOn hω (by simp only [Set.mem_Iio]; omega : a ∈ Set.Iio s)
    (by simp only [Set.mem_Iio]; omega : b + half ∈ Set.Iio s) hb2.symm
  omega

/-- The antipodal set lies in `G = ⟨ω⟩` (the order-`s` subgroup). -/
lemma antiSet_subset_G (hs : s = 2 * half) (hωhalf : ω ^ half = -1)
    {D : Finset ℕ} (hD : D ⊆ range half) :
    antiSet ω D ⊆ (range s).image (fun i => ω ^ i) := by
  intro x hx
  rw [antiSet, Finset.mem_union] at hx
  rcases hx with hx | hx
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨j, mem_range.mpr (by
      have := mem_range.mp (hD hj); omega), rfl⟩
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨j + half, mem_range.mpr ?_, ?_⟩
    · have := mem_range.mp (hD hj); omega
    · exact (neg_omega_pow hωhalf j).symm

/-- The two halves are disjoint, so the antipodal set has `2|D|` elements. -/
lemma antiSet_card (hs : s = 2 * half) (hω : orderOf ω = s) (hωhalf : ω ^ half = -1)
    {D : Finset ℕ} (hD : D ⊆ range half) :
    (antiSet ω D).card = 2 * D.card := by
  rw [antiSet, Finset.card_union_of_disjoint (anti_disjoint hω hωhalf hD hs),
    Finset.card_image_of_injOn (pos_injOn hω hD hs),
    Finset.card_image_of_injOn (neg_injOn hω hD hs)]
  ring

/-- The antipodal set has sum zero (each `ω^j` cancels its antipode `−ω^j`). -/
lemma antiSet_sum (hs : s = 2 * half) (hω : orderOf ω = s) (hωhalf : ω ^ half = -1)
    {D : Finset ℕ} (hD : D ⊆ range half) :
    ∑ x ∈ antiSet ω D, x = 0 := by
  rw [antiSet, Finset.sum_union (anti_disjoint hω hωhalf hD hs),
    Finset.sum_image (pos_injOn hω hD hs), Finset.sum_image (neg_injOn hω hD hs),
    ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun j _ => by ring

/-- Membership criterion: for `j < half`, `ω^j ∈ T_D ↔ j ∈ D` (the positive half is
disjoint from the negative half), giving recovery of `D` from `T_D`. -/
lemma omega_pow_mem_antiSet (hs : s = 2 * half) (hω : orderOf ω = s)
    (hωhalf : ω ^ half = -1) {D : Finset ℕ} (hD : D ⊆ range half) {j : ℕ}
    (hj : j < half) :
    ω ^ j ∈ antiSet ω D ↔ j ∈ D := by
  have hinj : Set.InjOn (fun j => ω ^ j) (Set.Iio s) := omega_pow_injOn hω
  rw [antiSet, Finset.mem_union]
  constructor
  · rintro (h | h)
    · obtain ⟨b, hb, hbe⟩ := Finset.mem_image.mp h
      have hb' := mem_range.mp (hD hb)
      have : j = b := hinj (by simp only [Set.mem_Iio]; omega)
        (by simp only [Set.mem_Iio]; omega) hbe.symm
      rwa [this]
    · exfalso
      obtain ⟨b, hb, hbe⟩ := Finset.mem_image.mp h
      rw [neg_omega_pow hωhalf] at hbe
      have hb' := mem_range.mp (hD hb)
      have : j = b + half := hinj (by simp only [Set.mem_Iio]; omega)
        (by simp only [Set.mem_Iio]; omega) hbe.symm
      omega
  · intro h
    exact Or.inl (Finset.mem_image_of_mem (fun k => ω ^ k) h)

/-- `D ↦ T_D` is injective on `(r/2)`-subsets of the half-system. -/
lemma antiSet_injOn (hs : s = 2 * half) (hω : orderOf ω = s) (hωhalf : ω ^ half = -1) :
    Set.InjOn (antiSet ω) ((range half).powerset : Set (Finset ℕ)) := by
  intro D₁ hD₁ D₂ hD₂ heq
  rw [Finset.coe_powerset] at hD₁ hD₂
  simp only [Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset] at hD₁ hD₂
  ext j
  by_cases hj : j < half
  · rw [← omega_pow_mem_antiSet hs hω hωhalf hD₁ hj,
      ← omega_pow_mem_antiSet hs hω hωhalf hD₂ hj, heq]
  · constructor <;> intro h
    · exact absurd (mem_range.mp (hD₁ h)) hj
    · exact absurd (mem_range.mp (hD₂ h)) hj

/-! ## The odd antipodal family `T_D = {1} ∪ {±ω^j : j ∈ D}` (singleton + pairs) -/

/-- The odd antipodal `r`-set: the unit `1 = ω^0` plus `(r−1)/2` antipodal pairs. -/
def antiSetOdd (ω : ZMod p) (D : Finset ℕ) : Finset (ZMod p) := insert 1 (antiSet ω D)

/-- `1 = ω^0 ∉ antiSet ω D` when `0 ∉ D` — the singleton is genuinely new. -/
lemma one_not_mem_antiSet (hs : s = 2 * half) (hhalf : 1 ≤ half) (hω : orderOf ω = s)
    (hωhalf : ω ^ half = -1) {D : Finset ℕ} (hD : D ⊆ range half) (h0 : 0 ∉ D) :
    (1 : ZMod p) ∉ antiSet ω D := by
  have h1 : (1 : ZMod p) = ω ^ 0 := (pow_zero ω).symm
  rw [h1, omega_pow_mem_antiSet hs hω hωhalf hD (by omega)]
  exact h0

lemma antiSetOdd_card (hs : s = 2 * half) (hhalf : 1 ≤ half) (hω : orderOf ω = s)
    (hωhalf : ω ^ half = -1) {D : Finset ℕ} (hD : D ⊆ range half) (h0 : 0 ∉ D) :
    (antiSetOdd ω D).card = 2 * D.card + 1 := by
  rw [antiSetOdd, Finset.card_insert_of_notMem
    (one_not_mem_antiSet hs hhalf hω hωhalf hD h0), antiSet_card hs hω hωhalf hD]

lemma antiSetOdd_sum (hs : s = 2 * half) (hhalf : 1 ≤ half) (hω : orderOf ω = s)
    (hωhalf : ω ^ half = -1) {D : Finset ℕ} (hD : D ⊆ range half) (h0 : 0 ∉ D) :
    ∑ x ∈ antiSetOdd ω D, x = 1 := by
  rw [antiSetOdd, Finset.sum_insert (one_not_mem_antiSet hs hhalf hω hωhalf hD h0),
    antiSet_sum hs hω hωhalf hD, add_zero]

lemma antiSetOdd_subset_G (hs : s = 2 * half) (hhalf : 1 ≤ half) (hω : orderOf ω = s)
    (hωhalf : ω ^ half = -1) {D : Finset ℕ} (hD : D ⊆ range half) :
    antiSetOdd ω D ⊆ (range s).image (fun i => ω ^ i) := by
  rw [antiSetOdd]
  refine Finset.insert_subset ?_ (antiSet_subset_G hs hωhalf hD)
  exact Finset.mem_image.mpr ⟨0, mem_range.mpr (by omega), pow_zero ω⟩

/-- `D ↦ T_D^odd` is injective on `(r−1)/2`-subsets of the punctured half-system. -/
lemma antiSetOdd_injOn (hs : s = 2 * half) (hhalf : 1 ≤ half) (hω : orderOf ω = s)
    (hωhalf : ω ^ half = -1) :
    Set.InjOn (antiSetOdd ω) (((range half).erase 0).powerset : Set (Finset ℕ)) := by
  intro D₁ hD₁ D₂ hD₂ heq
  rw [Finset.coe_powerset] at hD₁ hD₂
  simp only [Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset] at hD₁ hD₂
  have hsub₁ : D₁ ⊆ range half := fun x hx => Finset.mem_of_mem_erase (hD₁ hx)
  have hsub₂ : D₂ ⊆ range half := fun x hx => Finset.mem_of_mem_erase (hD₂ hx)
  ext j
  by_cases hj : j < half
  · by_cases hj0 : j = 0
    · subst hj0
      constructor <;> intro h
      · exact absurd rfl (Finset.mem_erase.mp (hD₁ h)).1
      · exact absurd rfl (Finset.mem_erase.mp (hD₂ h)).1
    · -- j ≥ 1: ω^j ≠ 1, so ω^j ∈ antiSetOdd ↔ ω^j ∈ antiSet ↔ j ∈ D
      have hne1 : ω ^ j ≠ 1 := by
        rw [show (1 : ZMod p) = ω ^ 0 from (pow_zero ω).symm]
        intro hc
        exact hj0 (omega_pow_injOn hω (by simp only [Set.mem_Iio]; omega)
          (by simp only [Set.mem_Iio]; omega) hc)
      have hmemOdd : ∀ {D : Finset ℕ}, D ⊆ range half →
          (ω ^ j ∈ antiSetOdd ω D ↔ j ∈ D) := by
        intro D hDsub
        rw [antiSetOdd, Finset.mem_insert]
        rw [omega_pow_mem_antiSet hs hω hωhalf hDsub hj]
        constructor
        · rintro (h | h)
          · exact absurd h hne1
          · exact h
        · exact fun h => Or.inr h
      rw [← hmemOdd hsub₁, ← hmemOdd hsub₂, heq]
  · constructor <;> intro h
    · exact absurd (mem_range.mp (hsub₁ h)) hj
    · exact absurd (mem_range.mp (hsub₂ h)) hj

/-! ## The evaluation-domain embedding and the index-level fibre count -/

/-- The smooth evaluation domain `i ↦ g^i : Fin n ↪ F_p` when `g` has order `n`. -/
def domEmb {n : ℕ} {g : ZMod p} (hg : orderOf g = n) : Fin n ↪ ZMod p where
  toFun i := g ^ (i : ℕ)
  inj' i j hij := Fin.ext (omega_pow_injOn hg
    (by simp only [Set.mem_Iio]; exact i.isLt)
    (by simp only [Set.mem_Iio]; exact j.isLt) hij)

/-- **Index-level fibre count.**  The number of indices `i : Fin (s·m)` whose domain
point `g^i` has `m`-th power in `S` is exactly `m·|S|` — the index form of the in-tree
`fiber_count`, via the injective `i ↦ g^i`. -/
lemma index_fiber_count {s m : ℕ} {g : ZMod p} (hm : 1 ≤ m) (hs : 1 ≤ s)
    (hg : orderOf g = s * m) (S : Finset (ZMod p))
    (hS : S ⊆ (range s).image (fun j => (g ^ m) ^ j)) :
    (Finset.univ.filter (fun i : Fin (s * m) => (g ^ (i : ℕ)) ^ m ∈ S)).card
      = m * S.card := by
  classical
  rw [← fiber_count hm hs hg S hS]
  refine Finset.card_bij (fun (a : Fin (s * m)) _ => g ^ (a : ℕ)) ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_filter] at ha ⊢
    refine ⟨Finset.mem_image.mpr ⟨(a : ℕ), mem_range.mpr a.isLt, rfl⟩, ha.2⟩
  · intro a ha b hb hab
    exact Fin.ext (omega_pow_injOn hg
      (by simp only [Set.mem_Iio]; exact a.isLt)
      (by simp only [Set.mem_Iio]; exact b.isLt) hab)
  · intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx.1
    refine ⟨⟨j, mem_range.mp hj⟩, ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hx.2⟩

/-! ## The main theorem: the exact list lower bound -/

open Classical in
/-- **THE EXACT SUB-JOHNSON LIST LOWER BOUND (#389).**  For the explicit smooth domain
`H = ⟨g⟩ ⊆ F_p^×` of order `n = 2^μ·m`, the Reed–Solomon code of degree `≤ (r−2)m`
(`r` even, `2 ≤ r ≤ 2^{μ−1}`), and the **monomial word** `w(x) = x^{rm}`, the sub-Johnson
list at agreement `rm` has size at least the maximal subset-sum fibre

  `C(2^{μ−1}, r/2) = N_fib(2^μ, r)`  (`TwoPowerFibreValue`).

Unconditional in `p` (no generic-prime hypothesis): the antipodal fibre family realizes
distinct codewords directly.  The matching upper bound is the recognized wall. -/
theorem monomial_list_card_ge {μ m r : ℕ} (hμ : 1 ≤ μ) (hm : 1 ≤ m) (hr2 : 2 ≤ r)
    (hreven : r % 2 = 0) (hr : r ≤ 2 ^ (μ - 1))
    {g : ZMod p} (hg : orderOf g = 2 ^ μ * m) :
    NeZero (2 ^ μ * m) ∧ ∃ w : Fin (2 ^ μ * m) → ZMod p,
      (2 ^ (μ - 1)).choose (r / 2) ≤
        (Finset.univ.filter (fun c : Fin (2 ^ μ * m) → ZMod p =>
          c ∈ rsCode (domEmb hg) ((r - 2) * m + 1) ∧
            r * m ≤ (Finset.univ.filter (fun i => c i = w i)).card)).card := by
  classical
  have hn0 : 0 < 2 ^ μ * m := by positivity
  have hNe : NeZero (2 ^ μ * m) := ⟨by omega⟩
  refine ⟨hNe, fun i => (g ^ (i : ℕ)) ^ (r * m), ?_⟩
  -- abbreviations
  set s := 2 ^ μ with hsdef
  set half := 2 ^ (μ - 1) with hhalfdef
  have hs2 : s = 2 * half := by
    rw [hsdef, hhalfdef, ← pow_succ']; congr 1; omega
  have hhalf1 : 1 ≤ half := Nat.one_le_two_pow
  have hs1 : 1 ≤ s := Nat.one_le_two_pow
  set ω := g ^ m with hωdef
  have hω : orderOf ω = s := by rw [hωdef, hsdef]; exact omega_orderOf hm hg
  have hωhalf : ω ^ half = -1 := by rw [hωdef, hhalfdef]; exact omega_pow_half hμ hm hg
  set w : Fin (2 ^ μ * m) → ZMod p := fun i => (g ^ (i : ℕ)) ^ (r * m) with hwdef
  -- the codeword polynomial for each index family D
  set Idx := (range half).powersetCard (r / 2) with hIdxdef
  -- per-D data
  have hcardT : ∀ D ∈ Idx, (antiSet ω D).card = r := by
    intro D hD
    obtain ⟨hDsub, hDcard⟩ := Finset.mem_powersetCard.mp hD
    rw [antiSet_card hs2 hω hωhalf hDsub, hDcard]
    omega
  have hsumT : ∀ D ∈ Idx, ∑ x ∈ antiSet ω D, x = 0 := by
    intro D hD
    exact antiSet_sum hs2 hω hωhalf (Finset.mem_powersetCard.mp hD).1
  have hTsub : ∀ D ∈ Idx, antiSet ω D ⊆ (range s).image (fun i => ω ^ i) := by
    intro D hD
    exact antiSet_subset_G hs2 hωhalf (Finset.mem_powersetCard.mp hD).1
  -- choose the badline codeword polynomial
  have hbl : ∀ D ∈ Idx, ∃ q : (ZMod p)[X], q.natDegree ≤ (r - 2) * m ∧
      ∀ x : ZMod p, x ^ m ∈ antiSet ω D → x ^ (r * m) = q.eval x := by
    intro D hD
    obtain ⟨q, hqdeg, hqagree⟩ :=
      badline_pointwise_agreement hm (antiSet ω D) (by rw [hcardT D hD]; exact hr2)
    rw [hcardT D hD] at hqdeg hqagree
    refine ⟨q, hqdeg, fun x hx => ?_⟩
    have := hqagree x hx
    rw [hsumT D hD, neg_zero, zero_mul, add_zero] at this
    exact this
  choose qpoly hqdeg hqagree using hbl
  -- the codeword as a word
  set cw : (D : Finset ℕ) → D ∈ Idx → (Fin (2 ^ μ * m) → ZMod p) :=
    fun D hD i => (qpoly D hD).eval (g ^ (i : ℕ)) with hcwdef
  -- membership in rsCode
  have hcw_mem : ∀ D (hD : D ∈ Idx),
      cw D hD ∈ rsCode (domEmb hg) ((r - 2) * m + 1) := by
    intro D hD
    refine ⟨qpoly D hD, ?_, by funext i; rfl⟩
    refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
    exact_mod_cast Nat.lt_succ_of_le (hqdeg D hD)
  -- agreement lower bound: rm ≤ #{ i : cw i = w i }
  have hcw_agree : ∀ D (hD : D ∈ Idx),
      r * m ≤ (Finset.univ.filter (fun i => cw D hD i = w i)).card := by
    intro D hD
    have hsub : (Finset.univ.filter
          (fun i : Fin (2 ^ μ * m) => (g ^ (i : ℕ)) ^ m ∈ antiSet ω D))
        ⊆ Finset.univ.filter (fun i => cw D hD i = w i) := by
      intro i hi
      rw [Finset.mem_filter] at hi ⊢
      refine ⟨Finset.mem_univ i, ?_⟩
      rw [hcwdef, hwdef]
      exact (hqagree D hD (g ^ (i : ℕ)) hi.2).symm
    have hfib : (Finset.univ.filter
        (fun i : Fin (2 ^ μ * m) => (g ^ (i : ℕ)) ^ m ∈ antiSet ω D)).card = m * r := by
      have := index_fiber_count (s := s) (m := m) hm hs1 (by rw [hsdef]; exact hg)
        (antiSet ω D) (hTsub D hD)
      rw [this, hcardT D hD]
    calc r * m = m * r := by ring
      _ = (Finset.univ.filter
            (fun i : Fin (2 ^ μ * m) => (g ^ (i : ℕ)) ^ m ∈ antiSet ω D)).card := hfib.symm
      _ ≤ _ := Finset.card_le_card hsub
  -- the codeword map lands in the list
  set L := Finset.univ.filter (fun c : Fin (2 ^ μ * m) → ZMod p =>
    c ∈ rsCode (domEmb hg) ((r - 2) * m + 1) ∧
      r * m ≤ (Finset.univ.filter (fun i => c i = w i)).card) with hLdef
  have hmaps : ∀ D (hD : D ∈ Idx), cw D hD ∈ L := by
    intro D hD
    rw [hLdef, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hcw_mem D hD, hcw_agree D hD⟩
  -- degree bookkeeping
  have hrm1 : (r - 2) * m < r * m := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
  have hrn : r ≤ 2 ^ μ := le_trans hr (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hrmn : (r - 2) * m < 2 ^ μ * m :=
    Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
  -- the codeword map is injective on Idx (the load-bearing degree argument)
  have hinj : ∀ D₁ (hD₁ : D₁ ∈ Idx) D₂ (hD₂ : D₂ ∈ Idx),
      cw D₁ hD₁ = cw D₂ hD₂ → D₁ = D₂ := by
    intro D₁ hD₁ D₂ hD₂ hcweq
    -- equal words ⟹ equal polynomials (n > deg)
    have hpoly : qpoly D₁ hD₁ = qpoly D₂ hD₂ := by
      have hsubz : qpoly D₁ hD₁ - qpoly D₂ hD₂ = 0 := by
        refine Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero
          (s := Finset.univ.image (domEmb hg)) ?_ ?_
        · rw [Finset.card_image_of_injective _ (domEmb hg).injective,
            Finset.card_univ, Fintype.card_fin]
          refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) ?_
          rw [max_lt_iff]
          refine ⟨lt_of_le_of_lt Polynomial.degree_le_natDegree ?_,
                  lt_of_le_of_lt Polynomial.degree_le_natDegree ?_⟩ <;>
            exact_mod_cast lt_of_le_of_lt (hqdeg _ _) hrmn
        · intro x hx
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
          have hi := congrFun hcweq i
          simp only [hcwdef] at hi
          rw [Polynomial.eval_sub, sub_eq_zero]
          exact hi
      exact sub_eq_zero.mp hsubz
    -- equal polynomials ⟹ T_{D₁} = T_{D₂} via the union-degree contradiction
    have hTeq : antiSet ω D₁ = antiSet ω D₂ := by
      by_contra hTne
      have hSunsub : antiSet ω D₁ ∪ antiSet ω D₂ ⊆ (range s).image (fun i => ω ^ i) :=
        Finset.union_subset (hTsub D₁ hD₁) (hTsub D₂ hD₂)
      -- |Sun| ≥ r+1 (distinct r-sets)
      have hSuncard : r + 1 ≤ (antiSet ω D₁ ∪ antiSet ω D₂).card := by
        have hsub2 : ¬ antiSet ω D₂ ⊆ antiSet ω D₁ := by
          intro hsub
          exact hTne (Finset.eq_of_subset_of_card_le hsub
            (by rw [hcardT D₁ hD₁, hcardT D₂ hD₂])).symm
        obtain ⟨b, hbB, hbA⟩ := Finset.not_subset.mp hsub2
        have hss : antiSet ω D₁ ⊂ antiSet ω D₁ ∪ antiSet ω D₂ := by
          refine Finset.ssubset_iff_of_subset Finset.subset_union_left |>.mpr ⟨b, ?_, hbA⟩
          exact Finset.mem_union_right _ hbB
        have := Finset.card_lt_card hss
        rw [hcardT D₁ hD₁] at this
        omega
      -- the union value-fibre (image under the injective embedding `domEmb hg`)
      set U := (Finset.univ.filter
        (fun i : Fin (2 ^ μ * m) => (g ^ (i : ℕ)) ^ m ∈ antiSet ω D₁ ∪ antiSet ω D₂)).image
          (domEmb hg) with hUdef
      have hUcard : U.card = m * (antiSet ω D₁ ∪ antiSet ω D₂).card := by
        rw [hUdef, Finset.card_image_of_injective _ (domEmb hg).injective]
        exact index_fiber_count (s := s) (m := m) hm hs1
          (by rw [hsdef]; exact hg) _ hSunsub
      have hWne : (X ^ (r * m) - qpoly D₁ hD₁ : (ZMod p)[X]) ≠ 0 := by
        intro h0
        have hWeq := sub_eq_zero.mp h0
        have h1 : (X ^ (r * m) : (ZMod p)[X]).natDegree = r * m :=
          Polynomial.natDegree_X_pow _
        rw [hWeq] at h1
        have := hqdeg D₁ hD₁
        omega
      have hdeg : (X ^ (r * m) - qpoly D₁ hD₁ : (ZMod p)[X]).degree ≤ (r * m : ℕ) := by
        refine le_trans (Polynomial.degree_sub_le _ _) ?_
        rw [max_le_iff]
        refine ⟨?_, ?_⟩
        · rw [Polynomial.degree_X_pow]
        · exact le_trans Polynomial.degree_le_natDegree
            (by exact_mod_cast le_trans (hqdeg D₁ hD₁) (le_of_lt hrm1))
      have hUgt : r * m < U.card := by
        rw [hUcard]
        have h1 : m * (r + 1) ≤ m * (antiSet ω D₁ ∪ antiSet ω D₂).card :=
          Nat.mul_le_mul_left m hSuncard
        have h2 : m * (r + 1) = r * m + m := by ring
        omega
      have hvanish : ∀ x ∈ U, (X ^ (r * m) - qpoly D₁ hD₁ : (ZMod p)[X]).eval x = 0 := by
        intro x hx
        rw [hUdef] at hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        have hmem := (Finset.mem_filter.mp hi).2
        show (X ^ (r * m) - qpoly D₁ hD₁ : (ZMod p)[X]).eval (g ^ (i : ℕ)) = 0
        rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero]
        rw [Finset.mem_union] at hmem
        rcases hmem with h | h
        · exact hqagree D₁ hD₁ (g ^ (i : ℕ)) h
        · rw [hpoly]; exact hqagree D₂ hD₂ (g ^ (i : ℕ)) h
      exact hWne (Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero (s := U)
        (lt_of_le_of_lt hdeg (by exact_mod_cast hUgt)) hvanish)
    -- conclude D₁ = D₂ from antiSet injectivity
    have hD1p : D₁ ∈ (range half).powerset := Finset.mem_powerset.mpr
      (Finset.mem_powersetCard.mp hD₁).1
    have hD2p : D₂ ∈ (range half).powerset := Finset.mem_powerset.mpr
      (Finset.mem_powersetCard.mp hD₂).1
    exact antiSet_injOn hs2 hω hωhalf hD1p hD2p hTeq
  -- assemble the cardinality bound
  have hcard : (2 ^ (μ - 1)).choose (r / 2) = Idx.card := by
    rw [hIdxdef, Finset.card_powersetCard, Finset.card_range, hhalfdef]
  rw [hcard]
  refine Finset.card_le_card_of_injOn (fun D => if hD : D ∈ Idx then cw D hD else w) ?_ ?_
  · intro D hD
    rw [Finset.mem_coe] at hD
    simp only [dif_pos hD]
    exact Finset.mem_coe.mpr (hmaps D hD)
  · intro D₁ hD₁ D₂ hD₂ heq
    rw [Finset.mem_coe] at hD₁ hD₂
    simp only [dif_pos hD₁, dif_pos hD₂] at heq
    exact hinj D₁ hD₁ D₂ hD₂ heq

/-! ## The generic equal-sum-family achievability lemma (all `r`, via any family) -/

open Classical in
/-- **Generic achievability.**  Any family `Fam` of distinct `r`-subsets of `G = ⟨g^m⟩`,
all with the SAME sum `σ`, yields `|Fam|` distinct codewords of `rsCode (domEmb hg)
((r−2)m+1)` agreeing on `≥ rm` points with the word `w(x) = x^{rm} − σ·x^{(r−1)m}`.
(The map `T ↦ q_T` is injective by the union-fibre degree contradiction; no index
structure needed since the `T`'s are already distinct.)  This is the construction-free
core: feed it the antipodal family (`σ = 0`, even `r`) or the singleton-plus-pairs family
(`σ = 1`, odd `r`) to get the closed-form bounds. -/
theorem equalSum_family_list_card_ge {μ m r : ℕ} (hμ : 1 ≤ μ) (hm : 1 ≤ m)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (μ - 1)) {g : ZMod p} (hg : orderOf g = 2 ^ μ * m)
    (σ : ZMod p) (Fam : Finset (Finset (ZMod p)))
    (hFamG : ∀ T ∈ Fam, T ⊆ (range (2 ^ μ)).image (fun j => (g ^ m) ^ j))
    (hFamcard : ∀ T ∈ Fam, T.card = r) (hFamsum : ∀ T ∈ Fam, ∑ x ∈ T, x = σ) :
    Fam.card ≤ (Finset.univ.filter (fun c : Fin (2 ^ μ * m) → ZMod p =>
      c ∈ rsCode (domEmb hg) ((r - 2) * m + 1) ∧ r * m ≤ (Finset.univ.filter
        (fun i => c i = (g ^ (i : ℕ)) ^ (r * m)
          - σ * (g ^ (i : ℕ)) ^ ((r - 1) * m))).card)).card := by
  classical
  have hs1 : (1 : ℕ) ≤ 2 ^ μ := Nat.one_le_two_pow
  have hrm1 : (r - 2) * m < r * m := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
  have hrn : r ≤ 2 ^ μ := le_trans hr (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hrmn : (r - 2) * m < 2 ^ μ * m := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
  set w : Fin (2 ^ μ * m) → ZMod p :=
    fun i => (g ^ (i : ℕ)) ^ (r * m) - σ * (g ^ (i : ℕ)) ^ ((r - 1) * m) with hwdef
  -- the badline codeword polynomial for each member T
  have hbl : ∀ T ∈ Fam, ∃ q : (ZMod p)[X], q.natDegree ≤ (r - 2) * m ∧
      ∀ x : ZMod p, x ^ m ∈ T →
        x ^ (r * m) - σ * x ^ ((r - 1) * m) = q.eval x := by
    intro T hT
    obtain ⟨q, hqdeg, hqagree⟩ :=
      badline_pointwise_agreement hm T (by rw [hFamcard T hT]; exact hr2)
    rw [hFamcard T hT] at hqdeg hqagree
    refine ⟨q, hqdeg, fun x hx => ?_⟩
    have := hqagree x hx
    rw [hFamsum T hT] at this
    rw [← this]; ring
  choose qpoly hqdeg hqagree using hbl
  set cw : (T : Finset (ZMod p)) → T ∈ Fam → (Fin (2 ^ μ * m) → ZMod p) :=
    fun T hT i => (qpoly T hT).eval (g ^ (i : ℕ)) with hcwdef
  -- membership in rsCode
  have hcw_mem : ∀ T (hT : T ∈ Fam), cw T hT ∈ rsCode (domEmb hg) ((r - 2) * m + 1) := by
    intro T hT
    refine ⟨qpoly T hT, ?_, by funext i; rfl⟩
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree
      (by exact_mod_cast Nat.lt_succ_of_le (hqdeg T hT))
  -- agreement lower bound
  have hcw_agree : ∀ T (hT : T ∈ Fam),
      r * m ≤ (Finset.univ.filter (fun i => cw T hT i = w i)).card := by
    intro T hT
    have hsub : (Finset.univ.filter
          (fun i : Fin (2 ^ μ * m) => (g ^ (i : ℕ)) ^ m ∈ T))
        ⊆ Finset.univ.filter (fun i => cw T hT i = w i) := by
      intro i hi
      rw [Finset.mem_filter] at hi ⊢
      refine ⟨Finset.mem_univ i, ?_⟩
      rw [hcwdef, hwdef]
      exact (hqagree T hT (g ^ (i : ℕ)) hi.2).symm
    have hfib : (Finset.univ.filter
        (fun i : Fin (2 ^ μ * m) => (g ^ (i : ℕ)) ^ m ∈ T)).card = m * r := by
      have := index_fiber_count (s := 2 ^ μ) (m := m) hm hs1 hg T (hFamG T hT)
      rw [this, hFamcard T hT]
    calc r * m = m * r := by ring
      _ = _ := hfib.symm
      _ ≤ _ := Finset.card_le_card hsub
  set L := Finset.univ.filter (fun c : Fin (2 ^ μ * m) → ZMod p =>
    c ∈ rsCode (domEmb hg) ((r - 2) * m + 1) ∧
      r * m ≤ (Finset.univ.filter (fun i => c i = w i)).card) with hLdef
  have hmaps : ∀ T (hT : T ∈ Fam), cw T hT ∈ L :=
    fun T hT => Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hcw_mem T hT, hcw_agree T hT⟩
  -- injectivity T ↦ q_T (the union-fibre degree contradiction)
  have hinj : ∀ T₁ (hT₁ : T₁ ∈ Fam) T₂ (hT₂ : T₂ ∈ Fam),
      cw T₁ hT₁ = cw T₂ hT₂ → T₁ = T₂ := by
    intro T₁ hT₁ T₂ hT₂ hcweq
    have hpoly : qpoly T₁ hT₁ = qpoly T₂ hT₂ := by
      have hsubz : qpoly T₁ hT₁ - qpoly T₂ hT₂ = 0 := by
        refine Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero
          (s := Finset.univ.image (domEmb hg)) ?_ ?_
        · rw [Finset.card_image_of_injective _ (domEmb hg).injective,
            Finset.card_univ, Fintype.card_fin]
          refine lt_of_le_of_lt (Polynomial.degree_sub_le _ _) ?_
          rw [max_lt_iff]
          refine ⟨lt_of_le_of_lt Polynomial.degree_le_natDegree ?_,
                  lt_of_le_of_lt Polynomial.degree_le_natDegree ?_⟩ <;>
            exact_mod_cast lt_of_le_of_lt (hqdeg _ _) hrmn
        · intro x hx
          obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
          have hi := congrFun hcweq i
          simp only [hcwdef] at hi
          rw [Polynomial.eval_sub, sub_eq_zero]
          exact hi
      exact sub_eq_zero.mp hsubz
    by_contra hTne
    have hSunsub : T₁ ∪ T₂ ⊆ (range (2 ^ μ)).image (fun j => (g ^ m) ^ j) :=
      Finset.union_subset (hFamG T₁ hT₁) (hFamG T₂ hT₂)
    have hSuncard : r + 1 ≤ (T₁ ∪ T₂).card := by
      have hsub2 : ¬ T₂ ⊆ T₁ := fun hsub => hTne (Finset.eq_of_subset_of_card_le hsub
        (by rw [hFamcard T₁ hT₁, hFamcard T₂ hT₂])).symm
      obtain ⟨b, hbB, hbA⟩ := Finset.not_subset.mp hsub2
      have hss : T₁ ⊂ T₁ ∪ T₂ := (Finset.ssubset_iff_of_subset Finset.subset_union_left).mpr
        ⟨b, Finset.mem_union_right _ hbB, hbA⟩
      have := Finset.card_lt_card hss
      rw [hFamcard T₁ hT₁] at this; omega
    set U := (Finset.univ.filter
      (fun i : Fin (2 ^ μ * m) => (g ^ (i : ℕ)) ^ m ∈ T₁ ∪ T₂)).image (domEmb hg) with hUdef
    have hUcard : U.card = m * (T₁ ∪ T₂).card := by
      rw [hUdef, Finset.card_image_of_injective _ (domEmb hg).injective]
      exact index_fiber_count (s := 2 ^ μ) (m := m) hm hs1 hg _ hSunsub
    set W : (ZMod p)[X] := X ^ (r * m) - Polynomial.C σ * X ^ ((r - 1) * m) with hWpdef
    have hWcoeff : W.coeff (r * m) = 1 := by
      have hne : (r * m) ≠ (r - 1) * m := by
        have : (r - 1) * m < r * m :=
          Nat.mul_lt_mul_of_pos_right (by omega : r - 1 < r) (by omega : 0 < m)
        omega
      rw [hWpdef, Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_pos rfl,
        Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hne, mul_zero, sub_zero]
    have hWne : W - qpoly T₁ hT₁ ≠ 0 := by
      intro h0
      have hc : (W - qpoly T₁ hT₁).coeff (r * m) = 0 := by rw [h0]; simp
      rw [Polynomial.coeff_sub, hWcoeff,
        Polynomial.coeff_eq_zero_of_natDegree_lt
          (lt_of_le_of_lt (hqdeg T₁ hT₁) hrm1)] at hc
      simp at hc
    have hdeg : (W - qpoly T₁ hT₁).degree ≤ (r * m : ℕ) := by
      refine le_trans (Polynomial.degree_sub_le _ _) ?_
      rw [max_le_iff]
      refine ⟨?_, le_trans Polynomial.degree_le_natDegree
        (by exact_mod_cast le_trans (hqdeg T₁ hT₁) (le_of_lt hrm1))⟩
      rw [hWpdef]
      refine le_trans (Polynomial.degree_sub_le _ _) ?_
      rw [max_le_iff]
      refine ⟨le_of_eq (Polynomial.degree_X_pow _), ?_⟩
      refine le_trans (Polynomial.degree_C_mul_X_pow_le _ _) ?_
      exact_mod_cast Nat.mul_le_mul_right m (by omega : r - 1 ≤ r)
    have hUgt : r * m < U.card := by
      rw [hUcard]
      have h1 : m * (r + 1) ≤ m * (T₁ ∪ T₂).card := Nat.mul_le_mul_left m hSuncard
      have h2 : m * (r + 1) = r * m + m := by ring
      omega
    have hvanish : ∀ x ∈ U, (W - qpoly T₁ hT₁).eval x = 0 := by
      intro x hx
      rw [hUdef] at hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      have hmem := (Finset.mem_filter.mp hi).2
      show (W - qpoly T₁ hT₁).eval (g ^ (i : ℕ)) = 0
      rw [Polynomial.eval_sub, sub_eq_zero, hWpdef, Polynomial.eval_sub,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X]
      rw [Finset.mem_union] at hmem
      rcases hmem with h | h
      · exact hqagree T₁ hT₁ (g ^ (i : ℕ)) h
      · rw [hpoly]; exact hqagree T₂ hT₂ (g ^ (i : ℕ)) h
    exact hWne (Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero (s := U)
      (lt_of_le_of_lt hdeg (by exact_mod_cast hUgt)) hvanish)
  -- assemble
  refine Finset.card_le_card_of_injOn (fun T => if hT : T ∈ Fam then cw T hT else w) ?_ ?_
  · intro T hT
    rw [Finset.mem_coe] at hT
    simp only [dif_pos hT]
    exact Finset.mem_coe.mpr (hmaps T hT)
  · intro T₁ hT₁ T₂ hT₂ heq
    rw [Finset.mem_coe] at hT₁ hT₂
    simp only [dif_pos hT₁, dif_pos hT₂] at heq
    exact hinj T₁ hT₁ T₂ hT₂ heq

/-! ## The closed-form lower bounds (even and odd `r`), via the generic lemma -/

open Classical in
/-- **EXACT list lower bound, EVEN `r`** (re-derived from the generic lemma via the
antipodal family, `σ = 0`): the monomial word `x^{rm}` has list `≥ C(2^{μ−1}, r/2)`. -/
theorem monomial_list_card_ge_even {μ m r : ℕ} (hμ : 1 ≤ μ) (hm : 1 ≤ m) (hr2 : 2 ≤ r)
    (hreven : r % 2 = 0) (hr : r ≤ 2 ^ (μ - 1)) {g : ZMod p} (hg : orderOf g = 2 ^ μ * m) :
    (2 ^ (μ - 1)).choose (r / 2) ≤
      (Finset.univ.filter (fun c : Fin (2 ^ μ * m) → ZMod p =>
        c ∈ rsCode (domEmb hg) ((r - 2) * m + 1) ∧ r * m ≤ (Finset.univ.filter
          (fun i => c i = (g ^ (i : ℕ)) ^ (r * m)
            - (0 : ZMod p) * (g ^ (i : ℕ)) ^ ((r - 1) * m))).card)).card := by
  have hs2 : (2 : ℕ) ^ μ = 2 * 2 ^ (μ - 1) := by rw [← pow_succ']; congr 1; omega
  have hω : orderOf (g ^ m) = 2 ^ μ := omega_orderOf hm hg
  have hωhalf : (g ^ m) ^ (2 ^ (μ - 1)) = -1 := omega_pow_half hμ hm hg
  set Fam := ((range (2 ^ (μ - 1))).powersetCard (r / 2)).image (antiSet (g ^ m)) with hFam
  have hFamcard : Fam.card = (2 ^ (μ - 1)).choose (r / 2) := by
    rw [hFam, Finset.card_image_of_injOn, Finset.card_powersetCard, Finset.card_range]
    intro D₁ hD₁ D₂ hD₂ heq
    exact antiSet_injOn hs2 hω hωhalf
      (Finset.mem_coe.mpr (Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hD₁).1))
      (Finset.mem_coe.mpr (Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hD₂).1)) heq
  rw [← hFamcard]
  refine equalSum_family_list_card_ge hμ hm hr2 hr hg 0 Fam ?_ ?_ ?_
  · intro T hT
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hT
    exact antiSet_subset_G hs2 hωhalf (Finset.mem_powersetCard.mp hD).1
  · intro T hT
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨hDsub, hDcard⟩ := Finset.mem_powersetCard.mp hD
    rw [antiSet_card hs2 hω hωhalf hDsub, hDcard]; omega
  · intro T hT
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hT
    exact antiSet_sum hs2 hω hωhalf (Finset.mem_powersetCard.mp hD).1

open Classical in
/-- **EXACT list lower bound, ODD `r`** (the generic lemma via the singleton-plus-pairs
family, `σ = 1`): the word `x^{rm} − x^{(r−1)m}` has list `≥ C(2^{μ−1}−1, (r−1)/2)`. -/
theorem monomial_list_card_ge_odd {μ m r : ℕ} (hμ : 1 ≤ μ) (hm : 1 ≤ m) (hr2 : 2 ≤ r)
    (hrodd : r % 2 = 1) (hr : r ≤ 2 ^ (μ - 1)) {g : ZMod p} (hg : orderOf g = 2 ^ μ * m) :
    (2 ^ (μ - 1) - 1).choose (r / 2) ≤
      (Finset.univ.filter (fun c : Fin (2 ^ μ * m) → ZMod p =>
        c ∈ rsCode (domEmb hg) ((r - 2) * m + 1) ∧ r * m ≤ (Finset.univ.filter
          (fun i => c i = (g ^ (i : ℕ)) ^ (r * m)
            - (1 : ZMod p) * (g ^ (i : ℕ)) ^ ((r - 1) * m))).card)).card := by
  have hhalf1 : (1 : ℕ) ≤ 2 ^ (μ - 1) := Nat.one_le_two_pow
  have hs2 : (2 : ℕ) ^ μ = 2 * 2 ^ (μ - 1) := by rw [← pow_succ']; congr 1; omega
  have hω : orderOf (g ^ m) = 2 ^ μ := omega_orderOf hm hg
  have hωhalf : (g ^ m) ^ (2 ^ (μ - 1)) = -1 := omega_pow_half hμ hm hg
  set E := (range (2 ^ (μ - 1))).erase 0 with hE
  have hEcard : E.card = 2 ^ (μ - 1) - 1 := by
    rw [hE, Finset.card_erase_of_mem (mem_range.mpr (by omega)), Finset.card_range]
  set Fam := (E.powersetCard (r / 2)).image (antiSetOdd (g ^ m)) with hFam
  have hFamcard : Fam.card = (2 ^ (μ - 1) - 1).choose (r / 2) := by
    rw [hFam, Finset.card_image_of_injOn, Finset.card_powersetCard, hEcard]
    intro D₁ hD₁ D₂ hD₂ heq
    exact antiSetOdd_injOn hs2 hhalf1 hω hωhalf
      (Finset.mem_coe.mpr (Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hD₁).1))
      (Finset.mem_coe.mpr (Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hD₂).1)) heq
  rw [← hFamcard]
  refine equalSum_family_list_card_ge hμ hm hr2 hr hg 1 Fam ?_ ?_ ?_
  · intro T hT
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hT
    have hDsub : D ⊆ range (2 ^ (μ - 1)) := fun x hx =>
      Finset.mem_of_mem_erase ((Finset.mem_powersetCard.mp hD).1 hx)
    exact antiSetOdd_subset_G hs2 hhalf1 hω hωhalf hDsub
  · intro T hT
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨hDsub, hDcard⟩ := Finset.mem_powersetCard.mp hD
    have hDsub' : D ⊆ range (2 ^ (μ - 1)) := fun x hx => Finset.mem_of_mem_erase (hDsub hx)
    have hD0 : 0 ∉ D := fun hc => (Finset.mem_erase.mp (hDsub hc)).1 rfl
    rw [antiSetOdd_card hs2 hhalf1 hω hωhalf hDsub' hD0, hDcard]; omega
  · intro T hT
    obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨hDsub, -⟩ := Finset.mem_powersetCard.mp hD
    have hDsub' : D ⊆ range (2 ^ (μ - 1)) := fun x hx => Finset.mem_of_mem_erase (hDsub hx)
    have hD0 : 0 ∉ D := fun hc => (Finset.mem_erase.mp (hDsub hc)).1 rfl
    exact antiSetOdd_sum hs2 hhalf1 hω hωhalf hDsub' hD0

/-! ## The matching UPPER bound at `r = 2` (the constant-code slice): pigeonhole

For `r = 2` the code has degree `≤ 0` (constants), and the list upper bound is a clean
pigeonhole — the agreement sets of distinct constants are disjoint value-fibres.  This is
the one slice of the otherwise-open upper-bound wall that falls unconditionally, and it
makes the list size EXACT (`= 2^{μ−1} = N_fib(2^μ, 2)`).  For `r ≥ 3` the upper bound is
the recognized Szemerédi–Trotter / additive-energy wall. -/

open Classical in
/-- **Pigeonhole upper bound for constant codewords.**  For any word `w` and threshold
`a`, the constant codewords (`rsCode dom 1`) agreeing with `w` on `≥ a` points number at
most `n / a`: their agreement sets are pairwise-disjoint value-fibres inside `[n]`. -/
theorem const_list_card_mul_le {n : ℕ} [NeZero n] (dom : Fin n ↪ ZMod p)
    (w : Fin n → ZMod p) (a : ℕ) :
    (Finset.univ.filter (fun c : Fin n → ZMod p => c ∈ rsCode dom 1 ∧
      a ≤ (Finset.univ.filter (fun i => c i = w i)).card)).card * a ≤ n := by
  classical
  set L := Finset.univ.filter (fun c : Fin n → ZMod p => c ∈ rsCode dom 1 ∧
    a ≤ (Finset.univ.filter (fun i => c i = w i)).card) with hLdef
  set ag : (Fin n → ZMod p) → Finset (Fin n) :=
    fun c => Finset.univ.filter (fun i => c i = w i) with hagdef
  -- constants agree at a point only on their unique value, so agreement sets are disjoint
  have hconst : ∀ c ∈ L, ∀ i j, c i = c j := by
    intro c hc i j
    obtain ⟨-, ⟨P, hP, rfl⟩, -⟩ := Finset.mem_filter.mp hc
    rcases eq_or_ne P 0 with rfl | hP0
    · simp
    · have hnd : P.natDegree = 0 := by
        have h1 : (P.natDegree : WithBot ℕ) < 1 := by
          rwa [← Polynomial.degree_eq_natDegree hP0]
        exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast h1)
      obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.mp hnd
      rw [← ha]; simp
  have hdisj : ∀ c ∈ L, ∀ c' ∈ L, c ≠ c' → Disjoint (ag c) (ag c') := by
    intro c hc c' hc' hne
    rw [Finset.disjoint_left]
    intro i hi hi'
    rw [hagdef, Finset.mem_filter] at hi hi'
    refine hne (funext fun j => ?_)
    rw [hconst c hc j i, hconst c' hc' j i, hi.2, hi'.2]
  -- the disjoint agreement sets fit in [n]
  have hbiUnion : (L.biUnion ag).card = ∑ c ∈ L, (ag c).card := Finset.card_biUnion hdisj
  have hle_n : (L.biUnion ag).card ≤ n := by
    calc (L.biUnion ag).card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card
          (Finset.biUnion_subset.mpr fun c _ => Finset.filter_subset _ _)
      _ = n := by rw [Finset.card_univ, Fintype.card_fin]
  -- each agreement set has ≥ a points
  have hge : ∀ c ∈ L, a ≤ (ag c).card := fun c hc => (Finset.mem_filter.mp hc).2.2
  calc L.card * a = ∑ _c ∈ L, a := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ c ∈ L, (ag c).card := Finset.sum_le_sum hge
    _ = (L.biUnion ag).card := hbiUnion.symm
    _ ≤ n := hle_n

open Classical in
/-- **EXACT list size at `r = 2`** — the first slice of the upper-bound wall to fall.
On the smooth domain of order `2^μ·m`, the agreement-`2m` list of constant codewords for
the word `x^{2m}` has size EXACTLY `2^{μ−1} = N_fib(2^μ, 2)`: the lower bound from the
antipodal family (`monomial_list_card_ge_even`) meets the pigeonhole upper bound. -/
theorem monomial_list_card_eq_two {μ m : ℕ} (hμ : 2 ≤ μ) (hm : 1 ≤ m)
    {g : ZMod p} (hg : orderOf g = 2 ^ μ * m) :
    haveI : NeZero (2 ^ μ * m) := ⟨by positivity⟩
    (Finset.univ.filter (fun c : Fin (2 ^ μ * m) → ZMod p =>
      c ∈ rsCode (domEmb hg) ((2 - 2) * m + 1) ∧ 2 * m ≤ (Finset.univ.filter
        (fun i => c i = (g ^ (i : ℕ)) ^ (2 * m)
          - (0 : ZMod p) * (g ^ (i : ℕ)) ^ ((2 - 1) * m))).card)).card = 2 ^ (μ - 1) := by
  haveI : NeZero (2 ^ μ * m) := ⟨by positivity⟩
  have hr2pow : (2 : ℕ) ≤ 2 ^ (μ - 1) := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (μ - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpow : (2 : ℕ) ^ μ * m = 2 ^ (μ - 1) * (2 * m) := by
    have h2 : (2 : ℕ) ^ μ = 2 * 2 ^ (μ - 1) := by rw [← pow_succ']; congr 1; omega
    rw [h2]; ring
  refine le_antisymm ?_ ?_
  · -- upper bound: pigeonhole gives list·2m ≤ 2^μ·m = 2^{μ−1}·2m, so list ≤ 2^{μ−1}
    have hub := const_list_card_mul_le (domEmb hg)
      (fun i => (g ^ (i : ℕ)) ^ (2 * m) - (0 : ZMod p) * (g ^ (i : ℕ)) ^ ((2 - 1) * m))
      (2 * m)
    rw [show (2 - 2) * m + 1 = 1 from by omega]
    refine Nat.le_of_mul_le_mul_right ?_ (show 0 < 2 * m by omega)
    rw [← hpow]; exact hub
  · -- lower bound: the even achievability at r = 2 gives ≥ C(2^{μ−1}, 1) = 2^{μ−1}
    have hlb := monomial_list_card_ge_even (p := p) (μ := μ) (m := m) (r := 2)
      (by omega) hm (by norm_num) (by norm_num) hr2pow hg
    rwa [show (2 : ℕ) / 2 = 1 from by norm_num, Nat.choose_one_right] at hlb

end ArkLib.ProximityGap.KKH26

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.KKH26.monomial_list_card_ge
#print axioms ArkLib.ProximityGap.KKH26.equalSum_family_list_card_ge
#print axioms ArkLib.ProximityGap.KKH26.monomial_list_card_ge_odd
#print axioms ArkLib.ProximityGap.KKH26.const_list_card_mul_le
#print axioms ArkLib.ProximityGap.KKH26.monomial_list_card_eq_two
