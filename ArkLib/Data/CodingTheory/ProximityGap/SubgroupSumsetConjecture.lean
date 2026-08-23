/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-!
# The BCHKS25 subgroup-sumset conjecture (Conj 1.12) and its Mersenne witness (Remark 7.3)

The δ\* literature sweep ([`docs/kb/deltastar-literature-findings-2026-06-13.md`]) pinned the
exact gating of the proximity-prize **upper bracket** `1 − ρ − Θ(1/log n)`: it is constructed by
**BCHKS25 (ePrint 2025/2055) Theorem 1.13** *conditional on* the open

> **Conjecture 1.12 (subgroup-sumset).** For infinitely many primes `q` there is `b ≤ 10·log q`
> and a multiplicative subgroup `G ⊆ F_q^×` of order `b` whose distinct-element `⌊b/2⌋`-fold
> sumset `G^{(+⌊b/2⌋)} = {e₁+…+e_{⌊b/2⌋} : eᵢ∈G distinct}` has size `≥ q/10`.

This is *weaker than the infinitude of Mersenne primes* and *stronger than* the best
unconditional Glibichuk–Konyagin bound — i.e. the prize upper bracket is gated on a genuinely
open additive-number-theory conjecture, the formal twin of the #389 "ℓ-fold subset-sumset
poly-vs-superpoly" framing. This file mirrors the conjecture in-tree (as the sweep recommended)
and proves the one realizable witness, **Remark 7.3**:

> **`mersenne_admissible`** — for `q = 2^p − 1` (`p ≥ 3`), the subgroup `G = ⟨−2⟩ = {±2^i : i<p}`
> has `|G| = 2p`, and its distinct-element `p`-fold sumset is **all of `ZMod q`**
> (`sumsetDistinct_signedPowers_eq_univ`), so `(q, q, 2p)` is admissible.

The mathematical heart (`mem_sumsetDistinct_signedPowers`) is the signed binary expansion: every
`u` is `∑_{i<p} (2·b_i − 1)·2^i` where `b_i` are the bits of `u/2` — the `⟨−2⟩` covering, holding
over `ZMod (2^p − 1)` for any `p ≥ 3` (no primality needed for the covering itself).

**The conjecture (`SubgroupSumsetConjecture`) stays an explicit named `Prop`; it is NOT proved**
(per the honesty contract — it is the open core gating the prize upper bracket). All proofs here
are axiom-clean (`propext, Classical.choice, Quot.sound`). Issue #389.
-/

open Finset

namespace ArkLib.ProximityGap.SubgroupSumset

/-- Def 1.10: the distinct-element `ℓ`-fold sumset of `E`. -/
def sumsetDistinct {F : Type*} [AddCommMonoid F] [DecidableEq F]
    (E : Finset F) (ℓ : ℕ) : Finset F :=
  (E.powersetCard ℓ).image (fun S => ∑ x ∈ S, x)

theorem mem_sumsetDistinct {F : Type*} [AddCommMonoid F] [DecidableEq F]
    {E : Finset F} {ℓ : ℕ} {u : F} :
    u ∈ sumsetDistinct E ℓ ↔ ∃ S : Finset F, S ⊆ E ∧ S.card = ℓ ∧ ∑ x ∈ S, x = u := by
  unfold sumsetDistinct
  simp only [Finset.mem_image, Finset.mem_powersetCard]
  constructor
  · rintro ⟨S, ⟨hSE, hScard⟩, hsum⟩; exact ⟨S, hSE, hScard, hsum⟩
  · rintro ⟨S, hSE, hScard, hsum⟩; exact ⟨S, ⟨hSE, hScard⟩, hsum⟩

/-- Every `k < 2^P` is the sum of `2^i` over a subset of `range P` (binary expansion). -/
theorem exists_subset_sum_eq (P : ℕ) :
    ∀ k, k < 2 ^ P → ∃ T : Finset ℕ, T ⊆ Finset.range P ∧ ∑ i ∈ T, 2 ^ i = k := by
  induction P with
  | zero =>
    intro k hk
    simp only [pow_zero, Nat.lt_one_iff] at hk
    exact ⟨∅, by simp, by simp [hk]⟩
  | succ P ih =>
    intro k hk
    by_cases hkp : k < 2 ^ P
    · obtain ⟨T, hT, hsum⟩ := ih k hkp
      refine ⟨T, ?_, hsum⟩
      intro x hx
      exact Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp (hT hx)))
    · push_neg at hkp
      have h2 : 2 ^ (P + 1) = 2 ^ P * 2 := pow_succ 2 P
      have hk' : k - 2 ^ P < 2 ^ P := by omega
      obtain ⟨T, hT, hsum⟩ := ih (k - 2 ^ P) hk'
      have hPnT : P ∉ T := fun h => by
        have := hT h; simp only [Finset.mem_range] at this; omega
      refine ⟨insert P T, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · simp [Finset.mem_range]
        · exact Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp (hT hx)))
      · rw [Finset.sum_insert hPnT, hsum]; omega

variable {p : ℕ}

/-- The signed powers `{±2^i : i < p}` as a subset of `ZMod (2^p - 1)`. -/
def signedPowers (p : ℕ) : Finset (ZMod (2 ^ p - 1)) :=
  (Finset.range p).image (fun i => (2 : ZMod (2 ^ p - 1)) ^ i) ∪
  (Finset.range p).image (fun i => -(2 : ZMod (2 ^ p - 1)) ^ i)

section
variable (hp : 3 ≤ p)

include hp

theorem N_pos : 0 < 2 ^ p - 1 := by
  have h : 2 ^ 1 ≤ 2 ^ p := by gcongr <;> omega
  simp only [pow_one] at h
  omega

instance instNeZeroN : NeZero (2 ^ p - 1) := ⟨by have := N_pos hp; omega⟩

/-- `2^i < N` for `i < p`. -/
theorem two_pow_lt {i : ℕ} (hi : i < p) : 2 ^ i < 2 ^ p - 1 := by
  have h1 : 2 ^ i ≤ 2 ^ (p - 1) := by gcongr <;> omega
  have hp2 : 2 ^ p = 2 ^ (p - 1) * 2 := by rw [← pow_succ]; congr 1; omega
  have hpos : 2 ^ 1 ≤ 2 ^ (p - 1) := by gcongr <;> omega
  simp only [pow_one] at hpos
  omega

/-- `(2 : R)^p = 1`. -/
theorem two_pow_p_eq_one : (2 : ZMod (2 ^ p - 1)) ^ p = 1 := by
  have hN : ((2 ^ p - 1 : ℕ) : ZMod (2 ^ p - 1)) = 0 := ZMod.natCast_self _
  have hle : (1 : ℕ) ≤ 2 ^ p := Nat.one_le_two_pow
  have hsub : ((2 ^ p - 1 : ℕ) : ZMod (2 ^ p - 1)) = (2 : ZMod (2 ^ p - 1)) ^ p - 1 := by
    push_cast [Nat.cast_sub hle]; ring
  rw [hN] at hsub
  exact eq_of_sub_eq_zero hsub.symm

/-- The full geometric sum vanishes: `∑_{i<p} 2^i = 0` in `R`. -/
theorem geom_sum_vanish : ∑ i ∈ Finset.range p, (2 : ZMod (2 ^ p - 1)) ^ i = 0 := by
  have hmul := geom_sum_mul (2 : ZMod (2 ^ p - 1)) p
  have h21 : (2 : ZMod (2 ^ p - 1)) - 1 = 1 := by norm_num
  rw [h21, mul_one, two_pow_p_eq_one hp, sub_self] at hmul
  exact hmul

/-- Injectivity ingredient (H1): `2^i = 2^j` in `R` forces `i = j` for `i,j < p`. -/
theorem two_pow_inj {i j : ℕ} (hi : i < p) (hj : j < p)
    (h : (2 : ZMod (2 ^ p - 1)) ^ i = (2 : ZMod (2 ^ p - 1)) ^ j) : i = j := by
  have hci : (2 : ZMod (2 ^ p - 1)) ^ i = ((2 ^ i : ℕ) : ZMod (2 ^ p - 1)) := by push_cast; ring
  have hcj : (2 : ZMod (2 ^ p - 1)) ^ j = ((2 ^ j : ℕ) : ZMod (2 ^ p - 1)) := by push_cast; ring
  rw [hci, hcj, ZMod.natCast_eq_natCast_iff] at h
  have hi' : 2 ^ i < 2 ^ p - 1 := two_pow_lt hp hi
  have hj' : 2 ^ j < 2 ^ p - 1 := two_pow_lt hp hj
  have heq : 2 ^ i = 2 ^ j := by
    unfold Nat.ModEq at h
    rw [Nat.mod_eq_of_lt hi', Nat.mod_eq_of_lt hj'] at h
    exact h
  exact Nat.pow_right_injective (by norm_num) heq

/-- Injectivity ingredient (H2): for `i ≠ j < p`, `2^i + 2^j ≠ 0` in `R`. -/
theorem two_pow_add_ne_zero {i j : ℕ} (hi : i < p) (hj : j < p) (hij : i ≠ j) :
    (2 : ZMod (2 ^ p - 1)) ^ i + (2 : ZMod (2 ^ p - 1)) ^ j ≠ 0 := by
  have hc : (2 : ZMod (2 ^ p - 1)) ^ i + (2 : ZMod (2 ^ p - 1)) ^ j
      = ((2 ^ i + 2 ^ j : ℕ) : ZMod (2 ^ p - 1)) := by push_cast; ring
  rw [hc, Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  have hpos : 0 < 2 ^ i + 2 ^ j := by positivity
  have hbound : 2 ^ i + 2 ^ j < 2 ^ p - 1 := by
    rcases Nat.lt_or_ge i j with hlt | hge
    · have hi2 : 2 ^ i ≤ 2 ^ (p - 2) := by gcongr <;> omega
      have hj2 : 2 ^ j ≤ 2 ^ (p - 1) := by gcongr <;> omega
      have e1 : 2 ^ (p - 1) = 2 ^ (p - 2) * 2 := by rw [← pow_succ]; congr 1; omega
      have e2 : (2 : ℕ) ^ p = 2 ^ (p - 2) * 4 := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
      have hpp : 2 ^ 1 ≤ 2 ^ (p - 2) := by gcongr <;> omega
      simp only [pow_one] at hpp
      omega
    · have hji : j < i := lt_of_le_of_ne hge (fun h => hij h.symm)
      have hi2 : 2 ^ i ≤ 2 ^ (p - 1) := by gcongr <;> omega
      have hj2 : 2 ^ j ≤ 2 ^ (p - 2) := by gcongr <;> omega
      have e1 : 2 ^ (p - 1) = 2 ^ (p - 2) * 2 := by rw [← pow_succ]; congr 1; omega
      have e2 : (2 : ℕ) ^ p = 2 ^ (p - 2) * 4 := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
      have hpp : 2 ^ 1 ≤ 2 ^ (p - 2) := by gcongr <;> omega
      simp only [pow_one] at hpp
      omega
  exact absurd (Nat.le_of_dvd hpos hdvd) (by omega)

/-- **Remark 7.3 (core covering).** Over `R = ZMod (2^p − 1)` (`p ≥ 3`), every element is the
sum of exactly `p` *distinct* signed powers `±2^i` (`i < p`) — the `⟨−2⟩` covering. -/
theorem mem_sumsetDistinct_signedPowers (u : ZMod (2 ^ p - 1)) :
    u ∈ sumsetDistinct (signedPowers p) p := by
  classical
  haveI : NeZero (2 ^ p - 1) := ⟨by have := N_pos hp; omega⟩
  rw [mem_sumsetDistinct]
  set w : ZMod (2 ^ p - 1) := (2 : ZMod (2 ^ p - 1)) ^ (p - 1) * u with hw
  have hk : w.val < 2 ^ p := by
    have h1 := ZMod.val_lt w
    have hN := N_pos hp
    omega
  obtain ⟨T, hTsub, hTsum⟩ := exists_subset_sum_eq p w.val hk
  set e : ℕ → ZMod (2 ^ p - 1) :=
    fun i => if i ∈ T then (2 : ZMod (2 ^ p - 1)) ^ i else -(2 : ZMod (2 ^ p - 1)) ^ i with he
  -- e is injective on range p
  have einj : ∀ i ∈ Finset.range p, ∀ j ∈ Finset.range p, e i = e j → i = j := by
    intro i hi j hj hij
    simp only [Finset.mem_range] at hi hj
    by_contra hne
    simp only [he] at hij
    by_cases hiT : i ∈ T <;> by_cases hjT : j ∈ T <;>
      simp only [hiT, hjT, if_true, if_false] at hij
    · exact hne (two_pow_inj hp hi hj hij)
    · exact two_pow_add_ne_zero hp hi hj hne (by linear_combination hij)
    · exact two_pow_add_ne_zero hp hj hi (fun h => hne h.symm) (by linear_combination -hij)
    · exact hne (two_pow_inj hp hi hj (by linear_combination -hij))
  refine ⟨(Finset.range p).image e, ?_, ?_, ?_⟩
  · -- the witness set is contained in the signed powers
    intro x hx
    simp only [Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    simp only [he, signedPowers, Finset.mem_union, Finset.mem_image, Finset.mem_range]
    by_cases hiT : i ∈ T
    · exact Or.inl ⟨i, hi, by rw [if_pos hiT]⟩
    · exact Or.inr ⟨i, hi, by rw [if_neg hiT]⟩
  · -- exactly p distinct elements
    rw [Finset.card_image_of_injOn
        (fun a ha b hb => einj a (by simpa using ha) b (by simpa using hb)),
      Finset.card_range]
  · -- the sum is u
    rw [Finset.sum_image einj]
    have hrw : ∀ i, e i
        = 2 * (if i ∈ T then (2 : ZMod (2 ^ p - 1)) ^ i else 0) - (2 : ZMod (2 ^ p - 1)) ^ i := by
      intro i
      simp only [he]
      by_cases h : i ∈ T
      · rw [if_pos h, if_pos h]; ring
      · rw [if_neg h, if_neg h]; ring
    have hgsum : ∑ i ∈ Finset.range p, (if i ∈ T then (2 : ZMod (2 ^ p - 1)) ^ i else 0)
        = ∑ i ∈ T, (2 : ZMod (2 ^ p - 1)) ^ i := by
      rw [← Finset.sum_filter]
      congr 1
      rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hTsub]
    have hTval : ∑ i ∈ T, (2 : ZMod (2 ^ p - 1)) ^ i = w := by
      have hcast : ∑ i ∈ T, (2 : ZMod (2 ^ p - 1)) ^ i
          = ((∑ i ∈ T, 2 ^ i : ℕ) : ZMod (2 ^ p - 1)) := by push_cast; ring
      rw [hcast, hTsum, ZMod.natCast_zmod_val]
    have h2p : (2 : ZMod (2 ^ p - 1)) * (2 : ZMod (2 ^ p - 1)) ^ (p - 1)
        = (2 : ZMod (2 ^ p - 1)) ^ p := by
      rw [← pow_succ']; congr 1; omega
    rw [Finset.sum_congr rfl (fun i _ => hrw i), Finset.sum_sub_distrib, geom_sum_vanish hp,
      sub_zero, ← Finset.mul_sum, hgsum, hTval, hw, ← mul_assoc, h2p, two_pow_p_eq_one hp, one_mul]

/-- **Remark 7.3 (full covering).** The `p`-fold distinct sumset of the `2p` signed powers
`{±2^i}` is the *entire* ring `ZMod (2^p − 1)`. -/
theorem sumsetDistinct_signedPowers_eq_univ [NeZero (2 ^ p - 1)] :
    sumsetDistinct (signedPowers p) p = Finset.univ :=
  Finset.eq_univ_of_forall (mem_sumsetDistinct_signedPowers hp)

/-- `2^i ≠ 0` for `i < p`. -/
theorem two_pow_ne_zero {i : ℕ} (hi : i < p) : (2 : ZMod (2 ^ p - 1)) ^ i ≠ 0 := by
  have hc : (2 : ZMod (2 ^ p - 1)) ^ i = ((2 ^ i : ℕ) : ZMod (2 ^ p - 1)) := by push_cast; ring
  rw [hc, Ne, ZMod.natCast_eq_zero_iff]
  intro hd
  have hlt := two_pow_lt hp hi
  have hpos : 0 < 2 ^ i := by positivity
  exact absurd (Nat.le_of_dvd hpos hd) (by omega)

/-- Disjointness ingredient: `2^i + 2^j ≠ 0` for ALL `i,j < p` (extends `two_pow_add_ne_zero`
to the diagonal `i = j` via `N ∤ 2^{i+1}`). -/
theorem two_pow_add_ne_zero_all {i j : ℕ} (hi : i < p) (hj : j < p) :
    (2 : ZMod (2 ^ p - 1)) ^ i + (2 : ZMod (2 ^ p - 1)) ^ j ≠ 0 := by
  by_cases h : i = j
  · subst h
    have hc : (2 : ZMod (2 ^ p - 1)) ^ i + (2 : ZMod (2 ^ p - 1)) ^ i
        = ((2 ^ (i + 1) : ℕ) : ZMod (2 ^ p - 1)) := by push_cast; ring
    rw [hc, Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    -- `(2^p − 1) ∣ 2^{i+1}` ⟹ `2^p − 1` is a power of 2, impossible by size
    rw [Nat.dvd_prime_pow Nat.prime_two] at hd
    obtain ⟨k, _, hke⟩ := hd
    rcases Nat.lt_or_ge k p with hkp | hkp
    · have hb : 2 ^ k ≤ 2 ^ (p - 1) := by gcongr <;> omega
      have he : (2 : ℕ) ^ p = 2 * 2 ^ (p - 1) := by rw [← pow_succ']; congr 1; omega
      have h4 : (4 : ℕ) ≤ 2 ^ (p - 1) := by
        have : (2 : ℕ) ^ 2 ≤ 2 ^ (p - 1) := by gcongr <;> omega
        simpa using this
      omega
    · have hb : (2 : ℕ) ^ p ≤ 2 ^ k := by gcongr; omega
      have h1 : 1 ≤ (2 : ℕ) ^ p := Nat.one_le_two_pow
      omega
  · exact two_pow_add_ne_zero hp hi hj h

/-- `2^k = 2^{k mod p}` in `R` (the cyclic reduction, since `2^p = 1`). -/
theorem two_pow_mod (k : ℕ) :
    (2 : ZMod (2 ^ p - 1)) ^ k = (2 : ZMod (2 ^ p - 1)) ^ (k % p) := by
  conv_lhs => rw [← Nat.div_add_mod k p, pow_add, pow_mul, two_pow_p_eq_one hp, one_pow, one_mul]

/-- Membership characterization of `signedPowers`. -/
theorem mem_signedPowers_iff {x : ZMod (2 ^ p - 1)} :
    x ∈ signedPowers p ↔ ∃ i, i < p ∧ (x = (2 : ZMod (2 ^ p - 1)) ^ i
      ∨ x = -(2 : ZMod (2 ^ p - 1)) ^ i) := by
  simp only [signedPowers, Finset.mem_union, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact ⟨i, hi, Or.inl rfl⟩
    · exact ⟨i, hi, Or.inr rfl⟩
  · rintro ⟨i, hi, (rfl | rfl)⟩
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr ⟨i, hi, rfl⟩

/-- `signedPowers` has exactly `2p` elements. -/
theorem signedPowers_card : (signedPowers p).card = 2 * p := by
  have hAinj : Set.InjOn (fun i => (2 : ZMod (2 ^ p - 1)) ^ i) ↑(Finset.range p) := by
    intro a ha b hb hab
    exact two_pow_inj hp (by simpa using ha) (by simpa using hb) hab
  have hBinj : Set.InjOn (fun i => -(2 : ZMod (2 ^ p - 1)) ^ i) ↑(Finset.range p) := by
    intro a ha b hb hab
    exact two_pow_inj hp (by simpa using ha) (by simpa using hb) (by linear_combination -hab)
  have hdisj : Disjoint ((Finset.range p).image (fun i => (2 : ZMod (2 ^ p - 1)) ^ i))
      ((Finset.range p).image (fun i => -(2 : ZMod (2 ^ p - 1)) ^ i)) := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    simp only [Finset.mem_image, Finset.mem_range] at hxA hxB
    obtain ⟨i, hi, rfl⟩ := hxA
    obtain ⟨j, hj, hji⟩ := hxB
    exact two_pow_add_ne_zero_all hp hi hj (by linear_combination -hji)
  rw [signedPowers, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injOn hAinj, Finset.card_image_of_injOn hBinj, Finset.card_range]
  omega

end

/-- Def 1.11 (subgroup structure as a finite multiplicatively-closed nonzero set containing
`1` — a finite submonoid of `(ZMod q)ˣ`, hence a subgroup of `F_q^×` when `q` is prime). -/
structure IsMulSubgroupOf {q : ℕ} (G : Finset (ZMod q)) : Prop where
  one_mem : (1 : ZMod q) ∈ G
  zero_not_mem : (0 : ZMod q) ∉ G
  mul_mem : ∀ a ∈ G, ∀ b ∈ G, a * b ∈ G

/-- **Definition 1.11 (BCHKS25).** `(q, a, b)` is *admissible* if there is a multiplicative
subgroup `G ⊆ F_q^×` of cardinality `b` whose distinct-element `⌊b/2⌋`-fold sumset has size
`≥ a`. -/
def Admissible (q a b : ℕ) : Prop :=
  ∃ G : Finset (ZMod q), IsMulSubgroupOf G ∧ G.card = b ∧
    a ≤ (sumsetDistinct G (b / 2)).card

/-- **Conjecture 1.12 (BCHKS25), the open subgroup-sumset conjecture.** For infinitely many
primes `q` there is `b ≤ 10·log₂ q` with `(q, q/10, b)` admissible. (Rendering `log q` as the
integer `Nat.log 2 q`; the constant `10` is as in the paper.) This is the open core gating the
prize upper bracket `1 − ρ − Θ(1/log n)` (Theorem 1.13); it is *weaker* than the infinitude of
Mersenne primes (Remark 7.3) and *stronger* than the best unconditional Glibichuk–Konyagin
bound. **Stated as a named `Prop`; NOT proved.** -/
def SubgroupSumsetConjecture : Prop :=
  ∀ M : ℕ, ∃ q : ℕ, M < q ∧ q.Prime ∧
    ∃ b : ℕ, b ≤ 10 * Nat.log 2 q ∧ Admissible q (q / 10) b

/-- **Remark 7.3 (BCHKS25), formalized.** For `q = 2^p − 1` (`p ≥ 3`), the subgroup
`G = ⟨−2⟩ = {±2^i : i < p}` has cardinality `2p` and its distinct-element `p`-fold sumset is
*all* of `ZMod q`; hence `(q, q, 2p)` is admissible. When `q` is a Mersenne prime this is the
explicit witness of the (otherwise open) subgroup-sumset phenomenon of Conjecture 1.12. -/
theorem mersenne_admissible {p : ℕ} (hp : 3 ≤ p) :
    Admissible (2 ^ p - 1) (2 ^ p - 1) (2 * p) := by
  haveI : NeZero (2 ^ p - 1) := ⟨by have := N_pos hp; omega⟩
  refine ⟨signedPowers p, ⟨?_, ?_, ?_⟩, signedPowers_card hp, ?_⟩
  · -- 1 ∈ G
    rw [mem_signedPowers_iff hp]
    exact ⟨0, by omega, Or.inl (by rw [pow_zero])⟩
  · -- 0 ∉ G
    rw [mem_signedPowers_iff hp]
    rintro ⟨i, hi, (h | h)⟩
    · exact two_pow_ne_zero hp hi h.symm
    · exact two_pow_ne_zero hp hi (neg_eq_zero.mp h.symm)
  · -- mul-closed
    intro x hx y hy
    rw [mem_signedPowers_iff hp] at hx hy ⊢
    obtain ⟨i, hi, hxi⟩ := hx
    obtain ⟨j, hj, hyj⟩ := hy
    have hmod : (2 : ZMod (2 ^ p - 1)) ^ (i + j) = (2 : ZMod (2 ^ p - 1)) ^ ((i + j) % p) :=
      two_pow_mod hp (i + j)
    refine ⟨(i + j) % p, Nat.mod_lt _ (by omega), ?_⟩
    rcases hxi with rfl | rfl <;> rcases hyj with rfl | rfl
    · exact Or.inl (by rw [← pow_add]; exact hmod)
    · exact Or.inr (by rw [mul_neg, ← pow_add, hmod])
    · exact Or.inr (by rw [neg_mul, ← pow_add, hmod])
    · exact Or.inl (by rw [neg_mul_neg, ← pow_add]; exact hmod)
  · -- the p-fold sumset is everything: card = q
    have hhalf : 2 * p / 2 = p := by omega
    rw [hhalf, sumsetDistinct_signedPowers_eq_univ hp, Finset.card_univ, ZMod.card]

end ArkLib.ProximityGap.SubgroupSumset

-- Axiom audit (expected: [propext, Classical.choice, Quot.sound] only)
#print axioms ArkLib.ProximityGap.SubgroupSumset.mem_sumsetDistinct_signedPowers
#print axioms ArkLib.ProximityGap.SubgroupSumset.sumsetDistinct_signedPowers_eq_univ
#print axioms ArkLib.ProximityGap.SubgroupSumset.mersenne_admissible
