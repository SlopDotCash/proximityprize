/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupSumsetConjecture
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupSumsetFactorWitness

/-!
# Base-free admissibility for `⟨−g⟩` subgroups (#389)

The in-tree subgroup-sumset witnesses (`mersenne_admissible`,
`mem_sumsetDistinct_signedPowers_factor`) are base-`2`-specific (binary expansion).  This file
proves the GENERAL covering lemma for a multiplicative subgroup `G = ⟨−g⟩ = {± g^i : i < p}` over
`ZMod q`, reducing its `p`-fold distinct signed-power sumset to `2·(`the `{0,1}`-subset-sum image
of `{g^i : i < p}`)`.

The reduction is isolated by a single structure `SignedWitnessHyp g p` capturing the only two
number-theoretic facts used: `g` has multiplicative order exactly `p`, and the `2p` signed powers
`±g^i` are pairwise distinct.  Given these (plus `2 ≠ 0`), the abstract criterion
`admissible_of_signedWitness` shows `(q, a, 2p)` is admissible whenever the `{0,1}`-subset-sum
image of `{g^i}` has size `≥ a`.  The **only** remaining open input is the number-theoretic
quantity `(subsetSumImage g p).card` — the genuinely open core of Conjecture 1.12 — which is the
EXPLICIT hypothesis, not re-proven here.

`admissible_two_factor` recovers the base-`2` Mersenne consequence (`subsetSumImage = univ`,
card `q`) purely from the base-free criterion, confirming it is at least as strong as the in-tree
witnesses.
-/

open Finset

namespace ArkLib.ProximityGap.SubgroupSumset.Widen

variable {q : ℕ}

/-- The signed powers `{± g^i : i < p}` of a base `g` in `ZMod q`. -/
def signedPowersG (g : ZMod q) (p : ℕ) : Finset (ZMod q) :=
  (Finset.range p).image (fun i => g ^ i) ∪
  (Finset.range p).image (fun i => -(g ^ i))

/-- The `{0,1}`-subset-sum image of `{g^i : i < p}` in `ZMod q`:
the set of all `∑_{i∈T} g^i` over `T ⊆ range p`. -/
def subsetSumImage (g : ZMod q) (p : ℕ) : Finset (ZMod q) :=
  (Finset.range p).powerset.image (fun T => ∑ i ∈ T, g ^ i)

/-- Every `k < 2^P` is a subset-sum of `{2^i}` is base-2-specific; for general `g` the
subset-sum image is just whatever it is. We characterize membership. -/
theorem mem_subsetSumImage {g : ZMod q} {p : ℕ} {v : ZMod q} :
    v ∈ subsetSumImage g p ↔ ∃ T ⊆ Finset.range p, ∑ i ∈ T, g ^ i = v := by
  unfold subsetSumImage
  simp only [Finset.mem_image, Finset.mem_powerset]

/-- The hypotheses isolating the number-theoretic core of a `⟨−g⟩`-witness:
* `hord` — `g` has multiplicative order exactly `p` (so the `g^i` (`i<p`) are distinct and
  `g^p = 1`, hence `∑_{i<p} g^i = 0`); and
* `hsigned` — the `2p` signed powers `±g^i` (`i<p`) are pairwise distinct,
  i.e. `g^i + g^j ≠ 0` for all `i, j < p`.
These two facts (and ONLY these) are what the in-tree base-`2` witness proves number-theoretically
(`orderOf_two_eq`, `two_pow_add_ne_zero_q'`); abstracting them makes the admissibility
reduction base-free. -/
structure SignedWitnessHyp (g : ZMod q) (p : ℕ) : Prop where
  hord : orderOf g = p
  hsigned : ∀ i < p, ∀ j < p, g ^ i + g ^ j ≠ (0 : ZMod q)

section
variable [Fact q.Prime] {g : ZMod q} {p : ℕ}

/-- `g^p = 1` from `orderOf g = p`. -/
theorem g_pow_p (H : SignedWitnessHyp g p) : g ^ p = 1 := by
  rw [← H.hord]; exact pow_orderOf_eq_one g

/-- `g ≠ 0` (else `g^p = 0 ≠ 1`, contradicting `g^p = 1` for `p ≥ 1`). -/
theorem g_ne_zero (H : SignedWitnessHyp g p) (hp : 1 ≤ p) : g ≠ 0 := by
  intro h
  have hgp := g_pow_p H
  rw [h, zero_pow (by omega)] at hgp
  exact zero_ne_one hgp

/-- The geometric sum vanishes: `∑_{i<p} g^i = 0` (since `g^p = 1` and `g ≠ 1`). -/
theorem geom_sum_vanishG (H : SignedWitnessHyp g p) (hp : 2 ≤ p) :
    ∑ i ∈ Finset.range p, g ^ i = 0 := by
  have hg1 : g ≠ 1 := by
    intro h
    have : orderOf g = 1 := by rw [h]; exact orderOf_one
    rw [H.hord] at this; omega
  -- (g - 1) * ∑ = g^p - 1 = 0, and g - 1 ≠ 0 a unit-free argument via geom_sum_mul
  have hmul := geom_sum_mul g p
  rw [g_pow_p H, sub_self] at hmul
  have hg1' : g - 1 ≠ 0 := sub_ne_zero.mpr hg1
  -- ∑ * (g-1) = 0 ⟹ ∑ = 0 (ZMod q for q prime is a domain)
  rcases mul_eq_zero.mp hmul with h | h
  · exact h
  · exact absurd h hg1'

/-- `g^i ≠ 0` for `i < p` (signed powers nonzero). -/
theorem g_pow_ne_zero (H : SignedWitnessHyp g p) {i : ℕ} (hi : i < p) :
    g ^ i ≠ (0 : ZMod q) := by
  intro h
  exact H.hsigned i hi i hi (by rw [h]; ring)

/-- `g^i = g^j` forces `i = j` for `i, j < p` (from `orderOf g = p`). -/
theorem g_pow_inj (H : SignedWitnessHyp g p) {i j : ℕ} (hi : i < p) (hj : j < p)
    (h : g ^ i = g ^ j) : i = j :=
  pow_injOn_Iio_orderOf (by rw [H.hord]; exact Set.mem_Iio.mpr hi)
    (by rw [H.hord]; exact Set.mem_Iio.mpr hj) h

/-- The "one sign per position" assignment for a subset `T ⊆ range p`:
`e_T i = g^i` if `i ∈ T`, else `−g^i`. -/
def signFun (g : ZMod q) (T : Finset ℕ) (i : ℕ) : ZMod q :=
  if i ∈ T then g ^ i else -(g ^ i)

/-- `signFun` is injective on `range p` (signed powers are pairwise distinct). -/
theorem signFun_injOn (H : SignedWitnessHyp g p) (T : Finset ℕ) :
    Set.InjOn (signFun g T) ↑(Finset.range p) := by
  intro i hi j hj hij
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  by_contra hne
  simp only [signFun] at hij
  by_cases hiT : i ∈ T <;> by_cases hjT : j ∈ T <;>
    simp only [hiT, hjT, if_true, if_false] at hij
  · exact hne (g_pow_inj H hi hj hij)
  · exact H.hsigned i hi j hj (by linear_combination hij)
  · exact H.hsigned j hj i hi (by linear_combination -hij)
  · exact hne (g_pow_inj H hi hj (by linear_combination -hij))

/-- The sum of the signed assignment over `range p` is `2·(subset-sum over T)`:
`∑_{i<p} e_T i = 2·∑_{i∈T} g^i` (the high/low recycling, via `∑_{i<p} g^i = 0`). -/
theorem signFun_sum (H : SignedWitnessHyp g p) (hp : 2 ≤ p) {T : Finset ℕ}
    (hT : T ⊆ Finset.range p) :
    ∑ i ∈ Finset.range p, signFun g T i = 2 * ∑ i ∈ T, g ^ i := by
  have hrw : ∀ i, signFun g T i = 2 * (if i ∈ T then g ^ i else 0) - g ^ i := by
    intro i
    simp only [signFun]
    by_cases h : i ∈ T
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]; ring
  have hgsum : ∑ i ∈ Finset.range p, (if i ∈ T then g ^ i else 0) = ∑ i ∈ T, g ^ i := by
    rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hT]
  rw [Finset.sum_congr rfl (fun i _ => hrw i), Finset.sum_sub_distrib,
    geom_sum_vanishG H hp, sub_zero, ← Finset.mul_sum, hgsum]

/-- The witness set `{e_T i : i < p}` for a subset `T ⊆ range p` lies in `signedPowersG g p`. -/
theorem signFun_image_subset (T : Finset ℕ) {p : ℕ} {g : ZMod q} :
    (Finset.range p).image (signFun g T) ⊆ signedPowersG g p := by
  intro x hx
  simp only [Finset.mem_image, Finset.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  simp only [signFun, signedPowersG, Finset.mem_union, Finset.mem_image, Finset.mem_range]
  by_cases h : i ∈ T
  · exact Or.inl ⟨i, hi, by rw [if_pos h]⟩
  · exact Or.inr ⟨i, hi, by rw [if_neg h]⟩

/-- **The core reduction (`⊇` direction).** Under the witness hypotheses, every `2·v` with
`v` a `{0,1}`-subset-sum of `{g^i : i<p}` is realized as a sum of `p` *distinct* signed powers,
i.e. lies in the `p`-fold distinct sumset of `signedPowersG g p`. -/
theorem doubled_subsetSum_mem_sumsetDistinct (H : SignedWitnessHyp g p) (hp : 2 ≤ p)
    {v : ZMod q} (hv : v ∈ subsetSumImage g p) :
    2 * v ∈ sumsetDistinct (signedPowersG g p) p := by
  rw [mem_subsetSumImage] at hv
  obtain ⟨T, hT, rfl⟩ := hv
  rw [mem_sumsetDistinct]
  refine ⟨(Finset.range p).image (signFun g T), signFun_image_subset T, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn (signFun_injOn H T), Finset.card_range]
  · rw [Finset.sum_image (fun a ha b hb h =>
      signFun_injOn H T (by simpa using ha) (by simpa using hb) h)]
    exact signFun_sum H hp hT

/-- **The doubled subset-sum image is contained in the signed `p`-fold sumset.** -/
theorem image_two_mul_subset (H : SignedWitnessHyp g p) (hp : 2 ≤ p) :
    (subsetSumImage g p).image (fun v => 2 * v) ⊆ sumsetDistinct (signedPowersG g p) p := by
  intro x hx
  simp only [Finset.mem_image] at hx
  obtain ⟨v, hv, rfl⟩ := hx
  exact doubled_subsetSum_mem_sumsetDistinct H hp hv

/-- **The signed `p`-fold sumset is at least as large as the subset-sum image.**
Since `2 ≠ 0` in a field of odd characteristic (`q ≠ 2`), `v ↦ 2v` is injective, so
`|sumsetDistinct (signedPowersG g p) p| ≥ |subsetSumImage g p|`. -/
theorem sumsetDistinct_card_ge (H : SignedWitnessHyp g p) (hp : 2 ≤ p)
    (hq2 : (2 : ZMod q) ≠ 0) :
    (subsetSumImage g p).card ≤ (sumsetDistinct (signedPowersG g p) p).card := by
  calc (subsetSumImage g p).card
      = ((subsetSumImage g p).image (fun v => 2 * v)).card := by
        rw [Finset.card_image_of_injOn]
        intro a _ b _ hab
        exact mul_left_cancel₀ hq2 hab
    _ ≤ (sumsetDistinct (signedPowersG g p) p).card :=
        Finset.card_le_card (image_two_mul_subset H hp)

/-- Membership characterization of `signedPowersG`. -/
theorem mem_signedPowersG {x : ZMod q} :
    x ∈ signedPowersG g p ↔ ∃ i < p, x = g ^ i ∨ x = -(g ^ i) := by
  simp only [signedPowersG, Finset.mem_union, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
    · exact ⟨i, hi, Or.inl rfl⟩
    · exact ⟨i, hi, Or.inr rfl⟩
  · rintro ⟨i, hi, (rfl | rfl)⟩
    · exact Or.inl ⟨i, hi, rfl⟩
    · exact Or.inr ⟨i, hi, rfl⟩

/-- `signedPowersG g p` has exactly `2p` elements (the `2p` signed powers are distinct). -/
theorem signedPowersG_card (H : SignedWitnessHyp g p) :
    (signedPowersG g p).card = 2 * p := by
  have hAinj : Set.InjOn (fun i => g ^ i) ↑(Finset.range p) := by
    intro a ha b hb hab
    exact g_pow_inj H (by simpa using ha) (by simpa using hb) hab
  have hBinj : Set.InjOn (fun i => -(g ^ i)) ↑(Finset.range p) := by
    intro a ha b hb hab
    exact g_pow_inj H (by simpa using ha) (by simpa using hb) (by linear_combination -hab)
  have hdisj : Disjoint ((Finset.range p).image (fun i => g ^ i))
      ((Finset.range p).image (fun i => -(g ^ i))) := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    simp only [Finset.mem_image, Finset.mem_range] at hxA hxB
    obtain ⟨i, hi, rfl⟩ := hxA
    obtain ⟨j, hj, hji⟩ := hxB
    exact H.hsigned i hi j hj (by linear_combination -hji)
  rw [signedPowersG, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injOn hAinj, Finset.card_image_of_injOn hBinj, Finset.card_range]
  omega

/-- `signedPowersG g p` is a multiplicative subgroup of `(ZMod q)ˣ` (Def 1.11): it contains `1`,
excludes `0`, and is closed under multiplication (using `g^a · g^b = g^{(a+b) mod p}` since
`g^p = 1`). -/
theorem isMulSubgroupOf_signedPowersG (H : SignedWitnessHyp g p) (hp : 2 ≤ p) :
    IsMulSubgroupOf (signedPowersG g p) := by
  haveI : NeZero q := ⟨(Fact.out (p := q.Prime)).pos.ne'⟩
  have hgp := g_pow_p H
  refine ⟨?_, ?_, ?_⟩
  · -- 1 ∈ G
    rw [mem_signedPowersG]; exact ⟨0, by omega, Or.inl (by rw [pow_zero])⟩
  · -- 0 ∉ G
    rw [mem_signedPowersG]
    rintro ⟨i, hi, (h | h)⟩
    · exact g_pow_ne_zero H hi h.symm
    · exact g_pow_ne_zero H hi (neg_eq_zero.mp h.symm)
  · -- mul-closed
    intro x hx y hy
    rw [mem_signedPowersG] at hx hy ⊢
    obtain ⟨i, hi, hxi⟩ := hx
    obtain ⟨j, hj, hyj⟩ := hy
    have hmod : g ^ (i + j) = g ^ ((i + j) % p) := by
      conv_lhs => rw [← Nat.div_add_mod (i + j) p, pow_add, pow_mul, hgp, one_pow, one_mul]
    refine ⟨(i + j) % p, Nat.mod_lt _ (by omega), ?_⟩
    rcases hxi with rfl | rfl <;> rcases hyj with rfl | rfl
    · exact Or.inl (by rw [← pow_add]; exact hmod)
    · exact Or.inr (by rw [mul_neg, ← pow_add, hmod])
    · exact Or.inr (by rw [neg_mul, ← pow_add, hmod])
    · exact Or.inl (by rw [neg_mul_neg, ← pow_add]; exact hmod)

/-- **THE ABSTRACT ADMISSIBILITY CRITERION (base-free).**
For a prime `q`, if `g ∈ ZMod q` has multiplicative order exactly `p ≥ 2`, its `2p` signed powers
`±g^i` (`i<p`) are pairwise distinct, `2 ≠ 0` in `ZMod q`, and the `{0,1}`-subset-sum image of
`{g^i : i<p}` has size `≥ a`, then `(q, a, 2p)` is admissible:
the subgroup `G = ⟨−g⟩` of order `2p` has `p`-fold distinct-element sumset of size `≥ a`.

This decouples the BCHKS25 admissibility plumbing from any particular base: the *only* remaining
input is the number-theoretic quantity `(subsetSumImage g p).card` (how many residues the base-`g`
`{0,1}`-digit sums hit) — which is the genuinely open core of Conjecture 1.12. The in-tree
base-`2` witnesses (`mersenne_admissible`, `mem_sumsetDistinct_signedPowers_factor`) are the
special case `g = 2`, `subsetSumImage = univ`; this brick covers *every* admissible base `g`. -/
theorem admissible_of_signedWitness (H : SignedWitnessHyp g p) (hp : 2 ≤ p)
    (hq2 : (2 : ZMod q) ≠ 0) {a : ℕ} (ha : a ≤ (subsetSumImage g p).card) :
    Admissible q a (2 * p) := by
  refine ⟨signedPowersG g p, isMulSubgroupOf_signedPowersG H hp, signedPowersG_card H, ?_⟩
  have hhalf : 2 * p / 2 = p := by omega
  rw [hhalf]
  exact le_trans ha (sumsetDistinct_card_ge H hp hq2)

end

/-! ## Sanity: the abstract criterion recovers the base-`2` Mersenne witness.

When `g = 2` over `ZMod (2^p − 1)` (`p` prime), the subset-sum image is *all* of `ZMod (2^p−1)`
(binary expansion), so the criterion fires with `a = q`. This shows the abstract criterion is at
least as strong as `mersenne_admissible` (it does not *re-prove* the base-`2` distinctness facts,
which live in `SubgroupSumsetConjecture`/`SubgroupSumsetFactorWitness`; the point is the *reduction*
is now base-free). -/

section Recovery
variable {p q : ℕ}

/-- For `g = 2` over a prime `q ∣ 2^p − 1` (`p ≥ 3` prime), the witness hypotheses hold:
order `p` (`orderOf_two_eq`) and signed-power distinctness (`two_pow_add_ne_zero_q'`). -/
theorem signedWitnessHyp_two (hpp : p.Prime) (hp3 : 3 ≤ p) (hqp : q.Prime) (hq : 1 < q)
    (hdvd : q ∣ 2 ^ p - 1) :
    SignedWitnessHyp (2 : ZMod q) p where
  hord := orderOf_two_eq hpp hq hdvd
  hsigned := by
    intro i hi j hj
    exact two_pow_add_ne_zero_q' hpp hp3 hqp hq hdvd hi hj

/-- For `g = 2` over a prime `q ∣ 2^p − 1`, the `{0,1}`-subset-sum image of `{2^i : i<p}` is
*all* of `ZMod q` — the binary expansion of `v.val < q ≤ 2^p − 1` (lifting the in-tree
`exists_subset_sum_eq` through the cast `ℕ → ZMod q`). -/
theorem subsetSumImage_two_eq_univ [NeZero q] (hp : 1 ≤ p)
    (hdvd : q ∣ 2 ^ p - 1) :
    subsetSumImage (2 : ZMod q) p = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro v
  rw [mem_subsetSumImage]
  -- v.val < q ≤ 2^p - 1 < 2^p
  have h2 : 2 ≤ 2 ^ p := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ p := by gcongr; omega
  have hqle : q ≤ 2 ^ p - 1 := Nat.le_of_dvd (by omega) hdvd
  have hvlt : v.val < 2 ^ p := by have := ZMod.val_lt v; omega
  obtain ⟨T, hT, hTsum⟩ := exists_subset_sum_eq p v.val hvlt
  refine ⟨T, hT, ?_⟩
  have hcast : ∑ i ∈ T, (2 : ZMod q) ^ i = ((∑ i ∈ T, 2 ^ i : ℕ) : ZMod q) := by
    push_cast; ring
  rw [hcast, hTsum, ZMod.natCast_zmod_val]

/-- **Recovery: the abstract criterion subsumes the base-`2` factor witness.**
For a prime `q ∣ 2^p − 1` (`p ≥ 3` prime), `(q, q, 2p)` is admissible — obtained purely from the
base-free `admissible_of_signedWitness` by feeding it `subsetSumImage = univ` (card `q`). This
reproduces `mem_sumsetDistinct_signedPowers_factor`'s consequence through the general reduction,
confirming the criterion is at least as strong as the in-tree witnesses. -/
theorem admissible_two_factor (hpp : p.Prime) (hp3 : 3 ≤ p) (hqp : q.Prime) (hq : 1 < q)
    (hdvd : q ∣ 2 ^ p - 1) :
    Admissible q q (2 * p) := by
  haveI : Fact q.Prime := ⟨hqp⟩
  haveI : NeZero q := ⟨by omega⟩
  have hH := signedWitnessHyp_two hpp hp3 hqp hq hdvd
  have hq2 : (2 : ZMod q) ≠ 0 := q_odd hp3 hq hdvd
  have hcard : q ≤ (subsetSumImage (2 : ZMod q) p).card := by
    rw [subsetSumImage_two_eq_univ (by omega) hdvd, Finset.card_univ, ZMod.card]
  exact admissible_of_signedWitness hH (by omega) hq2 hcard

end Recovery

end ArkLib.ProximityGap.SubgroupSumset.Widen
