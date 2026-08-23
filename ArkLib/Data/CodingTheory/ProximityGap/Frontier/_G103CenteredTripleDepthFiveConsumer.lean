/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# G103: centered triple concentration closes depth five (the minimal post-G102 certificate)

G102 proves that no envelope in (cardinality, pair-sum concentration) can absorb the depth-5
sector of the padded collision lane.  This file identifies and consumes the **minimal
upgrade**: the *centered* triple-sum concentration.

Raw triple concentration is degenerate at production: for even `n`, `-1 ∈ μ_n`, so every
`a ∈ H` carries the antipodal family `a + (y + (-y))`; the probe verifies `N₃(a) = 3n - 3`
exactly on `H`.  So raw `M₃ ≥ 3n ≈ 2^{31.6}` at `n = 2^30`, above the `2^{25.8}` closing
threshold — raw triple concentration cannot close depth 5 either.  Splitting off the
antipodal (degenerate) mass, the probe measures the centered concentration at
`6..18 = O(1)` across all tested scales.

**The consumer chain (this file).**  With `M₃ᶜ = max_x centTripleCount x` and
`M₂ = max_{c≠0} pairCount c`:

  `quintCount a = Σ_c pairCount c · tripleCount (a-c)`      (`quintCount_eq_conv`)
  `            ≤ M₃ᶜ·n² + 3·M₂·n² + 3·n²`      (degenerate total ≤ 3n², `c = 0` term ≤ 3n²)
  `J₅ = Σ_a quintCount a ^ 2 ≤ (M₃ᶜ + 3·M₂ + 3) · n⁷`,

and the production kernel inequality shows `(M₃ᶜ, M₂) = (2^24, 2^22)` puts the depth-5
sector inside one full Wick budget at `(n, r) = (2^30, 110)` — where `2^22 = 4·n^{2/3}` is
the known Stepanov pair bound (Garcia–Voloch 1988 / Heath-Brown–Konyagin 2000) and `2^24`
has `2^{20}` headroom over the measured `O(1)` truth (kernel margin `2^{1.01}`).

`hM3` is a **named external hypothesis** — no Stepanov analog is recorded for the centered
triple statistic; this file is the arithmetic consumer only.  Together with G102 the frontier
object is pinned exactly: pair statistics are provably insufficient at depth 5, and the
centered triple statistic is sufficient.
Probe: `scripts/probes/probe_466_g103_centered_triple_concentration.py`.  Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G103CenteredTripleDepthFiveConsumer

open Finset
open scoped Nat

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-! ## Counts -/

/-- Ordered pairs from `S` with sum `c`. -/
def pairCount (S : Finset G) (c : G) : ℕ :=
  ((S ×ˢ S).filter fun q => q.1 + q.2 = c).card

/-- Ordered triples from `S` with sum `a`. -/
def tripleCount (S : Finset G) (a : G) : ℕ :=
  ((S ×ˢ S ×ˢ S).filter fun t => t.1 + t.2.1 + t.2.2 = a).card

/-- A triple is degenerate when two of its entries are antipodal. -/
def IsDeg (t : G × G × G) : Prop :=
  t.1 + t.2.1 = 0 ∨ t.1 + t.2.2 = 0 ∨ t.2.1 + t.2.2 = 0

instance moduleInstance_G103CenteredTripleDepthFiveConsumer_1 : DecidablePred (IsDeg (G := G)) := fun t => by
  unfold IsDeg
  infer_instance

/-- Centered (non-degenerate) triple count. -/
def centTripleCount (S : Finset G) (a : G) : ℕ :=
  ((S ×ˢ S ×ˢ S).filter fun t => t.1 + t.2.1 + t.2.2 = a ∧ ¬IsDeg t).card

/-- Degenerate triple count with sum `a`. -/
def degTripleCount (S : Finset G) (a : G) : ℕ :=
  ((S ×ˢ S ×ˢ S).filter fun t => t.1 + t.2.1 + t.2.2 = a ∧ IsDeg t).card

/-- Ordered (pair, triple) tuples with total sum `a` — the depth-5 fiber count in the
reassociated shape (the G87 `quadCount` convention one depth up). -/
def quintCount (S : Finset G) (a : G) : ℕ :=
  (((S ×ˢ S) ×ˢ (S ×ˢ S ×ˢ S)).filter
    fun q => q.1.1 + q.1.2 + (q.2.1 + q.2.2.1 + q.2.2.2) = a).card

/-- The depth-5 equal-sum mass `J₅ = Σ_a N₅(a)²`. -/
def equalSumQuintMass (S : Finset G) : ℕ :=
  ∑ a : G, quintCount S a ^ 2

/-! ## Elementary mass identities -/

theorem pairCount_le_card (S : Finset G) (c : G) : pairCount S c ≤ S.card := by
  classical
  unfold pairCount
  have hsub : ∀ q ∈ (S ×ˢ S).filter (fun q : G × G => q.1 + q.2 = c), q.1 ∈ S :=
    fun q hq => (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).1
  have hinj : Set.InjOn (fun q : G × G => q.1)
      (((S ×ˢ S).filter (fun q : G × G => q.1 + q.2 = c) : Finset (G × G)) :
        Set (G × G)) := by
    rintro ⟨a1, a2⟩ ha ⟨b1, b2⟩ hb h
    have ha' : a1 + a2 = c := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
    have hb' : b1 + b2 = c := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2
    have h1 : a1 = b1 := h
    have h2 : a2 = b2 := by
      rw [h1] at ha'
      exact add_left_cancel (ha'.trans hb'.symm)
    simp [h1, h2]
  exact Finset.card_le_card_of_injOn _ hsub hinj

theorem sum_pairCount (S : Finset G) : ∑ c : G, pairCount S c = S.card ^ 2 := by
  classical
  have h : (S ×ˢ S).card =
      ∑ c ∈ Finset.univ, ((S ×ˢ S).filter fun q : G × G => q.1 + q.2 = c).card :=
    Finset.card_eq_sum_card_fiberwise fun q _ => Finset.mem_univ _
  unfold pairCount
  rw [← h, Finset.card_product]
  ring

theorem sum_quintCount (S : Finset G) : ∑ a : G, quintCount S a = S.card ^ 5 := by
  classical
  have h : (((S ×ˢ S) ×ˢ (S ×ˢ S ×ˢ S)).card) =
      ∑ a ∈ Finset.univ, (((S ×ˢ S) ×ˢ (S ×ˢ S ×ˢ S)).filter
        fun q => q.1.1 + q.1.2 + (q.2.1 + q.2.2.1 + q.2.2.2) = a).card :=
    Finset.card_eq_sum_card_fiberwise fun q _ => Finset.mem_univ _
  unfold quintCount
  rw [← h]
  simp only [Finset.card_product]
  ring

theorem tripleCount_split (S : Finset G) (a : G) :
    tripleCount S a = centTripleCount S a + degTripleCount S a := by
  classical
  unfold tripleCount centTripleCount degTripleCount
  rw [← Finset.filter_filter (fun t : G × G × G => t.1 + t.2.1 + t.2.2 = a)
      (fun t => ¬IsDeg t),
    ← Finset.filter_filter (fun t : G × G × G => t.1 + t.2.1 + t.2.2 = a)
      (fun t => IsDeg t),
    add_comm, Finset.filter_card_add_filter_neg_card_eq_card]

/-! ## The degenerate mass is at most `3n²` in total -/

/-- Encoding of a degenerate triple: which pair is antipodal, its first entry, and the
remaining free entry. -/
private def degEncode : G × G × G → ℕ × G × G := fun t =>
  if t.1 + t.2.1 = 0 then (0, t.1, t.2.2)
  else if t.1 + t.2.2 = 0 then (1, t.1, t.2.1)
  else (2, t.2.1, t.1)

private def degDecode : ℕ × G × G → G × G × G := fun q =>
  if q.1 = 0 then (q.2.1, -q.2.1, q.2.2)
  else if q.1 = 1 then (q.2.1, q.2.2, -q.2.1)
  else (q.2.2, q.2.1, -q.2.1)

private theorem degDecode_degEncode (t : G × G × G) (hdeg : IsDeg t) :
    degDecode (degEncode t) = t := by
  obtain ⟨x, y, z⟩ := t
  unfold degEncode
  by_cases c1 : x + y = 0
  · rw [if_pos c1]
    have hy : y = -x := (neg_eq_of_add_eq_zero_right c1).symm
    unfold degDecode
    norm_num
    exact hy.symm
  · rw [if_neg c1]
    by_cases c2 : x + z = 0
    · rw [if_pos c2]
      have hz : z = -x := (neg_eq_of_add_eq_zero_right c2).symm
      unfold degDecode
      norm_num
      exact hz.symm
    · rw [if_neg c2]
      have c3 : y + z = 0 := by
        rcases hdeg with h | h | h
        · exact absurd h c1
        · exact absurd h c2
        · exact h
      have hz : z = -y := (neg_eq_of_add_eq_zero_right c3).symm
      unfold degDecode
      norm_num
      exact hz.symm

/-- Total degenerate mass: at most `3·n²`. -/
theorem sum_degTripleCount_le (S : Finset G) :
    ∑ a : G, degTripleCount S a ≤ 3 * S.card ^ 2 := by
  classical
  have hfib : ∑ a : G, degTripleCount S a =
      ((S ×ˢ S ×ˢ S).filter fun t => IsDeg t).card := by
    unfold degTripleCount
    rw [Finset.card_eq_sum_card_fiberwise
      (f := fun t : G × G × G => t.1 + t.2.1 + t.2.2) (t := Finset.univ)
      (fun t _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.filter_filter]
    exact congrArg Finset.card (Finset.filter_congr fun t _ => and_comm)
  rw [hfib]
  have hmap : ∀ t ∈ (S ×ˢ S ×ˢ S).filter fun t => IsDeg t,
      degEncode t ∈ (Finset.range 3) ×ˢ S ×ˢ S := by
    intro t ht
    simp only [mem_filter, mem_product] at ht
    obtain ⟨⟨h1, h2, h3⟩, -⟩ := ht
    unfold degEncode
    by_cases c1 : t.1 + t.2.1 = 0
    · rw [if_pos c1]
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by norm_num),
        Finset.mem_product.mpr ⟨h1, h3⟩⟩
    · rw [if_neg c1]
      by_cases c2 : t.1 + t.2.2 = 0
      · rw [if_pos c2]
        exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by norm_num),
          Finset.mem_product.mpr ⟨h1, h2⟩⟩
      · rw [if_neg c2]
        exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by norm_num),
          Finset.mem_product.mpr ⟨h2, h1⟩⟩
  have hinj : Set.InjOn degEncode
      (((S ×ˢ S ×ˢ S).filter fun t => IsDeg t : Finset (G × G × G)) :
        Set (G × G × G)) := by
    intro t ht t' ht' he
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at ht ht'
    rw [← degDecode_degEncode t ht.2, ← degDecode_degEncode t' ht'.2, he]
  calc ((S ×ˢ S ×ˢ S).filter fun t => IsDeg t).card
      ≤ ((Finset.range 3) ×ˢ S ×ˢ S).card :=
        Finset.card_le_card_of_injOn degEncode hmap hinj
    _ = 3 * S.card ^ 2 := by
        simp only [Finset.card_product, Finset.card_range]
        ring

/-! ## The depth-5 convolution and the pointwise bound -/

/-- The depth-5 fiber over a fixed pair sum `c` is a product of the pair fiber at `c` and the
triple fiber at `a - c`. -/
theorem quint_fiber_eq_product (S : Finset G) (a c : G) :
    ((((S ×ˢ S) ×ˢ (S ×ˢ S ×ˢ S)).filter
        fun q => q.1.1 + q.1.2 + (q.2.1 + q.2.2.1 + q.2.2.2) = a).filter
      fun q => q.1.1 + q.1.2 = c) =
    ((S ×ˢ S).filter fun q : G × G => q.1 + q.2 = c) ×ˢ
      ((S ×ˢ S ×ˢ S).filter fun t => t.1 + t.2.1 + t.2.2 = a - c) := by
  classical
  ext q
  simp only [Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, htot⟩, hfst⟩
    refine ⟨⟨h1, hfst⟩, h2, ?_⟩
    rw [← htot, hfst]
    abel
  · rintro ⟨⟨h1, hfst⟩, h2, hsnd⟩
    refine ⟨⟨⟨h1, h2⟩, ?_⟩, hfst⟩
    rw [hfst, hsnd]
    abel

theorem quintCount_eq_conv (S : Finset G) (a : G) :
    quintCount S a = ∑ c : G, pairCount S c * tripleCount S (a - c) := by
  classical
  unfold quintCount
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun q : (G × G) × (G × G × G) => q.1.1 + q.1.2) (t := Finset.univ)
    (fun q _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [quint_fiber_eq_product, Finset.card_product]
  rfl

/-! ## The per-target degenerate bound `≤ 3n` -/

/-- Per-target degenerate encoding: the antipodal pair position and its first entry (the
third entry is forced by the sum). -/
private def degEncA : G × G × G → ℕ × G := fun t =>
  if t.1 + t.2.1 = 0 then (0, t.1)
  else if t.1 + t.2.2 = 0 then (1, t.1)
  else (2, t.2.1)

private def degDecA (a : G) : ℕ × G → G × G × G := fun q =>
  if q.1 = 0 then (q.2, -q.2, a)
  else if q.1 = 1 then (q.2, a, -q.2)
  else (a, q.2, -q.2)

private theorem degDecA_degEncA (a : G) (t : G × G × G)
    (hsum : t.1 + t.2.1 + t.2.2 = a) (hdeg : IsDeg t) :
    degDecA a (degEncA t) = t := by
  obtain ⟨x, y, z⟩ := t
  simp only at hsum
  unfold degEncA
  by_cases c1 : x + y = 0
  · rw [if_pos c1]
    have hy : y = -x := (neg_eq_of_add_eq_zero_right c1).symm
    have hz : z = a := by rwa [c1, zero_add] at hsum
    unfold degDecA
    norm_num
    exact ⟨hy.symm, hz.symm⟩
  · rw [if_neg c1]
    by_cases c2 : x + z = 0
    · rw [if_pos c2]
      have hz : z = -x := (neg_eq_of_add_eq_zero_right c2).symm
      have hy : y = a := by
        rw [hz] at hsum
        have hcancel : x + y + -x = y := by abel
        rwa [hcancel] at hsum
      unfold degDecA
      norm_num
      exact ⟨hy.symm, hz.symm⟩
    · rw [if_neg c2]
      have c3 : y + z = 0 := by
        rcases hdeg with h | h | h
        · exact absurd h c1
        · exact absurd h c2
        · exact h
      have hz : z = -y := (neg_eq_of_add_eq_zero_right c3).symm
      have hx : x = a := by
        rw [hz] at hsum
        have hcancel : x + y + -y = x := by abel
        rwa [hcancel] at hsum
      unfold degDecA
      norm_num
      exact ⟨hx.symm, hz.symm⟩

/-- Per-target degenerate mass: at most `3n` (the third entry is forced by the sum). -/
theorem degTripleCount_le (S : Finset G) (a : G) :
    degTripleCount S a ≤ 3 * S.card := by
  classical
  unfold degTripleCount
  have hmap : ∀ t ∈ (S ×ˢ S ×ˢ S).filter
      fun t => t.1 + t.2.1 + t.2.2 = a ∧ IsDeg t,
      degEncA t ∈ (Finset.range 3) ×ˢ S := by
    intro t ht
    simp only [mem_filter, mem_product] at ht
    obtain ⟨⟨h1, h2, h3⟩, -⟩ := ht
    unfold degEncA
    by_cases c1 : t.1 + t.2.1 = 0
    · rw [if_pos c1]
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by norm_num), h1⟩
    · rw [if_neg c1]
      by_cases c2 : t.1 + t.2.2 = 0
      · rw [if_pos c2]
        exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by norm_num), h1⟩
      · rw [if_neg c2]
        exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by norm_num), h2⟩
  have hinj : Set.InjOn degEncA
      (((S ×ˢ S ×ˢ S).filter fun t => t.1 + t.2.1 + t.2.2 = a ∧ IsDeg t :
        Finset (G × G × G)) : Set (G × G × G)) := by
    intro t ht t' ht' he
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at ht ht'
    rw [← degDecA_degEncA a t ht.2.1 ht.2.2, ← degDecA_degEncA a t' ht'.2.1 ht'.2.2, he]
  calc ((S ×ˢ S ×ˢ S).filter fun t => t.1 + t.2.1 + t.2.2 = a ∧ IsDeg t).card
      ≤ ((Finset.range 3) ×ˢ S).card :=
        Finset.card_le_card_of_injOn degEncA hmap hinj
    _ = 3 * S.card := by simp [Finset.card_product]

/-! ## The pointwise depth-5 bound and the mass bound -/

/-- **Pointwise depth-5 bound from centered-triple and pair concentrations.** -/
theorem quintCount_le (S : Finset G) {M2 M3 : ℕ}
    (hM2 : ∀ c : G, c ≠ 0 → pairCount S c ≤ M2)
    (hM3 : ∀ x : G, centTripleCount S x ≤ M3) (a : G) :
    quintCount S a ≤ (M3 + 3 * M2 + 3) * S.card ^ 2 := by
  classical
  rw [quintCount_eq_conv]
  have hsplit : ∀ c : G, pairCount S c * tripleCount S (a - c) =
      pairCount S c * centTripleCount S (a - c) +
        pairCount S c * degTripleCount S (a - c) := by
    intro c
    rw [tripleCount_split, Nat.mul_add]
  rw [Finset.sum_congr rfl fun c _ => hsplit c, Finset.sum_add_distrib]
  have hterm1 : ∑ c : G, pairCount S c * centTripleCount S (a - c)
      ≤ M3 * S.card ^ 2 := by
    calc ∑ c : G, pairCount S c * centTripleCount S (a - c)
        ≤ ∑ c : G, pairCount S c * M3 :=
          Finset.sum_le_sum fun c _ => Nat.mul_le_mul_left _ (hM3 _)
      _ = (∑ c : G, pairCount S c) * M3 := by rw [← Finset.sum_mul]
      _ = M3 * S.card ^ 2 := by rw [sum_pairCount]; ring
  have hterm2 : ∑ c : G, pairCount S c * degTripleCount S (a - c)
      ≤ 3 * M2 * S.card ^ 2 + 3 * S.card ^ 2 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : G))]
    have hzero : pairCount S 0 * degTripleCount S (a - 0) ≤ 3 * S.card ^ 2 := by
      calc pairCount S 0 * degTripleCount S (a - 0)
          ≤ S.card * (3 * S.card) :=
            Nat.mul_le_mul (pairCount_le_card S 0) (degTripleCount_le S _)
        _ = 3 * S.card ^ 2 := by ring
    have hrest : ∑ c ∈ Finset.univ.erase (0 : G),
        pairCount S c * degTripleCount S (a - c) ≤ 3 * M2 * S.card ^ 2 := by
      calc ∑ c ∈ Finset.univ.erase (0 : G), pairCount S c * degTripleCount S (a - c)
          ≤ ∑ c ∈ Finset.univ.erase (0 : G), M2 * degTripleCount S (a - c) :=
            Finset.sum_le_sum fun c hc =>
              Nat.mul_le_mul_right _ (hM2 c (Finset.ne_of_mem_erase hc))
        _ ≤ ∑ c : G, M2 * degTripleCount S (a - c) :=
            Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
        _ = M2 * ∑ c : G, degTripleCount S (a - c) := by rw [Finset.mul_sum]
        _ = M2 * ∑ x : G, degTripleCount S x := by
            rw [Fintype.sum_equiv (Equiv.subLeft a)
              (fun c => degTripleCount S (a - c)) (fun x => degTripleCount S x)
              (fun c => rfl)]
        _ ≤ M2 * (3 * S.card ^ 2) :=
            Nat.mul_le_mul_left _ (sum_degTripleCount_le S)
        _ = 3 * M2 * S.card ^ 2 := by ring
    omega
  calc (∑ c : G, pairCount S c * centTripleCount S (a - c)) +
        ∑ c : G, pairCount S c * degTripleCount S (a - c)
      ≤ M3 * S.card ^ 2 + (3 * M2 * S.card ^ 2 + 3 * S.card ^ 2) :=
        Nat.add_le_add hterm1 hterm2
    _ = (M3 + 3 * M2 + 3) * S.card ^ 2 := by ring

/-- **The depth-5 mass bound.** -/
theorem equalSumQuintMass_le (S : Finset G) {M2 M3 : ℕ}
    (hM2 : ∀ c : G, c ≠ 0 → pairCount S c ≤ M2)
    (hM3 : ∀ x : G, centTripleCount S x ≤ M3) :
    equalSumQuintMass S ≤ (M3 + 3 * M2 + 3) * S.card ^ 7 := by
  unfold equalSumQuintMass
  calc ∑ a : G, quintCount S a ^ 2
      ≤ ∑ a : G, ((M3 + 3 * M2 + 3) * S.card ^ 2) * quintCount S a := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [sq]
        exact Nat.mul_le_mul_right _ (quintCount_le S hM2 hM3 a)
    _ = ((M3 + 3 * M2 + 3) * S.card ^ 2) * ∑ a : G, quintCount S a := by
        rw [Finset.mul_sum]
    _ = ((M3 + 3 * M2 + 3) * S.card ^ 2) * S.card ^ 5 := by rw [sum_quintCount]
    _ = (M3 + 3 * M2 + 3) * S.card ^ 7 := by ring

/-! ## The production consumer -/

theorem choose_110_5 : Nat.choose 110 5 = 122391522 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]
  rfl

/-- Production kernel: the depth-5 mass bound at `(M₃ᶜ, M₂) = (2^24, 2^22)` fits inside the
depth-5 share of one full Wick budget at `(n, r) = (2^30, 110)` (margin `2^{1.01}`). -/
theorem production_kernel :
    ((2 ^ 24 + 3 * 2 ^ 22 + 3) * (2 ^ 30) ^ 7) * (122391522 ^ 2 * (105)!)
      ≤ Nat.doubleFactorial 219 * (2 ^ 30) ^ 5 := by
  decide

/-- **Headline: depth five is absorbed under centered-triple concentration `2^24` and pair
concentration `2^22`.**  `hM2` is the Stepanov level (Garcia–Voloch / Heath-Brown–Konyagin
give `4·n^{2/3} = 2^22` for multiplicative subgroups of size `n ≤ p^{2/3}`); `hM3` is the
named external hypothesis `CenteredTripleSumConcentration24`, measured at `O(1)` for real
subgroups by the probe.  G102 shows `hM2`-style inputs alone can never suffice. -/
theorem production_depth5_of_centered_triple (S : Finset G)
    (hcard : S.card = 2 ^ 30)
    (hM2 : ∀ c : G, c ≠ 0 → pairCount S c ≤ 2 ^ 22)
    (hM3 : ∀ x : G, centTripleCount S x ≤ 2 ^ 24) :
    equalSumQuintMass S * (Nat.choose 110 5 ^ 2 * (105)!) ≤
      Nat.doubleFactorial 219 * (2 ^ 30) ^ 5 := by
  have hJ := equalSumQuintMass_le S hM2 hM3
  rw [hcard] at hJ
  rw [choose_110_5]
  calc equalSumQuintMass S * (122391522 ^ 2 * (105)!)
      ≤ ((2 ^ 24 + 3 * 2 ^ 22 + 3) * (2 ^ 30) ^ 7) * (122391522 ^ 2 * (105)!) :=
        Nat.mul_le_mul_right _ hJ
    _ ≤ Nat.doubleFactorial 219 * (2 ^ 30) ^ 5 := production_kernel

end ArkLib.ProximityGap.Frontier.G103CenteredTripleDepthFiveConsumer

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G103CenteredTripleDepthFiveConsumer.tripleCount_split
#print axioms
  ArkLib.ProximityGap.Frontier.G103CenteredTripleDepthFiveConsumer.sum_degTripleCount_le
#print axioms
  ArkLib.ProximityGap.Frontier.G103CenteredTripleDepthFiveConsumer.degTripleCount_le
#print axioms
  ArkLib.ProximityGap.Frontier.G103CenteredTripleDepthFiveConsumer.quintCount_eq_conv
#print axioms
  ArkLib.ProximityGap.Frontier.G103CenteredTripleDepthFiveConsumer.quintCount_le
#print axioms
  ArkLib.ProximityGap.Frontier.G103CenteredTripleDepthFiveConsumer.equalSumQuintMass_le
#print axioms
  ArkLib.ProximityGap.Frontier.G103CenteredTripleDepthFiveConsumer.production_kernel
#print axioms ArkLib.ProximityGap.Frontier.G103CenteredTripleDepthFiveConsumer.production_depth5_of_centered_triple
