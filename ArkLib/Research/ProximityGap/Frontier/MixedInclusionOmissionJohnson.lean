/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.InterleavedListJohnsonPuncture

/-!
# Mixed Inclusion–Omission Johnson Bounds Beyond the Johnson Radius

Simultaneously conditioning a constant-weight set family `S : Fin m → Finset I`
(each of size `t`, pairwise intersections `≤ d`) on `s` included sites `A ⊆ S i`
and `r` omitted sites `R` disjoint from `S i` restricts the remaining coordinates
to a universe of size `n - s - r`, weight `t - s`, and pairwise cap `d - s`.
Whenever `(n - s - r) * (d - s) < (t - s)²`, the strict Johnson rank bound holds
on every fiber `(A, R)`, giving:
`m * choose t s * choose (n - t) r ≤ choose n s * choose (n - s) r * (n - s - r)`.

This strictly generalizes both `MultipleOmissionJohnson` (`s = 0`) and pure
site-inclusion (`r = 0`). At production length `n = 2³⁰`:
- Rate `1/16`, `Johnson + 1` (`e = 805,306,371`): `(r = 0, s = 1)` yields list size
  `≤ 4,294,967,340` (`4.00n`), improving `MultipleOmissionJohnson`'s `10,725,307,448`
  by `2.50×` and even beating `CubicHahnJohnson`'s `5,010,795,150`.
- Rate `1/4`, `Johnson + 1` (`e = 536,870,914`): the exact algebraic identity
  `(2k - 3)² - (4k - 4)(k - 2) = 1 > 0` lets `(r = 3, s = 1)` yield `≤ 17,179,868,992`
  (`16.00n`, cutting `MultipleOmissionJohnson`'s `34,359,737,888` in half for all `k ≥ 4`).
- Uniformly for all `n ≥ 256` at rate `1/16`, `(r = 0, s = 1)` certifies `≤ 5n`
  at `Johnson + 1` over arbitrary fields, injective domains, and widths.
-/

set_option autoImplicit false

namespace ProximityGap.MixedInclusionOmissionJohnson

open Finset Code InterleavedListJohnsonRank
open ArkLib.ProximityGap.Frontier.HalfPredecessorRateQuarterObtuse
  (card_le_universe_of_equal_card_pair_inter_le)

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Simultaneous `s`-inclusion and `r`-omission block bound:
each block contains `choose t s` `s`-sets and omits `choose (n - t) r` `r`-sets,
while every disjoint pair `(A, R)` of sizes `(s, r)` belongs to at most `n - s - r`
blocks once `(n - s - r) * (d - s) < (t - s)²`. -/
theorem block_inclusion_omission {m t d s r : ℕ} (S : Fin m → Finset I)
    (hts : s + 1 ≤ t) (hw : ∀ i, (S i).card = t)
    (hp : Pairwise fun i j => (S i ∩ S j).card ≤ d)
    (hstrict : (Fintype.card I - s - r) * (d - s) < (t - s) ^ 2) :
    m * (t.choose s * (Fintype.card I - t).choose r) ≤
      (Fintype.card I).choose s * (Fintype.card I - s).choose r *
        (Fintype.card I - s - r) := by
  classical
  let samples : Finset (Finset I × Finset I) :=
    ((univ : Finset I).powersetCard s).biUnion fun A =>
      (Aᶜ.powersetCard r).map ⟨fun R => (A, R), fun _ _ h => (Prod.mk.inj h).2⟩
  let cond (i : Fin m) (p : Finset I × Finset I) : Prop := p.1 ⊆ S i ∧ Disjoint p.2 (S i)
  have hsamples_card :
      samples.card = (Fintype.card I).choose s * (Fintype.card I - s).choose r := by
    rw [card_biUnion]
    · calc
        ∑ A ∈ (univ : Finset I).powersetCard s,
            ((Aᶜ.powersetCard r).map ⟨fun R => (A, R), fun _ _ h => (Prod.mk.inj h).2⟩).card
          = ∑ A ∈ (univ : Finset I).powersetCard s, (Fintype.card I - s).choose r := by
            refine Finset.sum_congr rfl fun A hA => ?_
            rw [card_map, card_powersetCard, card_compl, (mem_powersetCard.mp hA).2]
        _ = (Fintype.card I).choose s * (Fintype.card I - s).choose r := by
            simp [card_powersetCard]
    · intro A1 _ A2 _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      rcases mem_map.mp hp1 with ⟨R1, _, rfl⟩
      rcases mem_map.mp hp2 with ⟨R2, _, heq⟩
      exact hne (Prod.mk.inj heq).1.symm
  have above (i : Fin m) :
      (samples.bipartiteAbove cond i).card = t.choose s * (Fintype.card I - t).choose r := by
    have he : samples.bipartiteAbove cond i =
        (S i).powersetCard s ×ˢ ((S i)ᶜ).powersetCard r := by
      ext ⟨A, R⟩
      simp only [bipartiteAbove, mem_filter, samples, mem_biUnion, mem_powersetCard,
        mem_map, mem_product, cond, subset_univ, true_and, subset_compl_iff_disjoint_right]
      constructor
      · rintro ⟨⟨A', hA'card, R', ⟨_, hR'card⟩, hpair_eq⟩, hAsub, hRdis⟩
        rcases Prod.mk.inj hpair_eq with ⟨rfl, rfl⟩
        exact ⟨⟨hAsub, hA'card⟩, ⟨hRdis, hR'card⟩⟩
      · rintro ⟨⟨hAsub, hAcard⟩, ⟨hRdis, hRcard⟩⟩
        refine ⟨⟨A, hAcard, R, ⟨hRdis.mono_right hAsub, hRcard⟩, rfl⟩, hAsub, hRdis⟩
    rw [he, card_product, card_powersetCard, card_powersetCard, card_compl, hw]
  have below (p : Finset I × Finset I) (hp_mem : p ∈ samples) :
      (univ.bipartiteBelow cond p).card ≤ Fintype.card I - s - r := by
    rcases mem_biUnion.mp hp_mem with ⟨A, hA, hRmap⟩
    rcases mem_map.mp hRmap with ⟨R, hR, rfl⟩
    have hAcard : A.card = s := (mem_powersetCard.mp hA).2
    have hRsub : R ⊆ Aᶜ := (mem_powersetCard.mp hR).1
    have hRcard : R.card = r := (mem_powersetCard.mp hR).2
    have hARdis : Disjoint A R := (subset_compl_iff_disjoint_right.mp hRsub).symm
    let U : Finset I := (A ∪ R)ᶜ
    let T := univ.bipartiteBelow cond (A, R)
    let B (i : T) : Finset ↥U := (S i.val).subtype (· ∈ U)
    have hUcard : Fintype.card ↥U = Fintype.card I - s - r := by
      rw [Fintype.card_coe, card_compl, card_union_of_disjoint hARdis, hAcard, hRcard]
      omega
    have hfilter_eq (i : T) : (S i.val).filter (· ∈ U) = S i.val \ A := by
      have hRdis : Disjoint R (S i.val) := (mem_filter.mp i.property).2.2
      ext x
      simp only [mem_filter, U, mem_compl, mem_union, not_or, mem_sdiff]
      constructor
      · rintro ⟨hxS, hxA, _⟩; exact ⟨hxS, hxA⟩
      · rintro ⟨hxS, hxA⟩
        exact ⟨hxS, hxA, fun hxR => Finset.disjoint_left.mp hRdis hxR hxS⟩
    have hBcard (i : T) : (B i).card = t - s := by
      have hAsub : A ⊆ S i.val := (mem_filter.mp i.property).2.1
      rw [show (B i).card = ((S i.val).filter (· ∈ U)).card from card_subtype _ _,
        hfilter_eq i, card_sdiff_of_subset hAsub, hw, hAcard]
    have hBpair : Pairwise fun i j : T => (B i ∩ B j).card ≤ d - s := by
      intro i j hij
      have hAsub_i : A ⊆ S i.val := (mem_filter.mp i.property).2.1
      have hAsub_j : A ⊆ S j.val := (mem_filter.mp j.property).2.1
      have hAsub_ij : A ⊆ S i.val ∩ S j.val := subset_inter hAsub_i hAsub_j
      have hRdis_i : Disjoint R (S i.val) := (mem_filter.mp i.property).2.2
      have hinter : B i ∩ B j = (S i.val ∩ S j.val).subtype (· ∈ U) := by
        ext x; simp [B]
      have hfilt : (S i.val ∩ S j.val).filter (· ∈ U) = (S i.val ∩ S j.val) \ A := by
        ext x
        simp only [mem_filter, U, mem_compl, mem_union, not_or, mem_sdiff, mem_inter]
        constructor
        · rintro ⟨⟨h1, h2⟩, hxA, _⟩; exact ⟨⟨h1, h2⟩, hxA⟩
        · rintro ⟨⟨h1, h2⟩, hxA⟩
          exact ⟨⟨h1, h2⟩, hxA, fun hxR => Finset.disjoint_left.mp hRdis_i hxR h1⟩
      rw [hinter, card_subtype, hfilt, card_sdiff_of_subset hAsub_ij, hAcard]
      exact Nat.sub_le_sub_right (hp (fun h => hij (Subtype.ext h))) s
    have hcard := card_le_universe_of_equal_card_pair_inter_le B (Fintype.card I - s - r)
      (t - s) (d - s) hUcard (by omega) hBcard hBpair (by omega)
    exact (Fintype.card_coe T) ▸ hcard
  have h := card_mul_le_card_mul (s := (univ : Finset (Fin m))) (t := samples) cond
    (fun i _ => (above i).ge) below
  simpa [hsamples_card, mul_assoc] using h

omit [DecidableEq I] in
/-- Transfer the mixed `(s, r)` inclusion–omission bound directly to interleaved
Reed–Solomon lists over arbitrary fields, injective domains, and widths. -/
theorem list_le_of_inclusion_omission {F : Type*} [Field F] [Nonempty I] (D : I ↪ F)
    (k t width s r B : ℕ) (δ : ℝ) (hts : s + 1 ≤ t)
    (hδ : δ * (Fintype.card I : ℝ) < (Fintype.card I : ℝ) - t + 1)
    (hstrict : (Fintype.card I - s - r) * (k - 1 - s) < (t - s) ^ 2)
    (hbudget : (Fintype.card I).choose s * (Fintype.card I - s).choose r *
        (Fintype.card I - s - r) <
      (B + 1) * (t.choose s * (Fintype.card I - t).choose r)) :
    Lambda (interleavedCodeSet (κ := Fin width) (ReedSolomon.code D k : Set (I → F))) δ ≤ B := by
  classical
  apply interleaved_lambda_le_of_block_bound D k t width B δ hδ
  intro m S hw hp
  have h := (block_inclusion_omission S hts hw hp hstrict).trans_lt hbudget
  by_contra! hm
  exact h.not_ge (Nat.mul_le_mul_right _ hm)

private theorem atErrors_of_inclusion_omission {F : Type*} [Field F]
    (D : Fin 1073741824 ↪ F) (width k e t s r B : ℕ)
    (he : e + t = 1073741824) (hts : s + 1 ≤ t)
    (hstrict : (1073741824 - s - r) * (k - 1 - s) < (t - s) ^ 2)
    (hbudget : (1073741824 : ℕ).choose s * (1073741824 - s).choose r *
        (1073741824 - s - r) <
      (B + 1) * (t.choose s * (1073741824 - t).choose r)) :
    AtErrors D width k e B := by
  apply list_le_of_inclusion_omission D k t width s r B ((e : ℝ) / 1073741824) hts
  · simp only [Fintype.card_fin, Nat.cast_ofNat]
    have hsum : (e : ℝ) + t = 1073741824 := by exact_mod_cast he
    linarith
  · simpa only [Fintype.card_fin] using hstrict
  · simpa only [Fintype.card_fin] using hbudget

/-- Rate `1/16`, first step beyond Johnson (`e = 805,306,371`): pure 1-site inclusion
(`s = 1, r = 0`) certifies list size `≤ 4,294,967,340` (`4.00n`), beating both
`MultipleOmissionJohnson` (`10,725,307,448`) and `CubicHahnJohnson` (`5,010,795,150`). -/
theorem rate_sixteenth_johnson_plus_one {F : Type*} [Field F]
    (D : Fin 1073741824 ↪ F) (width : ℕ) :
    AtErrors D width 67108864 805306371 4294967340 :=
  atErrors_of_inclusion_omission D width 67108864 805306371 268435453 1 0 4294967340
    (by decide) (by decide) (by decide)
    (by simp only [Nat.choose_zero_right, Nat.choose_one_right]; decide)

/-- Rate `1/4`, first step beyond Johnson (`e = 536,870,914`): mixed `(s = 1, r = 3)`
exploits `(2k - 3)² - (4k - 4)(k - 2) = 1 > 0` to certify `≤ 17,179,868,992` (`16.00n`),
half of `MultipleOmissionJohnson`'s `34,359,737,888`. -/
theorem rate_quarter_johnson_plus_one_mixed {F : Type*} [Field F]
    (D : Fin 1073741824 ↪ F) (width : ℕ) :
    AtErrors D width 268435456 536870914 17179868992 :=
  atErrors_of_inclusion_omission D width 268435456 536870914 536870910 1 3 17179868992
    (by decide) (by decide) (by decide)
    (by simp only [Nat.choose_eq_descFactorial_div_factorial]; decide)

omit [DecidableEq I] in
/-- Uniform-in-`n` rate `1/16` (`n = 16k ≥ 64`) single-inclusion bound at `Johnson + 1`:
for arbitrary fields, injective domains, and widths, the list size at `t = 4k - 3`
(`e = 12k + 3`, strictly past Johnson) is at most `5n`. -/
theorem rate_sixteenth_uniform_five_n {F : Type*} [Field F] [Nonempty I] (D : I ↪ F)
    (k width : ℕ) (hn : Fintype.card I = 16 * k) (hk : 4 ≤ k) :
    let n := Fintype.card I
    Lambda (interleavedCodeSet (κ := Fin width) (ReedSolomon.code D k : Set (I → F)))
      (((12 * k + 3 : ℕ) : ℝ) / n) ≤ ((5 * n : ℕ) : ℕ∞) := by
  classical
  dsimp only
  let n := Fintype.card I
  let t := 4 * k - 3
  apply list_le_of_inclusion_omission D k t width 1 0 (5 * n) (((12 * k + 3 : ℕ) : ℝ) / n)
    (by dsimp [t]; omega)
  · have hnr : (0 : ℝ) < n := by
      have : 0 < n := by dsimp [n]; omega
      exact_mod_cast this
    rw [div_mul_cancel₀ _ hnr.ne']
    have hcast : (n : ℝ) = 16 * (k : ℝ) := by exact_mod_cast hn
    have htcast : (t : ℝ) = 4 * (k : ℝ) - 3 := by
      dsimp [t]
      rw [Nat.cast_sub (by omega)]
      push_cast; ring
    push_cast
    linarith
  · change (n - 1 - 0) * (k - 1 - 1) < (t - 1) ^ 2
    have h1 : n - 1 - 0 = 16 * k - 1 := by omega
    have h2 : k - 1 - 1 = k - 2 := by omega
    have h3 : t - 1 = 4 * k - 4 := by dsimp [t]; omega
    rw [h1, h2, h3]
    zify [show 1 ≤ 16 * k by omega, show 2 ≤ k by omega, show 4 ≤ 4 * k by omega]
    nlinarith
  · simp only [Nat.choose_zero_right, Nat.choose_one_right, Nat.sub_zero, mul_one]
    change n * (n - 1) < (5 * n + 1) * t
    have h1 : n = 16 * k := hn
    have h2 : t = 4 * k - 3 := rfl
    rw [h1, h2]
    zify [show 1 ≤ 16 * k by omega, show 3 ≤ 4 * k by omega]
    nlinarith

omit [DecidableEq I] in
/-- Uniform-in-`n` rate `1/4` (`n = 4k ≥ 16`) exact algebraic identity `(2k - 3)² - (4k - 4)(k - 2) = 1`:
mixed `(s = 1, r = 3)` certifies list size `≤ 17n` for all `k ≥ 20` (`n ≥ 80`) at `Johnson + 1`
(`t = 2k - 2`, `e = 2k + 2`), slashing `MultipleOmissionJohnson`'s `32n` nearly in half. -/
theorem rate_quarter_uniform_seventeen_n {F : Type*} [Field F] [Nonempty I] (D : I ↪ F)
    (k width : ℕ) (hn : Fintype.card I = 4 * k) (hk : 20 ≤ k) :
    let n := Fintype.card I
    Lambda (interleavedCodeSet (κ := Fin width) (ReedSolomon.code D k : Set (I → F)))
      (((2 * k + 2 : ℕ) : ℝ) / n) ≤ ((17 * n : ℕ) : ℕ∞) := by
  classical
  dsimp only
  let n := Fintype.card I
  let t := 2 * k - 2
  apply list_le_of_inclusion_omission D k t width 1 3 (17 * n) (((2 * k + 2 : ℕ) : ℝ) / n)
    (by dsimp [t]; omega)
  · have hnr : (0 : ℝ) < n := by
      have : 0 < n := by dsimp [n]; omega
      exact_mod_cast this
    rw [div_mul_cancel₀ _ hnr.ne']
    have hcast : (n : ℝ) = 4 * (k : ℝ) := by exact_mod_cast hn
    have htcast : (t : ℝ) = 2 * (k : ℝ) - 2 := by
      dsimp [t]
      rw [Nat.cast_sub (by omega)]
      push_cast; ring
    push_cast
    linarith
  · change (n - 1 - 3) * (k - 1 - 1) < (t - 1) ^ 2
    have h1 : n - 1 - 3 = 4 * k - 4 := by omega
    have h2 : k - 1 - 1 = k - 2 := by omega
    have h3 : t - 1 = 2 * k - 3 := by dsimp [t]; omega
    rw [h1, h2, h3]
    zify [show 4 ≤ 4 * k by omega, show 2 ≤ k by omega, show 3 ≤ 2 * k by omega]
    nlinarith
  · simp only [Nat.choose_one_right]
    change n * (n - 1).choose 3 * (n - 1 - 3) < (17 * n + 1) * (t * (n - t).choose 3)
    apply Nat.lt_of_mul_lt_mul_left (a := 6)
    have hch1 : 6 * (n - 1).choose 3 = (n - 1) * (n - 2) * (n - 3) := by
      have h := Nat.descFactorial_eq_factorial_mul_choose (n - 1) 3
      rw [show Nat.factorial 3 = 6 by decide, Nat.descFactorial_succ, Nat.descFactorial_succ,
        Nat.descFactorial_one] at h
      have hsub1 : n - 1 - 1 = n - 2 := by omega
      have hsub2 : n - 1 - 2 = n - 3 := by omega
      rw [hsub1, hsub2] at h
      linarith
    have hch2 : 6 * (n - t).choose 3 = (n - t) * (n - t - 1) * (n - t - 2) := by
      have h := Nat.descFactorial_eq_factorial_mul_choose (n - t) 3
      rw [show Nat.factorial 3 = 6 by decide, Nat.descFactorial_succ, Nat.descFactorial_succ,
        Nat.descFactorial_one] at h
      linarith
    have hL : 6 * (n * (n - 1).choose 3 * (n - 1 - 3)) =
        n * ((n - 1) * (n - 2) * (n - 3)) * (n - 4) := by
      have : n - 1 - 3 = n - 4 := by omega
      rw [this, ← hch1]; ring
    have hR : 6 * ((17 * n + 1) * (t * (n - t).choose 3)) =
        (17 * n + 1) * t * ((n - t) * (n - t - 1) * (n - t - 2)) := by
      rw [← hch2]; ring
    rw [hL, hR]
    have hnt : n - t = 2 * k + 2 := by dsimp [t]; omega
    have hnt1 : n - t - 1 = 2 * k + 1 := by omega
    have hnt2 : n - t - 2 = 2 * k := by omega
    have hn' : n = 4 * k := hn
    rw [hnt1, hnt2, hnt, hn']
    have ht' : t = 2 * k - 2 := rfl
    rw [ht']
    zify [show 1 ≤ 4 * k by omega, show 2 ≤ 4 * k by omega, show 3 ≤ 4 * k by omega,
      show 4 ≤ 4 * k by omega, show 2 ≤ 2 * k by omega]
    obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hu : (0 : ℤ) ≤ u := Nat.cast_nonneg _
    push_cast
    apply sub_pos.mp
    ring_nf
    positivity

end ProximityGap.MixedInclusionOmissionJohnson

#print axioms ProximityGap.MixedInclusionOmissionJohnson.block_inclusion_omission
#print axioms ProximityGap.MixedInclusionOmissionJohnson.list_le_of_inclusion_omission
#print axioms ProximityGap.MixedInclusionOmissionJohnson.rate_sixteenth_johnson_plus_one
#print axioms ProximityGap.MixedInclusionOmissionJohnson.rate_quarter_johnson_plus_one_mixed
#print axioms ProximityGap.MixedInclusionOmissionJohnson.rate_sixteenth_uniform_five_n
#print axioms ProximityGap.MixedInclusionOmissionJohnson.rate_quarter_uniform_seventeen_n
