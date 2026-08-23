/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26CharZeroCollisionLaw
import ArkLib.Data.CodingTheory.ProximityGap.KKH26StratifiedSpread

/-!
# The exact KKH26 census in characteristic zero (#357 S1, the counting corollary)

The collision law (`KKH26CharZeroCollisionLaw.sum_eq_iff_freePart_eq`) says subset sums of
`2^k`-th roots of unity collide *only* through antipodal-pair bookkeeping. This file converts
that law into the exact count the S1 unification promised: over any characteristic-zero
field, the number of **distinct** subset-sum values over `r`-subsets of `μ_{2^k}` is

  `#image = ∑_{j ∈ feasSet (2^{k−1}) r}  2^{r−2j} · C(2^{k−1}, r−2j)`   (`card_image_sum`),

— **exactly** the stratified expression of `kkh26_stratified_count`, which is thereby
promoted from a lower bound (over `F_p`, under the prime threshold) to an equality (over
char 0, unconditionally). Since the KKH26 bad scalars are `λ_S = −∑_{a∈S} a`, this is the
exact census of the near-capacity bad-scalar supply for the KKH26 construction class at
infinite characteristic; together with the collision law's surplus verdict, the only
deviation any `F_p` census can exhibit is characteristic arithmetic (`p ∣ N(λ−λ′)`).

## Structure

* `card_afSets` — the antipodal-free count: `μ_{2^k}` splits into `2^{k−1}` antipodal
  classes; antipodal-free `f`-subsets biject with (class set, sign vector) pairs, so there
  are exactly `2^f · C(2^{k−1}, f)` of them (encoder bijection from a sigma set).
* `freePart_realizable` — every `r`-subset's free part is antipodal-free of size `r − 2j`
  with `j ∈ feasSet` (the paired part is a disjoint union of `j` full antipodal classes;
  class accounting via the squaring map `μ_{2^k} → μ_{2^{k−1}}`).
* `exists_subset_with_freePart` — conversely every feasible antipodal-free set is realized
  as a free part (pad with full classes avoiding the used ones).
* `image_sum_eq_biUnion` + `card_image_sum` — the assembly: the image of the sum map is the
  disjoint union of the per-stratum images, each counted exactly by the collision law.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## References

- [KKH26] ePrint 2026/782 Lemma 1; `KKH26StratifiedSpread.lean` (`feasSet`,
  `kkh26_stratified_count`); `KKH26CharZeroCollisionLaw.lean`. Issue #357 (S1).
-/

set_option linter.unusedSectionVars false

open Finset Polynomial BigOperators

namespace ProximityGap.KKH26ExactCensus

open ProximityGap.KKH26CharZeroCollisionLaw
open ArkLib.ProximityGap.KKH26

variable {L : Type*} [Field L] [CharZero L] [DecidableEq L]
variable {k : ℕ} {ζ : L}

/-! ## Setup: the smooth root geometry -/

theorem two_mul_half (hk : 1 ≤ k) : 2 * 2 ^ (k - 1) = 2 ^ k := by
  rw [← pow_succ']
  congr 1
  omega

theorem half_lt (hk : 1 ≤ k) : 2 ^ (k - 1) < 2 ^ k :=
  Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- `ζ^{2^{k−1}} = −1` for a primitive `2^k`-th root. -/
theorem zeta_half_eq_neg_one (hk : 1 ≤ k) (hζ : IsPrimitiveRoot ζ (2 ^ k)) :
    ζ ^ (2 ^ (k - 1)) = -1 := by
  have hsq : (ζ ^ (2 ^ (k - 1))) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, two_mul_half hk, hζ.pow_eq_one]
  have hne : ζ ^ (2 ^ (k - 1)) ≠ 1 :=
    hζ.pow_ne_one_of_pos_of_lt (by positivity) (half_lt hk)
  have hfac : (ζ ^ (2 ^ (k - 1)) - 1) * (ζ ^ (2 ^ (k - 1)) + 1) = 0 := by
    linear_combination hsq
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (by linear_combination h) hne
  · linear_combination h

/-- Negation is the `+2^{k−1}` shift on exponents. -/
theorem neg_pow_shift (hk : 1 ≤ k) (hζ : IsPrimitiveRoot ζ (2 ^ k)) (i : ℕ) :
    -(ζ ^ i) = ζ ^ (i + 2 ^ (k - 1)) := by
  rw [pow_add, zeta_half_eq_neg_one hk hζ]
  ring

theorem zeta_pow_mem (hζ : IsPrimitiveRoot ζ (2 ^ k)) (t : ℕ) :
    ζ ^ t ∈ nthRootsFinset (2 ^ k) (1 : L) := by
  rw [mem_nthRootsFinset (by positivity) (1 : L), ← pow_mul, mul_comm, pow_mul,
    hζ.pow_eq_one, one_pow]

theorem exists_pow_eq (hζ : IsPrimitiveRoot ζ (2 ^ k)) {x : L}
    (hx : x ∈ nthRootsFinset (2 ^ k) (1 : L)) : ∃ t < 2 ^ k, ζ ^ t = x := by
  haveI : NeZero (2 ^ k) := ⟨by positivity⟩
  exact hζ.eq_pow_of_pow_eq_one ((mem_nthRootsFinset (by positivity) (1 : L)).mp hx)

/-- Distinctness of low powers (both exponents below `2^{k−1}`). -/
theorem pow_inj_half (hk : 1 ≤ k) (hζ : IsPrimitiveRoot ζ (2 ^ k)) {i j : ℕ}
    (hi : i < 2 ^ (k - 1)) (hj : j < 2 ^ (k - 1)) (h : ζ ^ i = ζ ^ j) : i = j :=
  hζ.pow_inj (lt_trans hi (half_lt hk)) (lt_trans hj (half_lt hk)) h

/-- A low power is never the negation of a low power. -/
theorem pow_ne_neg_pow (hk : 1 ≤ k) (hζ : IsPrimitiveRoot ζ (2 ^ k)) {i j : ℕ}
    (hi : i < 2 ^ (k - 1)) (hj : j < 2 ^ (k - 1)) : ζ ^ i ≠ -(ζ ^ j) := by
  intro h
  rw [neg_pow_shift hk hζ j] at h
  have hieq := hζ.pow_inj (lt_trans hi (half_lt hk))
    (by rw [← two_mul_half hk]; omega) h
  omega

/-! ## Antipodal-free sets and their count -/

/-- The antipodal-free `f`-subsets of `μ_s`. -/
noncomputable def afSets (s f : ℕ) : Finset (Finset L) :=
  ((nthRootsFinset s (1 : L)).powersetCard f).filter (fun F => ∀ z ∈ F, -z ∉ F)

theorem mem_afSets {s f : ℕ} {F : Finset L} :
    F ∈ afSets (L := L) s f ↔
      (F ⊆ nthRootsFinset s (1 : L) ∧ F.card = f) ∧ ∀ z ∈ F, -z ∉ F := by
  simp [afSets, Finset.mem_powersetCard]

/-- The encoder: a class set `A ⊆ range 2^{k−1}` and a positive-sign subset `B ⊆ A`
produce the antipodal-free set taking `ζ^i` for `i ∈ B` and `−ζ^i` for `i ∈ A \ B`. -/
def encode (ζ : L) (m : ℕ) (p : (_ : Finset ℕ) × Finset ℕ) : Finset L :=
  (p.2.image fun i => ζ ^ i) ∪ ((p.1 \ p.2).image fun i => -(ζ ^ i + 0) + 0)

theorem encode_def (ζ : L) (m : ℕ) (p : (_ : Finset ℕ) × Finset ℕ) :
    encode ζ m p = (p.2.image fun i => ζ ^ i) ∪ ((p.1 \ p.2).image fun i => -(ζ ^ i)) := by
  unfold encode
  congr 1
  apply Finset.image_congr
  intro i _
  ring

theorem mem_encode_pos (hk : 1 ≤ k) (hζ : IsPrimitiveRoot ζ (2 ^ k))
    {A B : Finset ℕ} (hA : A ⊆ Finset.range (2 ^ (k - 1))) (hB : B ⊆ A) {i : ℕ}
    (hi : i < 2 ^ (k - 1)) :
    ζ ^ i ∈ encode ζ (2 ^ (k - 1)) ⟨A, B⟩ ↔ i ∈ B := by
  rw [encode_def, Finset.mem_union]
  constructor
  · rintro (h | h)
    · obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp h
      have hjlt : j < 2 ^ (k - 1) := Finset.mem_range.mp (hA (hB hj))
      rwa [pow_inj_half hk hζ hi hjlt hje.symm]
    · obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp h
      have hjlt : j < 2 ^ (k - 1) :=
        Finset.mem_range.mp (hA (Finset.mem_sdiff.mp hj).1)
      exact absurd hje.symm (pow_ne_neg_pow hk hζ hi hjlt)
  · intro h
    exact Or.inl (Finset.mem_image_of_mem _ h)

theorem mem_encode_neg (hk : 1 ≤ k) (hζ : IsPrimitiveRoot ζ (2 ^ k))
    {A B : Finset ℕ} (hA : A ⊆ Finset.range (2 ^ (k - 1))) (hB : B ⊆ A) {i : ℕ}
    (hi : i < 2 ^ (k - 1)) :
    -(ζ ^ i) ∈ encode ζ (2 ^ (k - 1)) ⟨A, B⟩ ↔ i ∈ A \ B := by
  rw [encode_def, Finset.mem_union]
  constructor
  · rintro (h | h)
    · obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp h
      have hjlt : j < 2 ^ (k - 1) := Finset.mem_range.mp (hA (hB hj))
      exact absurd hje (pow_ne_neg_pow hk hζ hjlt hi)
    · obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp h
      have hjlt : j < 2 ^ (k - 1) :=
        Finset.mem_range.mp (hA (Finset.mem_sdiff.mp hj).1)
      have : ζ ^ j = ζ ^ i := by linear_combination -hje
      rwa [← pow_inj_half hk hζ hjlt hi this]
  · intro h
    exact Or.inr (Finset.mem_image_of_mem _ h)

/-- The encoder lands in the antipodal-free `|A|`-subsets. -/
theorem encode_mem_afSets (hk : 1 ≤ k) (hζ : IsPrimitiveRoot ζ (2 ^ k))
    {A B : Finset ℕ} (hA : A ⊆ Finset.range (2 ^ (k - 1))) (hB : B ⊆ A) :
    encode ζ (2 ^ (k - 1)) ⟨A, B⟩ ∈ afSets (L := L) (2 ^ k) A.card := by
  rw [mem_afSets]
  have hAlt : ∀ i ∈ A, i < 2 ^ (k - 1) := fun i hi => Finset.mem_range.mp (hA hi)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- subset of μ
    intro z hz
    rw [encode_def, Finset.mem_union] at hz
    rcases hz with h | h
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp h
      exact zeta_pow_mem hζ j
    · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp h
      rw [neg_pow_shift hk hζ j]
      exact zeta_pow_mem hζ _
  · -- cardinality
    rw [encode_def]
    have hinj1 : Set.InjOn (fun i => ζ ^ i) ↑B := by
      intro i hi j hj h
      exact pow_inj_half hk hζ (hAlt i (hB (Finset.mem_coe.mp hi)))
        (hAlt j (hB (Finset.mem_coe.mp hj))) h
    have hinj2 : Set.InjOn (fun i => -(ζ ^ i)) ↑(A \ B) := by
      intro i hi j hj h
      have hi' := hAlt i (Finset.mem_sdiff.mp (Finset.mem_coe.mp hi)).1
      have hj' := hAlt j (Finset.mem_sdiff.mp (Finset.mem_coe.mp hj)).1
      exact pow_inj_half hk hζ hi' hj' (by linear_combination -h)
    have hdisj : Disjoint (B.image fun i => ζ ^ i) ((A \ B).image fun i => -(ζ ^ i)) := by
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz1
      obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp hz2
      exact pow_ne_neg_pow hk hζ (hAlt i (hB hi))
        (hAlt j (Finset.mem_sdiff.mp hj).1) hje.symm
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj1,
      Finset.card_image_of_injOn hinj2, ← Finset.card_union_of_disjoint
        Finset.sdiff_disjoint.symm, Finset.union_sdiff_of_subset hB]
  · -- antipodal-free
    intro z hz hneg
    rw [encode_def, Finset.mem_union] at hz
    rcases hz with h | h
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
      have := (mem_encode_neg hk hζ hA hB (hAlt i (hB hi))).mp hneg
      exact absurd hi (Finset.mem_sdiff.mp this).2
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
      have hzz : -(-(ζ ^ i)) = ζ ^ i := neg_neg _
      rw [hzz] at hneg
      have := (mem_encode_pos hk hζ hA hB (hAlt i (Finset.mem_sdiff.mp hi).1)).mp hneg
      exact absurd this (Finset.mem_sdiff.mp hi).2

/-- **The antipodal-free count**: exactly `2^f · C(2^{k−1}, f)` antipodal-free `f`-subsets
of `μ_{2^k}`. -/
theorem card_afSets (hk : 1 ≤ k) (hζ : IsPrimitiveRoot ζ (2 ^ k)) (f : ℕ) :
    (afSets (L := L) (2 ^ k) f).card = 2 ^ f * (2 ^ (k - 1)).choose f := by
  classical
  set m := 2 ^ (k - 1) with hm
  set D : Finset ((_ : Finset ℕ) × Finset ℕ) :=
    ((Finset.range m).powersetCard f).sigma (fun A => A.powerset) with hD
  have hcard : D.card = (2 : ℕ) ^ f * m.choose f := by
    rw [hD, Finset.card_sigma]
    have hterm : ∀ A ∈ (Finset.range m).powersetCard f,
        A.powerset.card = 2 ^ f := by
      intro A hA
      rw [Finset.card_powerset, (Finset.mem_powersetCard.mp hA).2]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_powersetCard,
      Finset.card_range, smul_eq_mul, mul_comm]
  rw [← hcard]
  refine (Finset.card_bij (fun p _ => encode ζ m p) ?_ ?_ ?_).symm
  · -- well-defined into afSets
    rintro ⟨A, B⟩ hp
    rw [hD, Finset.mem_sigma] at hp
    have hA := (Finset.mem_powersetCard.mp hp.1).1
    have hAcard := (Finset.mem_powersetCard.mp hp.1).2
    have hB := Finset.mem_powerset.mp hp.2
    have := encode_mem_afSets hk hζ hA hB
    rwa [hAcard] at this
  · -- injective
    rintro ⟨A, B⟩ hp ⟨A', B'⟩ hp' heq
    rw [hD, Finset.mem_sigma] at hp hp'
    have hA := (Finset.mem_powersetCard.mp hp.1).1
    have hB := Finset.mem_powerset.mp hp.2
    have hA' := (Finset.mem_powersetCard.mp hp'.1).1
    have hB' := Finset.mem_powerset.mp hp'.2
    have heq' : encode ζ m ⟨A, B⟩ = encode ζ m ⟨A', B'⟩ := heq
    have hBB : B = B' := by
      ext i
      constructor
      · intro hi
        have hilt : i < m := Finset.mem_range.mp (hA (hB hi))
        have := (mem_encode_pos hk hζ hA hB hilt).mpr hi
        rw [heq'] at this
        exact (mem_encode_pos hk hζ hA' hB' hilt).mp this
      · intro hi
        have hilt : i < m := Finset.mem_range.mp (hA' (hB' hi))
        have := (mem_encode_pos hk hζ hA' hB' hilt).mpr hi
        rw [← heq'] at this
        exact (mem_encode_pos hk hζ hA hB hilt).mp this
    have hAB : A \ B = A' \ B' := by
      ext i
      constructor
      · intro hi
        have hilt : i < m := Finset.mem_range.mp (hA (Finset.mem_sdiff.mp hi).1)
        have := (mem_encode_neg hk hζ hA hB hilt).mpr hi
        rw [heq'] at this
        exact (mem_encode_neg hk hζ hA' hB' hilt).mp this
      · intro hi
        have hilt : i < m := Finset.mem_range.mp (hA' (Finset.mem_sdiff.mp hi).1)
        have := (mem_encode_neg hk hζ hA' hB' hilt).mpr hi
        rw [← heq'] at this
        exact (mem_encode_neg hk hζ hA hB hilt).mp this
    have hAA : A = A' := by
      have h1 : A = B ∪ (A \ B) := by
        rw [Finset.union_sdiff_of_subset hB]
      have h2 : A' = B' ∪ (A' \ B') := by
        rw [Finset.union_sdiff_of_subset hB']
      rw [h1, h2, hAB, hBB]
    subst hAA
    subst hBB
    rfl
  · -- surjective
    intro F hF
    rw [mem_afSets] at hF
    obtain ⟨⟨hFsub, hFcard⟩, hFaf⟩ := hF
    set B : Finset ℕ := (Finset.range m).filter (fun i => ζ ^ i ∈ F) with hBdef
    set Cc : Finset ℕ := (Finset.range m).filter (fun i => -(ζ ^ i) ∈ F) with hCdef
    have hBC : Disjoint B Cc := by
      rw [Finset.disjoint_left]
      intro i hi hi'
      rw [hBdef, Finset.mem_filter] at hi
      rw [hCdef, Finset.mem_filter] at hi'
      exact hFaf _ hi.2 hi'.2
    -- the two sign-classes partition F
    have hFsplit : F = (B.image fun i => ζ ^ i) ∪ (Cc.image fun i => -(ζ ^ i)) := by
      ext z
      constructor
      · intro hz
        obtain ⟨t, htlt, hte⟩ := exists_pow_eq hζ (hFsub hz)
        rcases lt_or_ge t m with htm | htm
        · refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨t, ?_, hte⟩)
          rw [hBdef, Finset.mem_filter, Finset.mem_range]
          exact ⟨htm, hte ▸ hz⟩
        · have htm2 : t - m + m = t := by omega
          have hneg : z = -(ζ ^ (t - m)) := by
            rw [neg_pow_shift hk hζ (t - m), htm2]
            exact hte.symm
          refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t - m, ?_, hneg.symm⟩)
          rw [hCdef, Finset.mem_filter, Finset.mem_range]
          have htlt2 : t < 2 * m := by
            rw [hm, two_mul_half hk]
            exact htlt
          exact ⟨by omega, hneg ▸ hz⟩
      · intro hz
        rcases Finset.mem_union.mp hz with h | h
        · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
          exact (Finset.mem_filter.mp hi).2
        · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
          exact (Finset.mem_filter.mp hi).2
    have hAfin : B ∪ Cc ⊆ Finset.range m :=
      Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hcardA : (B ∪ Cc).card = f := by
      have hinj1 : Set.InjOn (fun i => ζ ^ i) ↑B := by
        intro i hi j hj h
        exact pow_inj_half hk hζ
          (Finset.mem_range.mp (Finset.mem_of_mem_filter i (Finset.mem_coe.mp hi)))
          (Finset.mem_range.mp (Finset.mem_of_mem_filter j (Finset.mem_coe.mp hj))) h
      have hinj2 : Set.InjOn (fun i => -(ζ ^ i)) ↑Cc := by
        intro i hi j hj h
        exact pow_inj_half hk hζ
          (Finset.mem_range.mp (Finset.mem_of_mem_filter i (Finset.mem_coe.mp hi)))
          (Finset.mem_range.mp (Finset.mem_of_mem_filter j (Finset.mem_coe.mp hj)))
          (by linear_combination -h)
      have hdisj2 : Disjoint (B.image fun i => ζ ^ i) (Cc.image fun i => -(ζ ^ i)) := by
        rw [Finset.disjoint_left]
        intro z hz1 hz2
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz1
        obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp hz2
        exact pow_ne_neg_pow hk hζ
          (Finset.mem_range.mp (Finset.mem_of_mem_filter i hi))
          (Finset.mem_range.mp (Finset.mem_of_mem_filter j hj)) hje.symm
      rw [Finset.card_union_of_disjoint hBC, ← Finset.card_image_of_injOn hinj1,
        ← Finset.card_image_of_injOn hinj2,
        ← Finset.card_union_of_disjoint hdisj2, ← hFsplit, hFcard]
    refine ⟨⟨B ∪ Cc, B⟩, ?_, ?_⟩
    · rw [hD, Finset.mem_sigma]
      constructor
      · exact Finset.mem_powersetCard.mpr ⟨hAfin, hcardA⟩
      · exact Finset.mem_powerset.mpr Finset.subset_union_left
    · -- encode ⟨B ∪ Cc, B⟩ = F
      show encode ζ m ⟨B ∪ Cc, B⟩ = F
      rw [encode_def]
      have hsd : (B ∪ Cc) \ B = Cc := by
        rw [Finset.union_sdiff_cancel_left hBC]
      rw [hsd, ← hFsplit]

/-! ## Realizability of free parts -/

/-- Squaring sends `μ_{2^k}` into `μ_{2^{k−1}}`. -/
theorem sq_mem_half_of_mem (hk : 1 ≤ k) {z : L}
    (hz : z ∈ nthRootsFinset (2 ^ k) (1 : L)) :
    z ^ 2 ∈ nthRootsFinset (2 ^ (k - 1)) (1 : L) := by
  have h2 : (0 : ℕ) < 2 ^ (k - 1) := by positivity
  rw [mem_nthRootsFinset h2 (1 : L), ← pow_mul, two_mul_half hk]
  exact (mem_nthRootsFinset (by positivity) (1 : L)).mp hz

/-- **Forward realizability**: the free part of any `r`-subset of `μ_{2^k}` is an
antipodal-free set of size `r − 2j` for a feasible stratum `j`. -/
theorem freePart_realizable (hk : 1 ≤ k) (hζ : IsPrimitiveRoot ζ (2 ^ k))
    {S : Finset L} (hS : S ⊆ nthRootsFinset (2 ^ k) (1 : L)) {r : ℕ} (hr : S.card = r) :
    ∃ j ∈ feasSet (2 ^ (k - 1)) r,
      freePart S ∈ afSets (L := L) (2 ^ k) (r - 2 * j) := by
  classical
  set F := freePart S with hFdef
  set P := pairedPart S with hPdef
  -- basic structure
  have hsplit : F ∪ P = S := by
    ext z
    simp only [hFdef, hPdef, freePart, pairedPart, Finset.mem_union, Finset.mem_filter]
    by_cases h : -z ∈ S <;> simp [h]
  have hdisj : Disjoint F P := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    rw [hFdef, mem_freePart] at hz
    rw [hPdef, pairedPart, Finset.mem_filter] at hz'
    exact hz.2 hz'.2
  have hFS : F ⊆ S := by
    rw [hFdef, freePart]
    exact Finset.filter_subset _ _
  have hPS : P ⊆ S := by
    rw [hPdef, pairedPart]
    exact Finset.filter_subset _ _
  have hPneg : ∀ z ∈ P, -z ∈ P := by
    intro z hz
    rw [hPdef, pairedPart, Finset.mem_filter] at hz ⊢
    rw [neg_neg]
    exact ⟨hz.2, hz.1⟩
  have hz0 : ∀ z ∈ S, z ≠ 0 := by
    intro z hz h0
    have := (mem_nthRootsFinset (by positivity : (0:ℕ) < 2 ^ k) (1 : L)).mp (hS hz)
    rw [h0, zero_pow (by positivity : (2:ℕ) ^ k ≠ 0)] at this
    exact zero_ne_one this
  have hzneg : ∀ z ∈ S, z ≠ -z := by
    intro z hz h
    have h2z : (2 : L) * z = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2z with h' | h'
    · exact absurd h' two_ne_zero
    · exact hz0 z hz h'
  -- the stratum: number of antipodal classes inside P, via squaring
  set j := (P.image fun z => z ^ 2).card with hjdef
  -- |P| = 2j
  have hPcard : P.card = 2 * j := by
    rw [hjdef]
    rw [Finset.card_eq_sum_card_fiberwise
      (f := fun z => z ^ 2) (t := P.image fun z => z ^ 2)
      (fun z hz => Finset.mem_image_of_mem _ hz)]
    have hfiber : ∀ y ∈ P.image (fun z => z ^ 2),
        (P.filter fun z => z ^ 2 = y).card = 2 := by
      intro y hy
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
      have hfib : P.filter (fun z => z ^ 2 = w ^ 2) = {w, -w} := by
        ext z
        rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hzP, hsq⟩
          have hfac : (z - w) * (z + w) = 0 := by linear_combination hsq
          rcases mul_eq_zero.mp hfac with h | h
          · exact Or.inl (by linear_combination h)
          · exact Or.inr (by linear_combination h)
        · rintro (rfl | rfl)
          · exact ⟨hw, rfl⟩
          · exact ⟨hPneg w hw, by ring⟩
      rw [hfib, Finset.card_insert_of_notMem (by
        rw [Finset.mem_singleton]
        exact hzneg w (hPS hw)), Finset.card_singleton]
    rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul, mul_comm]
  -- F is antipodal-free
  have hFaf : ∀ z ∈ F, -z ∉ F := by
    intro z hz hneg
    rw [hFdef, mem_freePart] at hz hneg
    exact hz.2 hneg.1
  -- class accounting via squares: f + j ≤ 2^{k−1}
  have hsqinjF : Set.InjOn (fun z => z ^ 2) (F : Set L) := by
    intro z hz w hw h
    simp only at h
    have hfac : (z - w) * (z + w) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hfac with h' | h'
    · linear_combination h'
    · exfalso
      have hzw : z = -w := by linear_combination h'
      have hwF := Finset.mem_coe.mp hw
      have hzF := Finset.mem_coe.mp hz
      rw [hzw] at hzF
      exact hFaf w hwF hzF
  have hFimg : (F.image fun z => z ^ 2).card = F.card :=
    Finset.card_image_of_injOn hsqinjF
  have himgdisj : Disjoint (F.image fun z => z ^ 2) (P.image fun z => z ^ 2) := by
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy1
    obtain ⟨w, hw, hwe⟩ := Finset.mem_image.mp hy2
    have hfac : (w - z) * (w + z) = 0 := by linear_combination hwe
    rcases mul_eq_zero.mp hfac with h | h
    · have : w = z := by linear_combination h
      rw [this] at hw
      exact Finset.disjoint_left.mp hdisj hz hw
    · have hwz : w = -z := by linear_combination h
      have := hPneg w hw
      rw [hwz, neg_neg] at this
      exact Finset.disjoint_left.mp hdisj hz this
  have hsub : (F.image fun z => z ^ 2) ∪ (P.image fun z => z ^ 2)
      ⊆ nthRootsFinset (2 ^ (k - 1)) (1 : L) := by
    intro y hy
    rcases Finset.mem_union.mp hy with h | h
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp h
      exact sq_mem_half_of_mem hk (hS (hFS hz))
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp h
      exact sq_mem_half_of_mem hk (hS (hPS hz))
  have hζ2 : IsPrimitiveRoot (ζ ^ 2) (2 ^ (k - 1)) :=
    hζ.pow (by positivity) (two_mul_half hk).symm
  have hclassbound : F.card + j ≤ 2 ^ (k - 1) := by
    have h1 : ((F.image fun z => z ^ 2) ∪ (P.image fun z => z ^ 2)).card
        ≤ (nthRootsFinset (2 ^ (k - 1)) (1 : L)).card :=
      Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint himgdisj, hFimg, hζ2.card_nthRootsFinset] at h1
    rw [hjdef]
    exact h1
  -- the cardinality ledger
  have hcards : F.card + 2 * j = r := by
    rw [← hr, ← hsplit, Finset.card_union_of_disjoint hdisj, hPcard]
  refine ⟨j, ?_, ?_⟩
  · rw [mem_feasSet]
    constructor
    · omega
    · have : r - 2 * j = F.card := by omega
      rw [this]
      omega
  · rw [mem_afSets]
    refine ⟨⟨fun z hz => hS (hFS hz), by omega⟩, hFaf⟩

/-- **Backward realizability**: every antipodal-free set of feasible stratified size is the
free part of an `r`-subset (pad with full antipodal classes avoiding the used ones). -/
theorem exists_subset_with_freePart (hk : 1 ≤ k) (hζ : IsPrimitiveRoot ζ (2 ^ k))
    {r j : ℕ} (hj : j ∈ feasSet (2 ^ (k - 1)) r) {F : Finset L}
    (hF : F ∈ afSets (L := L) (2 ^ k) (r - 2 * j)) :
    ∃ S : Finset L, S ⊆ nthRootsFinset (2 ^ k) (1 : L) ∧ S.card = r ∧ freePart S = F := by
  classical
  set m := 2 ^ (k - 1) with hm
  rw [mem_afSets] at hF
  obtain ⟨⟨hFsub, hFcard⟩, hFaf⟩ := hF
  obtain ⟨h2j, hfeas⟩ := mem_feasSet.mp hj
  -- used classes
  set IF : Finset ℕ := (Finset.range m).filter
    (fun i => ζ ^ i ∈ F ∨ -(ζ ^ i) ∈ F) with hIF
  -- |IF| = |F| (each element of F uses exactly one class)
  set B : Finset ℕ := (Finset.range m).filter (fun i => ζ ^ i ∈ F) with hBdef
  set Cc : Finset ℕ := (Finset.range m).filter (fun i => -(ζ ^ i) ∈ F) with hCdef
  have hBC : Disjoint B Cc := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    rw [hBdef, Finset.mem_filter] at hi
    rw [hCdef, Finset.mem_filter] at hi'
    exact hFaf _ hi.2 hi'.2
  have hIF_eq : IF = B ∪ Cc := by
    rw [hIF, hBdef, hCdef, Finset.filter_or]
  have hFsplit : F = (B.image fun i => ζ ^ i) ∪ (Cc.image fun i => -(ζ ^ i)) := by
    ext z
    constructor
    · intro hz
      obtain ⟨t, htlt, hte⟩ := exists_pow_eq hζ (hFsub hz)
      rcases lt_or_ge t m with htm | htm
      · refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨t, ?_, hte⟩)
        rw [hBdef, Finset.mem_filter, Finset.mem_range]
        exact ⟨htm, hte ▸ hz⟩
      · have htm2 : t - m + m = t := by omega
        have hneg : z = -(ζ ^ (t - m)) := by
          rw [neg_pow_shift hk hζ (t - m), htm2]
          exact hte.symm
        refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨t - m, ?_, hneg.symm⟩)
        rw [hCdef, Finset.mem_filter, Finset.mem_range]
        have htlt2 : t < 2 * m := by
          rw [hm, two_mul_half hk]
          exact htlt
        exact ⟨by omega, hneg ▸ hz⟩
    · intro hz
      rcases Finset.mem_union.mp hz with h | h
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
        exact (Finset.mem_filter.mp hi).2
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
        exact (Finset.mem_filter.mp hi).2
  have hIFcard : IF.card = F.card := by
    have hinj1 : Set.InjOn (fun i => ζ ^ i) (B : Set ℕ) := by
      intro i hi j hj h
      exact pow_inj_half hk hζ
        (Finset.mem_range.mp (Finset.mem_of_mem_filter i (Finset.mem_coe.mp hi)))
        (Finset.mem_range.mp (Finset.mem_of_mem_filter j (Finset.mem_coe.mp hj))) h
    have hinj2 : Set.InjOn (fun i => -(ζ ^ i)) (Cc : Set ℕ) := by
      intro i hi j hj h
      exact pow_inj_half hk hζ
        (Finset.mem_range.mp (Finset.mem_of_mem_filter i (Finset.mem_coe.mp hi)))
        (Finset.mem_range.mp (Finset.mem_of_mem_filter j (Finset.mem_coe.mp hj)))
        (by linear_combination -h)
    have hdisj2 : Disjoint (B.image fun i => ζ ^ i) (Cc.image fun i => -(ζ ^ i)) := by
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz1
      obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp hz2
      exact pow_ne_neg_pow hk hζ
        (Finset.mem_range.mp (Finset.mem_of_mem_filter i hi))
        (Finset.mem_range.mp (Finset.mem_of_mem_filter j hj)) hje.symm
    rw [hIF_eq, Finset.card_union_of_disjoint hBC,
      ← Finset.card_image_of_injOn hinj1, ← Finset.card_image_of_injOn hinj2,
      ← Finset.card_union_of_disjoint hdisj2, ← hFsplit]
  -- pick j fresh classes
  have havail : j ≤ ((Finset.range m) \ IF).card := by
    have h1 : IF ⊆ Finset.range m := Finset.filter_subset _ _
    rw [Finset.card_sdiff_of_subset h1, Finset.card_range, hIFcard, hFcard]
    omega
  obtain ⟨J, hJsub, hJcard⟩ := Finset.exists_subset_card_eq havail
  -- the padded set
  set S : Finset L := F ∪ J.biUnion (fun i => {ζ ^ i, -(ζ ^ i)}) with hSdef
  have hJlt : ∀ i ∈ J, i < m := by
    intro i hi
    exact Finset.mem_range.mp ((Finset.sdiff_subset) (hJsub hi))
  have hJfresh : ∀ i ∈ J, ζ ^ i ∉ F ∧ -(ζ ^ i) ∉ F := by
    intro i hi
    have h := (Finset.mem_sdiff.mp (hJsub hi)).2
    rw [hIF, Finset.mem_filter] at h
    push_neg at h
    exact h (Finset.mem_range.mpr (hJlt i hi))
  have hpairdisj : ∀ i ∈ J, ∀ i' ∈ J, i ≠ i' →
      Disjoint ({ζ ^ i, -(ζ ^ i)} : Finset L) {ζ ^ i', -(ζ ^ i')} := by
    intro i hi i' hi' hne
    rw [Finset.disjoint_left]
    intro z hz hz'
    rw [Finset.mem_insert, Finset.mem_singleton] at hz hz'
    rcases hz with rfl | rfl <;> rcases hz' with h | h
    · exact hne (pow_inj_half hk hζ (hJlt i hi) (hJlt i' hi') h)
    · exact pow_ne_neg_pow hk hζ (hJlt i hi) (hJlt i' hi') h
    · exact pow_ne_neg_pow hk hζ (hJlt i' hi') (hJlt i hi) h.symm
    · exact hne (pow_inj_half hk hζ (hJlt i hi) (hJlt i' hi')
        (by linear_combination -h))
  have hFpadDisj : Disjoint F (J.biUnion (fun i => {ζ ^ i, -(ζ ^ i)})) := by
    rw [Finset.disjoint_right]
    intro z hz hzF
    obtain ⟨i, hi, hzi⟩ := Finset.mem_biUnion.mp hz
    rw [Finset.mem_insert, Finset.mem_singleton] at hzi
    rcases hzi with rfl | rfl
    · exact (hJfresh i hi).1 hzF
    · exact (hJfresh i hi).2 hzF
  have hScard : S.card = r := by
    rw [hSdef, Finset.card_union_of_disjoint hFpadDisj, Finset.card_biUnion hpairdisj]
    have hpair2 : ∀ i ∈ J, ({ζ ^ i, -(ζ ^ i)} : Finset L).card = 2 := by
      intro i hi
      rw [Finset.card_insert_of_notMem, Finset.card_singleton]
      rw [Finset.mem_singleton]
      intro h
      have h2z : (2 : L) * ζ ^ i = 0 := by linear_combination h
      rcases mul_eq_zero.mp h2z with h' | h'
      · exact two_ne_zero h'
      · exact pow_ne_zero i (hζ.ne_zero (by positivity)) h'
    rw [Finset.sum_congr rfl hpair2, Finset.sum_const, hJcard, hFcard, smul_eq_mul]
    omega
  have hSsub : S ⊆ nthRootsFinset (2 ^ k) (1 : L) := by
    intro z hz
    rw [hSdef, Finset.mem_union] at hz
    rcases hz with h | h
    · exact hFsub h
    · obtain ⟨i, hi, hzi⟩ := Finset.mem_biUnion.mp h
      rw [Finset.mem_insert, Finset.mem_singleton] at hzi
      rcases hzi with rfl | rfl
      · exact zeta_pow_mem hζ i
      · rw [neg_pow_shift hk hζ i]
        exact zeta_pow_mem hζ _
  refine ⟨S, hSsub, hScard, ?_⟩
  -- freePart S = F
  ext z
  rw [mem_freePart]
  constructor
  · rintro ⟨hzS, hznS⟩
    rw [hSdef, Finset.mem_union] at hzS
    rcases hzS with h | h
    · exact h
    · exfalso
      obtain ⟨i, hi, hzi⟩ := Finset.mem_biUnion.mp h
      rw [Finset.mem_insert, Finset.mem_singleton] at hzi
      apply hznS
      rw [hSdef, Finset.mem_union]
      refine Or.inr (Finset.mem_biUnion.mpr ⟨i, hi, ?_⟩)
      rw [Finset.mem_insert, Finset.mem_singleton]
      rcases hzi with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl (neg_neg _)
  · intro hzF
    constructor
    · rw [hSdef, Finset.mem_union]
      exact Or.inl hzF
    · intro hcon
      rw [hSdef, Finset.mem_union] at hcon
      rcases hcon with h | h
      · exact hFaf z hzF h
      · obtain ⟨i, hi, hzi⟩ := Finset.mem_biUnion.mp h
        rw [Finset.mem_insert, Finset.mem_singleton] at hzi
        rcases hzi with h' | h'
        · have : z = -(ζ ^ i) := by linear_combination -h'
          rw [this] at hzF
          exact (hJfresh i hi).2 hzF
        · have : z = ζ ^ i := by linear_combination -h'
          rw [this] at hzF
          exact (hJfresh i hi).1 hzF

/-! ## The assembly -/

/-- Subsets of `μ_{2^k}` satisfy the collision-law root hypothesis. -/
theorem roots_hyp {s : Finset L} (hs : s ⊆ nthRootsFinset (2 ^ k) (1 : L)) :
    ∀ z ∈ s, z ^ (2 ^ k) = 1 := fun z hz =>
  (mem_nthRootsFinset (by positivity) (1 : L)).mp (hs hz)

/-- Antipodal-free sets are their own free parts. -/
theorem freePart_eq_self_of_af {F : Finset L} (hF : ∀ z ∈ F, -z ∉ F) :
    freePart F = F := by
  rw [freePart, Finset.filter_eq_self]
  exact hF

/-- **The image decomposition**: the subset-sum image over `r`-subsets is the union over
feasible strata of the antipodal-free per-stratum images. -/
theorem image_sum_eq_biUnion (hk : 1 ≤ k) (hζ : IsPrimitiveRoot ζ (2 ^ k)) (r : ℕ) :
    (((nthRootsFinset (2 ^ k) (1 : L)).powersetCard r).image fun S => ∑ z ∈ S, z)
      = (feasSet (2 ^ (k - 1)) r).biUnion
          (fun j => (afSets (L := L) (2 ^ k) (r - 2 * j)).image fun F => ∑ z ∈ F, z) := by
  ext v
  rw [Finset.mem_image, Finset.mem_biUnion]
  constructor
  · rintro ⟨S, hS, rfl⟩
    obtain ⟨hSsub, hScard⟩ := Finset.mem_powersetCard.mp hS
    obtain ⟨j, hjfeas, hjmem⟩ := freePart_realizable hk hζ hSsub hScard
    exact ⟨j, hjfeas, Finset.mem_image.mpr
      ⟨freePart S, hjmem, (sum_eq_sum_freePart S).symm⟩⟩
  · rintro ⟨j, hjfeas, hvmem⟩
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hvmem
    obtain ⟨S, hSsub, hScard, hSfree⟩ := exists_subset_with_freePart hk hζ hjfeas hF
    have hmem := Finset.mem_image_of_mem (fun S : Finset L => ∑ z ∈ S, z)
      (Finset.mem_powersetCard.mpr ⟨hSsub, hScard⟩)
    simp only at hmem
    rw [sum_eq_sum_freePart S, hSfree] at hmem
    exact Finset.mem_image.mp hmem

/-- **THE EXACT CENSUS (S1 counting corollary).** Over any characteristic-zero field, the
number of distinct subset-sum values over `r`-subsets of `μ_{2^k}` is exactly the
stratified count:

  `#image = ∑_{j ∈ feasSet(2^{k−1}, r)} 2^{r−2j} · C(2^{k−1}, r−2j)`.

This is the expression of `kkh26_stratified_count` with `≤` upgraded to `=` — the
characteristic-zero KKH26 bad-scalar census is exactly the stratified antipodal count, and
any `F_p` deviation is characteristic arithmetic. -/
theorem card_image_sum (hk : 1 ≤ k) (hζ : IsPrimitiveRoot ζ (2 ^ k)) (r : ℕ) :
    ((((nthRootsFinset (2 ^ k) (1 : L)).powersetCard r).image
        fun S => ∑ z ∈ S, z)).card
      = ∑ j ∈ feasSet (2 ^ (k - 1)) r,
          2 ^ (r - 2 * j) * (2 ^ (k - 1)).choose (r - 2 * j) := by
  classical
  rw [image_sum_eq_biUnion hk hζ r]
  rw [Finset.card_biUnion]
  · -- per-stratum counts
    apply Finset.sum_congr rfl
    intro j hj
    rw [← card_afSets hk hζ (r - 2 * j)]
    have hinj : Set.InjOn (fun F : Finset L => ∑ z ∈ F, z)
        ↑(afSets (L := L) (2 ^ k) (r - 2 * j)) := by
      intro F hF F' hF' hsum
      have hsum' : ∑ z ∈ F, z = ∑ z ∈ F', z := hsum
      rw [Finset.mem_coe, mem_afSets] at hF hF'
      have h := (sum_eq_iff_freePart_eq hk (roots_hyp hF.1.1) (roots_hyp hF'.1.1)).mp hsum'
      rwa [freePart_eq_self_of_af hF.2, freePart_eq_self_of_af hF'.2] at h
    exact Finset.card_image_of_injOn hinj
  · -- cross-stratum disjointness
    intro j hj j' hj' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    rintro v hv hv'
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨F', hF', hsum⟩ := Finset.mem_image.mp hv'
    rw [mem_afSets] at hF hF'
    have h := (sum_eq_iff_freePart_eq hk (roots_hyp hF'.1.1) (roots_hyp hF.1.1)).mp hsum
    rw [freePart_eq_self_of_af hF'.2, freePart_eq_self_of_af hF.2] at h
    have hc : r - 2 * j = r - 2 * j' := by
      rw [← hF.1.2, ← hF'.1.2, h]
    obtain ⟨h2j, -⟩ := mem_feasSet.mp (Finset.mem_coe.mp hj)
    obtain ⟨h2j', -⟩ := mem_feasSet.mp (Finset.mem_coe.mp hj')
    exact hne (by omega)

/-- Data-set form of `card_image_sum`: in characteristic zero, the subset-sum census is
exactly the cardinality of the existing stratified signed-data index set. -/
theorem card_image_sum_eq_card_stratData (hk : 1 ≤ k)
    (hζ : IsPrimitiveRoot ζ (2 ^ k)) (r : ℕ) :
    ((((nthRootsFinset (2 ^ k) (1 : L)).powersetCard r).image
        fun S => ∑ z ∈ S, z)).card
      = (stratData (2 ^ (k - 1)) r).card := by
  rw [card_image_sum hk hζ r, card_stratData]

/-! ## Source audit -/

#print axioms card_afSets
#print axioms freePart_realizable
#print axioms exists_subset_with_freePart
#print axioms image_sum_eq_biUnion
#print axioms card_image_sum
#print axioms card_image_sum_eq_card_stratData

end ProximityGap.KKH26ExactCensus
