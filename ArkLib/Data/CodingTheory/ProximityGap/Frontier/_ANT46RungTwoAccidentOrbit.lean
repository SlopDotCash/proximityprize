/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapePrimeP30
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapePrimeP30Second

/-!
# Rung-two reduction accidents occur in packets of at least four

For a negation-closed finite multiplicative subgroup `H` of a field, consider normalized
additive-energy solutions

```text
a + b = c + 1,    a,b,c in H.
```

The three characteristic-zero (Mann) families are `a = 1`, `b = 1`, and
`c = -1, b = -a`.  A solution outside their union is called an accident.

The signed zero-sum quadruple `(a,b,-c,-1)` admits a cyclic re-rooting.  After normalizing
the next entry to `-1`, this gives

```text
tau(a,b,c) = (-b/a, c/a, -1/a).
```

On accidents, `tau` has exact order four: a fixed point forces `a = 1` or `b = 1`, while a
fixed point of `tau^2` forces a Mann family (in odd characteristic).  Consequently every
nonempty accident set contains four distinct elements.

This is a direct consumer for G136's production equivalence
`rung2 anchor <-> #accidents <= 3`: the tolerance `<= 3` is equivalent to *no accidents*.
It does not prove that the certified production prime is accident-free; it sharpens the remaining
arithmetic obligation from a count to an emptiness/resultant certificate.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace ArkLib.ProximityGap.Frontier.ANT46RungTwoAccidentOrbit

open Finset

variable {F : Type*} [Field F] [DecidableEq F]

/-- A normalized additive-energy triple. -/
structure Triple (F : Type*) where
  a : F
  b : F
  c : F
deriving DecidableEq

/-- The normalized additive-energy equation `a + b = c + 1`. -/
def IsSolution (x : Triple F) : Prop := x.a + x.b = x.c + 1

/-- The union of the three normalized characteristic-zero Mann families. -/
def IsLawful (x : Triple F) : Prop :=
  x.a = 1 ∨ x.b = 1 ∨ (x.c = -1 ∧ x.b = -x.a)

/-- A reduction accident: a normalized solution outside all three Mann families. -/
def IsAccident (x : Triple F) : Prop := IsSolution x ∧ ¬ IsLawful x

/-- All normalized accidents supported on `H`. -/
noncomputable def accidents (H : Finset F) : Finset (Triple F) := by
  classical
  exact (((H ×ˢ H) ×ˢ H).image
    (fun x => Triple.mk x.1.1 x.1.2 x.2)).filter IsAccident

/-- Cyclically re-root the signed zero-sum quadruple `(a,b,-c,-1)`. -/
def step (x : Triple F) : Triple F :=
  ⟨-x.b / x.a, x.c / x.a, -1 / x.a⟩

@[simp] theorem step_a (x : Triple F) : (step x).a = -x.b / x.a := rfl
@[simp] theorem step_b (x : Triple F) : (step x).b = x.c / x.a := rfl
@[simp] theorem step_c (x : Triple F) : (step x).c = -1 / x.a := rfl

/-- Re-rooting preserves the additive equation whenever the normalizing entry is nonzero. -/
theorem isSolution_step_iff (x : Triple F) (ha : x.a ≠ 0) :
    IsSolution (step x) ↔ IsSolution x := by
  change -x.b / x.a + x.c / x.a = -1 / x.a + 1 ↔
    x.a + x.b = x.c + 1
  constructor
  · intro h
    field_simp [ha] at h
    linear_combination -h
  · intro h
    field_simp [ha]
    linear_combination -h

/-- A lawful re-rooting came from a lawful triple. -/
theorem lawful_of_step_lawful (x : Triple F) (ha : x.a ≠ 0)
    (hsol : IsSolution x) (h : IsLawful (step x)) : IsLawful x := by
  unfold IsLawful at h ⊢
  rcases h with hA | hB | hC
  · right; right
    have hab : x.b = -x.a := by
      have hab' : -x.b = x.a := by
        simpa using (div_eq_iff ha).mp hA
      simpa using congrArg Neg.neg hab'
    constructor
    · unfold IsSolution at hsol
      rw [hab] at hsol
      have hzero : x.c + 1 = 0 := by simpa using hsol.symm
      exact eq_neg_of_add_eq_zero_left hzero
    · exact hab
  · right; left
    have hac : x.c = x.a := by
      simpa using (div_eq_iff ha).mp hB
    unfold IsSolution at hsol
    rw [hac] at hsol
    linear_combination hsol
  · left
    rcases hC with ⟨hC, _⟩
    have hC' : (-1 : F) = -1 * x.a := (div_eq_iff ha).mp hC
    simpa using hC'.symm

/-- Re-rooting preserves accidents. -/
theorem isAccident_step (x : Triple F) (ha : x.a ≠ 0) (hx : IsAccident x) :
    IsAccident (step x) := by
  refine ⟨(isSolution_step_iff x ha).2 hx.1, ?_⟩
  intro h
  exact hx.2 (lawful_of_step_lawful x ha hx.1 h)

/-- Closed formula for two re-rooting steps. -/
theorem step_step (x : Triple F) (ha : x.a ≠ 0) (hb : x.b ≠ 0) :
    step (step x) = ⟨x.c / x.b, 1 / x.b, x.a / x.b⟩ := by
  cases x with
  | mk a b c =>
      simp only [step]
      congr 1 <;> field_simp [ha, hb]

/-- Four re-rooting steps return to the original triple. -/
theorem step_four (x : Triple F) (ha : x.a ≠ 0) (hb : x.b ≠ 0) (hc : x.c ≠ 0) :
    step (step (step (step x))) = x := by
  cases x with
  | mk a b c =>
      simp only [step]
      congr 1 <;> field_simp [ha, hb, hc]

/-- No accident is fixed by one re-rooting step. -/
theorem step_ne_self_of_accident (x : Triple F) (ha : x.a ≠ 0) (hx : IsAccident x) :
    step x ≠ x := by
  rcases hx with ⟨hsol, hnlaw⟩
  intro h
  have hA : -x.b / x.a = x.a := by simpa [step] using congrArg Triple.a h
  have hB : x.c / x.a = x.b := by simpa [step] using congrArg Triple.b h
  have hab : x.c = x.a * x.b := by
    field_simp [ha] at hB
    linear_combination hB
  have hone : (x.a - 1) * (x.b - 1) = 0 := by
    unfold IsSolution at hsol
    rw [hab] at hsol
    linear_combination -hsol
  rcases mul_eq_zero.mp hone with h1 | h1
  · apply hnlaw
    left
    linear_combination h1
  · apply hnlaw
    right; left
    linear_combination h1

/-- No accident is fixed by two re-rooting steps (odd-characteristic input `2 != 0`). -/
theorem step_step_ne_self_of_accident (x : Triple F) (ha : x.a ≠ 0) (hb : x.b ≠ 0)
    (h2 : (2 : F) ≠ 0) (hx : IsAccident x) : step (step x) ≠ x := by
  rcases hx with ⟨hsol, hnlaw⟩
  intro h
  rw [step_step x ha hb] at h
  have hB : 1 / x.b = x.b := congrArg Triple.b h
  have hbSq : x.b ^ 2 = 1 := by
    field_simp [hb] at hB
    simpa [pow_two] using hB.symm
  have hbCases : x.b = 1 ∨ x.b = -1 := (sq_eq_one_iff).mp hbSq
  rcases hbCases with hb1 | hbm1
  · exact hnlaw (Or.inr (Or.inl hb1))
  · have hA : x.c / x.b = x.a := congrArg Triple.a h
    have hca : x.c = -x.a := by
      have hA' : x.c = x.a * x.b := (div_eq_iff hb).mp hA
      rw [hbm1] at hA'
      simpa using hA'
    have ha1 : x.a = 1 := by
      unfold IsSolution at hsol
      rw [hbm1, hca] at hsol
      apply (mul_left_cancel₀ h2)
      linear_combination hsol
    exact hnlaw (Or.inl ha1)

/-- Membership in the supporting triple product. -/
theorem mem_support_iff {H : Finset F} {x : Triple F} :
    x ∈ ((H ×ˢ H) ×ˢ H).image
        (fun y => Triple.mk y.1.1 y.1.2 y.2) ↔
      x.a ∈ H ∧ x.b ∈ H ∧ x.c ∈ H := by
  classical
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simp only [Finset.mem_product] at hy
    rcases hy with ⟨⟨ha, hb⟩, hc⟩
    exact ⟨ha, hb, hc⟩
  · rintro ⟨ha, hb, hc⟩
    refine Finset.mem_image.mpr ⟨((x.a, x.b), x.c), by simp [ha, hb, hc], ?_⟩
    cases x
    rfl

theorem mem_accidents_iff {H : Finset F} {x : Triple F} :
    x ∈ accidents H ↔ x.a ∈ H ∧ x.b ∈ H ∧ x.c ∈ H ∧ IsAccident x := by
  classical
  unfold accidents
  rw [Finset.mem_filter]
  rw [mem_support_iff]
  tauto

/-- Re-rooting preserves the concrete accident Finset under subgroup closure. -/
theorem step_mem_accidents {H : Finset F}
    (hneg : ∀ x ∈ H, -x ∈ H)
    (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H)
    (hinv : ∀ x ∈ H, x⁻¹ ∈ H)
    (h0 : (0 : F) ∉ H) {x : Triple F} (hx : x ∈ accidents H) :
    step x ∈ accidents H := by
  rw [mem_accidents_iff] at hx ⊢
  rcases hx with ⟨ha, hb, hc, hacc⟩
  have ha0 : x.a ≠ 0 := fun h => h0 (h ▸ ha)
  refine ⟨?_, ?_, ?_, isAccident_step x ha0 hacc⟩
  · simpa [step, div_eq_mul_inv] using hmul _ (hneg _ hb) _ (hinv _ ha)
  · simpa [step, div_eq_mul_inv] using hmul _ hc _ (hinv _ ha)
  · have hone : (1 : F) ∈ H := by
      rw [← mul_inv_cancel₀ ha0]
      exact hmul _ ha _ (hinv _ ha)
    simpa [step, div_eq_mul_inv] using hmul _ (hneg _ hone) _ (hinv _ ha)

/-! The last membership proof above is deliberately stated from the closure axioms only.  The
`-1` membership needed for `-a⁻¹` follows from negation closure applied to `1`; deriving `1 ∈ H`
from an existing `a ∈ H` uses `a*a⁻¹=1`. -/

/-- Four distinct accidents generated from any one accident. -/
theorem four_le_card_accidents_of_nonempty {H : Finset F}
    (hneg : ∀ x ∈ H, -x ∈ H)
    (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H)
    (hinv : ∀ x ∈ H, x⁻¹ ∈ H)
    (h0 : (0 : F) ∉ H) (h2 : (2 : F) ≠ 0)
    (hne : (accidents H).Nonempty) : 4 ≤ (accidents H).card := by
  classical
  obtain ⟨x, hx⟩ := hne
  have hx1 := step_mem_accidents hneg hmul hinv h0 hx
  have hx2 := step_mem_accidents hneg hmul hinv h0 hx1
  have hx3 := step_mem_accidents hneg hmul hinv h0 hx2
  rw [mem_accidents_iff] at hx
  have ha0 : x.a ≠ 0 := fun h => h0 (h ▸ hx.1)
  have hb0 : x.b ≠ 0 := fun h => h0 (h ▸ hx.2.1)
  have hc0 : x.c ≠ 0 := fun h => h0 (h ▸ hx.2.2.1)
  have h01 : x ≠ step x := (step_ne_self_of_accident x ha0 hx.2.2.2).symm
  have h02 : x ≠ step (step x) :=
    (step_step_ne_self_of_accident x ha0 hb0 h2 hx.2.2.2).symm
  have h12 : step x ≠ step (step x) := by
    rw [mem_accidents_iff] at hx1
    exact (step_ne_self_of_accident (step x)
      (fun h => h0 (h ▸ hx1.1)) hx1.2.2.2).symm
  have h23 : step (step x) ≠ step (step (step x)) := by
    rw [mem_accidents_iff] at hx2
    exact (step_ne_self_of_accident (step (step x))
      (fun h => h0 (h ▸ hx2.1)) hx2.2.2.2).symm
  have h30 : step (step (step x)) ≠ x := by
    intro h
    have := congrArg step h
    rw [step_four x ha0 hb0 hc0] at this
    exact h01 this
  have h13 : step x ≠ step (step (step x)) := by
    intro h
    have := congrArg step h
    rw [step_four x ha0 hb0 hc0] at this
    exact h02 this.symm
  let Q : Finset (Triple F) :=
    {x, step x, step (step x), step (step (step x))}
  have hQsub : Q ⊆ accidents H := by
    intro y hy
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact (mem_accidents_iff.mpr hx)
    · exact hx1
    · exact hx2
    · exact hx3
  have hQcard : Q.card = 4 := by
    simp only [Q]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa only [Finset.mem_singleton]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h12, h13⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h01, h02, h30.symm⟩
  rw [← hQcard]
  exact Finset.card_le_card hQsub

/-- The G136 production tolerance `#accidents <= 3` is exactly accident-freeness. -/
theorem card_accidents_le_three_iff_eq_zero {H : Finset F}
    (hneg : ∀ x ∈ H, -x ∈ H)
    (hmul : ∀ x ∈ H, ∀ y ∈ H, x * y ∈ H)
    (hinv : ∀ x ∈ H, x⁻¹ ∈ H)
    (h0 : (0 : F) ∉ H) (h2 : (2 : F) ≠ 0) :
    (accidents H).card ≤ 3 ↔ (accidents H).card = 0 := by
  constructor
  · intro hle
    by_contra hne
    have hpos : (accidents H).Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
    have hfour := four_le_card_accidents_of_nonempty hneg hmul hinv h0 h2 hpos
    omega
  · intro h
    omega

/-! ## Triple-equal projective stratum -/

/-- Three equal entries in the signed quadruple `(a,b,-c,-1)`. The four disjuncts record
which entry is omitted. -/
def HasTripleEqualSigned (x : Triple F) : Prop :=
  (x.a = x.b ∧ x.b = -x.c) ∨
  (x.a = x.b ∧ x.b = -1) ∨
  (x.a = -x.c ∧ -x.c = -1) ∨
  (x.b = -x.c ∧ -x.c = -1)

/-- A triple-equal signed accident forces `-3` into its supporting multiplicative subgroup.
Indeed, if three entries are `r`, the fourth is `-3r`. -/
theorem neg_three_mem_of_tripleEqual_accident {H : Finset F}
    (hneg : ∀ z ∈ H, -z ∈ H)
    (hmul : ∀ z ∈ H, ∀ w ∈ H, z * w ∈ H)
    (hinv : ∀ z ∈ H, z⁻¹ ∈ H)
    (h0 : (0 : F) ∉ H) {x : Triple F}
    (hx : x ∈ accidents H) (htriple : HasTripleEqualSigned x) :
    (-3 : F) ∈ H := by
  rw [mem_accidents_iff] at hx
  rcases hx with ⟨ha, hb, hc, hsol, _⟩
  have ha0 : x.a ≠ 0 := fun h => h0 (h ▸ ha)
  have hone : (1 : F) ∈ H := by
    rw [← mul_inv_cancel₀ ha0]
    exact hmul _ ha _ (hinv _ ha)
  rcases htriple with h012 | h013 | h023 | h123
  · rcases h012 with ⟨hab, hbc⟩
    have hba : x.b = x.a := hab.symm
    have hca : x.c = -x.a := by linear_combination hbc + hab
    have h3a : 3 * x.a = 1 := by
      unfold IsSolution at hsol
      rw [hba, hca] at hsol
      linear_combination hsol
    have heq : (-3 : F) = (-1) * x.a⁻¹ := by
      field_simp [ha0]
      linear_combination -h3a
    rw [heq]
    exact hmul _ (hneg _ hone) _ (hinv _ ha)
  · rcases h013 with ⟨hab, hb1⟩
    have ha1 : x.a = -1 := hab.trans hb1
    have hc3 : x.c = -3 := by
      unfold IsSolution at hsol
      rw [ha1, hb1] at hsol
      linear_combination -hsol
    rwa [← hc3]
  · rcases h023 with ⟨hac, hc1⟩
    have ha1 : x.a = -1 := hac.trans hc1
    have hcpos : x.c = 1 := by linear_combination -hc1
    have hb3 : x.b = 3 := by
      unfold IsSolution at hsol
      rw [ha1, hcpos] at hsol
      linear_combination hsol
    simpa [hb3] using hneg _ hb
  · rcases h123 with ⟨hbc, hc1⟩
    have hb1 : x.b = -1 := hbc.trans hc1
    have hcpos : x.c = 1 := by linear_combination -hc1
    have ha3 : x.a = 3 := by
      unfold IsSolution at hsol
      rw [hb1, hcpos] at hsol
      linear_combination hsol
    simpa [ha3] using hneg _ ha

/-- If `-3` is absent from the subgroup, no supported accident has a triple-equal signed
quadruple. -/
theorem not_tripleEqual_of_neg_three_notMem {H : Finset F}
    (hneg : ∀ z ∈ H, -z ∈ H)
    (hmul : ∀ z ∈ H, ∀ w ∈ H, z * w ∈ H)
    (hinv : ∀ z ∈ H, z⁻¹ ∈ H)
    (h0 : (0 : F) ∉ H) (h3 : (-3 : F) ∉ H)
    {x : Triple F} (hx : x ∈ accidents H) :
    ¬ HasTripleEqualSigned x := by
  intro htriple
  exact h3 (neg_three_mem_of_tripleEqual_accident hneg hmul hinv h0 hx htriple)

/-! ## Kernel-cheap certificate at the first production prime -/

private def binaryPowAux {M : Type*} [Monoid M] (a : M) (n : ℕ) : ℕ → M
  | 0 => 1
  | fuel + 1 =>
      if n = 0 then 1
      else if n % 2 = 0 then binaryPowAux (a * a) (n / 2) fuel
      else a * binaryPowAux (a * a) (n / 2) fuel

private def binaryPow {M : Type*} [Monoid M] (a : M) (n : ℕ) : M :=
  binaryPowAux a n (n + 1)

private theorem binaryPowAux_eq_pow {M : Type*} [Monoid M] (a : M) (n fuel : ℕ)
    (hnfuel : n < fuel) : binaryPowAux a n fuel = a ^ n := by
  induction fuel generalizing a n with
  | zero => omega
  | succ fuel ih =>
      rw [binaryPowAux]
      split_ifs with h0 heven
      · subst n
        simp
      · have hnpos : 0 < n := Nat.pos_of_ne_zero h0
        have hhalf : n / 2 < fuel :=
          (Nat.div_lt_self hnpos (by norm_num)).trans_le (by omega)
        rw [ih (a * a) (n / 2) hhalf, ← pow_two, ← pow_mul]
        have hdvd : 2 ∣ n := (Nat.dvd_iff_mod_eq_zero).2 heven
        have htwo : 2 * (n / 2) = n := Nat.mul_div_cancel' hdvd
        congr 1
      · have hnpos : 0 < n := Nat.pos_of_ne_zero h0
        have hhalf : n / 2 < fuel :=
          (Nat.div_lt_self hnpos (by norm_num)).trans_le (by omega)
        rw [ih (a * a) (n / 2) hhalf, ← pow_two, ← pow_mul, ← pow_succ']
        have hnmod : n % 2 = 1 := by omega
        have hdecomp := Nat.mod_add_div n 2
        congr 1
        omega

private theorem binaryPow_eq_pow {M : Type*} [Monoid M] (a : M) (n : ℕ) :
    binaryPow a n = a ^ n := by
  exact binaryPowAux_eq_pow a n (n + 1) (by omega)

open ArkLib.ProximityGap.PrizeShapePrimeP30

local instance firstPrimeFact : Fact (Nat.Prime P) := ⟨prime_P⟩

/-- Exact residue certificate: `-3` is not a `2^30`-th root of unity in the first certified
production field. -/
theorem firstPrime_neg_three_pow_ne_one :
    ((-3 : ZMod P) ^ (2 ^ 30 : ℕ)) ≠ 1 := by
  rw [← binaryPow_eq_pow]
  decide

/-- Production specialization. Any multiplicative support in the first certified field whose
elements are `2^30`-th roots of unity has no triple-equal signed accident.  G136's concrete
`rootsFinset g (2^30)` supplies the final `hpow` premise directly from `orderOf_g`. -/
theorem firstPrime_no_tripleEqual_accident {H : Finset (ZMod P)}
    (hneg : ∀ z ∈ H, -z ∈ H)
    (hmul : ∀ z ∈ H, ∀ w ∈ H, z * w ∈ H)
    (hinv : ∀ z ∈ H, z⁻¹ ∈ H)
    (h0 : (0 : ZMod P) ∉ H)
    (hpow : ∀ z ∈ H, z ^ (2 ^ 30 : ℕ) = 1)
    {x : Triple (ZMod P)} (hx : x ∈ accidents H) :
    ¬ HasTripleEqualSigned x := by
  have h3 : (-3 : ZMod P) ∉ H := by
    intro hmem
    exact firstPrime_neg_three_pow_ne_one (hpow _ hmem)
  exact not_tripleEqual_of_neg_three_notMem hneg hmul hinv h0 h3 hx

/-! The second certified endpoint has the same exclusion, although `-3` is a quadratic
residue there; the direct `2^30`-th-power certificate is therefore the right invariant. -/

local instance secondPrimeFact :
    Fact (Nat.Prime ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) :=
  ⟨ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P⟩

theorem secondPrime_neg_three_pow_ne_one :
    ((-3 : ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) ^
      (2 ^ 30 : ℕ)) ≠ 1 := by
  rw [← binaryPow_eq_pow]
  decide

/-- Second-production-prime version of `firstPrime_no_tripleEqual_accident`. -/
theorem secondPrime_no_tripleEqual_accident
    {H : Finset (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)}
    (hneg : ∀ z ∈ H, -z ∈ H)
    (hmul : ∀ z ∈ H, ∀ w ∈ H, z * w ∈ H)
    (hinv : ∀ z ∈ H, z⁻¹ ∈ H)
    (h0 : (0 : ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) ∉ H)
    (hpow : ∀ z ∈ H, z ^ (2 ^ 30 : ℕ) = 1)
    {x : Triple (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)}
    (hx : x ∈ accidents H) : ¬ HasTripleEqualSigned x := by
  have h3 :
      (-3 : ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) ∉ H := by
    intro hmem
    exact secondPrime_neg_three_pow_ne_one (hpow _ hmem)
  exact not_tripleEqual_of_neg_three_notMem hneg hmul hinv h0 h3 hx

end ArkLib.ProximityGap.Frontier.ANT46RungTwoAccidentOrbit

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.ANT46RungTwoAccidentOrbit.step_four
#print axioms ArkLib.ProximityGap.Frontier.ANT46RungTwoAccidentOrbit.four_le_card_accidents_of_nonempty
#print axioms ArkLib.ProximityGap.Frontier.ANT46RungTwoAccidentOrbit.card_accidents_le_three_iff_eq_zero
#print axioms ArkLib.ProximityGap.Frontier.ANT46RungTwoAccidentOrbit.neg_three_mem_of_tripleEqual_accident
#print axioms ArkLib.ProximityGap.Frontier.ANT46RungTwoAccidentOrbit.firstPrime_neg_three_pow_ne_one
#print axioms ArkLib.ProximityGap.Frontier.ANT46RungTwoAccidentOrbit.firstPrime_no_tripleEqual_accident
#print axioms ArkLib.ProximityGap.Frontier.ANT46RungTwoAccidentOrbit.secondPrime_neg_three_pow_ne_one
#print axioms ArkLib.ProximityGap.Frontier.ANT46RungTwoAccidentOrbit.secondPrime_no_tripleEqual_accident
