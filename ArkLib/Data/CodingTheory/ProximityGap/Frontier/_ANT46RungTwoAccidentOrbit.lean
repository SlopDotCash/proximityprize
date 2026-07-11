/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapePrimeP30
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapePrimeP30Second

/-!
# Rung-two reduction accidents: cyclic packets and the full projective `S₄` classifier

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

The second half of this file upgrades the cyclic action to all 24 coordinate permutations.
It first closes a subtle scalar-symmetry seam: for a general nonzero zero-sum quadruple,
projectively equal permutations need not literally preserve coordinate values.  For an
odd-characteristic accident, however, a nontrivial common scalar has fourth power one and forces
a signed coordinate to equal `1`, hence a lawful Mann family.  Therefore the identity fibre is
exactly the value-preserving stabilizer.  Equality partitions `1+1+1+1`, `2+1+1`, and `3+1`
give fibre sizes `1`, `2`, and `6`, and orbit sizes `24`, `12`, and `4`; the `2+2` and `4`
patterns are lawful.  The production `-3` certificate excludes `3+1`, so production accidents
partition into 12- or 24-element packets and their total number is divisible by 12.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option linter.style.longFile 2100

namespace ArkLib.ProximityGap.Frontier.ANT46RungTwoAccidentOrbit

open Finset

variable {F : Type*} [Field F] [DecidableEq F]

/-- A normalized additive-energy triple. -/
structure Triple (F : Type*) where
  a : F
  b : F
  c : F
deriving DecidableEq

@[ext] theorem Triple.ext' {x y : Triple F} (ha : x.a = y.a) (hb : x.b = y.b)
    (hc : x.c = y.c) : x = y := by
  cases x
  cases y
  simp_all

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

/-- The signed zero-sum quadruple attached to a normalized solution. -/
def signed (x : Triple F) : Fin 4 → F := ![x.a, x.b, -x.c, -1]

@[simp] theorem signed_zero (x : Triple F) : signed x 0 = x.a := rfl
@[simp] theorem signed_one (x : Triple F) : signed x 1 = x.b := rfl
@[simp] theorem signed_two (x : Triple F) : signed x 2 = -x.c := rfl
@[simp] theorem signed_three (x : Triple F) : signed x 3 = -1 := rfl

/-- Normalize a coordinate permutation of the signed quadruple back to last entry `-1`. -/
def reRoot (sigma : Equiv.Perm (Fin 4)) (x : Triple F) : Triple F :=
  let q := signed x
  ⟨-q (sigma 0) / q (sigma 3),
    -q (sigma 1) / q (sigma 3),
    q (sigma 2) / q (sigma 3)⟩

/-- The signed tuple of a re-rooting is the permuted tuple scaled by the common nonzero
normalization factor. -/
theorem signed_reRoot (x : Triple F) (sigma : Equiv.Perm (Fin 4))
    (hden : signed x (sigma 3) ≠ 0) (i : Fin 4) :
    signed (reRoot sigma x) i = -signed x (sigma i) / signed x (sigma 3) := by
  fin_cases i <;> simp [reRoot, hden] <;> ring

/-- The signed entries of a supported accident are all nonzero. -/
theorem signed_ne_zero_of_mem_accidents {H : Finset F} (h0 : (0 : F) ∉ H)
    {x : Triple F} (hx : x ∈ accidents H) (i : Fin 4) : signed x i ≠ 0 := by
  rw [mem_accidents_iff] at hx
  fin_cases i <;> simp [signed] <;>
    intro h <;> first | exact h0 (h ▸ hx.1) | exact h0 (h ▸ hx.2.1) |
      exact h0 (h ▸ hx.2.2.1)

/-- Exact projective collision criterion: two re-rootings agree iff every pair of permuted
coordinates has the same cross-ratio against its chosen root. -/
theorem reRoot_eq_iff_cross (x : Triple F) (sigma tau : Equiv.Perm (Fin 4))
    (hsigma : signed x (sigma 3) ≠ 0) (htau : signed x (tau 3) ≠ 0) :
    reRoot sigma x = reRoot tau x ↔
      ∀ i, signed x (sigma i) * signed x (tau 3) =
        signed x (tau i) * signed x (sigma 3) := by
  constructor
  · intro h i
    have ha := congrArg Triple.a h
    have hb := congrArg Triple.b h
    have hc := congrArg Triple.c h
    fin_cases i
    · change -signed x (sigma 0) / signed x (sigma 3) =
          -signed x (tau 0) / signed x (tau 3) at ha
      change signed x (sigma 0) * signed x (tau 3) =
        signed x (tau 0) * signed x (sigma 3)
      have ha' := (div_eq_div_iff hsigma htau).mp ha
      linear_combination -ha'
    · change -signed x (sigma 1) / signed x (sigma 3) =
          -signed x (tau 1) / signed x (tau 3) at hb
      change signed x (sigma 1) * signed x (tau 3) =
        signed x (tau 1) * signed x (sigma 3)
      have hb' := (div_eq_div_iff hsigma htau).mp hb
      linear_combination -hb'
    · simp only [reRoot] at hc
      change signed x (sigma 2) * signed x (tau 3) =
        signed x (tau 2) * signed x (sigma 3)
      field_simp [hsigma, htau] at hc
      simpa [mul_comm] using hc
    · change signed x (sigma 3) * signed x (tau 3) =
        signed x (tau 3) * signed x (sigma 3)
      exact mul_comm _ _
  · intro h
    apply Triple.ext'
    · simp only [reRoot]
      apply (div_eq_div_iff hsigma htau).mpr
      linear_combination -(h 0)
    · simp only [reRoot]
      apply (div_eq_div_iff hsigma htau).mpr
      linear_combination -(h 1)
    · simp only [reRoot]
      exact (div_eq_div_iff hsigma htau).mpr (h 2)

/-- The full projective permutation orbit of a normalized triple. -/
noncomputable def projectiveOrbit (x : Triple F) : Finset (Triple F) :=
  Finset.univ.image fun sigma : Equiv.Perm (Fin 4) => reRoot sigma x

/-- The fibre of one orbit point under the 24 coordinate permutations. -/
noncomputable def projectiveFiber (x y : Triple F) : Finset (Equiv.Perm (Fin 4)) :=
  Finset.univ.filter fun sigma => reRoot sigma x = y

theorem mem_projectiveOrbit_iff {x y : Triple F} :
    y ∈ projectiveOrbit x ↔ ∃ sigma : Equiv.Perm (Fin 4), reRoot sigma x = y := by
  classical
  simp [projectiveOrbit]

/-- The symmetric group on four letters has exactly 24 elements. -/
theorem card_perm_fin_four : Fintype.card (Equiv.Perm (Fin 4)) = 24 := by
  norm_num [Fintype.card_perm]

/-- Uniform-fibre orbit-count engine.  Proving fibre size `1`, `2`, or `6` immediately gives
projective orbit size `24`, `12`, or `4`, respectively. -/
theorem card_projectiveOrbit_mul_of_uniform_fiber (x : Triple F) (k : ℕ)
    (hfiber : ∀ y ∈ projectiveOrbit x, (projectiveFiber x y).card = k) :
    (projectiveOrbit x).card * k = 24 := by
  classical
  calc
    (projectiveOrbit x).card * k = ∑ _y ∈ projectiveOrbit x, k := by simp
    _ = ∑ y ∈ projectiveOrbit x, (projectiveFiber x y).card := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [hfiber y hy]
    _ = Finset.univ.card := by
      rw [Finset.card_eq_sum_card_fiberwise
        (f := fun sigma : Equiv.Perm (Fin 4) => reRoot sigma x)
        (t := projectiveOrbit x) (s := Finset.univ)
        (fun sigma _ => Finset.mem_image_of_mem _ (Finset.mem_univ sigma))]
      rfl
    _ = 24 := by rw [Finset.card_univ, card_perm_fin_four]

theorem card_projectiveOrbit_eq_twentyFour (x : Triple F)
    (hfiber : ∀ y ∈ projectiveOrbit x, (projectiveFiber x y).card = 1) :
    (projectiveOrbit x).card = 24 := by
  have h := card_projectiveOrbit_mul_of_uniform_fiber x 1 hfiber
  omega

theorem card_projectiveOrbit_eq_twelve (x : Triple F)
    (hfiber : ∀ y ∈ projectiveOrbit x, (projectiveFiber x y).card = 2) :
    (projectiveOrbit x).card = 12 := by
  have h := card_projectiveOrbit_mul_of_uniform_fiber x 2 hfiber
  omega

theorem card_projectiveOrbit_eq_four (x : Triple F)
    (hfiber : ∀ y ∈ projectiveOrbit x, (projectiveFiber x y).card = 6) :
    (projectiveOrbit x).card = 4 := by
  have h := card_projectiveOrbit_mul_of_uniform_fiber x 6 hfiber
  omega

/-- Re-rooting by the identity permutation does nothing. -/
@[simp] theorem reRoot_one (x : Triple F) : reRoot 1 x = x := by
  apply Triple.ext' <;> simp [reRoot, signed]

/-- Projective re-rooting composes in the opposite order to function application. -/
theorem reRoot_comp (x : Triple F) (hnz : ∀ i, signed x i ≠ 0)
    (sigma tau : Equiv.Perm (Fin 4)) :
    reRoot sigma (reRoot tau x) = reRoot (tau * sigma) x := by
  have htau : signed x (tau 3) ≠ 0 := hnz _
  have hinner : ∀ i, signed (reRoot tau x) i ≠ 0 := by
    intro i
    rw [signed_reRoot x tau htau i]
    exact div_ne_zero (neg_ne_zero.mpr (hnz _)) (hnz _)
  apply Triple.ext'
  · change -signed (reRoot tau x) (sigma 0) / signed (reRoot tau x) (sigma 3) =
      -signed x ((tau * sigma) 0) / signed x ((tau * sigma) 3)
    rw [signed_reRoot x tau htau (sigma 0), signed_reRoot x tau htau (sigma 3)]
    simp only [Equiv.Perm.mul_apply]
    field_simp [hnz]
  · change -signed (reRoot tau x) (sigma 1) / signed (reRoot tau x) (sigma 3) =
      -signed x ((tau * sigma) 1) / signed x ((tau * sigma) 3)
    rw [signed_reRoot x tau htau (sigma 1), signed_reRoot x tau htau (sigma 3)]
    simp only [Equiv.Perm.mul_apply]
    field_simp [hnz]
  · change signed (reRoot tau x) (sigma 2) / signed (reRoot tau x) (sigma 3) =
      signed x ((tau * sigma) 2) / signed x ((tau * sigma) 3)
    rw [signed_reRoot x tau htau (sigma 2), signed_reRoot x tau htau (sigma 3)]
    simp only [Equiv.Perm.mul_apply]
    field_simp [hnz]

/-- Every fibre over a projective orbit has the same size as the identity fibre. -/
theorem card_projectiveFiber_eq_base (x : Triple F) (hnz : ∀ i, signed x i ≠ 0)
    {y : Triple F} (hy : y ∈ projectiveOrbit x) :
    (projectiveFiber x y).card = (projectiveFiber x x).card := by
  classical
  obtain ⟨tau, htau⟩ := mem_projectiveOrbit_iff.mp hy
  symm
  apply Finset.card_bij'
      (fun rho _ => rho * tau) (fun sigma _ => sigma * tau⁻¹)
  · intro rho hrho
    simp only [projectiveFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hrho ⊢
    calc
      reRoot (rho * tau) x = reRoot tau (reRoot rho x) :=
        (reRoot_comp x hnz tau rho).symm
      _ = reRoot tau x := by rw [hrho]
      _ = y := htau
  · intro sigma hsigma
    simp only [projectiveFiber, Finset.mem_filter, Finset.mem_univ, true_and] at hsigma ⊢
    calc
      reRoot (sigma * tau⁻¹) x = reRoot tau⁻¹ (reRoot sigma x) :=
        (reRoot_comp x hnz tau⁻¹ sigma).symm
      _ = reRoot tau⁻¹ y := by rw [hsigma]
      _ = reRoot tau⁻¹ (reRoot tau x) := by rw [htau]
      _ = reRoot (tau * tau⁻¹) x := reRoot_comp x hnz tau⁻¹ tau
      _ = x := by simp
  · intro rho _
    simp
  · intro sigma _
    simp

/-- Orbit-stabilizer for the projective S4 action on a nonzero signed quadruple. -/
theorem card_projectiveOrbit_mul_card_baseFiber (x : Triple F)
    (hnz : ∀ i, signed x i ≠ 0) :
    (projectiveOrbit x).card * (projectiveFiber x x).card = 24 := by
  apply card_projectiveOrbit_mul_of_uniform_fiber
  intro y hy
  exact card_projectiveFiber_eq_base x hnz hy

theorem card_projectiveOrbit_dvd_twentyFour (x : Triple F)
    (hnz : ∀ i, signed x i ≠ 0) : (projectiveOrbit x).card ∣ 24 := by
  exact ⟨(projectiveFiber x x).card,
    (card_projectiveOrbit_mul_card_baseFiber x hnz).symm⟩

theorem card_projectiveOrbit_eq_twentyFour_of_baseFiber (x : Triple F)
    (hnz : ∀ i, signed x i ≠ 0) (hbase : (projectiveFiber x x).card = 1) :
    (projectiveOrbit x).card = 24 := by
  have h := card_projectiveOrbit_mul_card_baseFiber x hnz
  rw [hbase, Nat.mul_one] at h
  exact h

theorem card_projectiveOrbit_eq_twelve_of_baseFiber (x : Triple F)
    (hnz : ∀ i, signed x i ≠ 0) (hbase : (projectiveFiber x x).card = 2) :
    (projectiveOrbit x).card = 12 := by
  have h := card_projectiveOrbit_mul_card_baseFiber x hnz
  rw [hbase] at h
  omega

theorem card_projectiveOrbit_eq_four_of_baseFiber (x : Triple F)
    (hnz : ∀ i, signed x i ≠ 0) (hbase : (projectiveFiber x x).card = 6) :
    (projectiveOrbit x).card = 4 := by
  have h := card_projectiveOrbit_mul_card_baseFiber x hnz
  rw [hbase] at h
  omega

/-- Accident-specialized orbit-stabilizer: the nonzero premise is discharged from support. -/
theorem card_projectiveOrbit_mul_card_baseFiber_of_accident {H : Finset F}
    (h0 : (0 : F) ∉ H) {x : Triple F} (hx : x ∈ accidents H) :
    (projectiveOrbit x).card * (projectiveFiber x x).card = 24 :=
  card_projectiveOrbit_mul_card_baseFiber x (signed_ne_zero_of_mem_accidents h0 hx)

/-! ## Arbitrary `S₄` re-rooting and the scalar-symmetry seam -/

/-- The normalized additive equation is exactly vanishing of the four signed entries. -/
theorem isSolution_iff_sum_signed_eq_zero (x : Triple F) :
    IsSolution x ↔ ∑ i : Fin 4, signed x i = 0 := by
  simp [IsSolution, signed, Fin.sum_univ_succ]
  constructor <;> intro h <;> linear_combination h

/-- For a solution, seeing `1` in any signed coordinate is enough to enter one of the three
lawful Mann families. -/
theorem isLawful_of_signed_eq_one (x : Triple F) (hsol : IsSolution x)
    (h2 : (2 : F) ≠ 0) {i : Fin 4} (hi : signed x i = 1) : IsLawful x := by
  fin_cases i
  · exact Or.inl hi
  · exact Or.inr (Or.inl hi)
  · right; right
    change -x.c = 1 at hi
    have hc : x.c = -1 := by
      simpa using congrArg Neg.neg hi
    refine ⟨hc, ?_⟩
    unfold IsSolution at hsol
    rw [hc] at hsol
    linear_combination hsol
  · exfalso
    apply h2
    change (-1 : F) = 1 at hi
    calc
      (2 : F) = 1 + 1 := by norm_num
      _ = -1 + 1 := congrArg (fun z : F => z + 1) hi.symm
      _ = 0 := by ring

/-- Arbitrary projective re-rooting preserves the normalized equation. -/
theorem isSolution_reRoot (x : Triple F) (sigma : Equiv.Perm (Fin 4))
    (hnz : ∀ i, signed x i ≠ 0) (hsol : IsSolution x) :
    IsSolution (reRoot sigma x) := by
  rw [isSolution_iff_sum_signed_eq_zero] at hsol ⊢
  have hden : signed x (sigma 3) ≠ 0 := hnz _
  simp_rw [signed_reRoot x sigma hden]
  calc
    ∑ i, -signed x (sigma i) / signed x (sigma 3) =
        (-1 / signed x (sigma 3)) * ∑ i, signed x (sigma i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = (-1 / signed x (sigma 3)) * ∑ i, signed x i := by
      have hperm : ∑ i, signed x (sigma i) = ∑ i, signed x i :=
        Equiv.sum_comp sigma (signed x)
      rw [hperm]
    _ = 0 := by rw [hsol, mul_zero]

/-- A projectively invariant description of the three lawful families. -/
def HasOppositeSigned (x : Triple F) : Prop :=
  ∃ i j : Fin 4, i ≠ j ∧ signed x i = -signed x j

theorem hasOppositeSigned_iff (x : Triple F) :
    HasOppositeSigned x ↔
      x.a = -x.b ∨ x.a = x.c ∨ x.a = 1 ∨
        x.b = x.c ∨ x.b = 1 ∨ x.c = -1 := by
  constructor
  · rintro ⟨i, j, hij, hop⟩
    have hneg : ∀ z : F, -z = 1 → z = -1 := by
      intro z hz
      simpa using congrArg Neg.neg hz
    fin_cases i <;> fin_cases j <;> simp_all [signed] <;> aesop
  · rintro (hab | hac | ha | hbc | hb | hc)
    · exact ⟨0, 1, by decide, by simpa [signed]⟩
    · exact ⟨0, 2, by decide, by simpa [signed]⟩
    · exact ⟨0, 3, by decide, by simpa [signed]⟩
    · exact ⟨1, 2, by decide, by simpa [signed]⟩
    · exact ⟨1, 3, by decide, by simpa [signed]⟩
    · refine ⟨2, 3, by decide, ?_⟩
      simp only [signed_two, signed_three]
      simpa using congrArg Neg.neg hc

theorem isLawful_iff_hasOppositeSigned (x : Triple F) (hsol : IsSolution x) :
    IsLawful x ↔ HasOppositeSigned x := by
  rw [hasOppositeSigned_iff]
  constructor
  · rintro (ha | hb | ⟨hc, hba⟩)
    · exact Or.inr (Or.inr (Or.inl ha))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hb))))
    · left
      have hab0 : x.a + x.b = 0 := by rw [hba]; simp
      exact eq_neg_of_add_eq_zero_left hab0
  · rintro (hab | hac | ha | hbc | hb | hc)
    · right; right
      have hba : x.b = -x.a := by
        have hba0 : x.b + x.a = 0 := by rw [hab]; simp
        exact eq_neg_of_add_eq_zero_left hba0
      refine ⟨?_, hba⟩
      unfold IsSolution at hsol
      have hzero : x.c + 1 = 0 := by rw [← hsol, hab]; simp
      exact eq_neg_of_add_eq_zero_left hzero
    · right; left
      unfold IsSolution at hsol
      linear_combination hsol - hac
    · exact Or.inl ha
    · left
      unfold IsSolution at hsol
      linear_combination hsol - hbc
    · exact Or.inr (Or.inl hb)
    · right; right
      refine ⟨hc, ?_⟩
      unfold IsSolution at hsol
      have hzero : x.a + x.b = 0 := by rw [hsol, hc]; simp
      exact eq_neg_of_add_eq_zero_right hzero

theorem hasOppositeSigned_reRoot_iff (x : Triple F) (sigma : Equiv.Perm (Fin 4))
    (hnz : ∀ i, signed x i ≠ 0) :
    HasOppositeSigned (reRoot sigma x) ↔ HasOppositeSigned x := by
  have hden : signed x (sigma 3) ≠ 0 := hnz _
  constructor
  · rintro ⟨i, j, hij, hop⟩
    refine ⟨sigma i, sigma j, fun h => hij (sigma.injective h), ?_⟩
    rw [signed_reRoot x sigma hden i, signed_reRoot x sigma hden j] at hop
    field_simp [hden] at hop ⊢
    linear_combination -hop
  · rintro ⟨i, j, hij, hop⟩
    refine ⟨sigma.symm i, sigma.symm j, fun h => hij (sigma.symm.injective h), ?_⟩
    rw [signed_reRoot x sigma hden, signed_reRoot x sigma hden]
    simp only [Equiv.apply_symm_apply]
    field_simp [hden]
    linear_combination -hop

/-- Lawfulness is invariant under arbitrary projective re-rooting. -/
theorem isLawful_reRoot_iff (x : Triple F) (sigma : Equiv.Perm (Fin 4))
    (hnz : ∀ i, signed x i ≠ 0) (hsol : IsSolution x) :
    IsLawful (reRoot sigma x) ↔ IsLawful x := by
  rw [isLawful_iff_hasOppositeSigned _ (isSolution_reRoot x sigma hnz hsol),
    isLawful_iff_hasOppositeSigned x hsol]
  exact hasOppositeSigned_reRoot_iff x sigma hnz

/-- Arbitrary projective re-rooting preserves accidents. -/
theorem isAccident_reRoot (x : Triple F) (sigma : Equiv.Perm (Fin 4))
    (hnz : ∀ i, signed x i ≠ 0) (hx : IsAccident x) :
    IsAccident (reRoot sigma x) := by
  refine ⟨isSolution_reRoot x sigma hnz hx.1, ?_⟩
  rw [isLawful_reRoot_iff x sigma hnz hx.1]
  exact hx.2

/-- Every signed coordinate of a supported accident remains in the multiplicative support. -/
theorem signed_mem_of_mem_accidents {H : Finset F}
    (hneg : ∀ z ∈ H, -z ∈ H)
    (hmul : ∀ z ∈ H, ∀ w ∈ H, z * w ∈ H)
    (hinv : ∀ z ∈ H, z⁻¹ ∈ H)
    (h0 : (0 : F) ∉ H) {x : Triple F} (hx : x ∈ accidents H)
    (i : Fin 4) : signed x i ∈ H := by
  rw [mem_accidents_iff] at hx
  have ha0 : x.a ≠ 0 := fun h => h0 (h ▸ hx.1)
  have hone : (1 : F) ∈ H := by
    rw [← mul_inv_cancel₀ ha0]
    exact hmul _ hx.1 _ (hinv _ hx.1)
  fin_cases i
  · exact hx.1
  · exact hx.2.1
  · exact hneg _ hx.2.2.1
  · exact hneg _ hone

/-- Arbitrary projective re-rooting preserves the concrete supported accident set. -/
theorem reRoot_mem_accidents {H : Finset F}
    (hneg : ∀ z ∈ H, -z ∈ H)
    (hmul : ∀ z ∈ H, ∀ w ∈ H, z * w ∈ H)
    (hinv : ∀ z ∈ H, z⁻¹ ∈ H)
    (h0 : (0 : F) ∉ H) {x : Triple F} (hx : x ∈ accidents H)
    (sigma : Equiv.Perm (Fin 4)) : reRoot sigma x ∈ accidents H := by
  have hnz := signed_ne_zero_of_mem_accidents h0 hx
  rw [mem_accidents_iff]
  refine ⟨?_, ?_, ?_, isAccident_reRoot x sigma hnz (mem_accidents_iff.mp hx).2.2.2⟩
  · simp only [reRoot]
    simpa [div_eq_mul_inv] using
      hmul _ (hneg _ (signed_mem_of_mem_accidents hneg hmul hinv h0 hx (sigma 0))) _
        (hinv _ (signed_mem_of_mem_accidents hneg hmul hinv h0 hx (sigma 3)))
  · simp only [reRoot]
    simpa [div_eq_mul_inv] using
      hmul _ (hneg _ (signed_mem_of_mem_accidents hneg hmul hinv h0 hx (sigma 1))) _
        (hinv _ (signed_mem_of_mem_accidents hneg hmul hinv h0 hx (sigma 3)))
  · simp only [reRoot]
    simpa [div_eq_mul_inv] using
      hmul _ (signed_mem_of_mem_accidents hneg hmul hinv h0 hx (sigma 2)) _
        (hinv _ (signed_mem_of_mem_accidents hneg hmul hinv h0 hx (sigma 3)))

/-- **Scalar-symmetry exclusion.** If a coordinate permutation carries every signed entry to
one common scalar multiple, then that scalar is `1` on an odd-characteristic accident.  The
factorization `mu^4 - 1 = (mu-1)(mu+1)(mu^2+1)` is the key: `mu=-1` or `mu^2=-1` forces a
signed coordinate to equal `1`, hence a lawful Mann family. -/
theorem scalar_eq_one_of_permuted_signed_of_accident (x : Triple F)
    (sigma : Equiv.Perm (Fin 4)) (mu : F)
    (hnz : ∀ i, signed x i ≠ 0) (h2 : (2 : F) ≠ 0) (hx : IsAccident x)
    (hscale : ∀ i, signed x (sigma i) = mu * signed x i) : mu = 1 := by
  have hprodPerm : ∏ i, signed x (sigma i) = ∏ i, signed x i :=
    Equiv.prod_comp sigma (signed x)
  have hprodScale : ∏ i, signed x (sigma i) = ∏ i, mu * signed x i := by
    apply Finset.prod_congr rfl
    intro i _
    exact hscale i
  have hconst : (∏ _i : Fin 4, mu) = mu ^ 4 := by
    norm_num [Fin.prod_univ_succ, pow_succ]
  have hprod : (∏ i, signed x i) = mu ^ 4 * ∏ i, signed x i := by
    calc
      (∏ i, signed x i) = ∏ i, signed x (sigma i) := hprodPerm.symm
      _ = ∏ i, mu * signed x i := hprodScale
      _ = (∏ _i : Fin 4, mu) * ∏ i, signed x i := Finset.prod_mul_distrib
      _ = mu ^ 4 * ∏ i, signed x i := by rw [hconst]
  have hprod0 : (∏ i, signed x i) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hnz i
  have hmuPow : mu ^ 4 = 1 := by
    apply mul_right_cancel₀ hprod0
    simpa using hprod.symm
  have hfactor : (mu - 1) * (mu + 1) * (mu ^ 2 + 1) = 0 := by
    calc
      (mu - 1) * (mu + 1) * (mu ^ 2 + 1) = mu ^ 4 - 1 := by ring
      _ = 0 := by rw [hmuPow]; ring
  rcases mul_eq_zero.mp hfactor with hlinear | hquadratic
  · rcases mul_eq_zero.mp hlinear with hminus | hplus
    · linear_combination hminus
    · have hmu : mu = -1 := eq_neg_of_add_eq_zero_left hplus
      exfalso
      apply hx.2
      apply isLawful_of_signed_eq_one x hx.1 h2 (i := sigma 3)
      calc
        signed x (sigma 3) = mu * signed x 3 := hscale 3
        _ = 1 := by rw [hmu, signed_three]; ring
  · have hmu2 : mu ^ 2 = -1 := eq_neg_of_add_eq_zero_left hquadratic
    exfalso
    apply hx.2
    apply isLawful_of_signed_eq_one x hx.1 h2 (i := sigma (sigma 3))
    calc
      signed x (sigma (sigma 3)) = mu * signed x (sigma 3) := hscale (sigma 3)
      _ = mu * (mu * signed x 3) := by rw [hscale 3]
      _ = -(mu ^ 2) := by rw [signed_three]; ring
      _ = 1 := by rw [hmu2]; ring

/-- On an odd-characteristic accident the projective identity fibre is exactly the ordinary
value-preserving stabilizer of the signed four-tuple.  This is the formal seam that removes the
otherwise-real extra scalar symmetries. -/
theorem mem_projectiveFiber_self_iff_preserves_signed_of_accident
    (x : Triple F) (sigma : Equiv.Perm (Fin 4))
    (hnz : ∀ i, signed x i ≠ 0) (h2 : (2 : F) ≠ 0) (hx : IsAccident x) :
    sigma ∈ projectiveFiber x x ↔ ∀ i, signed x (sigma i) = signed x i := by
  classical
  simp only [projectiveFiber, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hr
    let mu : F := -signed x (sigma 3)
    have hden : signed x (sigma 3) ≠ 0 := hnz _
    have hscale : ∀ i, signed x (sigma i) = mu * signed x i := by
      intro i
      have heq : -signed x (sigma i) / signed x (sigma 3) = signed x i := by
        rw [← signed_reRoot x sigma hden i, hr]
      have hmul := (div_eq_iff hden).mp heq
      dsimp only [mu]
      calc
        signed x (sigma i) = -(-signed x (sigma i)) := by ring
        _ = -(signed x i * signed x (sigma 3)) := congrArg Neg.neg hmul
        _ = -signed x (sigma 3) * signed x i := by ring
    have hmu : mu = 1 :=
      scalar_eq_one_of_permuted_signed_of_accident x sigma mu hnz h2 hx hscale
    intro i
    rw [hscale i, hmu, one_mul]
  · intro hval
    apply Triple.ext'
    · simp only [reRoot]
      rw [hval 0, hval 3]
      simp [signed]
    · simp only [reRoot]
      rw [hval 1, hval 3]
      simp [signed]
    · simp only [reRoot]
      rw [hval 2, hval 3]
      simp [signed]

/-! ## Equality-pattern classifier -/

/-- Two disjoint equal pairs among the four signed coordinates. -/
def HasTwoPairsEqualSigned (x : Triple F) : Prop :=
  (signed x 0 = signed x 1 ∧ signed x 2 = signed x 3) ∨
  (signed x 0 = signed x 2 ∧ signed x 1 = signed x 3) ∨
  (signed x 0 = signed x 3 ∧ signed x 1 = signed x 2)

/-- In odd characteristic every `2+2` signed equality pattern is lawful. -/
theorem isLawful_of_hasTwoPairsEqualSigned (x : Triple F) (h2 : (2 : F) ≠ 0)
    (hsol : IsSolution x) (hpairs : HasTwoPairsEqualSigned x) : IsLawful x := by
  rcases hpairs with hpairs | hpairs | hpairs
  · rcases hpairs with ⟨hab, hc⟩
    change x.a = x.b at hab
    change -x.c = -1 at hc
    have hc1 : x.c = 1 := neg_injective hc
    left
    apply mul_left_cancel₀ h2
    unfold IsSolution at hsol
    linear_combination hsol + hab + hc1
  · rcases hpairs with ⟨hac, hb⟩
    change x.a = -x.c at hac
    change x.b = -1 at hb
    left
    apply mul_left_cancel₀ h2
    unfold IsSolution at hsol
    linear_combination hsol + hac - hb
  · rcases hpairs with ⟨ha, hbc⟩
    change x.a = -1 at ha
    change x.b = -x.c at hbc
    right; left
    apply mul_left_cancel₀ h2
    unfold IsSolution at hsol
    linear_combination hsol - ha + hbc

theorem not_hasTwoPairsEqualSigned_of_accident (x : Triple F) (h2 : (2 : F) ≠ 0)
    (hx : IsAccident x) : ¬ HasTwoPairsEqualSigned x := by
  intro hpairs
  exact hx.2 (isLawful_of_hasTwoPairsEqualSigned x h2 hx.1 hpairs)

/-- Exactly one unordered pair of indices has equal signed values. -/
def OnlyEqualPair (x : Triple F) (p q : Fin 4) : Prop :=
  p ≠ q ∧ ∀ i j, signed x i = signed x j ↔
    i = j ∨ (i = p ∧ j = q) ∨ (i = q ∧ j = p)

/-- A permutation preserving a four-tuple with one repeated pair is either the identity or the
transposition of that pair. -/
theorem perm_eq_one_or_swap_of_preserves_onlyEqualPair (x : Triple F)
    (sigma : Equiv.Perm (Fin 4)) {p q : Fin 4} (hpair : OnlyEqualPair x p q)
    (hval : ∀ i, signed x (sigma i) = signed x i) :
    sigma = 1 ∨ sigma = Equiv.swap p q := by
  rcases hpair with ⟨hpq, hpair⟩
  have hcases (i : Fin 4) :
      sigma i = i ∨ (sigma i = p ∧ i = q) ∨ (sigma i = q ∧ i = p) :=
    (hpair (sigma i) i).mp (hval i)
  by_cases hpp : sigma p = p
  · left
    apply Equiv.ext
    intro i
    rcases hcases i with hi | hi | hi
    · exact hi
    · rcases hi with ⟨hsi, hiq⟩
      subst i
      exfalso
      apply hpq
      have hqp : q = p := sigma.injective (hsi.trans hpp.symm)
      exact hqp.symm
    · rcases hi with ⟨hsi, hip⟩
      subst i
      exact (hpq (hpp.symm.trans hsi)).elim
  · have hspq : sigma p = q := by
      rcases hcases p with hp | hp | hp
      · exact (hpp hp).elim
      · exact (hpq hp.2).elim
      · exact hp.1
    right
    apply Equiv.ext
    intro i
    by_cases hip : i = p
    · subst i
      simp [hspq]
    by_cases hiq : i = q
    · subst i
      have hsq : sigma q = p := by
        rcases hcases q with hq | hq | hq
        · exfalso
          apply hpq
          exact sigma.injective (hspq.trans hq.symm)
        · exact hq.1
        · exact (hpq hq.2.symm).elim
      simp [hsq, hpq]
    · have hsi : sigma i = i := by
        rcases hcases i with hi | hi | hi
        · exact hi
        · exact (hiq hi.2).elim
        · exact (hip hi.2).elim
      rw [hsi]
      exact (Equiv.swap_apply_of_ne_of_ne hip hiq).symm

/-- The projective identity fibre has size two for an accident with exactly one repeated signed
pair. -/
theorem card_projectiveFiber_eq_two_of_onlyEqualPair (x : Triple F) {p q : Fin 4}
    (hnz : ∀ i, signed x i ≠ 0) (h2 : (2 : F) ≠ 0) (hx : IsAccident x)
    (hpair : OnlyEqualPair x p q) : (projectiveFiber x x).card = 2 := by
  classical
  have hpq := hpair.1
  have hset : projectiveFiber x x = {1, Equiv.swap p q} := by
    ext sigma
    rw [mem_projectiveFiber_self_iff_preserves_signed_of_accident x sigma hnz h2 hx]
    constructor
    · intro hval
      rcases perm_eq_one_or_swap_of_preserves_onlyEqualPair x sigma hpair hval with h | h
      · simp [h]
      · simp [h]
    · intro hs i
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl
      · simp
      · exact Equiv.apply_swap_eq_self
          ((hpair.2 p q).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))) i
  rw [hset]
  have hone_ne_swap : (1 : Equiv.Perm (Fin 4)) ≠ Equiv.swap p q := by
    intro h
    have hp := Equiv.congr_fun h p
    simp [hpq] at hp
  simp [hone_ne_swap]

/-- Pairwise-distinct signed values give a trivial projective identity fibre. -/
theorem card_projectiveFiber_eq_one_of_signed_injective (x : Triple F)
    (hnz : ∀ i, signed x i ≠ 0) (h2 : (2 : F) ≠ 0) (hx : IsAccident x)
    (hinj : Function.Injective (signed x)) : (projectiveFiber x x).card = 1 := by
  classical
  have hset : projectiveFiber x x = {1} := by
    ext sigma
    rw [mem_projectiveFiber_self_iff_preserves_signed_of_accident x sigma hnz h2 hx]
    constructor
    · intro hval
      have hsigma : sigma = 1 := by
        apply Equiv.ext
        intro i
        exact hinj (hval i)
      simp [hsigma]
    · intro h
      simp only [Finset.mem_singleton] at h
      subst sigma
      simp
  rw [hset]
  simp

theorem OnlyEqualPair.symm {x : Triple F} {p q : Fin 4} (h : OnlyEqualPair x p q) :
    OnlyEqualPair x q p := by
  refine ⟨h.1.symm, ?_⟩
  intro i j
  rw [h.2]
  tauto

theorem onlyEqualPair_zero_one (x : Triple F) (heq : signed x 0 = signed x 1)
    (htriple : ¬ HasTripleEqualSigned x) (hpairs : ¬ HasTwoPairsEqualSigned x) :
    OnlyEqualPair x 0 1 := by
  have h02 : signed x 0 ≠ signed x 2 := by
    intro h
    apply htriple
    exact Or.inl ⟨heq, heq.symm.trans h⟩
  have h03 : signed x 0 ≠ signed x 3 := by
    intro h
    apply htriple
    exact Or.inr (Or.inl ⟨heq, heq.symm.trans h⟩)
  have h23 : signed x 2 ≠ signed x 3 := by
    intro h
    apply hpairs
    exact Or.inl ⟨heq, h⟩
  refine ⟨by decide, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all <;> aesop

theorem onlyEqualPair_zero_two (x : Triple F) (heq : signed x 0 = signed x 2)
    (htriple : ¬ HasTripleEqualSigned x) (hpairs : ¬ HasTwoPairsEqualSigned x) :
    OnlyEqualPair x 0 2 := by
  have h01 : signed x 0 ≠ signed x 1 := by
    intro h
    apply htriple
    exact Or.inl ⟨h, h.symm.trans heq⟩
  have h03 : signed x 0 ≠ signed x 3 := by
    intro h
    apply htriple
    exact Or.inr (Or.inr (Or.inl ⟨heq, heq.symm.trans h⟩))
  have h13 : signed x 1 ≠ signed x 3 := by
    intro h
    apply hpairs
    exact Or.inr (Or.inl ⟨heq, h⟩)
  refine ⟨by decide, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all <;> aesop

theorem onlyEqualPair_zero_three (x : Triple F) (heq : signed x 0 = signed x 3)
    (htriple : ¬ HasTripleEqualSigned x) (hpairs : ¬ HasTwoPairsEqualSigned x) :
    OnlyEqualPair x 0 3 := by
  have h01 : signed x 0 ≠ signed x 1 := by
    intro h
    apply htriple
    exact Or.inr (Or.inl ⟨h, h.symm.trans heq⟩)
  have h02 : signed x 0 ≠ signed x 2 := by
    intro h
    apply htriple
    exact Or.inr (Or.inr (Or.inl ⟨h, h.symm.trans heq⟩))
  have h12 : signed x 1 ≠ signed x 2 := by
    intro h
    apply hpairs
    exact Or.inr (Or.inr ⟨heq, h⟩)
  refine ⟨by decide, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all <;> aesop

theorem onlyEqualPair_one_two (x : Triple F) (heq : signed x 1 = signed x 2)
    (htriple : ¬ HasTripleEqualSigned x) (hpairs : ¬ HasTwoPairsEqualSigned x) :
    OnlyEqualPair x 1 2 := by
  have h01 : signed x 0 ≠ signed x 1 := by
    intro h
    apply htriple
    exact Or.inl ⟨h, heq⟩
  have h13 : signed x 1 ≠ signed x 3 := by
    intro h
    apply htriple
    exact Or.inr (Or.inr (Or.inr ⟨heq, heq.symm.trans h⟩))
  have h03 : signed x 0 ≠ signed x 3 := by
    intro h
    apply hpairs
    exact Or.inr (Or.inr ⟨h, heq⟩)
  refine ⟨by decide, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all <;> aesop

theorem onlyEqualPair_one_three (x : Triple F) (heq : signed x 1 = signed x 3)
    (htriple : ¬ HasTripleEqualSigned x) (hpairs : ¬ HasTwoPairsEqualSigned x) :
    OnlyEqualPair x 1 3 := by
  have h01 : signed x 0 ≠ signed x 1 := by
    intro h
    apply htriple
    exact Or.inr (Or.inl ⟨h, heq⟩)
  have h12 : signed x 1 ≠ signed x 2 := by
    intro h
    apply htriple
    exact Or.inr (Or.inr (Or.inr ⟨h, h.symm.trans heq⟩))
  have h02 : signed x 0 ≠ signed x 2 := by
    intro h
    apply hpairs
    exact Or.inr (Or.inl ⟨h, heq⟩)
  refine ⟨by decide, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all <;> aesop

theorem onlyEqualPair_two_three (x : Triple F) (heq : signed x 2 = signed x 3)
    (htriple : ¬ HasTripleEqualSigned x) (hpairs : ¬ HasTwoPairsEqualSigned x) :
    OnlyEqualPair x 2 3 := by
  have h02 : signed x 0 ≠ signed x 2 := by
    intro h
    apply htriple
    exact Or.inr (Or.inr (Or.inl ⟨h, heq⟩))
  have h12 : signed x 1 ≠ signed x 2 := by
    intro h
    apply htriple
    exact Or.inr (Or.inr (Or.inr ⟨h, heq⟩))
  have h01 : signed x 0 ≠ signed x 1 := by
    intro h
    apply hpairs
    exact Or.inl ⟨h, heq⟩
  refine ⟨by decide, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all <;> aesop

/-- With triple-equalities and two-pair patterns excluded, any witnessed equality is the unique
repeated pair.  This is the finite `1+1+2` partition classifier on four coordinates. -/
theorem onlyEqualPair_of_eq_of_not_triple_of_not_twoPairs (x : Triple F)
    {p q : Fin 4} (hpq : p ≠ q) (heq : signed x p = signed x q)
    (htriple : ¬ HasTripleEqualSigned x)
    (hpairs : ¬ HasTwoPairsEqualSigned x) : OnlyEqualPair x p q := by
  fin_cases p
  · fin_cases q
    · exact (hpq rfl).elim
    · exact onlyEqualPair_zero_one x heq htriple hpairs
    · exact onlyEqualPair_zero_two x heq htriple hpairs
    · exact onlyEqualPair_zero_three x heq htriple hpairs
  · fin_cases q
    · exact (onlyEqualPair_zero_one x heq.symm htriple hpairs).symm
    · exact (hpq rfl).elim
    · exact onlyEqualPair_one_two x heq htriple hpairs
    · exact onlyEqualPair_one_three x heq htriple hpairs
  · fin_cases q
    · exact (onlyEqualPair_zero_two x heq.symm htriple hpairs).symm
    · exact (onlyEqualPair_one_two x heq.symm htriple hpairs).symm
    · exact (hpq rfl).elim
    · exact onlyEqualPair_two_three x heq htriple hpairs
  · fin_cases q
    · exact (onlyEqualPair_zero_three x heq.symm htriple hpairs).symm
    · exact (onlyEqualPair_one_three x heq.symm htriple hpairs).symm
    · exact (onlyEqualPair_two_three x heq.symm htriple hpairs).symm
    · exact (hpq rfl).elim

/-- Exactly one signed coordinate differs from the other three. -/
def OnlyDifferentIndex (x : Triple F) (d : Fin 4) : Prop :=
  ∀ i j, signed x i = signed x j ↔ (i = d ↔ j = d)

/-- There are exactly `3! = 6` permutations of four coordinates fixing a prescribed index. -/
theorem card_perm_fin_four_fix (d : Fin 4) :
    (Finset.univ.filter fun sigma : Equiv.Perm (Fin 4) => sigma d = d).card = 6 := by
  fin_cases d <;> decide

/-- A `3+1` signed equality pattern gives projective identity fibre size six. -/
theorem card_projectiveFiber_eq_six_of_onlyDifferentIndex (x : Triple F) {d : Fin 4}
    (hnz : ∀ i, signed x i ≠ 0) (h2 : (2 : F) ≠ 0) (hx : IsAccident x)
    (hdiff : OnlyDifferentIndex x d) : (projectiveFiber x x).card = 6 := by
  classical
  have hset : projectiveFiber x x =
      Finset.univ.filter fun sigma : Equiv.Perm (Fin 4) => sigma d = d := by
    ext sigma
    rw [mem_projectiveFiber_self_iff_preserves_signed_of_accident x sigma hnz h2 hx]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hval
      exact ((hdiff (sigma d) d).mp (hval d)).mpr rfl
    · intro hfix i
      apply (hdiff (sigma i) i).mpr
      constructor
      · intro hsid
        exact sigma.injective (hsid.trans hfix.symm)
      · intro hid
        subst i
        exact hfix
  rw [hset]
  exact card_perm_fin_four_fix d

/-- Every triple-equal pattern with no two-pair collapse has a unique exceptional coordinate. -/
theorem exists_onlyDifferentIndex_of_triple_of_not_twoPairs (x : Triple F)
    (htriple : HasTripleEqualSigned x) (hpairs : ¬ HasTwoPairsEqualSigned x) :
    ∃ d, OnlyDifferentIndex x d := by
  rcases htriple with h012 | h013 | h023 | h123
  · have h23 : signed x 2 ≠ signed x 3 := by
      intro h
      apply hpairs
      exact Or.inl ⟨h012.1, h⟩
    refine ⟨3, ?_⟩
    intro i j
    fin_cases i <;> fin_cases j <;> simp_all <;> aesop
  · have h02 : signed x 0 ≠ signed x 2 := by
      intro h
      apply hpairs
      exact Or.inr (Or.inl ⟨h, h013.2⟩)
    refine ⟨2, ?_⟩
    intro i j
    fin_cases i <;> fin_cases j <;> simp_all <;> aesop
  · have h13 : signed x 1 ≠ signed x 3 := by
      intro h
      apply hpairs
      exact Or.inr (Or.inl ⟨h023.1, h⟩)
    refine ⟨1, ?_⟩
    intro i j
    fin_cases i <;> fin_cases j <;> simp_all <;> aesop
  · have h01 : signed x 0 ≠ signed x 1 := by
      intro h
      apply hpairs
      exact Or.inl ⟨h, h123.2⟩
    refine ⟨0, ?_⟩
    intro i j
    fin_cases i <;> fin_cases j <;> simp_all <;> aesop

/-- Complete identity-fibre classification for odd-characteristic accidents. -/
theorem card_projectiveFiber_eq_one_or_two_or_six_of_accident (x : Triple F)
    (hnz : ∀ i, signed x i ≠ 0) (h2 : (2 : F) ≠ 0) (hx : IsAccident x) :
    (projectiveFiber x x).card = 1 ∨ (projectiveFiber x x).card = 2 ∨
      (projectiveFiber x x).card = 6 := by
  classical
  have hpairs := not_hasTwoPairsEqualSigned_of_accident x h2 hx
  by_cases htriple : HasTripleEqualSigned x
  · right; right
    obtain ⟨d, hdiff⟩ := exists_onlyDifferentIndex_of_triple_of_not_twoPairs x htriple hpairs
    exact card_projectiveFiber_eq_six_of_onlyDifferentIndex x hnz h2 hx hdiff
  · by_cases hinj : Function.Injective (signed x)
    · left
      exact card_projectiveFiber_eq_one_of_signed_injective x hnz h2 hx hinj
    · right; left
      obtain ⟨p, q, heq, hpq⟩ := Function.not_injective_iff.mp hinj
      exact card_projectiveFiber_eq_two_of_onlyEqualPair x hnz h2 hx
        (onlyEqualPair_of_eq_of_not_triple_of_not_twoPairs x hpq heq htriple hpairs)

/-- Excluding triple-equality leaves exactly the 24- or 12-element projective packets. -/
theorem card_projectiveOrbit_eq_twentyFour_or_twelve_of_accident
    (x : Triple F) (hnz : ∀ i, signed x i ≠ 0) (h2 : (2 : F) ≠ 0)
    (hx : IsAccident x) (htriple : ¬ HasTripleEqualSigned x) :
    (projectiveOrbit x).card = 24 ∨ (projectiveOrbit x).card = 12 := by
  have hpairs := not_hasTwoPairsEqualSigned_of_accident x h2 hx
  by_cases hinj : Function.Injective (signed x)
  · left
    exact card_projectiveOrbit_eq_twentyFour_of_baseFiber x hnz
      (card_projectiveFiber_eq_one_of_signed_injective x hnz h2 hx hinj)
  · right
    obtain ⟨p, q, heq, hpq⟩ := Function.not_injective_iff.mp hinj
    exact card_projectiveOrbit_eq_twelve_of_baseFiber x hnz
      (card_projectiveFiber_eq_two_of_onlyEqualPair x hnz h2 hx
        (onlyEqualPair_of_eq_of_not_triple_of_not_twoPairs x hpq heq htriple hpairs))

/-- Every point belongs to its projective permutation orbit. -/
theorem self_mem_projectiveOrbit (x : Triple F) : x ∈ projectiveOrbit x := by
  rw [mem_projectiveOrbit_iff]
  exact ⟨1, reRoot_one x⟩

/-- An invariant finite set contains each full projective orbit of each of its points. -/
theorem projectiveOrbit_subset_of_closed (S : Finset (Triple F))
    (hclosed : ∀ x ∈ S, ∀ sigma : Equiv.Perm (Fin 4), reRoot sigma x ∈ S)
    {x : Triple F} (hx : x ∈ S) : projectiveOrbit x ⊆ S := by
  intro y hy
  obtain ⟨sigma, rfl⟩ := mem_projectiveOrbit_iff.mp hy
  exact hclosed x hx sigma

/-- Removing one projective orbit from an invariant nonzero set leaves an invariant set. -/
theorem reRoot_mem_sdiff_projectiveOrbit (S : Finset (Triple F))
    (hnz : ∀ x ∈ S, ∀ i, signed x i ≠ 0)
    (hclosed : ∀ x ∈ S, ∀ sigma : Equiv.Perm (Fin 4), reRoot sigma x ∈ S)
    {x y : Triple F} (hx : x ∈ S) (hy : y ∈ S \ projectiveOrbit x)
    (sigma : Equiv.Perm (Fin 4)) : reRoot sigma y ∈ S \ projectiveOrbit x := by
  rw [Finset.mem_sdiff] at hy ⊢
  refine ⟨hclosed y hy.1 sigma, ?_⟩
  intro hmem
  apply hy.2
  obtain ⟨tau, htau⟩ := mem_projectiveOrbit_iff.mp hmem
  rw [mem_projectiveOrbit_iff]
  refine ⟨tau * sigma⁻¹, ?_⟩
  calc
    reRoot (tau * sigma⁻¹) x = reRoot sigma⁻¹ (reRoot tau x) :=
      (reRoot_comp x (hnz x hx) sigma⁻¹ tau).symm
    _ = reRoot sigma⁻¹ (reRoot sigma y) := by rw [htau]
    _ = reRoot (sigma * sigma⁻¹) y := reRoot_comp y (hnz y hy.1) sigma⁻¹ sigma
    _ = y := by simp

/-- If every projective packet in a finite invariant nonzero set has size `12` or `24`, then
the total set has cardinality divisible by `12`. -/
theorem twelve_dvd_card_of_projective_packets (S : Finset (Triple F))
    (hnz : ∀ x ∈ S, ∀ i, signed x i ≠ 0)
    (hclosed : ∀ x ∈ S, ∀ sigma : Equiv.Perm (Fin 4), reRoot sigma x ∈ S)
    (hpacket : ∀ x ∈ S,
      (projectiveOrbit x).card = 24 ∨ (projectiveOrbit x).card = 12) :
    12 ∣ S.card := by
  classical
  induction hcard : S.card using Nat.strong_induction_on generalizing S with
  | _ N ih =>
    subst hcard
    rcases S.eq_empty_or_nonempty with hS | ⟨x, hx⟩
    · subst hS
      simp
    · set orb := projectiveOrbit x with horb
      have horbSub : orb ⊆ S := by
        rw [horb]
        exact projectiveOrbit_subset_of_closed S hclosed hx
      have hxorb : x ∈ orb := by rw [horb]; exact self_mem_projectiveOrbit x
      have horbPos : 0 < orb.card := Finset.card_pos.mpr ⟨x, hxorb⟩
      have horbDvd : 12 ∣ orb.card := by
        rw [horb]
        rcases hpacket x hx with h24 | h12
        · rw [h24]
          norm_num
        · rw [h12]
      set T := S \ orb with hT
      have hTlt : T.card < S.card := by
        have horbLe : orb.card ≤ S.card := Finset.card_le_card horbSub
        rw [hT, Finset.card_sdiff_of_subset horbSub]
        omega
      have hnzT : ∀ y ∈ T, ∀ i, signed y i ≠ 0 := by
        intro y hy
        exact hnz y (Finset.mem_sdiff.mp (hT ▸ hy)).1
      have hclosedT : ∀ y ∈ T, ∀ sigma : Equiv.Perm (Fin 4), reRoot sigma y ∈ T := by
        intro y hy sigma
        rw [hT]
        apply reRoot_mem_sdiff_projectiveOrbit S hnz hclosed hx
        simpa [hT] using hy
      have hpacketT : ∀ y ∈ T,
          (projectiveOrbit y).card = 24 ∨ (projectiveOrbit y).card = 12 := by
        intro y hy
        exact hpacket y (Finset.mem_sdiff.mp (hT ▸ hy)).1
      have hTDvd : 12 ∣ T.card := ih T.card hTlt T hnzT hclosedT hpacketT rfl
      have hsplit : S.card = T.card + orb.card := by
        have h := Finset.card_sdiff_add_card_eq_card horbSub
        rw [← hT] at h
        exact h.symm
      rw [hsplit]
      exact Nat.dvd_add hTDvd horbDvd

/-- Global `12`-divisibility for a supported accident set once triple-equality is excluded. -/
theorem twelve_dvd_card_accidents_of_no_triple
    {H : Finset F}
    (hneg : ∀ z ∈ H, -z ∈ H)
    (hmul : ∀ z ∈ H, ∀ w ∈ H, z * w ∈ H)
    (hinv : ∀ z ∈ H, z⁻¹ ∈ H)
    (h0 : (0 : F) ∉ H) (h2 : (2 : F) ≠ 0)
    (htriple : ∀ x ∈ accidents H, ¬ HasTripleEqualSigned x) :
    12 ∣ (accidents H).card := by
  apply twelve_dvd_card_of_projective_packets (accidents H)
  · intro x hx
    exact signed_ne_zero_of_mem_accidents h0 hx
  · intro x hx sigma
    exact reRoot_mem_accidents hneg hmul hinv h0 hx sigma
  · intro x hx
    exact card_projectiveOrbit_eq_twentyFour_or_twelve_of_accident x
      (signed_ne_zero_of_mem_accidents h0 hx) h2 (mem_accidents_iff.mp hx).2.2.2
      (htriple x hx)

/-- Under the same hypotheses, every nonempty supported accident set contains at least twelve
elements.  Thus any independent upper bound `≤ 11` is already an accident-freeness certificate. -/
theorem twelve_le_card_accidents_of_nonempty_of_no_triple
    {H : Finset F}
    (hneg : ∀ z ∈ H, -z ∈ H)
    (hmul : ∀ z ∈ H, ∀ w ∈ H, z * w ∈ H)
    (hinv : ∀ z ∈ H, z⁻¹ ∈ H)
    (h0 : (0 : F) ∉ H) (h2 : (2 : F) ≠ 0)
    (htriple : ∀ x ∈ accidents H, ¬ HasTripleEqualSigned x)
    (hne : (accidents H).Nonempty) : 12 ≤ (accidents H).card := by
  have hdvd := twelve_dvd_card_accidents_of_no_triple hneg hmul hinv h0 h2 htriple
  obtain ⟨k, hk⟩ := hdvd
  have hpos : 0 < (accidents H).card := Finset.card_pos.mpr hne
  omega

/-- At the first certified production prime, every supported accident set has cardinality
divisible by `12` as soon as all support elements are `2^30`-th roots of unity. -/
theorem firstPrime_twelve_dvd_card_accidents {H : Finset (ZMod P)}
    (hneg : ∀ z ∈ H, -z ∈ H)
    (hmul : ∀ z ∈ H, ∀ w ∈ H, z * w ∈ H)
    (hinv : ∀ z ∈ H, z⁻¹ ∈ H)
    (h0 : (0 : ZMod P) ∉ H)
    (hpow : ∀ z ∈ H, z ^ (2 ^ 30 : ℕ) = 1) :
    12 ∣ (accidents H).card := by
  apply twelve_dvd_card_accidents_of_no_triple hneg hmul hinv h0
  · intro h
    have hdvd : P ∣ 2 := (ZMod.natCast_eq_zero_iff 2 P).mp h
    norm_num [P] at hdvd
  · intro x hx
    exact firstPrime_no_tripleEqual_accident hneg hmul hinv h0 hpow hx

/-- Second-certified-production-prime version of `firstPrime_twelve_dvd_card_accidents`. -/
theorem secondPrime_twelve_dvd_card_accidents
    {H : Finset (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)}
    (hneg : ∀ z ∈ H, -z ∈ H)
    (hmul : ∀ z ∈ H, ∀ w ∈ H, z * w ∈ H)
    (hinv : ∀ z ∈ H, z⁻¹ ∈ H)
    (h0 : (0 : ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) ∉ H)
    (hpow : ∀ z ∈ H, z ^ (2 ^ 30 : ℕ) = 1) :
    12 ∣ (accidents H).card := by
  apply twelve_dvd_card_accidents_of_no_triple hneg hmul hinv h0
  · intro h
    have hdvd : ArkLib.ProximityGap.PrizeShapePrimeP30Second.P ∣ 2 :=
      (ZMod.natCast_eq_zero_iff 2
        ArkLib.ProximityGap.PrizeShapePrimeP30Second.P).mp h
    norm_num [ArkLib.ProximityGap.PrizeShapePrimeP30Second.P] at hdvd
  · intro x hx
    exact secondPrime_no_tripleEqual_accident hneg hmul hinv h0 hpow hx

/-! ## Exact quotient by a cyclotomic-unit signature

For an `n`-th root of unity `x`, put `κ(x) = (x - 1)^n`.  Equality `κ(x) = κ(y)`
means that `(x - 1) / (y - 1)` is again an `n`-th root.  The diagonal collision `y = x`
and inversion collision `y = x⁻¹` are precisely the two lawful degeneracies.  Thus the
remaining arithmetic residual is injectivity of `κ` on nontrivial roots modulo inversion.
-/

/-- The cyclotomic-unit signature used to quotient normalized additive-energy accidents. -/
def differenceSignature (n : ℕ) (x : F) : F := (x - 1) ^ n

/-- A nontrivial collision before taking `n`-th powers.  The multiplier `h` records
`x - 1 = h * (y - 1)`; the two excluded values of `y` are exactly the lawful strata. -/
def IsNontrivialDifferenceCollision (H : Finset F) (x y h : F) : Prop :=
  x ∈ H ∧ y ∈ H ∧ h ∈ H ∧ x ≠ 1 ∧ y ≠ 1 ∧ y ≠ x ∧ y ≠ x⁻¹ ∧
    x - 1 = h * (y - 1)

/-- A nontrivial difference collision produces the normalized triple `(x,h,hy)`. -/
theorem mem_accidents_of_nontrivialDifferenceCollision
    {H : Finset F} {x y h : F}
    (hmul : ∀ z ∈ H, ∀ w ∈ H, z * w ∈ H)
    (hcol : IsNontrivialDifferenceCollision H x y h) :
    (⟨x, h, h * y⟩ : Triple F) ∈ accidents H := by
  rcases hcol with ⟨hxH, hyH, hhH, hx1, _hy1, hyx, hyinv, hrel⟩
  rw [mem_accidents_iff]
  refine ⟨hxH, hhH, hmul _ hhH _ hyH, ?_⟩
  constructor
  · unfold IsSolution
    dsimp
    linear_combination hrel
  · intro hlaw
    rcases hlaw with hxone | hhone | ⟨hhy, hhneg⟩
    · exact hx1 (by simpa using hxone)
    · change h = 1 at hhone
      apply hyx
      rw [hhone] at hrel
      linear_combination -hrel
    · apply hyinv
      change h * y = -1 at hhy
      change h = -x at hhneg
      have hxy : x * y = 1 := by
        rw [hhneg] at hhy
        have := congrArg Neg.neg hhy
        simpa using this
      exact eq_inv_of_mul_eq_one_right hxy

/-- Every supported accident gives a nontrivial difference collision, with
`y = c / b` and collision multiplier `h = b`. -/
theorem nontrivialDifferenceCollision_of_mem_accidents
    {H : Finset F} {t : Triple F}
    (hmul : ∀ z ∈ H, ∀ w ∈ H, z * w ∈ H)
    (hinv : ∀ z ∈ H, z⁻¹ ∈ H)
    (h0 : (0 : F) ∉ H)
    (ht : t ∈ accidents H) :
    IsNontrivialDifferenceCollision H t.a (t.c / t.b) t.b := by
  rw [mem_accidents_iff] at ht
  rcases ht with ⟨haH, hbH, hcH, hsol, hnlaw⟩
  have ha1 : t.a ≠ 1 := fun h => hnlaw (Or.inl h)
  have hb1 : t.b ≠ 1 := fun h => hnlaw (Or.inr (Or.inl h))
  have ha0 : t.a ≠ 0 := fun h => h0 (h ▸ haH)
  have hb0 : t.b ≠ 0 := fun h => h0 (h ▸ hbH)
  refine ⟨haH, ?_, hbH, ha1, ?_, ?_, ?_, ?_⟩
  · simpa [div_eq_mul_inv] using hmul _ hcH _ (hinv _ hbH)
  · intro hy1
    have hcb : t.c = t.b := by
      have h := (div_eq_iff hb0).mp hy1
      simpa using h
    apply hnlaw
    left
    unfold IsSolution at hsol
    rw [hcb] at hsol
    linear_combination hsol
  · intro hya
    have hc : t.c = t.a * t.b := (div_eq_iff hb0).mp hya
    have hprod : (t.a - 1) * (t.b - 1) = 0 := by
      unfold IsSolution at hsol
      rw [hc] at hsol
      linear_combination -hsol
    rcases mul_eq_zero.mp hprod with ha | hb
    · exact ha1 (sub_eq_zero.mp ha)
    · exact hb1 (sub_eq_zero.mp hb)
  · intro hyinv
    have hc : t.c = t.a⁻¹ * t.b := (div_eq_iff hb0).mp hyinv
    have hprod : (t.a - 1) * (t.a + t.b) = 0 := by
      unfold IsSolution at hsol
      rw [hc] at hsol
      field_simp [ha0] at hsol
      linear_combination hsol
    rcases mul_eq_zero.mp hprod with ha | hab
    · exact ha1 (sub_eq_zero.mp ha)
    · apply hnlaw
      right; right
      have hbneg : t.b = -t.a := by linear_combination hab
      constructor
      · rw [hc, hbneg]
        field_simp [ha0]
      · exact hbneg
  · calc
      t.a - 1 = t.c - t.b := by
        unfold IsSolution at hsol
        linear_combination hsol
      _ = t.b * (t.c / t.b - 1) := by field_simp [hb0]

/-- Taking `n`-th powers forgets the collision multiplier when every support element is an
`n`-th root of unity. -/
theorem differenceSignature_eq_of_nontrivialDifferenceCollision
    {H : Finset F} {n : ℕ} {x y h : F}
    (hpow : ∀ z ∈ H, z ^ n = 1)
    (hcol : IsNontrivialDifferenceCollision H x y h) :
    differenceSignature n x = differenceSignature n y := by
  rcases hcol with ⟨_, _, hhH, _, _, _, _, hrel⟩
  rw [differenceSignature, differenceSignature, hrel, mul_pow, hpow h hhH, one_mul]

/-- The exact small residual: the signature is injective after identifying `x` with `x⁻¹`. -/
def DifferenceSignatureInjectiveModInversion (H : Finset F) (n : ℕ) : Prop :=
  ∀ x ∈ H, x ≠ 1 → ∀ y ∈ H, y ≠ 1 →
    differenceSignature n x = differenceSignature n y → y = x ∨ y = x⁻¹

/-- Signature injectivity modulo inversion is an accident-freeness certificate. -/
theorem accidents_eq_empty_of_differenceSignatureInjectiveModInversion
    {H : Finset F} {n : ℕ}
    (hmul : ∀ z ∈ H, ∀ w ∈ H, z * w ∈ H)
    (hinv : ∀ z ∈ H, z⁻¹ ∈ H)
    (h0 : (0 : F) ∉ H)
    (hpow : ∀ z ∈ H, z ^ n = 1)
    (hinjective : DifferenceSignatureInjectiveModInversion H n) :
    accidents H = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  let y := t.c / t.b
  let h := t.b
  have hcol : IsNontrivialDifferenceCollision H t.a y h :=
    nontrivialDifferenceCollision_of_mem_accidents hmul hinv h0 ht
  rcases hcol with ⟨haH, hyH, hhH, ha1, hy1, hyx, hyinv, hrel⟩
  have hsig : differenceSignature n t.a = differenceSignature n y :=
    differenceSignature_eq_of_nontrivialDifferenceCollision hpow
      ⟨haH, hyH, hhH, ha1, hy1, hyx, hyinv, hrel⟩
  rcases hinjective t.a haH ha1 y hyH hy1 hsig with h | h
  · exact hyx h
  · exact hyinv h

/-- First-prime production socket: only signature injectivity modulo inversion remains. -/
theorem firstPrime_accidents_eq_empty_of_differenceSignatureInjectiveModInversion
    {H : Finset (ZMod P)}
    (hmul : ∀ z ∈ H, ∀ w ∈ H, z * w ∈ H)
    (hinv : ∀ z ∈ H, z⁻¹ ∈ H)
    (h0 : (0 : ZMod P) ∉ H)
    (hpow : ∀ z ∈ H, z ^ (2 ^ 30 : ℕ) = 1)
    (hinjective : DifferenceSignatureInjectiveModInversion H (2 ^ 30)) :
    accidents H = ∅ :=
  accidents_eq_empty_of_differenceSignatureInjectiveModInversion
    hmul hinv h0 hpow hinjective

/-- Second-prime production socket: only signature injectivity modulo inversion remains. -/
theorem secondPrime_accidents_eq_empty_of_differenceSignatureInjectiveModInversion
    {H : Finset (ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P)}
    (hmul : ∀ z ∈ H, ∀ w ∈ H, z * w ∈ H)
    (hinv : ∀ z ∈ H, z⁻¹ ∈ H)
    (h0 : (0 : ZMod ArkLib.ProximityGap.PrizeShapePrimeP30Second.P) ∉ H)
    (hpow : ∀ z ∈ H, z ^ (2 ^ 30 : ℕ) = 1)
    (hinjective : DifferenceSignatureInjectiveModInversion H (2 ^ 30)) :
    accidents H = ∅ :=
  accidents_eq_empty_of_differenceSignatureInjectiveModInversion
    hmul hinv h0 hpow hinjective

/-- Conversely, if `H` contains every `n`-th root, then an exceptional signature collision
would itself construct an accident. -/
theorem differenceSignatureInjectiveModInversion_of_accidents_eq_empty
    {H : Finset F} {n : ℕ}
    (hmul : ∀ z ∈ H, ∀ w ∈ H, z * w ∈ H)
    (hcomplete : ∀ z : F, z ^ n = 1 → z ∈ H)
    (hempty : accidents H = ∅) :
    DifferenceSignatureInjectiveModInversion H n := by
  intro x hxH hx1 y hyH hy1 hsig
  by_contra hnontrivial
  push_neg at hnontrivial
  rcases hnontrivial with ⟨hyx, hyinv⟩
  have hySub : y - 1 ≠ 0 := sub_ne_zero.mpr hy1
  let h : F := (x - 1) / (y - 1)
  have hhpow : h ^ n = 1 := by
    change (x - 1) ^ n = (y - 1) ^ n at hsig
    dsimp [h]
    rw [div_pow, hsig, div_self (pow_ne_zero n hySub)]
  have hhH : h ∈ H := hcomplete h hhpow
  have hrel : x - 1 = h * (y - 1) := by
    dsimp [h]
    exact (div_mul_cancel₀ _ hySub).symm
  have hcol : IsNontrivialDifferenceCollision H x y h :=
    ⟨hxH, hyH, hhH, hx1, hy1, hyx, hyinv, hrel⟩
  have hacc := mem_accidents_of_nontrivialDifferenceCollision hmul hcol
  rw [hempty] at hacc
  simp at hacc

/-- Exact quotient theorem for a support which is precisely the set of `n`-th roots. -/
theorem accidents_eq_empty_iff_differenceSignatureInjectiveModInversion
    {H : Finset F} {n : ℕ}
    (hmul : ∀ z ∈ H, ∀ w ∈ H, z * w ∈ H)
    (hinv : ∀ z ∈ H, z⁻¹ ∈ H)
    (h0 : (0 : F) ∉ H)
    (hpow : ∀ z ∈ H, z ^ n = 1)
    (hcomplete : ∀ z : F, z ^ n = 1 → z ∈ H) :
    accidents H = ∅ ↔ DifferenceSignatureInjectiveModInversion H n := by
  constructor
  · exact differenceSignatureInjectiveModInversion_of_accidents_eq_empty hmul hcomplete
  · exact accidents_eq_empty_of_differenceSignatureInjectiveModInversion
      hmul hinv h0 hpow

/-- Ordered exceptional signature collisions.  Removing the diagonal and inversion graph makes
this Finset have exactly the same cardinality as the normalized accident Finset. -/
noncomputable def differenceCollisionPairs (H : Finset F) (n : ℕ) : Finset (F × F) :=
  ((H.erase 1) ×ˢ (H.erase 1)).filter fun q =>
    differenceSignature n q.1 = differenceSignature n q.2 ∧
      q.2 ≠ q.1 ∧ q.2 ≠ q.1⁻¹

/-- Exact cardinality form of the signature quotient.  In a signature fibre of size `k`, the
right-hand side contributes `k² - 2k + s`, where `s` records whether the fibre contains `-1`.
This reduces accident counting from supported triples to ordered pairs in signature fibres. -/
theorem card_accidents_eq_card_differenceCollisionPairs
    {H : Finset F} {n : ℕ}
    (hmul : ∀ z ∈ H, ∀ w ∈ H, z * w ∈ H)
    (hinv : ∀ z ∈ H, z⁻¹ ∈ H)
    (h0 : (0 : F) ∉ H)
    (hpow : ∀ z ∈ H, z ^ n = 1)
    (hcomplete : ∀ z : F, z ^ n = 1 → z ∈ H) :
    (accidents H).card = (differenceCollisionPairs H n).card := by
  classical
  apply Finset.card_bij (fun t _ => (t.a, t.c / t.b))
  · intro t ht
    have hcol := nontrivialDifferenceCollision_of_mem_accidents hmul hinv h0 ht
    rcases hcol with ⟨haH, hyH, hbH, ha1, hy1, hyx, hyinv, hrel⟩
    rw [differenceCollisionPairs, Finset.mem_filter]
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_erase.mpr ⟨ha1, haH⟩,
      Finset.mem_erase.mpr ⟨hy1, hyH⟩⟩, ?_⟩
    exact ⟨differenceSignature_eq_of_nontrivialDifferenceCollision hpow
      ⟨haH, hyH, hbH, ha1, hy1, hyx, hyinv, hrel⟩, hyx, hyinv⟩
  · intro t ht u hu hpair
    have htcol := nontrivialDifferenceCollision_of_mem_accidents hmul hinv h0 ht
    have hucol := nontrivialDifferenceCollision_of_mem_accidents hmul hinv h0 hu
    rcases htcol with ⟨_, _, _, _, hty1, _, _, htrel⟩
    rcases hucol with ⟨_, _, _, _, _huy1, _, _, hurel⟩
    have ha : t.a = u.a := congrArg Prod.fst hpair
    have hy : t.c / t.b = u.c / u.b := congrArg Prod.snd hpair
    have hySub : t.c / t.b - 1 ≠ 0 := sub_ne_zero.mpr hty1
    have hmulEq :
        t.b * (t.c / t.b - 1) = u.b * (t.c / t.b - 1) := by
      calc
        t.b * (t.c / t.b - 1) = t.a - 1 := htrel.symm
        _ = u.a - 1 := congrArg (fun z => z - 1) ha
        _ = u.b * (u.c / u.b - 1) := hurel
        _ = u.b * (t.c / t.b - 1) := by rw [hy]
    have hb : t.b = u.b := mul_right_cancel₀ hySub hmulEq
    have htSol : IsSolution t := (mem_accidents_iff.mp ht).2.2.2.1
    have huSol : IsSolution u := (mem_accidents_iff.mp hu).2.2.2.1
    have hc : t.c = u.c := by
      unfold IsSolution at htSol huSol
      calc
        t.c = t.a + t.b - 1 := by linear_combination -htSol
        _ = u.a + u.b - 1 := by rw [ha, hb]
        _ = u.c := by linear_combination huSol
    exact Triple.ext' ha hb hc
  · rintro ⟨x, y⟩ hxy
    rw [differenceCollisionPairs, Finset.mem_filter] at hxy
    rcases hxy with ⟨hsupport, hsig, hyx, hyinv⟩
    rcases Finset.mem_product.mp hsupport with ⟨hxErase, hyErase⟩
    rcases Finset.mem_erase.mp hxErase with ⟨hx1, hxH⟩
    rcases Finset.mem_erase.mp hyErase with ⟨hy1, hyH⟩
    have hySub : y - 1 ≠ 0 := sub_ne_zero.mpr hy1
    let h : F := (x - 1) / (y - 1)
    have hhpow : h ^ n = 1 := by
      change (x - 1) ^ n = (y - 1) ^ n at hsig
      dsimp [h]
      rw [div_pow, hsig, div_self (pow_ne_zero n hySub)]
    have hhH : h ∈ H := hcomplete h hhpow
    have hrel : x - 1 = h * (y - 1) := by
      dsimp [h]
      exact (div_mul_cancel₀ _ hySub).symm
    have hcol : IsNontrivialDifferenceCollision H x y h :=
      ⟨hxH, hyH, hhH, hx1, hy1, hyx, hyinv, hrel⟩
    let t : Triple F := ⟨x, h, h * y⟩
    have ht : t ∈ accidents H :=
      mem_accidents_of_nontrivialDifferenceCollision hmul hcol
    refine ⟨t, ht, ?_⟩
    have hh0 : h ≠ 0 := fun hz => h0 (hz ▸ hhH)
    apply Prod.ext
    · rfl
    · dsimp [t]
      field_simp [hh0]

/-! ## Product adapter for the G136 representation -/

/-- G136 stores a normalized triple as `((a,b),c)`. -/
def toProduct (x : Triple F) : (F × F) × F := ((x.a, x.b), x.c)

def ofProduct (x : (F × F) × F) : Triple F := ⟨x.1.1, x.1.2, x.2⟩

/-- The ANT46 structure and G136's nested-product representation are definitionally equivalent. -/
def tripleProductEquiv : Triple F ≃ (F × F) × F where
  toFun := toProduct
  invFun := ofProduct
  left_inv x := by cases x; rfl
  right_inv x := rfl

theorem toProduct_injective : Function.Injective (toProduct : Triple F → (F × F) × F) :=
  tripleProductEquiv.injective

theorem isSolution_toProduct_iff (x : Triple F) :
    IsSolution x ↔ (toProduct x).1.1 + (toProduct x).1.2 = (toProduct x).2 + 1 := by
  rfl

theorem isLawful_toProduct_iff (x : Triple F) :
    IsLawful x ↔
      (toProduct x).1.1 = 1 ∨ (toProduct x).1.2 = 1 ∨
        ((toProduct x).2 = -1 ∧ (toProduct x).1.2 = -(toProduct x).1.1) := by
  rfl

/-- Product-form copy of ANT46 accidents, matching G136's carrier representation. -/
noncomputable def productAccidents (H : Finset F) : Finset ((F × F) × F) :=
  ((H ×ˢ H) ×ˢ H).filter fun x =>
    x.1.1 + x.1.2 = x.2 + 1 ∧
      ¬ (x.1.1 = 1 ∨ x.1.2 = 1 ∨ (x.2 = -1 ∧ x.1.2 = -x.1.1))

/-- Exact Triple/product adapter at the Finset level. -/
theorem image_toProduct_accidents (H : Finset F) :
    (accidents H).image toProduct = productAccidents H := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
    rw [mem_accidents_iff] at hx
    exact Finset.mem_filter.mpr ⟨by simp [toProduct, hx.1, hx.2.1, hx.2.2.1], hx.2.2.2⟩
  · intro hp
    rw [productAccidents, Finset.mem_filter] at hp
    refine Finset.mem_image.mpr ⟨ofProduct p, ?_, rfl⟩
    rw [mem_accidents_iff]
    rcases hp with ⟨hsupport, hacc⟩
    rcases Finset.mem_product.mp hsupport with ⟨hab, hc⟩
    rcases Finset.mem_product.mp hab with ⟨ha, hb⟩
    exact ⟨ha, hb, hc, hacc⟩

theorem card_productAccidents_eq (H : Finset F) :
    (productAccidents H).card = (accidents H).card := by
  rw [← image_toProduct_accidents]
  exact Finset.card_image_of_injective _ toProduct_injective

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
#print axioms ArkLib.ProximityGap.Frontier.ANT46RungTwoAccidentOrbit.reRoot_eq_iff_cross
#print axioms ArkLib.ProximityGap.Frontier.ANT46RungTwoAccidentOrbit.card_projectiveOrbit_mul_card_baseFiber
#print axioms ArkLib.ProximityGap.Frontier.ANT46RungTwoAccidentOrbit.image_toProduct_accidents
#print axioms ArkLib.ProximityGap.Frontier.ANT46RungTwoAccidentOrbit.isAccident_reRoot
#print axioms ArkLib.ProximityGap.Frontier.ANT46RungTwoAccidentOrbit.scalar_eq_one_of_permuted_signed_of_accident
#print axioms ArkLib.ProximityGap.Frontier.ANT46RungTwoAccidentOrbit.card_projectiveFiber_eq_one_or_two_or_six_of_accident
#print axioms ArkLib.ProximityGap.Frontier.ANT46RungTwoAccidentOrbit.twelve_dvd_card_of_projective_packets
#print axioms ArkLib.ProximityGap.Frontier.ANT46RungTwoAccidentOrbit.firstPrime_twelve_dvd_card_accidents
#print axioms ArkLib.ProximityGap.Frontier.ANT46RungTwoAccidentOrbit.secondPrime_twelve_dvd_card_accidents
#print axioms ArkLib.ProximityGap.Frontier.ANT46RungTwoAccidentOrbit.twelve_le_card_accidents_of_nonempty_of_no_triple
#print axioms ArkLib.ProximityGap.Frontier.ANT46RungTwoAccidentOrbit.accidents_eq_empty_iff_differenceSignatureInjectiveModInversion
#print axioms ArkLib.ProximityGap.Frontier.ANT46RungTwoAccidentOrbit.firstPrime_accidents_eq_empty_of_differenceSignatureInjectiveModInversion
#print axioms ArkLib.ProximityGap.Frontier.ANT46RungTwoAccidentOrbit.secondPrime_accidents_eq_empty_of_differenceSignatureInjectiveModInversion
#print axioms ArkLib.ProximityGap.Frontier.ANT46RungTwoAccidentOrbit.card_accidents_eq_card_differenceCollisionPairs
