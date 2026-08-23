/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G139SidonModNegClean
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G136ProductionInstantiation

/-!
# G139: the formal Phi-injectivity bridge contract

This file isolates the upstream proof obligation for the `Phi_H` certificate route.

The computational certificate checks injectivity of

```text
Phi(r) = (g^r - 1)^n,   1 <= r <= n/2.
```

To turn that into `SidonModNeg H`, one still needs the algebraic extraction lemma:
every non-lawful additive relation in `H` produces a nontrivial collision in this
Phi window.  The theorem below packages that interface exactly.  It is not the
extraction lemma itself; it is the Lean-checked contract showing what remains.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G139PhiInjectiveSidonBridge

open ArkLib.ProximityGap.AdditiveEnergySidonModNeg
open ArkLib.ProximityGap.Frontier.G136LawfulCount
open ArkLib.ProximityGap.Frontier.G136ProductionInstantiation
open ArkLib.ProximityGap.Frontier.G139SidonModNegClean

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
/-- Algebraic core of the difference-quotient mechanism.  If a power-sum
relation can be normalized so that `g^ia = g^ic * g^r` and
`g^id = g^ib * g^s`, then the relation forces equality of the two `Phi`
values. -/
theorem phi_collision_of_power_relation
    {g : F} {n ia ib ic id r s : ℕ}
    (hgn : g ^ n = 1)
    (hr : g ^ ia = g ^ ic * g ^ r)
    (hs : g ^ id = g ^ ib * g ^ s)
    (hsum : g ^ ia + g ^ ib = g ^ ic + g ^ id) :
    (g ^ r - 1) ^ n = (g ^ s - 1) ^ n := by
  have hcore : g ^ ic * (g ^ r - 1) = g ^ ib * (g ^ s - 1) := by
    rw [hr, hs] at hsum
    linear_combination hsum
  have hpow := congrArg (fun x => x ^ n) hcore
  have hic : (g ^ ic) ^ n = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hgn, one_pow]
  have hib : (g ^ ib) ^ n = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hgn, one_pow]
  change (g ^ ic * (g ^ r - 1)) ^ n = (g ^ ib * (g ^ s - 1)) ^ n at hpow
  rw [mul_pow, mul_pow, hic, hib] at hpow
  simpa using hpow

/-- The finite certificate predicate for the half-window quotienting the forced
`r ~ -r` symmetry. -/
def PhiWindowInjective (g : F) (n : ℕ) : Prop :=
  ∀ r s : ℕ, 1 ≤ r → r ≤ n / 2 → 1 ≤ s → s ≤ n / 2 →
    (g ^ r - 1) ^ n = (g ^ s - 1) ^ n → r = s

/-- Exact order predicate used by the upstream bridge: no positive exponent
below `n` sends `g` to `1`. -/
def HasExactOrder (g : F) (n : ℕ) : Prop :=
  ∀ m : ℕ, m < n → g ^ m = 1 → m = 0

omit [Fintype F] [DecidableEq F] in
/-- Exponents may be reduced modulo an order relation `g^n = 1`. -/
theorem pow_eq_pow_mod_of_pow_eq_one
    {g : F} {n m : ℕ} (hgn : g ^ n = 1) :
    g ^ m = g ^ (m % n) := by
  calc
    g ^ m = g ^ (n * (m / n) + m % n) := by rw [Nat.div_add_mod m n]
    _ = g ^ (m % n) := by
      rw [pow_add, pow_mul, hgn, one_pow, one_mul]

omit [Fintype F] [DecidableEq F] in
/-- Under exact order, a nonzero residue modulo `n` cannot represent the unit
power. -/
theorem pow_ne_one_of_mod_ne_zero
    {g : F} {n m : ℕ} (hn0 : n ≠ 0) (hgn : g ^ n = 1)
    (hExact : HasExactOrder g n) (hm0 : m % n ≠ 0) :
    g ^ m ≠ 1 := by
  intro hmone
  have hmod_lt : m % n < n := Nat.mod_lt m (Nat.pos_of_ne_zero hn0)
  have hmod_one : g ^ (m % n) = 1 := by
    rw [← pow_eq_pow_mod_of_pow_eq_one hgn]
    exact hmone
  exact hm0 (hExact (m % n) hmod_lt hmod_one)

omit [Fintype F] [DecidableEq F] in
/-- The algebraic reason the certificate only checks a half-window: when `n` is
even and `g^n = 1`, antipodal exponents have the same `Phi` value. -/
theorem phi_antipodal_eq_of_pow_eq_one
    {g : F} {n r : ℕ} (hgn : g ^ n = 1) (heven : Even n) (hr : r ≤ n) :
    (g ^ (n - r) - 1) ^ n = (g ^ r - 1) ^ n := by
  have hmul : g ^ (n - r) * g ^ r = 1 := by
    calc
      g ^ (n - r) * g ^ r = g ^ (n - r + r) := by rw [← pow_add]
      _ = g ^ n := by rw [Nat.sub_add_cancel hr]
      _ = 1 := hgn
  have hbase : g ^ (n - r) - 1 = -(g ^ (n - r) * (g ^ r - 1)) := by
    rw [mul_sub, hmul, mul_one]
    ring
  have hroot : (g ^ (n - r)) ^ n = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hgn, one_pow]
  calc
    (g ^ (n - r) - 1) ^ n = (-(g ^ (n - r) * (g ^ r - 1))) ^ n := by
      rw [hbase]
    _ = (g ^ (n - r) * (g ^ r - 1)) ^ n := by
      rw [neg_pow, heven.neg_one_pow, one_mul]
    _ = (g ^ r - 1) ^ n := by
      rw [mul_pow, hroot, one_mul]

omit [Fintype F] [DecidableEq F] in
/-- Adding full periods to an exponent does not change its `Phi` value. -/
theorem phi_periodic_add_order
    {g : F} {n r k : ℕ} (hgn : g ^ n = 1) :
    (g ^ (r + n * k) - 1) ^ n = (g ^ r - 1) ^ n := by
  have hpow : g ^ (r + n * k) = g ^ r := by
    rw [pow_add, pow_mul, hgn, one_pow, mul_one]
  rw [hpow]

omit [Field F] [Fintype F] [DecidableEq F] in
/-- Every nonzero residue modulo an even order has a representative in the
closed half-window, up to antipode. -/
theorem exists_halfWindow_antipodal_residue
    {n m : ℕ} (heven : Even n) (hm0 : m ≠ 0) (hmn : m < n) :
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ n / 2 ∧ (m = r ∨ m = n - r) := by
  by_cases hmhalf : m ≤ n / 2
  · exact ⟨m, Nat.pos_of_ne_zero hm0, hmhalf, Or.inl rfl⟩
  · rcases heven with ⟨t, rfl⟩
    refine ⟨2 * t - m, ?_, ?_, Or.inr ?_⟩
    · omega
    · omega
    · omega

omit [Field F] [Fintype F] [DecidableEq F] in
/-- Modulo form of the half-window representative lemma.  If an exponent has
nonzero residue modulo an even order, it is congruent to a unique-side
half-window representative up to antipode. -/
theorem exists_halfWindow_antipodal_mod
    {n m : ℕ} (hn0 : n ≠ 0) (heven : Even n) (hm0 : m % n ≠ 0) :
    ∃ r k : ℕ, 1 ≤ r ∧ r ≤ n / 2 ∧
      (m = r + n * k ∨ m = (n - r) + n * k) := by
  have hmod_lt : m % n < n := Nat.mod_lt m (Nat.pos_of_ne_zero hn0)
  rcases exists_halfWindow_antipodal_residue (n := n) (m := m % n) heven hm0
    hmod_lt with ⟨r, hr1, hrh, hrResidue | hrResidue⟩
  · refine ⟨r, m / n, hr1, hrh, Or.inl ?_⟩
    calc
      m = n * (m / n) + m % n := (Nat.div_add_mod m n).symm
      _ = r + n * (m / n) := by omega
  · refine ⟨r, m / n, hr1, hrh, Or.inr ?_⟩
    calc
      m = n * (m / n) + m % n := (Nat.div_add_mod m n).symm
      _ = (n - r) + n * (m / n) := by omega

/-- The remaining algebraic extraction obligation: any non-lawful additive relation
among elements of `H` must yield a genuinely distinct `Phi` collision in the
certified half-window. -/
def AdditiveRelationProducesPhiCollision (H : Finset F) (g : F) (n : ℕ) : Prop :=
  ∀ a ∈ H, ∀ b ∈ H, ∀ c ∈ H, ∀ d ∈ H,
    a + b = c + d →
    ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c) ∨ a + b = 0) →
      ∃ r s : ℕ,
        1 ≤ r ∧ r ≤ n / 2 ∧ 1 ≤ s ∧ s ≤ n / 2 ∧ r ≠ s ∧
          (g ^ r - 1) ^ n = (g ^ s - 1) ^ n

/-- Exponent-level version of the remaining extraction obligation for a root set
`{g^k : k < n}`. -/
def PowerRelationProducesPhiCollision (g : F) (n : ℕ) : Prop :=
  ∀ ia ib ic id : ℕ, ia < n → ib < n → ic < n → id < n →
    g ^ ia + g ^ ib = g ^ ic + g ^ id →
    ¬ ((g ^ ia = g ^ ic ∧ g ^ ib = g ^ id) ∨
        (g ^ ia = g ^ id ∧ g ^ ib = g ^ ic) ∨ g ^ ia + g ^ ib = 0) →
      ∃ r s : ℕ,
        1 ≤ r ∧ r ≤ n / 2 ∧ 1 ≤ s ∧ s ≤ n / 2 ∧ r ≠ s ∧
          (g ^ r - 1) ^ n = (g ^ s - 1) ^ n

set_option linter.unusedVariables false in
/-- Raw difference-factor witnesses before reducing to the certified half-window. -/
def PowerRelationHasRawDifferenceFactors (g : F) (n : ℕ) : Prop :=
  ∀ ia ib ic id : ℕ, ∃ r s : ℕ,
    g ^ ia = g ^ ic * g ^ r ∧ g ^ id = g ^ ib * g ^ s

omit [Fintype F] [DecidableEq F] in
/-- If `g^n = 1`, raw difference factors always exist.  The hard part is not
their existence, but folding them into distinct representatives in `1..n/2`. -/
theorem powerRelationHasRawDifferenceFactors_of_pow_eq_one
    {g : F} {n : ℕ} (hn0 : n ≠ 0) (hgn : g ^ n = 1) :
    PowerRelationHasRawDifferenceFactors g n := by
  intro ia ib ic id
  refine ⟨ia + n * (ic + 1) - ic, id + n * (ib + 1) - ib, ?_, ?_⟩
  · symm
    have hic_le : ic ≤ n * (ic + 1) := by
      calc
        ic ≤ ic + 1 := Nat.le_succ ic
        _ ≤ n * (ic + 1) := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hn0)
    calc
      g ^ ic * g ^ (ia + n * (ic + 1) - ic)
          = g ^ (ic + (ia + n * (ic + 1) - ic)) := by rw [← pow_add]
      _ = g ^ (ia + n * (ic + 1)) := by
        congr 1
        omega
      _ = g ^ ia := by
        rw [pow_add, pow_mul, hgn, one_pow, mul_one]
  · symm
    have hib_le : ib ≤ n * (ib + 1) := by
      calc
        ib ≤ ib + 1 := Nat.le_succ ib
        _ ≤ n * (ib + 1) := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hn0)
    calc
      g ^ ib * g ^ (id + n * (ib + 1) - ib)
          = g ^ (ib + (id + n * (ib + 1) - ib)) := by rw [← pow_add]
      _ = g ^ (id + n * (ib + 1)) := by
        congr 1
        omega
      _ = g ^ id := by
        rw [pow_add, pow_mul, hgn, one_pow, mul_one]

omit [Fintype F] [DecidableEq F] in
/-- In a non-lawful relation, neither raw difference factor can be congruent to
zero modulo the order.  A zero raw difference immediately forces the identical
lawful pairing. -/
theorem rawDifferenceFactorResidues_ne_zero_of_nonlawful
    {g : F} {n ia ib ic id r₀ s₀ : ℕ} (hgn : g ^ n = 1)
    (hr₀ : g ^ ia = g ^ ic * g ^ r₀)
    (hs₀ : g ^ id = g ^ ib * g ^ s₀)
    (hsum : g ^ ia + g ^ ib = g ^ ic + g ^ id)
    (hnonlawful :
      ¬ ((g ^ ia = g ^ ic ∧ g ^ ib = g ^ id) ∨
          (g ^ ia = g ^ id ∧ g ^ ib = g ^ ic) ∨ g ^ ia + g ^ ib = 0)) :
    r₀ % n ≠ 0 ∧ s₀ % n ≠ 0 := by
  constructor
  · intro hrzero
    have hrpow : g ^ r₀ = 1 := by
      have hr₀_eq : r₀ = n * (r₀ / n) := by
        calc
          r₀ = n * (r₀ / n) + r₀ % n := (Nat.div_add_mod r₀ n).symm
          _ = n * (r₀ / n) := by omega
      rw [hr₀_eq, pow_mul, hgn, one_pow]
    have hiaic : g ^ ia = g ^ ic := by
      rw [hr₀, hrpow, mul_one]
    have hibid : g ^ ib = g ^ id := by
      rw [hiaic] at hsum
      exact add_left_cancel hsum
    exact hnonlawful (Or.inl ⟨hiaic, hibid⟩)
  · intro hszero
    have hspow : g ^ s₀ = 1 := by
      have hs₀_eq : s₀ = n * (s₀ / n) := by
        calc
          s₀ = n * (s₀ / n) + s₀ % n := (Nat.div_add_mod s₀ n).symm
          _ = n * (s₀ / n) := by omega
      rw [hs₀_eq, pow_mul, hgn, one_pow]
    have hidib : g ^ id = g ^ ib := by
      rw [hs₀, hspow, mul_one]
    have hiaic : g ^ ia = g ^ ic := by
      rw [hidib] at hsum
      exact add_right_cancel hsum
    exact hnonlawful (Or.inl ⟨hiaic, hidib.symm⟩)

omit [Fintype F] [DecidableEq F] in
/-- If the two raw difference factors are equal and nontrivial, the additive
relation is the swapped lawful pairing. -/
theorem swapped_lawful_of_same_rawDifferenceFactor
    {g : F} {ia ib ic id r₀ s₀ : ℕ}
    (hr₀ : g ^ ia = g ^ ic * g ^ r₀)
    (hs₀ : g ^ id = g ^ ib * g ^ s₀)
    (hsum : g ^ ia + g ^ ib = g ^ ic + g ^ id)
    (hsame : g ^ r₀ = g ^ s₀) (hrne : g ^ r₀ ≠ 1) :
    g ^ ia = g ^ id ∧ g ^ ib = g ^ ic := by
  have hcore : g ^ ic * (g ^ r₀ - 1) = g ^ ib * (g ^ s₀ - 1) := by
    rw [hr₀, hs₀] at hsum
    linear_combination hsum
  rw [← hsame] at hcore
  have hfactor_ne : g ^ r₀ - 1 ≠ 0 := sub_ne_zero.mpr hrne
  have hicib : g ^ ic = g ^ ib := mul_right_cancel₀ hfactor_ne hcore
  constructor
  · rw [hr₀, hs₀, hicib, hsame]
  · exact hicib.symm

omit [Fintype F] [DecidableEq F] in
/-- If the two raw difference factors are antipodal and nontrivial, the
relation is the zero-sum lawful family. -/
theorem zeroSum_of_antipodal_rawDifferenceFactor
    {g : F} {ia ib ic id r₀ s₀ : ℕ}
    (hr₀ : g ^ ia = g ^ ic * g ^ r₀)
    (hs₀ : g ^ id = g ^ ib * g ^ s₀)
    (hsum : g ^ ia + g ^ ib = g ^ ic + g ^ id)
    (hinv : g ^ r₀ * g ^ s₀ = 1) (hrne : g ^ r₀ ≠ 1) :
    g ^ ia + g ^ ib = 0 := by
  rw [hr₀, hs₀] at hsum
  have hfactor_ne : g ^ r₀ - 1 ≠ 0 := sub_ne_zero.mpr hrne
  have hcore : g ^ ic * (g ^ r₀ - 1) = g ^ ib * (g ^ s₀ - 1) := by
    linear_combination hsum
  have hmul := congrArg (fun x => x * g ^ r₀) hcore
  have hright : (g ^ s₀ - 1) * g ^ r₀ = -(g ^ r₀ - 1) := by
    rw [sub_mul, mul_comm (g ^ s₀) (g ^ r₀), hinv, one_mul]
    ring
  have hmul' : g ^ ic * (g ^ r₀ - 1) * g ^ r₀ =
      g ^ ib * ((g ^ s₀ - 1) * g ^ r₀) := by
    calc
      g ^ ic * (g ^ r₀ - 1) * g ^ r₀
          = (g ^ ic * (g ^ r₀ - 1)) * g ^ r₀ := by ring
      _ = (g ^ ib * (g ^ s₀ - 1)) * g ^ r₀ := hmul
      _ = g ^ ib * ((g ^ s₀ - 1) * g ^ r₀) := by ring
  have hmul'' : g ^ ic * (g ^ r₀ - 1) * g ^ r₀ =
      -g ^ ib * (g ^ r₀ - 1) := by
    rw [hmul', hright]
    ring
  have hzero_factor : (g ^ ic * g ^ r₀ + g ^ ib) * (g ^ r₀ - 1) = 0 := by
    calc
      (g ^ ic * g ^ r₀ + g ^ ib) * (g ^ r₀ - 1)
          = g ^ ic * (g ^ r₀ - 1) * g ^ r₀ + g ^ ib * (g ^ r₀ - 1) := by
            ring
      _ = 0 := by rw [hmul'']; ring
  have hzero : g ^ ic * g ^ r₀ + g ^ ib = 0 := by
    exact (mul_eq_zero.mp hzero_factor).resolve_right hfactor_ne
  simpa [hr₀] using hzero

/- Folding raw difference factors into the certified half-window should preserve
the `Phi` values, not the raw quotient identities.  Replacing a raw exponent by
its antipodal representative generally changes `g^r`, but leaves `(g^r - 1)^n`
unchanged under the even-order roots-of-unity hypotheses used by the certificate
route. -/
def RawDifferenceFactorsFoldToPhiWindow (g : F) (n : ℕ) : Prop :=
  ∀ ia ib ic id r₀ s₀ : ℕ, ia < n → ib < n → ic < n → id < n →
    g ^ ia + g ^ ib = g ^ ic + g ^ id →
    ¬ ((g ^ ia = g ^ ic ∧ g ^ ib = g ^ id) ∨
        (g ^ ia = g ^ id ∧ g ^ ib = g ^ ic) ∨ g ^ ia + g ^ ib = 0) →
    g ^ ia = g ^ ic * g ^ r₀ → g ^ id = g ^ ib * g ^ s₀ →
      ∃ r s : ℕ,
        1 ≤ r ∧ r ≤ n / 2 ∧ 1 ≤ s ∧ s ≤ n / 2 ∧ r ≠ s ∧
          (g ^ r - 1) ^ n = (g ^ r₀ - 1) ^ n ∧
            (g ^ s - 1) ^ n = (g ^ s₀ - 1) ^ n

/-- `r` represents the antipodal residue class of `m` modulo `n` in the
certified half-window. -/
def AntipodalResidueRep (n m r : ℕ) : Prop :=
  1 ≤ r ∧ r ≤ n / 2 ∧ (m % n = r ∨ m % n = n - r)

set_option linter.unusedVariables false in
/- The narrow remaining obligation: for a non-lawful raw-factor relation, the
two raw difference exponents have distinct antipodal residue classes. -/
def RawDifferenceFactorsHaveDistinctAntipodalResidues (g : F) (n : ℕ) : Prop :=
  ∀ ia ib ic id r₀ s₀ : ℕ, ia < n → ib < n → ic < n → id < n →
    g ^ ia + g ^ ib = g ^ ic + g ^ id →
    ¬ ((g ^ ia = g ^ ic ∧ g ^ ib = g ^ id) ∨
        (g ^ ia = g ^ id ∧ g ^ ib = g ^ ic) ∨ g ^ ia + g ^ ib = 0) →
    g ^ ia = g ^ ic * g ^ r₀ → g ^ id = g ^ ib * g ^ s₀ →
      ∀ r s : ℕ, AntipodalResidueRep n r₀ r → AntipodalResidueRep n s₀ s → r ≠ s

omit [Fintype F] [DecidableEq F] in
/-- Exact order closes the remaining distinct-antipodal-residue obligation. -/
theorem rawDifferenceFactorsHaveDistinctAntipodalResidues_of_exactOrder
    {g : F} {n : ℕ} (hn0 : n ≠ 0) (hgn : g ^ n = 1)
    (hExact : HasExactOrder g n) :
    RawDifferenceFactorsHaveDistinctAntipodalResidues g n := by
  intro ia ib ic id r₀ s₀ _hia _hib _hic _hid hsum hnonlawful hr₀ hs₀ r s hrRep hsRep
    hrs
  rcases rawDifferenceFactorResidues_ne_zero_of_nonlawful hgn hr₀ hs₀ hsum hnonlawful with
    ⟨hrnz, _hsnz⟩
  have hrne : g ^ r₀ ≠ 1 := pow_ne_one_of_mod_ne_zero hn0 hgn hExact hrnz
  have hrpow : g ^ r₀ = g ^ (r₀ % n) := pow_eq_pow_mod_of_pow_eq_one hgn
  have hspow : g ^ s₀ = g ^ (s₀ % n) := pow_eq_pow_mod_of_pow_eq_one hgn
  rcases hrRep with ⟨_hr1, hrh, hrResidue⟩
  rcases hsRep with ⟨_hs1, _hsh, hsResidue⟩
  subst s
  have hr_le_n : r ≤ n := le_trans hrh (Nat.div_le_self n 2)
  have hantipodal_mul : g ^ r * g ^ (n - r) = 1 := by
    calc
      g ^ r * g ^ (n - r) = g ^ (r + (n - r)) := by rw [← pow_add]
      _ = g ^ n := by rw [Nat.add_sub_of_le hr_le_n]
      _ = 1 := hgn
  rcases hrResidue with hrResidue | hrResidue <;>
    rcases hsResidue with hsResidue | hsResidue
  · have hsame : g ^ r₀ = g ^ s₀ := by
      rw [hrpow, hspow, hrResidue, hsResidue]
    rcases swapped_lawful_of_same_rawDifferenceFactor hr₀ hs₀ hsum hsame hrne with
      ⟨hiaid, hibic⟩
    exact hnonlawful (Or.inr (Or.inl ⟨hiaid, hibic⟩))
  · have hinv : g ^ r₀ * g ^ s₀ = 1 := by
      rw [hrpow, hspow, hrResidue, hsResidue]
      exact hantipodal_mul
    exact hnonlawful (Or.inr (Or.inr
      (zeroSum_of_antipodal_rawDifferenceFactor hr₀ hs₀ hsum hinv hrne)))
  · have hinv : g ^ r₀ * g ^ s₀ = 1 := by
      rw [hrpow, hspow, hrResidue, hsResidue]
      rw [mul_comm]
      exact hantipodal_mul
    exact hnonlawful (Or.inr (Or.inr
      (zeroSum_of_antipodal_rawDifferenceFactor hr₀ hs₀ hsum hinv hrne)))
  · have hsame : g ^ r₀ = g ^ s₀ := by
      rw [hrpow, hspow, hrResidue, hsResidue]
    rcases swapped_lawful_of_same_rawDifferenceFactor hr₀ hs₀ hsum hsame hrne with
      ⟨hiaid, hibic⟩
    exact hnonlawful (Or.inr (Or.inl ⟨hiaid, hibic⟩))

set_option linter.unusedVariables false in
/- The same folding obligation stated only in terms of residues modulo `n`. -/
def RawDifferenceFactorsFoldToAntipodalResidues (g : F) (n : ℕ) : Prop :=
  ∀ ia ib ic id r₀ s₀ : ℕ, ia < n → ib < n → ic < n → id < n →
    g ^ ia + g ^ ib = g ^ ic + g ^ id →
    ¬ ((g ^ ia = g ^ ic ∧ g ^ ib = g ^ id) ∨
        (g ^ ia = g ^ id ∧ g ^ ib = g ^ ic) ∨ g ^ ia + g ^ ib = 0) →
    g ^ ia = g ^ ic * g ^ r₀ → g ^ id = g ^ ib * g ^ s₀ →
      ∃ r s : ℕ,
        1 ≤ r ∧ r ≤ n / 2 ∧ 1 ≤ s ∧ s ≤ n / 2 ∧ r ≠ s ∧
          (r₀ % n = r ∨ r₀ % n = n - r) ∧
            (s₀ % n = s ∨ s₀ % n = n - s)

omit [Fintype F] [DecidableEq F] in
/-- Nonzero raw residues plus distinct antipodal classes supply concrete
antipodal residue representatives. -/
theorem rawDifferenceFactorsFoldToAntipodalResidues_of_distinct
    {g : F} {n : ℕ} (hn0 : n ≠ 0) (hgn : g ^ n = 1) (heven : Even n)
    (hDistinct : RawDifferenceFactorsHaveDistinctAntipodalResidues g n) :
    RawDifferenceFactorsFoldToAntipodalResidues g n := by
  intro ia ib ic id r₀ s₀ hia hib hic hid hsum hnonlawful hr₀ hs₀
  rcases rawDifferenceFactorResidues_ne_zero_of_nonlawful hgn hr₀ hs₀ hsum hnonlawful with
    ⟨hrnz, hsnz⟩
  have hrmod_lt : r₀ % n < n := Nat.mod_lt r₀ (Nat.pos_of_ne_zero hn0)
  have hsmod_lt : s₀ % n < n := Nat.mod_lt s₀ (Nat.pos_of_ne_zero hn0)
  rcases exists_halfWindow_antipodal_residue (n := n) (m := r₀ % n) heven hrnz
    hrmod_lt with ⟨r, hr1, hrh, hrResidue⟩
  rcases exists_halfWindow_antipodal_residue (n := n) (m := s₀ % n) heven hsnz
    hsmod_lt with ⟨s, hs1, hsh, hsResidue⟩
  have hrRep : AntipodalResidueRep n r₀ r := ⟨hr1, hrh, hrResidue⟩
  have hsRep : AntipodalResidueRep n s₀ s := ⟨hs1, hsh, hsResidue⟩
  exact ⟨r, s, hr1, hrh, hs1, hsh,
    hDistinct ia ib ic id r₀ s₀ hia hib hic hid hsum hnonlawful hr₀ hs₀ r s hrRep
      hsRep,
    hrResidue, hsResidue⟩

set_option linter.unusedVariables false in
/- The more concrete remaining arithmetic obligation: the raw factors can be
folded into distinct half-window representatives up to period and antipode. -/
def RawDifferenceFactorsFoldToResidueWindow (g : F) (n : ℕ) : Prop :=
  ∀ ia ib ic id r₀ s₀ : ℕ, ia < n → ib < n → ic < n → id < n →
    g ^ ia + g ^ ib = g ^ ic + g ^ id →
    ¬ ((g ^ ia = g ^ ic ∧ g ^ ib = g ^ id) ∨
        (g ^ ia = g ^ id ∧ g ^ ib = g ^ ic) ∨ g ^ ia + g ^ ib = 0) →
    g ^ ia = g ^ ic * g ^ r₀ → g ^ id = g ^ ib * g ^ s₀ →
      ∃ r s kr ks : ℕ,
        1 ≤ r ∧ r ≤ n / 2 ∧ 1 ≤ s ∧ s ≤ n / 2 ∧ r ≠ s ∧
          (r₀ = r + n * kr ∨ r₀ = (n - r) + n * kr) ∧
            (s₀ = s + n * ks ∨ s₀ = (n - s) + n * ks)

omit [Fintype F] [DecidableEq F] in
/-- Residue-level folding supplies the period/antipode representatives needed
by the bridge. -/
theorem rawDifferenceFactorsFoldToResidueWindow_of_antipodalResidues
    {g : F} {n : ℕ}
    (hResidues : RawDifferenceFactorsFoldToAntipodalResidues g n) :
    RawDifferenceFactorsFoldToResidueWindow g n := by
  intro ia ib ic id r₀ s₀ hia hib hic hid hsum hnonlawful hr₀ hs₀
  rcases hResidues ia ib ic id r₀ s₀ hia hib hic hid hsum hnonlawful hr₀ hs₀ with
    ⟨r, s, hr1, hrh, hs1, hsh, hrs, hrResidue, hsResidue⟩
  refine ⟨r, s, r₀ / n, s₀ / n, hr1, hrh, hs1, hsh, hrs, ?_, ?_⟩
  · rcases hrResidue with hrResidue | hrResidue
    · refine Or.inl ?_
      calc
        r₀ = n * (r₀ / n) + r₀ % n := (Nat.div_add_mod r₀ n).symm
        _ = r + n * (r₀ / n) := by omega
    · refine Or.inr ?_
      calc
        r₀ = n * (r₀ / n) + r₀ % n := (Nat.div_add_mod r₀ n).symm
        _ = (n - r) + n * (r₀ / n) := by omega
  · rcases hsResidue with hsResidue | hsResidue
    · refine Or.inl ?_
      calc
        s₀ = n * (s₀ / n) + s₀ % n := (Nat.div_add_mod s₀ n).symm
        _ = s + n * (s₀ / n) := by omega
    · refine Or.inr ?_
      calc
        s₀ = n * (s₀ / n) + s₀ % n := (Nat.div_add_mod s₀ n).symm
        _ = (n - s) + n * (s₀ / n) := by omega

omit [Fintype F] [DecidableEq F] in
/-- Period/antipode residue-window folding implies the `Phi`-value folding
contract. -/
theorem rawDifferenceFactorsFoldToPhiWindow_of_residueWindow
    {g : F} {n : ℕ} (hgn : g ^ n = 1) (heven : Even n)
    (hResidue : RawDifferenceFactorsFoldToResidueWindow g n) :
    RawDifferenceFactorsFoldToPhiWindow g n := by
  intro ia ib ic id r₀ s₀ hia hib hic hid hsum hnonlawful hr₀ hs₀
  rcases hResidue ia ib ic id r₀ s₀ hia hib hic hid hsum hnonlawful hr₀ hs₀ with
    ⟨r, s, kr, ks, hr1, hrh, hs1, hsh, hrs, hrResidue, hsResidue⟩
  refine ⟨r, s, hr1, hrh, hs1, hsh, hrs, ?_, ?_⟩
  · have hr_le_n : r ≤ n := le_trans hrh (Nat.div_le_self n 2)
    rcases hrResidue with hrResidue | hrResidue
    · subst r₀
      exact (phi_periodic_add_order (g := g) (n := n) (r := r) (k := kr) hgn).symm
    · subst r₀
      calc
        (g ^ r - 1) ^ n = (g ^ (n - r) - 1) ^ n :=
          (phi_antipodal_eq_of_pow_eq_one (g := g) (n := n) (r := r) hgn heven
            hr_le_n).symm
        _ = (g ^ (n - r + n * kr) - 1) ^ n :=
          (phi_periodic_add_order (g := g) (n := n) (r := n - r) (k := kr) hgn).symm
  · have hs_le_n : s ≤ n := le_trans hsh (Nat.div_le_self n 2)
    rcases hsResidue with hsResidue | hsResidue
    · subst s₀
      exact (phi_periodic_add_order (g := g) (n := n) (r := s) (k := ks) hgn).symm
    · subst s₀
      calc
        (g ^ s - 1) ^ n = (g ^ (n - s) - 1) ^ n :=
          (phi_antipodal_eq_of_pow_eq_one (g := g) (n := n) (r := s) hgn heven
            hs_le_n).symm
        _ = (g ^ (n - s + n * ks) - 1) ^ n :=
          (phi_periodic_add_order (g := g) (n := n) (r := n - s) (k := ks) hgn).symm

omit [Fintype F] [DecidableEq F] in
/-- Raw factors plus `Phi`-value half-window folding give the nontrivial `Phi`
collision consumed by the downstream bridge. -/
theorem powerRelationProducesPhiCollision_of_rawFactors_and_phiFold
    {g : F} {n : ℕ} (hgn : g ^ n = 1)
    (hRaw : PowerRelationHasRawDifferenceFactors g n)
    (hFold : RawDifferenceFactorsFoldToPhiWindow g n) :
    PowerRelationProducesPhiCollision g n := by
  intro ia ib ic id hia hib hic hid hsum hnonlawful
  rcases hRaw ia ib ic id with ⟨r₀, s₀, hr₀, hs₀⟩
  have hrawPhi : (g ^ r₀ - 1) ^ n = (g ^ s₀ - 1) ^ n :=
    phi_collision_of_power_relation hgn hr₀ hs₀ hsum
  rcases hFold ia ib ic id r₀ s₀ hia hib hic hid hsum hnonlawful hr₀ hs₀ with
    ⟨r, s, hr1, hrh, hs1, hsh, hrs, hrfold, hsfold⟩
  refine ⟨r, s, hr1, hrh, hs1, hsh, hrs, ?_⟩
  calc
    (g ^ r - 1) ^ n = (g ^ r₀ - 1) ^ n := hrfold
    _ = (g ^ s₀ - 1) ^ n := hrawPhi
    _ = (g ^ s - 1) ^ n := hsfold.symm

omit [Fintype F] [DecidableEq F] in
/-- With `g^n = 1`, the only remaining upstream lemma is the half-window folding
of raw difference factors at the `Phi`-value level. -/
theorem powerRelationProducesPhiCollision_of_pow_eq_one_and_phiFold
    {g : F} {n : ℕ} (hn0 : n ≠ 0) (hgn : g ^ n = 1)
    (hFold : RawDifferenceFactorsFoldToPhiWindow g n) :
    PowerRelationProducesPhiCollision g n :=
  powerRelationProducesPhiCollision_of_rawFactors_and_phiFold hgn
    (powerRelationHasRawDifferenceFactors_of_pow_eq_one hn0 hgn) hFold

omit [Fintype F] [DecidableEq F] in
/-- Concrete residue-window version of the exponent-level `Phi` collision
bridge. -/
theorem powerRelationProducesPhiCollision_of_pow_eq_one_and_residueWindow
    {g : F} {n : ℕ} (hn0 : n ≠ 0) (hgn : g ^ n = 1) (heven : Even n)
    (hResidue : RawDifferenceFactorsFoldToResidueWindow g n) :
    PowerRelationProducesPhiCollision g n :=
  powerRelationProducesPhiCollision_of_pow_eq_one_and_phiFold hn0 hgn
    (rawDifferenceFactorsFoldToPhiWindow_of_residueWindow hgn heven hResidue)

omit [Fintype F] [DecidableEq F] in
/-- Antipodal residue representatives are enough for the exponent-level `Phi`
collision bridge. -/
theorem powerRelationProducesPhiCollision_of_pow_eq_one_and_antipodalResidues
    {g : F} {n : ℕ} (hn0 : n ≠ 0) (hgn : g ^ n = 1) (heven : Even n)
    (hResidues : RawDifferenceFactorsFoldToAntipodalResidues g n) :
    PowerRelationProducesPhiCollision g n :=
  powerRelationProducesPhiCollision_of_pow_eq_one_and_residueWindow hn0 hgn heven
    (rawDifferenceFactorsFoldToResidueWindow_of_antipodalResidues hResidues)

omit [Fintype F] [DecidableEq F] in
/-- Distinct antipodal residue classes are the final exponent-level obstruction
needed to force a `Phi` collision. -/
theorem powerRelationProducesPhiCollision_of_pow_eq_one_and_distinctAntipodalResidues
    {g : F} {n : ℕ} (hn0 : n ≠ 0) (hgn : g ^ n = 1) (heven : Even n)
    (hDistinct : RawDifferenceFactorsHaveDistinctAntipodalResidues g n) :
    PowerRelationProducesPhiCollision g n :=
  powerRelationProducesPhiCollision_of_pow_eq_one_and_antipodalResidues hn0 hgn heven
    (rawDifferenceFactorsFoldToAntipodalResidues_of_distinct hn0 hgn heven hDistinct)

set_option linter.unusedFintypeInType false in
/-- For an actual roots-of-unity Finset, the element-level bridge follows from
the exponent-level extraction obligation. -/
theorem additiveRelationProducesPhiCollision_rootsFinset
    {g : F} {n : ℕ} (hPower : PowerRelationProducesPhiCollision g n) :
    AdditiveRelationProducesPhiCollision (rootsFinset g n) g n := by
  intro a ha b hb c hc d hd hsum hnonlawful
  rw [mem_rootsFinset_iff] at ha hb hc hd
  obtain ⟨ia, hia, rfl⟩ := ha
  obtain ⟨ib, hib, rfl⟩ := hb
  obtain ⟨ic, hic, rfl⟩ := hc
  obtain ⟨id, hid, rfl⟩ := hd
  exact hPower ia ib ic id hia hib hic hid hsum hnonlawful

omit [Fintype F] [DecidableEq F] in
/-- If every non-lawful additive relation produces a nontrivial `Phi` collision,
then `Phi` injectivity on the certificate window implies `SidonModNeg`. -/
theorem sidonModNeg_of_phiWindowInjective
    {H : Finset F} {g : F} {n : ℕ}
    (hExtract : AdditiveRelationProducesPhiCollision H g n)
    (hPhi : PhiWindowInjective g n) :
    SidonModNeg H := by
  intro a ha b hb c hc d hd hsum
  by_cases hgood : (a = c ∧ b = d) ∨ (a = d ∧ b = c) ∨ a + b = 0
  · exact hgood
  · rcases hExtract a ha b hb c hc d hd hsum hgood with
      ⟨r, s, hr1, hrh, hs1, hsh, hrs, hphi⟩
    exact False.elim (hrs (hPhi r s hr1 hrh hs1 hsh hphi))

omit [Fintype F] in
/-- Combined downstream form: the `Phi` window contract plus injectivity certifies
zero normalized G139 accidents. -/
theorem accidents_card_eq_zero_of_phiWindowInjective
    {H : Finset F} {g : F} {n : ℕ} (h1 : (1 : F) ∈ H)
    (hExtract : AdditiveRelationProducesPhiCollision H g n)
    (hPhi : PhiWindowInjective g n) :
    (accidents H).card = 0 :=
  accidents_card_eq_zero_of_sidonModNeg h1
    (sidonModNeg_of_phiWindowInjective hExtract hPhi)

set_option linter.unusedFintypeInType false in
/-- Roots-of-unity specialization: an exponent-level extraction lemma plus the
finite `Phi` injectivity certificate is enough to certify zero normalized G139
accidents. -/
theorem accidents_card_eq_zero_rootsFinset_of_phiWindowInjective
    {g : F} {n : ℕ} (h1 : (1 : F) ∈ rootsFinset g n)
    (hPower : PowerRelationProducesPhiCollision g n)
    (hPhi : PhiWindowInjective g n) :
    (accidents (rootsFinset g n)).card = 0 :=
  accidents_card_eq_zero_of_phiWindowInjective h1
    (additiveRelationProducesPhiCollision_rootsFinset hPower) hPhi

set_option linter.unusedFintypeInType false in
/-- Fully factored bridge: root-set raw-factor folding plus finite `Phi`
injectivity certifies zero normalized G139 accidents. -/
theorem accidents_card_eq_zero_rootsFinset_of_phiFold
    {g : F} {n : ℕ} (h1 : (1 : F) ∈ rootsFinset g n) (hgn : g ^ n = 1)
    (hn0 : n ≠ 0) (hFold : RawDifferenceFactorsFoldToPhiWindow g n)
    (hPhi : PhiWindowInjective g n) :
    (accidents (rootsFinset g n)).card = 0 :=
  accidents_card_eq_zero_rootsFinset_of_phiWindowInjective h1
    (powerRelationProducesPhiCollision_of_pow_eq_one_and_phiFold hn0 hgn hFold) hPhi

set_option linter.unusedFintypeInType false in
/-- Fully factored bridge with the remaining obligation reduced to residue and
antipode selection in the half-window. -/
theorem accidents_card_eq_zero_rootsFinset_of_residueWindow
    {g : F} {n : ℕ} (h1 : (1 : F) ∈ rootsFinset g n) (hgn : g ^ n = 1)
    (hn0 : n ≠ 0) (heven : Even n)
    (hResidue : RawDifferenceFactorsFoldToResidueWindow g n)
    (hPhi : PhiWindowInjective g n) :
    (accidents (rootsFinset g n)).card = 0 :=
  accidents_card_eq_zero_rootsFinset_of_phiWindowInjective h1
    (powerRelationProducesPhiCollision_of_pow_eq_one_and_residueWindow hn0 hgn heven
      hResidue) hPhi

set_option linter.unusedFintypeInType false in
/-- Fully factored bridge with the remaining obligation reduced to distinct
antipodal residue classes for the raw factors. -/
theorem accidents_card_eq_zero_rootsFinset_of_antipodalResidues
    {g : F} {n : ℕ} (h1 : (1 : F) ∈ rootsFinset g n) (hgn : g ^ n = 1)
    (hn0 : n ≠ 0) (heven : Even n)
    (hResidues : RawDifferenceFactorsFoldToAntipodalResidues g n)
    (hPhi : PhiWindowInjective g n) :
    (accidents (rootsFinset g n)).card = 0 :=
  accidents_card_eq_zero_rootsFinset_of_phiWindowInjective h1
    (powerRelationProducesPhiCollision_of_pow_eq_one_and_antipodalResidues hn0 hgn
      heven hResidues) hPhi

set_option linter.unusedFintypeInType false in
/-- Final bridge contract: if non-lawful raw factors always have
distinct antipodal residue classes, then the finite `Phi` certificate proves
there are no normalized G139 accidents. -/
theorem accidents_card_eq_zero_rootsFinset_of_distinctAntipodalResidues
    {g : F} {n : ℕ} (h1 : (1 : F) ∈ rootsFinset g n) (hgn : g ^ n = 1)
    (hn0 : n ≠ 0) (heven : Even n)
    (hDistinct : RawDifferenceFactorsHaveDistinctAntipodalResidues g n)
    (hPhi : PhiWindowInjective g n) :
    (accidents (rootsFinset g n)).card = 0 :=
  accidents_card_eq_zero_rootsFinset_of_phiWindowInjective h1
    (powerRelationProducesPhiCollision_of_pow_eq_one_and_distinctAntipodalResidues
      hn0 hgn heven hDistinct) hPhi

set_option linter.unusedFintypeInType false in
/-- Closed Sidon bridge for roots of unity: exact order plus finite `Phi`
injectivity certifies `SidonModNeg` for the generated root set. -/
theorem sidonModNeg_rootsFinset_of_exactOrder_phiWindowInjective
    {g : F} {n : ℕ} (hgn : g ^ n = 1) (hn0 : n ≠ 0) (heven : Even n)
    (hExact : HasExactOrder g n) (hPhi : PhiWindowInjective g n) :
    SidonModNeg (rootsFinset g n) :=
  sidonModNeg_of_phiWindowInjective
    (additiveRelationProducesPhiCollision_rootsFinset
      (powerRelationProducesPhiCollision_of_pow_eq_one_and_distinctAntipodalResidues
        hn0 hgn heven
        (rawDifferenceFactorsHaveDistinctAntipodalResidues_of_exactOrder hn0 hgn
          hExact)))
    hPhi

set_option linter.unusedFintypeInType false in
/-- Closed upstream bridge: exact order plus finite `Phi` injectivity certifies
zero normalized G139 accidents for the generated root set. -/
theorem accidents_card_eq_zero_rootsFinset_of_exactOrder_phiWindowInjective
    {g : F} {n : ℕ} (h1 : (1 : F) ∈ rootsFinset g n) (hgn : g ^ n = 1)
    (hn0 : n ≠ 0) (heven : Even n) (hExact : HasExactOrder g n)
    (hPhi : PhiWindowInjective g n) :
    (accidents (rootsFinset g n)).card = 0 :=
  accidents_card_eq_zero_of_sidonModNeg h1
    (sidonModNeg_rootsFinset_of_exactOrder_phiWindowInjective hgn hn0 heven hExact hPhi)

set_option linter.unusedFintypeInType false in
/-- A `Phi` collision produces a root-of-unity additive relation.  This is the
reverse algebraic direction: equality of `n`th powers says the quotient
`(g^r - 1)/(g^s - 1)` is itself an `n`th root of unity. -/
theorem exists_root_relation_of_phi_collision
    {g : F} {n r s : ℕ} (hn0 : n ≠ 0) (hprim : IsPrimitiveRoot g n)
    (hs1 : 1 ≤ s) (hsh : s ≤ n / 2)
    (hphi : (g ^ r - 1) ^ n = (g ^ s - 1) ^ n) :
    ∃ u ∈ rootsFinset g n, g ^ r + u = 1 + u * g ^ s := by
  haveI : NeZero n := ⟨hn0⟩
  let u : F := (g ^ r - 1) / (g ^ s - 1)
  have hslt : s < n := lt_of_le_of_lt hsh
    (Nat.div_lt_self (Nat.pos_of_ne_zero hn0) (by norm_num : 1 < 2))
  have hgs_ne : g ^ s - 1 ≠ 0 := by
    rw [sub_ne_zero]
    intro hgs
    have hsdvd : n ∣ s := (hprim.pow_eq_one_iff_dvd s).mp (by simpa using hgs)
    rcases hsdvd with ⟨k, rfl⟩
    rcases k with _ | k
    · omega
    · have hle : n ≤ n * (k + 1) := Nat.le_mul_of_pos_right n (Nat.succ_pos k)
      exact (not_le_of_gt hslt) hle
  have hu_pow : u ^ n = 1 := by
    unfold u
    rw [div_pow, hphi, div_self]
    exact pow_ne_zero n hgs_ne
  obtain ⟨k, hklt, hku⟩ := hprim.eq_pow_of_pow_eq_one hu_pow
  refine ⟨u, ?_, ?_⟩
  · exact mem_rootsFinset_iff.mpr ⟨k, hklt, hku⟩
  · have hmul : u * (g ^ s - 1) = g ^ r - 1 := by
      unfold u
      field_simp [hgs_ne]
    rw [mul_sub] at hmul
    have hmul' : u * g ^ s - u = g ^ r - 1 := by simpa using hmul
    calc
      g ^ r + u = (u * g ^ s - u + 1) + u := by rw [hmul']; ring
      _ = 1 + u * g ^ s := by ring

set_option linter.unusedFintypeInType false in
/-- Reverse bridge for primitive cyclic root sets: `SidonModNeg` forces
`Phi` injectivity on the certified half-window. -/
theorem phiWindowInjective_of_sidonModNeg_rootsFinset
    {g : F} {n : ℕ} (hn0 : n ≠ 0) (heven : Even n)
    (hprim : IsPrimitiveRoot g n)
    (hS : SidonModNeg (rootsFinset g n)) :
    PhiWindowInjective g n := by
  intro r s hr1 hrh hs1 hsh hphi
  have hrlt : r < n := lt_of_le_of_lt hrh
    (Nat.div_lt_self (Nat.pos_of_ne_zero hn0) (by norm_num : 1 < 2))
  have hslt : s < n := lt_of_le_of_lt hsh
    (Nat.div_lt_self (Nat.pos_of_ne_zero hn0) (by norm_num : 1 < 2))
  rcases exists_root_relation_of_phi_collision hn0 hprim hs1 hsh hphi with
    ⟨u, hu, hrel⟩
  have hgr : g ^ r ∈ rootsFinset g n := pow_mem_rootsFinset hn0 hprim r
  have hone : (1 : F) ∈ rootsFinset g n := one_mem_rootsFinset hn0 hprim
  have hgs : g ^ s ∈ rootsFinset g n := pow_mem_rootsFinset hn0 hprim s
  have hugs : u * g ^ s ∈ rootsFinset g n := mul_mem_rootsFinset hn0 hprim hu hgs
  rcases hS (g ^ r) hgr u hu 1 hone (u * g ^ s) hugs hrel with
    ⟨hgr1, _hu_eq⟩ | ⟨hgr_us, hu1⟩ | hzero
  · have hr_ne0 : r ≠ 0 := by omega
    exact False.elim (hprim.pow_ne_one_of_pos_of_lt hr_ne0 hrlt (by simpa using hgr1))
  · have hpow : g ^ r = g ^ s := by simpa [hu1] using hgr_us
    exact hprim.pow_inj hrlt hslt hpow
  · have hright_zero : 1 + u * g ^ s = 0 := by
      rw [← hrel]
      exact hzero
    have hu_eq : u = -g ^ r := by linear_combination hzero
    have hprod_neg : -(g ^ (r + s)) = -1 := by
      have humul : u * g ^ s = -1 := by linear_combination hright_zero
      rw [pow_add]
      rw [hu_eq] at humul
      simpa [neg_mul] using humul
    have hprod : g ^ (r + s) = 1 := neg_injective hprod_neg
    have hsumdvd : n ∣ r + s := (hprim.pow_eq_one_iff_dvd (r + s)).mp hprod
    rcases heven with ⟨t, rfl⟩
    have hsum_le : r + s ≤ 2 * t := by omega
    rcases hsumdvd with ⟨k, hk⟩
    have hsum_pos : 0 < r + s := by omega
    have hsum_eq : r + s = 2 * t := by
      have htpos : 0 < t := by omega
      rcases k with _ | k
      · omega
      · rcases k with _ | k
        · simpa [two_mul] using hk
        · have hgt : 2 * t < 2 * t * (k + 2) := by
            simpa using
              (Nat.mul_lt_mul_of_pos_left (by omega : 1 < k + 2)
                (by omega : 0 < 2 * t))
          have hlarge : 2 * t < r + s := by
            calc
              2 * t < 2 * t * (k + 2) := hgt
              _ = r + s := by
                rw [hk]
                ring
          exact False.elim ((not_lt_of_ge hsum_le) hlarge)
    omega

omit [Fintype F] [DecidableEq F] in
/-- A primitive root has exact order in the lightweight predicate used by the
closed G139 bridge. -/
theorem hasExactOrder_of_isPrimitiveRoot
    {g : F} {n : ℕ} (hprim : IsPrimitiveRoot g n) :
    HasExactOrder g n := by
  intro m hm hpow
  by_cases hm0 : m = 0
  · exact hm0
  · exact False.elim (hprim.pow_ne_one_of_pos_of_lt hm0 hm hpow)

set_option linter.unusedFintypeInType false in
/-- Primitive cyclic root-set equivalence: the finite `Phi` half-window
certificate is exactly the `SidonModNeg` obstruction for the generated roots of
unity. -/
theorem phiWindowInjective_iff_sidonModNeg_rootsFinset
    {g : F} {n : ℕ} (hn0 : n ≠ 0) (heven : Even n)
    (hprim : IsPrimitiveRoot g n) :
    PhiWindowInjective g n ↔ SidonModNeg (rootsFinset g n) := by
  constructor
  · intro hPhi
    exact sidonModNeg_rootsFinset_of_exactOrder_phiWindowInjective
      hprim.pow_eq_one hn0 heven (hasExactOrder_of_isPrimitiveRoot hprim) hPhi
  · intro hS
    exact phiWindowInjective_of_sidonModNeg_rootsFinset hn0 heven hprim hS

/-! ## Axiom audit -/
#print axioms sidonModNeg_rootsFinset_of_exactOrder_phiWindowInjective
#print axioms accidents_card_eq_zero_rootsFinset_of_exactOrder_phiWindowInjective
#print axioms phiWindowInjective_iff_sidonModNeg_rootsFinset

end ArkLib.ProximityGap.Frontier.G139PhiInjectiveSidonBridge
