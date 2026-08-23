/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SidonLiftClosed
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergySidonModNeg

/-!
# The small-subgroup Sidon pin, unconditional (#389)

For `n = 2^m` (`m ≥ 1`) and a prime `p > 2^n` with a primitive `n`-th root `ω ∈ ZMod p`, the
subgroup `μ_n = {z : z^n = 1}` is **Sidon-modulo-negation** (`SidonModNeg`), hence has additive
energy exactly `3n² − 3n`.  No Weil, no Stepanov, no open conjecture — purely the cyclotomic
resultant bound `prime_le_of_parallelogram` (`|Res(Φ_n, ·)| ≤ 4^{φ(n)} = 2^n < p` forbids a
nontrivial nonzero-sum parallelogram) plus the elementary discharge of its two residuals:

* **(a) degree preservation mod `p`** (`fourTerm_natDegree_map_eq`): the four-term polynomial's
  coefficients have `|·| ≤ 2 < p`, so its leading coefficient is nonzero in `ZMod p`;
* **(b) the F_p → ℂ-primitive transfer** (`fourTerm_prim_ne_zero_of_Fp`): the nonvanishing
  conditions of the parallelogram transfer between `ZMod p` and `ℂ` through the *shared
  exponent-mod-`n` structure* of primitive `n`-th roots in both fields.

Combining with the in-tree `additiveEnergy_eq_of_sidonModNeg` pins `E(μ_n) = 3|G|² − 3|G|`
unconditionally in the small-subgroup regime `n < log₂ p`, the optimal (char-0) value.  This is
the closed, Weil-free core of the small-subgroup proximity-gap programme; the deployed prize
(`n ≫ log₂ p`) remains the separate specific-prime coincidence question.  Axiom-clean.
-/

open Polynomial

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

/-! ## Residual (a): degree preservation mod p -/

/-- Every coefficient of the four-term polynomial has absolute value `≤ 2`. -/
theorem fourTerm_coeff_abs_le_two (i j k l : ℕ) (e : ℕ) :
    |(fourTerm i j k l).coeff e| ≤ 2 := by
  simp only [fourTerm, coeff_sub, coeff_add, coeff_X_pow]
  split_ifs <;> norm_num

/-- **Degree preservation residual discharged.** For a prime `p ≥ 3`, the four-term polynomial
keeps its natDegree mod `p` (its leading coefficient has `|·| ≤ 2`, nonzero in `ZMod p`). -/
theorem fourTerm_natDegree_map_eq {p : ℕ} (hp : 2 < p) (i j k l : ℕ) :
    ((fourTerm i j k l).map (Int.castRingHom (ZMod p))).natDegree
      = (fourTerm i j k l).natDegree := by
  rcases eq_or_ne (fourTerm i j k l) 0 with h0 | h0
  · simp [h0]
  · apply natDegree_map_of_leadingCoeff_ne_zero
    have hlc : (fourTerm i j k l).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr h0
    have hle : |(fourTerm i j k l).leadingCoeff| ≤ 2 := fourTerm_coeff_abs_le_two i j k l _
    intro hzero
    rw [Int.castRingHom, eq_intCast] at hzero
    have hdvd : (p : ℤ) ∣ (fourTerm i j k l).leadingCoeff :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp (by simpa using hzero)
    have hpos : (0:ℤ) < |(fourTerm i j k l).leadingCoeff| := abs_pos.mpr hlc
    have hple : (p : ℤ) ≤ |(fourTerm i j k l).leadingCoeff| :=
      Int.le_of_dvd hpos ((dvd_abs _ _).mpr hdvd)
    have : (p : ℤ) ≤ 2 := le_trans hple hle
    omega

end ArkLib.ProximityGap.AdditiveEnergyRepBound

/-! ## Bridge lemmas: shared exponent structure of primitive roots -/

/-- A power of a primitive `n`-th root only depends on the exponent mod `n`. -/
theorem IsPrimitiveRoot.pow_eq_pow_mod {M : Type*} [CommMonoid M] {ξ : M} {n : ℕ}
    (h : IsPrimitiveRoot ξ n) (a : ℕ) : ξ ^ a = ξ ^ (a % n) := by
  conv_lhs => rw [← Nat.div_add_mod a n]
  rw [pow_add, pow_mul, h.pow_eq_one, one_pow, one_mul]

/-- For a primitive `n`-th root `ξ` in a commutative monoid, `ξ^x = ξ^y ↔ x % n = y % n`.
Built from `pow_inj` (valid in any monoid) and mod-reduction — no cancellativity needed, so it
applies to a field element directly (unlike `pow_eq_pow_iff_modEq`, which needs `LeftCancelMonoid`
and so does not fire on a field element such as a root of unity in `ZMod p` or `ℂ`). -/
theorem IsPrimitiveRoot.pow_eq_pow_iff_mod {M : Type*} [CommMonoid M] {ξ : M} {n : ℕ}
    (hn : n ≠ 0) (h : IsPrimitiveRoot ξ n) (x y : ℕ) : ξ ^ x = ξ ^ y ↔ x % n = y % n := by
  have hpos : 0 < n := Nat.pos_of_ne_zero hn
  constructor
  · intro hxy
    refine h.pow_inj (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos) ?_
    rw [← h.pow_eq_pow_mod, ← h.pow_eq_pow_mod, hxy]
  · intro hxy
    rw [h.pow_eq_pow_mod x, h.pow_eq_pow_mod y, hxy]

/-- In a field, the `n/2`-power of a primitive `n`-th root is `-1` (`n = 2h`, `h ≠ 0`). -/
theorem IsPrimitiveRoot.pow_half_eq_neg_one {K : Type*} [Field K] {ξ : K} {n h : ℕ}
    (hprim : IsPrimitiveRoot ξ n) (hnh : n = 2 * h) (hh : h ≠ 0) : ξ ^ h = -1 := by
  have hsq : ξ ^ h * ξ ^ h = 1 := by
    rw [← pow_add, ← two_mul, ← hnh]; exact hprim.pow_eq_one
  rcases mul_self_eq_one_iff.mp hsq with h1 | h1
  · exact absurd h1 (hprim.pow_ne_one_of_pos_of_lt hh (by omega))
  · exact h1

/-! ## Residual (b): F_p parallelogram ⇒ primitive-root ℂ nonvanishing -/

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

/-- **The transfer.** Given exponents whose F_p four-term is a nontrivial nonzero-sum parallelogram
at the primitive root `ω ∈ ZMod p`, the four-term value is nonzero at *every* primitive `n`-th root
over ℂ.  The conditions transfer through the shared exponent-mod-`n` structure of primitive roots,
discharging the `hne` hypothesis of `prime_le_of_parallelogram` from finite-field data alone. -/
theorem fourTerm_prim_ne_zero_of_Fp {p : ℕ} [Fact p.Prime] {n h : ℕ} (hn : n ≠ 0)
    (hnh : n = 2 * h) (hh : h ≠ 0) {ω : ZMod p} (hω : IsPrimitiveRoot ω n) {i j k l : ℕ}
    (hac : ¬(ω ^ i = ω ^ k ∧ ω ^ j = ω ^ l)) (had : ¬(ω ^ i = ω ^ l ∧ ω ^ j = ω ^ k))
    (hsum : ω ^ i + ω ^ j ≠ 0) :
    ∀ ζ : ℂ, IsPrimitiveRoot ζ n → ζ ^ i + ζ ^ j - ζ ^ k - ζ ^ l ≠ 0 := by
  refine fourTerm_ne_zero_primitive hn ?_ ?_
  · -- the partial sum is nonzero at every primitive root
    intro ζ hζ
    have bridge : ∀ x y : ℕ, (ζ ^ x = ζ ^ y ↔ ω ^ x = ω ^ y) := fun x y =>
      (hζ.pow_eq_pow_iff_mod hn x y).trans (hω.pow_eq_pow_iff_mod hn x y).symm
    have hζh : ζ ^ h = -1 := hζ.pow_half_eq_neg_one hnh hh
    have hωh : ω ^ h = -1 := hω.pow_half_eq_neg_one hnh hh
    intro hzero
    apply hsum
    have e1 : ζ ^ i = ζ ^ (h + j) := by rw [pow_add, hζh]; linear_combination hzero
    have e2 : ω ^ i = ω ^ (h + j) := (bridge i (h + j)).mp e1
    rw [pow_add, hωh] at e2
    linear_combination e2
  · -- the pair is not matched at any primitive root
    intro ζ hζ
    have bridge : ∀ x y : ℕ, (ζ ^ x = ζ ^ y ↔ ω ^ x = ω ^ y) := fun x y =>
      (hζ.pow_eq_pow_iff_mod hn x y).trans (hω.pow_eq_pow_iff_mod hn x y).symm
    rintro (⟨e1, e2⟩ | ⟨e1, e2⟩)
    · exact hac ⟨(bridge i k).mp e1, (bridge j l).mp e2⟩
    · exact had ⟨(bridge i l).mp e1, (bridge j k).mp e2⟩

end ArkLib.ProximityGap.AdditiveEnergyRepBound

/-! ## The capstone: μ_n is Sidon-mod-negation for p > 2^n -/

open ArkLib.ProximityGap.AdditiveEnergyRepBound

/-- `4^{φ(2^m)} = 2^{2^m}` for `m ≥ 1` (`φ(2^m) = 2^{m-1}`). -/
theorem four_pow_totient_two_pow {m : ℕ} (hm : 1 ≤ m) :
    (4 : ℕ) ^ Nat.totient (2 ^ m) = 2 ^ (2 ^ m) := by
  have ht : Nat.totient (2 ^ m) = 2 ^ (m - 1) := by
    rw [Nat.totient_prime_pow Nat.prime_two hm]; simp
  rw [ht, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  congr 1
  conv_rhs => rw [show m = 1 + (m - 1) by omega]
  rw [pow_add, pow_one]

namespace ArkLib.ProximityGap.AdditiveEnergySidonModNeg

open ArkLib.ProximityGap.AdditiveEnergyRepBound

/-- **THE SMALL-SUBGROUP SIDON PIN.** For `n = 2^m` (`m ≥ 1`) and a prime `p > 2^n` with a
primitive `n`-th root `ω ∈ ZMod p`, the subgroup `μ_n = {z : z^n = 1}` is Sidon-modulo-negation:
its only additive coincidences are the trivial and zero-sum ones.  Unconditional — no Weil, no
Stepanov, no open conjecture; the cyclotomic resultant `|Res(Φ_n, ·)| ≤ 2^n < p` forbids any
nontrivial nonzero-sum parallelogram. -/
theorem sidonModNeg_mu_n {p : ℕ} [Fact p.Prime] {n m : ℕ} (hn2 : n = 2 ^ m) (hm : 1 ≤ m)
    (hp : 2 ^ n < p) {ω : ZMod p} (hω : IsPrimitiveRoot ω n)
    {G : Finset (ZMod p)} (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) :
    SidonModNeg G := by
  have hn : n ≠ 0 := by rw [hn2]; positivity
  haveI : NeZero n := ⟨hn⟩
  have h2n : 2 ≤ 2 ^ n :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hn))
  -- p > 2^n > n, so p ∤ n hence (n : ZMod p) ≠ 0
  have hpn : n < p := by have h1 : n < 2 ^ n := n.lt_two_pow_self; omega
  haveI : NeZero (n : ZMod p) := ⟨by
    intro hzero
    rw [ZMod.natCast_eq_zero_iff] at hzero
    exact absurd (Nat.le_of_dvd (by omega) hzero) (by omega)⟩
  have hp2 : 2 < p := by omega
  -- 4^{φ(n)} = 2^n
  have key : (4 : ℕ) ^ n.totient = 2 ^ n := by rw [hn2]; exact four_pow_totient_two_pow hm
  -- n = 2 * (n/2), with n/2 ≠ 0
  obtain ⟨h, hnh⟩ : ∃ h, n = 2 * h := ⟨2 ^ (m - 1), by
    rw [hn2]; conv_lhs => rw [show m = 1 + (m - 1) by omega]
    rw [pow_add, pow_one]⟩
  have hh : h ≠ 0 := by rintro rfl; rw [mul_zero] at hnh; exact hn hnh
  -- a nontrivial nonzero-sum parallelogram would force p ≤ 2^n, contradiction
  intro a ha b hb c hc d hd hsum_eq
  by_contra hcon
  push_neg at hcon
  obtain ⟨hac', had', hab0⟩ := hcon
  obtain ⟨i, _, hi⟩ := hω.eq_pow_of_pow_eq_one ((hGmem a).mp ha)
  obtain ⟨j, _, hj⟩ := hω.eq_pow_of_pow_eq_one ((hGmem b).mp hb)
  obtain ⟨k, _, hk⟩ := hω.eq_pow_of_pow_eq_one ((hGmem c).mp hc)
  obtain ⟨l, _, hl⟩ := hω.eq_pow_of_pow_eq_one ((hGmem d).mp hd)
  subst hi hj hk hl
  have hac : ¬(ω ^ i = ω ^ k ∧ ω ^ j = ω ^ l) := fun ⟨e1, e2⟩ => hac' e1 e2
  have had : ¬(ω ^ i = ω ^ l ∧ ω ^ j = ω ^ k) := fun ⟨e1, e2⟩ => had' e1 e2
  have hsum : ω ^ i + ω ^ j ≠ 0 := hab0
  have hpara : ω ^ i + ω ^ j - ω ^ k - ω ^ l = 0 := by linear_combination hsum_eq
  have hne := fourTerm_prim_ne_zero_of_Fp hn hnh hh hω hac had hsum
  have hfdeg := fourTerm_natDegree_map_eq hp2 i j k l
  have hle := prime_le_of_parallelogram hn hω hfdeg hpara hne
  have hfin : p ≤ 2 ^ n := key ▸ hle
  omega

/-- **The additive energy of the small-subgroup `μ_n` is exactly `3n² − 3n`** for `p > 2^n`,
unconditionally — the char-0 minimal value, attained over `F_p` once `p` exceeds `2^n`. -/
theorem additiveEnergy_mu_n {p : ℕ} [Fact p.Prime] {n m : ℕ} (hn2 : n = 2 ^ m) (hm : 1 ≤ m)
    (hp : 2 ^ n < p) {ω : ZMod p} (hω : IsPrimitiveRoot ω n)
    {G : Finset (ZMod p)} (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) :
    ArkLib.ProximityGap.AdditiveEnergyRepBound.additiveEnergy G
      = 3 * G.card ^ 2 - 3 * G.card := by
  have hn : n ≠ 0 := by rw [hn2]; positivity
  have h2n : 2 ≤ 2 ^ n :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hn))
  have hp2 : 2 < p := by omega
  have h2F : (2 : ZMod p) ≠ 0 := by
    intro hcontra
    have hdvd : (p : ℕ) ∣ 2 := by
      rw [← ZMod.natCast_eq_zero_iff]; exact_mod_cast hcontra
    have := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have h0 : (0 : ZMod p) ∉ G := by
    rw [hGmem]; simp [zero_pow hn]
  have hneg : ∀ x ∈ G, -x ∈ G := by
    intro x hx
    rw [hGmem] at hx ⊢
    have he : Even n := by rw [hn2]; exact Nat.even_pow.mpr ⟨even_two, by omega⟩
    rw [neg_pow, he.neg_one_pow, one_mul]; exact hx
  exact additiveEnergy_eq_of_sidonModNeg h2F h0 hneg
    (sidonModNeg_mu_n hn2 hm hp hω hGmem)

/-- **The small-subgroup `μ_n` is Sidon**: every nonzero shift has at most two representations,
for `p > 2^n`, unconditionally.  This is the literal rep-count input the supply chain consumes
(`additiveEnergy_le_three_of_repTwo`, `gvRepBound_of_sidonModNeg`). -/
theorem repCount_mu_n_le_two {p : ℕ} [Fact p.Prime] {n m : ℕ} (hn2 : n = 2 ^ m) (hm : 1 ≤ m)
    (hp : 2 ^ n < p) {ω : ZMod p} (hω : IsPrimitiveRoot ω n)
    {G : Finset (ZMod p)} (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1)
    (c : ZMod p) (hc : c ≠ 0) :
    repCount G c ≤ 2 := by
  have hn : n ≠ 0 := by rw [hn2]; positivity
  have hS := sidonModNeg_mu_n hn2 hm hp hω hGmem
  have hneg : ∀ x ∈ G, -x ∈ G := by
    intro x hx
    rw [hGmem] at hx ⊢
    have he : Even n := by rw [hn2]; exact Nat.even_pow.mpr ⟨even_two, by omega⟩
    rw [neg_pow, he.neg_one_pow, one_mul]; exact hx
  rcases Nat.eq_zero_or_pos (repCount G c) with h0 | hpos
  · omega
  · obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter] at hy
    obtain ⟨hyG, hcyG⟩ := hy
    have hsum : y + (c - y) = c := by ring
    have hrc := repCount_sidonModNeg hneg hS hyG hcyG
    rw [hsum, if_neg hc] at hrc
    rw [hrc]
    exact le_trans (Finset.card_insert_le _ _) (by simp)

end ArkLib.ProximityGap.AdditiveEnergySidonModNeg

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.AdditiveEnergySidonModNeg.sidonModNeg_mu_n
#print axioms ArkLib.ProximityGap.AdditiveEnergySidonModNeg.additiveEnergy_mu_n
#print axioms ArkLib.ProximityGap.AdditiveEnergySidonModNeg.repCount_mu_n_le_two
