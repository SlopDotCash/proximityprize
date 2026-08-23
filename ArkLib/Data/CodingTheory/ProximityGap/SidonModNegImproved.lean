/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SidonThresholdImproved
import ArkLib.Data.CodingTheory.ProximityGap.SidonDoubledThreshold
import ArkLib.Data.CodingTheory.ProximityGap.SidonInjTransfer

/-!
# THE FULL IMPROVED SIDON-MOD-NEGATION THRESHOLD `p > 12^{n/4}` (#389)

The capstone of the Parseval/AM-GM improved-bound programme: `μ_n ⊂ F_p` is Sidon-modulo-negation
for `p > 12^{n/4}` (`12^{φ(n)} < p²`), sharpening the committed `sidonModNeg_rootsOfUnity` (`p > 2^n`).
A genuine nontrivial coincidence `a+b=c+d` (no-overlap) is either all-distinct (`S=4`, resultant
bound `8^{φ(n)}`, threshold `prime_sq_le_of_parallelogram`) or doubled (`S=6`, `12^{φ(n)}`,
`prime_sq_le_doubled`); the worst case `S=6` gives `p > 12^{n/4} ≈ 2^{0.896n}`.  The ℂ-side
distinctness hypotheses are supplied from the `F_p` data by `pow_inj_transfer` + `inj3`/`inj4`.
Axiom-clean.  Issue #389.
-/

open Complex Finset Polynomial
namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

/-- Matrix-form `Fin 3` distinctness transfer `F_p → ℂ`. -/
theorem matrix3_inj_transfer {n : ℕ} (hn0 : n ≠ 0) {p : ℕ} [Fact p.Prime] {ω : ZMod p}
    (hω : IsPrimitiveRoot ω n) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) {x y z : ℕ}
    (hinj : Function.Injective (![ω ^ x, ω ^ y, ω ^ z] : Fin 3 → ZMod p)) :
    Function.Injective (![ζ ^ x, ζ ^ y, ζ ^ z] : Fin 3 → ℂ) := by
  have h1 : (![ζ ^ x, ζ ^ y, ζ ^ z] : Fin 3 → ℂ) = fun a => ζ ^ (![x, y, z] a) := by
    funext a; fin_cases a <;> rfl
  have h2 : (![ω ^ x, ω ^ y, ω ^ z] : Fin 3 → ZMod p) = fun a => ω ^ (![x, y, z] a) := by
    funext a; fin_cases a <;> rfl
  rw [h1]; rw [h2] at hinj; exact pow_inj_transfer hn0 hω hζ ![x, y, z] hinj

/-- Matrix-form `Fin 4` distinctness transfer `F_p → ℂ`. -/
theorem matrix4_inj_transfer {n : ℕ} (hn0 : n ≠ 0) {p : ℕ} [Fact p.Prime] {ω : ZMod p}
    (hω : IsPrimitiveRoot ω n) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) {w x y z : ℕ}
    (hinj : Function.Injective (![ω ^ w, ω ^ x, ω ^ y, ω ^ z] : Fin 4 → ZMod p)) :
    Function.Injective (![ζ ^ w, ζ ^ x, ζ ^ y, ζ ^ z] : Fin 4 → ℂ) := by
  have h1 : (![ζ ^ w, ζ ^ x, ζ ^ y, ζ ^ z] : Fin 4 → ℂ) = fun a => ζ ^ (![w, x, y, z] a) := by
    funext a; fin_cases a <;> rfl
  have h2 : (![ω ^ w, ω ^ x, ω ^ y, ω ^ z] : Fin 4 → ZMod p) = fun a => ω ^ (![w, x, y, z] a) := by
    funext a; fin_cases a <;> rfl
  rw [h1]; rw [h2] at hinj; exact pow_inj_transfer hn0 hω hζ ![w, x, y, z] hinj

open ArkLib.ProximityGap.AdditiveEnergySidonModNeg in
/-- **THE FULL IMPROVED SIDON-MOD-NEGATION THRESHOLD.**  For `n = 2^m` and a prime `p > 12^{n/4}`
(`12^{φ(n)} < p²`), the `n`-th roots of unity in `F_p` are Sidon-modulo-negation.  Sharpens
`sidonModNeg_rootsOfUnity` (`p > 2^n`) by case-splitting genuine coincidences into the all-distinct
(`S=4`, bound `8^{φ(n)}`) and doubled (`S=6`, bound `12^{φ(n)}`) types and deploying the improved
resultant bounds; the worst case `S=6` gives the threshold `p > 12^{n/4} ≈ 2^{0.896n}`. -/
theorem sidonModNeg_rootsOfUnity_improved {m : ℕ} (hm : 1 ≤ m) {p : ℕ} [Fact p.Prime]
    [NeZero ((2 ^ m : ℕ) : ZMod p)] (hp : 12 ^ (2 ^ m).totient < p ^ 2)
    {ω : ZMod p} (hω : IsPrimitiveRoot ω (2 ^ m)) :
    SidonModNeg ((Finset.range (2 ^ m)).image (ω ^ ·)) := by
  set n := 2 ^ m with hn_def
  have hn0 : n ≠ 0 := by positivity
  have hn2 : 2 ∣ n := dvd_pow_self 2 (by omega)
  have h12 : (12 : ℕ) ≤ 12 ^ n.totient :=
    Nat.le_self_pow (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn0)).ne' 12
  have hp2 : 2 < p := by
    by_contra hcontra
    push_neg at hcontra
    have h2 : p ^ 2 ≤ 4 := by
      calc p ^ 2 ≤ 2 ^ 2 := Nat.pow_le_pow_left hcontra 2
        _ = 4 := by norm_num
    have h1 : (12 : ℕ) < p ^ 2 := lt_of_le_of_lt h12 hp
    omega
  set ζ := Complex.exp (2 * ↑Real.pi * Complex.I / ↑n) with hζdef
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn0
  intro a ha b hb c hc d hd hsum
  simp only [Finset.mem_image, Finset.mem_range] at ha hb hc hd
  obtain ⟨ea, _, rfl⟩ := ha
  obtain ⟨eb, _, rfl⟩ := hb
  obtain ⟨ec, _, rfl⟩ := hc
  obtain ⟨ed, _, rfl⟩ := hd
  by_contra hcon
  push_neg at hcon
  obtain ⟨hnp1, hnp2, hns⟩ := hcon
  -- no-overlap distinctness facts
  have hac : ω ^ ea ≠ ω ^ ec := fun h => hnp1 h (by linear_combination hsum - h)
  have had : ω ^ ea ≠ ω ^ ed := fun h => hnp2 h (by linear_combination hsum - h)
  have hbc : ω ^ eb ≠ ω ^ ec := fun h => hnp2 (by linear_combination hsum - h) h
  have hbd : ω ^ eb ≠ ω ^ ed := fun h => hnp1 (by linear_combination hsum - h) h
  have hω0 : ω ^ ea ≠ 0 := pow_ne_zero _ (by
    intro h; have := hω.pow_eq_one; rw [h, zero_pow hn0] at this; exact zero_ne_one this)
  have h2ne : (2 : ZMod p) ≠ 0 := by
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_cast, Ne, CharP.cast_eq_zero_iff (ZMod p) p]
    intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega
  by_cases hL : ω ^ ea = ω ^ eb
  · by_cases hR : ω ^ ec = ω ^ ed
    · -- both doubled ⇒ ω^ea = ω^ec, contradicting hac
      apply hac
      have h2 : (2 : ZMod p) * ω ^ ea = 2 * ω ^ ec := by linear_combination hsum + hL - hR
      exact mul_left_cancel₀ h2ne h2
    · -- doubled left: 2ω^ea = ω^ec + ω^ed
      have hpara : ω ^ ea + ω ^ ea - ω ^ ec - ω ^ ed = 0 := by linear_combination hsum + hL
      have hsum' : ω ^ ea + ω ^ ea ≠ 0 := by
        rw [← two_mul]; exact mul_ne_zero h2ne hω0
      have hpair' : ¬ ((ω ^ ea = ω ^ ec ∧ ω ^ ea = ω ^ ed) ∨
          (ω ^ ea = ω ^ ed ∧ ω ^ ea = ω ^ ec)) := by rintro (⟨h, _⟩ | ⟨_, h⟩) <;> exact hac h
      have hne := fourTerm_ne_zero_primitiveRoots_of_fp hn2 hn0 hω hsum' hpair'
      have hdistC : Function.Injective (![ζ ^ ea, ζ ^ ec, ζ ^ ed] : Fin 3 → ℂ) :=
        matrix3_inj_transfer hn0 hω hζ (inj3 hac had hR)
      have hle := prime_sq_le_doubled hm hp2 hω hζ hpara hne hdistC
      rw [← hn_def] at hle; omega
  · by_cases hR : ω ^ ec = ω ^ ed
    · -- doubled right: 2ω^ec = ω^ea + ω^eb
      have hpara : ω ^ ec + ω ^ ec - ω ^ ea - ω ^ eb = 0 := by linear_combination -hsum + hR
      have hec0 : ω ^ ec ≠ 0 := pow_ne_zero _ (by
        intro h; have := hω.pow_eq_one; rw [h, zero_pow hn0] at this; exact zero_ne_one this)
      have hsum' : ω ^ ec + ω ^ ec ≠ 0 := by rw [← two_mul]; exact mul_ne_zero h2ne hec0
      have hpair' : ¬ ((ω ^ ec = ω ^ ea ∧ ω ^ ec = ω ^ eb) ∨
          (ω ^ ec = ω ^ eb ∧ ω ^ ec = ω ^ ea)) := by
        rintro (⟨h, _⟩ | ⟨_, h⟩) <;> exact hac h.symm
      have hne := fourTerm_ne_zero_primitiveRoots_of_fp hn2 hn0 hω hsum' hpair'
      have hdistC : Function.Injective (![ζ ^ ec, ζ ^ ea, ζ ^ eb] : Fin 3 → ℂ) :=
        matrix3_inj_transfer hn0 hω hζ (inj3 (Ne.symm hac) (Ne.symm hbc) hL)
      have hle := prime_sq_le_doubled hm hp2 hω hζ hpara hne hdistC
      rw [← hn_def] at hle; omega
    · -- all distinct: S = 4
      have hpara : ω ^ ea + ω ^ eb - ω ^ ec - ω ^ ed = 0 := by linear_combination hsum
      have hpair : ¬ ((ω ^ ea = ω ^ ec ∧ ω ^ eb = ω ^ ed) ∨
          (ω ^ ea = ω ^ ed ∧ ω ^ eb = ω ^ ec)) := by
        rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact hnp1 h1 h2
        · exact hnp2 h1 h2
      have hne := fourTerm_ne_zero_primitiveRoots_of_fp hn2 hn0 hω hns hpair
      have hdistC : Function.Injective (![ζ ^ ea, ζ ^ eb, ζ ^ ec, ζ ^ ed] : Fin 4 → ℂ) :=
        matrix4_inj_transfer hn0 hω hζ (inj4 hL hac had hbc hbd hR)
      have hle := prime_sq_le_of_parallelogram hm hp2 hω hζ hpara hne hdistC
      rw [← hn_def] at hle
      have h812 : (8 : ℕ) ^ n.totient ≤ 12 ^ n.totient := Nat.pow_le_pow_left (by norm_num) _
      omega

/-- **The improved threshold strictly improves the committed one.**  For `n = 2^m`, the new
resultant bound `12^{φ(n)}` is strictly below the committed `(2^n)² = 4^n`, so the Sidon threshold
`p > 12^{n/4}` covers strictly more primes than `p > 2^n` (`12^{n/4} = 2^{0.896n} < 2^n`). -/
theorem improved_threshold_strict {m : ℕ} (hm : 1 ≤ m) :
    (12 : ℕ) ^ (2 ^ m).totient < 4 ^ (2 ^ m) := by
  have ht : (2 ^ m).totient = 2 ^ (m - 1) := by
    rw [Nat.totient_prime_pow Nat.prime_two (by omega)]; simp
  have h4 : (4 : ℕ) ^ (2 ^ m) = 16 ^ (2 ^ (m - 1)) := by
    rw [show (16 : ℕ) = 4 ^ 2 by norm_num, ← pow_mul,
      show 2 * 2 ^ (m - 1) = 2 ^ m from by rw [← pow_succ']; congr 1; omega]
  rw [ht, h4]
  exact Nat.pow_lt_pow_left (by norm_num) (by positivity)

open ArkLib.ProximityGap.AdditiveEnergySidonModNeg Finset in
/-- **The improved additive-energy pin.**  For `n = 2^m` and `p > 12^{n/4}` (`12^{φ(n)} < p²`), the
additive energy of the `n`-th roots of unity in `F_p` is exactly `3n² − 3n` — the char-0 minimal
value, now at the sharpened threshold (vs the committed `p > 2^n`). -/
theorem rootsOfUnity_additiveEnergy_eq_improved {m : ℕ} (hm : 1 ≤ m) {p : ℕ} [Fact p.Prime]
    [NeZero ((2 ^ m : ℕ) : ZMod p)] (hp : 12 ^ (2 ^ m).totient < p ^ 2)
    {ω : ZMod p} (hω : IsPrimitiveRoot ω (2 ^ m)) :
    additiveEnergy ((Finset.range (2 ^ m)).image (ω ^ ·)) = 3 * (2 ^ m) ^ 2 - 3 * 2 ^ m := by
  set n := 2 ^ m with hn_def
  have hn0 : n ≠ 0 := by positivity
  have hn0' : 0 < n := Nat.pos_of_ne_zero hn0
  have h12 : (12 : ℕ) ≤ 12 ^ n.totient := Nat.le_self_pow (Nat.totient_pos.mpr hn0').ne' 12
  have hp2 : 2 < p := by
    by_contra hc; push_neg at hc
    have h2 : p ^ 2 ≤ 4 := by calc p ^ 2 ≤ 2 ^ 2 := Nat.pow_le_pow_left hc 2
                                  _ = 4 := by norm_num
    have h1 : (12 : ℕ) < p ^ 2 := lt_of_le_of_lt h12 hp
    omega
  haveI : NeZero p := ⟨by omega⟩
  set G := (Finset.range n).image (ω ^ ·) with hG
  have hω0 : ω ≠ 0 := by
    intro h; have h1 := hω.pow_eq_one; rw [h, zero_pow hn0] at h1; exact zero_ne_one h1
  have h2 : (2 : ZMod p) ≠ 0 := by
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_cast, Ne, CharP.cast_eq_zero_iff (ZMod p) p]
    intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega
  have h0 : (0 : ZMod p) ∉ G := by
    rw [hG]; intro hmem; simp only [Finset.mem_image, Finset.mem_range] at hmem
    obtain ⟨t, _, ht⟩ := hmem; exact pow_ne_zero t hω0 ht
  have hev : Even n := by rw [hn_def]; exact (Nat.even_pow.mpr ⟨even_two, by omega⟩)
  have hhalf : ω ^ (n / 2) = -1 := primitiveRoot_pow_half (by rw [hn_def]; exact dvd_pow_self 2 (by omega)) hn0 hω
  have hneg : ∀ x ∈ G, -x ∈ G := by
    rw [hG]; intro x hx; simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
    obtain ⟨t, _, rfl⟩ := hx
    refine ⟨(n / 2 + t) % n, Nat.mod_lt _ (by omega), ?_⟩
    rw [(primitiveRoot_pow_eq_iff hn0 hω ((n / 2 + t) % n) (n / 2 + t)).mpr (Nat.mod_modEq _ _),
      pow_add, hhalf]; ring
  have hcard : G.card = n := by
    rw [hG, Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have h := (primitiveRoot_pow_eq_iff hn0 hω a b).mp hab
    unfold Nat.ModEq at h; rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  have hS : SidonModNeg G := sidonModNeg_rootsOfUnity_improved hm hp hω
  rw [additiveEnergy_eq_of_sidonModNeg h2 h0 hneg hS, hcard]

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.sidonModNeg_rootsOfUnity_improved
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.improved_threshold_strict
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.rootsOfUnity_additiveEnergy_eq_improved
