/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SidonLiftClosed
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergySidonModNeg

/-!
# THE USABLE SMALL-SUBGROUP SIDON ENERGY PIN — `E(μ_n ⊂ F_p) = 3n² − 3n` (#389)

The **all-roots** form of the resultant nonvanishing hypothesis —
`hne : ∀ ζ : ℂ, ζ^n = 1 → ζ^i + ζ^j − ζ^k − ζ^l ≠ 0` — is **unsatisfiable**: at the always-present
`n`-th root `ζ = 1` the four-term value is `1 + 1 − 1 − 1 = 0`, so `hne 1 (one_pow n)` proves
`(0 : ℂ) ≠ 0` (recorded as `allRoots_hne_false` below).  An earlier form of
`SidonLiftClosed.prime_le_of_parallelogram` carried exactly this unsatisfiable hypothesis — axiom-clean
but **vacuous as a brick** — and has since been restated over *primitive* roots.  The fix is the same
either way: the resultant only needs the primitive-root condition, which is satisfiable.  (A sibling
lane, `SidonSubgroupClosed.lean`, develops the small-subgroup energy pin in parallel.)

The fix is mechanical: the resultant `R = Res(Φ_n, f)` is a product over **primitive** `n`-th
roots, so all the proof ever needs is `f(ζ) ≠ 0` at primitive roots — a satisfiable condition.
This file:

* `resultant_fourTerm_ne_zero'` — the de-vacuated nonzero resultant (over primitive roots);
* `fourTerm_natDegree_map` — discharges the named `hfdeg` degree-preservation hypothesis of
  `resultant_map_eq_zero_of_primitiveRoot` (the leading coefficient has `|·| ≤ 2 < p`);
* `prime_le_of_parallelogram'` — the **usable** no-parallelogram theorem (no `hfdeg`, satisfiable
  `hne`);
* `primitiveRoot_pow_eq_iff`, `primitiveRoot_pow_half`, `primitiveRoot_sum_eq_zero_iff` — the
  combinatorial bridge: power-equality and zero-sum among powers of a primitive `n`-th root are
  governed by exponent congruences mod `n`, hence **field-independent** (the same in `F_p` and `ℂ`);
* `fourTerm_ne_zero_primitiveRoots_of_fp` — discharges the `ℂ` hypothesis of
  `prime_le_of_parallelogram'` directly from the `F_p` non-pair-match + non-zero-sum data;
* `sidonModNeg_rootsOfUnity` — `μ_n ⊂ F_p` is Sidon-modulo-negation for `p > 4^{φ(n)}`;
* `rootsOfUnity_additiveEnergy_eq_sidon` — the headline: `E(μ_n) = 3n² − 3n` exactly, for
  `n = 2^m` (so `4^{φ(n)} = 2^n`) and `p > 2^n`, **unconditionally** (no Weil, no Stepanov).

Issue #389.
-/

open Polynomial Complex

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

/-- **The recorded vacuity.**  The all-`n`-th-roots form of `hne` used by the companion
`resultant_fourTerm_ne_zero` / `prime_le_of_parallelogram` is unsatisfiable: at `ζ = 1` the
four-term value is identically `0`. -/
theorem allRoots_hne_false {n i j k l : ℕ}
    (hne : ∀ ζ : ℂ, ζ ^ n = 1 → ζ ^ i + ζ ^ j - ζ ^ k - ζ ^ l ≠ 0) : False := by
  have h := hne 1 (one_pow n)
  simp at h

/-! ## 1. The de-vacuated resultant-nonzero brick (over primitive roots). -/

/-- **`R ≠ 0`, de-vacuated.**  The integer resultant `Res(Φ_n, fourTerm)` is nonzero as soon as the
four-term value is nonzero at every **primitive** `n`-th root of unity — the satisfiable form of the
companion `resultant_fourTerm_ne_zero` (whose all-roots hypothesis is vacuous, `allRoots_hne_false`).
The resultant is a product over primitive roots, so this is all that is needed. -/
theorem resultant_fourTerm_ne_zero' {n : ℕ} (hn : n ≠ 0) {i j k l : ℕ}
    (hne : ∀ ζ : ℂ, IsPrimitiveRoot ζ n → ζ ^ i + ζ ^ j - ζ ^ k - ζ ^ l ≠ 0) :
    resultant (cyclotomic n ℤ) (fourTerm i j k l) ≠ 0 := by
  haveI : NeZero (n : ℂ) := ⟨Nat.cast_ne_zero.mpr hn⟩
  intro hR
  have hcast := resultant_cast_eq_prod (n := n) i j k l
  rw [hR, map_zero] at hcast
  rw [eq_comm, Multiset.prod_eq_zero_iff] at hcast
  obtain ⟨x, hx, hx0⟩ := Multiset.mem_map.mp hcast
  rw [eval_fourTerm_map] at hx0
  exact hne x ((isRoot_cyclotomic_iff (n := n) (R := ℂ)).mp (isRoot_of_mem_roots hx)) hx0

/-! ## 2. Discharge `hfdeg`: the four-term polynomial keeps its degree mod any prime `p > 2`. -/

/-- Every coefficient of `fourTerm i j k l` has absolute value `≤ 2`. -/
theorem fourTerm_coeff_natAbs_le (i j k l d : ℕ) :
    ((fourTerm i j k l).coeff d).natAbs ≤ 2 := by
  rw [fourTerm]
  simp only [coeff_sub, coeff_add, coeff_X_pow]
  split_ifs <;> decide

/-- The leading coefficient of `fourTerm i j k l` has absolute value `≤ 2`. -/
theorem fourTerm_leadingCoeff_natAbs_le (i j k l : ℕ) :
    (fourTerm i j k l).leadingCoeff.natAbs ≤ 2 := by
  rw [Polynomial.leadingCoeff]
  exact fourTerm_coeff_natAbs_le i j k l _

/-- **`hfdeg` discharged.**  For a prime `p > 2`, the four-term polynomial keeps its degree when
reduced mod `p`: its leading coefficient (absolute value `≤ 2`) is nonzero mod `p`. -/
theorem fourTerm_natDegree_map {p : ℕ} (hp : 2 < p) (i j k l : ℕ)
    (hne0 : fourTerm i j k l ≠ 0) :
    ((fourTerm i j k l).map (Int.castRingHom (ZMod p))).natDegree
      = (fourTerm i j k l).natDegree := by
  haveI : NeZero p := ⟨by omega⟩
  apply natDegree_map_of_leadingCoeff_ne_zero
  set c := (fourTerm i j k l).leadingCoeff with hc
  have hc0 : c ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hne0
  have hb : c.natAbs ≤ 2 := fourTerm_leadingCoeff_natAbs_le i j k l
  rw [Int.coe_castRingHom, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  intro hdvd
  have hdvd' : p ∣ c.natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa using this
  have hpos : 0 < c.natAbs := Int.natAbs_pos.mpr hc0
  have : p ≤ c.natAbs := Nat.le_of_dvd hpos hdvd'
  omega

/-! ## 3. The de-vacuated, self-contained no-parallelogram theorem. -/

/-- **THE USABLE NO-PARALLELOGRAM THEOREM.**  For a prime `p > 2` with a primitive `n`-th root
`ω ∈ ZMod p`, if `(i,j,k,l)` is a parallelogram mod `p` that is nontrivial over `ℂ` at every
primitive root (the *satisfiable* hypothesis), then `p ≤ 4^{φ(n)}`.  Discharges both the
unsatisfiable all-roots `hne` (now over primitive roots) and the named `hfdeg` of the original. -/
theorem prime_le_of_parallelogram' {n : ℕ} (hn : n ≠ 0) {p : ℕ} [Fact p.Prime]
    [NeZero (n : ZMod p)] (hp : 2 < p) {ω : ZMod p} (hω : IsPrimitiveRoot ω n) {i j k l : ℕ}
    (hpara : ω ^ i + ω ^ j - ω ^ k - ω ^ l = 0)
    (hne : ∀ ζ : ℂ, IsPrimitiveRoot ζ n → ζ ^ i + ζ ^ j - ζ ^ k - ζ ^ l ≠ 0) :
    p ≤ 4 ^ n.totient := by
  -- fourTerm ≠ 0: it is nonzero at a complex primitive root (which exists for n ≠ 0)
  have hne0 : fourTerm i j k l ≠ 0 := by
    intro h0
    refine hne _ (Complex.isPrimitiveRoot_exp n hn) ?_
    have he := eval_fourTerm_map (Int.castRingHom ℂ)
      (Complex.exp (2 * ↑Real.pi * Complex.I / ↑n)) i j k l
    rw [h0] at he
    simp only [Polynomial.map_zero, eval_zero] at he
    exact he.symm
  -- the degree-preservation hypothesis, discharged from `p > 2`
  have hfdeg : ((fourTerm i j k l).map (Int.castRingHom (ZMod p))).natDegree
      = (fourTerm i j k l).natDegree := fourTerm_natDegree_map hp i j k l hne0
  set R := resultant (cyclotomic n ℤ) (fourTerm i j k l) with hR
  have hdvd0 : (algebraMap ℤ (ZMod p)) R = 0 := by
    refine resultant_map_eq_zero_of_primitiveRoot hω (fourTerm i j k l) hfdeg ?_
    rw [eval_fourTerm_map]; exact hpara
  have hpdvd : (p : ℤ) ∣ R := (ZMod.intCast_zmod_eq_zero_iff_dvd R p).mp (by simpa using hdvd0)
  have hR0 : R ≠ 0 := resultant_fourTerm_ne_zero' hn hne
  have hdvdabs : (p : ℤ) ∣ |R| := by rw [Int.abs_eq_natAbs]; exact Int.dvd_natAbs.mpr hpdvd
  have hle : (p : ℤ) ≤ |R| := Int.le_of_dvd (abs_pos.mpr hR0) hdvdabs
  have hbound : |R| ≤ 4 ^ n.totient := abs_resultant_le hn i j k l
  have hfin : (p : ℤ) ≤ (4 ^ n.totient : ℤ) := le_trans hle (by exact_mod_cast hbound)
  exact_mod_cast hfin

/-! ## 4. The combinatorial bridge: F_p coincidence conditions ⟺ exponent conditions ⟺ ℂ. -/

/-- For a primitive `n`-th root `ω` in a field, `ω^a = ω^b ↔ a ≡ b [MOD n]`.  Field-independent on
the right — this is the bridge between `F_p` and `ℂ`. -/
theorem primitiveRoot_pow_eq_iff {K : Type*} [Field K] {ω : K} {n : ℕ} (hn0 : n ≠ 0)
    (hω : IsPrimitiveRoot ω n) (a b : ℕ) : ω ^ a = ω ^ b ↔ a ≡ b [MOD n] := by
  have ho : orderOf ω = n := hω.eq_orderOf.symm
  have hfin : IsOfFinOrder ω :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨n, Nat.pos_of_ne_zero hn0, hω.pow_eq_one⟩
  rw [← ho]; exact hfin.pow_eq_pow_iff_modEq

/-- For a primitive `n`-th root `ω` in a field with `n` even, `ω^(n/2) = -1`. -/
theorem primitiveRoot_pow_half {K : Type*} [Field K] {ω : K} {n : ℕ}
    (hn2 : 2 ∣ n) (hn0 : n ≠ 0) (hω : IsPrimitiveRoot ω n) : ω ^ (n / 2) = -1 := by
  obtain ⟨h, rfl⟩ := hn2
  rw [show 2 * h / 2 = h from by omega]
  have hsq' : ω ^ h * ω ^ h = 1 := by
    rw [← pow_add, show h + h = 2 * h from by omega]; exact hω.pow_eq_one
  have hne1 : ω ^ h ≠ 1 := hω.pow_ne_one_of_pos_of_lt (by omega) (by omega)
  rcases mul_self_eq_one_iff.mp hsq' with h1 | h1
  · exact absurd h1 hne1
  · exact h1

/-- For a primitive `n`-th root `ω` in a field with `n` even,
`ω^a + ω^b = 0 ↔ a ≡ b + n/2 [MOD n]`.  Field-independent on the right. -/
theorem primitiveRoot_sum_eq_zero_iff {K : Type*} [Field K] {ω : K} {n : ℕ}
    (hn2 : 2 ∣ n) (hn0 : n ≠ 0) (hω : IsPrimitiveRoot ω n) (a b : ℕ) :
    ω ^ a + ω ^ b = 0 ↔ a ≡ b + n / 2 [MOD n] := by
  have hhalf : ω ^ (n / 2) = -1 := primitiveRoot_pow_half hn2 hn0 hω
  rw [← primitiveRoot_pow_eq_iff hn0 hω a (b + n / 2), pow_add, hhalf, mul_neg, mul_one,
    add_eq_zero_iff_eq_neg]

/-- **The combinatorial discharge.**  If a parallelogram of exponents is non-pair-matched and
non-zero-sum at the `F_p` primitive root `ω` (`n` even), then the `ℂ` four-term is nonzero at every
complex primitive `n`-th root — the satisfiable hypothesis of `prime_le_of_parallelogram'`.  Both
conditions transfer because they reduce to the field-independent exponent congruences. -/
theorem fourTerm_ne_zero_primitiveRoots_of_fp {n : ℕ} (hn2 : 2 ∣ n) (hn0 : n ≠ 0)
    {p : ℕ} [Fact p.Prime] {ω : ZMod p} (hω : IsPrimitiveRoot ω n) {i j k l : ℕ}
    (hsum : ω ^ i + ω ^ j ≠ 0)
    (hpair : ¬ ((ω ^ i = ω ^ k ∧ ω ^ j = ω ^ l) ∨ (ω ^ i = ω ^ l ∧ ω ^ j = ω ^ k))) :
    ∀ ζ : ℂ, IsPrimitiveRoot ζ n → ζ ^ i + ζ ^ j - ζ ^ k - ζ ^ l ≠ 0 := by
  intro ζ hζ
  refine fourTerm_ne_zero_of_pair_ne hn0 hζ.pow_eq_one ?_ ?_
  · -- ζ^i + ζ^j ≠ 0  (zero-sum transfers via the exponent congruence)
    intro hz
    rw [primitiveRoot_sum_eq_zero_iff hn2 hn0 hζ] at hz
    exact hsum ((primitiveRoot_sum_eq_zero_iff hn2 hn0 hω i j).mpr hz)
  · -- ¬ pair-match in ℂ (pair-match transfers via the exponent congruences)
    rw [primitiveRoot_pow_eq_iff hn0 hζ, primitiveRoot_pow_eq_iff hn0 hζ,
      primitiveRoot_pow_eq_iff hn0 hζ, primitiveRoot_pow_eq_iff hn0 hζ]
    rw [primitiveRoot_pow_eq_iff hn0 hω, primitiveRoot_pow_eq_iff hn0 hω,
      primitiveRoot_pow_eq_iff hn0 hω, primitiveRoot_pow_eq_iff hn0 hω] at hpair
    exact hpair

/-! ## 5. The payoff: `μ_n ⊂ F_p` is Sidon-mod-negation for `p > 4^{φ(n)}`. -/

open ArkLib.ProximityGap.AdditiveEnergySidonModNeg in
/-- **`μ_n ⊂ F_p` is Sidon-modulo-negation** (the only additive coincidences are trivial or
zero-sum) when `p > 4^{φ(n)}` and `n` is even.  This is the no-parallelogram theorem turned into the
clean structural input that `additiveEnergy_eq_of_sidonModNeg` consumes.  `S` is the explicit set of
`n`-th roots `{ω^t : t < n}`. -/
theorem sidonModNeg_rootsOfUnity {n : ℕ} (hn2 : 2 ∣ n) (hn0 : n ≠ 0)
    {p : ℕ} [Fact p.Prime] [NeZero (n : ZMod p)] (hp : 4 ^ n.totient < p)
    {ω : ZMod p} (hω : IsPrimitiveRoot ω n) :
    SidonModNeg ((Finset.range n).image (ω ^ ·)) := by
  have hp2 : 2 < p := by
    have : (4 : ℕ) ≤ 4 ^ n.totient :=
      Nat.le_self_pow (by have : 1 ≤ n.totient := Nat.totient_pos.mpr (by omega); omega) 4
    omega
  intro a ha b hb c hc d hd hsum
  simp only [Finset.mem_image, Finset.mem_range] at ha hb hc hd
  obtain ⟨ea, _, rfl⟩ := ha
  obtain ⟨eb, _, rfl⟩ := hb
  obtain ⟨ec, _, rfl⟩ := hc
  obtain ⟨ed, _, rfl⟩ := hd
  by_contra hcon
  push_neg at hcon
  obtain ⟨hnp1, hnp2, hns⟩ := hcon
  have hpara : ω ^ ea + ω ^ eb - ω ^ ec - ω ^ ed = 0 := by rw [hsum]; ring
  have hpair :
      ¬ ((ω ^ ea = ω ^ ec ∧ ω ^ eb = ω ^ ed) ∨ (ω ^ ea = ω ^ ed ∧ ω ^ eb = ω ^ ec)) := by
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact hnp1 h1 h2
    · exact hnp2 h1 h2
  have hne := fourTerm_ne_zero_primitiveRoots_of_fp hn2 hn0 hω hns hpair
  have := prime_le_of_parallelogram' hn0 hp2 hω hpara hne
  omega

/-! ## 6. THE FINISHED HEADLINE: the exact additive energy `E(μ_n ⊂ F_p) = 3n² − 3n`. -/

open ArkLib.ProximityGap.AdditiveEnergySidonModNeg Finset in
/-- **`E(μ_n ⊂ F_p) = 3n² − 3n` exactly, for `n = 2^m` and `p > 4^{φ(n)} = 2^n`.**  The explicit
small-subgroup Sidon energy pin, fully unconditional (no Weil, no Stepanov): `p > 2^n` makes the
`n`-th roots of unity a Sidon-mod-negation set, whose additive energy is exactly the char-0 minimal
value `3n(n − 1)`. -/
theorem rootsOfUnity_additiveEnergy_eq_sidon {n : ℕ} (hn2 : 2 ∣ n) (hn0 : n ≠ 0)
    {p : ℕ} [Fact p.Prime] [NeZero (n : ZMod p)] (hp : 4 ^ n.totient < p)
    {ω : ZMod p} (hω : IsPrimitiveRoot ω n) :
    additiveEnergy ((Finset.range n).image (ω ^ ·)) = 3 * n ^ 2 - 3 * n := by
  set G := (Finset.range n).image (ω ^ ·) with hG
  have hp2 : 2 < p := by
    have : (4 : ℕ) ≤ 4 ^ n.totient :=
      Nat.le_self_pow (by have : 1 ≤ n.totient := Nat.totient_pos.mpr (by omega); omega) 4
    omega
  haveI : NeZero p := ⟨by omega⟩
  have hω0 : ω ≠ 0 := by
    intro h; have h1 := hω.pow_eq_one; rw [h, zero_pow hn0] at h1; exact zero_ne_one h1
  have h2 : (2 : ZMod p) ≠ 0 := by
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_cast, Ne,
      CharP.cast_eq_zero_iff (ZMod p) p]
    intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega
  have h0 : (0 : ZMod p) ∉ G := by
    rw [hG]; intro hmem
    simp only [Finset.mem_image, Finset.mem_range] at hmem
    obtain ⟨t, _, ht⟩ := hmem; exact pow_ne_zero t hω0 ht
  have hneg : ∀ x ∈ G, -x ∈ G := by
    rw [hG]; intro x hx
    simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
    obtain ⟨t, _, rfl⟩ := hx
    refine ⟨(n / 2 + t) % n, Nat.mod_lt _ (by omega), ?_⟩
    rw [(primitiveRoot_pow_eq_iff hn0 hω ((n / 2 + t) % n) (n / 2 + t)).mpr (Nat.mod_modEq _ _),
      pow_add, primitiveRoot_pow_half hn2 hn0 hω]; ring
  have hcard : G.card = n := by
    rw [hG, Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have h := (primitiveRoot_pow_eq_iff hn0 hω a b).mp hab
    unfold Nat.ModEq at h
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  have hS : SidonModNeg G := sidonModNeg_rootsOfUnity hn2 hn0 hp hω
  rw [additiveEnergy_eq_of_sidonModNeg h2 h0 hneg hS, hcard]

/-- For `n = 2^m` (`m ≥ 1`), `4^{φ(n)} = 2^n`: the resultant bound is exactly `2^n`. -/
theorem four_pow_totient_two_pow {m : ℕ} (hm : 1 ≤ m) :
    (4 : ℕ) ^ ((2 ^ m : ℕ).totient) = 2 ^ (2 ^ m) := by
  have htot : (2 ^ m : ℕ).totient = 2 ^ (m - 1) := by
    rw [Nat.totient_prime_pow Nat.prime_two (by omega)]; simp
  rw [htot, show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
  congr 1
  rw [show 2 * 2 ^ (m - 1) = 2 ^ m from by rw [← pow_succ']; congr 1; omega]

open Finset in
/-- **The issue-statement form.**  For `n = 2^m` and a prime `p > 2^n`, the additive energy of the
`n`-th roots of unity in `F_p` is exactly `3n² − 3n` — the explicit small-subgroup Sidon energy pin,
unconditional. -/
theorem rootsOfUnity_additiveEnergy_eq_sidon_two_pow {m : ℕ} (hm : 1 ≤ m)
    {p : ℕ} [Fact p.Prime] [NeZero ((2 ^ m : ℕ) : ZMod p)] (hp : 2 ^ (2 ^ m) < p)
    {ω : ZMod p} (hω : IsPrimitiveRoot ω (2 ^ m)) :
    additiveEnergy ((Finset.range (2 ^ m)).image (ω ^ ·)) = 3 * (2 ^ m) ^ 2 - 3 * 2 ^ m := by
  refine rootsOfUnity_additiveEnergy_eq_sidon (dvd_pow_self 2 (by omega)) (by positivity) ?_ hω
  rw [four_pow_totient_two_pow hm]; exact hp

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.prime_le_of_parallelogram'
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.sidonModNeg_rootsOfUnity
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.rootsOfUnity_additiveEnergy_eq_sidon
#print axioms
  ArkLib.ProximityGap.AdditiveEnergyRepBound.rootsOfUnity_additiveEnergy_eq_sidon_two_pow
