/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SidonParsevalGeneral
import ArkLib.Data.CodingTheory.ProximityGap.SidonParsevalNthRoots
import ArkLib.Data.CodingTheory.ProximityGap.SidonLiftAssembly
import ArkLib.Data.CodingTheory.ProximityGap.ManyTermResultantBound
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# THE SHARP SIX-TERM CYCLOTOMIC RESULTANT BOUND — `|Res|² ≤ 12^{φ(n)}` (the `r = 3` RepThree lift, #407)

This is the **`r = 3` analogue of `SidonResultantImproved.abs_resultant_fourTerm_sq_le`** (the four-term
`|Res|² ≤ 8^{φ(n)}` Sidon lift). A genuine (non-antipodally-paired) zero-sum **six**-tuple of `n`-th
roots `ζ^a+ζ^b+ζ^c = ζ^d+ζ^e+ζ^f` is exactly a root of the six-term polynomial

> `sixTerm a b c d e f = X^a + X^b + X^c − X^d − X^e − X^f`.

For `n = 2^m` and pairwise-distinct exponents, the **sharp Parseval `ℓ²` average** over `μ_n` is
`∑_{ζ ∈ μ_n} ‖sixTerm(ζ)‖² = 6n` (`parseval_general`, six unit coefficients), so **AM-GM** over the
`φ(n) = n/2` primitive roots gives

> `sixterm_resultant_sq_le` :  `|Res(Φ_n, sixTerm)|² ≤ 12^{φ(n)}`   (i.e. `|Res| ≤ 12^{n/4} = 2^{(log₂12)·n/4} ≈ 2^{0.896 n}`),

**strictly sharper** than the pointwise general bound `ManyTermResultant.abs_resultant_manyTerm_le`
(`|Res| ≤ 6^{φ(n)} = 6^{n/2} = 2^{1.29 n}`). Probe-verified **tight** (`max |Res| = 12^{n/4} = 144` at
`n = 8`), and probe-verified that the implied prime threshold is the right scale: a genuine six-term
relation over `F_p` (`p ≡ 1 mod n`, `μ_n` proper) appears only at primes `p ≤ 12^{n/4}` (e.g. `p = 17`
for `n = 8`), so **for `p > 12^{n/4}` every genuine six-term relation is forced to vanish ⟹ `RepThree(μ_n)`**.

This sharpens the `r = 3` energy-rung Sidon threshold (`DCEnergyRungThree.dcEnergyBound_three_of_repThree`,
which reduces `DCEnergyBound G 3` to `RepThree G`) from the pointwise `p > 6^{n/2}` to the sharp
`p > 12^{n/4}` — a constructive char-`p` transfer of the order-6 antipodal-pairing residual, the exact
`r = 3` analogue of the landed `r = 2` four-term lift. (The frontier `r ~ log q` still exceeds any
fixed-`r` threshold, consistent with the open core; this is the next unconditional rung, not a closure.)

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`. Issue #407.
-/

set_option linter.style.longLine false


open Complex Finset Polynomial

namespace ArkLib.ProximityGap.SixTermResultant

open ArkLib.ProximityGap.AdditiveEnergyRepBound

/-- The integer six-term polynomial `X^a + X^b + X^c − X^d − X^e − X^f`, encoding the candidate
order-6 relation `ζ^a + ζ^b + ζ^c = ζ^d + ζ^e + ζ^f` among `n`-th roots. -/
noncomputable def sixTerm (a b c d e f : ℕ) : ℤ[X] :=
  X ^ a + X ^ b + X ^ c - X ^ d - X ^ e - X ^ f

/-- Evaluation of the mapped six-term at any commutative-ring point. -/
theorem eval_sixTerm_map {K : Type*} [CommRing K] (φ : ℤ →+* K) (ζ : K) (a b c d e f : ℕ) :
    eval ζ ((sixTerm a b c d e f).map φ) = ζ ^ a + ζ ^ b + ζ ^ c - ζ ^ d - ζ ^ e - ζ ^ f := by
  simp [sixTerm]

/-- The six unit roots `![ζ^a, ζ^b, ζ^c, ζ^d, ζ^e, ζ^f]` as a `Fin 6 → ℂ` family. -/
noncomputable def sixVals (ω : ℂ) (a b c d e f : ℕ) : Fin 6 → ℂ :=
  ![ω ^ a, ω ^ b, ω ^ c, ω ^ d, ω ^ e, ω ^ f]

/-- The signed coefficient vector `![1, 1, 1, −1, −1, −1]` for the six-term. -/
noncomputable def sixSigns : Fin 6 → ℂ := ![1, 1, 1, -1, -1, -1]

/-- `∑_a ‖sixSigns a‖² = 6`. -/
theorem sixSigns_sq_sum : ∑ a : Fin 6, ‖sixSigns a‖ ^ 2 = 6 := by
  simp [sixSigns, Fin.sum_univ_six]; norm_num

/-- The six-term value as the `parseval_general` linear combination at `ω^t`. -/
theorem sixTerm_eq_lincomb (ω : ℂ) (a b c d e f : ℕ) (t : ℕ) :
    (ω ^ t) ^ a + (ω ^ t) ^ b + (ω ^ t) ^ c - (ω ^ t) ^ d - (ω ^ t) ^ e - (ω ^ t) ^ f
      = ∑ i : Fin 6, sixSigns i * (sixVals ω a b c d e f i) ^ t := by
  simp only [sixVals, sixSigns, Fin.sum_univ_six]
  simp only [Matrix.cons_val]
  ring

/-- **Parseval over `μ_n` for the six-term.** For a primitive `n`-th root `ω` (`n ≠ 0`) with
pairwise-distinct powers, `∑_{x ∈ μ_n} ‖x^a+x^b+x^c−x^d−x^e−x^f‖² = 6n`. -/
theorem parseval_sixTerm_nthRoots {n : ℕ} (hn : n ≠ 0) {ω : ℂ} (hω : IsPrimitiveRoot ω n)
    {a b c d e f : ℕ}
    (hdist : Function.Injective (sixVals ω a b c d e f)) :
    ∑ x ∈ Polynomial.nthRootsFinset n (1 : ℂ),
        ‖x ^ a + x ^ b + x ^ c - x ^ d - x ^ e - x ^ f‖ ^ 2 = 6 * n := by
  rw [sum_nthRootsFinset_reindex hω
      (fun x => ‖x ^ a + x ^ b + x ^ c - x ^ d - x ^ e - x ^ f‖ ^ 2)]
  have hrw : ∀ t ∈ Finset.range n,
      ‖(ω ^ t) ^ a + (ω ^ t) ^ b + (ω ^ t) ^ c - (ω ^ t) ^ d - (ω ^ t) ^ e - (ω ^ t) ^ f‖ ^ 2
        = ‖∑ i : Fin 6, sixSigns i * (sixVals ω a b c d e f i) ^ t‖ ^ 2 := by
    intro t _; rw [sixTerm_eq_lincomb]
  rw [Finset.sum_congr rfl hrw]
  have hpe : ∀ k : ℕ, (ω ^ k) ^ n = 1 := by
    intro k; rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
  have hvn : ∀ i, (sixVals ω a b c d e f i) ^ n = 1 := by
    intro i
    fin_cases i <;> · simp only [sixVals]; exact hpe _
  have hnorm : ∀ i, ‖sixVals ω a b c d e f i‖ = 1 := fun i =>
    norm_eq_one_of_primitiveRoot hn (hvn i)
  rw [parseval_general (sixVals ω a b c d e f) hvn hnorm hdist sixSigns, sixSigns_sq_sum]
  ring

/-- The integer resultant equals the complex product over primitive roots (six-term). -/
theorem resultant_cast_eq_prod_six {n : ℕ} (a b c d e f : ℕ) :
    (algebraMap ℤ ℂ) (resultant (cyclotomic n ℤ) (sixTerm a b c d e f)) =
      (((cyclotomic n ℂ).roots).map
        (fun ζ => ζ ^ a + ζ ^ b + ζ ^ c - ζ ^ d - ζ ^ e - ζ ^ f)).prod := by
  rw [ManyTermResultant.resultant_cast_eq_prod_gen (sixTerm a b c d e f)]
  apply congrArg
  apply Multiset.map_congr rfl
  intro ζ _
  exact eval_sixTerm_map (algebraMap ℤ ℂ) ζ a b c d e f

/-- **THE SHARP SIX-TERM RESULTANT BOUND.** For `n = 2^m` (`m ≥ 1`) and a six-term whose `ω`-powers
are pairwise distinct, `|Res(Φ_n, sixTerm)|² ≤ 12^{φ(n)}` — i.e. `|Res| ≤ 12^{φ(n)/2} = 12^{n/4}`,
sharper than the pointwise `6^{φ(n)} = 6^{n/2}`. Via Parseval `∑_{prim} ‖f(ζ)‖² ≤ 6n` and AM-GM over
the `φ(n) = n/2` primitive roots. -/
theorem sixterm_resultant_sq_le {m : ℕ} (hm : 1 ≤ m) {ω : ℂ}
    (hω : IsPrimitiveRoot ω (2 ^ m)) {a b c d e f : ℕ}
    (hdist : Function.Injective (sixVals ω a b c d e f)) :
    (resultant (cyclotomic (2 ^ m) ℤ) (sixTerm a b c d e f)).natAbs ^ 2 ≤ 12 ^ (2 ^ m).totient := by
  classical
  set n := 2 ^ m with hn_def
  have hn0 : n ≠ 0 := by positivity
  have hn0' : 0 < n := Nat.pos_of_ne_zero hn0
  haveI : NeZero (n : ℂ) := ⟨Nat.cast_ne_zero.mpr hn0⟩
  set R := resultant (cyclotomic n ℤ) (sixTerm a b c d e f) with hR
  set g : ℂ → ℂ := fun ζ => ζ ^ a + ζ ^ b + ζ ^ c - ζ ^ d - ζ ^ e - ζ ^ f with hg
  have hcast : (algebraMap ℤ ℂ) R = ((cyclotomic n ℂ).roots.map g).prod :=
    resultant_cast_eq_prod_six a b c d e f
  have hgsq : ∀ ζ : ℂ, Complex.normSq (g ζ) = ‖g ζ‖ ^ 2 := fun ζ => Complex.normSq_eq_norm_sq _
  have hprodeq : (Complex.normSq ((algebraMap ℤ ℂ) R))
      = ∏ ζ ∈ primitiveRoots n ℂ, Complex.normSq (g ζ) := by
    rw [hcast, map_multiset_prod, Multiset.map_map, cyclotomic.roots_eq_primitiveRoots_val]
    rfl
  have hlhs : Complex.normSq ((algebraMap ℤ ℂ) R) = ((R.natAbs : ℝ)) ^ 2 := by
    have hns : ((R.natAbs : ℝ)) ^ 2 = (R : ℝ) ^ 2 := by
      have hcastabs : (R.natAbs : ℝ) = |(R : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
      rw [hcastabs]; exact sq_abs (R : ℝ)
    have halg : (algebraMap ℤ ℂ) R = (R : ℂ) := by simp [algebraMap_int_eq]
    rw [halg, Complex.normSq_intCast, ← pow_two, hns]
  -- the sum over primitive roots ≤ 6n
  have hsub : primitiveRoots n ℂ ⊆ nthRootsFinset n (1 : ℂ) := by
    intro ζ hζ
    rw [mem_primitiveRoots hn0'] at hζ
    rw [mem_nthRootsFinset hn0']; exact hζ.pow_eq_one
  have hsum_le : ∑ ζ ∈ primitiveRoots n ℂ, Complex.normSq (g ζ) ≤ 6 * (n : ℝ) := by
    calc ∑ ζ ∈ primitiveRoots n ℂ, Complex.normSq (g ζ)
        ≤ ∑ ζ ∈ nthRootsFinset n (1 : ℂ), Complex.normSq (g ζ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ζ _ _ => Complex.normSq_nonneg _)
      _ = ∑ ζ ∈ nthRootsFinset n (1 : ℂ), ‖g ζ‖ ^ 2 :=
          Finset.sum_congr rfl (fun ζ _ => hgsq ζ)
      _ = 6 * n := parseval_sixTerm_nthRoots hn0 hω hdist
  have hcard : (primitiveRoots n ℂ).card = n.totient := hω.card_primitiveRoots
  have htot : (n.totient : ℝ) * 12 = 6 * n := by
    have h1 : n.totient = 2 ^ (m - 1) := by
      rw [hn_def, Nat.totient_prime_pow Nat.prime_two (by omega)]; simp
    rw [h1, hn_def]; push_cast
    rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, show (6 : ℝ) = 2 * 3 by norm_num]
    rw [show (2 : ℝ) ^ m = 2 ^ (m - 1) * 2 by rw [← pow_succ]; congr 1; omega]
    ring
  have hAMGM : ∏ ζ ∈ primitiveRoots n ℂ, Complex.normSq (g ζ) ≤ 12 ^ n.totient := by
    refine prod_le_of_sum_le (primitiveRoots n ℂ) (fun ζ => Complex.normSq (g ζ))
      (fun ζ _ => Complex.normSq_nonneg _) n.totient hcard 12 ?_
    rw [htot]; exact hsum_le
  have hfin : ((R.natAbs : ℝ)) ^ 2 ≤ 12 ^ n.totient := by
    rw [← hlhs, hprodeq]; exact hAMGM
  have hcastfin : ((R.natAbs ^ 2 : ℕ) : ℝ) ≤ ((12 ^ n.totient : ℕ) : ℝ) := by
    push_cast; exact hfin
  exact_mod_cast hcastfin

/-- The mapped six-term `f.map(Int.castRingHom K)` evaluates as expected at any field point. -/
theorem eval_sixTerm_castMap {K : Type*} [Field K] (ζ : K) (a b c d e f : ℕ) :
    ((sixTerm a b c d e f).map (Int.castRingHom K)).eval ζ
      = ζ ^ a + ζ ^ b + ζ ^ c - ζ ^ d - ζ ^ e - ζ ^ f := by
  rw [← eval_sixTerm_map (Int.castRingHom K) ζ a b c d e f]

/-- **THE CHAR-`p` SIX-TERM LIFT (`r = 3` RepThree transfer).** For `n = 2^m` (`m ≥ 1`), a primitive
`n`-th root `ω ∈ ZMod p`, a **genuine** six-term relation `ω^a+ω^b+ω^c = ω^d+ω^e+ω^f` over `F_p`
(distinct ω-powers, `hpara`) that does **not** hold at any complex primitive `n`-th root (`hne`, i.e.
it is not a char-0 / antipodally-paired relation) forces `p ≤ 12^{φ(n)/2} = 12^{n/4}`. So **for
`p > 12^{n/4}` there is no genuine six-term relation in `μ_n` — i.e. `RepThree(μ_n)` holds**. This is the
sharp `r = 3` analogue of `prime_le_of_parallelogram'`, discharging the open char-`p` residual of
`DCEnergyRungThree.dcEnergyBound_three_of_repThree` above the sharp threshold. -/
theorem prime_le_of_genuineSixTerm {m : ℕ} (hm : 1 ≤ m) {p : ℕ} [Fact p.Prime]
    [NeZero ((2 ^ m : ℕ) : ZMod p)] {ω : ZMod p} (hωp : IsPrimitiveRoot ω (2 ^ m))
    {a b c d e f : ℕ}
    (hfdeg : ((sixTerm a b c d e f).map (Int.castRingHom (ZMod p))).natDegree
        = (sixTerm a b c d e f).natDegree)
    (hpara : ω ^ a + ω ^ b + ω ^ c - ω ^ d - ω ^ e - ω ^ f = 0)
    {ωc : ℂ} (hωc : IsPrimitiveRoot ωc (2 ^ m))
    (hdist : Function.Injective (sixVals ωc a b c d e f))
    (hne : ∀ ζ : ℂ, IsPrimitiveRoot ζ (2 ^ m) →
        ζ ^ a + ζ ^ b + ζ ^ c - ζ ^ d - ζ ^ e - ζ ^ f ≠ 0) :
    p ^ 2 ≤ 12 ^ (2 ^ m).totient := by
  set n := 2 ^ m with hn_def
  have hn0 : n ≠ 0 := by positivity
  haveI : NeZero (n : ℂ) := ⟨Nat.cast_ne_zero.mpr hn0⟩
  set R := resultant (cyclotomic n ℤ) (sixTerm a b c d e f) with hR
  -- `p ∣ R` from the genuine relation mod p
  have hdvd0 : (algebraMap ℤ (ZMod p)) R = 0 := by
    refine resultant_map_eq_zero_of_primitiveRoot hωp (sixTerm a b c d e f) hfdeg ?_
    rw [eval_sixTerm_castMap]; exact hpara
  have hpdvd : (p : ℤ) ∣ R := (ZMod.intCast_zmod_eq_zero_iff_dvd R p).mp (by simpa using hdvd0)
  -- `R ≠ 0`: the resultant is the product over complex primitive roots, each factor nonzero by `hne`
  have hR0 : R ≠ 0 := by
    intro h0
    have hcast0 : (algebraMap ℤ ℂ) R = 0 := by rw [h0]; simp
    have hprod : (((cyclotomic n ℂ).roots).map
        (fun ζ => ζ ^ a + ζ ^ b + ζ ^ c - ζ ^ d - ζ ^ e - ζ ^ f)).prod = 0 := by
      rw [← resultant_cast_eq_prod_six a b c d e f]; exact hcast0
    rw [Multiset.prod_eq_zero_iff] at hprod
    obtain ⟨x, hx, hx0⟩ := Multiset.mem_map.mp hprod
    have hxprim : IsPrimitiveRoot x n := by
      rw [cyclotomic.roots_eq_primitiveRoots_val, Finset.mem_val,
        mem_primitiveRoots (Nat.pos_of_ne_zero hn0)] at hx
      exact hx
    exact hne x hxprim hx0
  -- `p ≤ |R|`, and `|R|² = (R.natAbs)² ≤ 12^{φ(n)}`
  have hdvdabs : (p : ℤ) ∣ |R| := by rw [Int.abs_eq_natAbs]; exact Int.dvd_natAbs.mpr hpdvd
  have hle : (p : ℤ) ≤ |R| := Int.le_of_dvd (abs_pos.mpr hR0) hdvdabs
  have hpnat : p ≤ R.natAbs := by
    have : (p : ℤ) ≤ (R.natAbs : ℤ) := by rwa [Int.abs_eq_natAbs] at hle
    exact_mod_cast this
  have hsq : p ^ 2 ≤ R.natAbs ^ 2 := Nat.pow_le_pow_left hpnat 2
  have hbound : R.natAbs ^ 2 ≤ 12 ^ n.totient := sixterm_resultant_sq_le hm hωc hdist
  exact le_trans hsq hbound

end ArkLib.ProximityGap.SixTermResultant

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SixTermResultant.sixterm_resultant_sq_le
#print axioms ArkLib.ProximityGap.SixTermResultant.parseval_sixTerm_nthRoots
#print axioms ArkLib.ProximityGap.SixTermResultant.prime_le_of_genuineSixTerm
