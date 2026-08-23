/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SidonLiftAssembly

/-!
# THE CLOSED "NO PARALLELOGRAM" THEOREM — `μ_n ⊂ F_p` IS SIDON FOR `p > 2^n` (#389)

Assembling the cyclotomic resultant bricks into the closed lifting:

* `resultant_fourTerm_ne_zero` — `R = Res(Φ_n, f) ≠ 0` (each complex factor `f(ζ) ≠ 0`);
* `abs_resultant_le` — `|R| ≤ 4^{φ(n)}` (`= 2^n` for `n = 2^m`);
* `resultant_map_eq_zero_of_primitiveRoot` — a parallelogram mod `p` forces `p ∣ R`.

Combined via `Int.le_of_dvd`: a nontrivial parallelogram in `μ_n ⊂ F_p` forces `p ≤ 4^{φ(n)}`.
Hence **for `p > 4^{φ(n)}` there is no nontrivial parallelogram** — `μ_n` is a Sidon set, with no
Weil and no Stepanov.  Issue #389.
-/

open Polynomial Complex

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

/-- The evaluation of the four-term polynomial through any ring map. -/
theorem eval_fourTerm_map {K : Type*} [CommRing K] (φ : ℤ →+* K) (ζ : K) (i j k l : ℕ) :
    eval ζ ((fourTerm i j k l).map φ) = ζ ^ i + ζ ^ j - ζ ^ k - ζ ^ l := by
  simp [fourTerm, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow]

/-- **`R ≠ 0`.**  If for every `n`-th root of unity the four-term value is nonzero (the parallelogram
is nontrivial over ℂ — guaranteed by `fourTerm_ne_zero_of_pair_ne`), then the integer resultant is
nonzero. -/
theorem resultant_fourTerm_ne_zero {n : ℕ} (hn : n ≠ 0) {i j k l : ℕ}
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

/-- **`hne` is satisfiable** (the theorems below are NOT vacuous): for a parallelogram that is a
genuine non-matched pair with nonzero partial sum at every primitive root, the four-term value is
nonzero — directly from `fourTerm_ne_zero_of_pair_ne`. -/
theorem fourTerm_ne_zero_primitive {n : ℕ} (hn : n ≠ 0) {i j k l : ℕ}
    (hsum : ∀ ζ : ℂ, IsPrimitiveRoot ζ n → ζ ^ i + ζ ^ j ≠ 0)
    (hpair : ∀ ζ : ℂ, IsPrimitiveRoot ζ n →
      ¬ ((ζ ^ i = ζ ^ k ∧ ζ ^ j = ζ ^ l) ∨ (ζ ^ i = ζ ^ l ∧ ζ ^ j = ζ ^ k))) :
    ∀ ζ : ℂ, IsPrimitiveRoot ζ n → ζ ^ i + ζ ^ j - ζ ^ k - ζ ^ l ≠ 0 :=
  fun ζ hζ => fourTerm_ne_zero_of_pair_ne hn hζ.pow_eq_one (hsum ζ hζ) (hpair ζ hζ)

/-- **THE CLOSED "NO PARALLELOGRAM" THEOREM.**  Let `n = 2^m`, `p` a prime with a primitive `n`-th
root `ω ∈ ZMod p`.  If `ω^i + ω^j = ω^k + ω^l` is a parallelogram that is nontrivial over ℂ for
every `n`-th root of unity (`∀ ζ, ζ^n=1 → ζ^i+ζ^j-ζ^k-ζ^l ≠ 0`), and the four-term polynomial keeps
its degree mod `p`, then `p ≤ 4^{φ(n)}`.  Contrapositive: for `p > 4^{φ(n)} = 2^n`, `μ_n ⊂ F_p` has
no such parallelogram — it is a Sidon set. -/
theorem prime_le_of_parallelogram {n : ℕ} (hn : n ≠ 0) {p : ℕ} [Fact p.Prime] [NeZero (n : ZMod p)]
    {ω : ZMod p} (hω : IsPrimitiveRoot ω n) {i j k l : ℕ}
    (hfdeg : ((fourTerm i j k l).map (Int.castRingHom (ZMod p))).natDegree = (fourTerm i j k l).natDegree)
    (hpara : ω ^ i + ω ^ j - ω ^ k - ω ^ l = 0)
    (hne : ∀ ζ : ℂ, IsPrimitiveRoot ζ n → ζ ^ i + ζ ^ j - ζ ^ k - ζ ^ l ≠ 0) :
    p ≤ 4 ^ n.totient := by
  set R := resultant (cyclotomic n ℤ) (fourTerm i j k l) with hR
  -- `p ∣ R` from the parallelogram
  have hdvd0 : (algebraMap ℤ (ZMod p)) R = 0 := by
    refine resultant_map_eq_zero_of_primitiveRoot hω (fourTerm i j k l) hfdeg ?_
    rw [eval_fourTerm_map]; exact hpara
  have hpdvd : (p : ℤ) ∣ R := (ZMod.intCast_zmod_eq_zero_iff_dvd R p).mp (by simpa using hdvd0)
  -- `R ≠ 0` and `|R| ≤ 4^φ(n)`, so `p ≤ |R| ≤ 4^φ(n)`
  have hR0 : R ≠ 0 := resultant_fourTerm_ne_zero hn hne
  have hdvdabs : (p : ℤ) ∣ |R| := by rw [Int.abs_eq_natAbs]; exact Int.dvd_natAbs.mpr hpdvd
  have hle : (p : ℤ) ≤ |R| := Int.le_of_dvd (abs_pos.mpr hR0) hdvdabs
  have hbound : |R| ≤ 4 ^ n.totient := abs_resultant_le hn i j k l
  have : (p : ℤ) ≤ (4 ^ n.totient : ℤ) := le_trans hle (by exact_mod_cast hbound)
  exact_mod_cast this

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.resultant_fourTerm_ne_zero
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.prime_le_of_parallelogram
