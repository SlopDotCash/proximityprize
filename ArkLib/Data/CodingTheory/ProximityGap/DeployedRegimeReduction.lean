/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SmallSubgroupSidon
import ArkLib.Data.CodingTheory.ProximityGap.AdditiveEnergySidonModNeg

/-!
# The exact deployed-regime reduction (#389)

The small-subgroup pin (`SmallSubgroupSidon.lean`) is unconditional only for `p > 2^n`, which the
deployed NTT regime (`n = 2^20 ≫ log p`) does not satisfy.  This file states a *sufficient*
condition for the deployed regime, machine-checked:

`sidonModNeg_of_forall_resultant_ne` — `μ_n ⊆ F_p` is `SidonModNeg` **if** `p` divides none of
the cyclotomic resultants `Res(Φ_n, X^a+X^b−X^c−X^d)` over the exponent configurations with
`{a,b} ≠ {c,d}` **and non-antipodal left pair**, i.e. excluding `2a ≡ 2b ∧ a ≢ b (mod n)`
(equivalently `ζ^a + ζ^b ≠ 0`, the same nonzero-partial-sum condition that the ℂ-Sidon
`fourTerm_sidon` and `primitiveRoot_pow_add_eq_zero_iff` use).  Only this direction is proved;
the converse is not formalized here.

The antipodal exclusion is necessary for the hypothesis to be satisfiable: at `n = 4`, the
configuration `(a,b,c,d) = (0,2,1,3)` has `{a,b} ≠ {c,d}` but
`1 + X² − X − X³ = (1 − X)·Φ₄`, so its resultant with `Φ₄` is `0` and every `p` divides it
(`antipodal_resultant_eq_zero` below).  An earlier version of this premise omitted the exclusion and
was therefore unsatisfiable at `n = 4`, even though `μ_4 ⊆ F_17` is `SidonModNeg`.

For the remaining (non-antipodal) configurations the resultants are nonzero integers (by the ℂ-Sidon
`fourTerm_sidon`), so the condition is a **finite, in-principle-decidable `p`-non-divisibility
condition** on a fixed explicit family of integers.  It is *not* a closure of the deployed prize —
verifying the hypothesis for the deployed `(n, p)` requires factoring `~2^60` very large integers,
which is infeasible, and sporadic primes failing it are known to exist.  But it converts the
abstract "is the deployed prime good?" question into an explicit, machine-checked arithmetic
sufficient condition.  Axiom-clean.
-/

open Polynomial
open ArkLib.ProximityGap.AdditiveEnergySidonModNeg

/-- **The deployed-regime reduction (sufficient condition, machine-checked).** `μ_n ⊆ F_p` is
`SidonModNeg` **if** `p` divides none of the cyclotomic resultants
`Res(Φ_n, X^a+X^b−X^c−X^d)` over the exponent configurations with `{a,b} ≠ {c,d}` whose left pair
is non-antipodal (`¬ (2a ≡ 2b ∧ a ≢ b [MOD n])`, i.e. `ζ^a + ζ^b ≠ 0`).  Antipodal configurations
must be excluded: their polynomial can be divisible by `Φ_n` (see `antipodal_resultant_eq_zero`),
making the resultant `0`.  Only this direction is proved.  (The small-subgroup pin is the special
case where `p > 2^n` forces all the relevant nonzero resultants to be coprime to `p`.) -/
theorem sidonModNeg_of_forall_resultant_ne {n : ℕ} (hn : 0 < n) {p : ℕ} [Fact p.Prime] (hp2 : 2 < p)
    {ζ : ZMod p} (hζ : IsPrimitiveRoot ζ n)
    (hres : ∀ a b c d : ℕ, a < n → b < n → c < n → d < n →
      ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) →
      ¬ (2 * a ≡ 2 * b [MOD n] ∧ ¬ a ≡ b [MOD n]) →
      ¬ (p : ℤ) ∣ resultant (cyclotomic n ℤ)
          (X ^ a + X ^ b - X ^ c - X ^ d)
          (cyclotomic n ℤ).natDegree (X ^ a + X ^ b - X ^ c - X ^ d : ℤ[X]).natDegree) :
    SidonModNeg (Finset.univ.filter (fun x : ZMod p => x ^ n = 1)) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  intro a ha b hb c hc d hd hsum
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2, hab0⟩ := hcon
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb hc hd
  obtain ⟨a', ha'lt, ha'⟩ := hζ.eq_pow_of_pow_eq_one ha
  obtain ⟨b', hb'lt, hb'⟩ := hζ.eq_pow_of_pow_eq_one hb
  obtain ⟨c', hc'lt, hc'⟩ := hζ.eq_pow_of_pow_eq_one hc
  obtain ⟨d', hd'lt, hd'⟩ := hζ.eq_pow_of_pow_eq_one hd
  subst ha' hb' hc' hd'
  have hdist : ¬ ((a' = c' ∧ b' = d') ∨ (a' = d' ∧ b' = c')) := by
    rintro (⟨e1, e2⟩ | ⟨e1, e2⟩)
    · exact h1 (by rw [e1]) (by rw [e2])
    · exact h2 (by rw [e1]) (by rw [e2])
  -- the parallelogram makes `g(ζ) = 0` mod p, so `p ∣ Res`, contradicting `hres`.
  set g : ℤ[X] := X ^ a' + X ^ b' - X ^ c' - X ^ d' with hg
  have hmapP : g.map (Int.castRingHom (ZMod p)) = X ^ a' + X ^ b' - X ^ c' - X ^ d' := by simp [hg]
  have hgζ : (g.map (Int.castRingHom (ZMod p))).eval ζ = 0 := by
    rw [hmapP]; simp only [eval_sub, eval_add, eval_pow, eval_X]; linear_combination hsum
  have hcoeffbd : ∀ k, |g.coeff k| ≤ 2 := fun k => by
    rw [hg]; simp only [coeff_sub, coeff_add, coeff_X_pow]; split_ifs <;> norm_num
  -- the left pair is non-antipodal (exponent form of `ζ^a' + ζ^b' ≠ 0`)
  have hchar : (2 : ZMod p) ≠ 0 := by
    intro h; have h2n : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    have hpd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h2n
    have := Nat.le_of_dvd (by norm_num) hpd; omega
  have hexp : ¬ (2 * a' ≡ 2 * b' [MOD n] ∧ ¬ a' ≡ b' [MOD n]) := fun h =>
    hab0 ((primitiveRoot_pow_add_eq_zero_iff hchar hn hζ).mpr h)
  -- g ≠ 0: a primitive complex root is not a root of g (the ℂ-Sidon, fourTerm_sidon)
  have hg0 : g ≠ 0 := by
    haveI : NeZero ((n : ℕ) : ℂ) := ⟨Nat.cast_ne_zero.mpr hn.ne'⟩
    have hrootne : (cyclotomic n ℂ).roots ≠ 0 := by
      rw [← Multiset.card_pos,
        (IsAlgClosed.splits (cyclotomic n ℂ)).natDegree_eq_card_roots.symm, natDegree_cyclotomic]
      exact n.totient_pos.mpr hn
    obtain ⟨ω, hω⟩ := Multiset.exists_mem_of_ne_zero hrootne
    have hωp : IsPrimitiveRoot ω n := isRoot_cyclotomic_iff.mp (isRoot_of_mem_roots hω)
    have hCsum : ω ^ a' + ω ^ b' ≠ 0 := fun hh =>
      hexp ((primitiveRoot_pow_add_eq_zero_iff (by norm_num) hn hωp).mp hh)
    intro hgeq
    have : (g.map (Int.castRingHom ℂ)).eval ω = 0 := by rw [hgeq]; simp
    rw [show g.map (Int.castRingHom ℂ) = X ^ a' + X ^ b' - X ^ c' - X ^ d' by simp [hg]] at this
    rw [eval_sub, eval_sub, eval_add, eval_pow, eval_pow, eval_pow, eval_pow, eval_X] at this
    exact fourTerm_sidon hn hωp ha'lt hb'lt hc'lt hd'lt hCsum hdist this
  have hgdeg : (g.map (Int.castRingHom (ZMod p))).natDegree = g.natDegree := by
    apply natDegree_map_of_leadingCoeff_ne_zero
    show ((g.leadingCoeff : ℤ) : ZMod p) ≠ 0
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro hdvd
    have hlc0 : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg0
    have hple : (p : ℤ) ≤ |g.leadingCoeff| :=
      Int.le_of_dvd (abs_pos.mpr hlc0) ((dvd_abs (p : ℤ) g.leadingCoeff).mpr hdvd)
    have : (p : ℤ) ≤ 2 := le_trans hple (hcoeffbd g.natDegree)
    omega
  exact hres a' b' c' d' ha'lt hb'lt hc'lt hd'lt hdist hexp
    (dvd_resultant_of_isPrimitiveRoot_isRoot hn g hgdeg hζ hgζ)

namespace ArkLib.ProximityGap.DeployedRegimeReduction

/-- `Φ₄ = X² + 1` over `ℤ`. -/
theorem cyclotomic_four_int : cyclotomic 4 ℤ = X ^ 2 + 1 := by
  have h := cyclotomic_prime_pow_eq_geom_sum (R := ℤ) (p := 2) (n := 1) Nat.prime_two
  norm_num [Finset.sum_range_succ] at h
  simpa [add_comm] using h

/-- **Why antipodal configurations are excluded.** At `n = 4` the configuration
`(a,b,c,d) = (0,2,1,3)` has `{a,b} ≠ {c,d}`, but `1 + X² − X − X³ = (1 − X)·Φ₄`, so its
resultant with `Φ₄` vanishes and every `p` divides it.  Without the antipodal exclusion the
hypothesis of `sidonModNeg_of_forall_resultant_ne` would be unsatisfiable at `n = 4`. -/
theorem antipodal_resultant_eq_zero :
    resultant (cyclotomic 4 ℤ) (X ^ 0 + X ^ 2 - X ^ 1 - X ^ 3 : ℤ[X]) = 0 := by
  have hf : (X ^ 0 + X ^ 2 - X ^ 1 - X ^ 3 : ℤ[X]) = (1 - X) * cyclotomic 4 ℤ := by
    rw [cyclotomic_four_int]; ring
  have hn1 : (1 - X : ℤ[X]) ≠ 0 := by
    intro h
    have hc := congrArg (fun P : ℤ[X] => P.coeff 1) h
    norm_num [Polynomial.coeff_one] at hc
  have hnphi : cyclotomic 4 ℤ ≠ 0 := cyclotomic_ne_zero 4 ℤ
  have hdphi : (cyclotomic 4 ℤ).natDegree ≠ 0 := by
    rw [natDegree_cyclotomic]
    decide
  rw [hf, natDegree_mul hn1 hnphi,
    resultant_mul_right (cyclotomic 4 ℤ) (1 - X) (cyclotomic 4 ℤ)
      (cyclotomic 4 ℤ).natDegree le_rfl,
    resultant_self_eq_zero (cyclotomic 4 ℤ) hdphi, mul_zero]

/-- The configuration `(0,2,1,3)` at `n = 4` is exactly the kind excluded by the antipodal
condition: its left pair satisfies `2·0 ≡ 2·2 ∧ 0 ≢ 2 (mod 4)`. -/
theorem antipodal_config_excluded : 2 * 0 ≡ 2 * 2 [MOD 4] ∧ ¬ 0 ≡ 2 [MOD 4] := by
  decide

end ArkLib.ProximityGap.DeployedRegimeReduction
