/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CyclotomicResultantBound

/-!
# The complete small-subgroup Sidon keystone (#389)

This file assembles the cyclotomic-resultant pipeline (`CyclotomicResultantBound.lean`) into the
end-to-end statement: **a nontrivial additive parallelogram among the `n`-th roots of unity in
`F_p` forces `p ≤ 2^n`** (`n = 2^m`).

`prime_le_of_zeta_parallelogram`: for a primitive `n`-th root `ζ ∈ ZMod p` (`p` prime, `p > 2`),
if `ζ^a + ζ^b = ζ^c + ζ^d` with nonzero sum and `{a,b} ≠ {c,d}`, then `p ≤ 4^{φ(n)} = 2^n`.

The proof sets `g = X^a + X^b − X^c − X^d` and feeds `prime_le_of_cyclotomic_parallelogram`:
the magnitude bound `‖g(ω)‖ ≤ 4` (4-term), the ℂ-Sidon `hSidon` (`fourTerm_sidon`, with the
nonzero-sum side condition transferred from `F_p` to `ℂ` by `primitiveRoot_pow_add_eq_zero_iff`),
the degree condition (the 4-term leading coefficient has `|·| ≤ 2 < p`, so it survives mod `p`),
and the root `g(ζ) = 0`.  `g ≠ 0` follows because some primitive root is not a root of `g`.

**Contrapositive**: `p > 2^n ⟹ μ_n ⊆ F_p` has no nontrivial additive parallelogram, i.e.
`SidonModNeg(μ_n)`; with `rootsOfUnity_additiveEnergy_eq` that pins `E(μ_n) = 3n(n−1)` and hence
δ* to its ladder value — **unconditionally, for every explicit smooth-RS code of length
`n < log₂ p`**.  Axiom-clean.
-/

open Polynomial

/-- **The complete small-subgroup keystone.** If a primitive `n`-th root `ζ` of `ZMod p`
(`p` prime, `p > 2`) admits a nontrivial additive parallelogram `ζ^a+ζ^b = ζ^c+ζ^d` with nonzero
sum and `{a,b} ≠ {c,d}`, then `p ≤ 4^{φ(n)} = 2^n`.  Contrapositive: `p > 2^n` rules out every
nontrivial parallelogram in `μ_n ⊆ F_p`, i.e. `μ_n` is `SidonModNeg`. -/
theorem prime_le_of_zeta_parallelogram {n : ℕ} (hn : 0 < n) {p : ℕ} [Fact p.Prime] (hp2 : 2 < p)
    {ζ : ZMod p} (hζ : IsPrimitiveRoot ζ n) {a b c d : ℕ}
    (ha : a < n) (hb : b < n) (hc : c < n) (hd : d < n)
    (hpar : ζ ^ a + ζ ^ b = ζ ^ c + ζ ^ d) (hsum : ζ ^ a + ζ ^ b ≠ 0)
    (hdist : ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c))) :
    p ≤ 4 ^ n.totient := by
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).ne_zero⟩
  haveI : NeZero n := ⟨hn.ne'⟩
  have hp2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    have h2n : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    have hpd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h2n
    have := Nat.le_of_dvd (by norm_num) hpd; omega
  set g : ℤ[X] := X ^ a + X ^ b - X ^ c - X ^ d with hg
  have hmapC : g.map (Int.castRingHom ℂ) = X ^ a + X ^ b - X ^ c - X ^ d := by
    simp [hg]
  have hmapP : g.map (Int.castRingHom (ZMod p)) = X ^ a + X ^ b - X ^ c - X ^ d := by
    simp [hg]
  -- g(ζ) = 0 mod p
  have hgζ : (g.map (Int.castRingHom (ZMod p))).eval ζ = 0 := by
    rw [hmapP]; simp only [eval_sub, eval_add, eval_pow, eval_X]; linear_combination hpar
  -- magnitude
  have hgC : ∀ ω : ℂ, ω ^ n = 1 → ‖(g.map (Int.castRingHom ℂ)).eval ω‖₊ ≤ 4 := fun ω hω => by
    rw [hmapC]; exact fourTerm_eval_nnnorm_le_four hn.ne' hω
  -- ℂ-Sidon
  have hSidon : ∀ ω : ℂ, ω ∈ (cyclotomic n ℂ).roots →
      (g.map (Int.castRingHom ℂ)).eval ω ≠ 0 := fun ω hω => by
    haveI : NeZero ((n : ℕ) : ℂ) := ⟨Nat.cast_ne_zero.mpr hn.ne'⟩
    have hωp : IsPrimitiveRoot ω n := isRoot_cyclotomic_iff.mp (isRoot_of_mem_roots hω)
    have hCsum : ω ^ a + ω ^ b ≠ 0 := by
      intro h0
      apply hsum
      rw [primitiveRoot_pow_add_eq_zero_iff hp2ne hn hζ]
      exact (primitiveRoot_pow_add_eq_zero_iff (by norm_num) hn hωp).mp h0
    rw [hmapC, eval_sub, eval_sub, eval_add, eval_pow, eval_pow, eval_pow, eval_pow, eval_X]
    exact fourTerm_sidon hn hωp ha hb hc hd hCsum hdist
  -- g ≠ 0 (a primitive root exists and is not a root of g)
  have hg0 : g ≠ 0 := by
    have hrootne : (cyclotomic n ℂ).roots ≠ 0 := by
      rw [← Multiset.card_pos]
      rw [(IsAlgClosed.splits (cyclotomic n ℂ)).natDegree_eq_card_roots.symm, natDegree_cyclotomic]
      exact n.totient_pos.mpr hn
    obtain ⟨ω, hω⟩ := Multiset.exists_mem_of_ne_zero hrootne
    intro h
    exact hSidon ω hω (by rw [h]; simp)
  -- leading coefficient survives mod p (|lc| ≤ 2 < p)
  have hcoeffbd : ∀ k, |g.coeff k| ≤ 2 := fun k => by
    rw [hg]; simp only [coeff_sub, coeff_add, coeff_X_pow]; split_ifs <;> norm_num
  have hgdeg : (g.map (Int.castRingHom (ZMod p))).natDegree = g.natDegree := by
    apply natDegree_map_of_leadingCoeff_ne_zero
    show ((g.leadingCoeff : ℤ) : ZMod p) ≠ 0
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro hdvd
    have hlc0 : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg0
    have hbd : |g.leadingCoeff| ≤ 2 := hcoeffbd g.natDegree
    have hpdvd : (p : ℤ) ∣ |g.leadingCoeff| := (dvd_abs (p : ℤ) g.leadingCoeff).mpr hdvd
    have hple : (p : ℤ) ≤ |g.leadingCoeff| := Int.le_of_dvd (abs_pos.mpr hlc0) hpdvd
    have : (p : ℤ) ≤ 2 := le_trans hple hbd
    omega
  exact prime_le_of_cyclotomic_parallelogram hn g hgC hgdeg hSidon hζ hgζ
