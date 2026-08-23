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
deployed NTT regime (`n = 2^20 ≫ log p`) does not satisfy.  This file states the *exact* condition
for the deployed regime, machine-checked:

`sidonModNeg_of_forall_resultant_ne` — `μ_n ⊆ F_p` is `SidonModNeg` (hence pins δ\*) **iff** `p`
divides none of the cyclotomic resultants `Res(Φ_n, X^a+X^b−X^c−X^d)` over the nontrivial exponent
configurations `{a,b} ≠ {c,d}`.

This pins down the open deployed core precisely: the δ\*-pinning Sidon property is a **finite,
in-principle-decidable `p`-non-divisibility condition** on a fixed explicit family of integers
(each of magnitude `≤ 2^n`, nonzero by the ℂ-Sidon `fourTerm_sidon`).  It is *not* a closure of the
deployed prize — verifying the hypothesis for the deployed `(n, p)` requires factoring `~2^60`
integers of `~2^{2^20}` digits, which is infeasible, and sporadic primes failing it are known to
exist.  But it converts the abstract "is the deployed prime good?" question into an explicit,
machine-checked arithmetic statement.  Axiom-clean.
-/

open Polynomial
open ArkLib.ProximityGap.AdditiveEnergySidonModNeg

/-- **The exact deployed-regime reduction (machine-checked).** `μ_n ⊆ F_p` is `SidonModNeg`
**iff** `p` divides none of the cyclotomic resultants `Res(Φ_n, X^a+X^b−X^c−X^d)` over the
nontrivial exponent configurations.  This makes the open deployed core *precise*: the δ\*-pinning
Sidon property is a finite (in principle decidable) `p`-non-divisibility condition on a fixed,
explicit family of integers.  (The small-subgroup pin is the special case where `p > 2^n` forces
all those resultants — each of magnitude `≤ 2^n` — to be coprime to `p`.) -/
theorem sidonModNeg_of_forall_resultant_ne {n : ℕ} (hn : 0 < n) {p : ℕ} [Fact p.Prime] (hp2 : 2 < p)
    {ζ : ZMod p} (hζ : IsPrimitiveRoot ζ n)
    (hres : ∀ a b c d : ℕ, a < n → b < n → c < n → d < n →
      ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) →
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
  -- g ≠ 0: a primitive complex root is not a root of g (the ℂ-Sidon, fourTerm_sidon)
  have hg0 : g ≠ 0 := by
    haveI : NeZero ((n : ℕ) : ℂ) := ⟨Nat.cast_ne_zero.mpr hn.ne'⟩
    have hrootne : (cyclotomic n ℂ).roots ≠ 0 := by
      rw [← Multiset.card_pos,
        (IsAlgClosed.splits (cyclotomic n ℂ)).natDegree_eq_card_roots.symm, natDegree_cyclotomic]
      exact n.totient_pos.mpr hn
    obtain ⟨ω, hω⟩ := Multiset.exists_mem_of_ne_zero hrootne
    have hωp : IsPrimitiveRoot ω n := isRoot_cyclotomic_iff.mp (isRoot_of_mem_roots hω)
    have hCsum : ω ^ a' + ω ^ b' ≠ 0 := by
      intro hh
      apply hab0
      rw [primitiveRoot_pow_add_eq_zero_iff (by
        intro h; have h2n : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
        have hpd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h2n
        have := Nat.le_of_dvd (by norm_num) hpd; omega) hn hζ]
      exact (primitiveRoot_pow_add_eq_zero_iff (by norm_num) hn hωp).mp hh
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
  exact hres a' b' c' d' ha'lt hb'lt hc'lt hd'lt hdist
    (dvd_resultant_of_isPrimitiveRoot_isRoot hn g hgdeg hζ hgζ)
