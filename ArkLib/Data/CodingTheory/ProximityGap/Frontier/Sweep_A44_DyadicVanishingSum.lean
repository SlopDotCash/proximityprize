/-
# Char-0 dyadic vanishing-sum rigidity, FULLY PROVEN (#444, the provable half of `defect = 0`)

This lifts the rigidity engine (`Sweep_A49`, `coeff_symm_of_dvd_X_pow_add_one`) to the genuine
char-0 statement by supplying its hypothesis from the cyclotomic structure:

  *If `g ∈ ℚ[X]` with `deg g < 2^μ` vanishes at a primitive `2^μ`-th root of unity `ζ ∈ ℂ`, then the
  coefficients of `g` are antipodally symmetric: `g.coeff j = g.coeff (j + 2^{μ-1})` for `j < 2^{μ-1}`.*

On the multiset of roots (a vanishing sum `Σ cⱼ ζ^j = 0` of `2^μ`-th roots of unity gives such a `g`
with `cⱼ = g.coeff j`) this is exactly **Lam–Leung for the prime 2: a vanishing sum of `2^μ`-th roots
of unity decomposes into `±`-pairs** (`ζ^j` and `ζ^{j+2^{μ-1}} = −ζ^j` occur with equal multiplicity).
This is the char-0 / Johnson-side rigidity that makes the dyadic-lacunary count equal to the coset
count — the **complete, correct, closed bound in characteristic 0**, and the result is *not* in Mathlib.

The proof is the honest mechanism: `ζ`'s minimal polynomial over `ℚ` is `Φ_{2^μ} = X^{2^{μ-1}} + 1`
(irreducible over `ℚ`: `cyclotomic.irreducible_rat`), so `(X^{2^{μ-1}}+1) ∣ g`, and the `Sweep_A49`
engine converts that divisibility into the `±`-pairing. **This is exactly the step that fails in
characteristic `p ≡ 1 mod 2^μ`** (prize regime): `Φ_{2^μ}` splits, `ζ ∈ F_p`, `minpoly = X−ζ`,
so `g(ζ)=0` gives only `(X−ζ) ∣ g` — the pairing is not forced, and the *non-coset* defect (the
open core) can appear. So this file proves the char-0 half and pins the open core to the char-`p`
failure of cyclotomic irreducibility.

Axiom-clean: `propext, Classical.choice, Quot.sound` (cyclotomic + the A49 engine). No `sorry`.
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.Sweep_A49_DyadicRigidityEngine
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Data.Complex.Basic

namespace ArkLib.ProximityGap.EvenOddDescent

open Polynomial

/-- **Char-0 dyadic vanishing-sum rigidity (Lam–Leung for `p = 2`), fully proven.** A rational
polynomial of degree `< 2^μ` vanishing at a primitive `2^μ`-th root of unity has antipodally-symmetric
coefficients `g.coeff j = g.coeff (j + 2^{μ-1})` — i.e. its root multiset (a vanishing sum of `2^μ`-th
roots of unity) is invariant under `ω ↦ −ω`, the `±`-pairing. This is the char-0 / Johnson-side
rigidity; its char-`p` failure (cyclotomic splits) is the proximity-prize wall. -/
theorem dyadic_vanishing_sum_paired {μ : ℕ} (hμ : 1 ≤ μ) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (2 ^ μ)) (g : ℚ[X]) (hdeg : g.natDegree < 2 ^ μ)
    (hroot : (aeval ζ) g = 0) :
    ∀ j < 2 ^ (μ - 1), g.coeff j = g.coeff (j + 2 ^ (μ - 1)) := by
  have hμ' : μ - 1 + 1 = μ := Nat.succ_pred_eq_of_pos hμ
  -- cyclotomic (2^μ) ℚ = X^{2^{μ-1}} + 1  (prime-power geometric-sum value at p = 2)
  have hcyc : (cyclotomic (2 ^ μ) ℚ) = X ^ (2 ^ (μ - 1)) + 1 := by
    have h := cyclotomic_prime_pow_eq_geom_sum (R := ℚ) (p := 2) (n := μ - 1) Nat.prime_two
    rw [hμ'] at h
    rw [h, Finset.sum_range_succ, Finset.sum_range_one]; ring
  have hpos : 0 < 2 ^ μ := pow_pos (by norm_num) μ
  haveI : NeZero ((2 ^ μ : ℕ) : ℚ) :=
    ⟨by exact_mod_cast pow_ne_zero μ (two_ne_zero : (2 : ℕ) ≠ 0)⟩
  -- minimal polynomial of ζ over ℚ is the (irreducible) cyclotomic, hence it divides g
  have hmin : cyclotomic (2 ^ μ) ℚ = minpoly ℚ ζ :=
    hζ.minpoly_eq_cyclotomic_of_irreducible (cyclotomic.irreducible_rat hpos)
  have hdvd : (X ^ (2 ^ (μ - 1)) + 1 : ℚ[X]) ∣ g := by
    rw [← hcyc, hmin]; exact minpoly.dvd ℚ ζ hroot
  -- feed the divisibility to the rigidity engine
  have hmpos : 0 < 2 ^ (μ - 1) := pow_pos (by norm_num) (μ - 1)
  have hdeg' : g.natDegree < 2 * 2 ^ (μ - 1) := by
    have h2 : 2 * 2 ^ (μ - 1) = 2 ^ μ := by rw [mul_comm, ← pow_succ, hμ']
    rw [h2]; exact hdeg
  intro j hj
  exact coeff_symm_of_dvd_X_pow_add_one (2 ^ (μ - 1)) hmpos g hdvd hdeg' j hj

/-- **Char-0 defect-vanishing in subset terms (first level).** A subset of `μ_{2^μ}` (given by its
exponent set `S ⊆ {0,…,2^μ−1}`) whose roots sum to zero is closed under negation `t ↦ −t`
(equivalently `j ↦ j + 2^{μ-1}` on exponents, since `ζ^{2^{μ-1}} = −1`). This is the prize's
char-0 lacunary rigidity in the actual subset language: a *vanishing-sum* subset is `±`-symmetric,
so the first nontrivial elementary symmetric vanishing already forces coset (`μ₂`) structure — there
is **no char-0 defect at the first level**. Proof: apply `dyadic_vanishing_sum_paired` to the
indicator polynomial `g = ∑_{j∈S} Xʲ` (whose `j`-th coefficient is `⟦j ∈ S⟧` and which vanishes at `ζ`
exactly because the roots sum to zero). The char-`p` failure is identical: `ζ ∈ F_p` kills the
cyclotomic divisibility, so a vanishing sum mod `p` need *not* be `±`-symmetric — the defect. -/
theorem vanishing_exponent_set_neg_symmetric {μ : ℕ} (hμ : 1 ≤ μ) (ζ : ℂ)
    (hζ : IsPrimitiveRoot ζ (2 ^ μ)) (S : Finset ℕ) (hS : ∀ j ∈ S, j < 2 ^ μ)
    (hsum : ∑ j ∈ S, ζ ^ j = 0) (j : ℕ) (hj : j < 2 ^ (μ - 1)) :
    (j ∈ S ↔ j + 2 ^ (μ - 1) ∈ S) := by
  classical
  set g : ℚ[X] := ∑ i ∈ S, X ^ i with hg
  -- coefficients of the indicator polynomial
  have hcoeff : ∀ k, g.coeff k = if k ∈ S then 1 else 0 := by
    intro k
    rw [hg, finset_sum_coeff]
    simp_rw [coeff_X_pow]
    rw [Finset.sum_ite_eq S k (fun _ => (1 : ℚ))]
  -- degree bound: every exponent is `< 2^μ`
  have hdeg : g.natDegree < 2 ^ μ := by
    have hpos : 0 < 2 ^ μ := pow_pos (by norm_num) μ
    have hle : g.natDegree ≤ 2 ^ μ - 1 := by
      rw [natDegree_le_iff_coeff_eq_zero]
      intro m hm
      rw [hcoeff]
      have : m ∉ S := fun h => by have := hS m h; omega
      simp [this]
    omega
  -- the indicator polynomial vanishes at ζ ⇔ the roots sum to zero
  have hroot : (aeval ζ) g = 0 := by
    rw [hg, map_sum]; simp_rw [aeval_X_pow]; exact hsum
  -- apply the dyadic vanishing-sum rigidity and read off the indicators
  have hsymm := dyadic_vanishing_sum_paired hμ ζ hζ g hdeg hroot j hj
  rw [hcoeff, hcoeff] at hsymm
  by_cases h1 : j ∈ S <;> by_cases h2 : j + 2 ^ (μ - 1) ∈ S <;> simp_all

end ArkLib.ProximityGap.EvenOddDescent
