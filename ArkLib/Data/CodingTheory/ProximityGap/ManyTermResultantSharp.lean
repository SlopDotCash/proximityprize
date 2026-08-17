/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ManyTermResultantBound
import ArkLib.Data.CodingTheory.ProximityGap.SidonParsevalGeneral
import ArkLib.Data.CodingTheory.ProximityGap.SidonParsevalNthRoots

/-!
# THE SHARP GENERAL-`r` CYCLOTOMIC RESULTANT BOUND — `|Res|² ≤ (4r)^{φ(n)}` (#389/#407)

`ManyTermResultant.abs_resultant_manyTerm_le` gives the **pointwise** general-`r` bound
`|Res(Φ_n, manyTerm r a b)| ≤ (2r)^{φ(n)}` (`= (2r)^{n/2}` for `n = 2^m`), from `‖manyTerm(ζ)‖ ≤ 2r`.
This file proves the **sharp** bound

> `abs_resultant_manyTerm_sq_le` :  `|Res(Φ_n, manyTerm r a b)|² ≤ (4r)^{φ(n)}`   (i.e. `|Res| ≤ (4r)^{φ(n)/2} = (4r)^{n/4}`),

replacing the pointwise `‖f(ζ)‖ ≤ 2r` by the **Parseval `ℓ²` average**
`∑_{ζ ∈ μ_n} ‖manyTerm(ζ)‖² = 2r·n` (`2r` unit coefficients, distinct exponents) and **AM-GM** over the
`φ(n) = n/2` primitive roots. The single sharpening that subsumes **both** landed special cases:
`r = 2` gives `(8)^{φ(n)}` (`SidonResultantImproved.abs_resultant_fourTerm_sq_le`) and `r = 3` gives
`12^{φ(n)}` (`SixTermResultantImproved.sixterm_resultant_sq_le`). Probe-verified tight at `r = 2, 3`
(`max |Res| = (4r)^{n/4}` exactly at `n = 8`).

Consequence: an `r`-fold additive relation among **distinct** `μ_n`-powers over `F_p` forces
`p ≤ (4r)^{n/4}` — a `≈ log₂(4r)/2` improvement in the threshold exponent over the pointwise
`(2r)^{n/2}` (`log₂(2r)`), i.e. the unconditional sharp-`E_r`-pin regime is **doubled** in `n`. Still
bounded `r` for production `q`, consistent with the open core (`r ~ log q`), but the sharpest possible
single-rung pin. Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

set_option linter.style.longLine false


open Complex Finset Polynomial
open ArkLib.ProximityGap.AdditiveEnergyRepBound

namespace ArkLib.ProximityGap.ManyTermResultant

variable {n : ℕ}

/-- The `2r` signed unit-root family `Fin r ⊕ Fin r → ℂ`: `a`-side `ω^{a s}`, `b`-side `ω^{b s}`. -/
noncomputable def manyVals (ω : ℂ) (r : ℕ) (a b : ℕ → ℕ) : (Fin r ⊕ Fin r) → ℂ :=
  Sum.elim (fun s => ω ^ (a s)) (fun s => ω ^ (b s))

/-- The signed coefficients: `+1` on the `a`-side, `−1` on the `b`-side. -/
noncomputable def manySigns (r : ℕ) : (Fin r ⊕ Fin r) → ℂ :=
  Sum.elim (fun _ => 1) (fun _ => -1)

/-- `∑_i ‖manySigns r i‖² = 2r`. -/
theorem manySigns_sq_sum (r : ℕ) : ∑ i : Fin r ⊕ Fin r, ‖manySigns r i‖ ^ 2 = 2 * r := by
  rw [Fintype.sum_sum_type]
  simp only [manySigns, Sum.elim_inl, Sum.elim_inr, norm_one, norm_neg, one_pow,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  ring

/-- `manyTerm` evaluated at `ω^t` as the `parseval_general` linear combination. -/
theorem manyTerm_eq_lincomb (ω : ℂ) (r : ℕ) (a b : ℕ → ℕ) (t : ℕ) :
    (manyTerm r a b).eval₂ (algebraMap ℤ ℂ) (ω ^ t)
      = ∑ i : Fin r ⊕ Fin r, manySigns r i * (manyVals ω r a b i) ^ t := by
  simp only [manyTerm, eval₂_finset_sum, eval₂_sub, eval₂_pow, eval₂_X]
  rw [Fintype.sum_sum_type]
  simp only [manySigns, manyVals, Sum.elim_inl, Sum.elim_inr, one_mul, neg_one_mul,
    Finset.sum_neg_distrib]
  rw [Fin.sum_univ_eq_sum_range (fun s => (ω ^ (a s)) ^ t) r,
      Fin.sum_univ_eq_sum_range (fun s => (ω ^ (b s)) ^ t) r, ← sub_eq_add_neg,
      Finset.sum_sub_distrib]
  have e1 : ∀ s ∈ Finset.range r, (ω ^ t) ^ (a s) = (ω ^ (a s)) ^ t :=
    fun s _ => by rw [← pow_mul, ← pow_mul, mul_comm]
  have e2 : ∀ s ∈ Finset.range r, (ω ^ t) ^ (b s) = (ω ^ (b s)) ^ t :=
    fun s _ => by rw [← pow_mul, ← pow_mul, mul_comm]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2]

/-- **Parseval over `μ_n` for the general `2r`-term.** For a primitive `n`-th root `ω` (`n ≠ 0`) with
the `2r` powers pairwise distinct, `∑_{x ∈ μ_n} ‖manyTerm(x)‖² = 2r·n`. -/
theorem parseval_manyTerm_nthRoots (hn : n ≠ 0) {ω : ℂ} (hω : IsPrimitiveRoot ω n)
    (r : ℕ) (a b : ℕ → ℕ) (hdist : Function.Injective (manyVals ω r a b)) :
    ∑ x ∈ Polynomial.nthRootsFinset n (1 : ℂ),
        ‖(manyTerm r a b).eval₂ (algebraMap ℤ ℂ) x‖ ^ 2 = 2 * r * n := by
  rw [sum_nthRootsFinset_reindex hω (fun x => ‖(manyTerm r a b).eval₂ (algebraMap ℤ ℂ) x‖ ^ 2)]
  have hrw : ∀ t ∈ Finset.range n,
      ‖(manyTerm r a b).eval₂ (algebraMap ℤ ℂ) (ω ^ t)‖ ^ 2
        = ‖∑ i : Fin r ⊕ Fin r, manySigns r i * (manyVals ω r a b i) ^ t‖ ^ 2 := by
    intro t _; rw [manyTerm_eq_lincomb]
  rw [Finset.sum_congr rfl hrw]
  have hpe : ∀ k : ℕ, (ω ^ k) ^ n = 1 := by
    intro k; rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
  have hvn : ∀ i, (manyVals ω r a b i) ^ n = 1 := by
    intro i; cases i with
    | inl s => exact hpe _
    | inr s => exact hpe _
  have hnorm : ∀ i, ‖manyVals ω r a b i‖ = 1 := fun i =>
    norm_eq_one_of_primitiveRoot hn (hvn i)
  rw [parseval_general (manyVals ω r a b) hvn hnorm hdist (manySigns r), manySigns_sq_sum]
  ring

/-- **THE SHARP GENERAL-`r` RESULTANT BOUND.** For `n = 2^m` (`m ≥ 1`), any `r`, and a `manyTerm`
whose `2r` `ω`-powers are pairwise distinct, `|Res(Φ_n, manyTerm r a b)|² ≤ (4r)^{φ(n)}` — i.e.
`|Res| ≤ (4r)^{φ(n)/2} = (4r)^{n/4}`, sharper than the pointwise `(2r)^{φ(n)} = (2r)^{n/2}`. Via
Parseval `∑_{prim} ‖f(ζ)‖² ≤ 2r·n` and AM-GM over the `φ(n) = n/2` primitive roots. Subsumes the
landed `r = 2` (`8^{φ(n)}`) and `r = 3` (`12^{φ(n)}`) special cases. -/
theorem abs_resultant_manyTerm_sq_le {m : ℕ} (hm : 1 ≤ m) (r : ℕ) (a b : ℕ → ℕ)
    {ω : ℂ} (hω : IsPrimitiveRoot ω (2 ^ m))
    (hdist : Function.Injective (manyVals ω r a b)) :
    (resultant (cyclotomic (2 ^ m) ℤ) (manyTerm r a b)).natAbs ^ 2 ≤ (4 * r) ^ (2 ^ m).totient := by
  classical
  set n := 2 ^ m with hn_def
  have hn0 : n ≠ 0 := by positivity
  have hn0' : 0 < n := Nat.pos_of_ne_zero hn0
  haveI : NeZero (n : ℂ) := ⟨Nat.cast_ne_zero.mpr hn0⟩
  set R := resultant (cyclotomic n ℤ) (manyTerm r a b) with hR
  set g : ℂ → ℂ := fun ζ => eval ζ ((manyTerm r a b).map (algebraMap ℤ ℂ)) with hg
  have hgval : ∀ ζ : ℂ, g ζ = (manyTerm r a b).eval₂ (algebraMap ℤ ℂ) ζ :=
    fun ζ => (eval₂_eq_eval_map _).symm
  have hcast : (algebraMap ℤ ℂ) R = ((cyclotomic n ℂ).roots.map g).prod :=
    resultant_cast_eq_prod_gen (manyTerm r a b)
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
  have hsub : primitiveRoots n ℂ ⊆ nthRootsFinset n (1 : ℂ) := by
    intro ζ hζ
    rw [mem_primitiveRoots hn0'] at hζ
    rw [mem_nthRootsFinset hn0']; exact hζ.pow_eq_one
  have hsum_le : ∑ ζ ∈ primitiveRoots n ℂ, Complex.normSq (g ζ) ≤ 2 * r * (n : ℝ) := by
    calc ∑ ζ ∈ primitiveRoots n ℂ, Complex.normSq (g ζ)
        ≤ ∑ ζ ∈ nthRootsFinset n (1 : ℂ), Complex.normSq (g ζ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ζ _ _ => Complex.normSq_nonneg _)
      _ = ∑ ζ ∈ nthRootsFinset n (1 : ℂ), ‖(manyTerm r a b).eval₂ (algebraMap ℤ ℂ) ζ‖ ^ 2 := by
          refine Finset.sum_congr rfl (fun ζ _ => ?_); rw [hgsq, hgval]
      _ = 2 * r * n := parseval_manyTerm_nthRoots hn0 hω r a b hdist
  have hcard : (primitiveRoots n ℂ).card = n.totient := hω.card_primitiveRoots
  have htot : (n.totient : ℝ) * (4 * r) = 2 * r * n := by
    have h1 : n.totient = 2 ^ (m - 1) := by
      rw [hn_def, Nat.totient_prime_pow Nat.prime_two (by omega)]; simp
    rw [h1, hn_def]; push_cast
    rw [show (2 : ℝ) ^ m = 2 ^ (m - 1) * 2 by rw [← pow_succ]; congr 1; omega]
    ring
  have hAMGM : ∏ ζ ∈ primitiveRoots n ℂ, Complex.normSq (g ζ) ≤ (4 * r) ^ n.totient := by
    refine prod_le_of_sum_le (primitiveRoots n ℂ) (fun ζ => Complex.normSq (g ζ))
      (fun ζ _ => Complex.normSq_nonneg _) n.totient hcard (4 * r) ?_
    rw [htot]; exact hsum_le
  have hfin : ((R.natAbs : ℝ)) ^ 2 ≤ (4 * r) ^ n.totient := by
    rw [← hlhs, hprodeq]; exact hAMGM
  have hcastfin : ((R.natAbs ^ 2 : ℕ) : ℝ) ≤ (((4 * r) ^ n.totient : ℕ) : ℝ) := by
    push_cast; exact hfin
  exact_mod_cast hcastfin

end ArkLib.ProximityGap.ManyTermResultant

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.ManyTermResultant.parseval_manyTerm_nthRoots
#print axioms ArkLib.ProximityGap.ManyTermResultant.abs_resultant_manyTerm_sq_le
