/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ManyTermResultantBound
import ArkLib.Data.CodingTheory.ProximityGap.SidonParsevalGeneral
import ArkLib.Data.CodingTheory.ProximityGap.SidonParsevalNthRoots

/-!
# THE FULLY GENERAL SHARP RESULTANT BOUND — `|Res|² ≤ (2·W)^{φ(n)}`, `W = ∑ mᵢ²` (#389/#407)

The capstone sharpening: for **any** integer-coefficient sparse polynomial `f = ∑ᵢ mᵢ·X^{eᵢ}` with
**pairwise-distinct** exponents over `μ_n` (`n = 2^m`),

> `weightedSparse_resultant_sq_le` :  `|Res(Φ_n, f)|² ≤ (2·W)^{φ(n)}`,   `W = ∑ᵢ mᵢ²`   (so `|Res| ≤ (2W)^{n/4}`),

via the **weighted Parseval `ℓ²` average** `∑_{ζ ∈ μ_n} ‖f(ζ)‖² = n·∑ᵢ mᵢ²` (`parseval_general` with the
integer coefficients `mᵢ`) and **AM-GM** over the `φ(n) = n/2` primitive roots. This **subsumes every
prior sharp bound** as the special case of `±1` coefficients:
- four-term (`±1`, `k = 4`, `W = 4`): `8^{φ(n)}` (`SidonResultantImproved`),
- six-term (`±1`, `k = 6`, `W = 6`): `12^{φ(n)}` (`SixTermResultantImproved`),
- `2r`-term (`±1`, `W = 2r`): `(4r)^{φ(n)}` (`ManyTermResultantSharp`),

AND captures the **repeated-value / non-unit-coefficient** relations the `±1` bounds miss. This is the
honest fix to the over-stated `r = 3` `RepThree` claim: a full order-6 zero-sum sextuple of `μ_n`,
grouped by value, is a relation `∑ᵢ mᵢ·ζ^{eᵢ} = 0` with `∑ᵢ |mᵢ| ≤ 6`; the **worst** non-antipodal
multiplicity pattern (e.g. `5·ζ⁰ + ζ⁵`, `W = 26`) sets the **true** `RepThree` threshold
`p > (2·26)^{n/4} = 52^{n/4}` — strictly larger than the `±1` six-term `12^{n/4}` (probe-confirmed:
`RepThree(μ_8)` fails at `p = 313 > 144 = 12^{8/4}` via `5 + ζ⁵ ≡ 0 (mod 313)`, but the
coefficient-weighted bound `(2·26)^{8/4} = 2704 > 313` covers it; `|Res(Φ_8, 5+X⁵)| = 626 = 2·313`).

So the genuine `r = 3` char-`p` `RepThree` transfer holds for `p > (2·Wmax(6))^{n/4}` where `Wmax(6)` is
the largest `∑mᵢ²` over non-antipodally-pairable signed multiplicity patterns of six `2^m`-th roots
(`= 26` for the `5+1` concentration). The constant `Wmax(6)` is the remaining elementary combinatorial
input; this file supplies the sharp resultant machinery for **every** weighted shape. Axiom-clean
(`propext, Classical.choice, Quot.sound`); no `sorry`.
-/

set_option linter.style.longLine false


open Complex Finset Polynomial
open ArkLib.ProximityGap.AdditiveEnergyRepBound

namespace ArkLib.ProximityGap.WeightedSparseResultant

variable {n : ℕ}

/-- The integer-coefficient sparse polynomial `∑ᵢ mᵢ·X^{eᵢ}` over `ℤ`. -/
noncomputable def weightedSparse {k : ℕ} (m : Fin k → ℤ) (e : Fin k → ℕ) : ℤ[X] :=
  ∑ i : Fin k, (C (m i)) * X ^ (e i)

/-- The complex unit-root family `ζ^{eᵢ}`. -/
noncomputable def weightedVals {k : ℕ} (ω : ℂ) (e : Fin k → ℕ) : Fin k → ℂ :=
  fun i => ω ^ (e i)

/-- `weightedSparse` evaluated at `ω^t` as the `parseval_general` linear combination with the
integer coefficients `(mᵢ : ℂ)`. -/
theorem weightedSparse_eq_lincomb {k : ℕ} (ω : ℂ) (m : Fin k → ℤ) (e : Fin k → ℕ) (t : ℕ) :
    (weightedSparse m e).eval₂ (algebraMap ℤ ℂ) (ω ^ t)
      = ∑ i : Fin k, ((m i : ℂ)) * (weightedVals ω e i) ^ t := by
  simp only [weightedSparse, eval₂_finset_sum, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X,
    weightedVals]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← pow_mul, ← pow_mul, mul_comm (e i) t]
  simp [algebraMap_int_eq, eq_intCast]

/-- **Weighted Parseval over `μ_n`.** For a primitive `n`-th root `ω` (`n ≠ 0`) with pairwise-distinct
powers, `∑_{x ∈ μ_n} ‖f(x)‖² = n·∑ᵢ mᵢ²`. -/
theorem parseval_weightedSparse_nthRoots (hn : n ≠ 0) {ω : ℂ} (hω : IsPrimitiveRoot ω n)
    {k : ℕ} (m : Fin k → ℤ) (e : Fin k → ℕ) (hdist : Function.Injective (weightedVals ω e)) :
    ∑ x ∈ Polynomial.nthRootsFinset n (1 : ℂ),
        ‖(weightedSparse m e).eval₂ (algebraMap ℤ ℂ) x‖ ^ 2
      = (n : ℝ) * ∑ i : Fin k, ((m i : ℝ)) ^ 2 := by
  rw [sum_nthRootsFinset_reindex hω (fun x => ‖(weightedSparse m e).eval₂ (algebraMap ℤ ℂ) x‖ ^ 2)]
  have hrw : ∀ t ∈ Finset.range n,
      ‖(weightedSparse m e).eval₂ (algebraMap ℤ ℂ) (ω ^ t)‖ ^ 2
        = ‖∑ i : Fin k, ((m i : ℂ)) * (weightedVals ω e i) ^ t‖ ^ 2 := by
    intro t _; rw [weightedSparse_eq_lincomb]
  rw [Finset.sum_congr rfl hrw]
  have hpe : ∀ j : ℕ, (ω ^ j) ^ n = 1 := by
    intro j; rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
  have hvn : ∀ i, (weightedVals ω e i) ^ n = 1 := fun i => hpe _
  have hnorm : ∀ i, ‖weightedVals ω e i‖ = 1 := fun i =>
    norm_eq_one_of_primitiveRoot hn (hvn i)
  rw [parseval_general (weightedVals ω e) hvn hnorm hdist (fun i => (m i : ℂ))]
  refine congrArg (fun z => (n : ℝ) * z) ?_
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Complex.norm_intCast]
  rw [← Int.cast_abs]
  push_cast
  rw [sq_abs]

/-- **THE FULLY GENERAL SHARP RESULTANT BOUND.** For `n = 2^m` (`m ≥ 1`) and any integer-coefficient
sparse polynomial `f = ∑ᵢ mᵢ·X^{eᵢ}` whose `ω`-powers are pairwise distinct,
`|Res(Φ_n, f)|² ≤ (2·W)^{φ(n)}` where `W = ∑ᵢ mᵢ²` — i.e. `|Res| ≤ (2W)^{φ(n)/2} = (2W)^{n/4}`. Via the
weighted Parseval `∑_{prim} ‖f(ζ)‖² ≤ n·W` and AM-GM over the `φ(n) = n/2` primitive roots. Subsumes
all `±1` special cases (`W = 2r ⟹ (4r)^{φ(n)}`) and the repeated-value relations. -/
theorem weightedSparse_resultant_sq_le {M : ℕ} (hM : 1 ≤ M) {k : ℕ} (m : Fin k → ℤ) (e : Fin k → ℕ)
    {ω : ℂ} (hω : IsPrimitiveRoot ω (2 ^ M)) (hdist : Function.Injective (weightedVals ω e))
    {W : ℕ} (hW : ∑ i : Fin k, (m i) ^ 2 ≤ (W : ℤ)) :
    (resultant (cyclotomic (2 ^ M) ℤ) (weightedSparse m e)).natAbs ^ 2 ≤ (2 * W) ^ (2 ^ M).totient := by
  classical
  set n := 2 ^ M with hn_def
  have hn0 : n ≠ 0 := by positivity
  have hn0' : 0 < n := Nat.pos_of_ne_zero hn0
  haveI : NeZero (n : ℂ) := ⟨Nat.cast_ne_zero.mpr hn0⟩
  set R := resultant (cyclotomic n ℤ) (weightedSparse m e) with hR
  set g : ℂ → ℂ := fun ζ => eval ζ ((weightedSparse m e).map (algebraMap ℤ ℂ)) with hg
  have hgval : ∀ ζ : ℂ, g ζ = (weightedSparse m e).eval₂ (algebraMap ℤ ℂ) ζ :=
    fun ζ => (eval₂_eq_eval_map _).symm
  have hcast : (algebraMap ℤ ℂ) R = ((cyclotomic n ℂ).roots.map g).prod :=
    ArkLib.ProximityGap.ManyTermResultant.resultant_cast_eq_prod_gen (weightedSparse m e)
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
  -- W as a real, ≥ ∑ mᵢ²
  have hWreal : (∑ i : Fin k, ((m i : ℝ)) ^ 2) ≤ (W : ℝ) := by
    have := hW
    have hcast2 : ((∑ i : Fin k, (m i) ^ 2 : ℤ) : ℝ) ≤ ((W : ℤ) : ℝ) := by exact_mod_cast this
    push_cast at hcast2 ⊢
    exact hcast2
  have hsum_le : ∑ ζ ∈ primitiveRoots n ℂ, Complex.normSq (g ζ) ≤ (n : ℝ) * (W : ℝ) := by
    calc ∑ ζ ∈ primitiveRoots n ℂ, Complex.normSq (g ζ)
        ≤ ∑ ζ ∈ nthRootsFinset n (1 : ℂ), Complex.normSq (g ζ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ζ _ _ => Complex.normSq_nonneg _)
      _ = ∑ ζ ∈ nthRootsFinset n (1 : ℂ), ‖(weightedSparse m e).eval₂ (algebraMap ℤ ℂ) ζ‖ ^ 2 := by
          refine Finset.sum_congr rfl (fun ζ _ => ?_); rw [hgsq, hgval]
      _ = (n : ℝ) * ∑ i : Fin k, ((m i : ℝ)) ^ 2 := parseval_weightedSparse_nthRoots hn0 hω m e hdist
      _ ≤ (n : ℝ) * (W : ℝ) := by
          apply mul_le_mul_of_nonneg_left hWreal (by positivity)
  have hcard : (primitiveRoots n ℂ).card = n.totient := hω.card_primitiveRoots
  have htot : (n.totient : ℝ) * (2 * W) = n * W := by
    have h1 : n.totient = 2 ^ (M - 1) := by
      rw [hn_def, Nat.totient_prime_pow Nat.prime_two (by omega)]; simp
    rw [h1, hn_def]; push_cast
    rw [show (2 : ℝ) ^ M = 2 ^ (M - 1) * 2 by rw [← pow_succ]; congr 1; omega]
    ring
  have hAMGM : ∏ ζ ∈ primitiveRoots n ℂ, Complex.normSq (g ζ) ≤ ((2 * W : ℕ) : ℝ) ^ n.totient := by
    refine prod_le_of_sum_le (primitiveRoots n ℂ) (fun ζ => Complex.normSq (g ζ))
      (fun ζ _ => Complex.normSq_nonneg _) n.totient hcard ((2 * W : ℕ) : ℝ) ?_
    have hpush : ((2 * W : ℕ) : ℝ) = 2 * (W : ℝ) := by push_cast; ring
    rw [hpush, htot]
    exact hsum_le
  have hcastfin : ((R.natAbs ^ 2 : ℕ) : ℝ) ≤ (((2 * W) ^ n.totient : ℕ) : ℝ) := by
    push_cast
    rw [← hlhs, hprodeq]
    have : ((2 * W : ℕ) : ℝ) ^ n.totient = (2 * (W : ℝ)) ^ n.totient := by push_cast; ring
    rw [this] at hAMGM
    exact hAMGM
  exact_mod_cast hcastfin

end ArkLib.ProximityGap.WeightedSparseResultant

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.WeightedSparseResultant.parseval_weightedSparse_nthRoots
#print axioms ArkLib.ProximityGap.WeightedSparseResultant.weightedSparse_resultant_sq_le
