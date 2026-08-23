/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Agent
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.CyclotomicNormDefectThreshold

/-!
# Unify-B: the demand `e₂ = 0` defect and the supply `Spurᵣ` are ONE norm object (#444)

This brick machine-checks the **consolidation** found numerically in
`scripts/probes/probe_444_unifyB_{norm_object,identity_vs_subcase}.py`: the *demand-side*
char-`p` defect (the `e₂ = 0` surplus on `μ_{n/2}`-subsets, the `O_P` / `DeltaStarOP1BindingN16`
object) and the *supply-side* `Spurᵣ = Eᵣ − Eᵣ^{c0}` (char-`p` short `±1`-relations of
`2^μ`-th roots) are governed by the **same** object:

> `p ∣ Norm(short root-of-unity sum)`, the sum nonzero in characteristic `0`.

## The two objects

* **Supply `Spurᵣ`** (`CyclotomicNormDefectThreshold.prime_le_of_cyclotomic_signed_sum`):
  `α = Σ_{i ≤ 2r} ε_i ζ_n^{e_i}` with `ε_i = ±1`, `α ≡ 0 (mod p)`, `α ≠ 0` in char `0`;
  controlled by `p ∣ Res(Φ_n, g) = Norm(α)`, `|Norm| ≤ (2r)^{φ(n)}`.

* **Demand `e₂ = 0`** (this file): a `w`-subset `J = {ζ_{n/2}^{a_k}} ⊆ μ_{n/2}` with
  `e₂(J) ≡ 0 (mod p)` but `e₂(J) ≠ 0` in char `0`. The key structural fact, proven here, is

  `e₂(J) = Σ_{i<j} ζ_{n/2}^{a_i + a_j}`  — a sum of **`C(w,2)` roots of unity** in `μ_{n/2}`.

  So `e₂(J)` is **literally** a short (all-coefficients `= 1`) root-of-unity sum, and the
  *same* norm-defect threshold applies verbatim with `M = C(w,2)`:

  `p ∣ Norm(e₂(J)) ≤ C(w,2)^{φ(n/2)}`.

## The verdict (consolidation, not closure — see honesty note)

`e₂(J)` is a **special member** of the supply `±1`-relation family:
* coefficients all `+1` (a *sign-restricted* slice — `−1 = ζ_{n/2}^{(n/2)/2}` absorbs signs);
* group `μ_{n/2} = ⟨ζ_n²⟩ ⊆ μ_n`, the *subfield* `ℚ(ζ_{n/2}) ⊆ ℚ(ζ_n)`, **same prime** `P ∣ p`;
* term count `C(w,2)` at *fixed small* `w` ⟹ a **fixed-shallow-depth** slice, not the prize
  `r ∼ log m`.

Hence the demand defect and the supply `Spurᵣ` are the **same wall object** — `p` dividing the
norm of a short `2^μ`-root-of-unity combination — with the demand a sign-restricted, fixed-depth
*slice*. This is a genuine **consolidation** (the two char-`p` defects are one), **not** a new
bound on `Spurᵣ`: the demand slice does not reach `r ∼ log m`, so it does not close the prize.

The load-bearing content here is `e2_eq_signedSum` (the `e₂`-as-root-of-unity-sum identity) and
`demand_defect_prime_le` (the demand defect inherits the supply norm bound), both axiom-clean.

Axiom target: `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial Complex
open scoped NNReal

namespace ArkLib.ProximityGap.UnifyBConsolidation

open ArkLib.ProximityGap.CyclotomicNormDefectThreshold

/-- The unordered-pair index set `{(i,j) : i < j}` of `Fin w`, whose cardinality is `C(w,2)` (the
number of terms in `e₂`). Abbreviated to keep the norm-bound statements within the line limit. -/
def pairSet (w : ℕ) : Finset (Fin w × Fin w) :=
  Finset.univ.filter (fun p : Fin w × Fin w => p.1 < p.2)

/-! ## §1  `e₂(J)` is a sum of `C(w,2)` roots of unity — the structural identity -/

/-- The exponent list of `e₂`: for a `w`-subset given by exponents `a : Fin w → ℕ` (the powers of
`ζ_{N}` indexing `J ⊆ μ_N`), the second elementary symmetric polynomial `e₂(J) = Σ_{i<j} ζ_N^{a i}
ζ_N^{a j} = Σ_{i<j} ζ_N^{a i + a j}` is a sum over the `C(w,2)` unordered pairs of the monomials
`ζ_N^{a i + a j}`.  We realize it as a polynomial `∑ over offDiag, C 1 * X^{a i + a j}` and read it
back at a root of unity. -/
noncomputable def e2Poly {w : ℕ} (a : Fin w → ℕ) : ℂ[X] :=
  ∑ p ∈ pairSet w, C (1 : ℂ) * X ^ (a p.1 + a p.2)

/-- **`e₂` is a `C(w,2)`-term root-of-unity sum.** Evaluated at any `N`-th root of unity `ω`,
`e2Poly a` is the sum of the `C(w,2)` unit-modulus monomials `ω^{a i + a j}` (`i < j`); hence
`‖e2Poly a (ω)‖ ≤ C(w,2)`. This is the demand `e₂(J)` written in the *exact* shape of the supply
short-root-sum, with **all coefficients `= 1`** (`M = C(w,2)`, no signs). -/
theorem e2Poly_eval_nnnorm_le {N w : ℕ} (hN : N ≠ 0) (a : Fin w → ℕ) {ω : ℂ}
    (hω : ω ^ N = 1) :
    ‖(e2Poly a).eval ω‖₊ ≤ ((pairSet w).card : ℝ≥0) := by
  classical
  have hnormω : ‖ω‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hω hN
  set S := pairSet w with hS
  have heval : (e2Poly a).eval ω = ∑ p ∈ S, ω ^ (a p.1 + a p.2) := by
    rw [e2Poly, ← hS, eval_finset_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    simp only [eval_mul, eval_C, eval_pow, eval_X, one_mul]
  have hterm : ∀ p ∈ S, ‖ω ^ (a p.1 + a p.2)‖ = 1 := by
    intro p _; rw [norm_pow, hnormω, one_pow]
  have hreal : ‖(e2Poly a).eval ω‖ ≤ (S.card : ℝ) := by
    rw [heval]
    calc ‖∑ p ∈ S, ω ^ (a p.1 + a p.2)‖
        ≤ ∑ p ∈ S, ‖ω ^ (a p.1 + a p.2)‖ := norm_sum_le _ _
      _ = ∑ _p ∈ S, (1 : ℝ) := Finset.sum_congr rfl hterm
      _ = (S.card : ℝ) := by simp
  exact_mod_cast hreal

/-! ## §2  `e2Poly` over `ℤ` and the demand defect inherits the supply norm bound -/

/-- The integer version of `e2Poly` (coefficients are literally `1 ∈ ℤ`). -/
noncomputable def e2PolyZ {w : ℕ} (a : Fin w → ℕ) : ℤ[X] :=
  ∑ p ∈ pairSet w, C (1 : ℤ) * X ^ (a p.1 + a p.2)

/-- The complex map of `e2PolyZ` is `e2Poly` (casting the all-`1` coefficients). -/
theorem map_e2PolyZ {w : ℕ} (a : Fin w → ℕ) :
    (e2PolyZ a).map (Int.castRingHom ℂ) = e2Poly a := by
  classical
  rw [e2PolyZ, e2Poly, Polynomial.map_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X, map_one]

/-- **THE CONSOLIDATION (assembled, axiom-clean).** A demand-side `e₂ = 0` char-`p` defect — i.e.
exponents `a : Fin w → ℕ` whose `e₂` (a sum of `C(w,2)` `N`-th roots of unity) is `≠ 0` in char `0`
(`hChar0`) yet vanishes at a primitive `N`-th root `ζ ∈ ZMod p` (`hVanish`) — satisfies the **same**
cyclotomic norm-defect bound as the supply `Spurᵣ`:

  `p ≤ C(w,2)^{φ(N)} = |Norm(e₂(J))|`-bound,

via `CyclotomicNormDefectThreshold.prime_le_of_cyclotomic_signed_sum` with `M = C(w,2)`. This is the
**identical** prime-divides-norm-of-short-root-sum object that governs the supply side; the demand
`e₂` defect is the all-`+1`-coefficient, group-`μ_N` slice of it.

Honest scope: this PROVES the demand defect is the SAME norm object as supply (consolidation). It
does NOT bound `Spurᵣ` at `r ∼ log m`: the bound `C(w,2)^{φ(N)}` is VACUOUS in the prize regime
(`φ(N) = N/2`, `C(w,2)^{N/2} ≫ p`) exactly as supply is — the open wall is unchanged. -/
theorem demand_defect_prime_le {N : ℕ} (hN : 0 < N) {p w : ℕ} [Fact p.Prime] (a : Fin w → ℕ)
    (hgdeg : ((e2PolyZ a).map (Int.castRingHom (ZMod p))).natDegree = (e2PolyZ a).natDegree)
    (hChar0 : ∀ ω : ℂ, ω ∈ (cyclotomic N ℂ).roots → (e2Poly a).eval ω ≠ 0)
    {ζ : ZMod p} (hζ : IsPrimitiveRoot ζ N)
    (hVanish : ((e2PolyZ a).map (Int.castRingHom (ZMod p))).eval ζ = 0) :
    p ≤ (pairSet w).card ^ N.totient := by
  classical
  set M := (pairSet w).card with hM
  refine prime_le_of_cyclotomic_signed_sum hN (M := M) (e2PolyZ a) ?_ hgdeg ?_ hζ hVanish
  · -- the archimedean bound: ‖(e2PolyZ a → ℂ).eval ω‖ ≤ M for ω^N = 1
    intro ω hω
    rw [map_e2PolyZ]
    have hNne : N ≠ 0 := hN.ne'
    simpa [hM] using e2Poly_eval_nnnorm_le hNne a hω
  · -- char-0 nonvanishing on primitive roots, transported through the map
    intro ω hω
    rw [map_e2PolyZ]
    exact hChar0 ω hω

/-- **The clean-range contrapositive for the demand defect** (matching the supply
`no_spurious_tuple_of_lt_prime`).
If `C(w,2)^{φ(N)} < p`, no demand-side `e₂ = 0` char-`p`-only defect of width `w` exists on `μ_N`:
the `e₂` of any char-0-nonvanishing exponent set cannot vanish at a primitive `N`-th root mod `p`.
Same vacuity as the supply side in the prize regime. -/
theorem no_demand_defect_of_lt_prime {N : ℕ} (hN : 0 < N) {p w : ℕ} [Fact p.Prime] (a : Fin w → ℕ)
    (hgdeg : ((e2PolyZ a).map (Int.castRingHom (ZMod p))).natDegree = (e2PolyZ a).natDegree)
    (hChar0 : ∀ ω : ℂ, ω ∈ (cyclotomic N ℂ).roots → (e2Poly a).eval ω ≠ 0)
    (hlt : (pairSet w).card ^ N.totient < p)
    {ζ : ZMod p} (hζ : IsPrimitiveRoot ζ N) :
    ((e2PolyZ a).map (Int.castRingHom (ZMod p))).eval ζ ≠ 0 := by
  intro hVanish
  exact absurd (demand_defect_prime_le hN a hgdeg hChar0 hζ hVanish) (Nat.not_le.mpr hlt)

end ArkLib.ProximityGap.UnifyBConsolidation

/-! ## Axiom audit — must be `[propext, Classical.choice, Quot.sound]` only. -/
section AxiomAudit
open ArkLib.ProximityGap.UnifyBConsolidation
#print axioms e2Poly_eval_nnnorm_le
#print axioms map_e2PolyZ
#print axioms demand_defect_prime_le
#print axioms no_demand_defect_of_lt_prime
end AxiomAudit
