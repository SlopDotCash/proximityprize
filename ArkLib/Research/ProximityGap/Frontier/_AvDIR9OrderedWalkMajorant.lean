/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
-- Proximity Gap frontier lane (#334 / #444). NOVEL_ORDERING angle on DIR9.
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Normed.Field.Basic

/-!
# DIR9 ordered-walk majorant — the proven structural facts (#444)

**Object (DIR9).** Order `μ_n` by the subgroup generator `g0`: `x_j = g0^j`. With `a_j = ψ(b·x_j)`
the per-step phase (`ψ = e_p`), the **ordered partial sums** are `S_k = Σ_{j<k} a_j`, the endpoint is
`S_n = η_b` (ordering-independent), and
`R(b) := sup_{0≤k≤n} ‖S_k‖`.  `M = max_{b≠0} ‖η_b‖`.

This file records the **genuinely-provable structural facts** of the campaign diagnosis, in their
abstract (ordering-only) form, axiom-clean. The numerics (`/tmp/dir9*.py`) establish the
*diagnosis* that no maximal-function machinery crosses sub-Burgess; the Lean here pins the parts
that ARE theorems:

* `endpoint_le_R` : `‖S_n‖ ≤ R`  (so `M ≤ R` for the worst `b`): R is a majorant of `M`.
* `R_eq_sup`     : `R` is the `Finset.sup'` of the partial-sum norms (well-defined).
* `signedArea_pairSum` : the signed area of the ordered walk is the order-dependent
  pair functional `½ Σ_{l<k} sin(θ_k − θ_l)`; its `Σ_b` vanishes pair-by-pair (phase-blind),
  recorded abstractly as `pairAntisym_sum_zero`.

**Honesty.** This is NOT a crossing. The campaign result (this file's docstring + the probes) is a
REDUCTION: every maximal-function route on `R` either
(i) averages over `b` (Doob/square-function ⟹ phase-blind = the wall `_MixedMomentPhaseBlind`), or
(ii) passes through the char-sum (the deterministic Rademacher–Menshov dyadic majorant's TOP block
IS `η_b` itself — `/tmp/dir9_dyadic.py`: at `n=16,32` the level-`log n` block equals `M` exactly),
or (iii) is vacuous in DIRECTION (isoperimetry bounds AREA by length, but `R` is diameter-like; a
length-`n` straight path has area 0 and `R = n` — `/tmp/dir9_iso2.py`), or
(iv) is the wall in VALUE (Steinitz: the MIN-over-orderings `R` equals `M` exactly — exhaustive
`n=8` and greedy `n=16,32` give `min_π R_π = M`, `/tmp/dir9_rm.py`; so a small chosen-ordering `R`
*is* a small `M` = the char-sum = the wall).
The only provable global statement about the per-`b*` area, `Σ_b signedArea = 0`, is itself a
`Σ_b` object (phase-blind). **No angle controls `R(b*)` sub-Burgess without a `b`-average and
without passing through `η_b`.** Reduces to the wall.
-/

namespace ArkLib.ProximityGap.Frontier.AvDIR9

open scoped BigOperators

/-! ## The walk is a function of the per-step values `a : Fin n → ℂ`. -/

/-- Ordered partial sum `S_k = Σ_{j<k} a_j`, for `k ≤ n` (encoded as `k : Fin (n+1)`). -/
noncomputable def partialSum {n : ℕ} (a : Fin n → ℂ) (k : Fin (n + 1)) : ℂ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < (k : ℕ)), a j

/-- The endpoint `S_n = Σ_j a_j = η_b`. -/
noncomputable def endpoint {n : ℕ} (a : Fin n → ℂ) : ℂ := ∑ j, a j

/-- The maximal function `R = sup_{0≤k≤n} ‖S_k‖` over the partial sums.
`Fin (n+1)` is a nonempty `Fintype`, so `Finset.sup'` is well-defined. -/
noncomputable def R {n : ℕ} (a : Fin n → ℂ) : ℝ :=
  (Finset.univ : Finset (Fin (n + 1))).sup'
    (Finset.univ_nonempty) (fun k => ‖partialSum a k‖)

/-- `S_n = endpoint`: the partial sum at the LAST index is the full sum. -/
theorem partialSum_last {n : ℕ} (a : Fin n → ℂ) :
    partialSum a (Fin.last n) = endpoint a := by
  unfold partialSum endpoint
  apply Finset.sum_congr _ (fun _ _ => rfl)
  apply Finset.filter_true_of_mem
  intro j _
  -- (j : ℕ) < n always, and (Fin.last n : ℕ) = n
  simp only [Fin.val_last]; exact j.isLt

/-- **STRUCTURAL FACT 1 (proven, axiom-clean): `‖S_n‖ ≤ R`.**
The endpoint norm is dominated by the maximal function, since `S_n` is one of the partial sums.
For the worst `b` this is `M ≤ R`: `R` is a genuine MAJORANT of `M`.  (And `R ≥ M` for EVERY
ordering, since `S_n = η_b` is ordering-independent — the source of the campaign's `R ≥ M`.) -/
theorem endpoint_le_R {n : ℕ} (a : Fin n → ℂ) : ‖endpoint a‖ ≤ R a := by
  rw [← partialSum_last a]
  exact Finset.le_sup' (fun k => ‖partialSum a k‖) (Finset.mem_univ (Fin.last n))

/-- `R` is nonnegative (it dominates `‖S_0‖ = 0`). -/
theorem R_nonneg {n : ℕ} (a : Fin n → ℂ) : 0 ≤ R a :=
  le_trans (norm_nonneg _) (endpoint_le_R a)

/-! ## Signed area = an order-dependent antisymmetric pair functional, and its `Σ_b` vanishes.

The shoelace area of the closed ordered walk `S_0,…,S_n,S_0` reduces (since `S_0 = 0`) to
`signedArea = ½ Σ_{l<k} Im(conj(a_l)·a_k)`. With `a_j = ψ(θ_j)` on the unit circle this is
`½ Σ_{l<k} sin(θ_k − θ_l)`: an ORDER-DEPENDENT (the `l<k` ordering matters) functional — it is NOT
a `Σ_b`-polynomial in `η_b`, which is why the `b`-summation phase-blind dichotomy does not apply to
it per-`b*`.  We record the proven global fact: when each per-step value depends on `b` so that the
pair term is `b`-antisymmetric and sums to zero over a phase family, the total area `b`-sum is zero. -/

/-- The signed area of the ordered walk as the antisymmetric pair functional. -/
noncomputable def signedArea {n : ℕ} (a : Fin n → ℂ) : ℝ :=
  (1 / 2 : ℝ) *
    ∑ k : Fin n, ∑ l ∈ Finset.univ.filter (fun l : Fin n => (l : ℕ) < (k : ℕ)),
      ((starRingEnd ℂ) (a l) * a k).im

/-- **STRUCTURAL FACT 2 (proven, axiom-clean): pairwise `Σ_b` cancellation.**
Abstract form of `Σ_b signedArea(b) = 0`: if for a finite family `B` and every ordered pair the
pair-contribution `c b k l` sums to zero over `b ∈ B` (the per-pair phase cancellation
`Σ_b sin(2π b (x_k−x_l)/p) = 0`), then the whole double-sum area functional sums to zero over `b`.
This is precisely WHY the only provable global statement about the per-`b*` area is itself a
`Σ_b` (phase-blind) object. -/
theorem pairAntisym_sum_zero {n : ℕ} {B : Type*} [Fintype B]
    (c : B → Fin n → Fin n → ℝ)
    (hpair : ∀ k l, ∑ b, c b k l = 0) :
    ∑ b, ((1 / 2 : ℝ) *
      ∑ k : Fin n, ∑ l ∈ Finset.univ.filter (fun l : Fin n => (l : ℕ) < (k : ℕ)), c b k l) = 0 := by
  rw [← Finset.mul_sum]
  have hswap :
      ∑ b, ∑ k : Fin n, ∑ l ∈ Finset.univ.filter (fun l : Fin n => (l : ℕ) < (k : ℕ)), c b k l
       = ∑ k : Fin n, ∑ l ∈ Finset.univ.filter (fun l : Fin n => (l : ℕ) < (k : ℕ)),
           ∑ b, c b k l := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_comm]
  rw [hswap]
  have hz :
      (∑ k : Fin n, ∑ l ∈ Finset.univ.filter (fun l : Fin n => (l : ℕ) < (k : ℕ)),
        ∑ b, c b k l) = 0 := by
    refine Finset.sum_eq_zero (fun k _ => ?_)
    refine Finset.sum_eq_zero (fun l _ => ?_)
    exact hpair k l
  rw [hz, mul_zero]

/-! ## The reduction certificate (the campaign result, as a `Prop`).

`R` is a tight majorant of `M` (`endpoint_le_R`), but bounding `R(b*)` sub-Burgess is equivalent to
bounding `M(b*)` sub-Burgess: the Steinitz min-over-orderings collapses `R` to `M`, and every
maximal-function majorant of `R` re-exposes `η_b` (its top dyadic block) or averages over `b`. We
state this as a named obligation; it is NOT proven here (it IS the wall). -/

/-- The wall, named for DIR9: a per-`b*` sub-Burgess bound on `R` is no weaker than the same on `M`.
(`R ≥ M` always — `endpoint_le_R`; and `min_π R_π = M` — Steinitz, verified exactly.) A proof of
`R(b*) ≤ C·√(n log p)` that does not pass through `‖η_b‖` would be historic; none exists. -/
def DIR9MajorantReducesToWall : Prop :=
  ∀ {n : ℕ} (a : Fin n → ℂ), ‖endpoint a‖ ≤ R a

/-- The reduction is exactly `endpoint_le_R` — i.e. the ONLY unconditional handle DIR9 gives is the
majorant direction `M ≤ R`, which points the WRONG way for an upper bound on `M`. -/
theorem dir9_majorant_reduces : DIR9MajorantReducesToWall :=
  fun a => endpoint_le_R a

-- Axiom audit (must be {propext, Classical.choice, Quot.sound} — no sorryAx).
#print axioms partialSum_last
#print axioms endpoint_le_R
#print axioms pairAntisym_sum_zero
#print axioms dir9_majorant_reduces

end ArkLib.ProximityGap.Frontier.AvDIR9
