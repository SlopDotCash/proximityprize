/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment

/-!
# The closed-walk power-sum identity `Σ_b η_b^k = q · #{k-walks closing at 0}` (#444)

ANGLE 4 (generalized-Paley spectral-moment handle), the ODD-aware companion to
`Frontier/_SpectralTraceZeroSignForcing`. With `η_b = Σ_{y∈G} ψ(b·y)` the non-principal eigenvalues
of the Cayley graph `Cay(F_q, G)` (`A = Σ_{x∈G} P^x`), the `k`-th **un-conjugated** power-sum is the
trace of `A^k`:

> **`spectral_pow_sum_eq`** : `Σ_{b∈F} (η_b)^k = q · #{v : Fin k → F | (∀i, v i ∈ G) ∧ Σᵢ v i = 0}`.

This is `tr(A^k) = Σ_b η_b^k = q · (#closed k-walks based at 0)` — a single application of additive-
character orthogonality, no Weil. It generalizes the file `_SpectralTraceZeroSignForcing`'s **`k=1`**
trace-zero case `Σ_b η_b = q·[0∈G] = 0` (since `0∉G`) to ALL `k`, and is the EXACT spectral analogue
of `SubgroupGaussSumMoment.subgroup_gaussSum_moment` (which is the **even, conjugated** form
`Σ_b ‖η_b‖^{2r} = q·E_r`). The difference is decisive:

* the conjugated/even moments `Σ_b‖η_b‖^{2r}` are **phase-blind** (`specMoment_phase_blind`) — sums of
  nonnegative magnitudes, invariant under `η_b ↦ -η_b`;
* the un-conjugated power-sums `Σ_b η_b^k` for **odd** `k` are NOT phase-blind — they are signed, and
  `tr(A^3) = Σ_b η_b^3` is the triangle/closed-3-walk count of the Paley graph (the first signed
  spectral invariant beyond the bare trace).

## Two clean structural corollaries

* **`spectral_pow_sum_nonneg_real`** : `Σ_b η_b^k` is a NONNEGATIVE REAL — it equals `q` times a
  cardinality (a `ℕ`), so the entire odd power-sum ladder is pinned to `q·ℤ_{≥0}`, an integrality/
  nonnegativity constraint the bulk `L²` energy functionals do not record per-`k`.
* **`spectral_pow_sum_one_eq_zero`** : the `k=1` instance recovers exactly `Σ_b η_b = 0` (no
  self-loops), reproving the trace-zero identity as the degenerate walk count `#{v : Fin 1 → G : v 0 = 0}
  = 0`.

## Honesty (project §6)

POSITIVE structural brick, NOT a closure and NOT a refutation. The identity is exact and axiom-clean
(orthogonality only, `AddChar.sum_mulShift`). It bounds NOTHING from above: the prize
`M = max_{b≠0}‖η_b‖ ≤ C√(n·log p)` (the char-`p` energy saddle / BGK wall) stays OPEN. The closed-walk
counts `#{k-walks}` are the COMBINATORIAL/additive-energy face; turning a count into the signed sup-norm
bound is exactly the unsigned→signed transfer the in-tree meta-theorem and the census-necessity entry
record as the wall. This is the un-conjugated, odd-`k`-aware companion of the even-moment
`SubgroupGaussSumMoment` and the first-moment `_SpectralTraceZeroSignForcing`. Issue #444 / #389.

## References
- `SubgroupGaussSumMoment.subgroup_gaussSum_moment` (`Σ_b‖η_b‖^{2r} = q·E_r`, conjugated/even form).
- `SubgroupGaussSumMoment.eta_pow` (`η_b^r = Σ_{v:Fin r→G} ψ(b·Σv)`).
- `Frontier/_SpectralTraceZeroSignForcing` (`Σ_b η_b = 0`, the `k=1` trace-zero case).
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false


open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment

namespace ProximityGap.Frontier.ClosedWalkPowerSum

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The set of closed `k`-walks based at `0`: `k`-tuples drawn from `G` whose entries sum to `0`. -/
noncomputable def closedWalks (G : Finset F) (k : ℕ) : Finset (Fin k → F) :=
  (Fintype.piFinset (fun _ : Fin k => G)).filter (fun v => ∑ i, v i = 0)

/-- **★ The closed-walk power-sum identity: `Σ_b η_b^k = q · #{closed k-walks at 0}`.**

`Σ_b η_b^k = Σ_b Σ_{v:Fin k→G} ψ(b·Σv) = Σ_{v:Fin k→G} Σ_b ψ(b·Σv) = Σ_{v:Fin k→G} q·[Σv=0]
= q·#{v : Σv=0}`. Pure orthogonality (`AddChar.sum_mulShift`), no Weil. This is `tr(A^k)` of the
generalized-Paley Cayley graph; for odd `k` it is a SIGNED spectral invariant the even-moment hierarchy
`Σ_b‖η_b‖^{2r}` (phase-blind) cannot encode. -/
theorem spectral_pow_sum_eq {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (k : ℕ) :
    ∑ b : F, eta ψ G b ^ k = (Fintype.card F : ℂ) * (closedWalks G k).card := by
  classical
  calc ∑ b : F, eta ψ G b ^ k
      = ∑ b : F, ∑ v ∈ Fintype.piFinset (fun _ : Fin k => G), ψ (b * ∑ i, v i) := by
        refine Finset.sum_congr rfl (fun b _ => ?_); rw [eta_pow]
    _ = ∑ v ∈ Fintype.piFinset (fun _ : Fin k => G), ∑ b : F, ψ (b * ∑ i, v i) :=
        Finset.sum_comm
    _ = ∑ v ∈ Fintype.piFinset (fun _ : Fin k => G),
          (if ∑ i, v i = 0 then (Fintype.card F : ℂ) else 0) := by
        refine Finset.sum_congr rfl (fun v _ => ?_)
        rw [AddChar.sum_mulShift (∑ i, v i) hψ]
        by_cases h : ∑ i, v i = 0 <;> simp [h]
    _ = (Fintype.card F : ℂ) * (closedWalks G k).card := by
        rw [closedWalks, ← Finset.sum_filter, Finset.sum_const]
        rw [nsmul_eq_mul, mul_comm]

/-- **The odd/all-`k` power-sum is a nonnegative real (pinned to `q·ℤ_{≥0}`).** `Σ_b η_b^k` equals `q`
times a cardinality, hence is a nonnegative real number — a per-`k` integrality/nonnegativity constraint
on the (signed) trace ladder that the bulk energy functionals do not record. -/
theorem spectral_pow_sum_nonneg_real {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (k : ℕ) :
    (∑ b : F, eta ψ G b ^ k).im = 0 ∧ 0 ≤ (∑ b : F, eta ψ G b ^ k).re := by
  rw [spectral_pow_sum_eq hψ G k]
  refine ⟨by simp, ?_⟩
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero]
  positivity

/-- **The `k=1` case recovers the trace-zero identity `Σ_b η_b = 0`** (no self-loops, `0∉G`). The
closed-`1`-walk count `#{v : Fin 1 → G | v 0 = 0}` is `0` because `0 ∉ G`. -/
theorem spectral_pow_sum_one_eq_zero {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (h0 : (0 : F) ∉ G) :
    ∑ b : F, eta ψ G b ^ 1 = 0 := by
  classical
  rw [spectral_pow_sum_eq hψ G 1]
  have hempty : closedWalks G 1 = ∅ := by
    rw [closedWalks, Finset.filter_eq_empty_iff]
    intro v hv
    rw [Fintype.mem_piFinset] at hv
    rw [Fin.sum_univ_one]
    intro hcontra
    exact h0 (hcontra ▸ hv 0)
  rw [hempty]; simp

end ProximityGap.Frontier.ClosedWalkPowerSum

/-! ## Axiom audit (expected: `propext, Classical.choice, Quot.sound` only). -/
#print axioms ProximityGap.Frontier.ClosedWalkPowerSum.spectral_pow_sum_eq
#print axioms ProximityGap.Frontier.ClosedWalkPowerSum.spectral_pow_sum_nonneg_real
#print axioms ProximityGap.Frontier.ClosedWalkPowerSum.spectral_pow_sum_one_eq_zero
