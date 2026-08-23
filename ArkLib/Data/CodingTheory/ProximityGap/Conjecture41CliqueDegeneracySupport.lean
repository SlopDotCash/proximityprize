/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Conjecture41CliqueKernelStructure

/-!
# Round 23 (Issue #444 / #232) — the clique kernel pencil's WEIGHT/SUPPORT readoff: the degeneracy
# coordinate `b(α)` is recovered from a single pairing, characterizing the "false-positive" object

`Conjecture41CliqueKernelStructure` (Round 20) proves the twisted evaluation pencil
`s₂(b) = ∑_{β∈W} b(β)·ev_β` lies in the clique kernel and that `b ↦ s₂(b)` is injective. Per
#444 §6.1 (line 187) the residual of Conjecture 41 is the **degeneracy escape clause**: for which
`p` does the pencil contain a syndrome that is a *genuine* full-weight error supported on the
vertex set `W` (the "false positives" of ePrint 2026/858 Remark 31). That object is governed by
the support of the weight vector `b`. This file lands the clean readoff that makes the support of
`s₂(b)` decidable coordinate-by-coordinate, axiom-clean:

* **`pairing_kernel_pencil_eq` :** `⟨Λ_{E_α}, s₂(b)⟩ = b(α)·Λ_{E_α}(α)` — the pencil's pairing
  against the `α`-locator reads off exactly the `α`-coordinate weight (off-diagonal vanishes by
  duality, diagonal survives). PROBE-confirmed exactly (200/200, ℚ + F_p).
* **`pairing_kernel_pencil_ne_zero_iff` (HEADLINE):** `⟨Λ_{E_α}, s₂(b)⟩ ≠ 0 ⟺ b(α) ≠ 0`
  (since `Λ_{E_α}(α) ≠ 0` in a field) — so the **support of the degeneracy weight is recoverable
  from the syndrome**: `{α∈W : b(α)≠0} = {α∈W : ⟨Λ_{E_α}, s₂(b)⟩ ≠ 0}`. The pencil is a
  full-weight-`(w+1)` error on `W` iff every such pairing is nonzero — the precise condition the
  degeneracy escape clause quantifies over `p`.

NON-MOMENT structural (the in-tree clique duality, no Wick/energy/orbit/char-sum), EXTEND-proven
(sits directly on `Round20CliqueKernel.pairing_locator_evalSyndrome` /
`cliqueLocator_eval_self_ne_zero`), FRONTIER-MOVEMENT (turns the degeneracy object into a decidable
coordinate readoff). Honest scope: this is the *characterization* of the degeneracy object, NOT a
bound on the exceptional primes — that integer-determinant height bound (the Round-19 transfer
engine target) remains the OPEN §6.1 residual.
-/

open Polynomial Finset

namespace Round23CliqueDegeneracy

variable {F : Type*} [Field F] [DecidableEq F]

open Round20CliqueKernel

/-- The kernel pencil syndrome `s₂(b) = ∑_{β∈W} b(β)·ev_β` (Round-20 kernel member). -/
noncomputable def kernelPencil (W : Finset F) (b : F → F) (D : ℕ) : Fin D → F :=
  fun j => ∑ β ∈ W, b β * evalSyndrome D β j

/-- **Coordinate readoff.** Pairing the kernel pencil `s₂(b)` against the `α`-locator
`Λ_{E_α}` reads off the `α`-weight: `⟨Λ_{E_α}, s₂(b)⟩ = b(α)·Λ_{E_α}(α)`. The off-diagonal
contributions vanish (`Λ_{E_α}(β)=0` for `β∈W∖{α}`), the diagonal survives. -/
theorem pairing_kernel_pencil_eq {W : Finset F} {α : F} (hα : α ∈ W) {D : ℕ}
    (hD : W.card - 1 < D) (b : F → F) :
    pairing D (normalPoly W α 0) (kernelPencil W b D)
      = b α * (cliqueLocator W α).eval α := by
  classical
  unfold kernelPencil
  -- linearity of the pairing in the syndrome argument, then collapse to the diagonal
  have hlin : pairing D (normalPoly W α 0) (fun j => ∑ β ∈ W, b β * evalSyndrome D β j)
      = ∑ β ∈ W, b β * pairing D (normalPoly W α 0) (evalSyndrome D β) := by
    unfold pairing
    calc ∑ j : Fin D, (normalPoly W α 0).coeff (j : ℕ) * ∑ β ∈ W, b β * evalSyndrome D β j
        = ∑ j : Fin D, ∑ β ∈ W, (normalPoly W α 0).coeff (j : ℕ) * (b β * evalSyndrome D β j) := by
          refine Finset.sum_congr rfl (fun j _ => ?_); rw [Finset.mul_sum]
      _ = ∑ β ∈ W, ∑ j : Fin D, (normalPoly W α 0).coeff (j : ℕ) * (b β * evalSyndrome D β j) :=
          Finset.sum_comm
      _ = ∑ β ∈ W, b β * ∑ j : Fin D, (normalPoly W α 0).coeff (j : ℕ) * evalSyndrome D β j := by
          refine Finset.sum_congr rfl (fun β _ => ?_)
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun j _ => ?_); ring
  have hD0 : W.card - 1 + 0 < D := by omega
  rw [hlin, Finset.sum_eq_single α]
  · rw [pairing_locator_evalSyndrome hα hD0]; simp
  · intro β hβ hne
    rw [pairing_locator_evalSyndrome hα hD0, cliqueLocator_eval_other hβ hne]; ring
  · intro h; exact absurd hα h

/-- **HEADLINE — the degeneracy support readoff.** `⟨Λ_{E_α}, s₂(b)⟩ ≠ 0 ⟺ b(α) ≠ 0`: the
support of the degeneracy weight `b` is recoverable coordinate-by-coordinate from the kernel
pencil syndrome (because `Λ_{E_α}(α) ≠ 0` in a field). So
`{α∈W : b(α)≠0} = {α∈W : ⟨Λ_{E_α}, s₂(b)⟩ ≠ 0}`, and the pencil is a full weight-`(w+1)` error
on `W` iff every such pairing is nonzero — the exact object the §6.1 degeneracy escape clause
quantifies over `p`. -/
theorem pairing_kernel_pencil_ne_zero_iff {W : Finset F} {α : F} (hα : α ∈ W) {D : ℕ}
    (hD : W.card - 1 < D) (b : F → F) :
    pairing D (normalPoly W α 0) (kernelPencil W b D) ≠ 0 ↔ b α ≠ 0 := by
  rw [pairing_kernel_pencil_eq hα hD b]
  constructor
  · intro h hb; exact h (by rw [hb, zero_mul])
  · intro hb
    exact mul_ne_zero hb cliqueLocator_eval_self_ne_zero

end Round23CliqueDegeneracy

#print axioms Round23CliqueDegeneracy.pairing_kernel_pencil_eq
#print axioms Round23CliqueDegeneracy.pairing_kernel_pencil_ne_zero_iff
