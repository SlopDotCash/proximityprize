/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Round 20 (Issue #232) — the clique double-block KERNEL STRUCTURE THEOREM: the twisted
# evaluation pencil lies in the kernel at EVERY codimension, over EVERY field

Direct new mathematics on Conjecture 41's object (ePrint 2026/858, the c≥3 Open-Set Rank Lemma ≈
the Grand List Challenge). The constraint matrix of a support family `{E_i}` with twists `{γ_i}`
has row blocks `[N_{E_i} | γ_i·N_{E_i}]`, where the `c` normals of `E` are the coefficient vectors
of `Λ_E·X^r` (`r < c`); the kernel condition for a syndrome pair `(s₁, s₂) ∈ F^D × F^D` is

  `∀ i, ∀ r < c : ⟨Λ_{E_i}·X^r, s₁⟩ + γ_i·⟨Λ_{E_i}·X^r, s₂⟩ = 0`.

For the **clique configuration** (the conjecture's universal obstruction: `E_α = W ∖ {α}`,
`|W| = w+1`) we prove the kernel structure:

* **Duality** (`pairing_locator_evalSyndrome`): under the coefficient pairing
  `⟨P, s⟩ = ∑_j P_j s_j`, the clique locators and the vertex evaluation syndromes
  `ev_β = (1, β, β², …)` are a **dual system**: `⟨Λ_{E_α}·X^r, ev_β⟩ = β^r·Λ_{E_α}(β)`, which is
  `0` for `β ∈ W ∖ {α}` and `≠ 0` at `β = α`.

* **The twisted evaluation pencil is in the kernel** (`clique_kernel_mem`): for EVERY weight
  function `b : W → F`, the pair

    `s₁ = − ∑_β γ(β)·b(β)·ev_β,    s₂ = ∑_β b(β)·ev_β`

  satisfies ALL `(w+1)·c` kernel conditions, at every codimension `c`, over every field: the
  `α`-condition collapses (diagonality) to `(−γ(α) + γ(α))·b(α)·α^r·Λ_{E_α}(α) = 0`.

* **The pencil has full dimension `w+1`** (`evalSyndrome_family_injective`): `b ↦ ∑_β b(β)·ev_β`
  is injective — pairing with `Λ_{E_α}` reads off `b(α)·Λ_{E_α}(α)` (duality again; no Vandermonde
  determinant needed).

**Consequences for Conjecture 41.** The universal obstruction is **unconditionally rank-deficient**:
`rank A_clique ≤ 2D − (w+1)` for every field, every codimension, every twist assignment — the
conjecture's "full rank" branch ALWAYS fails for cliques, so the conjecture lives entirely in its
second (degeneracy) branch: every kernel syndrome must be DEGENERATE (these pencil syndromes are
exactly the syndromes of error vectors supported on the vertex set `W`, the "false positives" of
their Remark 31). The complete kernel description (these pencils are the WHOLE kernel — the
partial-fraction relation count `dim = (w+1) + (w−1)(c−1) − …`) and the degeneracy analysis at
`c ≥ 2` are the remaining open steps; this file supplies the verified structural floor.
-/

open Polynomial Finset

namespace Round20CliqueKernel

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## 1. The objects: locators, normals, evaluation syndromes, the pairing -/

/-- The clique error locator at vertex `α`: `Λ_{W∖{α}} = ∏_{β ∈ W.erase α} (X − β)`. -/
noncomputable def cliqueLocator (W : Finset F) (α : F) : F[X] :=
  ∏ β ∈ W.erase α, (X - C β)

/-- The `r`-th normal polynomial of the support `E_α`: `Λ_{E_α}·X^r`. -/
noncomputable def normalPoly (W : Finset F) (α : F) (r : ℕ) : F[X] :=
  cliqueLocator W α * X ^ r

/-- The coefficient pairing `⟨P, s⟩ = ∑_{j<D} P_j·s_j` between polynomials and syndromes. -/
noncomputable def pairing (D : ℕ) (P : F[X]) (s : Fin D → F) : F :=
  ∑ j : Fin D, P.coeff (j : ℕ) * s j

/-- The evaluation syndrome at `t`: `ev_t = (1, t, t², …, t^{D−1})`. -/
def evalSyndrome (D : ℕ) (t : F) : Fin D → F := fun j => t ^ (j : ℕ)

/-! ## 2. Pairing against an evaluation syndrome = evaluation -/

omit [DecidableEq F] in
/-- For `natDegree P < D`: `⟨P, ev_t⟩ = P(t)` (the truncated coefficient sum captures all of `P`). -/
theorem pairing_evalSyndrome {D : ℕ} {P : F[X]} (hP : P.natDegree < D) (t : F) :
    pairing D P (evalSyndrome D t) = P.eval t := by
  unfold pairing evalSyndrome
  rw [Polynomial.eval_eq_sum_range' hP, ← Fin.sum_univ_eq_sum_range]

/-- Locator degree: `natDegree Λ_{E_α} = |W| − 1` for `α ∈ W`. -/
theorem cliqueLocator_natDegree {W : Finset F} {α : F} (hα : α ∈ W) :
    (cliqueLocator W α).natDegree = W.card - 1 := by
  unfold cliqueLocator
  rw [Polynomial.natDegree_prod]
  · rw [Finset.sum_congr rfl (fun β _ => Polynomial.natDegree_X_sub_C β), Finset.sum_const,
        smul_eq_mul, mul_one, Finset.card_erase_of_mem hα]
  · intro β _
    exact Polynomial.X_sub_C_ne_zero β

/-- Normal degree: `natDegree (Λ_{E_α}·X^r) = |W| − 1 + r`. -/
theorem normalPoly_natDegree {W : Finset F} {α : F} (hα : α ∈ W) (r : ℕ) :
    (normalPoly W α r).natDegree = W.card - 1 + r := by
  unfold normalPoly
  rw [Polynomial.natDegree_mul, cliqueLocator_natDegree hα, Polynomial.natDegree_X_pow]
  · unfold cliqueLocator
    apply Finset.prod_ne_zero_iff.mpr
    intro β _
    exact Polynomial.X_sub_C_ne_zero β
  · exact pow_ne_zero r Polynomial.X_ne_zero

/-- Locator evaluation at the vertices: `Λ_{E_α}(β) = 0` for `β ∈ W`, `β ≠ α`. -/
theorem cliqueLocator_eval_other {W : Finset F} {α β : F} (hβ : β ∈ W) (hne : β ≠ α) :
    (cliqueLocator W α).eval β = 0 := by
  unfold cliqueLocator
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hne, hβ⟩)
  simp

/-- **The dual-system identity:** `⟨Λ_{E_α}·X^r, ev_β⟩ = β^r·Λ_{E_α}(β)` whenever the normal's
degree fits below `D`. Diagonal: `≠ 0` only possibly at `β = α` (for `β ∈ W`). -/
theorem pairing_locator_evalSyndrome {W : Finset F} {α : F} (hα : α ∈ W) {r D : ℕ}
    (hD : W.card - 1 + r < D) (β : F) :
    pairing D (normalPoly W α r) (evalSyndrome D β)
      = β ^ r * (cliqueLocator W α).eval β := by
  rw [pairing_evalSyndrome (by rw [normalPoly_natDegree hα]; exact hD)]
  unfold normalPoly
  rw [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  ring

/-! ## 3. The kernel structure theorem -/

/-- **THE TWISTED EVALUATION PENCIL LIES IN THE KERNEL** — at every codimension `c`, over every
field, for every twist `γ : F → F` and weight `b : F → F`. With

  `s₁ := −∑_{β∈W} γ(β)·b(β)·ev_β,   s₂ := ∑_{β∈W} b(β)·ev_β`,

every kernel condition `⟨Λ_{E_α}X^r, s₁⟩ + γ(α)·⟨Λ_{E_α}X^r, s₂⟩ = 0` holds (`α ∈ W`, `r` with
the degree bound): off-diagonal terms vanish by duality, and the diagonal collapses to
`(−γ(α) + γ(α))·b(α)·α^r·Λ_{E_α}(α) = 0`. The conjecture's universal obstruction (the clique) is
therefore **unconditionally rank-deficient, with an explicit kernel family**. -/
theorem clique_kernel_mem (W : Finset F) (γ b : F → F) {α : F} (hα : α ∈ W) {r D : ℕ}
    (hD : W.card - 1 + r < D) :
    pairing D (normalPoly W α r) (fun j => -∑ β ∈ W, γ β * b β * evalSyndrome D β j)
      + γ α * pairing D (normalPoly W α r) (fun j => ∑ β ∈ W, b β * evalSyndrome D β j) = 0 := by
  classical
  -- linearity of the pairing in the syndrome argument
  have hlin : ∀ (w : F → F),
      pairing D (normalPoly W α r) (fun j => ∑ β ∈ W, w β * evalSyndrome D β j)
        = ∑ β ∈ W, w β * pairing D (normalPoly W α r) (evalSyndrome D β) := by
    intro w
    unfold pairing
    simp only
    calc ∑ j : Fin D, (normalPoly W α r).coeff (j : ℕ) * ∑ β ∈ W, w β * evalSyndrome D β j
        = ∑ j : Fin D, ∑ β ∈ W, (normalPoly W α r).coeff (j : ℕ) * (w β * evalSyndrome D β j) := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Finset.mul_sum]
      _ = ∑ β ∈ W, ∑ j : Fin D, (normalPoly W α r).coeff (j : ℕ) * (w β * evalSyndrome D β j) :=
          Finset.sum_comm
      _ = ∑ β ∈ W, w β * ∑ j : Fin D, (normalPoly W α r).coeff (j : ℕ) * evalSyndrome D β j := by
          refine Finset.sum_congr rfl (fun β _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          ring
  have hneg : pairing D (normalPoly W α r) (fun j => -∑ β ∈ W, γ β * b β * evalSyndrome D β j)
      = -pairing D (normalPoly W α r) (fun j => ∑ β ∈ W, γ β * b β * evalSyndrome D β j) := by
    unfold pairing
    simp [mul_neg]
  rw [hneg, hlin (fun β => γ β * b β), hlin b]
  -- only the diagonal β = α survives in each sum
  have hdiag : ∀ (w : F → F), (∑ β ∈ W, w β * pairing D (normalPoly W α r) (evalSyndrome D β))
      = w α * ((α : F) ^ r * (cliqueLocator W α).eval α) := by
    intro w
    rw [Finset.sum_eq_single α]
    · rw [pairing_locator_evalSyndrome hα hD]
    · intro β hβ hne
      rw [pairing_locator_evalSyndrome hα hD, cliqueLocator_eval_other hβ hne]
      ring
    · intro h; exact absurd hα h
  rw [hdiag, hdiag]
  ring

/-! ## 4. The pencil has full dimension `w+1`: `b ↦ ∑ b(β)·ev_β` is injective -/

/-- Locator self-evaluation is nonzero (distinct nodes). -/
theorem cliqueLocator_eval_self_ne_zero {W : Finset F} {α : F} :
    (cliqueLocator W α).eval α ≠ 0 := by
  unfold cliqueLocator
  rw [Polynomial.eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro β hβ
  have hne : β ≠ α := (Finset.mem_erase.mp hβ).1
  simpa using sub_ne_zero.mpr (Ne.symm hne)

/-- **Injectivity of the evaluation family** (duality, no Vandermonde determinant): if
`∑_β b(β)·ev_β = 0` in `F^D` (with `D > |W|−1` so the locators fit), pairing with `Λ_{E_α}` reads
off `b(α)·Λ_{E_α}(α) = 0`, hence `b ≡ 0` on `W`. So the kernel pencil of `clique_kernel_mem` has
full dimension `|W| = w+1`. -/
theorem evalSyndrome_family_injective (W : Finset F) {D : ℕ} (hD : W.card - 1 < D)
    (b : F → F) (hb : (fun j : Fin D => ∑ β ∈ W, b β * evalSyndrome D β j) = 0) :
    ∀ α ∈ W, b α = 0 := by
  classical
  intro α hα
  -- pair the vanishing syndrome with the locator (r = 0 normal)
  have hpair : pairing D (normalPoly W α 0) (fun j => ∑ β ∈ W, b β * evalSyndrome D β j) = 0 := by
    rw [hb]
    unfold pairing
    simp
  have hlin : pairing D (normalPoly W α 0) (fun j => ∑ β ∈ W, b β * evalSyndrome D β j)
      = ∑ β ∈ W, b β * pairing D (normalPoly W α 0) (evalSyndrome D β) := by
    unfold pairing
    simp only
    calc ∑ j : Fin D, (normalPoly W α 0).coeff (j : ℕ) * ∑ β ∈ W, b β * evalSyndrome D β j
        = ∑ j : Fin D, ∑ β ∈ W, (normalPoly W α 0).coeff (j : ℕ) * (b β * evalSyndrome D β j) := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Finset.mul_sum]
      _ = ∑ β ∈ W, ∑ j : Fin D, (normalPoly W α 0).coeff (j : ℕ) * (b β * evalSyndrome D β j) :=
          Finset.sum_comm
      _ = ∑ β ∈ W, b β * ∑ j : Fin D, (normalPoly W α 0).coeff (j : ℕ) * evalSyndrome D β j := by
          refine Finset.sum_congr rfl (fun β _ => ?_)
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          ring
  have hD0 : W.card - 1 + 0 < D := by omega
  rw [hlin, Finset.sum_eq_single α] at hpair
  · rw [pairing_locator_evalSyndrome hα hD0] at hpair
    simp only [pow_zero, one_mul] at hpair
    rcases mul_eq_zero.mp hpair with h | h
    · exact h
    · exact absurd h cliqueLocator_eval_self_ne_zero
  · intro β hβ hne
    rw [pairing_locator_evalSyndrome hα hD0, cliqueLocator_eval_other hβ hne]
    ring
  · intro h; exact absurd hα h

end Round20CliqueKernel

#print axioms Round20CliqueKernel.pairing_locator_evalSyndrome
#print axioms Round20CliqueKernel.clique_kernel_mem
#print axioms Round20CliqueKernel.evalSyndrome_family_injective
