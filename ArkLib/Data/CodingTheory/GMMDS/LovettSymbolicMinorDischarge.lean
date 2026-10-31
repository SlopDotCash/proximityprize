/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.GMMDS.LovettDualSpanConnector
import ArkLib.Data.CodingTheory.AGL24NonzeroMinor

/-!
# `SymbolicMinorFromLovett` via the direct ring-change transfer (#389)

`LovettDualSpanConnector.lean` leaves `SymbolicMinorFromLovett` as residual 1 (the *encoding*
move): from Lovett's Theorem 1.7 (`LovettThm17`, **proven** unconditionally, see
`lovettThm17_unconditional`) and a generic zero pattern `(e, δ)` with `GZPCondition e δ k`, the
AGL24 reduced intersection matrix `RIM F e` has a square `(Fin t × Fin k)` submatrix whose
**polynomial** determinant is not identically zero.

## Why the two earlier shortcuts are dead

* The **WPC shortcut** (`symbolicMinor_of_symbolicFullRank`) routes through
  `WeaklyPartitionConnected k univ e`.  But **`GZPCondition e δ k` does NOT imply
  `WeaklyPartitionConnected k univ e`** (the 11th machine-checked false-residual of the #389
  GM-MDS cone; see `Research/ProximityPrize/DISPROOF_LOG.md`).  So that consumer cannot be fed from a bare GZP.

* The **`symbolicFullRank_of_classical_imports` route is CIRCULAR**: it discharges
  `SymbolicFullRankResidual` by routing through `GMMDSResidual`, which is itself the AGL24
  GM-MDS boundary we are trying to prove.

So `SymbolicMinorFromLovett` must be obtained on the **genuine path**: turn Lovett's symbolic
independence — which lives over the *dual-variable* ring `MvPolynomial (Fin n) F` (the formal
evaluation points `a₁,…,aₙ`) — into kernel-triviality of `RIM F e`, which lives over the
*edge-variable* ring `MvPolynomial ι F` (the Vandermonde variables `Xᵢ`).  That is the
GM-MDS matrix construction (Lovett §1, AGL24 Appendix A / [9, Thm A.2]).

## What this file delivers

1. **`RIMKernelTrivialFromLovett`** — the precisely-stated **ring-change transfer residual**:
   `(∀ m, LovettThm17 F m) → GZPCondition e δ k → ((RIM F e).mulVec v = 0 → v = 0)` over
   `MvPolynomial ι F`.  It was intended to isolate the transport of Lovett's independence
   across the two polynomial rings to the RIM's trivial kernel, dropping the WPC hypothesis.
   Dropping WPC makes it **false** (see "Status of the residual" below).

2. **`symbolicMinorFromLovett_of_ringChange`** — the **discharge**: from
   `RIMKernelTrivialFromLovett` the connector residual `SymbolicMinorFromLovett` follows by the
   same fraction-field extraction + `RingHom.map_det` descent that proves
   `exists_nonzero_poly_minor` (here re-run without the WPC detour).  Axiom-clean.

3. **A WPC-guarded companion** (`rimKernelTrivial_conclusion_of_symbolicFullRank_wpc`): the
   residual's *conclusion* follows from `SymbolicFullRankResidual` under the stronger WPC and
   `1 ≤ t` premises. This does **not** show the universally quantified residual is satisfiable —
   and in fact it is not: `RIMKernelTrivialFromLovett` is **refuted**
   (`rimKernelTrivialFromLovett_refuted`, and for every `1 ≤ k`
   `not_rimKernelTrivialFromLovett`, in `LovettRIMKernelTrivial.lean`; the 14th false-residual
   catch: at `e ≡ ∅`, `δ ≡ 0` the bare `GZPCondition` holds but the RIM has no rows).

4. **The column-index bijection brick** (`rimCols_equiv_pFamUnion_index_of_shape`): the AGL24
   RIM column index `Fin t × Fin k` is in bijection with Lovett's family index
   `Σᵢ Fin(k − |vᵢ|)` exactly when the `V*(k)` system has the *generic shape*
   `∑ᵢ (k − |vᵢ|) = t · k` (Lovett Def 1.4's `m`-rows-of-the-`k×n`-MDS-matrix normalization).
   This is only a cardinality identification (any two finite types of equal size are in
   bijection); it carries no ring-change content and certifies nothing about the transfer.

## Status of the residual (corrected)

`RIMKernelTrivialFromLovett` was intended to carry the full GM-MDS matrix construction (Lovett's
`pFamUnion`-independence over `MvPolynomial (Fin n) F` ⟹ `RIM`-kernel-triviality over
`MvPolynomial ι F`). It is not circular, but **as stated it is FALSE** for every `1 ≤ k`
(`not_rimKernelTrivialFromLovett`): a bare `GZPCondition` admits degenerate, row-free edge
families. An earlier version of this docstring called it "not vacuous" on the strength of the
WPC-guarded companion lemma, which proves a different statement. The corrected residual is
`RIMKernelTrivialFromLovettWPC` (`LovettRIMKernelTrivial.lean`). The conditional determinant
descent `symbolicMinorFromLovett_of_ringChange` itself is correct.

Issue #389.
-/

open Finset

namespace ArkLib.GMMDS

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F]

/-- **The ring-change transfer residual** (refuted as stated; see below), stated directly at
the RIM kernel (no `WeaklyPartitionConnected`, no `SymbolicFullRankResidual`, no `GMMDSResidual`).

From Lovett's Theorem 1.7 (proven unconditionally) and a generic zero pattern `(e, δ)` with
`GZPCondition e δ k`, the reduced intersection matrix `RIM F e` has **trivial kernel over the
edge-variable ring** `MvPolynomial ι F`.

Mathematically this is the GM-MDS matrix construction: Lovett's `pFamUnion V k` is linearly
independent over the *dual-variable* ring `MvPolynomial (Fin n) F`, and the GM-MDS
correspondence transports that independence — across the column-index bijection
`Fin t × Fin k ≃ Σᵢ Fin(k − |vᵢ|)` and the ring change — to the RIM's full column rank, i.e.
its trivial polynomial kernel.  **As stated this `Prop` is FALSE** for every `1 ≤ k`
(`not_rimKernelTrivialFromLovett`, `LovettRIMKernelTrivial.lean`): replacing the
`WeaklyPartitionConnected` hypothesis of `exists_nonzero_poly_minor` by a bare `GZPCondition`
loses the nondegeneracy (`e ≡ ∅`, `δ ≡ 0` satisfies `GZPCondition` with a zero-row RIM). The
corrected form is `RIMKernelTrivialFromLovettWPC`. -/
def RIMKernelTrivialFromLovett (ι : Type*) [Fintype ι] [DecidableEq ι]
    (F : Type*) [Field F] (k : ℕ) : Prop :=
  (∀ m : ℕ, LovettThm17 (F := F) m) →
  ∀ {t : ℕ}, ∀ e : ι → Finset (Fin (t + 1)), ∀ δ : Fin (t + 1) → ℕ,
    AGL24.GZPCondition e δ k →
    ∀ v : Fin t × Fin k → MvPolynomial ι F,
      (AGL24.RIM F e).mulVec v = 0 → v = 0

/-- **The discharge of `SymbolicMinorFromLovett` from the ring-change transfer.**

Given `RIMKernelTrivialFromLovett` — the genuine transport of Lovett's independence to the RIM
kernel — `SymbolicMinorFromLovett` follows.  The proof is the fraction-field extraction +
`RingHom.map_det` descent of `exists_nonzero_poly_minor`, re-run with the trivial kernel coming
from `RIMKernelTrivialFromLovett` (the GZP path) instead of from `SymbolicFullRankResidual`
applied to a WPC witness (the dead WPC path).  Axiom-clean. -/
theorem symbolicMinorFromLovett_of_ringChange {k : ℕ}
    (hrc : RIMKernelTrivialFromLovett ι F k) :
    SymbolicMinorFromLovett ι F k := by
  classical
  intro hlovett t e δ hgzp
  -- The polynomial kernel is trivial, by the ring-change transfer.
  have hpoly : ∀ v : Fin t × Fin k → MvPolynomial ι F,
      (AGL24.RIM F e).mulVec v = 0 → v = 0 := hrc hlovett e δ hgzp
  -- Lift to the fraction field.
  set K := FractionRing (MvPolynomial ι F)
  have hfrac : ∀ v : Fin t × Fin k → K,
      ((AGL24.RIM F e).map (algebraMap (MvPolynomial ι F) K)).mulVec v = 0 → v = 0 :=
    AGL24.frac_kernel_trivial_of_poly_kernel_trivial (AGL24.RIM F e) hpoly
  -- Extract a nonsingular square submatrix over the fraction field.
  obtain ⟨rows, hinj, hdet⟩ :=
    AGL24.exists_square_submatrix_det_ne_zero
      ((AGL24.RIM F e).map (algebraMap (MvPolynomial ι F) K)) hfrac
  refine ⟨rows, hinj, ?_⟩
  -- Descend the determinant: nonzero over `K` ⟹ nonzero as a polynomial.
  intro hzero
  apply hdet
  have hcomm : ((AGL24.RIM F e).map (algebraMap (MvPolynomial ι F) K)).submatrix rows
      (id : Fin t × Fin k → Fin t × Fin k)
      = (((AGL24.RIM F e).submatrix rows
          (id : Fin t × Fin k → Fin t × Fin k)).map
            (algebraMap (MvPolynomial ι F) K)) := rfl
  rw [hcomm]
  rw [show ((((AGL24.RIM F e).submatrix rows (id : Fin t × Fin k → Fin t × Fin k)).map
      (algebraMap (MvPolynomial ι F) K)).det)
      = (algebraMap (MvPolynomial ι F) K) (((AGL24.RIM F e).submatrix rows
          (id : Fin t × Fin k → Fin t × Fin k)).det) from by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]]
  rw [hzero, map_zero]

/-! ## A WPC-guarded companion (not a satisfiability proof)

Whenever a `WeaklyPartitionConnected` witness is available and the symbolic full-rank interface
holds, the RIM kernel is trivial — the conclusion shape of `RIMKernelTrivialFromLovett`. This
does **not** show the residual is satisfiable: the residual quantifies over all bare-GZP
families, and it is refuted (`not_rimKernelTrivialFromLovett`). -/

omit [DecidableEq ι] in
/-- **The ring-change conclusion under the symbolic full-rank interface + a WPC
witness.**  If `SymbolicFullRankResidual F k` holds and the edge family is weakly partition
connected, then `RIM F e` has trivial polynomial kernel — the conclusion shape of
`RIMKernelTrivialFromLovett`.  Axiom-clean.

This is not a non-vacuity certificate for `RIMKernelTrivialFromLovett`: the residual asks for
the same conclusion from the strictly weaker bare `GZPCondition`, and that strengthening is
false (`not_rimKernelTrivialFromLovett`). -/
theorem rimKernelTrivial_conclusion_of_symbolicFullRank_wpc {k : ℕ}
    (hsym : AGL24.SymbolicFullRankResidual (ι := ι) F k)
    {t : ℕ} (ht : 1 ≤ t) (e : ι → Finset (Fin (t + 1)))
    (hwpc : AGL24.WeaklyPartitionConnected k (Finset.univ : Finset (Fin (t + 1))) e)
    (v : Fin t × Fin k → MvPolynomial ι F)
    (hker : (AGL24.RIM F e).mulVec v = 0) :
    v = 0 :=
  hsym ht e hwpc v hker

/-! ## The column-index bijection (step (3) of the genuine path)

The AGL24 RIM has columns `Fin t × Fin k` (`t·k` of them, the `(t−1+1)·k` after the reduced
vertex bookkeeping is absorbed into `t`).  Lovett's family `pFamUnion V k` has index
`Σᵢ Fin(k − |vᵢ|)`, of cardinality `∑ᵢ (k − |vᵢ|)` (`card_pFamUnion_index`).  These match in
cardinality exactly when the `V*(k)` system has the generic shape `∑ᵢ (k − |vᵢ|) = t·k` — the
"`m` generator rows of the `k × n` MDS matrix" normalization of Lovett Def 1.4.  We record the
bijection at that shape; it is the index identification any ring-change transfer must perform. -/

/-- **The column-index bijection brick.**  When the `V*(k)` system `V : Fin m → Fin n → ℕ` has
the generic shape `∑ᵢ (k − |vᵢ|) = t · k`, the AGL24 RIM column index `Fin t × Fin k` is in
bijection with Lovett's family index `Σᵢ Fin(k − |vᵢ|)`.  Field-independent; purely a counting
identification (both sides are finite of equal cardinality).  Axiom-clean. -/
noncomputable def rimCols_equiv_pFamUnion_index_of_shape
    {t k m n : ℕ} (V : Fin m → (Fin n → ℕ))
    (hshape : ∑ i, (k - vAbs (V i)) = t * k) :
    (Fin t × Fin k) ≃ (Σ i : Fin m, Fin (k - vAbs (V i))) := by
  classical
  apply Fintype.equivOfCardEq
  rw [card_pFamUnion_index, hshape]
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

omit [DecidableEq ι] in
/-- **The genuine shape is realizable** (non-vacuity of the bijection brick): the all-zero
`V*(k)`-shaped system over `m = t` rows has `∑ᵢ (k − |vᵢ|) = t · k`, so the column-index
bijection is inhabited at the generic shape.  (This is a *shape* witness for the bijection, not
a claim that the all-zero system is `V*(k)` — `IsVStar` fails for `t ≥ 2`; the genuine `vᵢ`
encode the edge structure.  It shows only that the cardinality identity `∑(k−|vᵢ|)=t·k` is
satisfiable; it certifies nothing about the ring-change transfer.)  Axiom-clean. -/
theorem rimCols_shape_satisfiable (t k : ℕ) :
    ∑ _i : Fin t, (k - vAbs (Function.const (Fin (Fintype.card ι)) (0 : ℕ)))
      = t * k := by
  simp [vAbs, Function.const]

end ArkLib.GMMDS

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ArkLib.GMMDS.symbolicMinorFromLovett_of_ringChange
#print axioms ArkLib.GMMDS.rimKernelTrivial_conclusion_of_symbolicFullRank_wpc
#print axioms ArkLib.GMMDS.rimCols_equiv_pFamUnion_index_of_shape
#print axioms ArkLib.GMMDS.rimCols_shape_satisfiable
