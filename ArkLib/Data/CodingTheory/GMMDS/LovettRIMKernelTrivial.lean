/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.GMMDS.LovettSymbolicMinorDischarge
import ArkLib.Data.CodingTheory.GMMDS.LovettMergeIndepProof

/-!
# `RIMKernelTrivialFromLovett` is **FALSE as stated** — and the corrected, true residual (#389)

`LovettSymbolicMinorDischarge.lean` isolates the GM-MDS ring-transfer as the named residual
`RIMKernelTrivialFromLovett`:

```
(∀ m, LovettThm17 F m) → ∀ {t} e δ, GZPCondition e δ k →
  ∀ v, (RIM F e).mulVec v = 0 → v = 0.
```

This file records a **machine-checked refutation** of that residual (the 14th false-residual of
the #389 GM-MDS cone), and replaces it with the corrected statement that *is* true and that the
genuine GM-MDS construction actually supplies.

## The refutation (`rimKernelTrivialFromLovett_refuted`)

`GZPCondition e δ k` is **vacuously true** when `δ ≡ 0` (its quantifier ranges only over
`κ ≤ δ` with `0 < ∑ κ`, of which there are none).  Take the *degenerate* zero pattern
`e ≡ ∅`, `δ ≡ 0` over `ι = Fin 1`, `t = k = 1`:

* `GZPCondition (fun _ => ∅) (fun _ => 0) 1` holds (vacuously);
* but `RIMRowIdx (fun _ => ∅)` is **empty** (an empty edge has no non-minimal vertices), so
  `RIM F e` has **zero rows** and `(RIM F e).mulVec v = 0` holds for **every** `v`;
* yet the conclusion demands `v = 0`, which fails at `v ≡ 1 ≠ 0`.

So `GZPCondition` alone is *too weak* to force the RIM kernel to be trivial: a degenerate edge
family satisfies the hypothesis but leaves the matrix with fewer rows than columns (rank
deficient).  This is exactly the in-tree fact that **`GZPCondition` does NOT imply
`WeaklyPartitionConnected`** (the 11th false-residual, `DISPROOF_LOG.md`), now sharpened to a
full refutation of the kernel-triviality conclusion itself, not merely of the WPC bridge.

## The corrected residual (`RIMKernelTrivialFromLovettWPC`)

The genuine GM-MDS path does **not** feed the RIM kernel from a bare `GZPCondition`: the
construction produces a *weakly partition connected* edge family (the `k` edge-disjoint paths of
[AGL24] Theorem A.3 / Frank's orientation theorem are exactly the WPC supply).  With that
nondegeneracy hypothesis the conclusion is true and already in tree:

* `RIMKernelTrivialFromLovettWPC` — the kernel-triviality conclusion under the genuine
  `WeaklyPartitionConnected` + `1 ≤ t` hypotheses;
* `rimKernelTrivialFromLovettWPC_of_symbolicFullRank` — it follows from the [AGL24] Theorem 2.11
  interface `SymbolicFullRankResidual` (this is `exists_nonzero_poly_minor`'s hypothesis, the
  genuine Appendix-A input).  Axiom-clean.

So the honest ledger after this file: the GM-MDS algebra reduces to `SymbolicFullRankResidual`
(Theorem 2.11, a self-contained statement with its own Appendix-A proof) **under the WPC
nondegeneracy that the construction supplies** — not to the false `RIMKernelTrivialFromLovett`.

Issue #389.
-/

open Finset

namespace ArkLib.GMMDS

/-! ## The refutation of `RIMKernelTrivialFromLovett` -/

/-- **`RIMKernelTrivialFromLovett` is FALSE as stated** (the 14th machine-checked
false-residual of the #389 GM-MDS cone).

Witness: `ι = Fin 1`, `F = ℚ`, `k = 1`, and the degenerate zero pattern `e ≡ ∅`, `δ ≡ 0`,
`t = 1`.  `GZPCondition` holds vacuously (no `κ ≤ 0` with `0 < ∑ κ`); the RIM has **zero rows**
(empty edges have no non-minimal vertices), so `mulVec v = 0` for *every* `v`; yet the
conclusion forces `v = 0`, contradicted by the constant-`1` vector.

The takeaway: `GZPCondition` alone is too weak to make the RIM kernel trivial — the genuine
GM-MDS construction supplies a `WeaklyPartitionConnected` family (the corrected residual below).
Axiom-clean. -/
theorem rimKernelTrivialFromLovett_refuted :
    ¬ RIMKernelTrivialFromLovett (Fin 1) ℚ 1 := by
  classical
  intro h
  -- GZPCondition holds vacuously for δ ≡ 0.
  have hgzp : AGL24.GZPCondition (fun _ : Fin 1 => (∅ : Finset (Fin (1 + 1))))
      (fun _ => 0) 1 := by
    intro κ hκ hpos
    exfalso
    have hz : ∀ j, κ j = 0 := fun j => Nat.le_zero.mp (hκ j)
    simp only [hz] at hpos
    simp at hpos
  -- Lovett's Theorem 1.7 holds unconditionally.
  have hlov : ∀ m : ℕ, LovettThm17 (F := ℚ) m := fun _ => lovettThm17_unconditional
  -- The constant-one vector is a kernel vector (the matrix has no rows).
  set v : Fin 1 × Fin 1 → MvPolynomial (Fin 1) ℚ := fun _ => 1 with hv
  have hmul :
      (AGL24.RIM ℚ (fun _ : Fin 1 => (∅ : Finset (Fin (1 + 1))))).mulVec v = 0 := by
    funext r
    exact absurd r.2.property.1 (by simp)
  have hv0 := h hlov (fun _ : Fin 1 => (∅ : Finset (Fin (1 + 1)))) (fun _ => 0) hgzp v hmul
  have : v (0, 0) = (0 : MvPolynomial (Fin 1) ℚ) := by rw [hv0]; rfl
  simp only [hv] at this
  exact one_ne_zero this

/-! ## The corrected residual: kernel-triviality under the WPC nondegeneracy

The genuine GM-MDS path produces a weakly partition connected edge family (the `k`
edge-disjoint paths of [AGL24] Theorem A.3).  Under that hypothesis the kernel-triviality
conclusion is true — and follows directly from the [AGL24] Theorem 2.11 interface. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F]

/-- **The corrected ring-change residual.**  Identical conclusion to
`RIMKernelTrivialFromLovett`, but with the genuine **`WeaklyPartitionConnected` + `1 ≤ t`**
nondegeneracy hypotheses that the GM-MDS construction supplies (in place of the too-weak bare
`GZPCondition`, which `rimKernelTrivialFromLovett_refuted` shows is insufficient). -/
def RIMKernelTrivialFromLovettWPC (ι : Type*) [Fintype ι] [DecidableEq ι]
    (F : Type*) [Field F] (k : ℕ) : Prop :=
  ∀ {t : ℕ}, 1 ≤ t → ∀ e : ι → Finset (Fin (t + 1)),
    AGL24.WeaklyPartitionConnected k (Finset.univ : Finset (Fin (t + 1))) e →
    ∀ v : Fin t × Fin k → MvPolynomial ι F,
      (AGL24.RIM F e).mulVec v = 0 → v = 0

/-- **The corrected residual follows from the [AGL24] Theorem 2.11 interface.**  The genuine
Appendix-A input `SymbolicFullRankResidual` discharges `RIMKernelTrivialFromLovettWPC` directly:
this is exactly the hypothesis of `exists_nonzero_poly_minor`.  Axiom-clean.

So the honest residual ledger reduces the GM-MDS algebra to `SymbolicFullRankResidual` under the
WPC nondegeneracy the construction provides — not to the refuted `RIMKernelTrivialFromLovett`. -/
theorem rimKernelTrivialFromLovettWPC_of_symbolicFullRank {k : ℕ}
    (hsym : AGL24.SymbolicFullRankResidual (ι := ι) F k) :
    RIMKernelTrivialFromLovettWPC ι F k :=
  fun ht e hwpc v hker => hsym ht e hwpc v hker

end ArkLib.GMMDS

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ArkLib.GMMDS.rimKernelTrivialFromLovett_refuted
#print axioms ArkLib.GMMDS.rimKernelTrivialFromLovettWPC_of_symbolicFullRank
