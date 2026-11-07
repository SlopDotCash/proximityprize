/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.AGL24DualSpan
import ArkLib.Data.CodingTheory.AGL24GenericZeroPattern

/-!
# [AGL24] the grand assembly: Theorem 2.11 from the two classical imports
# (issue #346, brick 26 — the campaign capstone)

The single composition theorem threading every proven layer of the campaign: **Frank's
orientation theorem** (Theorem A.3, as `FrankOrientationResidual`) and **GM-MDS**
(Theorem A.2, as `GMMDSResidual`, stated in the matrix-free dual-span form brick 25
earned) jointly discharge the symbolic Theorem 2.11 interface — and with it, every
conditional statement above it in the tower, up to the front door.

The chain: weak partition connectivity → Frank's orientation (+ crossing supply) →
the generic zero pattern (brick 20, proven) → GM-MDS dual span → pinning (brick 25,
proven) → the evaluated witness (brick 24, proven) → symbolic full rank (brick 18,
proven).

* `FrankOrientationResidual` — Theorem A.3's interface;
* `GMMDSResidual` — Theorem A.2's interface (zero-pattern dual span from a GZP);
* `symbolicFullRank_of_classical_imports` — **the capstone**.
-/

open Finset

namespace AGL24

variable (ι : Type*) [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

/-- **The Frank orientation interface** ([AGL24] Theorem A.3, [20]): every
`k`-weakly-partition-connected hypergraph admits a head orientation with a root of
in-degree at least `k` and `k` crossing edges into every proper root-containing vertex
subset (the `k` edge-disjoint paths to the root). -/
def FrankOrientationResidual (k : ℕ) : Prop :=
  ∀ {t : ℕ}, 1 ≤ t → ∀ e : ι → Finset (Fin (t + 1)),
    (∀ i, (e i).Nonempty) →
    WeaklyPartitionConnected k (Finset.univ : Finset (Fin (t + 1))) e →
    ∃ O : HeadOrientation e, ∃ r : Fin (t + 1),
      k ≤ O.inDegree r ∧
      ∀ T : Finset (Fin (t + 1)), r ∈ T → T ≠ Finset.univ →
        k ≤ (Finset.univ.filter (fun i => O.head i ∈ T ∧ ¬ e i ⊆ T)).card

/-- **The GM-MDS interface** ([AGL24] Theorem A.2, [9]; matrix-free dual-span form): a
generic zero pattern for an edge family yields an evaluation embedding together with
zero-pattern dual vectors spanning the Reed–Solomon dual. -/
def GMMDSResidual (k : ℕ) : Prop :=
  ∀ {t : ℕ}, ∀ e : ι → Finset (Fin (t + 1)), ∀ δ : Fin (t + 1) → ℕ,
    GZPCondition e δ k →
    ∃ φ : ι ↪ F, ∃ d : ℕ, ∃ h : Fin d → (ι → F),
      (∀ ℓ, ∃ j : Fin (t + 1), ∀ i : ι, j ∉ e i → h ℓ i = 0) ∧
      Submodule.span F (Set.range h)
        = dotForm.orthogonal (ReedSolomon.code φ k)

/-- **THE CAMPAIGN CAPSTONE**: Frank's orientation theorem and GM-MDS jointly discharge
the symbolic Theorem 2.11 interface — and with it every layer of the tower above, up to
the front door. Every other step is a proven theorem of this campaign. -/
theorem symbolicFullRank_of_classical_imports {k : ℕ}
    (hfrank : FrankOrientationResidual ι k)
    (hgmmds : GMMDSResidual ι F k)
    (hnonempty : ∀ {t : ℕ}, ∀ e : ι → Finset (Fin (t + 1)),
      WeaklyPartitionConnected k (Finset.univ : Finset (Fin (t + 1))) e →
      ∀ i, (e i).Nonempty) :
    SymbolicFullRankResidual (ι := ι) F k := by
  refine symbolicFullRank_of_pinning ?_ hnonempty
  intro t ht e hne hwpc
  -- Frank: the orientation with root and crossing supply.
  obtain ⟨O, r, hroot, hcross⟩ := hfrank ht e hne hwpc
  -- Brick 20: the generic zero pattern.
  have hgzp := gzp_of_orientation O r k hne hroot hcross
  -- GM-MDS: the zero-pattern dual span.
  obtain ⟨φ, d, h, hsupp, hspan⟩ := hgmmds e _ hgzp
  -- Brick 25: pinning.
  exact ⟨φ, pinning_of_dual_span φ e h hsupp hspan⟩

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.symbolicFullRank_of_classical_imports
