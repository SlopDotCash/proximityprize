/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BSG_DRC1
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Tactic.GCongr

/-!
# BSG `E4d` — the Ruzsa-triangle finish for `BareDRCExtract` (correct shape)

This file supplies the **mathematically correct** small-doubling finish of the dependent-random-
choice extraction, replacing the *wrong-shaped* `DRCRefinedReps` residual of `_BSG_BareDRCExtract`.

## Why the old `DRCRefinedReps` route was the wrong shape

`_BSG_BareDRCExtract` derived the doubling bound from `card_diffSet_le_of_reps_ge` (`E4b`), which
needs **every** difference `d ∈ A'' - A''` to have `≥ t` representations *inside* `A'' ×ˢ A''`.
That uniform per-difference lower bound is not merely hard to supply — it is **false even for a
genuine small-doubling set**: if `#(A'' - A'') ≤ s · #A''` then the *average* difference has
`≥ #A'' / s` representations, but the extreme differences (e.g. `max A'' - min A''` for `A'' ⊆ ℤ`)
have exactly one. So `DRCRefinedReps` could never be discharged by the real DRC argument. The naive
attempt to supply it is independently machine-refuted in `_BSG_EX_E4cObstruction`
(`naiveDiffReps_REFUTED`): the factorisation `a - a' = (a - w) - (a' - w)` lands in the *difference
set*, never inside `A''`.

## The correct shape: Ruzsa on a one-sided relative difference

The real BSG finish (Tao–Vu, *Additive Combinatorics*, Thm 2.29; Gowers 1998 §6) controls the
*two-sided* difference set `A'' - A''` via the **Ruzsa triangle inequality**
`#(A'' - A'') · #B ≤ #(A'' - B) · #(A'' - B)` applied to an auxiliary set `B` (a common
neighbourhood), where DRC produces a `B` with a *small one-sided* relative difference
`#(A'' - B) ≤ s · #A''` and comparable size `#A'' ≤ s · #B`. Then

  `#(A'' - A'') · #B ≤ #(A'' - B)² ≤ (s·#A'')² = s²·#A''²`
                                  `≤ s²·(s·#A''·#B) = s³·#A''·#B`,

and cancelling `#B > 0` gives `#(A'' - A'') ≤ s³ · #A''` — a **linear** doubling bound. This is the
input the real dependent-random-choice extraction supplies; `DRCRuzsaInput` below names it, and
`bareDRCExtract_of_ruzsaInput` discharges `BareDRCExtract` from it, axiom-clean, via Mathlib's
`Finset.ruzsa_triangle_inequality_sub_sub_sub`.

## What remains open

`DRCRuzsaInput` is the genuine residual of BGK: the *existence*, from the post-averaging
neighbourhood data, of a refinement `A''` and an auxiliary set `B` with the one-sided relative
difference bound and comparable sizes. It is now the **correct shape** — the real DRC argument
produces exactly this — unlike the refuted `DRCRefinedReps`. The whole BGK chain
`DRCRuzsaInput → BareDRCExtract → BareDRC → BSGCore → BGK → δ*-floor` is unconditional modulo this
single named `Prop`.

## References

* W. T. Gowers, *A new proof of Szemerédi's theorem for AP4* (1998), §6.
* T. Tao, V. Vu, *Additive Combinatorics*, Cambridge (2006), Theorem 2.29.
-/

open Finset
open scoped BigOperators Pointwise

namespace Finset.BSG

variable {α : Type*} [AddCommGroup α] [DecidableEq α]

/-! ## The Ruzsa-triangle doubling lemma (the proven consumer) -/

/-- **E4d core — small two-sided doubling from a one-sided relative difference.** If there is an
auxiliary set `B` (nonempty) with a small one-sided relative difference `#(A'' - B) ≤ s · #A''` and
comparable size `#A'' ≤ s · #B`, then the two-sided difference set is linearly bounded:
`#(A'' - A'') ≤ s³ · #A''`.

Proof: the Ruzsa triangle inequality `#(A'' - A'') · #B ≤ #(A'' - B) · #(A'' - B)`; bound the RHS by
`(s·#A'')²`; bound `#A''² ≤ s·#A''·#B`; cancel `#B > 0`. -/
theorem card_diffSet_le_of_ruzsa (A'' B : Finset α) (s : ℕ)
    (hBne : B.Nonempty)
    (hdiff : #(A'' - B) ≤ s * #A'')
    (hsize : #A'' ≤ s * #B) :
    #(A'' - A'') ≤ s * s * s * #A'' := by
  classical
  have hBpos : 0 < #B := hBne.card_pos
  -- Ruzsa triangle: `#(A'' - A'') · #B ≤ #(A'' - B) · #(A'' - B)`.
  have hruzsa : #(A'' - A'') * #B ≤ #(A'' - B) * #(A'' - B) := by
    simpa using Finset.ruzsa_triangle_inequality_sub_sub_sub A'' B A''
  -- `#(A'' - B)² ≤ (s·#A'')²`.
  have hsq : #(A'' - B) * #(A'' - B) ≤ (s * #A'') * (s * #A'') := Nat.mul_le_mul hdiff hdiff
  -- `#A''² ≤ s·#A''·#B`.
  have haa : #A'' * #A'' ≤ s * #A'' * #B := by
    calc #A'' * #A'' ≤ #A'' * (s * #B) := by gcongr
      _ = s * #A'' * #B := by ring
  -- chain into `(s³·#A'')·#B`.
  have hchain : #(A'' - A'') * #B ≤ (s * s * s * #A'') * #B := by
    calc #(A'' - A'') * #B ≤ (s * #A'') * (s * #A'') := le_trans hruzsa hsq
      _ = (s * s) * (#A'' * #A'') := by ring
      _ ≤ (s * s) * (s * #A'' * #B) := by gcongr
      _ = (s * s * s * #A'') * #B := by ring
  exact Nat.le_of_mul_le_mul_right hchain hBpos

/-! ## The correctly-shaped residual -/

/-- **`DRCRuzsaInput` — the correctly-shaped dependent-random-choice residual.**

Given the post-averaging data of `BareDRCExtract` (a good vertex `b₀` with large left-neighbourhood
`N = leftNbhd A G b₀`, cherry-richness, edge-density), this asserts the existence of:

* a **refinement** `A'' ⊆ N` that is a constant fraction of `A` up to `K` (`C₁ · K · #A'' ≥ #A`),
* an **auxiliary set** `B` (nonempty), and
* a refinement factor `s ≤ s_C · K ^ s_c`,

with the two Ruzsa-ready facts:

* a **small one-sided relative difference** `#(A'' - B) ≤ s · #A''`, and
* **comparable sizes** `#A'' ≤ s · #B` (i.e. `#B ≥ #A'' / s`).

This is exactly what the real DRC extraction supplies and exactly what the proven
`card_diffSet_le_of_ruzsa` turns into the linear doubling bound. Unlike the refuted
`DRCRefinedReps`, this shape is consistent with genuine small-doubling sets.

**On the auxiliary set `B`.** `B` is existentially quantified, so this `Prop` is agnostic to how it
is produced. In the real Tao–Vu/Gowers argument `B` is a **fixed second popular fibre**
`leftNbhd A G b₁` (a single set), *not* a per-pair common neighbourhood — the latter varies with the
pair, has no fixed cardinality, and is exactly the object the `E4c` countermodel
(`naiveDiffReps_REFUTED`) shows cannot carry a uniform bound. The honestly-named explicit-fibre
refinement `DRCRuzsaInputFixed` (in `_BSG_EX_E4e_RuzsaShapeAudit`) pins this `B` and reduces to this
`Prop` via `drcRuzsaInput_of_fixed`. The Ruzsa triangle below needs only the *cardinality*
`#(A'' - B)`, never a per-pair count — which is why this shape is repairable where `DRCRefinedReps`
was not.

⚠️ **REFUTED — this `Prop` is FALSE as written (see `_BSG_EX_E4g_attempt0`, `drcRuzsaInput_false`).**
The clause `A'' ⊆ leftNbhd A G b₀` (apex confinement) paired with `C₁ * K * #A'' ≥ #A` is
*unsatisfiable* for constant `C₁`: a diagonal countermodel (`#A = 4K²`, every `leftNbhd b₀` a
singleton) forces `#A'' = 1`, hence `C₁ ≥ 4K`. The theorems below (`card_diffSet_le_of_ruzsa`,
`bareDRCExtract_of_ruzsaInput`) remain TRUE implications, but their premise can never be supplied,
so this is a *vacuous* reduction. The honest fix relaxes confinement to `A'' ⊆ A`:
`DRCRuzsaInputFixedRepaired` + `bareDRCExtract_of_drcRuzsaInputFixedRepaired` (both in
`_BSG_EX_E4g_attempt0`). Kept here as documented-refuted (the standard `_REFUTED` convention). -/
def DRCRuzsaInput (C₁ s_C s_c : ℕ) : Prop :=
  ∀ {α : Type} [inst : AddCommGroup α] [inst2 : DecidableEq α],
    ∀ (A : Finset α) (K : ℕ) (G : Finset (α × α)) (b₀ : α),
      0 < K → A.Nonempty → G ⊆ A ×ˢ A → b₀ ∈ A →
      #A ^ 2 ≤ 4 * K ^ 2 * #G →
      #A ^ 4 ≤ 16 * K ^ 4 * (#A * (∑ b ∈ A, rDeg A G b ^ 2)) →
      #A ≤ 4 * K ^ 2 * rDeg A G b₀ →
      ∃ (A'' B : Finset α) (s : ℕ),
        A'' ⊆ leftNbhd A G b₀ ∧ A''.Nonempty ∧ B.Nonempty ∧
        s ≤ s_C * K ^ s_c ∧
        C₁ * K * #A'' ≥ #A ∧
        #(A'' - B) ≤ s * #A'' ∧
        #A'' ≤ s * #B

/-- **`BareDRCExtract` from `DRCRuzsaInput`.** The refined set `A''` is the output `A'`. Containment
`A'' ⊆ A` follows from `A'' ⊆ leftNbhd A G b₀ ⊆ A`; nonemptiness and the size bound
`C₁ K #A'' ≥ #A` come directly from `DRCRuzsaInput`; the doubling bound is the proven
`card_diffSet_le_of_ruzsa` (Ruzsa triangle), with `s³` absorbed into the constant
`C₂ = s_C³`, `c = 3·s_c` via `(s_C · K^{s_c})³ = s_C³ · K^{3 s_c}`. -/
theorem bareDRCExtract_of_ruzsaInput {C₁ s_C s_c : ℕ} (hR : DRCRuzsaInput C₁ s_C s_c) :
    BareDRCExtract C₁ (s_C ^ 3) (3 * s_c) := by
  intro α _ _ A K G b₀ hK hA hGsub hb₀ hdense hcherry hgood
  classical
  obtain ⟨A'', B, s, hsub, hne, hBne, hsbd, hsize, hdiff, hcomp⟩ :=
    hR A K G b₀ hK hA hGsub hb₀ hdense hcherry hgood
  -- containment `A'' ⊆ A`
  have hsubA : A'' ⊆ A := hsub.trans (Finset.filter_subset _ _)
  refine ⟨A'', hsubA, hne, hsize, ?_⟩
  -- doubling: Ruzsa gives `#(A'' - A'') ≤ s³ · #A''`.
  have hdoub : #(A'' - A'') ≤ s * s * s * #A'' :=
    card_diffSet_le_of_ruzsa A'' B s hBne hdiff hcomp
  -- absorb `s³ ≤ (s_C K^{s_c})³ = s_C³ K^{3 s_c}` into the constant.
  have hscube : s * s * s ≤ s_C ^ 3 * K ^ (3 * s_c) := by
    have hpow : s ^ 3 ≤ (s_C * K ^ s_c) ^ 3 := Nat.pow_le_pow_left hsbd 3
    have he : (s_C * K ^ s_c) ^ 3 = s_C ^ 3 * K ^ (3 * s_c) := by
      rw [mul_pow, ← pow_mul, Nat.mul_comm s_c 3]
    calc s * s * s = s ^ 3 := by ring
      _ ≤ (s_C * K ^ s_c) ^ 3 := hpow
      _ = s_C ^ 3 * K ^ (3 * s_c) := he
  calc #(A'' - A'') ≤ s * s * s * #A'' := hdoub
    _ ≤ (s_C ^ 3 * K ^ (3 * s_c)) * #A'' := by gcongr
    _ = s_C ^ 3 * K ^ (3 * s_c) * #A'' := by ring

end Finset.BSG

-- Axiom audit (expected: propext, Classical.choice, Quot.sound — and NO sorryAx).
#print axioms Finset.BSG.card_diffSet_le_of_ruzsa
#print axioms Finset.BSG.bareDRCExtract_of_ruzsaInput
