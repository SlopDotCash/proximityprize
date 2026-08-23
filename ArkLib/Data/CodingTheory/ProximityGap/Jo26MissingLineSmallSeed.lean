/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Jo26ObstructionCount

/-!
# S2(b) positive half (#357): `MissingLine` holds for every small-seed generator

The cocycle refutation (`Jo26MissingLineGenerousRefuted.lean`) kills the generous form of
the missing-line hypothesis: a single stack *can* realize all `q+1` lines of `F²` as
obstruction subspaces across its witness sets. This file proves the **positive half** that
survives — and pins exactly where the open part of S2(b) now lives:

* `missingLine_of_card_le` — **`MissingLine` holds whenever `|Ω| ≤ q`**, for trivial but
  decisive counting reasons: each *bad seed* contributes (at most) one obstruction subspace
  via any chosen witness, properness is automatic (`jointStackSubmodule_ne_top` — the
  witness's no-joint-agreement clause), and a family of `≤ |Ω| ≤ q` subspaces covers all
  bad seeds. The generous form quantified over **all witness sets**; the true form
  quantifies over **bad seeds** — that order-of-quantifiers difference is the entire
  content.
* `epsMCAG_interleaved_eq_of_card_le` — the corollary through the S2(a) engine: generator
  MCA interleaving is **exact** (`ε_G(C^⋈2) = ε_G(C)`, no `A(q,s)` factor) for *every*
  generator with at most `q` seeds. This recovers the seed-size regime of [Jo26]
  Theorem 4.4 by a purely structural route (obstruction counting + the covering lemma),
  independent of the paper's averaging argument — and in particular re-derives affine-line
  exactness (`Ω = F`).

**Where S2(b) now stands.** Open exactly for `|Ω| > q` (e.g. power/product generators with
seed spaces `F^s`). There the cocycle construction supplies `q+1` candidate obstruction
lines, and the question is whether `q+1` *bad seeds* can be forced onto pairwise-distinct
lines — forced meaning *every* witness of each seed lands on its line. The affine design
class cannot do this (the in-tree proportionality trap); the cocycle class is unexplored.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- Issue #357 (the δ* campaign; hypothesis S2(b)); [Jo26] ePrint 2026/891 §3–4.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset NNReal Code
open scoped ProbabilityTheory BigOperators

namespace ProximityGap.Jo26MissingLineSmallSeed

open ProximityGap ProximityGap.Jo26Obstruction

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- **`MissingLine` holds for every generator with at most `q` seeds.** Each bad seed
donates one obstruction subspace through any chosen witness; properness is the witness's
own no-joint-agreement clause; `≤ |Ω| ≤ q` subspaces cover everything. -/
theorem missingLine_of_card_le (C : Submodule F (ι → A)) (δ : ℝ≥0) {l : ℕ}
    {Ω : Type} [Fintype Ω] [Nonempty Ω] (G : Ω → Fin l → F)
    (hΩ : Fintype.card Ω ≤ Fintype.card F)
    (U : Fin l → ι → Fin 2 → A) :
    MissingLine C δ G U := by
  -- choose one witness per bad seed
  let T : Ω → Finset ι := fun ω =>
    if h : mcaEventG ((C : Set (ι → A))^⋈ (Fin 2)) δ U (G ω) then h.choose else ∅
  have hTw : ∀ ω, mcaEventG ((C : Set (ι → A))^⋈ (Fin 2)) δ U (G ω) →
      mcaWitnessG ((C : Set (ι → A))^⋈ (Fin 2)) δ U (G ω) (T ω) := by
    intro ω hev
    simp only [T, dif_pos hev]
    exact hev.choose_spec
  refine ⟨(Finset.univ.filter
      (fun ω => mcaEventG ((C : Set (ι → A))^⋈ (Fin 2)) δ U (G ω))).image
      (fun ω => jointStackSubmodule C (T ω) U), ?_, ?_, ?_⟩
  · -- cardinality: ≤ #bad seeds ≤ |Ω| ≤ q
    calc ((Finset.univ.filter (fun ω =>
          mcaEventG ((C : Set (ι → A))^⋈ (Fin 2)) δ U (G ω))).image
          (fun ω => jointStackSubmodule C (T ω) U)).card
        ≤ (Finset.univ.filter (fun ω =>
          mcaEventG ((C : Set (ι → A))^⋈ (Fin 2)) δ U (G ω))).card :=
          Finset.card_image_le
      _ ≤ (Finset.univ : Finset Ω).card := Finset.card_filter_le _ _
      _ = Fintype.card Ω := Finset.card_univ
      _ ≤ Fintype.card F := hΩ
  · -- properness: each chosen witness's no-joint-agreement clause
    intro K hK
    rw [Finset.mem_image] at hK
    obtain ⟨ω, hωmem, rfl⟩ := hK
    rw [Finset.mem_filter] at hωmem
    exact jointStackSubmodule_ne_top C U (hTw ω hωmem.2).2.2
  · -- coverage: each bad seed via its chosen witness
    intro ω hev
    exact ⟨T ω, hTw ω hev,
      Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hev⟩)⟩

open Classical in
/-- **Interleaving exactness for every small-seed generator** (`|Ω| ≤ q`): the [Jo26]
Theorem 4.2 factor `A(q,s)` vanishes, by the obstruction-counting route. Recovers the
seed-size regime of [Jo26] Theorem 4.4 structurally, and affine-line exactness at
`Ω = F`. -/
theorem epsMCAG_interleaved_eq_of_card_le (C : Submodule F (ι → A)) (δ : ℝ≥0) {l : ℕ}
    {Ω : Type} [Fintype Ω] [Nonempty Ω] (G : Ω → Fin l → F)
    (hΩ : Fintype.card Ω ≤ Fintype.card F) :
    epsMCAG (A := Fin 2 → A) ((C : Set (ι → A))^⋈ (Fin 2)) δ G
      = epsMCAG (A := A) (C : Set (ι → A)) δ G :=
  epsMCAG_interleaved_eq_of_missingLine C δ G (missingLine_of_card_le C δ G hΩ)

/-! ## Source audit -/

#print axioms missingLine_of_card_le
#print axioms epsMCAG_interleaved_eq_of_card_le

end ProximityGap.Jo26MissingLineSmallSeed
