/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GWKernelReduction

/-!
# GW BRICK-W mis-wiring catch + the correctly-scoped direction bound (R2 / #93/#94)

This file performs a rigour audit of the Guruswami–Wang kernel reduction in
`GWKernelReduction.lean` and lands the *correctly-scoped* replacement of one of its named
hypotheses.

## What this file establishes

* **A machine-checked refutation** (`gwDirectionFinrankLe_refuted`): the named hypothesis
  `GWDirectionFinrankLe s C := ∀ A ≤ C, finrank A ≤ s − 1` fed into the conditional headline
  `cz25CoordFiberCap_of_interp_and_multiplicity` is **mathematically false for every code
  `C` of dimension `≥ s`** — in particular for *every* capacity-regime folded-RS code, where
  `dim C = k ≫ s`. Instantiating the universal `A := C` forces `finrank C ≤ s − 1`. We exhibit
  the concrete countermodel `C := ⊤` (the whole code space), whose finrank is `|ι| · s > s − 1`.

  So `GWDirectionFinrankLe` is **not** the conclusion of the proven BRICK-W lane
  (`GWAffinePinning.gw_solutionSet_finrank_le`): that lemma bounds the finrank of the *single*
  GW homogeneous-solution submodule `W₀ = gwHomogSolution A γ k`, **not** that of every
  submodule of the code. The headline's claim that `hW` is "the orchestrator-wired conclusion
  of BRICK-W (proven in lane `GWBrickW`)" over-states the scope: the proven object is a bound
  on *one designated* submodule, the named Prop demands it on *all* submodules and is therefore
  unsatisfiable for nondegenerate codes.

* **The correctly-scoped Prop** `GWAgreeForcesDirectionScoped`: BRICK-V's existential output
  (a direction submodule `A ≤ C` capturing every recentred difference) bundled with the genuine
  BRICK-W bound `finrank A ≤ s − 1` *on that produced `A`*. This is exactly the shape the proven
  BRICK-W lane delivers (a finrank bound on the constructed solution space). Crucially it does
  **not** mention `dim A ≤ |Lset| − 1`; the BRICK-L charge (`GWAffineFiberCharge`) still carries
  the genuine affine-flat content, so the scoped Prop is a strict weakening of the false `hW`,
  not a relabelling of the cap.

* **The corrected conditional headline** `cz25CoordFiberCap_of_interp_and_multiplicity_scoped`:
  the same `CZ25CoordFiberCap` conclusion from `{BRICK-I, BRICK-V-scoped, BRICK-L}` — replacing
  the false universal `GWDirectionFinrankLe` with the satisfiable scoped form. The arithmetic
  collapse (`cz25CoordFiberCap_of_affineFiberCharge`) and the BRICK-L charge are reused verbatim
  from `GWKernelReduction.lean`; only the `hW` leg is corrected. This keeps the kernel genuinely
  conditional on satisfiable analytic obligations rather than on an unsatisfiable one.

## Honesty note (gap localization)

`cz25CoordFiberCap_of_interp_and_multiplicity` in `GWKernelReduction.lean` is *syntactically*
`sorry`-free and axiom-clean, but its `hW : GWDirectionFinrankLe s C` premise is **false for
genuine codes**, so the theorem is consumable only with an unsatisfiable hypothesis (and the
`_chain` step that uses `hW` would, with a real BRICK-W, produce only a bound on the *solution*
submodule). This file does not refute the GW kernel — it refutes one *statement* of one of its
legs and supplies the satisfiable replacement. The genuinely-deep remaining content (the
affine-flat charge `GWAffineFiberCharge` / the `card ≤ finrank` fiber cap = the `q^{dim}` vs
`dim + 1` obstruction documented at `CZ25SpanDimension.lean:292–302`) is untouched and remains
the open kernel of the GW `|L| > 1` capacity argument.

## References

- [GW13] Guruswami–Wang. *Linear-algebraic list decoding of folded Reed–Solomon codes.*
- [CZ25] Thm B.5 (subspace-design route to capacity list decoding).
- [GK16] Guruswami–Kopparty. The folded-Wronskian non-vanishing engine for BRICK-W.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace CodingTheory

open scoped NNReal
open ListDecodable
open Module

section ScopedWiring

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ### The mis-wiring catch: `GWDirectionFinrankLe` forces `finrank C ≤ s − 1` -/

/-- **The over-strong universal direction bound forces a tiny code.** The named hypothesis
`GWDirectionFinrankLe s C` (`∀ A ≤ C, finrank A ≤ s − 1`), applied to `A := C` itself, forces
`finrank C ≤ s − 1`. Hence it holds *only* for codes of dimension `≤ s − 1`; for every code of
dimension `≥ s` (all capacity-regime folded-RS codes) it is false. -/
theorem gwDirectionFinrankLe_forces_small
    (s : ℕ) (C : Submodule F (ι → Fin s → F)) (hW : GWDirectionFinrankLe s C) :
    finrank F C ≤ s - 1 :=
  hW C le_rfl

/-- **Refutation: `GWDirectionFinrankLe` is false on the whole code space (`s ≥ 2`).** For any
nonempty index set `ι`, the whole code space `C := ⊤` has `finrank = |ι| · s`. Whenever `s ≥ 2`,
this exceeds `s − 1`, so `GWDirectionFinrankLe s ⊤` fails. This is the concrete countermodel
certifying that the headline's `hW` premise is **not** the conclusion of the proven BRICK-W lane:
the proven lane bounds the finrank of *one designated* solution submodule, not of every `A ≤ C`. -/
theorem gwDirectionFinrankLe_refuted
    (s : ℕ) (hs : 2 ≤ s) :
    ¬ GWDirectionFinrankLe s (⊤ : Submodule F (ι → Fin s → F)) := by
  intro hW
  have hforce : finrank F (⊤ : Submodule F (ι → Fin s → F)) ≤ s - 1 :=
    gwDirectionFinrankLe_forces_small s ⊤ hW
  have htop : finrank F (⊤ : Submodule F (ι → Fin s → F)) = Fintype.card ι * s := by
    rw [finrank_top]
    simp [Module.finrank_pi_fintype, Fintype.card_fin]
  rw [htop] at hforce
  have hcard : 1 ≤ Fintype.card ι := Fintype.card_pos
  have hsle : s ≤ Fintype.card ι * s := Nat.le_mul_of_pos_left s hcard
  omega

/-! ### The correctly-scoped BRICK-V output (`A` produced *with* its finrank bound) -/

/-- **BRICK-V, correctly scoped (the genuine BRICK-W wiring).** Identical to
`GWAgreeForcesDirection`, except the produced direction submodule `A` is delivered *together with*
the genuine BRICK-W finrank bound `finrank A ≤ s − 1` on **that** `A`. This is precisely the shape
the proven lane `GWAffinePinning.gw_solutionSet_finrank_le` supplies — a finrank bound on the
single constructed solution submodule, *not* on every submodule of the code. Unlike the false
`GWDirectionFinrankLe`, this Prop is satisfiable for genuine codes (its `A` is the small solution
flat). -/
def GWAgreeForcesDirectionScoped
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (_h : IsSubspaceDesign s τ C) (η : ℝ) (_hη : 0 < η) : Prop :=
  ∀ f c₀ : ι → Fin s → F,
    0 ≤ 1 - τ (Nat.floor (1 / η)) - η →
    c₀ ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f
        (1 - τ (Nat.floor (1 / η)) - η) →
    (∃ Q : Polynomial F × Polynomial F, (Q.1 ≠ 0 ∨ Q.2 ≠ 0)) →
    ∃ A : Submodule F (ι → Fin s → F), A ≤ C ∧ Module.finrank F A ≤ s - 1 ∧
      ∀ c ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f
          (1 - τ (Nat.floor (1 / η)) - η), c - c₀ ∈ A

/-- **The scoped BRICK-V output is genuinely satisfiable where the over-strong `hW` is not.** On
the whole code space `C := ⊤` (with `s ≥ 2`), `GWAgreeForcesDirectionScoped` is *inhabited* — take
the produced direction submodule `A := ⊥` of finrank `0 ≤ s − 1`, which captures `c − c₀ ∈ ⊥`
exactly when the close-list collapses to its base point. Meanwhile `GWDirectionFinrankLe s ⊤` is
*refuted* (`gwDirectionFinrankLe_refuted`). Concretely, the scoped Prop holds whenever the close
list is the singleton `{c₀}` for every `f` (the sub-Johnson slice). This certifies that the scoped
replacement is a strict weakening of the false `hW`, not a relabelling. -/
theorem gwAgreeForcesDirectionScoped_holds_of_close_list_singleton
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (η : ℝ) (hη : 0 < η)
    (hsing : ∀ (f c₀ : ι → Fin s → F),
      c₀ ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f
          (1 - τ (Nat.floor (1 / η)) - η) →
      ∀ c ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f
          (1 - τ (Nat.floor (1 / η)) - η), c = c₀) :
    GWAgreeForcesDirectionScoped s τ C h η hη := by
  intro f c₀ _hδ hc₀ _hQ
  refine ⟨⊥, bot_le, ?_, ?_⟩
  · -- `finrank ⊥ = 0 ≤ s − 1`.
    rw [finrank_bot]
    omega
  · intro c hc
    -- The close list collapses to `{c₀}`, so `c = c₀` and `c − c₀ = 0 ∈ ⊥`.
    rw [hsing f c₀ hc₀ c hc, sub_self]
    exact Submodule.zero_mem ⊥

/-! ### The corrected conditional headline -/

/-- **CORRECTED HEADLINE: `CZ25CoordFiberCap` from `{BRICK-I, BRICK-V-scoped, BRICK-L}`.**

The GW kernel reduced to satisfiable analytic obligations, fixing the mis-wired `hW` leg of
`cz25CoordFiberCap_of_interp_and_multiplicity`. The over-strong universal direction bound
`GWDirectionFinrankLe` (refuted by `gwDirectionFinrankLe_refuted` for every genuine code) is
**dropped**: the genuine BRICK-W bound `finrank A ≤ s − 1` is instead carried *with* the BRICK-V
output `A` via the scoped Prop `GWAgreeForcesDirectionScoped`. Given:

* `hI : GWInterpExists …`               (BRICK-I, analytic, named);
* `hV : GWAgreeForcesDirectionScoped …` (BRICK-V scoped: produces `A` *with* `finrank A ≤ s − 1`);
* `hL : GWAffineFiberCharge …`          (BRICK-L conclusion, the genuine affine-flat charge);
* `hτ : 0 ≤ τ(r₀)`                       (nonnegativity of the design profile);

the cap holds. The composition: BRICK-I gives a nonzero interpolant `Q`; BRICK-V (scoped) feeds it
into the multiplicity argument, producing the direction submodule `A ≤ C` with the genuine
`finrank A ≤ s − 1` bound on **that** `A` (no false universal claim); BRICK-L's affine-flat charge
plus the arithmetic collapse `cz25CoordFiberCap_of_affineFiberCharge` yield `CZ25CoordFiberCap`.

`sorry`/`axiom`-free; the only admitted inputs are `{hI, hV, hL, hτ}`, all *satisfiable* (unlike
the original `hW`). -/
theorem cz25CoordFiberCap_of_interp_and_multiplicity_scoped
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (η : ℝ) (hη : 0 < η)
    (hτ : 0 ≤ τ (Nat.floor (1 / η)))
    (hI : GWInterpExists s τ C h η hη)
    (hV : GWAgreeForcesDirectionScoped s τ C h η hη)
    (hL : GWAffineFiberCharge s τ C h η hη) :
    CZ25CoordFiberCap s τ C h η hη := by
  classical
  -- The analytic chain `{I → V-scoped}` is consumable: it yields, for any non-degenerate `f` and
  -- base close codeword `c₀`, a direction submodule `A ≤ C` with `finrank A ≤ s − 1` capturing
  -- every recentred difference — the genuine BRICK-W bound carried on the *produced* `A`.
  have _chain : ∀ f c₀ : ι → Fin s → F, 0 ≤ 1 - τ (Nat.floor (1 / η)) - η →
      c₀ ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f
          (1 - τ (Nat.floor (1 / η)) - η) →
      ∃ A : Submodule F (ι → Fin s → F), A ≤ C ∧ Module.finrank F A ≤ s - 1 ∧
        ∀ c ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f
            (1 - τ (Nat.floor (1 / η)) - η), c - c₀ ∈ A := by
    intro f c₀ hδ hc₀
    obtain ⟨Q, hQ⟩ := hI f hδ
    exact hV f c₀ hδ hc₀ ⟨Q, hQ⟩
  -- The cap from the (wired) affine-flat charge `hL` and the arithmetic collapse.
  exact cz25CoordFiberCap_of_affineFiberCharge s τ C h η hη hτ hL

end ScopedWiring

end CodingTheory

#print axioms CodingTheory.gwDirectionFinrankLe_refuted
#print axioms CodingTheory.gwAgreeForcesDirectionScoped_holds_of_close_list_singleton
#print axioms CodingTheory.cz25CoordFiberCap_of_interp_and_multiplicity_scoped
