/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MissingLineDefeater

/-!
# Exactness without coverability: the sup-level/pointwise separation at the Johnson radius

`MissingLineDefeater.lean` kills the obstruction-covering route at the Johnson radius:
for the repetition code `repC` over `F₂` at `δ = 1/2`, the stack `Udef` has three bad
seeds pinning the three distinct lines of `F₂²` as obstructions. This file proves the
two complementary facts that pin down **what that refutation does and does not mean**:

* **Pointwise transfer is impossible** (`no_avoiding_combiner`): the three pinned
  obstruction lines cover *all* of `F₂²` (`obstruction_lines_cover`), so no nonzero
  combiner `λ` avoids them — the [Jo26] Lemma-4.1-style argument "one combiner
  preserves every bad seed" has **no candidate** `λ` at this configuration. This is
  the first machine-checked instance where the covering mechanism is structurally
  impossible rather than merely unproven.

* **Sup-level exactness holds anyway** (`exactness_at_defeater`):
  `epsMCAG((repC)^⋈², 1/2, id) = epsMCAG(repC, 1/2, id)` — both sides equal `1`,
  witnessed by explicit saturating stacks (`Ubase = (e₃, e₂)`, all four seeds bad;
  `Uint` with rows `(0, e₃), (0, e₂)`, all four seeds bad). Probe cross-validation
  (`probe_exactness_at_defeater.py`): exactness holds at every tested configuration —
  Johnson and sub-Johnson, `F₂` and `F₃`, affine/nonzero/full seed sets — including
  the non-saturated rungs.

**The structural lesson** (`exactness_without_coverability` packages it): generator-MCA
interleaving exactness is *not* equivalent to per-stack combiner transfer. The
obstruction-covering hypothesis (`ObstructionBound`/`MissingLine`) is sufficient but
provably non-necessary; past the Johnson radius the only living route to exactness is
**global** (comparing the two suprema), not pointwise (transporting a single stack's
bad seeds along one combiner). Any future attack on the [ABF26] §5 collapse question
through this layer must therefore be sup-level from the start.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References

- Issue #357 (S2(b) refutation arc and its named follow-up probe).
- `MissingLineDefeater.lean`, `Jo26ObstructionCount.lean`, `GeneratorMCA.lean`.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.ExactnessWithoutCoverability

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code MissingLineDefeater

/-! ## Pointwise transfer is impossible: the obstruction lines cover `F₂²` -/

/-- The three pinned obstruction lines cover every combiner. -/
theorem obstruction_lines_cover (lam : Fin 2 → F2) :
    lam ∈ L01 ∨ lam ∈ L10 ∨ lam ∈ L11 := by
  have h : (lam = 0 ∨ lam = ![0, 1]) ∨ (lam = 0 ∨ lam = ![1, 0]) ∨
      (lam = 0 ∨ lam = ![1, 1]) := by
    revert lam
    decide
  exact h

/-- **No avoiding combiner exists** at the defeater configuration: every `λ` lies in
one of the three bad seeds' pinned obstructions, so the covering-lemma mechanism
("one nonzero combiner preserves all bad seeds") has no candidate. -/
theorem no_avoiding_combiner :
    ¬ ∃ lam : Fin 2 → F2, lam ≠ 0 ∧ lam ∉ L01 ∧ lam ∉ L10 ∧ lam ∉ L11 := by
  rintro ⟨lam, _, h1, h2, h3⟩
  rcases obstruction_lines_cover lam with h | h | h
  · exact h1 h
  · exact h2 h
  · exact h3 h

/-! ## The saturating stacks -/

/-- The saturating base stack: `f₀ = e₃`, `f₁ = e₂` — all four seeds are bad. -/
def Ubase : WordStack F2 (Fin 2) (Fin 4) :=
  ![![0, 0, 0, 1], ![0, 0, 1, 0]]

/-- The saturating interleaved stack: rows `(0, e₃)` and `(0, e₂)`. -/
def Uint : Fin 2 → Fin 4 → Fin 2 → F2 :=
  ![![![0, 0], ![0, 0], ![0, 0], ![0, 1]],
    ![![0, 0], ![0, 0], ![0, 1], ![0, 0]]]

/-! ## Base events: all four seeds bad for `Ubase` -/

/-- Base event builder: a size-2 witness, a constant explaining codeword, and a
decidable non-joint core. -/
theorem base_event_of (c : Fin 2 → F2) (T : Finset (Fin 4)) (a : F2)
    (hcard : T.card = 2)
    (hag : ∀ i ∈ T, a = ∑ j, c j • Ubase j i)
    (hno : ¬ ∃ b : Fin 2 → F2, ∀ i ∈ T, ∀ j, Ubase j i = b j) :
    mcaEventG (repC : Set (Fin 4 → F2)) (1/2) Ubase c := by
  refine ⟨T, card_clause_of_two hcard, ⟨fun _ => a, ⟨a, fun _ => rfl⟩, hag⟩, ?_⟩
  rintro ⟨cs, hcs, hagj⟩
  refine hno ⟨fun j => cs j 0, fun i hi j => ?_⟩
  obtain ⟨b, hb⟩ := (mem_repC _).mp (hcs j)
  have h : cs j i = Ubase j i := hagj i hi j
  show Ubase j i = cs j 0
  rw [← h, hb i, hb 0]

theorem base_event_00 :
    mcaEventG (repC : Set (Fin 4 → F2)) (1/2) Ubase (![0, 0] : Fin 2 → F2) :=
  base_event_of ![0, 0] {2, 3} 0 (by decide) (by decide) (by decide)

theorem base_event_01 :
    mcaEventG (repC : Set (Fin 4 → F2)) (1/2) Ubase (![0, 1] : Fin 2 → F2) :=
  base_event_of ![0, 1] {1, 3} 0 (by decide) (by decide) (by decide)

theorem base_event_10 :
    mcaEventG (repC : Set (Fin 4 → F2)) (1/2) Ubase (![1, 0] : Fin 2 → F2) :=
  base_event_of ![1, 0] {1, 2} 0 (by decide) (by decide) (by decide)

theorem base_event_11 :
    mcaEventG (repC : Set (Fin 4 → F2)) (1/2) Ubase (![1, 1] : Fin 2 → F2) :=
  base_event_of ![1, 1] {2, 3} 1 (by decide) (by decide) (by decide)

/-- Every seed is bad for the base stack. -/
theorem base_all_bad (w : Fin 2 → F2) :
    mcaEventG (repC : Set (Fin 4 → F2)) (1/2) Ubase w := by
  have h : w = ![0, 0] ∨ w = ![0, 1] ∨ w = ![1, 0] ∨ w = ![1, 1] := by
    revert w
    decide
  rcases h with rfl | rfl | rfl | rfl
  · exact base_event_00
  · exact base_event_01
  · exact base_event_10
  · exact base_event_11

/-! ## Interleaved events: all four seeds bad for `Uint` -/

/-- Interleaved event builder for `Uint` (mirrors
`MissingLineDefeater.event_of`, which is `Udef`-specific). -/
theorem inter_event_of (c : Fin 2 → F2) (T : Finset (Fin 4)) (a : Fin 2 → F2)
    (hcard : T.card = 2)
    (hag : ∀ i ∈ T, (fun (_ : Fin 4) => a) i = ∑ j, c j • Uint j i)
    (hno : ¬ ∃ b : Fin 2 → Fin 2 → F2, ∀ i ∈ T, ∀ j k, Uint j i k = b j k) :
    mcaEventG ((repC : Set (Fin 4 → F2))^⋈ (Fin 2)) (1/2) Uint c := by
  refine ⟨T, card_clause_of_two hcard,
    ⟨fun _ => a, (mem_inter _).mpr fun k => ⟨a k, fun _ => rfl⟩, hag⟩, ?_⟩
  rintro ⟨cs, hcs, hagj⟩
  refine hno ⟨fun j k => cs j 0 k, fun i hi j k => ?_⟩
  obtain ⟨b, hb⟩ := (mem_inter (cs j)).mp (hcs j) k
  have h : cs j i k = Uint j i k := congrFun (hagj i hi j) k
  show Uint j i k = cs j 0 k
  rw [← h, hb i, hb 0]

theorem inter_event_00 :
    mcaEventG ((repC : Set (Fin 4 → F2))^⋈ (Fin 2)) (1/2) Uint
      (![0, 0] : Fin 2 → F2) :=
  inter_event_of ![0, 0] {2, 3} ![0, 0] (by decide) (by decide) (by decide)

theorem inter_event_01 :
    mcaEventG ((repC : Set (Fin 4 → F2))^⋈ (Fin 2)) (1/2) Uint
      (![0, 1] : Fin 2 → F2) :=
  inter_event_of ![0, 1] {1, 3} ![0, 0] (by decide) (by decide) (by decide)

theorem inter_event_10 :
    mcaEventG ((repC : Set (Fin 4 → F2))^⋈ (Fin 2)) (1/2) Uint
      (![1, 0] : Fin 2 → F2) :=
  inter_event_of ![1, 0] {1, 2} ![0, 0] (by decide) (by decide) (by decide)

theorem inter_event_11 :
    mcaEventG ((repC : Set (Fin 4 → F2))^⋈ (Fin 2)) (1/2) Uint
      (![1, 1] : Fin 2 → F2) :=
  inter_event_of ![1, 1] {2, 3} ![0, 1] (by decide) (by decide) (by decide)

/-- Every seed is bad for the interleaved stack. -/
theorem inter_all_bad (w : Fin 2 → F2) :
    mcaEventG ((repC : Set (Fin 4 → F2))^⋈ (Fin 2)) (1/2) Uint w := by
  have h : w = ![0, 0] ∨ w = ![0, 1] ∨ w = ![1, 0] ∨ w = ![1, 1] := by
    revert w
    decide
  rcases h with rfl | rfl | rfl | rfl
  · exact inter_event_00
  · exact inter_event_01
  · exact inter_event_10
  · exact inter_event_11

/-! ## The two suprema both equal `1` -/

open Classical in
/-- A uniform-seed probability over an everywhere-true event is `1`. -/
theorem pr_eq_one_of_forall {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (P : Ω → Prop) (h : ∀ ω, P ω) :
    Pr_{let ω ← $ᵖ Ω}[P ω] = 1 := by
  rw [prob_uniform_eq_card_filter_div_card,
    Finset.filter_true_of_mem (fun ω _ => h ω), Finset.card_univ]
  rw [ENNReal.coe_natCast]
  exact ENNReal.div_self (by
      exact_mod_cast Fintype.card_ne_zero) (by simp)

open Classical in
/-- The base generator-MCA error saturates: `epsMCAG(repC, 1/2, id) = 1`. -/
theorem epsMCAG_base_eq_one :
    epsMCAG (A := F2) (repC : Set (Fin 4 → F2)) (1/2)
      (id : (Fin 2 → F2) → Fin 2 → F2) = 1 := by
  refine le_antisymm (iSup_le fun f => Pr_le_one _ _) ?_
  refine le_trans ?_ (le_iSup (fun f : WordStack F2 (Fin 2) (Fin 4) =>
    Pr_{let ω ← $ᵖ (Fin 2 → F2)}[mcaEventG (repC : Set (Fin 4 → F2)) (1/2) f
      (id ω)]) Ubase)
  exact le_of_eq (pr_eq_one_of_forall _ (fun ω => base_all_bad ω)).symm

open Classical in
/-- The interleaved generator-MCA error saturates: `epsMCAG(repC^⋈², 1/2, id) = 1`. -/
theorem epsMCAG_inter_eq_one :
    epsMCAG (A := Fin 2 → F2) ((repC : Set (Fin 4 → F2))^⋈ (Fin 2)) (1/2)
      (id : (Fin 2 → F2) → Fin 2 → F2) = 1 := by
  refine le_antisymm (iSup_le fun f => Pr_le_one _ _) ?_
  refine le_trans ?_ (le_iSup (fun f : WordStack (Fin 2 → F2) (Fin 2) (Fin 4) =>
    Pr_{let ω ← $ᵖ (Fin 2 → F2)}[mcaEventG ((repC : Set (Fin 4 → F2))^⋈ (Fin 2))
      (1/2) f (id ω)]) Uint)
  exact le_of_eq (pr_eq_one_of_forall _ (fun ω => inter_all_bad ω)).symm

/-! ## The separation -/

/-- **Sup-level exactness at the defeater configuration.** -/
theorem exactness_at_defeater :
    epsMCAG (A := Fin 2 → F2) ((repC : Set (Fin 4 → F2))^⋈ (Fin 2)) (1/2)
      (id : (Fin 2 → F2) → Fin 2 → F2)
      = epsMCAG (A := F2) (repC : Set (Fin 4 → F2)) (1/2)
          (id : (Fin 2 → F2) → Fin 2 → F2) := by
  rw [epsMCAG_base_eq_one, epsMCAG_inter_eq_one]

/-- **Exactness without coverability** — the packaged separation: at the `F₂`
Johnson-radius defeater, generator-MCA interleaving exactness holds at the sup level
while the obstruction-covering route (`MissingLine`) is false and the pointwise
combiner mechanism has no candidate. The covering hypothesis is sufficient but
provably non-necessary. -/
theorem exactness_without_coverability :
    (epsMCAG (A := Fin 2 → F2) ((repC : Set (Fin 4 → F2))^⋈ (Fin 2)) (1/2)
        (id : (Fin 2 → F2) → Fin 2 → F2)
      = epsMCAG (A := F2) (repC : Set (Fin 4 → F2)) (1/2)
          (id : (Fin 2 → F2) → Fin 2 → F2))
    ∧ ¬ Jo26Obstruction.MissingLine repC (1/2)
        (id : (Fin 2 → F2) → Fin 2 → F2) Udef
    ∧ ¬ ∃ lam : Fin 2 → F2, lam ≠ 0 ∧ lam ∉ L01 ∧ lam ∉ L10 ∧ lam ∉ L11 :=
  ⟨exactness_at_defeater, missingLine_defeated, no_avoiding_combiner⟩

/-! ## Source audit -/

#print axioms no_avoiding_combiner
#print axioms exactness_at_defeater
#print axioms exactness_without_coverability

end ProximityGap.ExactnessWithoutCoverability
