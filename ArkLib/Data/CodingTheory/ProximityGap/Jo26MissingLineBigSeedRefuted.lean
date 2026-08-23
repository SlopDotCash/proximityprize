/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Jo26MissingLineSmallSeed

/-!
# S2(b) endgame (#357): the constrained `MissingLine` is FALSE for `|Ω| > q` — seed forcing

`Jo26MissingLineSmallSeed.lean` proved `MissingLine` for every generator with `|Ω| ≤ q`.
This file settles the other half: **for `|Ω| > q` the hypothesis is false** — there are
stacks whose bad seeds are *forced* onto more than `q` pairwise-distinct obstruction
subspaces, so no admissible family covers them. With this, S2(b) is fully resolved:

* `|Ω| ≤ q` — `MissingLine` **holds** (trivial counting; `missingLine_of_card_le`);
* `|Ω| > q` — `MissingLine` **fails** (this file), hence `ObstructionBound` fails, and the
  S2(a) obstruction-counting route to interleaving exactness is *not* available for
  large-seed generators. (Exactness itself is not refuted here — at this toy instance both
  sides saturate; whether exactness genuinely fails for some large-seed generator remains
  the open residue, now cleanly separated from the obstruction-family geometry.)

**The instance** (found by exhaustive search over all `2^16` stacks at `F₂, n = 4`,
constants code, `δ = 1/2`, seed space `Ω = F₂²`, generator `G = id` — 9,216 of 65,536
stacks refute; this is the first, with witness structure verified exactly):

  row 0 columns: `(0,0,0,1)` and `(0,0,1,0)` · row 1 columns: `(0,0,1,0)` and `(0,1,0,1)`.

The three nonzero seeds are bad and **forced**: every admissible witness `T` of seed `ω`
has `jointStackSubmodule C T U` equal to one fixed line depending on `ω` —
`(0,1) ↦ span(0,1)` (witness `{1,3}`), `(1,0) ↦ span(1,0)` (witness `{0,1}`),
`(1,1) ↦ span(1,1)` (witness `{2,3}`). Three distinct proper subspaces must lie in any
covering family, but `|Ls| ≤ q = 2`. The forcing is machine-checked by `decide` over all
16 witness sets (`forced01/forced10/forced11`).

This complements the cocycle refutation of the *generous* form
(`Jo26MissingLineGenerousRefuted.lean`): there the issue was the obstruction-family
geometry (all `q+1` lines realizable); here the *constrained* form dies because seed
badness can pin each seed to its own line. Together: the order of quantifiers (`≤ q` seeds
vs `> q` seeds) is the exact boundary of the missing-line phenomenon.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- Issue #357 (the δ* campaign; hypothesis S2(b) — resolution); [Jo26] ePrint 2026/891.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset NNReal Code
open scoped ProbabilityTheory BigOperators

namespace ProximityGap.Jo26MissingLineBigSeedRefuted

open ProximityGap ProximityGap.Jo26Obstruction

abbrev F2 := ZMod 2

/-- The constants code over `F₂` on 4 points. -/
def constC2 : Submodule F2 (Fin 4 → F2) where
  carrier := {w | ∃ c : F2, ∀ i, w i = c}
  zero_mem' := ⟨0, fun _ => rfl⟩
  add_mem' := by
    rintro w w' ⟨c, hc⟩ ⟨c', hc'⟩
    exact ⟨c + c', fun i => by show w i + w' i = c + c'; rw [hc i, hc' i]⟩
  smul_mem' := by
    rintro a w ⟨c, hc⟩
    exact ⟨a * c, fun i => by show a * w i = a * c; rw [hc i]⟩

/-- The columns of the refuting stack: `colsU j k` is the `k`-th interleaved column of
row `j`. -/
def colsU : Fin 2 → Fin 2 → Fin 4 → F2 :=
  ![![![0, 0, 0, 1], ![0, 0, 1, 0]], ![![0, 0, 1, 0], ![0, 1, 0, 1]]]

/-- The refuting stack (`l = 2` rows of the 2-interleaved code). -/
def Uref : Fin 2 → Fin 4 → Fin 2 → F2 := fun j i k => colsU j k i

/-- Decidable "constant on `T`" predicate. -/
def constOn (w : Fin 4 → F2) (T : Finset (Fin 4)) : Prop := ∃ c : F2, ∀ i ∈ T, w i = c

instance (w : Fin 4 → F2) (T : Finset (Fin 4)) : Decidable (constOn w T) := by
  unfold constOn; infer_instance

/-- The decidable witness predicate mirroring `mcaWitnessG` at `δ = 1/2`. -/
def witD (ω : Fin 2 → F2) (T : Finset (Fin 4)) : Prop :=
  2 ≤ T.card ∧
  (∀ k : Fin 2, constOn (fun i => ω 0 * colsU 0 k i + ω 1 * colsU 1 k i) T) ∧
  ¬ (∀ j k : Fin 2, constOn (colsU j k) T)

instance (ω : Fin 2 → F2) (T : Finset (Fin 4)) : Decidable (witD ω T) := by
  unfold witD; infer_instance

/-- The decidable obstruction-membership predicate mirroring `jointStackSubmodule`. -/
def inK2 (T : Finset (Fin 4)) (lam : Fin 2 → F2) : Prop :=
  ∀ j : Fin 2, constOn (fun i => lam 0 * colsU j 0 i + lam 1 * colsU j 1 i) T

instance (T : Finset (Fin 4)) (lam : Fin 2 → F2) : Decidable (inK2 T lam) := by
  unfold inK2; infer_instance

/-! ### The bridges -/

/-- Row-combination reduction: `∑ k, lam k • Uref j i k` is the two-term column mix. -/
theorem sum_comb (lam : Fin 2 → F2) (j : Fin 2) (i : Fin 4) :
    (∑ k, lam k • Uref j i k) = lam 0 * colsU j 0 i + lam 1 * colsU j 1 i := by
  rw [Fin.sum_univ_two]
  simp [Uref, smul_eq_mul]

/-- Membership in the obstruction subspace is `inK2`. -/
theorem mem_jSS_iff_inK2 (T : Finset (Fin 4)) (lam : Fin 2 → F2) :
    lam ∈ jointStackSubmodule constC2 T Uref ↔ inK2 T lam := by
  constructor
  · rintro ⟨cs, hcs, hag⟩
    intro j
    obtain ⟨c, hc⟩ := hcs j
    refine ⟨c, fun i hi => ?_⟩
    have h : cs j i = ∑ k, lam k • Uref j i k := hag i hi j
    show lam 0 * colsU j 0 i + lam 1 * colsU j 1 i = c
    rw [← sum_comb, ← h]
    exact hc i
  · intro h
    choose cs hcs using h
    refine ⟨fun j _ => cs j, fun j => ⟨cs j, fun _ => rfl⟩, fun i hi j => ?_⟩
    show cs j = ∑ k, lam k • Uref j i k
    rw [sum_comb]
    exact (hcs j i hi).symm

/-- Seed-combination reduction: column `k` of `∑ j, ω j • Uref j i`. -/
theorem seed_comb (ω : Fin 2 → F2) (i : Fin 4) (k : Fin 2) :
    (∑ j, ω j • Uref j i) k = ω 0 * colsU 0 k i + ω 1 * colsU 1 k i := by
  rw [Fin.sum_univ_two]
  simp [Uref, smul_eq_mul]

/-- The radius clause at `δ = 1/2`, `n = 4`. -/
theorem card_clause_iff (T : Finset (Fin 4)) :
    ((T.card : ℝ≥0) ≥ ((1 : ℝ≥0) - 1/2) * (Fintype.card (Fin 4) : ℝ≥0)) ↔ 2 ≤ T.card := by
  have hhalf : (1 : ℝ≥0) - 1/2 = 1/2 := by
    apply NNReal.coe_injective
    rw [NNReal.coe_sub (by norm_num)]
    norm_num
  rw [hhalf, Fintype.card_fin]
  constructor
  · intro h
    have h2 : (2 : ℝ≥0) ≤ (T.card : ℝ≥0) := by
      calc (2 : ℝ≥0) = (1/2 : ℝ≥0) * (4 : ℕ) := by push_cast; norm_num
        _ ≤ (T.card : ℝ≥0) := h
    exact_mod_cast h2
  · intro h
    calc ((1 : ℝ≥0)/2) * ((4 : ℕ) : ℝ≥0) = 2 := by push_cast; norm_num
      _ ≤ (T.card : ℝ≥0) := by exact_mod_cast h

/-- The witness bridge: `mcaWitnessG` for the interleaved constants code is `witD`. -/
theorem mcaWitnessG_iff_witD (ω : Fin 2 → F2) (T : Finset (Fin 4)) :
    mcaWitnessG ((constC2 : Set (Fin 4 → F2))^⋈ (Fin 2)) (1/2) Uref ω T ↔ witD ω T := by
  unfold mcaWitnessG witD
  constructor
  · rintro ⟨hcard, ⟨w, hwmem, hwag⟩, hno⟩
    refine ⟨(card_clause_iff T).mp hcard, ?_, ?_⟩
    · intro k
      obtain ⟨c, hc⟩ := hwmem k
      refine ⟨c, fun i hi => ?_⟩
      have h : w i k = (∑ j, ω j • Uref j i) k := congrFun (hwag i hi) k
      show ω 0 * colsU 0 k i + ω 1 * colsU 1 k i = c
      rw [← seed_comb, ← h]
      exact hc i
    · intro hall
      apply hno
      refine ⟨fun j i k => (hall j k).choose, fun j k => ⟨(hall j k).choose, fun _ => rfl⟩,
        fun i hi j => ?_⟩
      funext k
      show (hall j k).choose = Uref j i k
      exact ((hall j k).choose_spec i hi).symm
  · rintro ⟨hcard, hcols, hno⟩
    refine ⟨(card_clause_iff T).mpr hcard, ?_, ?_⟩
    · refine ⟨fun _ k => (hcols k).choose, fun k => ⟨(hcols k).choose, fun _ => rfl⟩,
        fun i hi => ?_⟩
      funext k
      show (hcols k).choose = (∑ j, ω j • Uref j i) k
      rw [seed_comb]
      exact ((hcols k).choose_spec i hi).symm
    · rintro ⟨cs, hcs, hag⟩
      apply hno
      intro j k
      obtain ⟨c, hc⟩ := hcs j k
      refine ⟨c, fun i hi => ?_⟩
      have h : cs j i = Uref j i := hag i hi j
      have hk : cs j i k = colsU j k i := by rw [h]; rfl
      rw [← hk]
      exact hc i

/-! ### The forced obstruction lines (exhaustive `decide` over all 16 witness sets) -/

theorem forced01 : ∀ T : Finset (Fin 4), witD ![0, 1] T →
    ∀ lam : Fin 2 → F2, (inK2 T lam ↔ (lam = 0 ∨ lam = ![0, 1])) := by decide

theorem forced10 : ∀ T : Finset (Fin 4), witD ![1, 0] T →
    ∀ lam : Fin 2 → F2, (inK2 T lam ↔ (lam = 0 ∨ lam = ![1, 0])) := by decide

theorem forced11 : ∀ T : Finset (Fin 4), witD ![1, 1] T →
    ∀ lam : Fin 2 → F2, (inK2 T lam ↔ (lam = 0 ∨ lam = ![1, 1])) := by decide

/-! ### The three lines, as submodules -/

/-- The line `{0, v}` of `F₂²`. -/
def lineThrough (v : Fin 2 → F2) : Submodule F2 (Fin 2 → F2) where
  carrier := {lam | lam = 0 ∨ lam = v}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro a b ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · rw [ha, hb, add_zero]
      exact Or.inl rfl
    · rw [ha, hb, zero_add]
      exact Or.inr rfl
    · rw [ha, hb, add_zero]
      exact Or.inr rfl
    · rw [ha, hb]
      refine Or.inl ?_
      funext i
      exact CharTwo.add_self_eq_zero (v i)
  smul_mem' := by
    intro c lam hl
    rcases hl with hl | hl
    · rw [hl, smul_zero]
      exact Or.inl rfl
    · rw [hl]
      rcases (by decide : ∀ x : F2, x = 0 ∨ x = 1) c with hc | hc
      · rw [hc, zero_smul]
        exact Or.inl rfl
      · rw [hc, one_smul]
        exact Or.inr rfl

theorem mem_lineThrough (v lam : Fin 2 → F2) :
    lam ∈ lineThrough v ↔ (lam = 0 ∨ lam = v) := Iff.rfl

/-- The obstruction subspace of any `witD`-witness of a forced seed *is* its line. -/
theorem jSS_eq_line_of_forced {v : Fin 2 → F2} {T : Finset (Fin 4)}
    (hforced : ∀ lam : Fin 2 → F2, (inK2 T lam ↔ (lam = 0 ∨ lam = v))) :
    jointStackSubmodule constC2 T Uref = lineThrough v := by
  ext lam
  rw [mem_jSS_iff_inK2, mem_lineThrough]
  exact hforced lam

/-! ### The refutation -/

open Classical in
/-- **`MissingLine` is FALSE for the full-plane generator** (`Ω = F₂²`, `|Ω| = 4 > q = 2`):
the three nonzero seeds of the refuting stack are bad and forced onto three pairwise-distinct
obstruction lines, but the covering family may hold at most `q = 2` subspaces. Hence
`ObstructionBound` fails too, and the obstruction-counting route to interleaving exactness
is unavailable for large-seed generators. -/
theorem missingLine_bigseed_refuted :
    ¬ MissingLine constC2 (1/2 : ℝ≥0) (fun ω : Fin 2 → F2 => ω) Uref := by
  rintro ⟨Ls, hcard, _hproper, hcover⟩
  -- the three bad seeds, with explicit witnesses
  have hbad01 : mcaEventG ((constC2 : Set (Fin 4 → F2))^⋈ (Fin 2)) (1/2) Uref (![0, 1] : Fin 2 → F2) :=
    ⟨{1, 3}, (mcaWitnessG_iff_witD ![0, 1] {1, 3}).mpr (by decide)⟩
  have hbad10 : mcaEventG ((constC2 : Set (Fin 4 → F2))^⋈ (Fin 2)) (1/2) Uref (![1, 0] : Fin 2 → F2) :=
    ⟨{0, 1}, (mcaWitnessG_iff_witD ![1, 0] {0, 1}).mpr (by decide)⟩
  have hbad11 : mcaEventG ((constC2 : Set (Fin 4 → F2))^⋈ (Fin 2)) (1/2) Uref (![1, 1] : Fin 2 → F2) :=
    ⟨{2, 3}, (mcaWitnessG_iff_witD ![1, 1] {2, 3}).mpr (by decide)⟩
  -- coverage hands each seed a witness whose obstruction is in Ls; forcing pins the line
  obtain ⟨T1, hW1, hK1⟩ := hcover ![0, 1] hbad01
  obtain ⟨T2, hW2, hK2⟩ := hcover ![1, 0] hbad10
  obtain ⟨T3, hW3, hK3⟩ := hcover ![1, 1] hbad11
  rw [jSS_eq_line_of_forced (forced01 T1 ((mcaWitnessG_iff_witD _ _).mp hW1))] at hK1
  rw [jSS_eq_line_of_forced (forced10 T2 ((mcaWitnessG_iff_witD _ _).mp hW2))] at hK2
  rw [jSS_eq_line_of_forced (forced11 T3 ((mcaWitnessG_iff_witD _ _).mp hW3))] at hK3
  -- the three lines are pairwise distinct
  have hmem01 : (![0, 1] : Fin 2 → F2) ∈ lineThrough ![0, 1] := Or.inr rfl
  have hmem10 : (![1, 0] : Fin 2 → F2) ∈ lineThrough ![1, 0] := Or.inr rfl
  have hd12 : lineThrough (![0, 1] : Fin 2 → F2) ≠ lineThrough ![1, 0] := fun h => by
    have := h ▸ hmem01
    rw [mem_lineThrough] at this
    exact (by decide : ¬((![0, 1] : Fin 2 → F2) = 0 ∨ (![0, 1] : Fin 2 → F2) = ![1, 0])) this
  have hd13 : lineThrough (![0, 1] : Fin 2 → F2) ≠ lineThrough ![1, 1] := fun h => by
    have := h ▸ hmem01
    rw [mem_lineThrough] at this
    exact (by decide : ¬((![0, 1] : Fin 2 → F2) = 0 ∨ (![0, 1] : Fin 2 → F2) = ![1, 1])) this
  have hd23 : lineThrough (![1, 0] : Fin 2 → F2) ≠ lineThrough ![1, 1] := fun h => by
    have := h ▸ hmem10
    rw [mem_lineThrough] at this
    exact (by decide : ¬((![1, 0] : Fin 2 → F2) = 0 ∨ (![1, 0] : Fin 2 → F2) = ![1, 1])) this
  -- three distinct members force |Ls| ≥ 3 > 2 = |F₂|
  have hsub : ({lineThrough ![0, 1], lineThrough ![1, 0], lineThrough ![1, 1]} :
      Finset (Submodule F2 (Fin 2 → F2))) ⊆ Ls := by
    intro K hK
    simp only [Finset.mem_insert, Finset.mem_singleton] at hK
    rcases hK with rfl | rfl | rfl
    exacts [hK1, hK2, hK3]
  have hcard3 : ({lineThrough ![0, 1], lineThrough ![1, 0], lineThrough ![1, 1]} :
      Finset (Submodule F2 (Fin 2 → F2))).card = 3 := by
    rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push Not
      exact ⟨hd12, hd13⟩)]
    rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_singleton]
      exact hd23)]
    rfl
  have h3le : (3 : ℕ) ≤ Ls.card := hcard3 ▸ Finset.card_le_card hsub
  have h2 : Fintype.card F2 = 2 := by rw [ZMod.card]
  omega

/-- The seed space genuinely exceeds the field: `|Ω| = 4 > 2 = q` — so this refutation is
exactly complementary to `missingLine_of_card_le`, and the `|Ω| ≤ q` bound there is sharp. -/
theorem seed_space_exceeds_field :
    Fintype.card F2 < Fintype.card (Fin 2 → F2) := by
  rw [ZMod.card]
  rw [Fintype.card_fun]
  rw [ZMod.card]
  norm_num

/-! ## Source audit -/

#print axioms mem_jSS_iff_inK2
#print axioms mcaWitnessG_iff_witD
#print axioms forced01
#print axioms missingLine_bigseed_refuted
#print axioms seed_space_exceeds_field

end ProximityGap.Jo26MissingLineBigSeedRefuted
