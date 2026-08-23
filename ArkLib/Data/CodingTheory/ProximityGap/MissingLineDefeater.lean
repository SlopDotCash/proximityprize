/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Jo26ObstructionCount

/-!
# S2(b) REFUTED at the Johnson radius: an explicit `MissingLine` defeater

Hypothesis S2(b) of the #357 campaign asked whether every two-column stack misses a line —
formally, whether `MissingLine C δ G U` (`Jo26ObstructionCount.lean`) holds for **every**
stack `U`, which would discharge `ObstructionBound` and give generator-MCA interleaving
exactness for every generator via `epsMCAG_interleaved_eq_of_missingLine`.

**This file refutes the universal form.** The probe campaign
(`probe_missing_line_f5_rungs.py`, `probe_missing_line_l3.py`,
`probe_missing_line_heavy_fast.py`, cross-validated by
`verify_missing_line_defeater.py`) found that the minimum obstruction-hitting number
`H(U)` undergoes a **phase transition at the Johnson radius**: in every sub-Johnson rung
`H ≤ 2`, but at `δ = 1 − √ρ` it jumps (`H = 4` at `F₅, n = 4, k = 1`) and defeats the
`≤ q` family bound outright over small fields (`H = 3 > q = 2` at `F₂`,
`H = 4 > q = 3` at `F₃`, both `n = 4`, `k = 1`, `δ = 1/2 = 1 − √(1/4)`).

Here we machine-check the `F₂` defeater. `C` = the repetition code on `Fin 4` over
`F₂` (`ρ = 1/4`, Johnson radius `1 − √ρ = 1/2 = δ`), stack rows
`U 0 = (e₀, e₁)`, `U 1 = (e₁, e₀ + e₂)`, seed generator = the identity (all coefficient
pairs — the universal generator at `l = 2`). The structure is fully rigid:

* seed `(0,1)` has the **unique** witness `T = {0,2}`, with obstruction `{0, (0,1)}`;
* seed `(1,0)` has the unique witness `T = {2,3}`, with obstruction `{0, (1,0)}`;
* seed `(1,1)` has the unique witness `T = {0,1}`, with obstruction `{0, (1,1)}`.

Three bad seeds pin three **pairwise distinct** lines of `F₂²`, so any dominating family
must contain all three — but `MissingLine` allows at most `q = |F₂| = 2`. Hence
`¬ MissingLine` (`missingLine_defeated`), and since `ObstructionBound` at `s = 2` is the
same statement, `¬ ObstructionBound` (`obstructionBound_defeated`).

**Honest scope.** This kills `MissingLine`/`ObstructionBound` as *universal* (all codes,
all radii) discharge routes: any future proof must be code- and radius-aware. It does
**not** refute generator-MCA interleaving exactness itself (the route is sufficient, not
necessary), and it says nothing below Johnson — where every probe rung still satisfies
`H ≤ 2` and the route remains conjecturally open (the surviving, re-aimed S2(b)).

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References

- Issue #357 (the δ* campaign, hypothesis S2(b)); `DISPROOF_LOG.md` entry of the same date.
- `Jo26ObstructionCount.lean` (the `MissingLine`/`ObstructionBound` targets).
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.MissingLineDefeater

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

/-- The base field `F₂`. -/
abbrev F2 := ZMod 2

/-- The repetition code on four coordinates: rate `1/4`, Johnson radius `1/2`. -/
def repC : Submodule F2 (Fin 4 → F2) where
  carrier := {f | ∃ a : F2, ∀ i, f i = a}
  zero_mem' := ⟨0, fun _ => rfl⟩
  add_mem' := by
    rintro f g ⟨a, hf⟩ ⟨b, hg⟩
    exact ⟨a + b, fun i => by rw [Pi.add_apply, hf i, hg i]⟩
  smul_mem' := by
    rintro c f ⟨a, hf⟩
    exact ⟨c * a, fun i => by rw [Pi.smul_apply, hf i, smul_eq_mul]⟩

theorem mem_repC (f : Fin 4 → F2) :
    f ∈ (repC : Set (Fin 4 → F2)) ↔ ∃ a : F2, ∀ i, f i = a :=
  Iff.rfl

/-- The defeating stack (probe-discovered): rows `(e₀, e₁)` and `(e₁, e₀ + e₂)`,
indexed as `U j i k` (row `j`, coordinate `i`, column `k`). -/
def Udef : Fin 2 → Fin 4 → Fin 2 → F2 :=
  ![![![1, 0], ![0, 1], ![0, 0], ![0, 0]],
    ![![0, 1], ![1, 0], ![0, 1], ![0, 0]]]

/-- Case analysis for `F₂` scalars. -/
theorem F2_cases : ∀ t : F2, t = 0 ∨ t = 1 := by decide

/-- The line `{0, c}` of `F₂²` through a vector `c`. -/
def line2 (c : Fin 2 → F2) (hcc : c + c = 0) : Submodule F2 (Fin 2 → F2) where
  carrier := {x | x = 0 ∨ x = c}
  zero_mem' := Or.inl rfl
  add_mem' := by
    rintro x y (hx | hx) (hy | hy)
    · exact Or.inl (by rw [hx, hy, add_zero])
    · exact Or.inr (by rw [hx, hy, zero_add])
    · exact Or.inr (by rw [hx, hy, add_zero])
    · exact Or.inl (by rw [hx, hy, hcc])
  smul_mem' := by
    rintro t x (hx | hx)
    · exact Or.inl (by rw [hx, smul_zero])
    · rcases F2_cases t with ht | ht
      · exact Or.inl (by rw [hx, ht, zero_smul])
      · exact Or.inr (by rw [hx, ht, one_smul])

/-- The three lines pinned by the three bad seeds. -/
def L01 : Submodule F2 (Fin 2 → F2) := line2 ![0, 1] (by decide)
def L10 : Submodule F2 (Fin 2 → F2) := line2 ![1, 0] (by decide)
def L11 : Submodule F2 (Fin 2 → F2) := line2 ![1, 1] (by decide)

theorem mem_line2 (c : Fin 2 → F2) (hcc : c + c = 0) (x : Fin 2 → F2) :
    x ∈ line2 c hcc ↔ x = 0 ∨ x = c :=
  Iff.rfl

/-- Membership in the interleaved repetition code, in per-column form. -/
theorem mem_inter (w : Fin 4 → Fin 2 → F2) :
    w ∈ ((repC : Set (Fin 4 → F2))^⋈ (Fin 2)) ↔
      ∀ k, ∃ a : F2, ∀ i, w i k = a :=
  Iff.rfl

/-! ## The decidable cores -/

/-- Decidable core of the `mcaWitnessG` clause for the interleaved repetition code at
`δ = 1/2`: size-`≥ 2` witness, both combined columns constant on `T`, and the four base
words not simultaneously column-constant on `T`. -/
def coreW (c : Fin 2 → F2) (T : Finset (Fin 4)) : Prop :=
  2 ≤ T.card ∧
  (∃ a : Fin 2 → F2, ∀ i ∈ T, ∀ k, (∑ j, c j • Udef j i k) = a k) ∧
  ¬ (∃ b : Fin 2 → Fin 2 → F2, ∀ i ∈ T, ∀ j k, Udef j i k = b j k)

instance (c : Fin 2 → F2) (T : Finset (Fin 4)) : Decidable (coreW c T) := by
  unfold coreW; infer_instance

/-- The card-clause bridge at `δ = 1/2`, `n = 4`. -/
theorem card_bridge {T : Finset (Fin 4)}
    (h : (T.card : ℝ≥0) ≥ (1 - (1/2 : ℝ≥0)) * (Fintype.card (Fin 4) : ℝ≥0)) :
    2 ≤ T.card := by
  have h2 : (2 : ℝ≥0) ≤ (T.card : ℝ≥0) := by
    refine le_trans ?_ h
    have hhalf : (2 : ℝ≥0) = (1/2 : ℝ≥0) * 4 := by norm_num
    have hle : (1/2 : ℝ≥0) ≤ 1 - (1/2 : ℝ≥0) := by
      rw [le_tsub_iff_right (by norm_num : (1/2 : ℝ≥0) ≤ 1)]
      norm_num
    rw [Fintype.card_fin]
    calc (2 : ℝ≥0) = (1/2 : ℝ≥0) * 4 := hhalf
      _ ≤ (1 - (1/2 : ℝ≥0)) * 4 := by gcongr
      _ = (1 - (1/2 : ℝ≥0)) * ((4 : ℕ) : ℝ≥0) := by norm_num
  exact_mod_cast h2

/-- The reverse card clause: a size-2 witness set satisfies the `ℝ≥0` clause. -/
theorem card_clause_of_two {T : Finset (Fin 4)} (h : T.card = 2) :
    (T.card : ℝ≥0) ≥ (1 - (1/2 : ℝ≥0)) * (Fintype.card (Fin 4) : ℝ≥0) := by
  have hle : (1 - (1/2 : ℝ≥0)) ≤ 1/2 := tsub_le_iff_right.mpr (by norm_num)
  rw [h, Fintype.card_fin]
  calc (1 - (1/2 : ℝ≥0)) * ((4 : ℕ) : ℝ≥0) ≤ (1/2 : ℝ≥0) * ((4 : ℕ) : ℝ≥0) := by gcongr
    _ = 2 := by norm_num

/-- Bridge: the real `mcaWitnessG` clause implies the decidable core. -/
theorem coreW_of_witness (c : Fin 2 → F2) (T : Finset (Fin 4))
    (hw : mcaWitnessG ((repC : Set (Fin 4 → F2))^⋈ (Fin 2)) (1/2) Udef c T) :
    coreW c T := by
  obtain ⟨hcard, ⟨w, hwmem, hag⟩, hno⟩ := hw
  refine ⟨card_bridge hcard, ?_, ?_⟩
  · -- both combined columns are constant on T, with values from the codeword columns
    refine ⟨fun k => w 0 k, fun i hi k => ?_⟩
    obtain ⟨ak, hcol⟩ := (mem_inter w).mp hwmem k
    have hwi : w i k = (∑ j, c j • Udef j i) k := congrFun (hag i hi) k
    have hsum : (∑ j, c j • Udef j i) k = ∑ j, c j • Udef j i k := by
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl fun j _ => by rw [Pi.smul_apply]
    show (∑ j, c j • Udef j i k) = w 0 k
    calc (∑ j, c j • Udef j i k) = (∑ j, c j • Udef j i) k := hsum.symm
      _ = w i k := hwi.symm
      _ = ak := hcol i
      _ = w 0 k := (hcol 0).symm
  · -- the stack is not jointly column-constant on T
    rintro ⟨b, hb⟩
    refine hno ⟨fun j => fun _ k => b j k, fun j k => ⟨b j k, fun _ => rfl⟩,
      fun i hi j => ?_⟩
    funext k
    exact (hb i hi j k).symm

/-- Membership in the obstruction subspace, in decidable form: the `λ`-combination of
every row is constant on `S`. -/
theorem mem_jointStack_iff (S : Finset (Fin 4)) (lam : Fin 2 → F2) :
    lam ∈ jointStackSubmodule repC S Udef ↔
      ∃ b : Fin 2 → F2, ∀ i ∈ S, ∀ j, (∑ k, lam k • Udef j i k) = b j := by
  constructor
  · rintro ⟨cs, hcs, hag⟩
    refine ⟨fun j => cs j 0, fun i hi j => ?_⟩
    obtain ⟨a, ha⟩ := (mem_repC _).mp (hcs j)
    have h : cs j i = ∑ k, lam k • Udef j i k := hag i hi j
    show (∑ k, lam k • Udef j i k) = cs j 0
    rw [← h, ha i, ha 0]
  · rintro ⟨b, hb⟩
    exact ⟨fun j _ => b j, fun j => ⟨b j, fun _ => rfl⟩,
      fun i hi j => (hb i hi j).symm⟩

/-! ## The three pinned seeds (kernel-checked cores) -/

theorem pin01_core : ∀ T : Finset (Fin 4),
    coreW ![0, 1] T → T = ({0, 2} : Finset (Fin 4)) := by decide

theorem pin10_core : ∀ T : Finset (Fin 4),
    coreW ![1, 0] T → T = ({2, 3} : Finset (Fin 4)) := by decide

theorem pin11_core : ∀ T : Finset (Fin 4),
    coreW ![1, 1] T → T = ({0, 1} : Finset (Fin 4)) := by decide

theorem jointSub01_core : ∀ lam : Fin 2 → F2,
    (∃ b : Fin 2 → F2, ∀ i ∈ ({0, 2} : Finset (Fin 4)), ∀ j,
        (∑ k, lam k • Udef j i k) = b j)
      ↔ (lam = 0 ∨ lam = ![0, 1]) := by decide

theorem jointSub10_core : ∀ lam : Fin 2 → F2,
    (∃ b : Fin 2 → F2, ∀ i ∈ ({2, 3} : Finset (Fin 4)), ∀ j,
        (∑ k, lam k • Udef j i k) = b j)
      ↔ (lam = 0 ∨ lam = ![1, 0]) := by decide

theorem jointSub11_core : ∀ lam : Fin 2 → F2,
    (∃ b : Fin 2 → F2, ∀ i ∈ ({0, 1} : Finset (Fin 4)), ∀ j,
        (∑ k, lam k • Udef j i k) = b j)
      ↔ (lam = 0 ∨ lam = ![1, 1]) := by decide

/-- Seed `(0,1)`: every witness pins the obstruction to the line `{0,(0,1)}`. -/
theorem pinned01 (T : Finset (Fin 4))
    (hw : mcaWitnessG ((repC : Set (Fin 4 → F2))^⋈ (Fin 2)) (1/2) Udef (![0, 1] : Fin 2 → F2) T) :
    jointStackSubmodule repC T Udef = L01 := by
  have hT := pin01_core T (coreW_of_witness _ T hw)
  subst hT
  exact Submodule.ext fun lam =>
    (mem_jointStack_iff _ lam).trans (jointSub01_core lam)

/-- Seed `(1,0)`: every witness pins the obstruction to the line `{0,(1,0)}`. -/
theorem pinned10 (T : Finset (Fin 4))
    (hw : mcaWitnessG ((repC : Set (Fin 4 → F2))^⋈ (Fin 2)) (1/2) Udef (![1, 0] : Fin 2 → F2) T) :
    jointStackSubmodule repC T Udef = L10 := by
  have hT := pin10_core T (coreW_of_witness _ T hw)
  subst hT
  exact Submodule.ext fun lam =>
    (mem_jointStack_iff _ lam).trans (jointSub10_core lam)

/-- Seed `(1,1)`: every witness pins the obstruction to the line `{0,(1,1)}`. -/
theorem pinned11 (T : Finset (Fin 4))
    (hw : mcaWitnessG ((repC : Set (Fin 4 → F2))^⋈ (Fin 2)) (1/2) Udef (![1, 1] : Fin 2 → F2) T) :
    jointStackSubmodule repC T Udef = L11 := by
  have hT := pin11_core T (coreW_of_witness _ T hw)
  subst hT
  exact Submodule.ext fun lam =>
    (mem_jointStack_iff _ lam).trans (jointSub11_core lam)

/-! ## The three bad-seed events -/

/-- The constant interleaved codeword with column values `a`. -/
theorem constWord_mem (a : Fin 2 → F2) :
    (fun (_ : Fin 4) => a) ∈ ((repC : Set (Fin 4 → F2))^⋈ (Fin 2)) :=
  (mem_inter _).mpr fun k => ⟨a k, fun _ => rfl⟩

/-- Generic event builder from a size-2 witness with explicit constant explanation. -/
theorem event_of (c : Fin 2 → F2) (T : Finset (Fin 4)) (a : Fin 2 → F2)
    (hcard : T.card = 2)
    (hag : ∀ i ∈ T, (fun (_ : Fin 4) => a) i = ∑ j, c j • Udef j i)
    (hno : ¬ stackJointAgreesOn ((repC : Set (Fin 4 → F2))^⋈ (Fin 2)) T Udef) :
    mcaEventG ((repC : Set (Fin 4 → F2))^⋈ (Fin 2)) (1/2) Udef c :=
  ⟨T, card_clause_of_two hcard, ⟨fun _ => a, constWord_mem a, hag⟩, hno⟩

/-- Joint column-constancy fails on any `T` containing two coordinates where some base
word differs (decidable contradiction form). -/
theorem no_joint_of_core (T : Finset (Fin 4))
    (hcore : ¬ ∃ b : Fin 2 → Fin 2 → F2, ∀ i ∈ T, ∀ j k, Udef j i k = b j k) :
    ¬ stackJointAgreesOn ((repC : Set (Fin 4 → F2))^⋈ (Fin 2)) T Udef := by
  rintro ⟨cs, hcs, hag⟩
  refine hcore ⟨fun j k => cs j 0 k, fun i hi j k => ?_⟩
  obtain ⟨a, ha⟩ := (mem_inter (cs j)).mp (hcs j) k
  have h3 : cs j i k = Udef j i k := congrFun (hag i hi j) k
  show Udef j i k = cs j 0 k
  rw [← h3, ha i, ha 0]

theorem event01 :
    mcaEventG ((repC : Set (Fin 4 → F2))^⋈ (Fin 2)) (1/2) Udef (![0, 1] : Fin 2 → F2) :=
  event_of ![0, 1] {0, 2} ![0, 1] (by decide)
    (by decide)
    (no_joint_of_core _ (by decide))

theorem event10 :
    mcaEventG ((repC : Set (Fin 4 → F2))^⋈ (Fin 2)) (1/2) Udef (![1, 0] : Fin 2 → F2) :=
  event_of ![1, 0] {2, 3} ![0, 0] (by decide)
    (by decide)
    (no_joint_of_core _ (by decide))

theorem event11 :
    mcaEventG ((repC : Set (Fin 4 → F2))^⋈ (Fin 2)) (1/2) Udef (![1, 1] : Fin 2 → F2) :=
  event_of ![1, 1] {0, 1} ![1, 1] (by decide)
    (by decide)
    (no_joint_of_core _ (by decide))

/-! ## Distinctness of the pinned lines -/

theorem L01_ne_L10 : L01 ≠ L10 := by
  intro h
  have hmem : (![0, 1] : Fin 2 → F2) ∈ L10 := by
    rw [← h]; exact Or.inr rfl
  rcases hmem with h0 | h1
  · exact absurd h0 (by decide)
  · exact absurd h1 (by decide)

theorem L01_ne_L11 : L01 ≠ L11 := by
  intro h
  have hmem : (![0, 1] : Fin 2 → F2) ∈ L11 := by
    rw [← h]; exact Or.inr rfl
  rcases hmem with h0 | h1
  · exact absurd h0 (by decide)
  · exact absurd h1 (by decide)

theorem L10_ne_L11 : L10 ≠ L11 := by
  intro h
  have hmem : (![1, 0] : Fin 2 → F2) ∈ L11 := by
    rw [← h]; exact Or.inr rfl
  rcases hmem with h0 | h1
  · exact absurd h0 (by decide)
  · exact absurd h1 (by decide)

/-! ## The refutation -/

open Classical in
/-- **S2(b) universal form REFUTED.** The repetition code over `F₂` at its Johnson
radius `δ = 1/2` admits a stack defeating `MissingLine`: three bad seeds pin three
distinct lines, overflowing every `≤ q = 2` dominating family. -/
theorem missingLine_defeated :
    ¬ Jo26Obstruction.MissingLine repC (1/2)
      (id : (Fin 2 → F2) → Fin 2 → F2) Udef := by
  rintro ⟨Ls, hcard, _hproper, hcover⟩
  obtain ⟨T1, hw1, hmem1⟩ := hcover ![0, 1] event01
  obtain ⟨T2, hw2, hmem2⟩ := hcover ![1, 0] event10
  obtain ⟨T3, hw3, hmem3⟩ := hcover ![1, 1] event11
  rw [pinned01 T1 hw1] at hmem1
  rw [pinned10 T2 hw2] at hmem2
  rw [pinned11 T3 hw3] at hmem3
  have hsub : ({L01, L10, L11} : Finset (Submodule F2 (Fin 2 → F2))) ⊆ Ls := by
    intro K hK
    simp only [Finset.mem_insert, Finset.mem_singleton] at hK
    rcases hK with rfl | rfl | rfl
    · exact hmem1
    · exact hmem2
    · exact hmem3
  have hcard3 : ({L01, L10, L11} : Finset (Submodule F2 (Fin 2 → F2))).card = 3 := by
    rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact fun h => h.elim (fun h' => L01_ne_L10 h') (fun h' => L01_ne_L11 h'))]
    rw [Finset.card_insert_of_notMem (by
      simp only [Finset.mem_singleton]
      exact fun h => L10_ne_L11 h)]
    rw [Finset.card_singleton]
  have h3 : 3 ≤ Ls.card := hcard3 ▸ Finset.card_le_card hsub
  have h2 : Fintype.card F2 = 2 := by rw [ZMod.card]
  omega

/-- The universal discharge hypothesis of `epsMCAG_interleaved_eq_of_missingLine` is
false at the Johnson radius: not every stack misses a line. -/
theorem not_forall_missingLine :
    ¬ ∀ U : Fin 2 → Fin 4 → Fin 2 → F2,
        Jo26Obstruction.MissingLine repC (1/2)
          (id : (Fin 2 → F2) → Fin 2 → F2) U :=
  fun h => missingLine_defeated (h Udef)

/-- `ObstructionBound` at `s = 2` is the same statement, so it is defeated too. -/
theorem obstructionBound_defeated :
    ¬ Jo26Obstruction.ObstructionBound repC (1/2)
      (id : (Fin 2 → F2) → Fin 2 → F2) Udef :=
  missingLine_defeated

/-! ## Source audit -/

#print axioms missingLine_defeated
#print axioms not_forall_missingLine
#print axioms obstructionBound_defeated

end ProximityGap.MissingLineDefeater
