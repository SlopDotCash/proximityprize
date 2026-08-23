/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# Tower monotonicity: `ε_mca` is monotone up the 2-adic tower (#357, item 23)

Item 23 of the 26-thread review — the V-vector recursion down the fold tower, the
composition of the fold fixed-point with the step-function law that was never made.
The result is an `ε_mca`-level tower theorem (the landed tower theorems are
census-level):

**Lifting preserves badness at the same relative radius.**  Pair the `2m` upstairs
positions as `{inl j, inr j}` and lift a downstairs stack by `u(±x_j) := u'(x_j²)`
(constant on fibers).  Then for every bad scalar `γ` of `(u₀', u₁')` at radius `δ`:
the lifted witness (the full fiber preimage, twice the size — same *relative* size)
carries the lifted line explanation, and any upstairs joint explanation would
**average down** (`evenPart v := (v(inl j) + v(inr j))/2`) to a downstairs joint
explanation.  Hence with two structural hypotheses —

* `hlift` : lifts of downstairs codewords are upstairs codewords,
* `heven` : even parts of upstairs codewords are downstairs codewords —

(both hold for smooth-tower Reed–Solomon with `K = 2K′−1`, by `P′ ↦ P′(X²)` and the
even-coefficient projection), we get

  `epsMCA (C′, δ) ≤ epsMCA (C, δ)`   —   **the same `δ`**.

Consequences: every exact window value at scale `m` is a production lower bound at
every tower scale above it; the V-vector of `C_m` embeds into the even floors of the
V-vector of `C_{2m}`; and window lower-bound constructions need only be found at the
smallest scale where they exist.
-/

open Finset
open scoped NNReal ENNReal ProbabilityTheory

namespace ProximityGap.Tower

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {m : ℕ} [NeZero m]

/-- Upstairs position of the first fiber element over class `j`. -/
def inl (j : Fin m) : Fin (2 * m) :=
  ⟨j, by have := j.2; omega⟩

/-- Upstairs position of the second fiber element over class `j`. -/
def inr (j : Fin m) : Fin (2 * m) :=
  ⟨j + m, by have := j.2; omega⟩

theorem inl_ne_inr (j j' : Fin m) : inl j ≠ inr j' := by
  intro h
  have h1 := congrArg Fin.val h
  simp only [inl, inr] at h1
  have := j.2
  have := j'.2
  omega

theorem inl_injective : Function.Injective (inl (m := m)) := by
  intro a b h
  have := congrArg Fin.val h
  simp only [inl] at this
  exact Fin.val_injective this

theorem inr_injective : Function.Injective (inr (m := m)) := by
  intro a b h
  have := congrArg Fin.val h
  simp only [inr] at this
  have ha := a.2
  have hb := b.2
  exact Fin.val_injective (by omega)

/-- The fiber class of an upstairs position. -/
def cls (i : Fin (2 * m)) : Fin m :=
  ⟨i % m, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne m))⟩

theorem cls_inl (j : Fin m) : cls (inl j) = j := by
  simp only [cls, inl]
  exact Fin.val_injective (by simp [Nat.mod_eq_of_lt j.2])

theorem cls_inr (j : Fin m) : cls (inr j) = j := by
  simp only [cls, inr]
  refine Fin.val_injective ?_
  simp only [Nat.add_mod_right, Nat.mod_eq_of_lt j.2]

/-- The lift of a downstairs word: constant on fibers. -/
def lift (u : Fin m → F) : Fin (2 * m) → F :=
  fun i => u (cls i)

/-- The even part (fiber average) of an upstairs word. -/
def evenPart (v : Fin (2 * m) → F) : Fin m → F :=
  fun j => (v (inl j) + v (inr j)) / 2

theorem lift_inl (u : Fin m → F) (j : Fin m) : lift u (inl j) = u j := by
  simp [lift, cls_inl]

theorem lift_inr (u : Fin m → F) (j : Fin m) : lift u (inr j) = u j := by
  simp [lift, cls_inr]

/-- The lifted witness: both fiber elements over every downstairs witness class. -/
def liftWitness (T : Finset (Fin m)) : Finset (Fin (2 * m)) :=
  T.image inl ∪ T.image inr

theorem liftWitness_card (T : Finset (Fin m)) :
    (liftWitness T).card = 2 * T.card := by
  unfold liftWitness
  rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective _ inl_injective,
    Finset.card_image_of_injective _ inr_injective]
  · ring
  · rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j', -, hj'⟩ := Finset.mem_image.mp hb
    exact inl_ne_inr j j' hj'.symm

open Classical in
/-- **Tower monotonicity of the MCA error.**  If lifts of `C′`-codewords are
`C`-codewords and even parts of `C`-codewords are `C′`-codewords, then
`ε_mca(C′, δ) ≤ ε_mca(C, δ)` — at the same relative radius. -/
theorem epsMCA_le_of_tower (C : Submodule F (Fin (2 * m) → F))
    (C' : Submodule F (Fin m → F)) (h2 : (2 : F) ≠ 0)
    (hlift : ∀ c' ∈ C', lift c' ∈ C)
    (heven : ∀ v ∈ C, evenPart v ∈ C') (δ : ℝ≥0) :
    epsMCA (F := F) (A := F) (C' : Set (Fin m → F)) δ
      ≤ epsMCA (F := F) (A := F) (C : Set (Fin (2 * m) → F)) δ := by
  unfold epsMCA
  refine iSup_le fun u => ?_
  refine le_trans (Pr_le_Pr_of_implies _ _ _ ?_)
    (le_iSup (fun v : Code.WordStack F (Fin 2) (Fin (2 * m)) =>
      Pr_{let γ ← $ᵖ F}[mcaEvent (C : Set (Fin (2 * m) → F)) δ (v 0) (v 1) γ])
      ![lift (u 0), lift (u 1)])
  -- badness lifts, scalar by scalar
  intro γ hbad
  obtain ⟨T, hTsz, ⟨w, hw, hag⟩, hno⟩ := hbad
  refine ⟨liftWitness T, ?_, ?_, ?_⟩
  · -- size: 2|T| ≥ (1−δ)·2m
    rw [liftWitness_card]
    have hcast : ((2 * T.card : ℕ) : ℝ≥0) = 2 * (T.card : ℝ≥0) := by push_cast; ring
    rw [hcast]
    have hcard2m : (Fintype.card (Fin (2 * m)) : ℝ≥0)
        = 2 * (Fintype.card (Fin m) : ℝ≥0) := by
      rw [Fintype.card_fin, Fintype.card_fin]
      push_cast
      ring
    rw [hcard2m]
    calc (1 - δ) * (2 * (Fintype.card (Fin m) : ℝ≥0))
        = 2 * ((1 - δ) * (Fintype.card (Fin m) : ℝ≥0)) := by ring
      _ ≤ 2 * (T.card : ℝ≥0) := by gcongr
  · -- the lifted line explanation
    refine ⟨lift w, hlift w hw, ?_⟩
    intro i hi
    rcases Finset.mem_union.mp hi with h | h
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
      show lift w (inl j) = lift (u 0) (inl j) + γ • lift (u 1) (inl j)
      rw [lift_inl, lift_inl, lift_inl]
      exact hag j hj
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
      show lift w (inr j) = lift (u 0) (inr j) + γ • lift (u 1) (inr j)
      rw [lift_inr, lift_inr, lift_inr]
      exact hag j hj
  · -- no upstairs joint explanation: it would average down
    rintro ⟨v₀, hv₀, v₁, hv₁, hagv⟩
    apply hno
    refine ⟨evenPart v₀, heven v₀ hv₀, evenPart v₁, heven v₁ hv₁, ?_⟩
    intro j hj
    have hl := hagv (inl j) (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨j, hj, rfl⟩))
    have hr := hagv (inr j) (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨j, hj, rfl⟩))
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      at hl hr
    constructor
    · show (v₀ (inl j) + v₀ (inr j)) / 2 = u 0 j
      rw [hl.1, hr.1, lift_inl, lift_inr]
      field_simp
      ring
    · show (v₁ (inl j) + v₁ (inr j)) / 2 = u 1 j
      rw [hl.2, hr.2, lift_inl, lift_inr]
      field_simp
      ring

end ProximityGap.Tower

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Tower.epsMCA_le_of_tower
