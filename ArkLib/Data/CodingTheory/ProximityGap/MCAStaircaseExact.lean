/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAStaircaseMaster
import ArkLib.Data.CodingTheory.ProximityGap.MCALowerBound

/-!
# Round 4 (#357): THE EXACT STAIRCASE — `ε_mca = b/|F|` on every band below `3b − 2`

Companion to the master collapse (`MCAStaircaseMaster`): the matching `b`-spike lower bound
for every band, and the exact value. For every linear code with no nonzero codeword on
`≤ 3(b−1)` points, any `b` injectively-placed spikes and `b` distinct scalars:

  `epsMCA_eq_div_card_of_dist` : `ε_mca(C, δ) = b/|F|` on the band `b − 1 ≤ δ·n < b`.

**The `b`-spike pencil.** With positions `i : Fin b ↪ ι`, scalars `g : Fin b ↪ F`, value
`a ≠ 0`:

  `u₁ = −Σ_x single (i x) a`, `u₀ = Σ_x (g x) • single (i x) a`,
  so `u₀ + γ • u₁ = Σ_x (g x − γ) • single (i x) a`.

At `γ = g x₀` the `x₀`-spike vanishes: the line point agrees with the codeword `0` off the
other `b − 1` spike positions — a band-`b` witness. No joint explanation: an explaining
second row agrees with `u₁` off `b − 1` points, hence is a codeword supported on the `b`
spike positions (`b ≤ 3(b−1)` for `b ≥ 2`) — zero, contradicting the surviving spike.
So all `b` scalars `g x` are bad, and the master collapse closes the sandwich.

**Consequence.** The MCA staircase of every linear code is **exactly linear through every
band below a third of the distance**: for production-scale Reed–Solomon (`d = n − k + 1`),
`ε_mca(δ) = (⌊δn⌋ + 1)/q` for all `δ < (d + 2)/(3n) ≈ (1 − ρ)/3` — the first exact-value
theorem family reaching a constant fraction of the unique-decoding radius, every code, every
field, no asymptotics.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ProximityGap.MCAStaircaseExact

open ProximityGap.MCAStaircaseMaster

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- The `b`-spike second row. -/
def brow {b : ℕ} (i : Fin b → ι) (a : A) : ι → A :=
  -(∑ x : Fin b, (Pi.single (i x) a : ι → A))

/-- The `b`-spike first row. -/
def zrow {b : ℕ} (i : Fin b → ι) (g : Fin b → F) (a : A) : ι → A :=
  ∑ x : Fin b, g x • (Pi.single (i x) a : ι → A)

/-- The pencil identity, pointwise. -/
theorem bline {b : ℕ} (i : Fin b → ι) (g : Fin b → F) (a : A) (γ : F) (j : ι) :
    zrow i g a j + γ • brow i a j
      = ∑ x : Fin b, (g x - γ) • (Pi.single (i x) a : ι → A) j := by
  show (∑ x : Fin b, g x • (Pi.single (i x) a : ι → A)) j
      + γ • (-(∑ x : Fin b, (Pi.single (i x) a : ι → A))) j = _
  rw [Finset.sum_apply, Pi.neg_apply, Finset.sum_apply]
  rw [smul_neg, ← sub_eq_add_neg, Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  show g x • (Pi.single (i x) a : ι → A) j - γ • (Pi.single (i x) a : ι → A) j = _
  rw [← sub_smul]

/-- Spike-sum value at a spike position (pointwise form). -/
theorem sum_single_apply_self {b : ℕ} (i : Fin b → ι) (a : A)
    (hi : Function.Injective i) (c : Fin b → F) (y : Fin b) :
    (∑ x : Fin b, c x • (Pi.single (i x) a : ι → A) (i y)) = c y • a := by
  rw [Finset.sum_eq_single y]
  · show c y • (Pi.single (i y) a : ι → A) (i y) = c y • a
    rw [Pi.single_eq_same]
  · intro x _ hxy
    show c x • (Pi.single (i x) a : ι → A) (i y) = 0
    have hne : i y ≠ i x := fun heq => hxy (hi heq).symm
    rw [Pi.single_eq_of_ne hne, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ y) h

/-- Spike-sum value off the spike positions (pointwise form). -/
theorem sum_single_apply_off {b : ℕ} (i : Fin b → ι) (a : A)
    (c : Fin b → F) {j : ι} (hj : ∀ x, j ≠ i x) :
    (∑ x : Fin b, c x • (Pi.single (i x) a : ι → A) j) = 0 := by
  refine Finset.sum_eq_zero fun x _ => ?_
  show c x • (Pi.single (i x) a : ι → A) j = 0
  rw [Pi.single_eq_of_ne (hj x), smul_zero]

open Classical in
/-- **The `b`-spike bad event** at `γ = g x₀`, witness = the universe minus the other
`b − 1` spike positions. -/
theorem mcaEvent_bspike (C : Submodule F (ι → A)) {b : ℕ} (hb : 2 ≤ b)
    (hC : NoWeightLE C (3 * (b - 1)))
    {δ : ℝ≥0} (hδ1 : ((b - 1 : ℕ) : ℝ≥0) ≤ δ * (Fintype.card ι : ℝ≥0))
    {i : Fin b → ι} (hi : Function.Injective i)
    {g : Fin b → F} {a : A} (ha : a ≠ 0) (x₀ : Fin b) :
    mcaEvent (F := F) (C : Set (ι → A)) δ (zrow i g a) (brow i a) (g x₀) := by
  set P : Finset ι := (Finset.univ.erase x₀).image i with hP
  have hPcard : P.card = b - 1 := by
    rw [hP, Finset.card_image_of_injective _ hi,
      Finset.card_erase_of_mem (Finset.mem_univ x₀), Finset.card_univ, Fintype.card_fin]
  have hix₀P : i x₀ ∉ P := by
    rw [hP]
    intro hmem
    obtain ⟨x, hx, hix⟩ := Finset.mem_image.mp hmem
    exact (Finset.mem_erase.mp hx).1 (hi hix)
  refine ⟨Finset.univ \ P, ?_, ⟨0, C.zero_mem, fun j hj => ?_⟩, ?_⟩
  · -- the size clause: n − (b−1) ≥ (1−δ)·n when δ·n ≥ b−1
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, hPcard]
    have hble : b - 1 ≤ Fintype.card ι := by
      have := Fintype.card_le_of_injective i hi
      rw [Fintype.card_fin] at this
      omega
    have hcast : ((Fintype.card ι - (b - 1) : ℕ) : ℝ≥0)
        = (Fintype.card ι : ℝ≥0) - ((b - 1 : ℕ) : ℝ≥0) := by
      have h : ((Fintype.card ι - (b - 1) : ℕ) : ℝ≥0) + ((b - 1 : ℕ) : ℝ≥0)
          = (Fintype.card ι : ℝ≥0) := by
        exact_mod_cast (by omega : Fintype.card ι - (b - 1) + (b - 1) = Fintype.card ι)
      exact eq_tsub_of_add_eq h
    rw [ge_iff_le, hcast]
    calc (1 - δ) * (Fintype.card ι : ℝ≥0)
        ≤ (Fintype.card ι : ℝ≥0) - δ * (Fintype.card ι : ℝ≥0) := by
          rw [tsub_mul, one_mul]
      _ ≤ (Fintype.card ι : ℝ≥0) - ((b - 1 : ℕ) : ℝ≥0) := tsub_le_tsub_left hδ1 _
  · -- the zero codeword matches the line off P
    obtain ⟨_, hjP⟩ := Finset.mem_sdiff.mp hj
    show (0 : A) = zrow i g a j + g x₀ • brow i a j
    rw [bline]
    by_cases hjx : j = i x₀
    · rw [hjx, sum_single_apply_self i a hi]
      rw [sub_self, zero_smul]
    · refine (sum_single_apply_off i a _ fun x => ?_).symm
      intro hjix
      by_cases hxx : x = x₀
      · exact hjx (hxx ▸ hjix)
      · refine hjP ?_
        rw [hP]
        exact Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨hxx, Finset.mem_univ x⟩, hjix.symm⟩
  · -- no joint explanation: the second row is trapped on the spikes
    rintro ⟨v₀, _, v₁, hv₁, hag⟩
    have hv₁supp : ∀ j : ι, (∀ x, j ≠ i x) → v₁ j = 0 := by
      intro j hjx
      have hjS : j ∈ Finset.univ \ P := by
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, fun hjP => ?_⟩
        rw [hP] at hjP
        obtain ⟨x, _, hix⟩ := Finset.mem_image.mp hjP
        exact hjx x hix.symm
      have h := (hag j hjS).2
      rw [h]
      show (-(∑ x : Fin b, (Pi.single (i x) a : ι → A))) j = 0
      rw [Pi.neg_apply, Finset.sum_apply]
      have hz : (∑ x : Fin b, (Pi.single (i x) a : ι → A) j) = 0 := by
        refine Finset.sum_eq_zero fun x _ => ?_
        show (Pi.single (i x) a : ι → A) j = 0
        rw [Pi.single_eq_of_ne (hjx x)]
      rw [hz]
      exact neg_zero
    have hzero : v₁ = 0 := by
      refine hC v₁ hv₁ ⟨Finset.univ.image i, ?_, fun j hj => ?_⟩
      · have h := Finset.card_image_le (s := (Finset.univ : Finset (Fin b))) (f := i)
        rw [Finset.card_univ, Fintype.card_fin] at h
        omega
      · refine hv₁supp j fun x hjix => ?_
        exact hj (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, hjix.symm⟩)
    -- but v₁ must carry the surviving spike at i x₀ ∈ S
    have hix₀S : i x₀ ∈ Finset.univ \ P := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hix₀P⟩
    have h := (hag (i x₀) hix₀S).2
    rw [hzero] at h
    apply ha
    have hsumval : (∑ x : Fin b, (Pi.single (i x) a : ι → A)) (i x₀) = a := by
      rw [Finset.sum_apply, Finset.sum_eq_single x₀]
      · exact Pi.single_eq_same _ _
      · intro x _ hxx
        show (Pi.single (i x) a : ι → A) (i x₀) = 0
        have hne : i x₀ ≠ i x := fun heq => hxx (hi heq).symm
        rw [Pi.single_eq_of_ne hne]
      · intro habs
        exact absurd (Finset.mem_univ x₀) habs
    have hval : (0 : A) = -a := by
      calc (0 : A) = (0 : ι → A) (i x₀) := rfl
        _ = brow i a (i x₀) := h
        _ = -((∑ x : Fin b, (Pi.single (i x) a : ι → A)) (i x₀)) := rfl
        _ = -a := by rw [hsumval]
    rw [← neg_neg a, ← hval, neg_zero]

open Classical in
/-- **Lower half:** the `b`-spike stack has `b` bad scalars, so `ε_mca ≥ b/|F|`. -/
theorem epsMCA_ge_div_card (C : Submodule F (ι → A)) {b : ℕ} (hb : 2 ≤ b)
    (hC : NoWeightLE C (3 * (b - 1)))
    {δ : ℝ≥0} (hδ1 : ((b - 1 : ℕ) : ℝ≥0) ≤ δ * (Fintype.card ι : ℝ≥0))
    {i : Fin b → ι} (hi : Function.Injective i)
    {g : Fin b → F} (hg : Function.Injective g) {a : A} (ha : a ≠ 0) :
    (b : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
      ≤ epsMCA (F := F) (A := A) (C : Set (ι → A)) δ := by
  refine le_trans ?_ (mcaEvent_prob_le_epsMCA (F := F) (A := A) (C : Set (ι → A)) δ
    ![zrow i g a, brow i a])
  have h0 : (![zrow i g a, brow i a] : WordStack A (Fin 2) ι) 0 = zrow i g a := rfl
  have h1 : (![zrow i g a, brow i a] : WordStack A (Fin 2) ι) 1 = brow i a := rfl
  rw [h0, h1, prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  gcongr
  have hsub : Finset.univ.image g ⊆ Finset.filter (fun γ : F =>
      mcaEvent (F := F) (C : Set (ι → A)) δ (zrow i g a) (brow i a) γ) Finset.univ := by
    intro γ hγ
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hγ
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mcaEvent_bspike C hb hC hδ1 hi ha x⟩
  have hcard : (Finset.univ.image g).card = b := by
    rw [Finset.card_image_of_injective _ hg, Finset.card_univ, Fintype.card_fin]
  calc b = (Finset.univ.image g).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

open Classical in
/-- **THE EXACT STAIRCASE:** `ε_mca(C, δ) = b/|F|` exactly on the band `b−1 ≤ δ·n < b`,
for every linear code with no nonzero codeword on `≤ 3(b−1)` points — every band of every
such code, including all production-scale Reed–Solomon below a third of the distance. -/
theorem epsMCA_eq_div_card_of_dist (C : Submodule F (ι → A)) {b : ℕ} (hb : 2 ≤ b)
    (hC : NoWeightLE C (3 * (b - 1))) (hnb : b ≤ Fintype.card ι)
    {δ : ℝ≥0} (hδ1 : ((b - 1 : ℕ) : ℝ≥0) ≤ δ * (Fintype.card ι : ℝ≥0))
    (hδ2 : δ * (Fintype.card ι : ℝ≥0) < (b : ℝ≥0))
    {i : Fin b → ι} (hi : Function.Injective i)
    {g : Fin b → F} (hg : Function.Injective g) {a : A} (ha : a ≠ 0) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ = (b : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  le_antisymm (epsMCA_le_div_card_of_dist C b (by omega) hC hnb hδ2)
    (epsMCA_ge_div_card C hb hC hδ1 hi hg ha)

/-! ## Source audit -/

#print axioms mcaEvent_bspike
#print axioms epsMCA_ge_div_card
#print axioms epsMCA_eq_div_card_of_dist

end ProximityGap.MCAStaircaseExact
