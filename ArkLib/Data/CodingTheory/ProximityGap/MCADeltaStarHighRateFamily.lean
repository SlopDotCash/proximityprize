/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAListBracketInterpolation
import ArkLib.Data.CodingTheory.ProximityGap.MCADeltaStarExactPoint
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# The first exact `δ*` for an infinite family: `δ*(RS[F, D, n−2], ε*) = 1/n` (#357)

R1 (`MCADeltaStarExactPoint.lean`) produced the first machine-checked exact `δ*` value, at
one toy instance. This file turns that point into the **first exact `δ*` theorem for an
infinite family of codes**: for *every* finite field `F`, *every* evaluation domain
`D : ι ↪ F` on *every* index set of size `n ≥ 3`, and the high-rate Reed–Solomon code
`C = RS[F, D, n−2]` (rate `(n−2)/n`, distance 3):

  `mcaDeltaStar(C, ε*) = 1/n`  **exactly**, for every `ε* ∈ [1/q, 2/q)`.

`1/n` is simultaneously the granularity radius and the unique-decoding radius
`(1−ρ)/2 = 1/n` of this family: the theorem says the MCA threshold of high-rate RS codes
sits *exactly at unique decoding* for error targets in the natural band, over every field
and every domain — no smoothness, no field-size condition beyond the band being nonempty.

## The two certificates (the S2 `certificates-meet` pattern, executed)

* **Good side** — the sub-unit collapse (`epsMCA_le_inv_card_of_small_radius`, R1's
  general brick): `δ·n < 1` forces a single witness set and at most one bad scalar, so
  `ε_mca(C, δ) ≤ 1/q ≤ ε*` for every `δ < 1/n`.
* **Bad side** — the indicator-pair stack `(𝟙_{b₂}, 𝟙_{b₁,b₂})`: at `δ = 1/n` both
  `γ = 0` (witness `univ \ {b₂}`) and `γ = −1` (witness `univ \ {b₁}`) fire `mcaEvent` —
  the zero codeword matches the line, while any joint explanation would give a
  degree-`< n−2` polynomial vanishing at `n−2` points yet equal to `1` somewhere
  (`rs_vanish_forced_zero`). Hence `ε_mca(C, 1/n) ≥ 2/q > ε*`.

The jump-pin engine (`mcaDeltaStar_eq_of_jump`, S2) closes the sandwich. Note the bad
scalars `{0, −1}` are distinct in **every** field (including characteristic 2, where the
set is `{0, 1}`).

As a corollary, the **n = 8 exact rung** the campaign queued: `RS[F₁₇, ⟨2⟩, 6]` on the
smooth order-8 subgroup of `F₁₇ˣ` has `mcaDeltaStar = 1/8` at `ε* = 1/17`
(`mcaDeltaStar_rs17_eq_eighth`).

Honest scope note: `1/n` is the *unique-decoding* radius of this family — the window
`(1−√ρ, 1−ρ)` of the open core is not touched; what this theorem contributes is the first
infinite-family exactness data point for the certificate-gap programme, and the
field/domain-universality of the high-rate jump.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`, no `native_decide`.

## References

- Issue #357 (campaign round 2); [ABF26] ePrint 2026/680.
-/

set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code
open ProximityGap.MCAThresholdLedger ProximityGap.MCAWitnessSpread
open ProximityGap.MCAListBracketInterpolation ProximityGap.MCADeltaStarExactPoint

namespace ProximityGap.MCADeltaStarHighRateFamily

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## The vanishing-forces-zero brick -/

/-- A Reed–Solomon codeword of degree bound `k` vanishing on `k` coordinates is zero. -/
theorem rs_vanish_forced_zero (domain : ι ↪ F) {k : ℕ} {v : ι → F}
    (hv : v ∈ ReedSolomon.code domain k) {T : Finset ι} (hT : k ≤ T.card)
    (hvan : ∀ i ∈ T, v i = 0) : v = 0 := by
  rw [ReedSolomon.mem_code_iff_exists_polynomial] at hv
  obtain ⟨p, hdeg, rfl⟩ := hv
  rcases eq_or_ne p 0 with rfl | hp0
  · funext i
    simp [ReedSolomon.evalOnPoints]
  · exfalso
    have hzero : p = 0 := by
      apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p (T.image domain)
      · intro x hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        exact hvan i hi
      · rw [Finset.card_image_of_injective T domain.injective]
        exact lt_of_lt_of_le ((Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hdeg) hT
    exact hp0 hzero

/-! ## The indicator-pair bad stack -/

/-- `u₀ = 𝟙_{b₂}`. -/
def ind1 (b₂ : ι) : ι → F := fun i => if i = b₂ then 1 else 0

/-- `u₁ = 𝟙_{b₁, b₂}`. -/
def ind2 (b₁ b₂ : ι) : ι → F := fun i => if i = b₁ ∨ i = b₂ then 1 else 0

/-- The witness-size arithmetic at the jump radius: `(1 − 1/n)·n = n − 1` in `ℝ≥0`. -/
theorem card_clause_arith {n : ℕ} (hn : 0 < n) :
    ((1 : ℝ≥0) - 1 / (n : ℝ≥0)) * (n : ℝ≥0) = ((n - 1 : ℕ) : ℝ≥0) := by
  have hne : (n : ℝ≥0) ≠ 0 := by exact_mod_cast hn.ne'
  have hinv : (1 / (n : ℝ≥0)) * (n : ℝ≥0) = 1 := by
    rw [one_div, inv_mul_cancel₀ hne]
  have h1 : ((n - 1 : ℕ) : ℝ≥0) + 1 = (n : ℝ≥0) := by
    exact_mod_cast Nat.succ_pred_eq_of_pos hn
  rw [tsub_mul, one_mul, hinv, ← h1, add_tsub_cancel_right]

/-- The erased-point witness set meets the size clause at `δ = 1/n`. -/
theorem erase_card_clause (b : ι) :
    ((Finset.univ.erase b).card : ℝ≥0)
      ≥ ((1 : ℝ≥0) - 1 / (Fintype.card ι : ℝ≥0)) * (Fintype.card ι : ℝ≥0) := by
  rw [card_clause_arith Fintype.card_pos, Finset.card_erase_of_mem (Finset.mem_univ b),
    Finset.card_univ]

/-- **`mcaEvent` fires at `γ = 0`** on the indicator-pair stack, at radius `1/n`, for the
high-rate code: witness `univ \ {b₂}`, zero codeword, and no joint explanation (a joint
second row would vanish at `n−2` points yet equal `1` at `b₁`). -/
theorem mcaEvent_highRate_zero (domain : ι ↪ F) {k : ℕ}
    (hk : k ≤ Fintype.card ι - 2)
    {b₁ b₂ : ι} (hb : b₁ ≠ b₂) :
    mcaEvent (F := F)
      (ReedSolomon.code domain k : Set (ι → F))
      (1 / (Fintype.card ι : ℝ≥0)) (ind1 b₂) (ind2 b₁ b₂) (0 : F) := by
  refine ⟨Finset.univ.erase b₂, erase_card_clause b₂,
    ⟨0, (ReedSolomon.code domain k).zero_mem, ?_⟩, ?_⟩
  · intro i hi
    have hib : i ≠ b₂ := (Finset.mem_erase.mp hi).1
    simp [ind1, ind2, hib]
  · rintro ⟨v₀, hv₀, v₁, hv₁, hag⟩
    -- the second row is forced to vanish at the `n−2` points away from `b₁, b₂`
    have hvan : ∀ i ∈ (Finset.univ.erase b₂).erase b₁, v₁ i = 0 := by
      intro i hi
      obtain ⟨hib1, hi2⟩ := Finset.mem_erase.mp hi
      have hib2 : i ≠ b₂ := (Finset.mem_erase.mp hi2).1
      have h := (hag i hi2).2
      rw [ind2] at h
      simpa [hib1, hib2] using h
    have hcard : k ≤ ((Finset.univ.erase b₂).erase b₁).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b₁⟩),
        Finset.card_erase_of_mem (Finset.mem_univ b₂), Finset.card_univ]
      omega
    have hv1zero : v₁ = 0 := rs_vanish_forced_zero domain hv₁ hcard hvan
    -- but the second row equals `1` at `b₁ ∈ S`
    have hb1S : b₁ ∈ Finset.univ.erase b₂ := Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b₁⟩
    have h1 := (hag b₁ hb1S).2
    rw [hv1zero, ind2] at h1
    simp at h1

/-- **`mcaEvent` fires at `γ = −1`** on the indicator-pair stack: witness `univ \ {b₁}`,
the line `𝟙_{b₂} − 𝟙_{b₁,b₂} = −𝟙_{b₁}` vanishes there, and a joint second row would
vanish at `n−2` points yet equal `1` at `b₂`. -/
theorem mcaEvent_highRate_negOne (domain : ι ↪ F) {k : ℕ}
    (hk : k ≤ Fintype.card ι - 2)
    {b₁ b₂ : ι} (hb : b₁ ≠ b₂) :
    mcaEvent (F := F)
      (ReedSolomon.code domain k : Set (ι → F))
      (1 / (Fintype.card ι : ℝ≥0)) (ind1 b₂) (ind2 b₁ b₂) (-1 : F) := by
  refine ⟨Finset.univ.erase b₁, erase_card_clause b₁,
    ⟨0, (ReedSolomon.code domain k).zero_mem, ?_⟩, ?_⟩
  · intro i hi
    have hib : i ≠ b₁ := (Finset.mem_erase.mp hi).1
    by_cases h2 : i = b₂
    · subst h2
      simp [ind1, ind2, hib]
    · simp [ind1, ind2, hib, h2]
  · rintro ⟨v₀, hv₀, v₁, hv₁, hag⟩
    have hvan : ∀ i ∈ (Finset.univ.erase b₁).erase b₂, v₁ i = 0 := by
      intro i hi
      obtain ⟨hib2, hi1⟩ := Finset.mem_erase.mp hi
      have hib1 : i ≠ b₁ := (Finset.mem_erase.mp hi1).1
      have h := (hag i hi1).2
      rw [ind2] at h
      simpa [hib1, hib2] using h
    have hcard : k ≤ ((Finset.univ.erase b₁).erase b₂).card := by
      rw [Finset.card_erase_of_mem
          (Finset.mem_erase.mpr ⟨hb.symm, Finset.mem_univ b₂⟩),
        Finset.card_erase_of_mem (Finset.mem_univ b₁), Finset.card_univ]
      omega
    have hv1zero : v₁ = 0 := rs_vanish_forced_zero domain hv₁ hcard hvan
    have hb2S : b₂ ∈ Finset.univ.erase b₁ :=
      Finset.mem_erase.mpr ⟨hb.symm, Finset.mem_univ b₂⟩
    have h1 := (hag b₂ hb2S).2
    rw [hv1zero, ind2] at h1
    simp at h1

/-- The indicator-pair stack. -/
def indStack (b₁ b₂ : ι) : WordStack F (Fin 2) ι :=
  fun k => if k = 0 then ind1 b₂ else ind2 b₁ b₂

/-- **The bad half: `ε_mca(RS[F, D, n−2], 1/n) ≥ 2/q`** — two bad scalars, every field,
every domain. -/
theorem epsMCA_highRate_ge (domain : ι ↪ F) {k : ℕ}
    (hk : k ≤ Fintype.card ι - 2)
    {b₁ b₂ : ι} (hb : b₁ ≠ b₂) :
    (2 : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
      ≤ epsMCA (F := F) (A := F)
          (ReedSolomon.code domain k : Set (ι → F))
          (1 / (Fintype.card ι : ℝ≥0)) := by
  classical
  have hne : (0 : F) ∉ ({-1} : Finset F) := by
    rw [Finset.mem_singleton]
    intro h
    have : (1 : F) = 0 := by linear_combination h
    exact one_ne_zero this
  have h := epsMCA_ge_card_div_of_mcaEvent_set (F := F) (A := F)
    (ReedSolomon.code domain k : Set (ι → F))
    (1 / (Fintype.card ι : ℝ≥0)) (indStack b₁ b₂) ({0, -1} : Finset F) (by
      intro γ hγ
      rw [Finset.mem_insert, Finset.mem_singleton] at hγ
      have h0 : indStack (F := F) b₁ b₂ 0 = ind1 b₂ := rfl
      have h1 : indStack (F := F) b₁ b₂ 1 = ind2 b₁ b₂ := by
        show (if (1 : Fin 2) = 0 then ind1 b₂ else ind2 b₁ b₂) = ind2 b₁ b₂
        norm_num
      rw [h0, h1]
      rcases hγ with rfl | rfl
      · exact mcaEvent_highRate_zero domain hk hb
      · exact mcaEvent_highRate_negOne domain hk hb)
  have hcard : ({0, -1} : Finset F).card = 2 := by
    rw [Finset.card_insert_of_notMem hne, Finset.card_singleton]
  rwa [hcard] at h

/-! ## The family theorem -/

/-- **THE FIRST EXACT `δ*` THEOREM FOR AN INFINITE FAMILY.**

For every finite field `F`, every evaluation domain `D : ι ↪ F` with `n = |ι| ≥ 3`,
**every degree bound `k ≤ n − 2`**, and every error target `ε* ∈ [1/q, 2/q)`:

  `mcaDeltaStar(RS[F, D, k], ε*) = 1/n`  **exactly**.

At the tightest nontrivial error band the MCA threshold of *every* Reed–Solomon code with
distance `≥ 3` sits exactly at the granularity radius `1/n` — which for the high-rate
member `k = n − 2` is also its unique-decoding radius `(1−ρ)/2`. Certified on both sides:
the sub-unit collapse below, the indicator-pair two-scalar stack at the radius. (The
red-team probe at `F₇, D = (1,…,5)` confirms both brackets exhaustively, and shows the
two-scalar bad side is *tight* for `k < n−2` while `k = n−2` carries `n` bad scalars —
the flat-`n` law.) -/
theorem mcaDeltaStar_rs_eq_inv_card (domain : ι ↪ F) {k : ℕ}
    (hk : k ≤ Fintype.card ι - 2)
    {b₁ b₂ : ι} (hb : b₁ ≠ b₂) {εstar : ℝ≥0∞}
    (hlo : 1 / (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (hhi : εstar < 2 / (Fintype.card F : ℝ≥0∞)) :
    mcaDeltaStar (F := F) (A := F)
        (ReedSolomon.code domain k : Set (ι → F)) εstar
      = 1 / (Fintype.card ι : ℝ≥0) := by
  have hnpos : (0 : ℝ≥0) < (Fintype.card ι : ℝ≥0) := by
    exact_mod_cast Fintype.card_pos
  apply mcaDeltaStar_eq_of_jump
  · -- `1/n ≤ 1`
    rw [div_le_one hnpos]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr Fintype.card_ne_zero
  · -- good below the jump: the sub-unit collapse
    intro δ hδ
    have hδn : δ * (Fintype.card ι : ℝ≥0) < 1 := by
      have h := mul_lt_mul_of_pos_right hδ hnpos
      rwa [one_div, inv_mul_cancel₀ (ne_of_gt hnpos)] at h
    exact le_trans
      (epsMCA_le_inv_card_of_small_radius
        (ReedSolomon.code domain k) hδn) hlo
  · -- bad at the jump: two scalars
    exact lt_of_lt_of_le hhi (epsMCA_highRate_ge domain hk hb)

/-- The high-rate (unique-decoding-radius) member: `δ*(RS[F, D, n−2], ε*) = 1/n = (1−ρ)/2`. -/
theorem mcaDeltaStar_rs_highRate_eq (domain : ι ↪ F) (hn : 3 ≤ Fintype.card ι)
    {b₁ b₂ : ι} (hb : b₁ ≠ b₂) {εstar : ℝ≥0∞}
    (hlo : 1 / (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (hhi : εstar < 2 / (Fintype.card F : ℝ≥0∞)) :
    mcaDeltaStar (F := F) (A := F)
        (ReedSolomon.code domain (Fintype.card ι - 2) : Set (ι → F)) εstar
      = 1 / (Fintype.card ι : ℝ≥0) :=
  mcaDeltaStar_rs_eq_inv_card domain le_rfl hb hlo hhi

/-- Existence form: any index type of size `≥ 3` supplies the two marked positions. -/
theorem mcaDeltaStar_rs_highRate_eq' (domain : ι ↪ F) (hn : 3 ≤ Fintype.card ι)
    {εstar : ℝ≥0∞} (hlo : 1 / (Fintype.card F : ℝ≥0∞) ≤ εstar)
    (hhi : εstar < 2 / (Fintype.card F : ℝ≥0∞)) :
    mcaDeltaStar (F := F) (A := F)
        (ReedSolomon.code domain (Fintype.card ι - 2) : Set (ι → F)) εstar
      = 1 / (Fintype.card ι : ℝ≥0) := by
  have h1 : 1 < Fintype.card ι := by omega
  obtain ⟨b₁, b₂, hb⟩ := Fintype.exists_pair_of_one_lt_card h1
  exact mcaDeltaStar_rs_highRate_eq domain hn hb hlo hhi

/-! ## The n = 8 smooth rung -/

section Rung8

instance primeFact_MCADeltaStarHighRateFamily_1 : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- The smooth order-8 subgroup of `F₁₇ˣ`: powers of `2`. -/
def gdom8 : Fin 8 → ZMod 17 := ![1, 2, 4, 8, 16, 15, 13, 9]

theorem gdom8_injective : Function.Injective gdom8 := by decide

/-- The domain embedding for the n = 8 rung. -/
def domain8 : Fin 8 ↪ ZMod 17 := ⟨gdom8, gdom8_injective⟩

/-- **The n = 8 exact rung**: the high-rate code on the smooth order-8 subgroup of
`F₁₇ˣ` has `mcaDeltaStar = 1/8` exactly at `ε* = 1/17`. The campaign's queued second
exact point, delivered by the family theorem. -/
theorem mcaDeltaStar_rs17_eq_eighth :
    mcaDeltaStar (F := ZMod 17) (A := ZMod 17)
        (ReedSolomon.code domain8 6 : Set (Fin 8 → ZMod 17))
        (1 / (17 : ℝ≥0∞))
      = 1 / 8 := by
  have hF : ((Fintype.card (ZMod 17) : ℕ) : ℝ≥0∞) = 17 := by
    rw [ZMod.card]
    norm_num
  have h := mcaDeltaStar_rs_highRate_eq' (F := ZMod 17) domain8
    (by simp) (εstar := 1 / (17 : ℝ≥0∞))
    (by rw [hF])
    (by
      rw [hF, ENNReal.div_lt_iff (by norm_num) (by norm_num),
        ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
      norm_num)
  simpa using h

end Rung8

/-! ## Source audit -/

#print axioms rs_vanish_forced_zero
#print axioms mcaEvent_highRate_zero
#print axioms mcaEvent_highRate_negOne
#print axioms epsMCA_highRate_ge
#print axioms mcaDeltaStar_rs_eq_inv_card
#print axioms mcaDeltaStar_rs_highRate_eq
#print axioms mcaDeltaStar_rs_highRate_eq'
#print axioms mcaDeltaStar_rs17_eq_eighth

end ProximityGap.MCADeltaStarHighRateFamily
