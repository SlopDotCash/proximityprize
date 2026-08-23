/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCADeltaStarExactPoint

/-!
# Round 2 (#357): the band-2 collapse — `ε_mca ≤ 2/|F|` on `[1/n, 2/n)` for distance `≥ 4`

The band-2 probe campaign (12 instances, exact via the syndrome/coset licence) discovered a
**trichotomy** for the second step of the MCA staircase, the band `δ·n < 2` where witness
sets have `≥ n−1` points:

| `n − k` (distance `d = n−k+1`) | max bad scalars per stack |
|---|---|
| `1` (`d = 2`) | `1` — the staircase has **no jump** at the granularity radius |
| `2` (`d = 3`) | `n` — the R1 phenomenon, **field-independent** (`5, 7, 13` all give `n`) |
| `≥ 3` (`d ≥ 4`) | `2` — **collapse to the spike value** |

This file proves the collapse row as a general theorem — for **every** linear code with no
nonzero codeword supported on `≤ 3` points (minimum distance `≥ 4`):

* `badScalar_card_le_two_of_dist4` — every stack has at most `2` bad scalars at every
  radius with `δ·n < 2`;
* `epsMCA_le_two_div_card_of_dist4` — hence `ε_mca(C, δ) ≤ 2/|F|` on the whole band.

This sharpens the canonical-witness window bound (`epsMCA_le_choose_div`, `C(n,n−1)/q = n/q`
on this band) by a factor of `n/2`, and the in-tree spike lower bound reaches `2/q` here, so
the value is **tight**. Together with the sub-granularity band (R1's
`epsMCA_eq_inv_card_of_small_radius`): the first two steps of the MCA staircase are now
controlled for every linear code of distance `≥ 4` — including the production-scale
Reed–Solomon codes of the prize statement.

**The mechanism** (why three bad scalars are impossible). At most one scalar's line point
can itself be a codeword (`pairJoint_of_two_codeword_points`); a non-codeword bad scalar's
witness is exactly a punctured universe (`extract_puncture`), and two such scalars cannot
share a puncture (`pairJoint_of_shared_witness`). Three bad scalars therefore give three
agreement families off pairwise-distinct punctures `i_a, i_b, i_c`. The combination

  `c* := (γ_a−γ_c) • (w_a − w_b) − (γ_a−γ_b) • (w_a − w_c) ∈ C`

telescopes to `0` off `{i_a, i_b, i_c}`; by the distance hypothesis `c* = 0` everywhere.
Evaluating at `i_b` (where `w_a, w_c` still agree with their lines) solves for
`w_b i_b = u₀ i_b + γ_b • u₁ i_b` — the agreement of `w_b` extends across its own puncture,
so the line point at `γ_b` is a codeword after all: contradiction. ∎

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- Issue #357 (the δ* campaign; round 2 — the staircase program); the band-2 probe campaign
  (pre-registered trichotomy, 12 instances).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code

namespace ProximityGap.MCABandTwoCollapse

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- Distance-`≥ 4` hypothesis, support form: no nonzero codeword is supported on `≤ 3`
points. -/
def NoLowWeight (C : Submodule F (ι → A)) : Prop :=
  ∀ w ∈ C, (∃ T : Finset ι, T.card ≤ 3 ∧ ∀ i ∉ T, w i = 0) → w = 0

/-- **Shared witness ⟹ joint explanation.** If two distinct scalars' lines agree with
codewords on the same set `S`, the pair is jointly explained on `S`. -/
theorem pairJoint_of_shared_witness (C : Submodule F (ι → A)) {γ γ' : F} (hne : γ ≠ γ')
    {u₀ u₁ : ι → A} {S : Finset ι} {w w' : ι → A} (hw : w ∈ C) (hw' : w' ∈ C)
    (hag : ∀ i ∈ S, w i = u₀ i + γ • u₁ i) (hag' : ∀ i ∈ S, w' i = u₀ i + γ' • u₁ i) :
    pairJointAgreesOn (C : Set (ι → A)) S u₀ u₁ := by
  have hv₁mem : (γ - γ')⁻¹ • (w - w') ∈ C := C.smul_mem _ (C.sub_mem hw hw')
  have hv₁ag : ∀ i ∈ S, ((γ - γ')⁻¹ • (w - w')) i = u₁ i := by
    intro i hi
    show (γ - γ')⁻¹ • (w i - w' i) = u₁ i
    rw [hag i hi, hag' i hi, add_sub_add_left_eq_sub, ← sub_smul, smul_smul,
      inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul]
  refine ⟨w - γ • ((γ - γ')⁻¹ • (w - w')),
    C.sub_mem hw (C.smul_mem γ hv₁mem), (γ - γ')⁻¹ • (w - w'), hv₁mem,
    fun i hi => ⟨?_, hv₁ag i hi⟩⟩
  show w i - γ • (((γ - γ')⁻¹ • (w - w')) i) = u₀ i
  rw [show ((γ - γ')⁻¹ • (w - w')) i = u₁ i from hv₁ag i hi, hag i hi, add_sub_cancel_right]

/-- **Two codeword line points ⟹ joint explanation on every set.** -/
theorem pairJoint_of_two_codeword_points (C : Submodule F (ι → A)) {γ γ' : F}
    (hne : γ ≠ γ') {u₀ u₁ : ι → A}
    (hy : (u₀ + γ • u₁) ∈ C) (hy' : (u₀ + γ' • u₁) ∈ C) (S : Finset ι) :
    pairJointAgreesOn (C : Set (ι → A)) S u₀ u₁ := by
  have hu₁ : u₁ ∈ C := by
    have hsub : (γ - γ') • u₁ ∈ C := by
      have h := C.sub_mem hy hy'
      rwa [add_sub_add_left_eq_sub, ← sub_smul] at h
    have h := C.smul_mem (γ - γ')⁻¹ hsub
    rwa [inv_smul_smul₀ (sub_ne_zero.mpr hne)] at h
  have hu₀ : u₀ ∈ C := by
    have h := C.sub_mem hy (C.smul_mem γ hu₁)
    rwa [add_sub_cancel_right] at h
  exact ⟨u₀, hu₀, u₁, hu₁, fun i _ => ⟨rfl, rfl⟩⟩

/-- **Band-2 witnesses contain a punctured universe**: some `i` has `univ \ {i} ⊆ S`.
Requires `3 ≤ n` for the numeric step. -/
theorem witness_puncture (hn : 3 ≤ Fintype.card ι) {δ : ℝ≥0}
    (hδ : δ * (Fintype.card ι : ℝ≥0) < 2) {S : Finset ι}
    (hS : (S.card : ℝ≥0) ≥ (1 - δ) * (Fintype.card ι : ℝ≥0)) :
    ∃ i : ι, ∀ j : ι, j ≠ i → j ∈ S := by
  by_cases huniv : S = Finset.univ
  · obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    exact ⟨i, fun j _ => huniv ▸ Finset.mem_univ j⟩
  obtain ⟨i, hi⟩ : ∃ i, i ∉ S := by
    by_contra h
    push Not at h
    exact huniv (Finset.eq_univ_of_forall h)
  refine ⟨i, fun j hji => ?_⟩
  by_contra hjS
  have hsub : S ⊆ (Finset.univ.erase i).erase j := fun x hx =>
    Finset.mem_erase.mpr ⟨fun h => hjS (h ▸ hx),
      Finset.mem_erase.mpr ⟨fun h => hi (h ▸ hx), Finset.mem_univ x⟩⟩
  have hcard2 : S.card ≤ Fintype.card ι - 2 := by
    have h1 := Finset.card_le_card hsub
    have h2 : ((Finset.univ.erase i).erase j).card = Fintype.card ι - 2 := by
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩),
        Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
      omega
    omega
  have hδ1 : δ < 1 := by
    by_contra hge
    push Not at hge
    have h3 : (3 : ℝ≥0) ≤ (Fintype.card ι : ℝ≥0) := by exact_mod_cast hn
    have h2lt : (2 : ℝ≥0) < δ * (Fintype.card ι : ℝ≥0) := by
      calc (2 : ℝ≥0) < 3 := by norm_num
        _ ≤ (Fintype.card ι : ℝ≥0) := h3
        _ = 1 * (Fintype.card ι : ℝ≥0) := (one_mul _).symm
        _ ≤ δ * (Fintype.card ι : ℝ≥0) := by gcongr
    exact absurd hδ (not_lt.mpr h2lt.le)
  have hSR : ((1 : ℝ) - δ) * (Fintype.card ι : ℝ) ≤ (S.card : ℝ) := by
    have hcast : ((1 - δ : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ) ≤ (S.card : ℝ) := by
      exact_mod_cast hS
    rwa [NNReal.coe_sub hδ1.le, NNReal.coe_one] at hcast
  have hδR : (δ : ℝ) * (Fintype.card ι : ℝ) < 2 := by exact_mod_cast hδ
  have hc2 : (S.card : ℝ) ≤ (Fintype.card ι : ℝ) - 2 := by
    have hn2 : 2 ≤ Fintype.card ι := by omega
    have hcast : (S.card : ℝ) ≤ ((Fintype.card ι - 2 : ℕ) : ℝ) := by exact_mod_cast hcard2
    rwa [Nat.cast_sub hn2] at hcast
  nlinarith

/-- **Puncture extraction.** A bad scalar whose line point is *not* a codeword has a
witness of the exact form `univ \ {i}`: a codeword agreeing off `i`, and no joint
explanation on `univ \ {i}`. -/
theorem extract_puncture (C : Submodule F (ι → A)) (hn : 3 ≤ Fintype.card ι) {δ : ℝ≥0}
    (hδ : δ * (Fintype.card ι : ℝ≥0) < 2) {u₀ u₁ : ι → A} {γ : F}
    (hev : mcaEvent (F := F) (C : Set (ι → A)) δ u₀ u₁ γ)
    (hY : (u₀ + γ • u₁) ∉ C) :
    ∃ (i : ι) (w : ι → A), w ∈ C ∧ (∀ j : ι, j ≠ i → w j = u₀ j + γ • u₁ j) ∧
      ¬ pairJointAgreesOn (C : Set (ι → A)) (Finset.univ.erase i) u₀ u₁ := by
  obtain ⟨S, hS, ⟨w, hw, hag⟩, hno⟩ := hev
  obtain ⟨i, hi⟩ := witness_puncture hn hδ hS
  have hoff : ∀ j : ι, j ≠ i → w j = u₀ j + γ • u₁ j := fun j hj => hag j (hi j hj)
  -- i itself is not in S: otherwise S = univ and the line point is a codeword
  have hiS : i ∉ S := by
    intro hiS
    apply hY
    have hall : ∀ j, w j = u₀ j + γ • u₁ j := by
      intro j
      by_cases hj : j = i
      · rw [hj]; exact hag i hiS
      · exact hoff j hj
    have heq : u₀ + γ • u₁ = w := by
      funext j
      show u₀ j + γ • u₁ j = w j
      exact (hall j).symm
    rw [heq]
    exact hw
  -- S ⊆ univ.erase i, so the non-explanation transfers up to univ.erase i?  No:
  -- ¬pairJoint is anti-monotone in the wrong direction; but S ⊆ univ.erase i means a
  -- joint explanation on univ.erase i would restrict to one on S.
  have hsub : S ⊆ Finset.univ.erase i := fun x hx =>
    Finset.mem_erase.mpr ⟨fun h => hiS (h ▸ hx), Finset.mem_univ x⟩
  refine ⟨i, w, hw, hoff, fun hpj => ?_⟩
  obtain ⟨v₀, hv₀, v₁, hv₁, hagv⟩ := hpj
  exact hno ⟨v₀, hv₀, v₁, hv₁, fun j hj => hagv j (hsub hj)⟩

open Classical in
/-- **The band-2 collapse:** for a code with no nonzero codeword on `≤ 3` points (distance
`≥ 4`), every stack has at most `2` bad scalars at every radius with `δ·n < 2`. -/
theorem badScalar_card_le_two_of_dist4 (C : Submodule F (ι → A)) (hC : NoLowWeight C)
    (hn : 3 ≤ Fintype.card ι) {δ : ℝ≥0} (hδ : δ * (Fintype.card ι : ℝ≥0) < 2)
    (u : WordStack A (Fin 2) ι) :
    (Finset.filter (fun γ : F =>
        mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) γ) Finset.univ).card ≤ 2 := by
  by_contra hgt
  push Not at hgt
  obtain ⟨γ₁, γ₂, γ₃, hγ₁, hγ₂, hγ₃, h12, h13, h23⟩ := Finset.two_lt_card_iff.mp hgt
  rw [Finset.mem_filter] at hγ₁ hγ₂ hγ₃
  -- at most one of the three line points is a codeword
  have hUmax : ∀ γ γ' : F, γ ≠ γ' →
      mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) γ →
      (u 0 + γ • u 1) ∈ C → (u 0 + γ' • u 1) ∈ C → False := by
    intro γ γ' hne hev hy hy'
    obtain ⟨S, _, _, hno⟩ := hev
    exact hno (pairJoint_of_two_codeword_points C hne hy hy' S)
  -- two distinct non-codeword bad scalars cannot share a puncture
  have hdistinct : ∀ {γ γ' : F} {i : ι} {w w' : ι → A}, γ ≠ γ' → w ∈ C → w' ∈ C →
      (∀ j : ι, j ≠ i → w j = u 0 j + γ • u 1 j) →
      (∀ j : ι, j ≠ i → w' j = u 0 j + γ' • u 1 j) →
      ¬ pairJointAgreesOn (C : Set (ι → A)) (Finset.univ.erase i) (u 0) (u 1) → False := by
    intro γ γ' i w w' hne hw hw' hoff hoff' hno
    exact hno (pairJoint_of_shared_witness C hne hw hw'
      (fun j hj => hoff j (Finset.mem_erase.mp hj).1)
      (fun j hj => hoff' j (Finset.mem_erase.mp hj).1))
  -- THE CORE: three distinct bad scalars, two of which (b, c) are non-codeword type
  have core : ∀ ga gb gc : F, ga ≠ gb → ga ≠ gc → gb ≠ gc →
      mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) ga →
      mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) gb →
      mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) gc →
      (u 0 + gb • u 1) ∉ C → (u 0 + gc • u 1) ∉ C → False := by
    intro ga gb gc hab hac hbc heva hevb hevc hYb hYc
    obtain ⟨ib, wb, hwb, hoffb, hnob⟩ := extract_puncture C hn hδ hevb hYb
    obtain ⟨ic, wc, hwc, hoffc, hnoc⟩ := extract_puncture C hn hδ hevc hYc
    have hibc : ib ≠ ic := by
      rintro rfl
      exact hdistinct hbc hwb hwc hoffb hoffc hnob
    -- data for a: either its line point is a codeword (agreement everywhere), or extract
    obtain ⟨ia, wa, hwa, hoffa, hia_b, hia_c⟩ :
        ∃ (ia : ι) (wa : ι → A), wa ∈ C ∧
          (∀ j : ι, j ≠ ia → wa j = u 0 j + ga • u 1 j) ∧ ia ≠ ib ∧ ia ≠ ic := by
      by_cases hYa : (u 0 + ga • u 1) ∈ C
      · -- pick a fresh point: agreements hold everywhere anyway
        obtain ⟨ia, hia⟩ : ∃ i : ι, i ≠ ib ∧ i ≠ ic := by
          by_contra h
          push Not at h
          have hsub : (Finset.univ : Finset ι) ⊆ {ib, ic} := fun x _ => by
            rcases Classical.em (x = ib) with hx | hx
            · exact Finset.mem_insert.mpr (Or.inl hx)
            · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (h x hx)))
          have hle := Finset.card_le_card hsub
          rw [Finset.card_univ] at hle
          have h2 : ({ib, ic} : Finset ι).card ≤ 2 :=
            le_trans (Finset.card_insert_le _ _) (by rw [Finset.card_singleton])
          omega
        exact ⟨ia, u 0 + ga • u 1, hYa, fun j _ => rfl, hia.1, hia.2⟩
      · obtain ⟨ia, wa, hwa, hoffa, hnoa⟩ := extract_puncture C hn hδ heva hYa
        have h1 : ia ≠ ib := by
          rintro rfl
          exact hdistinct hab hwa hwb hoffa hoffb hnoa
        have h2 : ia ≠ ic := by
          rintro rfl
          exact hdistinct hac hwa hwc hoffa hoffc hnoa
        exact ⟨ia, wa, hwa, hoffa, h1, h2⟩
    -- the codeword combination c*
    set cstar : ι → A := (ga - gc) • (wa - wb) - (ga - gb) • (wa - wc) with hcstar
    have hcmem : cstar ∈ C :=
      C.sub_mem (C.smul_mem _ (C.sub_mem hwa hwb)) (C.smul_mem _ (C.sub_mem hwa hwc))
    -- c* is supported on {ia, ib, ic}
    have hsupp : ∀ j ∉ ({ia, ib, ic} : Finset ι), cstar j = 0 := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      push Not at hj
      obtain ⟨hja, hjb, hjc⟩ := hj
      show (ga - gc) • (wa j - wb j) - (ga - gb) • (wa j - wc j) = 0
      rw [hoffa j hja, hoffb j hjb, hoffc j hjc]
      module
    -- the distance hypothesis kills it
    have hczero : cstar = 0 := hC cstar hcmem
      ⟨{ia, ib, ic}, le_trans (Finset.card_insert_le _ _)
        (by
          have : ({ib, ic} : Finset ι).card ≤ 2 :=
            le_trans (Finset.card_insert_le _ _) (by rw [Finset.card_singleton])
          omega), hsupp⟩
    -- evaluate at i_b: w_a and w_c still agree there
    have hz : (ga - gc) • (wa ib - wb ib) - (ga - gb) • (wa ib - wc ib) = 0 := by
      have h := congrFun hczero ib
      exact h
    rw [hoffa ib (Ne.symm hia_b), hoffc ib hibc] at hz
    -- solve for w_b i_b
    have hkey : wb ib = u 0 ib + gb • u 1 ib := by
      have hac0 : ga - gc ≠ 0 := sub_ne_zero.mpr hac
      have hXY : (ga - gc) • ((u 0 ib + ga • u 1 ib) - wb ib)
          = (ga - gc) • ((ga - gb) • u 1 ib) := by
        have hY : (ga - gb) • ((u 0 ib + ga • u 1 ib) - (u 0 ib + gc • u 1 ib))
            = (ga - gc) • ((ga - gb) • u 1 ib) := by module
        have hXeq := sub_eq_zero.mp hz
        rw [hY] at hXeq
        exact hXeq
      have hcanc := congrArg (fun x => (ga - gc)⁻¹ • x) hXY
      simp only [inv_smul_smul₀ hac0] at hcanc
      -- (u0 + ga•u1) − wb = (ga − gb)•u1  ⟹  wb = u0 + gb•u1
      have hwb_eq : wb ib = (u 0 ib + ga • u 1 ib) - (ga - gb) • u 1 ib := by
        rw [← hcanc]
        abel
      rw [hwb_eq]
      module
    -- the line point at γ_b is a codeword after all — contradiction
    apply hYb
    have hall : u 0 + gb • u 1 = wb := by
      funext j
      show u 0 j + gb • u 1 j = wb j
      by_cases hj : j = ib
      · rw [hj, hkey]
      · exact (hoffb j hj).symm
    rw [hall]
    exact hwb
  -- pigeonhole on codeword-type among the three scalars
  by_cases hY1 : (u 0 + γ₁ • u 1) ∈ C
  · by_cases hY2 : (u 0 + γ₂ • u 1) ∈ C
    · exact hUmax γ₁ γ₂ h12 hγ₁.2 hY1 hY2
    · by_cases hY3 : (u 0 + γ₃ • u 1) ∈ C
      · exact hUmax γ₁ γ₃ h13 hγ₁.2 hY1 hY3
      · exact core γ₁ γ₂ γ₃ h12 h13 h23 hγ₁.2 hγ₂.2 hγ₃.2 hY2 hY3
  · by_cases hY2 : (u 0 + γ₂ • u 1) ∈ C
    · by_cases hY3 : (u 0 + γ₃ • u 1) ∈ C
      · exact hUmax γ₂ γ₃ h23 hγ₂.2 hY2 hY3
      · exact core γ₂ γ₁ γ₃ (Ne.symm h12) h23 h13 hγ₂.2 hγ₁.2 hγ₃.2 hY1 hY3
    · exact core γ₃ γ₁ γ₂ (Ne.symm h13) (Ne.symm h23) h12 hγ₃.2 hγ₁.2 hγ₂.2 hY1 hY2

open Classical in
/-- **`ε_mca ≤ 2/|F|` on the whole band `δ·n < 2`**, for every linear code of distance
`≥ 4`: the second step of the MCA staircase collapses to the spike value. -/
theorem epsMCA_le_two_div_card_of_dist4 (C : Submodule F (ι → A)) (hC : NoLowWeight C)
    (hn : 3 ≤ Fintype.card ι) {δ : ℝ≥0} (hδ : δ * (Fintype.card ι : ℝ≥0) < 2) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ ≤ 2 / (Fintype.card F : ℝ≥0∞) := by
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  gcongr
  exact_mod_cast badScalar_card_le_two_of_dist4 C hC hn hδ u

/-! ## Source audit -/

#print axioms pairJoint_of_shared_witness
#print axioms pairJoint_of_two_codeword_points
#print axioms witness_puncture
#print axioms extract_puncture
#print axioms badScalar_card_le_two_of_dist4
#print axioms epsMCA_le_two_div_card_of_dist4

end ProximityGap.MCABandTwoCollapse
