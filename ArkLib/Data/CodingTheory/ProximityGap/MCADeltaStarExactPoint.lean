/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger
import ArkLib.Data.CodingTheory.ProximityGap.MCALowerBound

/-!
# R1 (#357): the first machine-checked exact `δ*` value — `mcaDeltaStar(RS[F₅, F₅ˣ, 2], 2/5) = 1/4`

The `δ*` campaign (#357) asks for the exact MCA threshold
`mcaDeltaStar C ε* = sSup {δ ≤ 1 | ε_mca(C, δ) ≤ ε*}` of explicit smooth-domain Reed–Solomon
codes. The literature only ever *bounds* `ε_mca`; no exact value of the threshold functional has
been certified for any code, by anyone, in any proof format. This file produces the first one,
at toy scale, for a **genuine smooth-domain RS code**: the full multiplicative group
`F₅ˣ = ⟨2⟩` (size `n = 4 = 2²`, a smooth domain) with dimension `k = 2`, i.e. rate `ρ = 1/2`
(a production rate). The result:

  `mcaDeltaStar (RS[F₅, ⟨2⟩, 2]) (2/5) = 1/4`.

The two halves, exactly as the bracket engine (`MCAThresholdLedger`) demands:

* **Good side — new general theory** (`epsMCA_le_inv_card_of_small_radius`): at any radius
  below the granularity `1/n`, the witness set in `mcaEvent` is forced to be all of `ι`; then
  two distinct bad scalars are *algebraically contradictory* for **every** linear code:
  subtracting the two on-line codewords gives `(γ−γ')•u₁ ∈ C`, hence `u₁ ∈ C`, hence
  `u₀ ∈ C`, hence the pair `(u₀, u₁)` is jointly explained on `univ` — contradiction. So each
  stack has at most one bad scalar and `ε_mca(C, δ) ≤ 1/|F|` with no computation at all. With
  the matching one-scalar witness (`epsMCA_eq_inv_card_of_small_radius`):
  **every proper linear code has `ε_mca(C, δ) = 1/|F|` exactly for `δ·n < 1`** — the exact
  MCA error of the sub-granularity regime, in full generality (generalizes
  `MCAZeroCodeExact.epsMCA_bot_eq_inv_card` from the zero code to all proper submodule codes).
* **Bad side — explicit witness spread** (`epsMCA_rs_quarter_ge`): the stack
  `u₀ = (0,0,0,1)`, `u₁ = (0,0,1,1)` over the domain enumeration `(1,2,4,3) = (2⁰,2¹,2²,2³)`
  has **four** of the five scalars bad at `δ = 1/4`, each with its own witness set varying
  with `γ` (as `MCAWitnessSpread.unique_bad_gamma_common_witness` mandates):
  `γ=0 ↦ S={0,1,2}`, `γ=2 ↦ S={0,2,3}`, `γ=3 ↦ S={1,2,3}`, `γ=4 ↦ S={0,1,3}`, so
  `ε_mca(C, 1/4) ≥ 4/5 > 2/5`.

Ground truth (exact-arithmetic probe, two independent engines, plus an in-session exhaustive
re-enumeration over all `5⁸` stacks): `ε_mca(C, δ)` is the step function `1/5` on `[0, 1/4)`
and `4/5` on `[1/4, 1]`, and the maximizing stack at `δ = 1/4` is exactly the one used here.
With `ε* = 2/5` (any `ε* ∈ [1/5, 4/5)` gives the same threshold): `mcaGoodRadii = [0, 1/4)`
and `δ* = 1/4` — note the supremum is **not attained** (`deltaStar_not_good`): `δ*` can sit at
a jump of `ε_mca`. At this scale and `ε*`, the pinned value `1/4 = (1−ρ)/2` is the
unique-decoding radius — the first data point of the "where in the window does `δ*` sit" curve.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- Issue #357 (the δ* campaign; hypothesis R1), [ABF26] ePrint 2026/680.
- Probe: `scripts/probes/probe_exact_epsmca_ladder.py` (syndrome-reduced exact `ε_mca`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code
open ProximityGap.MCAThresholdLedger

namespace ProximityGap.MCADeltaStarExactPoint

/-! ## Part 1 — general theory: the exact MCA error below the granularity radius -/

section General

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- Below the granularity radius (`δ·n < 1`), the `mcaEvent` witness-set size clause
`|S| ≥ (1−δ)·n` forces `S = univ`. -/
theorem witness_eq_univ_of_small_radius {δ : ℝ≥0}
    (hδ : δ * (Fintype.card ι : ℝ≥0) < 1) {S : Finset ι}
    (hS : (S.card : ℝ≥0) ≥ (1 - δ) * (Fintype.card ι : ℝ≥0)) :
    S = Finset.univ := by
  have hn1 : 1 ≤ Fintype.card ι := Fintype.card_pos
  -- δ < 1, so the truncated subtraction is honest
  have hδ1 : δ < 1 := by
    by_contra hge
    push Not at hge
    have : (1 : ℝ≥0) ≤ δ * (Fintype.card ι : ℝ≥0) := by
      calc (1 : ℝ≥0) = 1 * 1 := (one_mul 1).symm
        _ ≤ δ * (Fintype.card ι : ℝ≥0) := by
            exact mul_le_mul hge (by exact_mod_cast hn1) zero_le_one (zero_le δ)
    exact absurd hδ (not_lt.mpr this)
  -- move to ℝ
  have hSR : ((1 - δ : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ) ≤ (S.card : ℝ) := by
    exact_mod_cast hS
  rw [NNReal.coe_sub hδ1.le, NNReal.coe_one] at hSR
  have hδR : (δ : ℝ) * (Fintype.card ι : ℝ) < 1 := by exact_mod_cast hδ
  have hgt : (Fintype.card ι : ℝ) - 1 < (S.card : ℝ) := by nlinarith
  have hle : Fintype.card ι ≤ S.card := by
    have : (Fintype.card ι : ℝ) < (S.card : ℝ) + 1 := by linarith
    exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
  exact Finset.eq_univ_of_card S (le_antisymm (Finset.card_le_univ S) hle)

open Classical in
/-- **At most one bad scalar per stack, for every linear code, below the granularity radius.**
Two distinct bad scalars `γ ≠ γ'` both force their (univ) witness lines into `C`; subtracting
gives `(γ−γ')•u₁ ∈ C`, hence `u₁ ∈ C`, hence `u₀ ∈ C`, hence the pair is jointly explained on
`univ` — contradicting badness. Generalizes `MCAZeroCode.badScalar_card_le_one_bot` from the
zero code to arbitrary submodule codes. -/
theorem badScalar_card_le_one_of_small_radius (C : Submodule F (ι → A)) {δ : ℝ≥0}
    (hδ : δ * (Fintype.card ι : ℝ≥0) < 1) (u : WordStack A (Fin 2) ι) :
    (Finset.filter (fun γ : F =>
        mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) γ) Finset.univ).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro γ hγ γ' hγ'
  rw [Finset.mem_filter] at hγ hγ'
  obtain ⟨S, hS, ⟨w, hwmem, hweq⟩, hno⟩ := hγ.2
  obtain ⟨S', hS', ⟨w', hwmem', hweq'⟩, _⟩ := hγ'.2
  have hSuniv : S = Finset.univ := witness_eq_univ_of_small_radius hδ hS
  have hS'univ : S' = Finset.univ := witness_eq_univ_of_small_radius hδ hS'
  by_contra hne
  -- the two on-line codewords
  have hw_eq : w = u 0 + γ • u 1 := funext fun i => by
    rw [hweq i (hSuniv ▸ Finset.mem_univ i)]; rfl
  have hw'_eq : w' = u 0 + γ' • u 1 := funext fun i => by
    rw [hweq' i (hS'univ ▸ Finset.mem_univ i)]; rfl
  have m1 : u 0 + γ • u 1 ∈ C := hw_eq ▸ hwmem
  have m2 : u 0 + γ' • u 1 ∈ C := hw'_eq ▸ hwmem'
  -- subtract: (γ − γ')•u₁ ∈ C, hence u₁ ∈ C, hence u₀ ∈ C
  have hsub : (γ - γ') • u 1 ∈ C := by
    have h := C.sub_mem m1 m2
    rwa [add_sub_add_left_eq_sub, ← sub_smul] at h
  have hu1 : u 1 ∈ C := by
    have h := C.smul_mem (γ - γ')⁻¹ hsub
    rwa [inv_smul_smul₀ (sub_ne_zero.mpr hne)] at h
  have hu0 : u 0 ∈ C := by
    have h := C.sub_mem m1 (C.smul_mem γ hu1)
    rwa [add_sub_cancel_right] at h
  exact hno ⟨u 0, hu0, u 1, hu1, fun i _ => ⟨rfl, rfl⟩⟩

open Classical in
/-- **Upper half:** every linear code has `ε_mca(C, δ) ≤ 1/|F|` below the granularity radius. -/
theorem epsMCA_le_inv_card_of_small_radius (C : Submodule F (ι → A)) {δ : ℝ≥0}
    (hδ : δ * (Fintype.card ι : ℝ≥0) < 1) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ ≤ 1 / (Fintype.card F : ℝ≥0∞) := by
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  gcongr
  exact_mod_cast badScalar_card_le_one_of_small_radius C hδ u

open Classical in
/-- **The exact MCA error of the sub-granularity regime:** every **proper** linear code has
`ε_mca(C, δ) = 1/|F|` exactly, for every radius `δ` with `δ·n < 1`. The lower half fires
`mcaEvent` at `γ₀ = 1` on the stack `(c − v, v)` for `v ∉ C` — here with `c = 0`. -/
theorem epsMCA_eq_inv_card_of_small_radius (C : Submodule F (ι → A)) {δ : ℝ≥0}
    (hδ : δ * (Fintype.card ι : ℝ≥0) < 1) (hC : (C : Set (ι → A)) ≠ Set.univ) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ = 1 / (Fintype.card F : ℝ≥0∞) := by
  refine le_antisymm (epsMCA_le_inv_card_of_small_radius C hδ) ?_
  obtain ⟨v, hv⟩ : ∃ v, v ∉ (C : Set (ι → A)) := by
    by_contra h
    push Not at h
    exact hC (Set.eq_univ_of_forall h)
  refine epsMCA_ge_inv_card_of_mcaEvent (F := F) (A := A) (C : Set (ι → A)) δ
    ![-v, v] 1 ⟨Finset.univ, ?_, ⟨0, C.zero_mem, fun i _ => ?_⟩, ?_⟩
  · rw [Finset.card_univ]
    calc (1 - δ) * (Fintype.card ι : ℝ≥0) ≤ 1 * (Fintype.card ι : ℝ≥0) := by
          gcongr
          exact tsub_le_self
      _ = (Fintype.card ι : ℝ≥0) := one_mul _
  · show (0 : ι → A) i = (![-v, v] : WordStack A (Fin 2) ι) 0 i
      + (1 : F) • (![-v, v] : WordStack A (Fin 2) ι) 1 i
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  · rintro ⟨v₀, _hv₀, v₁, hv₁, hagree⟩
    apply hv
    have hv1eq : v₁ = v := funext fun i => (hagree i (Finset.mem_univ i)).2
    rwa [hv1eq] at hv₁

end General

/-! ## Part 2 — the concrete smooth-domain RS code `RS[F₅, ⟨2⟩, 2]` -/

section Concrete

abbrev F5 := ZMod 5

instance primeFact_MCADeltaStarExactPoint_1 : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The smooth evaluation domain: the full multiplicative group `F₅ˣ = ⟨2⟩` of size
`n = 4 = 2²`, enumerated as successive powers of the generator `2`. -/
def gdom : Fin 4 → F5 := ![1, 2, 4, 3]

/-- The domain really is the cyclic 2-power group `⟨2⟩`: `gdom i = 2^i`. -/
theorem gdom_powers : ∀ i : Fin 4, gdom i = 2 ^ (i : ℕ) := by decide

/-- The domain enumeration is injective (4 distinct points). -/
theorem gdom_injective : Function.Injective gdom := by decide

/-- `RS[F₅, ⟨2⟩, 2]`: evaluations of polynomials of degree `< 2` on the smooth domain.
Dimension `k = 2`, block length `n = 4`, rate `ρ = 1/2` (a production rate). -/
def rsC : Submodule F5 (Fin 4 → F5) where
  carrier := {w | ∃ a b : F5, ∀ i, w i = a + b * gdom i}
  add_mem' := by
    rintro w w' ⟨a, b, h⟩ ⟨a', b', h'⟩
    exact ⟨a + a', b + b', fun i => by
      show w i + w' i = _
      rw [h i, h' i]; ring⟩
  zero_mem' := ⟨0, 0, fun i => by simp⟩
  smul_mem' := by
    rintro c w ⟨a, b, h⟩
    exact ⟨c * a, c * b, fun i => by
      show c * w i = _
      rw [h i]; ring⟩

theorem mem_rsC_iff (w : Fin 4 → F5) :
    w ∈ (rsC : Set (Fin 4 → F5)) ↔ ∃ a b : F5, ∀ i, w i = a + b * gdom i := Iff.rfl

/-- The witness-spread stack (probe-discovered, the unique maximizer at `δ = 1/4`). -/
def u0 : Fin 4 → F5 := ![0, 0, 0, 1]

def u1 : Fin 4 → F5 := ![0, 0, 1, 1]

/-- The membership clause of `mcaEvent`'s witness sets at `δ = 1/4`, `n = 4`: card `3`
suffices (`(1 − 1/4) · 4 ≤ 3`). -/
theorem card_clause {S : Finset (Fin 4)} (hS : S.card = 3) :
    (S.card : ℝ≥0) ≥ ((1 : ℝ≥0) - 1/4) * (Fintype.card (Fin 4) : ℝ≥0) := by
  rw [hS, Fintype.card_fin]
  calc ((1 : ℝ≥0) - 1/4) * (4 : ℕ) ≤ (3/4 : ℝ≥0) * (4 : ℕ) := by
        gcongr
        exact tsub_le_iff_right.mpr (by norm_num)
    _ ≤ ((3 : ℕ) : ℝ≥0) := by
        push_cast
        norm_num

/-! ### The four bad scalars at `δ = 1/4`, each with its own witness set

`γ = 1` is the unique good scalar: the line point `(0,0,1,2)` agrees with no codeword on any
3-subset (probe-verified; not needed for the pin). -/

/-- `γ = 0`, witness `S = {0,1,2}`, on-line codeword `0`; no pair: `u₁` is not interpolable
on `S` (`a+b=0, a+2b=0 ⟹ a=b=0`, but `u₁` needs value `1` at `gdom 2 = 4`). -/
theorem mcaEvent_g0 :
    mcaEvent (F := F5) (rsC : Set (Fin 4 → F5)) (1/4) u0 u1 0 := by
  refine ⟨{0, 1, 2}, card_clause (by decide), ⟨0, rsC.zero_mem, by decide⟩, ?_⟩
  rintro ⟨v₀, _, v₁, ⟨a, b, h⟩, hagree⟩
  have e0 : a + b * gdom 0 = u1 0 := by rw [← h 0]; exact (hagree 0 (by decide)).2
  have e1 : a + b * gdom 1 = u1 1 := by rw [← h 1]; exact (hagree 1 (by decide)).2
  have e2 : a + b * gdom 2 = u1 2 := by rw [← h 2]; exact (hagree 2 (by decide)).2
  clear h
  revert e0 e1 e2
  revert a b
  decide

/-- `γ = 2`, witness `S = {0,2,3}`, on-line codeword `1 + 4·x`; no pair: `u₀` is not
interpolable on `S`. -/
theorem mcaEvent_g2 :
    mcaEvent (F := F5) (rsC : Set (Fin 4 → F5)) (1/4) u0 u1 2 := by
  refine ⟨{0, 2, 3}, card_clause (by decide),
    ⟨fun i => 1 + 4 * gdom i, ⟨1, 4, fun _ => rfl⟩, by decide⟩, ?_⟩
  rintro ⟨v₀, ⟨a, b, h⟩, v₁, _, hagree⟩
  have e0 : a + b * gdom 0 = u0 0 := by rw [← h 0]; exact (hagree 0 (by decide)).1
  have e2 : a + b * gdom 2 = u0 2 := by rw [← h 2]; exact (hagree 2 (by decide)).1
  have e3 : a + b * gdom 3 = u0 3 := by rw [← h 3]; exact (hagree 3 (by decide)).1
  clear h
  revert e0 e2 e3
  revert a b
  decide

/-- `γ = 3`, witness `S = {1,2,3}`, on-line codeword `2 + 4·x`; no pair: `u₀` is not
interpolable on `S`. -/
theorem mcaEvent_g3 :
    mcaEvent (F := F5) (rsC : Set (Fin 4 → F5)) (1/4) u0 u1 3 := by
  refine ⟨{1, 2, 3}, card_clause (by decide),
    ⟨fun i => 2 + 4 * gdom i, ⟨2, 4, fun _ => rfl⟩, by decide⟩, ?_⟩
  rintro ⟨v₀, ⟨a, b, h⟩, v₁, _, hagree⟩
  have e1 : a + b * gdom 1 = u0 1 := by rw [← h 1]; exact (hagree 1 (by decide)).1
  have e2 : a + b * gdom 2 = u0 2 := by rw [← h 2]; exact (hagree 2 (by decide)).1
  have e3 : a + b * gdom 3 = u0 3 := by rw [← h 3]; exact (hagree 3 (by decide)).1
  clear h
  revert e1 e2 e3
  revert a b
  decide

/-- `γ = 4`, witness `S = {0,1,3}`, on-line codeword `0`; no pair: `u₀` is not interpolable
on `S`. -/
theorem mcaEvent_g4 :
    mcaEvent (F := F5) (rsC : Set (Fin 4 → F5)) (1/4) u0 u1 4 := by
  refine ⟨{0, 1, 3}, card_clause (by decide), ⟨0, rsC.zero_mem, by decide⟩, ?_⟩
  rintro ⟨v₀, ⟨a, b, h⟩, v₁, _, hagree⟩
  have e0 : a + b * gdom 0 = u0 0 := by rw [← h 0]; exact (hagree 0 (by decide)).1
  have e1 : a + b * gdom 1 = u0 1 := by rw [← h 1]; exact (hagree 1 (by decide)).1
  have e3 : a + b * gdom 3 = u0 3 := by rw [← h 3]; exact (hagree 3 (by decide)).1
  clear h
  revert e0 e1 e3
  revert a b
  decide

open Classical in
/-- At least 4 of the 5 scalars are bad at `δ = 1/4` for the spread stack. -/
theorem badScalar_card_ge_four :
    4 ≤ (Finset.filter (fun γ : F5 =>
        mcaEvent (F := F5) (rsC : Set (Fin 4 → F5)) (1/4) u0 u1 γ) Finset.univ).card := by
  have hsub : ({0, 2, 3, 4} : Finset F5) ⊆ Finset.filter (fun γ : F5 =>
      mcaEvent (F := F5) (rsC : Set (Fin 4 → F5)) (1/4) u0 u1 γ) Finset.univ := by
    intro γ hγ
    fin_cases hγ
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mcaEvent_g0⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mcaEvent_g2⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mcaEvent_g3⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mcaEvent_g4⟩
  calc (4 : ℕ) = ({0, 2, 3, 4} : Finset F5).card := by decide
    _ ≤ _ := Finset.card_le_card hsub

open Classical in
/-- **Bad side:** `ε_mca(RS[F₅, ⟨2⟩, 2], 1/4) ≥ 4/5`. (Probe ground truth: equality.) -/
theorem epsMCA_rs_quarter_ge :
    (4 : ℝ≥0∞) / 5 ≤ epsMCA (F := F5) (A := F5) (rsC : Set (Fin 4 → F5)) (1/4) := by
  refine le_trans ?_
    (mcaEvent_prob_le_epsMCA (F := F5) (A := F5) (rsC : Set (Fin 4 → F5)) (1/4) ![u0, u1])
  have h0 : (![u0, u1] : WordStack F5 (Fin 2) (Fin 4)) 0 = u0 := rfl
  have h1 : (![u0, u1] : WordStack F5 (Fin 2) (Fin 4)) 1 = u1 := rfl
  rw [h0, h1, prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  have hcard : (Fintype.card F5 : ℝ≥0∞) = 5 := by
    rw [ZMod.card]; norm_num
  rw [hcard]
  gcongr
  exact_mod_cast badScalar_card_ge_four

/-! ### The pin: both brackets meet at `1/4` -/

/-- **Upper bracket:** `δ* ≤ 1/4`, since `ε_mca(C, 1/4) ≥ 4/5 > 2/5 = ε*`. -/
theorem mcaDeltaStar_rs_le_quarter :
    mcaDeltaStar (F := F5) (A := F5) (rsC : Set (Fin 4 → F5)) (2/5 : ℝ≥0∞) ≤ 1/4 := by
  refine MCAThresholdLedger.mcaDeltaStar_le_of_bad _ _ (lt_of_lt_of_le ?_ epsMCA_rs_quarter_ge)
  exact ENNReal.div_lt_div_right (by norm_num) (by norm_num) (by norm_num)

/-- **Lower bracket:** `1/4 ≤ δ*`: every `δ < 1/4` is below the granularity radius `1/n`,
so `ε_mca(C, δ) ≤ 1/5 ≤ 2/5 = ε*`; conclude by density of `ℝ≥0`. -/
theorem quarter_le_mcaDeltaStar_rs :
    (1/4 : ℝ≥0) ≤ mcaDeltaStar (F := F5) (A := F5) (rsC : Set (Fin 4 → F5)) (2/5 : ℝ≥0∞) := by
  by_contra hlt
  push Not at hlt
  obtain ⟨c, hc1, hc2⟩ := exists_between hlt
  have hcsmall : c * (Fintype.card (Fin 4) : ℝ≥0) < 1 := by
    rw [Fintype.card_fin]
    calc c * (4 : ℕ) < (1/4 : ℝ≥0) * (4 : ℕ) := by
          have h4 : (0 : ℝ≥0) < ((4 : ℕ) : ℝ≥0) := by norm_num
          exact mul_lt_mul_of_pos_right hc2 h4
      _ = 1 := by push_cast; norm_num
  have hgood : epsMCA (F := F5) (A := F5) (rsC : Set (Fin 4 → F5)) c ≤ (2/5 : ℝ≥0∞) := by
    refine le_trans (epsMCA_le_inv_card_of_small_radius rsC hcsmall) ?_
    have hcard : (Fintype.card F5 : ℝ≥0∞) = 5 := by rw [ZMod.card]; norm_num
    rw [hcard]
    exact ENNReal.div_le_div_right (by norm_num) 5
  have hquarter_le_one : (1/4 : ℝ≥0) ≤ 1 := by
    rw [div_le_one (by norm_num : (0 : ℝ≥0) < 4)]
    norm_num
  have hle : c ≤ mcaDeltaStar (F := F5) (A := F5) (rsC : Set (Fin 4 → F5)) (2/5 : ℝ≥0∞) :=
    MCAThresholdLedger.le_mcaDeltaStar_of_good _ _
      (le_of_lt (lt_of_lt_of_le hc2 hquarter_le_one)) hgood
  exact absurd (lt_of_le_of_lt hle hc1) (lt_irrefl _)

/-- **THE PIN — the first machine-checked exact `δ*` value for any code:**
`mcaDeltaStar (RS[F₅, ⟨2⟩, 2]) (2/5) = 1/4`. A genuine smooth-domain RS code (domain
`⟨2⟩ = F₅ˣ`, `n = 4 = 2²`), rate `ρ = 1/2`; both bracket halves meet. At this scale and
`ε*`, `δ* = (1−ρ)/2` — the unique-decoding radius. -/
theorem mcaDeltaStar_rs_F5_eq_quarter :
    mcaDeltaStar (F := F5) (A := F5) (rsC : Set (Fin 4 → F5)) (2/5 : ℝ≥0∞) = 1/4 :=
  le_antisymm mcaDeltaStar_rs_le_quarter quarter_le_mcaDeltaStar_rs

/-- The supremum is **not attained**: `δ* = 1/4` is itself a bad radius
(`ε_mca(C, δ*) ≥ 4/5 > 2/5`). `δ*` sits exactly at a jump of the step function `ε_mca`. -/
theorem deltaStar_not_good :
    (2/5 : ℝ≥0∞) < epsMCA (F := F5) (A := F5) (rsC : Set (Fin 4 → F5))
      (mcaDeltaStar (F := F5) (A := F5) (rsC : Set (Fin 4 → F5)) (2/5 : ℝ≥0∞)) := by
  rw [mcaDeltaStar_rs_F5_eq_quarter]
  refine lt_of_lt_of_le ?_ epsMCA_rs_quarter_ge
  exact ENNReal.div_lt_div_right (by norm_num) (by norm_num) (by norm_num)

/-- The code is proper, so the general exact sub-granularity value applies:
`ε_mca(C, δ) = 1/5` exactly for every `δ < 1/4` — the good-side step of the ladder is not
just a bound but the exact value. -/
theorem rsC_proper : (rsC : Set (Fin 4 → F5)) ≠ Set.univ := by
  intro h
  have hmem : u1 ∈ (rsC : Set (Fin 4 → F5)) := h ▸ Set.mem_univ u1
  obtain ⟨a, b, hab⟩ := hmem
  have e0 := hab 0
  have e1 := hab 1
  have e2 := hab 2
  clear h
  clear hab
  revert e0 e1 e2
  revert a b
  decide

/-- The exact step-function value on the good side: `ε_mca(C, δ) = 1/5` for `δ·4 < 1`. -/
theorem epsMCA_rs_eq_fifth_of_small {δ : ℝ≥0} (hδ : δ * (Fintype.card (Fin 4) : ℝ≥0) < 1) :
    epsMCA (F := F5) (A := F5) (rsC : Set (Fin 4 → F5)) δ = 1 / 5 := by
  have h := epsMCA_eq_inv_card_of_small_radius rsC hδ rsC_proper
  rwa [show (Fintype.card F5 : ℝ≥0∞) = 5 by rw [ZMod.card]; norm_num] at h

end Concrete

/-! ## Source audit -/

#print axioms witness_eq_univ_of_small_radius
#print axioms badScalar_card_le_one_of_small_radius
#print axioms epsMCA_le_inv_card_of_small_radius
#print axioms epsMCA_eq_inv_card_of_small_radius
#print axioms epsMCA_rs_quarter_ge
#print axioms mcaDeltaStar_rs_F5_eq_quarter
#print axioms deltaStar_not_good
#print axioms epsMCA_rs_eq_fifth_of_small

end ProximityGap.MCADeltaStarExactPoint
