/-
Copyright (c) 2026 Proximity Prize Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Proximity Prize Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.FineGridFirstOrderSecurity
import ArkLib.Research.ProximityGap.Frontier.FourRateListPrime246
import ArkLib.Research.ProximityGap.SmoothListRankBracket
import ArkLib.ToMathlib.InformationTheory.Hamming

/-!
# Derivative-Capped Tight First-Order List Bounds and Smooth Production Rank Brackets

`ScaledFirstOrderSecurity`, `FineGridFirstOrderSecurity`, and `FineGridWideLists` derive linear
worst-center Reed–Solomon list bounds from shifted first-order interpolation slot certificates via
`finite_firstOrder_list_bound_of_heightSlotCount_sharp`, charging every order-one separant stage
by the uncapped product `j * (1 + 2 * K * (j - 1)) * n / (A - k + 1)`.

Here we prove a uniform-in-`b` scaling theorem for the dimension-sensitive derivative-capped
bound `finite_firstOrder_list_bound_of_shiftedHeightSlotCount_tight` at exponent `2 * K - 3`,
transported across arbitrary finite domain index types and arbitrary finite interleaving widths
over any field of characteristic zero or characteristic at least the block length.

## Main statements

* `tight_interleaved_list_of_slots`: one reference slot inequality and one integer cost inequality
  at reference length `N` bound `Code.Lambda` for every `width`-interleaved Reed–Solomon code of
  length `b * N` over every field with `ringChar F = 0 ∨ b * N ≤ ringChar F`.
* `tight_128_interleaved_bounds`, `tight_4096_interleaved_bounds`,
  `tight_wide_4096_interleaved_bounds`: reduces all twelve linear list-size constants of the
  `128 b`, `4096 b`, and wide `4096 b` beyond-Johnson certificates by factors between `4.94×` and
  `8.88×`, uniformly over all eligible fields and all interleaving widths.
* `low_budget_4096_interleaved_bounds`: four compact (`M = 3`, `μ ≤ 34`) certificates at
  `1215/4096`, `2089/4096`, `2695/4096`, and `3116/4096` with linear list constants at most `407 n`.
* `ultra_fine_65536_interleaved_bounds`: four fine-grid (`N = 65536`) certificates at radii
  `20314/65536`, `34801/65536`, `44611/65536`, and `51226/65536` — strictly exceeding all four
  radii of `FineGridWideLists` while keeping every list-size constant below `2^31 n`.
* `first_failure_low_budget`, `first_failure_fine_grid`, `prime_production_rank_brackets`:
  upgrades the lower endpoint of `SmoothListRankBracket.first_failure_reserved` on smooth domains
  from `+1` step above Johnson to explicit beyond-Johnson first-order error counts (`+18.33M` to
  `+36.78M` additional safe errors past Johnson at `n = 2^30` for every prime `2^189 ≤ p < 2^256`).

## References

* [DKT26]
-/

set_option autoImplicit false

namespace ProximityGap.CarbonListTightFirstOrder

open Code ReedSolomon ReedSolomon.HiddenDerivative ProximityGap.GrandChallenges
open ProximityGap.FineGridFirstOrderSecurity
open scoped NNReal ENNReal

/-! ### Uniform scaling of the derivative-capped first-order list charge -/

/-- Reference order-one stage unit before multiplying by `(N - k) / (A - k)`. -/
def tightStageOneUnit (k j r : ℕ) : ℕ :=
  if j ≤ 1 then 1
  else (j - r) * min (2 * k * (j - 1)) (k * (2 * r - 1)) + r * (2 * k * (j - 1))

/-- Sum of reference order-one stage units across `(μ, M)`. -/
def tightOrderOneUnits (k : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | μ + 1, M + 1 =>
      tightStageOneUnit k (μ + 1) (min (M + 1) (μ + 1)) + tightOrderOneUnits k μ M

/-- Sum of order-zero stage degrees across `(μ, M)`. -/
def tightOrderZeroUnits : ℕ → ℕ → ℕ
  | 0, _ => 0
  | μ + 1, 0 => (μ + 1) + tightOrderZeroUnits μ 0
  | μ + 1, M + 1 => tightOrderZeroUnits μ M

/-- Exact integer certificate inequality implying `firstOrderTightListWeight ≤ C * (b * N)`
at every positive scale multiple `b`. -/
def tightCostHolds (N k A μ M C : ℕ) : Prop :=
  tightOrderZeroUnits μ M * (A - k) + tightOrderOneUnits k μ M * (N - k) ≤
    C * N * (A - k)

instance instDecidableTightCostHolds (N k A μ M C : ℕ) :
    Decidable (tightCostHolds N k A μ M C) :=
  inferInstanceAs (Decidable (_ ≤ _))

private theorem ringChar_eq_of_injective {R S : Type*} [NonAssocSemiring R]
    [NonAssocSemiring S] (φ : R →+* S) (hφ : Function.Injective φ) :
    ringChar S = ringChar R := by
  refine Nat.dvd_antisymm (ringChar.dvd ?_) (ringChar.dvd ?_)
  · rw [← map_natCast φ, ringChar.Nat.cast_ringChar, map_zero]
  · apply hφ
    rw [map_natCast, map_zero]
    exact ringChar.Nat.cast_ringChar

private theorem mul_min_distrib (b x y : ℕ) :
    b * min x y = min (b * x) (b * y) := by
  rcases le_total x y with hxy | hyx
  · rw [min_eq_left hxy, min_eq_left (Nat.mul_le_mul_left b hxy)]
  · rw [min_eq_right hyx, min_eq_right (Nat.mul_le_mul_left b hyx)]

private theorem stageOne_le_scaled {b k j r : ℕ} (hb : 0 < b) (hk : 2 ≤ k)
    (hr0 : 1 ≤ r) (hrj : r ≤ j) :
    firstOrderCurveFiberStageOne (b * k) j r (2 * (b * k) - 3) ≤
      b * tightStageOneUnit k j r := by
  have hcb := firstOrderTaylorDerivativeCap_le_totalCap (b * k) j r (2 * (b * k) - 3)
  rw [firstOrderCurveFiberStageOne, MvPolynomial.cappedDegreeMixedVolume_eq hrj hcb]
  by_cases hj1 : j ≤ 1
  · have hj : j = 1 := by omega
    have hr : r = 1 := by omega
    subst hj
    subst hr
    simp only [tightStageOneUnit, le_rfl, ↓reduceIte, Nat.sub_self, zero_mul,
      zero_add, mul_one, firstOrderTaylorTotalCap, mul_zero, add_zero]
    omega
  · rw [tightStageOneUnit, ite_eq_right hj1]
    have hbk : 2 ≤ b * k := by nlinarith
    obtain ⟨m, hm⟩ : ∃ m, j = m + 2 := ⟨j - 2, by omega⟩
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    have hbCap : firstOrderTaylorTotalCap j (2 * (b * k) - 3) ≤ b * (2 * k * (j - 1)) := by
      unfold firstOrderTaylorTotalCap
      have hsub : j - 1 = m + 1 := by omega
      rw [hsub]
      have hsum : (2 * (b * k) - 3) * (m + 1) + 3 * (m + 1) = 2 * (b * k) * (m + 1) := by
        rw [← Nat.add_mul, show 2 * (b * k) - 3 + 3 = 2 * (b * k) by omega]
      calc
        1 + (2 * (b * k) - 3) * (m + 1) ≤
            (2 * (b * k) - 3) * (m + 1) + 3 * (m + 1) := by omega
        _ = 2 * (b * k) * (m + 1) := hsum
        _ = b * (2 * k * (m + 1)) := by ring
    have hcCap : firstOrderTaylorDerivativeCap (b * k) j (r' + 1) (2 * (b * k) - 3) ≤
        b * min (2 * k * (j - 1)) (k * (2 * (r' + 1) - 1)) := by
      rw [firstOrderTaylorDerivativeCap, mul_min_distrib]
      refine min_le_min hbCap ?_
      have h1 : (2 * (b * k) - 3) * ((r' + 1) - 1) + (b * k - 1) ≤
          (2 * (b * k)) * r' + b * k := by
        rw [Nat.add_sub_cancel]
        exact Nat.add_le_add (Nat.mul_le_mul_right r' (Nat.sub_le _ _)) (Nat.sub_le _ _)
      have h2 : 2 * (r' + 1) - 1 = 2 * r' + 1 := by omega
      rw [h2]
      exact h1.trans_eq (by ring)
    calc
      (j - (r' + 1)) * firstOrderTaylorDerivativeCap (b * k) j (r' + 1) (2 * (b * k) - 3) +
          (r' + 1) * firstOrderTaylorTotalCap j (2 * (b * k) - 3) ≤
        (j - (r' + 1)) * (b * min (2 * k * (j - 1)) (k * (2 * (r' + 1) - 1))) +
          (r' + 1) * (b * (2 * k * (j - 1))) := by gcongr
      _ = b * ((j - (r' + 1)) * min (2 * k * (j - 1)) (k * (2 * (r' + 1) - 1)) +
          (r' + 1) * (2 * k * (j - 1))) := by ring

private theorem ratio_le_scaled {b N A k : ℕ} (hkA : k < A) (hAN : A ≤ N) :
    (((b * N - b * k + 1 : ℕ) : ℚ) / ((b * A - b * k + 1 : ℕ) : ℚ)) ≤
      (((N - k : ℕ) : ℚ) / ((A - k : ℕ) : ℚ)) := by
  have hd1 : (0 : ℚ) < ((b * A - b * k + 1 : ℕ) : ℚ) := by positivity
  have hd2 : (0 : ℚ) < ((A - k : ℕ) : ℚ) := by exact_mod_cast Nat.sub_pos_of_lt hkA
  rw [div_le_div_iff₀ hd1 hd2, ← Nat.mul_sub, ← Nat.mul_sub]
  have hsub : A - k ≤ N - k := Nat.sub_le_sub_right hAN k
  exact_mod_cast (show (b * (N - k) + 1) * (A - k) ≤ (N - k) * (b * (A - k) + 1) by
    nlinarith)

private theorem tightWeight_le_scaled {b N A k : ℕ} (hb : 0 < b) (hk : 2 ≤ k)
    (hkA : k < A) (hAN : A ≤ N) (μ M : ℕ) :
    firstOrderTightListWeight (b * N) (b * A) (b * k) (b * k) (2 * (b * k) - 3) μ M ≤
      (b : ℚ) * ((tightOrderZeroUnits μ M : ℚ) +
        ((tightOrderOneUnits k μ M * (N - k) : ℕ) : ℚ) / ((A - k : ℕ) : ℚ)) := by
  induction μ generalizing M with
  | zero =>
    simp only [firstOrderTightListWeight, tightOrderZeroUnits, tightOrderOneUnits,
      Nat.zero_mul, Nat.cast_zero, zero_div, add_zero, mul_zero, le_rfl]
  | succ μ ih =>
    cases M with
    | zero =>
      rw [firstOrderTightListWeight, tightOrderZeroUnits, tightOrderOneUnits]
      have hb1 : (1 : ℚ) ≤ (b : ℚ) := by exact_mod_cast hb
      have hterm : ((μ + 1 : ℕ) : ℚ) ≤ (b : ℚ) * ((μ + 1 : ℕ) : ℚ) := by
        nlinarith [ (Nat.cast_nonneg (α := ℚ) (μ + 1)) ]
      have hz1 : tightOrderOneUnits k μ 0 = 0 := by cases μ <;> rfl
      have hih := ih 0
      rw [hz1] at hih
      simp only [Nat.zero_mul, Nat.cast_zero, zero_div, add_zero] at hih ⊢
      push_cast at hterm hih ⊢
      rw [mul_add]
      linarith
    | succ M =>
      rw [firstOrderTightListWeight, tightOrderZeroUnits, tightOrderOneUnits]
      have hstageNat := stageOne_le_scaled (b := b) hb hk
        (show 1 ≤ min (M + 1) (μ + 1) by omega) (min_le_right (M + 1) (μ + 1))
      have hstage : (firstOrderCurveFiberStageOne (b * k) (μ + 1)
          (min (M + 1) (μ + 1)) (2 * (b * k) - 3) : ℚ) ≤
          (b : ℚ) * (tightStageOneUnit k (μ + 1) (min (M + 1) (μ + 1)) : ℚ) := by
        exact_mod_cast hstageNat
      have hrat := ratio_le_scaled (b := b) hkA hAN
      have hprod : (firstOrderCurveFiberStageOne (b * k) (μ + 1)
            (min (M + 1) (μ + 1)) (2 * (b * k) - 3) : ℚ) *
            ((b * N - b * k + 1 : ℕ) : ℚ) / ((b * A - b * k + 1 : ℕ) : ℚ) ≤
          (b : ℚ) * (tightStageOneUnit k (μ + 1) (min (M + 1) (μ + 1)) : ℚ) *
            (((N - k : ℕ) : ℚ) / ((A - k : ℕ) : ℚ)) := by
        rw [mul_div_assoc]
        exact mul_le_mul hstage hrat (by positivity) (by positivity)
      have hih := ih M
      have hsplit : (((tightStageOneUnit k (μ + 1) (min (M + 1) (μ + 1)) +
            tightOrderOneUnits k μ M) * (N - k) : ℕ) : ℚ) / ((A - k : ℕ) : ℚ) =
          (tightStageOneUnit k (μ + 1) (min (M + 1) (μ + 1)) : ℚ) *
            (((N - k : ℕ) : ℚ) / ((A - k : ℕ) : ℚ)) +
          ((tightOrderOneUnits k μ M * (N - k) : ℕ) : ℚ) / ((A - k : ℕ) : ℚ) := by
        push_cast
        ring
      rw [hsplit]
      linarith

private theorem tightWeight_le_mul {b N A k μ M C : ℕ} (hb : 0 < b) (hk : 2 ≤ k)
    (hkA : k < A) (hAN : A ≤ N) (hcost : tightCostHolds N k A μ M C) :
    firstOrderTightListWeight (b * N) (b * A) (b * k) (b * k) (2 * (b * k) - 3) μ M ≤
      ((C * (b * N) : ℕ) : ℚ) := by
  have hd : (0 : ℚ) < ((A - k : ℕ) : ℚ) := by exact_mod_cast Nat.sub_pos_of_lt hkA
  have hcostQ : (tightOrderZeroUnits μ M : ℚ) * ((A - k : ℕ) : ℚ) +
      ((tightOrderOneUnits k μ M * (N - k) : ℕ) : ℚ) ≤
      ((C * N : ℕ) : ℚ) * ((A - k : ℕ) : ℚ) := by
    exact_mod_cast hcost
  have href : (tightOrderZeroUnits μ M : ℚ) +
      ((tightOrderOneUnits k μ M * (N - k) : ℕ) : ℚ) / ((A - k : ℕ) : ℚ) ≤
      ((C * N : ℕ) : ℚ) := by
    have hmul : ((tightOrderZeroUnits μ M : ℚ) +
        ((tightOrderOneUnits k μ M * (N - k) : ℕ) : ℚ) / ((A - k : ℕ) : ℚ)) *
        ((A - k : ℕ) : ℚ) ≤ ((C * N : ℕ) : ℚ) * ((A - k : ℕ) : ℚ) := by
      rwa [add_mul, div_mul_cancel₀ _ hd.ne']
    exact le_of_mul_le_mul_right hmul hd
  refine (tightWeight_le_scaled hb hk hkA hAN μ M).trans ?_
  calc
    (b : ℚ) * ((tightOrderZeroUnits μ M : ℚ) +
        ((tightOrderOneUnits k μ M * (N - k) : ℕ) : ℚ) / ((A - k : ℕ) : ℚ)) ≤
      (b : ℚ) * ((C * N : ℕ) : ℚ) :=
        mul_le_mul_of_nonneg_left href (Nat.cast_nonneg b)
    _ = ((C * (b * N) : ℕ) : ℚ) := by push_cast; ring

/-! ### General field-uniform and domain-uniform interleaved list transfer -/

private theorem lambda_reindex_le {I J α : Type*} [Fintype I] [Fintype J] (e : I ≃ J)
    (C : Set (J → α)) (D : Set (I → α)) (hd : ∀ w ∈ C, w ∘ e ∈ D) (δ : ℝ) :
    Code.Lambda C δ ≤ Code.Lambda D δ := by
  classical
  apply Code.Lambda_le_iff_forall_encard_le.mpr
  intro W
  refine le_trans ?_ (Code.encard_closeCodewordsRel_le_Lambda D δ (W ∘ e))
  have hin : (Code.closeCodewordsRel C W δ).InjOn (fun w => w ∘ e) :=
    fun w _ v _ h => funext fun j => by simpa using congrFun h (e.symm j)
  rw [← hin.encard_image]
  apply Set.encard_mono
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨hc, hδ⟩ := Code.mem_closeCodewordsRel_iff.mp hw
  refine Code.mem_closeCodewordsRel_iff.mpr ⟨hd w hc, ?_⟩
  rw [Code.relHammingDist_coe, hammingDist_comp_equiv, Fintype.card_congr e,
    ← Code.relHammingDist_coe]
  exact hδ

/-- A reference slot inequality and reference tight-cost bound control worst-center scalar
Reed–Solomon lists on `Fin (b * N)` over any field with `ringChar F = 0 ∨ b * N ≤ ringChar F`. -/
theorem tight_fin_list_of_slots {F : Type*} [Field F] {N b k A m M μ h C : ℕ}
    (hb : 0 < b) (hk : 2 ≤ k) (hkA : k < A) (hAN : A ≤ N) (hμ : μ < N)
    (hfield : ringChar F = 0 ∨ b * N ≤ ringChar F)
    (hcost : tightCostHolds N k A μ M C)
    (hslots : rowSlots N m M μ h < columnSlots k A m M μ h)
    (dom : Fin (b * N) ↪ F) :
    Code.Lambda (code dom (b * k) : Set (Fin (b * N) → F)) (1 - (A : ℝ) / N) ≤
      ((C * (b * N) : ℕ) : ℕ∞) := by
  classical
  have hNpos : 0 < N := by omega
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hNb : N ≤ b * N := Nat.le_mul_of_pos_left N hb
  let g := ((A - k : ℕ) : ℝ) / N
  have hg : 0 ≤ g := by dsimp [g]; positivity
  have h₁ : capacityAgreementThreshold g (b * N) (b * k) = b * A := by
    have he : g * ((b * N : ℕ) : ℝ) = ((b * (A - k) : ℕ) : ℝ) := by
      dsimp [g]
      push_cast
      field_simp
    rw [capacityAgreementThreshold, he, Nat.ceil_natCast, Nat.mul_sub, Nat.add_sub_of_le]
    exact Nat.mul_le_mul_left b hkA.le
  have h₂ : capacityRadius g (b * N) (b * k) = 1 - (A : ℝ) / N := by
    unfold capacityRadius g
    rw [Nat.cast_sub hkA.le]
    push_cast
    field_simp
    ring
  rw [← h₂, ← Nat.ceil_natCast (R := ℝ) (C * (b * N))]
  apply lambda_le_ceil_of_closePolynomialSet_bound hg (by omega)
  intro f
  rw [h₁]
  let T := @closePolynomialSet F _ (Classical.decEq _) _ dom f (b * k) (b * A)
  have hbk : 2 ≤ b * k := by nlinarith
  have hlt : b * k < b * A := Nat.mul_lt_mul_of_pos_left hkA hb
  have hAn' := Nat.mul_le_mul_left b hAN
  have hchar : ringChar F = 0 ∨ max (b * k - 1) μ < ringChar F := by
    rcases hfield with hc | hc
    · exact Or.inl hc
    · exact Or.inr (by omega)
  have bound (S : Finset (Polynomial F)) (hST : (↑S : Set _) ⊆ T) :
      S.card ≤ C * (b * N) := by
    have hpoint (P : Polynomial F) (hP : P ∈ S) :
        P.degree < b * k ∧
          b * A ≤ ({i : Fin (b * N) | P.eval (dom i) = f i} : Set _).ncard := by
      have h := hST hP
      refine ⟨h.1, h.2.trans_eq ?_⟩
      rw [Set.ncard_eq_toFinset_card']
      congr 1
      ext i
      simp [polynomialAgreementSet]
    have hbound := finite_firstOrder_list_bound_of_shiftedHeightSlotCount_tight
      (D := b * k - 1) (K := b * k) (by omega) (by omega) dom f
      (scaled_slots hb hslots) hbk le_rfl (by omega) hlt.le hchar S hpoint
    exact_mod_cast hbound.trans (tightWeight_le_mul hb hk hkA hAN hcost)
  have hfin : T.Finite :=
    Set.finite_of_forall_finset_card_le (R := ℕ) (ℓ := C * (b * N)) bound
  refine ⟨hfin, ?_⟩
  have h := bound hfin.toFinset (fun _ hx => hfin.mem_toFinset.mp hx)
  rw [← Set.ncard_eq_toFinset_card _ hfin] at h
  exact_mod_cast h

/-- A reference slot inequality and reference tight-cost bound control worst-center
`width`-interleaved Reed–Solomon lists on any injective domain `D : I ↪ F` of size `b * N`,
over any field of characteristic zero or characteristic at least `b * N`. -/
theorem tight_interleaved_list_of_slots {I F : Type*} [Fintype I] [Field F]
    {N b k A m M μ h C : ℕ} (hb : 0 < b) (hk : 2 ≤ k) (hkA : k < A) (hAN : A ≤ N)
    (hμ : μ < N) (hfield : ringChar F = 0 ∨ b * N ≤ ringChar F)
    (hcost : tightCostHolds N k A μ M C)
    (hslots : rowSlots N m M μ h < columnSlots k A m M μ h)
    (D : I ↪ F) (hn : Fintype.card I = b * N) (width : ℕ) :
    Code.Lambda (Code.interleavedCodeSet (κ := Fin width)
      (code D (b * k) : Set (I → F))) (1 - (A : ℝ) / N) ≤
      ((C * (b * N) : ℕ) : ℕ∞) := by
  let e : Fin (b * N) ≃ I := (Fintype.equivFinOfCardEq hn).symm
  let dom : Fin (b * N) ↪ F := e.toEmbedding.trans D
  have hreindex : Code.Lambda (Code.interleavedCodeSet (κ := Fin width)
        (code D (b * k) : Set (I → F))) (1 - (A : ℝ) / N) ≤
      Code.Lambda (Code.interleavedCodeSet (κ := Fin width)
        (code dom (b * k) : Set (Fin (b * N) → F))) (1 - (A : ℝ) / N) := by
    apply lambda_reindex_le e
    intro w hw row
    obtain ⟨P, hdeg, heval⟩ := ReedSolomon.mem_code_iff_eval.mp (hw row)
    exact ReedSolomon.mem_code_iff_eval.mpr ⟨P, hdeg, fun idx => heval (e idx)⟩
  let φ := algebraMap F (RatFunc F)
  have hcharRat : ringChar (RatFunc F) = ringChar F :=
    ringChar_eq_of_injective φ φ.injective
  have hfieldRat : ringChar (RatFunc F) = 0 ∨ b * N ≤ ringChar (RatFunc F) := by
    rw [hcharRat]
    exact hfield
  refine hreindex.trans ((Lambda_interleaved_le_ratFunc dom (b * k) width _).trans ?_)
  exact tight_fin_list_of_slots hb hk hkA hAN hμ hfieldRat hcost hslots
    (dom.trans ⟨φ, φ.injective⟩)

/-- Scalar specialization on `Fin (b * N)` follows directly from `tight_fin_list_of_slots`. -/
theorem tight_prime_interleaved_list_of_slots {I : Type*} [Fintype I]
    {p N b k A m M μ h C : ℕ} [Fact p.Prime] (hb : 0 < b) (hk : 2 ≤ k)
    (hkA : k < A) (hAN : A ≤ N) (hμ : μ < N) (hcost : tightCostHolds N k A μ M C)
    (hslots : rowSlots N m M μ h < columnSlots k A m M μ h)
    (D : I ↪ ZMod p) (hn : Fintype.card I = b * N) (width : ℕ) :
    Code.Lambda (Code.interleavedCodeSet (κ := Fin width)
      (code D (b * k) : Set (I → ZMod p))) (1 - (A : ℝ) / N) ≤
      ((C * (b * N) : ℕ) : ℕ∞) := by
  have hsize : b * N ≤ ringChar (ZMod p) := by
    rw [ZMod.ringChar_zmod_n, ← hn]
    simpa only [ZMod.card] using Fintype.card_le_of_injective D D.injective
  exact tight_interleaved_list_of_slots hb hk hkA hAN hμ (Or.inr hsize) hcost hslots D hn width

/-! ### Sharpened linear list bounds for the 128b, 4096b, and wide 4096b families -/

private theorem slot_certificates_128 :
    rowSlots 128 43 12 59 1426 < columnSlots 64 89 43 12 59 1426 ∧
    rowSlots 128 35 15 66 1217 < columnSlots 32 61 35 15 66 1217 ∧
    rowSlots 128 26 13 67 1181 < columnSlots 16 42 26 13 67 1181 ∧
    rowSlots 128 22 13 79 1321 < columnSlots 8 29 22 13 79 1321 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- Tight derivative-capped interleaved list bounds at length `128 * b` (`39/128`, `67/128`,
`86/128`, `99/128`), reducing the constants `(173373, 113975, 58872, 52349)` of
`ScaledFirstOrderSecurity` to `(19522, 21491, 11002, 8811)` (`5.30×` to `8.88×` smaller). -/
theorem tight_128_interleaved_bounds {I F : Type*} [Fintype I] [Field F] {b : ℕ}
    (hb : 0 < b) (hfield : ringChar F = 0 ∨ b * 128 ≤ ringChar F)
    (D : I ↪ F) (hn : Fintype.card I = b * 128) (width : ℕ) :
    let bounded := fun (k : ℕ) (r : ℝ) (C : ℕ) =>
      Code.Lambda (Code.interleavedCodeSet (κ := Fin width)
        (code D (b * k) : Set (I → F))) r ≤ ((C * (b * 128) : ℕ) : ℕ∞)
    bounded 64 (39 / 128) 19522 ∧ bounded 32 (67 / 128) 21491 ∧
      bounded 16 (86 / 128) 11002 ∧ bounded 8 (99 / 128) 8811 := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := slot_certificates_128
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Nat.cast_ofNat, show (1 - (89 : ℝ) / 128) = 39 / 128 by norm_num] using
      tight_interleaved_list_of_slots (C := 19522) hb (by decide) (by decide) (by decide)
        (by decide) hfield (by decide +kernel) h₁ D hn width
  · simpa only [Nat.cast_ofNat, show (1 - (61 : ℝ) / 128) = 67 / 128 by norm_num] using
      tight_interleaved_list_of_slots (C := 21491) hb (by decide) (by decide) (by decide)
        (by decide) hfield (by decide +kernel) h₂ D hn width
  · simpa only [Nat.cast_ofNat, show (1 - (42 : ℝ) / 128) = 86 / 128 by norm_num] using
      tight_interleaved_list_of_slots (C := 11002) hb (by decide) (by decide) (by decide)
        (by decide) hfield (by decide +kernel) h₃ D hn width
  · simpa only [Nat.cast_ofNat, show (1 - (29 : ℝ) / 128) = 99 / 128 by norm_num] using
      tight_interleaved_list_of_slots (C := 8811) hb (by decide) (by decide) (by decide)
        (by decide) hfield (by decide +kernel) h₄ D hn width

/-- Tight derivative-capped interleaved list bounds at length `4096 * b` (`1262/4096`,
`2166/4096`, `2780/4096`, `3195/4096`), reducing `(3722270, 3891790, 4624878, 5864546)` of
`FineGridFirstOrderSecurity` to `(441892, 755543, 929137, 1077546)` (`4.98×` to `8.42×`). -/
theorem tight_4096_interleaved_bounds {I F : Type*} [Fintype I] [Field F] {b : ℕ}
    (hb : 0 < b) (hfield : ringChar F = 0 ∨ b * 4096 ≤ ringChar F)
    (D : I ↪ F) (hn : Fintype.card I = b * 4096) (width : ℕ) :
    let bounded := fun (k : ℕ) (r : ℝ) (C : ℕ) =>
      Code.Lambda (Code.interleavedCodeSet (κ := Fin width)
        (code D (b * k) : Set (I → F))) r ≤ ((C * (b * 4096) : ℕ) : ℕ∞)
    bounded 2048 (1262 / 4096) 441892 ∧ bounded 1024 (2166 / 4096) 755543 ∧
      bounded 512 (2780 / 4096) 929137 ∧ bounded 256 (3195 / 4096) 1077546 := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := slot_certificates
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Nat.cast_ofNat, show (1 - (2834 : ℝ) / 4096) = 1262 / 4096 by norm_num] using
      tight_interleaved_list_of_slots (C := 441892) hb (by decide) (by decide) (by decide)
        (by decide) hfield (by decide +kernel) h₁ D hn width
  · simpa only [Nat.cast_ofNat, show (1 - (1930 : ℝ) / 4096) = 2166 / 4096 by norm_num] using
      tight_interleaved_list_of_slots (C := 755543) hb (by decide) (by decide) (by decide)
        (by decide) hfield (by decide +kernel) h₂ D hn width
  · simpa only [Nat.cast_ofNat, show (1 - (1316 : ℝ) / 4096) = 2780 / 4096 by norm_num] using
      tight_interleaved_list_of_slots (C := 929137) hb (by decide) (by decide) (by decide)
        (by decide) hfield (by decide +kernel) h₃ D hn width
  · simpa only [Nat.cast_ofNat, show (1 - (901 : ℝ) / 4096) = 3195 / 4096 by norm_num] using
      tight_interleaved_list_of_slots (C := 1077546) hb (by decide) (by decide) (by decide)
        (by decide) hfield (by decide +kernel) h₄ D hn width

/-- Tight derivative-capped interleaved list bounds at the wide radii (`1269/4096`, `2174/4096`,
`2788/4096`, `3201/4096`), reducing `(1369562863, 649560740, 2486297660, 615760719)` of
`FineGridWideLists` to `(164423839, 127463408, 503349611, 115572934)` (`4.94×` to `8.33×`). -/
theorem tight_wide_4096_interleaved_bounds {I F : Type*} [Fintype I] [Field F] {b : ℕ}
    (hb : 0 < b) (hfield : ringChar F = 0 ∨ b * 4096 ≤ ringChar F)
    (D : I ↪ F) (hn : Fintype.card I = b * 4096) (width : ℕ) :
    let bounded := fun (k : ℕ) (r : ℝ) (C : ℕ) =>
      Code.Lambda (Code.interleavedCodeSet (κ := Fin width)
        (code D (b * k) : Set (I → F))) r ≤ ((C * (b * 4096) : ℕ) : ℕ∞)
    bounded 2048 (1269 / 4096) 164423839 ∧ bounded 1024 (2174 / 4096) 127463408 ∧
      bounded 512 (2788 / 4096) 503349611 ∧ bounded 256 (3201 / 4096) 115572934 := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := wide_slot_certificates
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Nat.cast_ofNat, show (1 - (2827 : ℝ) / 4096) = 1269 / 4096 by norm_num] using
      tight_interleaved_list_of_slots (C := 164423839) hb (by decide) (by decide) (by decide)
        (by decide) hfield (by decide +kernel) h₁ D hn width
  · simpa only [Nat.cast_ofNat, show (1 - (1922 : ℝ) / 4096) = 2174 / 4096 by norm_num] using
      tight_interleaved_list_of_slots (C := 127463408) hb (by decide) (by decide) (by decide)
        (by decide) hfield (by decide +kernel) h₂ D hn width
  · simpa only [Nat.cast_ofNat, show (1 - (1308 : ℝ) / 4096) = 2788 / 4096 by norm_num] using
      tight_interleaved_list_of_slots (C := 503349611) hb (by decide) (by decide) (by decide)
        (by decide) hfield (by decide +kernel) h₃ D hn width
  · simpa only [Nat.cast_ofNat, show (1 - (895 : ℝ) / 4096) = 3201 / 4096 by norm_num] using
      tight_interleaved_list_of_slots (C := 115572934) hb (by decide) (by decide) (by decide)
        (by decide) hfield (by decide +kernel) h₄ D hn width

/-! ### Low-budget (`C ≤ 407`) and ultra-fine (`N = 65536`) beyond-Johnson list families -/

/-- Four compact `M = 3` slot inequalities at reference length `4096`. -/
theorem low_budget_4096_slot_certificates :
    rowSlots 4096 13 3 18 7021 < columnSlots 2048 2881 13 3 18 7021 ∧
    rowSlots 4096 12 3 23 4874 < columnSlots 1024 2007 12 3 23 4874 ∧
    rowSlots 4096 10 3 27 15246 < columnSlots 512 1401 10 3 27 15246 ∧
    rowSlots 4096 9 3 34 25721 < columnSlots 256 980 9 3 34 25721 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- Beyond-Johnson interleaved list bounds at `1215/4096`, `2089/4096`, `2695/4096`, and
`3116/4096` with small linear constants `(407, 341, 263, 222)`. -/
theorem low_budget_4096_interleaved_bounds {I F : Type*} [Fintype I] [Field F] {b : ℕ}
    (hb : 0 < b) (hfield : ringChar F = 0 ∨ b * 4096 ≤ ringChar F)
    (D : I ↪ F) (hn : Fintype.card I = b * 4096) (width : ℕ) :
    let bounded := fun (k : ℕ) (r : ℝ) (C : ℕ) =>
      Code.Lambda (Code.interleavedCodeSet (κ := Fin width)
        (code D (b * k) : Set (I → F))) r ≤ ((C * (b * 4096) : ℕ) : ℕ∞)
    bounded 2048 (1215 / 4096) 407 ∧ bounded 1024 (2089 / 4096) 341 ∧
      bounded 512 (2695 / 4096) 263 ∧ bounded 256 (3116 / 4096) 222 := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := low_budget_4096_slot_certificates
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Nat.cast_ofNat, show (1 - (2881 : ℝ) / 4096) = 1215 / 4096 by norm_num] using
      tight_interleaved_list_of_slots (C := 407) hb (by decide) (by decide) (by decide)
        (by decide) hfield (by decide +kernel) h₁ D hn width
  · simpa only [Nat.cast_ofNat, show (1 - (2007 : ℝ) / 4096) = 2089 / 4096 by norm_num] using
      tight_interleaved_list_of_slots (C := 341) hb (by decide) (by decide) (by decide)
        (by decide) hfield (by decide +kernel) h₂ D hn width
  · simpa only [Nat.cast_ofNat, show (1 - (1401 : ℝ) / 4096) = 2695 / 4096 by norm_num] using
      tight_interleaved_list_of_slots (C := 263) hb (by decide) (by decide) (by decide)
        (by decide) hfield (by decide +kernel) h₃ D hn width
  · simpa only [Nat.cast_ofNat, show (1 - (980 : ℝ) / 4096) = 3116 / 4096 by norm_num] using
      tight_interleaved_list_of_slots (C := 222) hb (by decide) (by decide) (by decide)
        (by decide) hfield (by decide +kernel) h₄ D hn width

/-- Four fine-grid (`N = 65536`) slot inequalities strictly beyond `FineGridWideLists`. -/
theorem ultra_fine_65536_slot_certificates :
    rowSlots 65536 1650 495 2274 121442956 <
      columnSlots 32768 45222 1650 495 2274 121442956 ∧
    rowSlots 65536 1200 540 2249 2046046579 <
      columnSlots 16384 30735 1200 540 2249 2046046579 ∧
    rowSlots 65536 850 467 2164 144172924 <
      columnSlots 8192 20925 850 467 2164 144172924 ∧
    rowSlots 65536 650 422 2268 467160053 <
      columnSlots 4096 14310 650 422 2268 467160053 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- Fine-grid (`N = 65536`) beyond-Johnson interleaved list bounds at `20314/65536`,
`34801/65536`, `44611/65536`, and `51226/65536`, each strictly exceeding the corresponding
radius of `FineGridWideLists` while keeping every list multiple below `2^31`. -/
theorem ultra_fine_65536_interleaved_bounds {I F : Type*} [Fintype I] [Field F] {b : ℕ}
    (hb : 0 < b) (hfield : ringChar F = 0 ∨ b * 65536 ≤ ringChar F)
    (D : I ↪ F) (hn : Fintype.card I = b * 65536) (width : ℕ) :
    let bounded := fun (k : ℕ) (r : ℝ) (C : ℕ) =>
      Code.Lambda (Code.interleavedCodeSet (κ := Fin width)
        (code D (b * k) : Set (I → F))) r ≤ ((C * (b * 65536) : ℕ) : ℕ∞)
    bounded 32768 (20314 / 65536) 1254436992 ∧ bounded 16384 (34801 / 65536) 944087037 ∧
      bounded 8192 (44611 / 65536) 455358934 ∧ bounded 4096 (51226 / 65536) 266313397 := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := ultra_fine_65536_slot_certificates
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Nat.cast_ofNat, show (1 - (45222 : ℝ) / 65536) = 20314 / 65536 by norm_num] using
      tight_interleaved_list_of_slots (C := 1254436992) hb (by decide) (by decide) (by decide)
        (by decide) hfield (by decide +kernel) h₁ D hn width
  · simpa only [Nat.cast_ofNat, show (1 - (30735 : ℝ) / 65536) = 34801 / 65536 by norm_num] using
      tight_interleaved_list_of_slots (C := 944087037) hb (by decide) (by decide) (by decide)
        (by decide) hfield (by decide +kernel) h₂ D hn width
  · simpa only [Nat.cast_ofNat, show (1 - (20925 : ℝ) / 65536) = 44611 / 65536 by norm_num] using
      tight_interleaved_list_of_slots (C := 455358934) hb (by decide) (by decide) (by decide)
        (by decide) hfield (by decide +kernel) h₃ D hn width
  · simpa only [Nat.cast_ofNat, show (1 - (14310 : ℝ) / 65536) = 51226 / 65536 by norm_num] using
      tight_interleaved_list_of_slots (C := 266313397) hb (by decide) (by decide) (by decide)
        (by decide) hfield (by decide +kernel) h₄ D hn width

/-! ### Upgraded two-sided smooth list rank brackets (`RankReview.listAnswer`) -/

/-- Certified safe error numerators at reference length `4096` for low-budget fields. -/
def lowBudgetErrors : Fin 4 → ℕ := ![1215, 2089, 2695, 3116]

/-- Linear list-size multiples for `lowBudgetErrors`. -/
def lowBudgetMultiple : Fin 4 → ℕ := ![407, 341, 263, 222]

/-- Certified safe error numerators at reference length `65536` for fine-grid fields. -/
def fineGridErrors : Fin 4 → ℕ := ![20314, 34801, 44611, 51226]

/-- Linear list-size multiples for `fineGridErrors`. -/
def fineGridMultiple : Fin 4 → ℕ := ![1254436992, 944087037, 455358934, 266313397]

/-- Each fine-grid radius strictly exceeds the corresponding radius of `FineGridWideLists`. -/
theorem fineGrid_gt_wide :
    (1269 : ℚ) / 4096 < 20314 / 65536 ∧ (2174 : ℚ) / 4096 < 34801 / 65536 ∧
      (2788 : ℚ) / 4096 < 44611 / 65536 ∧ (3201 : ℚ) / 4096 < 51226 / 65536 := by
  norm_num

/-- On any smooth domain of length `n ≥ 4096` with `ringChar F = 0 ∨ n ≤ ringChar F`,
the low-budget first-order certificates raise the lower bound on `RankReview.listAnswer`
well above the single-step Johnson bound of `SmoothListRankBracket.first_failure_reserved`. -/
theorem first_failure_low_budget {I F : Type} [Fintype I] [Nonempty I] [Field F] [Fintype F]
    [DecidableEq F] (D : I ↪ F) [ReedSolomon.Smooth D] (j : Fin 4) (width : ℕ) [NeZero width]
    (hn : 4096 ≤ Fintype.card I) (hchar : ringChar F = 0 ∨ Fintype.card I ≤ ringChar F)
    (hq : Fintype.card F < 2 ^ 256)
    (hbudget : lowBudgetMultiple j * Fintype.card I ≤ Fintype.card F / 2 ^ 128) :
    let n := Fintype.card I
    let k := prizeDimension (ι := I) j
    let h := ProximityPrize.SmoothPrizeCapacityTable.failureLength j
    let c := ProximityPrize.SmoothReservedListBoundary.errorCoefficient j
    ∃ e : Fin (n + 1),
      ProximityPrize.RankReview.listAnswer D (prizeThreshold : ℝ≥0) k width = some e ∧
      lowBudgetErrors j * (n / 4096) + 1 ≤ e.val ∧ e.val ≤ c * (n / h) + 1 := by
  classical
  have hlenBase : ProximityPrize.SmoothPrizeCapacityTable.failureLength j ≤ Fintype.card I :=
    le_trans (by fin_cases j <;> decide) hn
  obtain ⟨mRes, e, _, hlenRes, he, hhi⟩ :=
    ProximityPrize.SmoothReservedListBoundary.first_failure_le D j width hlenBase hq
  have hpRes : 0 < ProximityPrize.SmoothPrizeCapacityTable.failureLength j := by
    fin_cases j <;> decide
  have hdivRes :
      Fintype.card I / ProximityPrize.SmoothPrizeCapacityTable.failureLength j = mRes := by
    rw [hlenRes, Nat.mul_div_cancel _ hpRes]
  obtain ⟨b, hb, hlen4096, hdim⟩ :=
    ProximityPrize.SmoothPrizeCapacityTable.dimensions D j ⟨12, by decide⟩ hn
      (by fin_cases j <;> decide)
  have hdiv4096 : Fintype.card I / 4096 = b := by
    rw [hlen4096, Nat.mul_div_cancel _ (by decide : 0 < 4096)]
  have hchar' : ringChar F = 0 ∨ b * 4096 ≤ ringChar F := by rwa [← hlen4096]
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  let a := lowBudgetErrors j * b
  let z : ℝ≥0 := (a : ℝ≥0) / (Fintype.card I : ℝ≥0)
  have han : a ≤ Fintype.card I := by
    rw [hlen4096]
    have hle : lowBudgetErrors j ≤ 4096 := by fin_cases j <;> decide
    dsimp only [a]
    nlinarith
  have hnr : 0 < (Fintype.card I : ℝ≥0) := by exact_mod_cast Fintype.card_pos (α := I)
  have hz1 : z ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast han) hnr.le
  have hzReal : (z : ℝ) = (lowBudgetErrors j : ℝ) / 4096 := by
    simp only [z, a, hlen4096, NNReal.coe_div, NNReal.coe_natCast]
    push_cast
    calc
      (lowBudgetErrors j : ℝ) * (b : ℝ) / ((b : ℝ) * 4096) =
          (b : ℝ) * (lowBudgetErrors j : ℝ) / ((b : ℝ) * 4096) := by ring
      _ = (lowBudgetErrors j : ℝ) / 4096 := mul_div_mul_left _ _ hbR
  have hlambda : Code.Lambda (Code.interleavedCodeSet (κ := Fin width)
      (code D (prizeDimension (ι := I) j) : Set (I → F))) (z : ℝ) ≤
      ((lowBudgetMultiple j * Fintype.card I : ℕ) : ℕ∞) := by
    have hbounds := low_budget_4096_interleaved_bounds hb hchar' D hlen4096 width
    let target (k' : ℕ) (r' : ℝ) (M' : ℕ) : Prop :=
      Code.Lambda (Code.interleavedCodeSet (κ := Fin width)
        (code D k' : Set (I → F))) r' ≤ ((M' : ℕ) : ℕ∞)
    change target (prizeDimension (ι := I) j) (z : ℝ) (lowBudgetMultiple j * Fintype.card I)
    rw [hdim, hzReal, hlen4096]
    rcases j with ⟨_ | _ | _ | _ | n, hj⟩
    · rw [show (⟨0, hj⟩ : Fin 4) = 0 from Fin.ext rfl,
        show 4096 / prizeDenominator 0 = 2048 by decide, Nat.mul_comm 2048 b,
        show lowBudgetErrors 0 = 1215 by decide,
        show ((1215 : ℕ) : ℝ) = 1215 by norm_num,
        show lowBudgetMultiple 0 = 407 by decide]
      exact hbounds.1
    · rw [show (⟨1, hj⟩ : Fin 4) = 1 from Fin.ext rfl,
        show 4096 / prizeDenominator 1 = 1024 by decide, Nat.mul_comm 1024 b,
        show lowBudgetErrors 1 = 2089 by decide,
        show ((2089 : ℕ) : ℝ) = 2089 by norm_num,
        show lowBudgetMultiple 1 = 341 by decide]
      exact hbounds.2.1
    · rw [show (⟨2, hj⟩ : Fin 4) = 2 from Fin.ext rfl,
        show 4096 / prizeDenominator 2 = 512 by decide, Nat.mul_comm 512 b,
        show lowBudgetErrors 2 = 2695 by decide,
        show ((2695 : ℕ) : ℝ) = 2695 by norm_num,
        show lowBudgetMultiple 2 = 263 by decide]
      exact hbounds.2.2.1
    · rw [show (⟨3, hj⟩ : Fin 4) = 3 from Fin.ext rfl,
        show 4096 / prizeDenominator 3 = 256 by decide, Nat.mul_comm 256 b,
        show lowBudgetErrors 3 = 3116 by decide,
        show ((3116 : ℕ) : ℝ) = 3116 by norm_num,
        show lowBudgetMultiple 3 = 222 by decide]
      exact hbounds.2.2.2
    · omega
  have hc := ProximityPrize.RankReview.listAnswer_correct D (prizeThreshold : ℝ≥0)
    (prizeDimension (ι := I) j) width (Nat.div_le_self _ _)
  have hpass : z < (e.val : ℝ≥0) / (Fintype.card I : ℝ≥0) := by
    have hcorr := (hc z hz1).mp ((FourRateList128.budget_cast (Fintype.card F) _).mpr
      (hlambda.trans (by exact_mod_cast hbudget)))
    rwa [he] at hcorr
  have hlow : a < e.val := by
    exact_mod_cast (div_lt_div_iff_of_pos_right hnr).mp hpass
  refine ⟨e, he, ?_, ?_⟩
  · rw [hdiv4096]
    exact Nat.succ_le_of_lt hlow
  · rw [hdivRes]
    exact hhi

/-- On any smooth domain of length `n ≥ 65536` with `ringChar F = 0 ∨ n ≤ ringChar F` and
`fineGridMultiple j * n ≤ |F| / 2^128` (in particular whenever `2^159 * n ≤ |F| < 2^256`),
the fine-grid first-order certificates bracket `RankReview.listAnswer` strictly above the
wide `4096`-grid radii across all four prize rates and all positive interleaving widths. -/
theorem first_failure_fine_grid {I F : Type} [Fintype I] [Nonempty I] [Field F] [Fintype F]
    [DecidableEq F] (D : I ↪ F) [ReedSolomon.Smooth D] (j : Fin 4) (width : ℕ) [NeZero width]
    (hn : 65536 ≤ Fintype.card I) (hchar : ringChar F = 0 ∨ Fintype.card I ≤ ringChar F)
    (hq : Fintype.card F < 2 ^ 256)
    (hbudget : fineGridMultiple j * Fintype.card I ≤ Fintype.card F / 2 ^ 128) :
    let n := Fintype.card I
    let k := prizeDimension (ι := I) j
    let h := ProximityPrize.SmoothPrizeCapacityTable.failureLength j
    let c := ProximityPrize.SmoothReservedListBoundary.errorCoefficient j
    ∃ e : Fin (n + 1),
      ProximityPrize.RankReview.listAnswer D (prizeThreshold : ℝ≥0) k width = some e ∧
      fineGridErrors j * (n / 65536) + 1 ≤ e.val ∧ e.val ≤ c * (n / h) + 1 := by
  classical
  have hlenBase : ProximityPrize.SmoothPrizeCapacityTable.failureLength j ≤ Fintype.card I :=
    le_trans (by fin_cases j <;> decide) hn
  obtain ⟨mRes, e, _, hlenRes, he, hhi⟩ :=
    ProximityPrize.SmoothReservedListBoundary.first_failure_le D j width hlenBase hq
  have hpRes : 0 < ProximityPrize.SmoothPrizeCapacityTable.failureLength j := by
    fin_cases j <;> decide
  have hdivRes :
      Fintype.card I / ProximityPrize.SmoothPrizeCapacityTable.failureLength j = mRes := by
    rw [hlenRes, Nat.mul_div_cancel _ hpRes]
  obtain ⟨b, hb, hlen65536, hdim⟩ :=
    ProximityPrize.SmoothPrizeCapacityTable.dimensions D j ⟨16, by decide⟩ hn
      (by fin_cases j <;> decide)
  have hdiv65536 : Fintype.card I / 65536 = b := by
    rw [hlen65536, Nat.mul_div_cancel _ (by decide : 0 < 65536)]
  have hchar' : ringChar F = 0 ∨ b * 65536 ≤ ringChar F := by rwa [← hlen65536]
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  let a := fineGridErrors j * b
  let z : ℝ≥0 := (a : ℝ≥0) / (Fintype.card I : ℝ≥0)
  have han : a ≤ Fintype.card I := by
    rw [hlen65536]
    have hle : fineGridErrors j ≤ 65536 := by fin_cases j <;> decide
    dsimp only [a]
    nlinarith
  have hnr : 0 < (Fintype.card I : ℝ≥0) := by exact_mod_cast Fintype.card_pos (α := I)
  have hz1 : z ≤ 1 := div_le_one_of_le₀ (by exact_mod_cast han) hnr.le
  have hzReal : (z : ℝ) = (fineGridErrors j : ℝ) / 65536 := by
    simp only [z, a, hlen65536, NNReal.coe_div, NNReal.coe_natCast]
    push_cast
    calc
      (fineGridErrors j : ℝ) * (b : ℝ) / ((b : ℝ) * 65536) =
          (b : ℝ) * (fineGridErrors j : ℝ) / ((b : ℝ) * 65536) := by ring
      _ = (fineGridErrors j : ℝ) / 65536 := mul_div_mul_left _ _ hbR
  have hlambda : Code.Lambda (Code.interleavedCodeSet (κ := Fin width)
      (code D (prizeDimension (ι := I) j) : Set (I → F))) (z : ℝ) ≤
      ((fineGridMultiple j * Fintype.card I : ℕ) : ℕ∞) := by
    have hbounds := ultra_fine_65536_interleaved_bounds hb hchar' D hlen65536 width
    let target (k' : ℕ) (r' : ℝ) (M' : ℕ) : Prop :=
      Code.Lambda (Code.interleavedCodeSet (κ := Fin width)
        (code D k' : Set (I → F))) r' ≤ ((M' : ℕ) : ℕ∞)
    change target (prizeDimension (ι := I) j) (z : ℝ) (fineGridMultiple j * Fintype.card I)
    rw [hdim, hzReal, hlen65536]
    rcases j with ⟨_ | _ | _ | _ | n, hj⟩
    · rw [show (⟨0, hj⟩ : Fin 4) = 0 from Fin.ext rfl,
        show 65536 / prizeDenominator 0 = 32768 by decide, Nat.mul_comm 32768 b,
        show fineGridErrors 0 = 20314 by decide,
        show ((20314 : ℕ) : ℝ) = 20314 by norm_num,
        show fineGridMultiple 0 = 1254436992 by decide]
      exact hbounds.1
    · rw [show (⟨1, hj⟩ : Fin 4) = 1 from Fin.ext rfl,
        show 65536 / prizeDenominator 1 = 16384 by decide, Nat.mul_comm 16384 b,
        show fineGridErrors 1 = 34801 by decide,
        show ((34801 : ℕ) : ℝ) = 34801 by norm_num,
        show fineGridMultiple 1 = 944087037 by decide]
      exact hbounds.2.1
    · rw [show (⟨2, hj⟩ : Fin 4) = 2 from Fin.ext rfl,
        show 65536 / prizeDenominator 2 = 8192 by decide, Nat.mul_comm 8192 b,
        show fineGridErrors 2 = 44611 by decide,
        show ((44611 : ℕ) : ℝ) = 44611 by norm_num,
        show fineGridMultiple 2 = 455358934 by decide]
      exact hbounds.2.2.1
    · rw [show (⟨3, hj⟩ : Fin 4) = 3 from Fin.ext rfl,
        show 65536 / prizeDenominator 3 = 4096 by decide, Nat.mul_comm 4096 b,
        show fineGridErrors 3 = 51226 by decide,
        show ((51226 : ℕ) : ℝ) = 51226 by norm_num,
        show fineGridMultiple 3 = 266313397 by decide]
      exact hbounds.2.2.2
    · omega
  have hc := ProximityPrize.RankReview.listAnswer_correct D (prizeThreshold : ℝ≥0)
    (prizeDimension (ι := I) j) width (Nat.div_le_self _ _)
  have hpass : z < (e.val : ℝ≥0) / (Fintype.card I : ℝ≥0) := by
    have hcorr := (hc z hz1).mp ((FourRateList128.budget_cast (Fintype.card F) _).mpr
      (hlambda.trans (by exact_mod_cast hbudget)))
    rwa [he] at hcorr
  have hlow : a < e.val := by
    exact_mod_cast (div_lt_div_iff_of_pos_right hnr).mp hpass
  refine ⟨e, he, ?_, ?_⟩
  · rw [hdiv65536]
    exact Nat.succ_le_of_lt hlow
  · rw [hdivRes]
    exact hhi

/-- Explicit production (`n = 2^30`) two-sided rank brackets over every prime field with
`2^189 ≤ p < 2^256` admitting a smooth length-`2^30` evaluation domain (such as
`FourRateListPrime246.K`, the BLS12-381 scalar field, and the Pasta Pallas/Vesta fields),
raising the safe 128-bit list floor to `332824577`, `570179585`, `730906625`, and `839286785`
across all positive interleaving widths. -/
def productionSafeFloor : Fin 4 → ℕ := ![332824577, 570179585, 730906625, 839286785]

/-- Upper endpoints from `SmoothReservedListBoundary` at `n = 2^30`. -/
def productionReservedCeiling : Fin 4 → ℕ := ![528482305, 796917761, 931135489, 1002438657]

theorem prime_production_rank_brackets {I : Type} [Fintype I] [Nonempty I] {p : ℕ}
    [Fact p.Prime] (D : I ↪ ZMod p) [ReedSolomon.Smooth D]
    (hn : Fintype.card I = 2 ^ 30) (hlo : 2 ^ 189 ≤ p) (hhi : p < 2 ^ 256)
    (j : Fin 4) (width : ℕ) [NeZero width] :
    ∃ e : Fin (Fintype.card I + 1),
      ProximityPrize.RankReview.listAnswer D (prizeThreshold : ℝ≥0)
        (prizeDimension (ι := I) j) width = some e ∧
      productionSafeFloor j ≤ e.val ∧ e.val ≤ productionReservedCeiling j := by
  have hchar : ringChar (ZMod p) = 0 ∨ Fintype.card I ≤ ringChar (ZMod p) := by
    right
    rw [ZMod.ringChar_zmod_n]
    simpa only [ZMod.card] using Fintype.card_le_of_injective D D.injective
  have hmult : fineGridMultiple j ≤ 2 ^ 31 := by fin_cases j <;> decide
  have hbudget : fineGridMultiple j * Fintype.card I ≤ Fintype.card (ZMod p) / 2 ^ 128 := by
    rw [ZMod.card, hn, Nat.le_div_iff_mul_le (by decide : 0 < 2 ^ 128)]
    calc
      fineGridMultiple j * 2 ^ 30 * 2 ^ 128 ≤ 2 ^ 31 * 2 ^ 30 * 2 ^ 128 := by gcongr
      _ = 2 ^ 189 := by decide
      _ ≤ p := hlo
  obtain ⟨e, he, hfloor, hceil⟩ := first_failure_fine_grid D j width
    (by rw [hn]; decide) hchar (by rwa [ZMod.card]) hbudget
  refine ⟨e, he, ?_, ?_⟩
  · have heq : productionSafeFloor j = fineGridErrors j * (Fintype.card I / 65536) + 1 := by
      rw [hn]
      fin_cases j <;> decide
    rwa [heq]
  · have heq :
        ProximityPrize.SmoothReservedListBoundary.errorCoefficient j *
          (Fintype.card I / ProximityPrize.SmoothPrizeCapacityTable.failureLength j) + 1 =
        productionReservedCeiling j := by
      rw [hn]
      fin_cases j <;> decide
    rwa [← heq]

/-- Instantiation on the named 246-bit prime field `FourRateListPrime246.K`. -/
theorem prime246_production_rank_brackets {I : Type} [Fintype I] [Nonempty I]
    (D : I ↪ FourRateListPrime246.K) [ReedSolomon.Smooth D]
    (hn : Fintype.card I = 2 ^ 30) (j : Fin 4) (width : ℕ) [NeZero width] :
    ∃ e : Fin (Fintype.card I + 1),
      ProximityPrize.RankReview.listAnswer D (prizeThreshold : ℝ≥0)
        (prizeDimension (ι := I) j) width = some e ∧
      productionSafeFloor j ≤ e.val ∧ e.val ≤ productionReservedCeiling j :=
  prime_production_rank_brackets D hn (by decide) (by decide) j width

end ProximityGap.CarbonListTightFirstOrder

#print axioms ProximityGap.CarbonListTightFirstOrder.tight_interleaved_list_of_slots
#print axioms ProximityGap.CarbonListTightFirstOrder.tight_128_interleaved_bounds
#print axioms ProximityGap.CarbonListTightFirstOrder.tight_4096_interleaved_bounds
#print axioms ProximityGap.CarbonListTightFirstOrder.tight_wide_4096_interleaved_bounds
#print axioms ProximityGap.CarbonListTightFirstOrder.low_budget_4096_interleaved_bounds
#print axioms ProximityGap.CarbonListTightFirstOrder.ultra_fine_65536_interleaved_bounds
#print axioms ProximityGap.CarbonListTightFirstOrder.first_failure_low_budget
#print axioms ProximityGap.CarbonListTightFirstOrder.first_failure_fine_grid
#print axioms ProximityGap.CarbonListTightFirstOrder.prime_production_rank_brackets
#print axioms ProximityGap.CarbonListTightFirstOrder.prime246_production_rank_brackets
