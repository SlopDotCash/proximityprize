/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMomentLadder
import Mathlib.Tactic

/-!
# General-`r` anti-concentration from the moment ladder (#357/#389)

From `subgroup_gaussSum_moment` (`∑_b ‖η_b‖^{2r} = q·E_r(G)`), Markov at the `r`-th power of the
Johnson scale gives, for every `r ≥ 1`,

  `#{b : ‖η_b‖² ≥ q} · q^{r-1} ≤ E_r(G)`,    i.e.    `#{·} ≤ E_r(G)/q^{r-1}`,

and with the trivial `energyR_le_pow` (`E_r(G) ≤ |G|^{2r-1}`) the no-Johnson threshold is
`|G|^{2r-1} < q^{r-1}` — which tends to `|G| < q^{1/2}` as `r → ∞`, the strongest count-side
anti-concentration the moment method yields. Average/count side only; the open core is untouched.
-/

set_option linter.style.longLine false


open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMomentLadder

namespace ArkLib.ProximityGap.SubgroupGaussSumMomentLadder

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **General Markov count bound.** For `r ≥ 1`, `#{b : ‖η_b‖² ≥ q} · q^{r-1} ≤ E_r(G)`. -/
theorem card_johnson_scale_frequencies_mul_le_energyR {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (r : ℕ) (hr : 1 ≤ r) (hq : 0 < Fintype.card F) :
    ((Finset.univ.filter (fun b : F => (Fintype.card F : ℝ) ≤ ‖eta ψ G b‖ ^ 2)).card : ℝ)
        * (Fintype.card F : ℝ) ^ (r - 1)
      ≤ (energyR G r : ℝ) := by
  classical
  set q : ℝ := (Fintype.card F : ℝ) with hqdef
  have hqpos : (0 : ℝ) < q := by rw [hqdef]; exact_mod_cast hq
  set S := Finset.univ.filter (fun b : F => q ≤ ‖eta ψ G b‖ ^ 2) with hS
  have hstep : (S.card : ℝ) * q ^ r ≤ q * (energyR G r : ℝ) := by
    calc (S.card : ℝ) * q ^ r
        = ∑ _b ∈ S, q ^ r := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ b ∈ S, ‖eta ψ G b‖ ^ (2 * r) := by
            refine Finset.sum_le_sum (fun b hb => ?_)
            have hb2 : q ≤ ‖eta ψ G b‖ ^ 2 := (Finset.mem_filter.mp hb).2
            have h2r : ‖eta ψ G b‖ ^ (2 * r) = (‖eta ψ G b‖ ^ 2) ^ r := by
              rw [← pow_mul, Nat.mul_comm]
            rw [h2r]
            gcongr
      _ ≤ ∑ b : F, ‖eta ψ G b‖ ^ (2 * r) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
              (fun b _ _ => by positivity)
      _ = q * (energyR G r : ℝ) := by rw [subgroup_gaussSum_moment hψ G r]
  -- `q^r = q^{r-1}·q` (uses `r ≥ 1`); cancel one `q`
  have hqr : q ^ r = q ^ (r - 1) * q := by rw [← pow_succ, Nat.sub_add_cancel hr]
  rw [hqr] at hstep
  have hfac : (S.card : ℝ) * (q ^ (r - 1) * q) = ((S.card : ℝ) * q ^ (r - 1)) * q := by ring
  rw [hfac, mul_comm q (energyR G r : ℝ)] at hstep
  exact le_of_mul_le_mul_right hstep hqpos

/-- **The `r`-fold additive energy is at most `|G|^{2r-1}`** (for `r ≥ 1`): fix the first tuple
(`|G|^r` ways) and the first `r-1` coordinates of the second (`|G|^{r-1}` ways); the last coordinate
of the second is then forced by the equal-sum condition. -/
theorem energyR_le_pow (G : Finset F) (m : ℕ) :
    energyR G (m + 1) ≤ G.card ^ (2 * (m + 1) - 1) := by
  classical
  -- `energyR = ∑_{x} #{z : ∑x = ∑z}`; bound the inner fiber by `|G|^m`.
  have hfiber : ∀ x : Fin (m + 1) → F,
      ((Fintype.piFinset (fun _ : Fin (m + 1) => G)).filter
        (fun z => ∑ i, x i = ∑ i, z i)).card ≤ G.card ^ m := by
    intro x
    -- inject `z ↦ z ∘ Fin.castSucc` into `Fin m → G`; the last coordinate is recovered from the sum
    have hinj : Set.InjOn (fun z : Fin (m + 1) → F => fun i : Fin m => z i.castSucc)
        ↑((Fintype.piFinset (fun _ : Fin (m + 1) => G)).filter
          (fun z => ∑ i, x i = ∑ i, z i)) := by
      intro z hz z' hz' heq
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_coe,
        Fintype.mem_piFinset] at hz hz'
      funext j
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · exact congrFun heq j'
      · have hcs : ∑ i : Fin m, z i.castSucc = ∑ i : Fin m, z' i.castSucc :=
          Finset.sum_congr rfl (fun i _ => congrFun heq i)
        have hsum_eq : ∑ i, z i = ∑ i, z' i := by rw [← hz.2, ← hz'.2]
        rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, hcs] at hsum_eq
        exact add_left_cancel hsum_eq
    calc ((Fintype.piFinset (fun _ : Fin (m + 1) => G)).filter
            (fun z => ∑ i, x i = ∑ i, z i)).card
        ≤ (Fintype.piFinset (fun _ : Fin m => G)).card := by
          refine Finset.card_le_card_of_injOn
            (fun z => fun i : Fin m => z i.castSucc) (fun z hz => ?_) hinj
          have hz1 := (Finset.mem_filter.mp hz).1
          exact Fintype.mem_piFinset.mpr (fun i => (Fintype.mem_piFinset.mp hz1) i.castSucc)
      _ = G.card ^ m := by simp [Fintype.card_piFinset]
  -- sum the fiber bound over `x`
  have hkey : energyR G (m + 1)
      ≤ ∑ _x ∈ Fintype.piFinset (fun _ : Fin (m + 1) => G), G.card ^ m := by
    rw [energyR]
    refine Finset.sum_le_sum (fun x _ => ?_)
    rw [Finset.sum_boole]
    exact hfiber x
  calc energyR G (m + 1)
      ≤ ∑ _x ∈ Fintype.piFinset (fun _ : Fin (m + 1) => G), G.card ^ m := hkey
    _ = G.card ^ (m + 1) * G.card ^ m := by
        rw [Finset.sum_const, Fintype.card_piFinset]
        simp [mul_comm]
    _ = G.card ^ (2 * (m + 1) - 1) := by
        rw [← pow_add]; congr 1; omega

/-- **The general `q^{1/2}` no-Johnson threshold.** If `|G|^{2m+1} < q^m` then *no* frequency reaches
the Johnson scale `‖η_b‖² ≥ q`. The condition `|G|^{2m+1} < q^m` is `|G| < q^{m/(2m+1)}`, and
`m/(2m+1) → 1/2` as `m → ∞`: the moment ladder drives the no-Johnson threshold up to `|G| < q^{1/2}`. -/
theorem no_johnson_scale_frequency_of_ladder {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (m : ℕ) (hq : 0 < Fintype.card F)
    (hlt : (G.card : ℝ) ^ (2 * m + 1) < (Fintype.card F : ℝ) ^ m) :
    (Finset.univ.filter (fun b : F => (Fintype.card F : ℝ) ≤ ‖eta ψ G b‖ ^ 2)) = ∅ := by
  classical
  by_contra hne
  have hnemp : (Finset.univ.filter (fun b : F => (Fintype.card F : ℝ) ≤ ‖eta ψ G b‖ ^ 2)).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hne
  have hcard1 : (1 : ℝ) ≤
      ((Finset.univ.filter (fun b : F => (Fintype.card F : ℝ) ≤ ‖eta ψ G b‖ ^ 2)).card : ℝ) := by
    exact_mod_cast Finset.Nonempty.card_pos hnemp
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) ^ m := by
    have : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast hq
    positivity
  have hb := card_johnson_scale_frequencies_mul_le_energyR hψ G (m + 1) (Nat.le_add_left 1 m) hq
  simp only [Nat.add_sub_cancel] at hb
  have he : (energyR G (m + 1) : ℝ) ≤ (G.card : ℝ) ^ (2 * (m + 1) - 1) := by
    exact_mod_cast energyR_le_pow G m
  have h2m1 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  rw [h2m1] at he
  -- `q^m ≤ #S·q^m ≤ E ≤ |G|^{2m+1} < q^m`, contradiction
  have hq2le : (Fintype.card F : ℝ) ^ m ≤
      ((Finset.univ.filter (fun b : F => (Fintype.card F : ℝ) ≤ ‖eta ψ G b‖ ^ 2)).card : ℝ)
        * (Fintype.card F : ℝ) ^ m := by
    nlinarith [hcard1, hqpos]
  linarith [hq2le, hb, he, hlt]

end ArkLib.ProximityGap.SubgroupGaussSumMomentLadder

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMomentLadder.card_johnson_scale_frequencies_mul_le_energyR
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMomentLadder.energyR_le_pow
#print axioms ArkLib.ProximityGap.SubgroupGaussSumMomentLadder.no_johnson_scale_frequency_of_ladder
