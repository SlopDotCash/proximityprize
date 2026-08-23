/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GaussPeriodCosetReduction

/-!
# The first UNCONDITIONAL sub-√q ceiling for the subgroup Gauss period (#407)

`GaussPeriodCosetReduction.cosetReduced_eta_pow_le` (#419) gives, for a finite multiplicative
subgroup `G = μ_n` and every `b ≠ 0`,
`‖η_b‖^{2r} ≤ (q·E_r(G) − n^{2r}) / n`,
in terms of the `r`-fold additive energy `E_r = rEnergy G r`. Most consumers feed this the
**conditional** energy hypothesis `GaussianEnergyBound` (`E_r ≤ (2r-1)‼·n^r`), whose char-`p`
transfer is the open core.

This file takes the `r = 2` slice and feeds it the **unconditional** additive-energy bound
`E_2(G) = rEnergy G 2 ≤ |G|^3` — the textbook `E(A) ≤ |A|^3` (fix three of the four summands;
the fourth is determined, so at most one choice). That gives

> `‖η_b‖^4 ≤ (q·n^3 − n^4)/n = n^2·(q − n)`,   hence   `M(n) ≤ √n · (q − n)^{1/4}`,

the **first unconditional sub-√q ceiling** (`n^2(q-n) < q^2 ⟺ n^2 < q`), binding in the band
`q ~ n^2`. No char-`p` energy input, no Lam–Leung, no BGK: a real theorem.

Axiom-clean. Issue #407.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.GaussPeriodCosetReduction

namespace ArkLib.ProximityGap.EtaQuarticUncond

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] in
/-- **Inner count: at most `|G|` pairs `(w₀,w₁) ∈ G²` have a prescribed sum `S`.**
For a fixed value `S`, the set of `w ∈ G × G` (encoded as `Fin 2 → G`) with `w₀ + w₁ = S`
injects into `G` via `w ↦ w 0`: knowing `w 0` forces `w 1 = S − w 0`, and a `Fin 2 → F` is
determined by its two values. -/
theorem card_fiber_le_card (G : Finset F) (S : F) :
    #{w ∈ Fintype.piFinset (fun _ : Fin 2 => G) | S = ∑ i, w i} ≤ G.card := by
  classical
  refine Finset.card_le_card_of_injOn (fun w => w 0) ?_ ?_
  · -- maps into G
    intro w hw
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hw
    exact hw.1 0
  · -- injective on the fiber
    intro w hw w' hw' hww
    simp only [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset] at hw hw'
    simp only at hww
    have hsum : ∑ i, w i = ∑ i, w' i := by rw [← hw.2, ← hw'.2]
    rw [Fin.sum_univ_two, Fin.sum_univ_two] at hsum
    -- w 0 = w' 0 (hypothesis) and w 0 + w 1 = w' 0 + w' 1 ⟹ w 1 = w' 1
    have h1 : w 1 = w' 1 := by rw [hww] at hsum; exact add_left_cancel hsum
    funext i
    fin_cases i
    · exact hww
    · exact h1

omit [Fintype F] in
/-- **The unconditional 2-fold additive-energy bound `E_2(G) ≤ |G|^3`.**
`rEnergy G 2 = ∑_{v ∈ G²} #{w ∈ G² : ∑w = ∑v} ≤ ∑_{v ∈ G²} |G| = |G|^2 · |G| = |G|^3`. -/
theorem rEnergy_two_le_card_cubed (G : Finset F) :
    rEnergy G 2 ≤ (G.card) ^ 3 := by
  classical
  have hpiCard : (Fintype.piFinset (fun _ : Fin 2 => G)).card = G.card ^ 2 := by
    rw [Fintype.card_piFinset]
    simp [Finset.prod_const, Finset.card_univ]
  calc rEnergy G 2
      = ∑ v ∈ Fintype.piFinset (fun _ : Fin 2 => G),
          #{w ∈ Fintype.piFinset (fun _ : Fin 2 => G) | ∑ i, v i = ∑ i, w i} := by
        simp only [rEnergy]
        refine Finset.sum_congr rfl (fun v _ => ?_)
        exact (Finset.card_filter (fun w : Fin 2 → F => ∑ i, v i = ∑ i, w i) _).symm
    _ ≤ ∑ _v ∈ Fintype.piFinset (fun _ : Fin 2 => G), G.card :=
        Finset.sum_le_sum (fun v _ => card_fiber_le_card G (∑ i, v i))
    _ = G.card ^ 2 * G.card := by rw [Finset.sum_const, hpiCard, smul_eq_mul]
    _ = G.card ^ 3 := by ring

/-- **The first unconditional sub-√q ceiling.** For a finite multiplicative subgroup `G = μ_n`
(`hbij`, `h0`, `hne`) of `F^×` and every nonzero frequency `b₀`,
`‖η_{b₀}‖^4 ≤ n^2·(q − n)`,  `q = |F|`, `n = |G|`.
Equivalently `M(n) ≤ √n·(q − n)^{1/4}`. Proved from the coset-reduced moment bound
(`cosetReduced_eta_pow_le` at `r = 2`) and the unconditional energy bound
(`rEnergy_two_le_card_cubed`); no char-`p` energy hypothesis. -/
theorem eta_quartic_le_uncond {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    (hbij : ∀ u ∈ G, G.image (fun y => u * y) = G) (h0 : (0 : F) ∉ G) (hne : G.Nonempty)
    {b₀ : F} (hb₀ : b₀ ≠ 0) :
    ‖eta ψ G b₀‖ ^ 4 ≤ (G.card : ℝ) ^ 2 * ((Fintype.card F : ℝ) - (G.card : ℝ)) := by
  have hcardpos : 0 < (G.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hne
  -- coset-reduced moment bound at r = 2 (2*2 = 4)
  have hcoset := cosetReduced_eta_pow_le hψ hbij h0 hne 2 hb₀
  -- unconditional energy bound, cast to ℝ
  have henergy : (rEnergy G 2 : ℝ) ≤ (G.card : ℝ) ^ 3 := by
    exact_mod_cast rEnergy_two_le_card_cubed G
  -- assemble: numerator monotone, divide by n > 0, then simplify the rhs
  have hQpos : (0 : ℝ) ≤ (Fintype.card F : ℝ) := by positivity
  have hmono : (Fintype.card F : ℝ) * (rEnergy G 2 : ℝ) - (G.card : ℝ) ^ (2 * 2)
      ≤ (Fintype.card F : ℝ) * (G.card : ℝ) ^ 3 - (G.card : ℝ) ^ (2 * 2) := by
    have := mul_le_mul_of_nonneg_left henergy hQpos
    linarith
  have hbound : ‖eta ψ G b₀‖ ^ (2 * 2)
      ≤ ((Fintype.card F : ℝ) * (G.card : ℝ) ^ 3 - (G.card : ℝ) ^ (2 * 2)) / (G.card : ℝ) :=
    le_trans hcoset (div_le_div_of_nonneg_right hmono hcardpos.le)
  -- rewrite (q·n^3 − n^4)/n = n^2·(q − n) and 2*2 = 4
  have hrw : ((Fintype.card F : ℝ) * (G.card : ℝ) ^ 3 - (G.card : ℝ) ^ (2 * 2)) / (G.card : ℝ)
      = (G.card : ℝ) ^ 2 * ((Fintype.card F : ℝ) - (G.card : ℝ)) := by
    field_simp
    ring
  rw [hrw] at hbound
  -- (2 * 2) = 4 on the LHS exponent
  have h44 : (2 * 2 : ℕ) = 4 := by norm_num
  rw [h44] at hbound
  exact hbound

/-- **The first unconditional sub-√q ceiling, in norm form.** Taking the 4-th root of
`eta_quartic_le_uncond`: for every nonzero frequency `b₀`,
`‖η_{b₀}‖ ≤ √n · (q − n)^{1/4}`,  `q = |F|`, `n = |G|`.
Since this holds for *every* `b₀ ≠ 0` it bounds the worst-case period
`M(n) = max_{b≠0}‖η_b‖ ≤ √n·(q−n)^{1/4}`. Genuinely sub-`√q`: the square is
`n·√(q−n) < n·√q`, and `M < √q ⟺ n^2 < q`, binding in the band `q ~ n^2`.
Unconditional — no char-`p` energy hypothesis, no BGK, no Lam–Leung. -/
theorem eta_le_uncond_norm {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {G : Finset F}
    (hbij : ∀ u ∈ G, G.image (fun y => u * y) = G) (h0 : (0 : F) ∉ G) (hne : G.Nonempty)
    {b₀ : F} (hb₀ : b₀ ≠ 0) :
    ‖eta ψ G b₀‖
      ≤ Real.sqrt (G.card : ℝ)
        * ((Fintype.card F : ℝ) - (G.card : ℝ)) ^ ((4 : ℕ)⁻¹ : ℝ) := by
  have hquartic := eta_quartic_le_uncond hψ hbij h0 hne hb₀
  have hcardpos : 0 < (G.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hne
  -- `q − n ≥ 0`: else the rhs `n²·(q−n)` is `< 0`, contradicting `‖η‖⁴ ≥ 0`.
  have hqn : (0 : ℝ) ≤ (Fintype.card F : ℝ) - (G.card : ℝ) := by
    by_contra hlt
    rw [not_le] at hlt
    have hrhs_neg : (G.card : ℝ) ^ 2 * ((Fintype.card F : ℝ) - (G.card : ℝ)) < 0 :=
      mul_neg_of_pos_of_neg (by positivity) hlt
    have : (0 : ℝ) ≤ ‖eta ψ G b₀‖ ^ 4 := by positivity
    linarith
  set R : ℝ := Real.sqrt (G.card : ℝ)
      * ((Fintype.card F : ℝ) - (G.card : ℝ)) ^ ((4 : ℕ)⁻¹ : ℝ) with hR
  have hRnonneg : 0 ≤ R := by
    rw [hR]; positivity
  -- the 4-th power of the rhs is exactly `n²·(q−n)`
  have hR4 : R ^ 4 = (G.card : ℝ) ^ 2 * ((Fintype.card F : ℝ) - (G.card : ℝ)) := by
    rw [hR, mul_pow]
    have hsq4 : (Real.sqrt (G.card : ℝ)) ^ 4 = (G.card : ℝ) ^ 2 := by
      have h2 : (Real.sqrt (G.card : ℝ)) ^ 2 = (G.card : ℝ) := Real.sq_sqrt hcardpos.le
      calc (Real.sqrt (G.card : ℝ)) ^ 4
          = ((Real.sqrt (G.card : ℝ)) ^ 2) ^ 2 := by ring
        _ = (G.card : ℝ) ^ 2 := by rw [h2]
    have hroot4 : (((Fintype.card F : ℝ) - (G.card : ℝ)) ^ ((4 : ℕ)⁻¹ : ℝ)) ^ 4
        = (Fintype.card F : ℝ) - (G.card : ℝ) :=
      Real.rpow_inv_natCast_pow hqn (by norm_num)
    rw [hsq4, hroot4]
  -- 4-th root monotonicity: `‖η‖⁴ ≤ R⁴` with `0 ≤ R` gives `‖η‖ ≤ R`.
  have hpow_le : ‖eta ψ G b₀‖ ^ 4 ≤ R ^ 4 := by rw [hR4]; exact hquartic
  exact le_of_pow_le_pow_left₀ (by norm_num) hRnonneg hpow_le

end ArkLib.ProximityGap.EtaQuarticUncond

#print axioms ArkLib.ProximityGap.EtaQuarticUncond.card_fiber_le_card
#print axioms ArkLib.ProximityGap.EtaQuarticUncond.rEnergy_two_le_card_cubed
#print axioms ArkLib.ProximityGap.EtaQuarticUncond.eta_quartic_le_uncond
#print axioms ArkLib.ProximityGap.EtaQuarticUncond.eta_le_uncond_norm
