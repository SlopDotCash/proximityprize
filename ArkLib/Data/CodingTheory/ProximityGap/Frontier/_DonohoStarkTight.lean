/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ZModDonohoStark

/-!
# Tightness of the Donoho–Stark uncertainty principle on `ZMod N` (#407)

`_ZModDonohoStark` proves `|supp Φ|·|supp 𝓕Φ| ≥ N`. This file shows the bound is **tight** —
there is a nonzero `Φ` with `|supp Φ|·|supp 𝓕Φ| = N`. That tightness is the crux of the #407
c.349 reframing: the uncertainty principle has *no slack*, so on saturating configurations there
is nothing to exploit — which is precisely why the smooth-domain (`μ_{2^μ}`) prize floor is hard.

The witness here is the delta `δ₀` (`𝓕δ₀ = 1`, the constant): `|supp δ₀| = 1`, `|supp 𝓕δ₀| = N`,
product `N`. (The prize-relevant saturators are the *subgroup* indicators `1_H`, with
`𝓕 1_H = |H|·1_{H^⊥}` and product `|H|·(N/|H|) = N`; `δ₀ = 1_{0}` is the `H = {0}` case. The general
subgroup case needs the annihilator machinery; this file lands the existence of saturation, the key
qualitative fact.) Axiom-clean. Issue #407.
-/

open Finset ZMod
open ProximityGap.Frontier.ZModDonohoStark

namespace ProximityGap.Frontier.DonohoStarkTight

variable {N : ℕ} [NeZero N]

/-- The delta at `0`. -/
def delta0 : ZMod N → ℂ := fun j => if j = 0 then 1 else 0

/-- `𝓕 δ₀` is the constant function `1`. -/
theorem dft_delta0 (k : ZMod N) : (𝓕 (delta0 (N := N))) k = 1 := by
  rw [dft_apply]
  rw [Finset.sum_eq_single (0 : ZMod N)]
  · simp [delta0]
  · intro b _ hb; simp [delta0, hb]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Donoho–Stark is tight:** there is a nonzero `Φ` saturating `|supp Φ|·|supp 𝓕Φ| = N`. -/
theorem donoho_stark_tight :
    ∃ Φ : ZMod N → ℂ, Φ ≠ 0 ∧ ((supp Φ).card : ℝ) * (supp (𝓕 Φ)).card = N := by
  refine ⟨delta0, ?_, ?_⟩
  · intro h
    have h0 : delta0 (N := N) 0 = (0 : ZMod N → ℂ) 0 := by rw [h]
    simp [delta0] at h0
  · have hsuppΦ : supp (delta0 (N := N)) = {0} := by
      ext j
      simp only [supp, mem_filter, mem_univ, true_and, mem_singleton, delta0]
      constructor
      · intro hj; by_contra hjne; simp [hjne] at hj
      · intro hj; simp [hj]
    have hsuppF : supp (𝓕 (delta0 (N := N))) = univ := by
      ext k
      simp only [supp, mem_filter, mem_univ, true_and, dft_delta0]
      norm_num
    rw [hsuppΦ, hsuppF, Finset.card_singleton, Finset.card_univ, ZMod.card]
    push_cast; ring

end ProximityGap.Frontier.DonohoStarkTight

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.DonohoStarkTight.dft_delta0
#print axioms ProximityGap.Frontier.DonohoStarkTight.donoho_stark_tight
