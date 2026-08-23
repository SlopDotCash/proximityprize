/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves.HeavyCodeword
import Mathlib.Combinatorics.Pigeonhole

/-!
# Proximity gap via the close-codeword list size ([BCIKS20] §6)

Pigeonholes the good curve parameters onto their close codewords: if the good set `G` exceeds
`L · k · |ι|` (where `L` is the number of *distinct* close codewords across `G`), some codeword is
hit by more than `k·|ι|` parameters, which by the agreement-count dichotomy
(`jointAgreement_of_heavy_codeword`) forces joint agreement.

This reduces the proximity gap to bounding the single quantity `L` (the Johnson list size) so that
the keystone threshold `Pr > k·errorBound` implies `|G| > L·k·|ι|` — isolating the remaining
content as a clean list-size statement.
-/

open Finset BigOperators
open scoped NNReal

namespace ProximityGap

set_option linter.unusedSectionVars false

variable {ι : Type} [Fintype ι] [DecidableEq ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Proximity gap via the close-codeword list size.** Let `G` be a set of curve parameters,
each equipped (via `cw`) with a code-codeword that the curve agrees with on `≥ |ι| - e`
coordinates. If `G` is larger than `L · k · |ι|`, where `L = |G.image cw|` is the number of
*distinct* close codewords across `G`, then the word stack `u` jointly agrees with `C`.

This pigeonholes the good parameters onto their close codewords: some codeword is hit by more
than `k·|ι|` parameters, which by the agreement-count dichotomy forces permanent agreement (joint
agreement). It reduces the proximity gap to the single clean quantity `L` (the Johnson list size):
the remaining content is exactly bounding `L` so that the keystone threshold `Pr > k·errorBound`
implies `|G| > L·k·|ι|`. -/
theorem jointAgreement_of_close_codeword_pigeonhole {k : ℕ} {C : Set (ι → F)} {δ : ℝ≥0}
    (u : Fin (k + 1) → ι → F) (e : ℕ) (G : Finset F) (cw : F → ι → F)
    (hk : k < Fintype.card F)
    (h0 : (0 : ι → F) ∈ C)
    (hsize : (1 - δ) * (Fintype.card ι : ℝ≥0) ≤ ((Fintype.card ι - e : ℕ) : ℝ≥0))
    (hcw_mem : ∀ z ∈ G, cw z ∈ C)
    (hcw_agree : ∀ z ∈ G, Fintype.card ι - e ≤
      (Finset.univ.filter (fun i => ∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i = cw z i)).card)
    (hbig : (G.image cw).card * (k * Fintype.card ι) < G.card) :
    Code.jointAgreement (κ := Fin (k + 1)) C δ u := by
  classical
  obtain ⟨c, hc_img, hc_card⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := G) (t := G.image cw) (f := cw) (n := k * Fintype.card ι)
      (fun z hz => Finset.mem_image_of_mem cw hz) hbig
  obtain ⟨z₀, hz₀G, hz₀⟩ := Finset.mem_image.mp hc_img
  have hcC : c ∈ C := hz₀ ▸ hcw_mem z₀ hz₀G
  have hsub : {z ∈ G | cw z = c} ⊆ Finset.univ.filter (fun z : F =>
      Fintype.card ι - e ≤
        (Finset.univ.filter (fun i => ∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i = c i)).card) := by
    intro z hz
    rw [Finset.mem_filter] at hz
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have hag := hcw_agree z hz.1
    rw [hz.2] at hag
    exact hag
  have hheavy : k * Fintype.card ι < (Finset.univ.filter (fun z : F =>
      Fintype.card ι - e ≤
        (Finset.univ.filter (fun i => ∑ t : Fin (k + 1), z ^ (t : ℕ) * u t i = c i)).card)).card :=
    lt_of_lt_of_le hc_card (Finset.card_le_card hsub)
  exact jointAgreement_of_heavy_codeword u c e hk hcC h0 hsize hheavy

end ProximityGap
