/-
Downstream additions retained during the ArkLib integration.
Initial source and revision: scripts/integration/downstream-extension-audit.json.
Shared declarations come from the canonical ArkLib modules.
Checked-in source owns later API ports. Generate separate review candidates with:
scripts/integration/extract_downstream_extensions.py --output-dir <directory>.
-/
import ArkLib.Data.CodingTheory.DivergenceOfSets

/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
-/

import ArkLib.Data.CodingTheory.Basic.DecodingRadius
import ProximityPrize.Extensions.Data.CodingTheory.Basic.Distance
import ProximityPrize.Extensions.Data.CodingTheory.Basic.LinearCode
import ProximityPrize.Extensions.Data.CodingTheory.Basic.RelativeDistance
import ProximityPrize.Extensions.Data.CodingTheory.ProximityGap.Basic
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ErrorBound
import ProximityPrize.Extensions.Data.CodingTheory.ReedSolomon
import ProximityPrize.Compatibility.UniformProbability
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs

/-!
  # Definitions and Theorems about Divergence of Sets

  ## Main Definitions and Statements

  - divergence of sets
  - statement of Corollary 1.3 (Concentration bounds) from [BCIKS20].
-/

open NNReal ProximityGap

namespace DivergenceOfSets

open Code ReedSolomon ProbabilityTheory

section Defs

variable {ι : Type*} [Fintype ι] [Nonempty ι]
         {F : Type*} [DecidableEq F]
         {U V : Set (ι → F)} [Nonempty V] [Fintype V]

end Defs

section Theorems

variable {ι : Type} [Fintype ι] [Nonempty ι]
         {F : Type} [Fintype F] [Field F]
         {U V : Set (ι → F)}

open scoped ProbabilityTheory in
theorem Pr_uniform_eq_one_imp_forall {α : Type} [Fintype α] [Nonempty α] (P : α → Prop) :
    Pr_{let a ← $ᵖ α}[P a] = 1 → ∀ a, P a := by
  classical
  let : SampleableType α := SampleableType.ofFintype α
  rw [ProximityPrize.Compatibility.pmf_uniform_probability_eq_native]
  exact (SampleableType.prEvent_uniformSample_eq_one_iff P).mp

open scoped ProbabilityTheory in
theorem Pr_uniform_equiv {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (e : α ≃ β) (P : β → Prop) :
  Pr_{let a ← $ᵖ α}[P (e a)] = Pr_{let b ← $ᵖ β}[P b] := by
  classical
  have hmap : (ProximityPrize.Compatibility.uniformOfFintype α).map e =
      ProximityPrize.Compatibility.uniformOfFintype β := by
    ext b
    -- Reduce to a finite sum over a singleton fiber.
    simp only [PMF.map_apply, ProximityPrize.Compatibility.uniformOfFintype_apply,
      Fintype.card_congr e, tsum_fintype]
    -- Transport the sum along the equivalence `e`.
    have hs :
        Finset.univ.sum (fun a : α =>
            if b = e a then (Fintype.card β : ENNReal)⁻¹ else 0)
          =
          Finset.univ.sum (fun b' : β =>
            if b = b' then (Fintype.card β : ENNReal)⁻¹ else 0) := by
      -- `Fintype.sum_equiv` is the change-of-variables lemma for sums over `univ`.
      simpa using
        (Fintype.sum_equiv e
          (fun a : α => if b = e a then (Fintype.card β : ENNReal)⁻¹ else 0)
          (fun b' : β => if b = b' then (Fintype.card β : ENNReal)⁻¹ else 0)
          (by intro a; rfl))
    -- Evaluate the Kronecker delta sum.
    have hdelta :
        Finset.univ.sum (fun b' : β =>
            if b = b' then (Fintype.card β : ENNReal)⁻¹ else 0) =
          (Fintype.card β : ENNReal)⁻¹ := by
      simp
    exact hs.trans hdelta
  -- Now use functoriality of `PMF.map` to move `P` across the equivalence.
  -- (Unfolding `Pr_{...}[_]` gives a `PMF Prop` evaluated at `True`.)
  change
    (do
        let a ← (ProximityPrize.Compatibility.uniformOfFintype α)
        pure (P (e a))) True =
      (do
        let b ← (ProximityPrize.Compatibility.uniformOfFintype β)
        pure (P b)) True
  -- Rewrite the left-hand `do` block as successive `PMF.map`s.
  -- First push forward along `e`, then along `P`.
  --
  -- `do let a ← p; pure (P (e a))` is `p.map (P ∘ e)`.
  -- `PMF.map_comp` converts it to `((p.map e).map P)`.
  have hcomp :
      (ProximityPrize.Compatibility.uniformOfFintype α).map (P ∘ e) =
        ((ProximityPrize.Compatibility.uniformOfFintype α).map e).map P := by
    simpa [Function.comp] using
      (PMF.map_comp (p := ProximityPrize.Compatibility.uniformOfFintype α) (f := e) (g := P)).symm
  -- Apply both sides to `True`, then use `hmap`.
  -- Finally, recognize the right-hand side as the original `do` block.
  simpa using congrArg (fun q : PMF Prop => q True) (by
    calc
      (ProximityPrize.Compatibility.uniformOfFintype α).map (P ∘ e)
          = ((ProximityPrize.Compatibility.uniformOfFintype α).map e).map P := hcomp
      _ = (ProximityPrize.Compatibility.uniformOfFintype β).map P := by simp [hmap]
    )

end Theorems

end DivergenceOfSets
