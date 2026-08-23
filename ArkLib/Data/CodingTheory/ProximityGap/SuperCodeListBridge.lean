/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.FarLineIncidenceEquivariance

/-!
# The general super-code bridge: MCA incidence ≤ list size of a `dim+1` super-code (issue #389)

The monomial-line bridge (`MonomialLineListBridge`) reduced the MCA incidence of the *monomial*
direction `X^k` to the list-decoding of `RS[k+1]`. But monomial directions are **not** the worst
case in the prize regime (probe: the `2`-sparse monomial words are atypically far from the code, so
"worst-over-monomials" sits *below* the average pencil incidence). The worst far direction `u₁` is a
general word, and the right object is the **general one-dimension-larger super-code**

  `C⁺ := C ⊔ ⟨u₁⟩`   (the code `C` plus the far direction `u₁`).

This file proves the general bridge for **any** linear code `C` and **any** far direction `u₁ ∉ C`:

> **`explainableScalars_card_le_superList`** — the number of bad scalars of the line `(u₀, u₁)` for
> `C` at radius `δ` is at most the number of codewords of `C⁺ = C ⊔ ⟨u₁⟩` that `(1−δ)n`-agree with
> `u₀` — the size of the radius-`δn` list of the `+1`-dimensional super-code.

The mechanism is the same `+1` lift, abstractly: `u₀ + γ·u₁` agrees with `c ∈ C` on a witness set
`iff` `u₀` agrees with `c − γ·u₁ ∈ C⁺` there, and the map `γ ↦ c_γ − γ·u₁` is **injective** because
`u₁ ∉ C` makes `C ⊕ ⟨u₁⟩` a direct sum (so the `u₁`-coordinate `−γ` is recovered from the codeword).
No degree/evaluation machinery is needed — just `u₁ ∉ C`.

Consequently the governing law gives, for the **worst-case** MCA incidence,

  `I(δ) = max over far directions u₁ of  #bad(u₀,u₁)`
        `≤ max over (dim C + 1)-dim super-codes C⁺ ⊇ C of  |list(C⁺, radius δn)|`,

i.e. **the grand MCA challenge reduces to list-decoding of the worst `(dim+1)`-super-code of `RS[k]`**
— the monomial bridge's `RS[k+1]` is one (sub-optimal) member of this family. Axiom-clean
`[propext, Classical.choice, Quot.sound]`.
-/

open Finset
open scoped NNReal Classical

namespace ProximityGap.FarCosetExplosion

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The general super-code bridge (cardinality form).** For any linear code `C ≤ (ι → F)` and any
far direction `u₁ ∉ C`, the number of bad scalars of the line `(u₀, u₁)` for `C` at radius `δ` is at
most the size of the radius-`δn` agreement list of the one-dimension-larger super-code `C ⊔ ⟨u₁⟩`.
The injection `γ ↦ c_γ − γ·u₁` lands in the super-code and is injective because `u₁ ∉ C`. -/
theorem explainableScalars_card_le_superList (C : Submodule F (ι → F)) (δ : ℝ≥0)
    (u₀ u₁ : ι → F) (hu₁ : u₁ ∉ C) :
    (explainableScalars (F := F) (↑C : Set (ι → F)) δ u₀ u₁).card
      ≤ (Finset.univ.filter (fun e : ι → F => e ∈ (C ⊔ Submodule.span F {u₁}) ∧
          ∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
            ∀ i ∈ S, e i = u₀ i)).card := by
  classical
  have key : ∀ γ ∈ explainableScalars (F := F) (↑C : Set (ι → F)) δ u₀ u₁,
      ∃ c : ι → F, c ∈ C ∧ ∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
        ∀ i ∈ S, c i = u₀ i + γ • u₁ i := by
    intro γ hγ
    simp only [explainableScalars, Finset.mem_filter, Finset.mem_univ, true_and] at hγ
    obtain ⟨S, hS, w, hwC, hw⟩ := hγ
    exact ⟨w, hwC, S, hS, hw⟩
  choose! cf hcC Sf hScard hagree using key
  refine Finset.card_le_card_of_injOn (fun γ => cf γ - γ • u₁) ?_ ?_
  · intro γ hγ
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, Sf γ, hScard γ hγ, ?_⟩
    · exact Submodule.sub_mem _ (Submodule.mem_sup_left (hcC γ hγ))
        (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
    · intro i hiS
      have hag := hagree γ hγ i hiS
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hag ⊢
      linear_combination hag
  · intro γ hγ γ' hγ' heq
    rw [Finset.mem_coe] at hγ hγ'
    by_contra hne
    have hsub : γ - γ' ≠ 0 := sub_ne_zero.mpr hne
    -- `cf γ − γ•u₁ = cf γ' − γ'•u₁`  ⟹  `(γ−γ')•u₁ = cf γ − cf γ' ∈ C`
    have hfun : cf γ - cf γ' = (γ - γ') • u₁ := by
      funext i
      have h := congrFun heq i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h ⊢
      linear_combination h
    have hmem : (γ - γ') • u₁ ∈ C :=
      hfun ▸ Submodule.sub_mem _ (hcC γ hγ) (hcC γ' hγ')
    have : u₁ ∈ C := by
      have h2 := Submodule.smul_mem C (γ - γ')⁻¹ hmem
      rwa [inv_smul_smul₀ hsub] at h2
    exact hu₁ this

end ProximityGap.FarCosetExplosion

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.FarCosetExplosion.explainableScalars_card_le_superList
