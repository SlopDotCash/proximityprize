/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.SeparationSurvivalCount

/-!
# Conditional line-decodability of subspace-design codes (issue #389, GG25 §4.3 conclusion)

The culmination of the §4.3 separation/survival machinery: when the design parameter `θ` (bounding
`τ`) is strictly below the close radius `θ'`, a low-dimensional span `H ≤ C` of a `τ`-subspace-design
is **line-decodable** within any agreement set `T` of density `≥ θ'`.

* `exists_surv_tuple` — a good sample exists: the combined count `card_surv_ge` is positive, so some
  tuple `v` both separates `H` and lies entirely in `T`.
* `tuple_agree_subsingleton` — a separating tuple determines `H`: at most one codeword of `H` agrees
  with a given `y` on the tuple's coordinates.
* `exists_determining_tuple` — **the conclusion**: a tuple `v ⊆ T` whose coordinates determine `H`.

Given a list-decoder that supplies `H` as the span of the `δ`-close codewords (the CZ25 list-recovery,
in-tree via the span-bound route), with `θ' = 1 − δ`, this is exactly the line-decodability that GG25
§4.3 turns into proximity gaps / mutual correlated agreement (`GG25SpreadBound`, `GG25CurveDecodability`).
The `θ < θ'` hypothesis is the design-vs-radius gap that makes the close codewords separable. Axiom-clean
`[propext, Classical.choice, Quot.sound]`.
-/

open Finset CodingTheory

namespace ProximityGap

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] {F : Type} [Field F]

open Classical in
theorem exists_surv_tuple {s : ℕ} {τ : ℕ → ℝ} {θ θ' : ℝ}
    {C : Submodule F (ι → Fin s → F)} (h : IsSubspaceDesign s τ C)
    (hθ : ∀ j, τ j ≤ θ) (hθ0 : 0 ≤ θ) (hθθ' : θ < θ') (hθ'1 : θ' ≤ 1)
    (T : Finset ι) (hT : θ' * (Fintype.card ι : ℝ) ≤ T.card)
    (r : ℕ) (H : Submodule F (ι → Fin s → F)) (hHC : H ≤ C) (hr : Module.finrank F H ≤ r) :
    ∃ v : Fin r → ι, Separates H v ∧ ∀ j, v j ∈ T := by
  have hcount := card_surv_ge h hθ hθ0 (le_of_lt hθθ') hθ'1 T hT r H hHC hr
  have hd : (0 : ℝ) < θ' - θ := by linarith
  have hnpos : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hpos : (0 : ℝ) < (θ' - θ) ^ r * (Fintype.card ι : ℝ) ^ r := by positivity
  have hcard : 0 < (univ.filter (fun v : Fin r → ι => Separates H v ∧ ∀ j, v j ∈ T)).card := by
    have : (0 : ℝ) < ((univ.filter (fun v : Fin r → ι => Separates H v ∧ ∀ j, v j ∈ T)).card : ℝ) :=
      lt_of_lt_of_le hpos hcount
    exact_mod_cast this
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hcard
  rw [mem_filter] at hv
  exact ⟨v, hv.2⟩

/-- A separating tuple **determines** `H`: at most one codeword of `H` agrees with `y` on the tuple's
coordinates. (The tuple form of `SeparatingCoordinates.separated_agree_subsingleton`.) -/
lemma tuple_agree_subsingleton {s r : ℕ} {H : Submodule F (ι → Fin s → F)} {v : Fin r → ι}
    (hsep : Separates H v) (y : ι → Fin s → F) :
    {c : ι → Fin s → F | c ∈ H ∧ ∀ j, c (v j) = y (v j)}.Subsingleton := by
  intro c₁ hc₁ c₂ hc₂
  have hdiff : (c₁ - c₂) ∈ H ⊓ (⨅ j : Fin r, LinearMap.ker
      (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) (v j))) := by
    refine Submodule.mem_inf.mpr ⟨H.sub_mem hc₁.1 hc₂.1, ?_⟩
    simp only [Submodule.mem_iInf]
    intro j
    rw [LinearMap.mem_ker, LinearMap.proj_apply, Pi.sub_apply, sub_eq_zero, hc₁.2 j, hc₂.2 j]
  have hsep' : H ⊓ (⨅ j : Fin r, LinearMap.ker
      (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) (v j))) = ⊥ := hsep
  rw [hsep', Submodule.mem_bot, sub_eq_zero] at hdiff
  exact hdiff

open Classical in
/-- **Conditional line-decodability (GG25 §4.3 conclusion).** When the design parameter `θ` is below
the close radius `θ'`, there is a tuple `v` lying entirely in the agreement set `T` whose coordinates
**determine** the low-dimensional span `H`: at most one codeword of `H` agrees with any `y` on them.
Given a list-decoder supplying `H` as the span of the close codewords (CZ25), this is exactly the
line-decodability of subspace-design codes. -/
theorem exists_determining_tuple {s : ℕ} {τ : ℕ → ℝ} {θ θ' : ℝ}
    {C : Submodule F (ι → Fin s → F)} (h : IsSubspaceDesign s τ C)
    (hθ : ∀ j, τ j ≤ θ) (hθ0 : 0 ≤ θ) (hθθ' : θ < θ') (hθ'1 : θ' ≤ 1)
    (T : Finset ι) (hT : θ' * (Fintype.card ι : ℝ) ≤ T.card)
    (r : ℕ) (H : Submodule F (ι → Fin s → F)) (hHC : H ≤ C) (hr : Module.finrank F H ≤ r) :
    ∃ v : Fin r → ι, (∀ j, v j ∈ T) ∧
      ∀ y : ι → Fin s → F, {c : ι → Fin s → F | c ∈ H ∧ ∀ j, c (v j) = y (v j)}.Subsingleton := by
  obtain ⟨v, hsep, hvT⟩ := exists_surv_tuple h hθ hθ0 hθθ' hθ'1 T hT r H hHC hr
  exact ⟨v, hvT, fun y => tuple_agree_subsingleton hsep y⟩

open Classical in
/-- **Per-codeword recovery (line-decodability for a codeword).** A codeword `c` of a low-dimensional
span `H ≤ C` that agrees with the received word `y` on a `≥ θ'`-fraction of coordinates (and with the
design parameter `θ < θ'`) is **uniquely recovered**: there is a tuple `v` of coordinates on which
`c` equals `y`, and `c` is the only codeword of `H` agreeing with `y` on them. -/
theorem exists_recovering_tuple {s : ℕ} {τ : ℕ → ℝ} {θ θ' : ℝ}
    {C : Submodule F (ι → Fin s → F)} (h : IsSubspaceDesign s τ C)
    (hθ : ∀ j, τ j ≤ θ) (hθ0 : 0 ≤ θ) (hθθ' : θ < θ') (hθ'1 : θ' ≤ 1)
    (r : ℕ) (H : Submodule F (ι → Fin s → F)) (hHC : H ≤ C) (hr : Module.finrank F H ≤ r)
    (y c : ι → Fin s → F) (hcH : c ∈ H)
    (hagree : θ' * (Fintype.card ι : ℝ)
      ≤ ((univ.filter (fun i : ι => c i = y i)).card : ℝ)) :
    ∃ v : Fin r → ι, (∀ j, c (v j) = y (v j)) ∧
      ∀ c' : ι → Fin s → F, c' ∈ H → (∀ j, c' (v j) = y (v j)) → c' = c := by
  obtain ⟨v, hvT, hdet⟩ := exists_determining_tuple h hθ hθ0 hθθ' hθ'1
    (univ.filter (fun i : ι => c i = y i)) hagree r H hHC hr
  have hcv : ∀ j, c (v j) = y (v j) := fun j => (mem_filter.mp (hvT j)).2
  refine ⟨v, hcv, fun c' hc'H hc'agree => ?_⟩
  exact hdet y ⟨hc'H, hc'agree⟩ ⟨hcH, hcv⟩

end ProximityGap


#print axioms ProximityGap.exists_surv_tuple
#print axioms ProximityGap.exists_determining_tuple
#print axioms ProximityGap.exists_recovering_tuple
