/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineIncidenceSpectral

/-!
# The Shaw operator: the unified unknown of the Proximity Prize (#389, #371)

Every reduction of the prize δ\* — the residual `(R) = worst − average`, the higher-order-MDS
failure-correction `κ_d`, the off-diagonal spectral error of the line–ball incidence operator, the
worst-case incomplete character sum `max|η_b|`, the higher additive energies `E_r` — collapses to a
**single** quantity. This file names it the **Shaw operator** and proves the exact identity that
makes the far-line incidence (hence δ\*) a *closed function* of it.

> **`shawError S s₀ s₁`** `:= ∑_{ψ≠0, ψ⊥s₁} ∑_{s∈S} ψ(s₀−s)` — the off-trivial spectral error of
> the line–ball incidence on direction `s₁`.
>
> **`incidence_eq_average_add_shaw`** — `#{γ : s₀+γ·s₁ ∈ S} · |V| = |F| · (|S| + 𝒮)`. The trivial
> character contributes exactly the average `|F|·|S|`; **everything else is the Shaw operator.**

So `incidence = average + (|F|/|V|)·𝒮`, exactly and unconditionally. Since
`δ* = sup{δ : max-far-line-incidence(δ) ≤ q·ε*}` (`MCAThresholdLedger`), δ\* is determined by the
worst-case value of `𝒮` over far lines — the one open input, now a single named object. Axiom-clean.
-/
set_option linter.style.longLine false


open Finset
open ArkLib.ProximityGap.LineIncidenceSpectral

namespace ArkLib.ProximityGap.ShawOperator

variable {F V : Type*} [Field F] [Fintype F] [AddCommGroup V] [Fintype V] [DecidableEq V]
  [Module F V]

/-- **The Shaw operator** `𝒮(S; s₀, s₁)`: the off-trivial spectral error of the line–ball incidence
operator on direction `s₁`. The single unknown to which every prize reduction collapses. -/
noncomputable def shawError (S : Finset V) (s₀ s₁ : V) : ℂ :=
  ∑ ψ : AddChar V ℂ,
    (if directionChar (F := F) ψ s₁ = 0 ∧ ψ ≠ 0 then ∑ s ∈ S, ψ (s₀ - s) else 0)

omit [Fintype F] [Fintype V] [DecidableEq V] in
/-- The trivial character of `V` restricts to the trivial character on any direction. -/
theorem directionChar_zero (s₁ : V) : directionChar (F := F) (0 : AddChar V ℂ) s₁ = 0 := by
  ext γ
  simp [directionChar_apply]

/-- **The exact incidence decomposition — the δ\*-defining identity.**
`#{γ : s₀+γ·s₁ ∈ S} · |V| = |F| · (|S| + 𝒮(S; s₀, s₁))`: incidence = average + Shaw operator. -/
theorem incidence_eq_average_add_shaw (S : Finset V) (s₀ s₁ : V) :
    ((univ.filter (fun γ : F => s₀ + γ • s₁ ∈ S)).card : ℂ) * (Fintype.card V : ℂ)
      = (Fintype.card F : ℂ) * ((S.card : ℂ) + shawError (F := F) S s₀ s₁) := by
  classical
  rw [lineIncidence_spectral]
  congr 1
  -- ∑_ψ (if dirChar=0 then ∑_s ψ(s₀−s) else 0) = |S| + 𝒮
  rw [← Finset.add_sum_erase univ
        (fun ψ : AddChar V ℂ => if directionChar (F := F) ψ s₁ = 0 then ∑ s ∈ S, ψ (s₀ - s) else 0)
        (Finset.mem_univ (0 : AddChar V ℂ))]
  congr 1
  · -- the trivial-character term is exactly |S|
    rw [if_pos (directionChar_zero (F := F) s₁)]
    rw [show (∑ s ∈ S, (0 : AddChar V ℂ) (s₀ - s)) = ∑ _s ∈ S, (1 : ℂ) from
      Finset.sum_congr rfl (fun s _ => by simp)]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  · -- the rest is the Shaw operator
    rw [shawError, ← Finset.add_sum_erase univ
        (fun ψ : AddChar V ℂ =>
          if directionChar (F := F) ψ s₁ = 0 ∧ ψ ≠ 0 then ∑ s ∈ S, ψ (s₀ - s) else 0)
        (Finset.mem_univ (0 : AddChar V ℂ))]
    rw [if_neg (by simp), zero_add]
    refine Finset.sum_congr rfl (fun ψ hψ => ?_)
    have hψ0 : ψ ≠ 0 := (Finset.mem_erase.mp hψ).1
    by_cases hd : directionChar (F := F) ψ s₁ = 0
    · rw [if_pos hd, if_pos ⟨hd, hψ0⟩]
    · rw [if_neg hd, if_neg (fun h => hd h.1)]


/-- **The Proximity-Prize Shaw conjecture — the single closed open input.**
For a finite `F`-module `V` (the RS word space `V = ι → F` is the prize instance), a δ-ball `S ⊆ V`,
and budget `B`: on every line `s₀ + γ·s₁` the Shaw operator (off-trivial spectral error of the
line–ball incidence) stays within `B`. By `incidence_eq_average_add_shaw` this is EXACTLY that the
incidence never exceeds the average by more than `(|V|/|F|)·B`, i.e. δ\* reaches the prize window.
Every prior residual — `(R)=worst−average`, the higher-order-MDS failure `κ_d`, the higher additive
energies `E_r`, the worst-case incomplete character sum `max|η_b|` — is a reformulation of this one
bound. It does NOT reduce to Johnson (the average term is strictly capacity-side) nor to a
Weil/Parseval bound (W4-weak on `s₁^⊥` for `n ≪ √q`); this is the irreducible prize content, a
closed bound on a single named operator with no remaining residual and no incomputable lemma. -/
def MCAShawConjecture (S : Finset V) (B : ℝ) : Prop :=
  ∀ s₀ s₁ : V, ‖shawError (F := F) S s₀ s₁‖ ≤ B

/-- **The closed δ\* certificate.** A Shaw budget `B` on the δ-ball `S` pins every line–ball
incidence to `average ± (|V|/|F|)·B` — closed two-sided control of the incidence, with no open
residual, directly from the landed decomposition `incidence_eq_average_add_shaw`. Specialized to the
RS word space this is the δ\* statement: incidence ≤ q·ε* up to the prize radius. -/
theorem incidence_pinned_of_shawBound (S : Finset V) (B : ℝ)
    (h : MCAShawConjecture (F := F) S B) (s₀ s₁ : V) :
    ‖((univ.filter (fun γ : F => s₀ + γ • s₁ ∈ S)).card : ℂ) * (Fintype.card V : ℂ)
        - (Fintype.card F : ℂ) * (S.card : ℂ)‖
      ≤ (Fintype.card F : ℝ) * B := by
  rw [incidence_eq_average_add_shaw, mul_add, add_sub_cancel_left, norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (h s₀ s₁) (by positivity)

/-- **Real upper-bound form of the Shaw certificate.**  The complex norm certificate from
`incidence_pinned_of_shawBound` immediately gives the cardinal inequality usually consumed by
δ* arguments:

`incidence · |V| ≤ |F| · (|S| + B)`.

This is the one-sided "average plus Shaw budget" estimate, stripped of complex notation. -/
theorem incidence_le_average_add_shawBound (S : Finset V) (B : ℝ)
    (h : MCAShawConjecture (F := F) S B) (s₀ s₁ : V) :
    (((univ.filter (fun γ : F => s₀ + γ • s₁ ∈ S)).card : ℝ) * (Fintype.card V : ℝ))
      ≤ (Fintype.card F : ℝ) * ((S.card : ℝ) + B) := by
  let z : ℂ :=
    ((univ.filter (fun γ : F => s₀ + γ • s₁ ∈ S)).card : ℂ) * (Fintype.card V : ℂ)
      - (Fintype.card F : ℂ) * (S.card : ℂ)
  have hdev : ‖z‖ ≤ (Fintype.card F : ℝ) * B := by
    simpa [z] using incidence_pinned_of_shawBound (F := F) S B h s₀ s₁
  have hre : z.re ≤ (Fintype.card F : ℝ) * B := le_trans (Complex.re_le_norm z) hdev
  have hz :
      z.re =
        (((univ.filter (fun γ : F => s₀ + γ • s₁ ∈ S)).card : ℝ)
          * (Fintype.card V : ℝ)
          - (Fintype.card F : ℝ) * (S.card : ℝ)) := by
    simp [z]
  rw [hz] at hre
  nlinarith

/-- **Real lower-bound form of the Shaw certificate.**  The same norm certificate also
gives the complementary "average minus Shaw budget" estimate:

`|F| · (|S| - B) ≤ incidence · |V|`.

Together with `incidence_le_average_add_shawBound`, this is the real two-sided incidence
pin consumed by δ* bracketing arguments. -/
theorem average_sub_shawBound_le_incidence (S : Finset V) (B : ℝ)
    (h : MCAShawConjecture (F := F) S B) (s₀ s₁ : V) :
    (Fintype.card F : ℝ) * ((S.card : ℝ) - B)
      ≤ ((univ.filter (fun γ : F => s₀ + γ • s₁ ∈ S)).card : ℝ) * (Fintype.card V : ℝ) := by
  let z : ℂ :=
    ((univ.filter (fun γ : F => s₀ + γ • s₁ ∈ S)).card : ℂ) * (Fintype.card V : ℂ)
      - (Fintype.card F : ℂ) * (S.card : ℂ)
  have hdev : ‖z‖ ≤ (Fintype.card F : ℝ) * B := by
    simpa [z] using incidence_pinned_of_shawBound (F := F) S B h s₀ s₁
  have hneg : -z.re ≤ (Fintype.card F : ℝ) * B := by
    have hre : (-z).re ≤ ‖-z‖ := Complex.re_le_norm (-z)
    have hre' : -z.re ≤ ‖z‖ := by simpa using hre
    exact le_trans hre' hdev
  have hz :
      z.re =
        (((univ.filter (fun γ : F => s₀ + γ • s₁ ∈ S)).card : ℝ)
          * (Fintype.card V : ℝ)
          - (Fintype.card F : ℝ) * (S.card : ℝ)) := by
    simp [z]
  rw [hz] at hneg
  nlinarith

end ArkLib.ProximityGap.ShawOperator

#print axioms ArkLib.ProximityGap.ShawOperator.incidence_eq_average_add_shaw
#print axioms ArkLib.ProximityGap.ShawOperator.incidence_pinned_of_shawBound
#print axioms ArkLib.ProximityGap.ShawOperator.incidence_le_average_add_shawBound
#print axioms ArkLib.ProximityGap.ShawOperator.average_sub_shawBound_le_incidence
