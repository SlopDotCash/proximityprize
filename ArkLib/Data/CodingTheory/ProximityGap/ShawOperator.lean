/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineIncidenceSpectral

/-!
# The Shaw operator: the unified unknown of the Proximity Prize (#389, #371)

Several reductions of the prize δ\* — the residual `(R) = worst − average`, the higher-order-MDS
failure-correction `κ_d`, the off-diagonal spectral error of the line–ball incidence operator, the
worst-case incomplete character sum `max|η_b|`, the higher additive energies `E_r` — are
*heuristically* related to one spectral quantity. This file names it the **Shaw operator** and
proves the exact identity expressing each line–ball incidence in terms of it. (That the other
residuals are reformulations of a Shaw bound is **not** proved here.)

> **`shawError S s₀ s₁`** `:= ∑_{ψ≠0, ψ⊥s₁} ∑_{s∈S} ψ(s₀−s)` — the off-trivial spectral error of
> the line–ball incidence on direction `s₁`.
>
> **`incidence_eq_average_add_shaw`** — `#{γ : s₀+γ·s₁ ∈ S} · |V| = |F| · (|S| + 𝒮)`. The trivial
> character contributes exactly the average `|F|·|S|`; **everything else is the Shaw operator.**

So `incidence = |F|·|S|/|V| + (|F|/|V|)·𝒮`, exactly and unconditionally. Since
`δ* = sup{δ : max-far-line-incidence(δ) ≤ q·ε*}` (`MCAThresholdLedger`), δ\* is governed by the
worst-case value of `𝒮` over the *far, MCA-admissible* lines only. **Caveat (scope):** the
universal budget `MCAShawConjecture S B` below quantifies over *all* lines, including the zero
direction `s₁ = 0`, where `𝒮 = |V| − |S|` (if `s₀ ∈ S`) or `𝒮 = −|S|` (if `s₀ ∉ S`)
(`shawError_zero_direction_of_mem`, `shawError_zero_direction_of_not_mem`). Hence for a nonempty
proper `S` it forces `B ≥ max(|S|, |V| − |S|) ≥ |V|/2` (`MCAShawConjecture.zero_direction_bounds`,
`MCAShawConjecture.card_le_two_mul`): it is **not** a small-error statement and is not the prize
reformulation. A restricted residual over far / unexplained lines would need its own definition
and an explicit bridge to the MCA threshold (deleting `s₁ = 0` alone does not remove
code-contained, fully explained lines); neither is supplied here. Axiom-clean.
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


/-- **The universal (all-lines) Shaw budget.**
For a finite `F`-module `V` (the RS word space `V = ι → F` is the prize instance), a set `S ⊆ V`
(e.g. a δ-ball), and budget `B`: on **every** line `s₀ + γ·s₁` — with no far-direction or
unexplained-agreement restriction, and including `s₁ = 0` — the Shaw operator stays within `B`.
By `incidence_eq_average_add_shaw` this says the incidence deviates from the average
`|F|·|S|/|V|` by at most `(|F|/|V|)·B` on every line.

**This is not the prize reformulation.** Because zero directions are included, for nonempty proper
`S` it forces `B ≥ max(|S|, |V| − |S|) ≥ |V|/2` (`MCAShawConjecture.zero_direction_bounds`,
`MCAShawConjecture.card_le_two_mul`), so no small-error interpretation is available. A prize-
relevant residual must restrict to far / unexplained lines and come with an explicit bridge to the
MCA threshold; that the other residuals (`(R)`, `κ_d`, `E_r`, `max|η_b|`) are reformulations of
such a bound is not proved here. -/
def MCAShawConjecture (S : Finset V) (B : ℝ) : Prop :=
  ∀ s₀ s₁ : V, ‖shawError (F := F) S s₀ s₁‖ ≤ B

/-- **Zero direction, base point in `S`.** On the degenerate line `s₁ = 0` with `s₀ ∈ S`, every
`γ` is incident, and the Shaw operator equals `|V| − |S|`. -/
theorem shawError_zero_direction_of_mem (S : Finset V) {s₀ : V} (hs₀ : s₀ ∈ S) :
    shawError (F := F) S s₀ 0 = (Fintype.card V : ℂ) - (S.card : ℂ) := by
  have h := incidence_eq_average_add_shaw (F := F) S s₀ 0
  have hfilt : (univ.filter (fun γ : F => s₀ + γ • (0 : V) ∈ S)) = univ := by
    ext γ; simp [hs₀]
  rw [hfilt, Finset.card_univ] at h
  have hF : (Fintype.card F : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h' := mul_left_cancel₀ hF h
  linear_combination -h'

/-- **Zero direction, base point outside `S`.** On the degenerate line `s₁ = 0` with `s₀ ∉ S`, no
`γ` is incident, and the Shaw operator equals `−|S|`. -/
theorem shawError_zero_direction_of_not_mem (S : Finset V) {s₀ : V} (hs₀ : s₀ ∉ S) :
    shawError (F := F) S s₀ 0 = -(S.card : ℂ) := by
  have h := incidence_eq_average_add_shaw (F := F) S s₀ 0
  have hfilt : (univ.filter (fun γ : F => s₀ + γ • (0 : V) ∈ S)) = ∅ := by
    ext γ; simp [hs₀]
  rw [hfilt, Finset.card_empty, Nat.cast_zero, zero_mul] at h
  have hF : (Fintype.card F : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h' : (S.card : ℂ) + shawError (F := F) S s₀ 0 = 0 :=
    (mul_eq_zero.mp h.symm).resolve_left hF
  linear_combination h'

/-- **The universal Shaw budget is never small (zero-direction lower bounds).** Any `B` with
`MCAShawConjecture S B` satisfies `|V| − |S| ≤ B` when `S` is nonempty and `|S| ≤ B` when `S` is
proper. -/
theorem MCAShawConjecture.zero_direction_bounds {S : Finset V} {B : ℝ}
    (h : MCAShawConjecture (F := F) S B) :
    (S.Nonempty → (Fintype.card V : ℝ) - S.card ≤ B) ∧
      ((∃ s₀, s₀ ∉ S) → (S.card : ℝ) ≤ B) := by
  refine ⟨fun ⟨s₀, hs₀⟩ => ?_, fun ⟨s₀, hs₀⟩ => ?_⟩
  · have h1 := h s₀ 0
    rw [shawError_zero_direction_of_mem (F := F) S hs₀] at h1
    have hcast : ((Fintype.card V : ℂ) - (S.card : ℂ))
        = (((Fintype.card V : ℝ) - (S.card : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs] at h1
    exact le_trans (le_abs_self _) h1
  · have h1 := h s₀ 0
    rwa [shawError_zero_direction_of_not_mem (F := F) S hs₀, norm_neg,
      Complex.norm_natCast] at h1

/-- **The universal Shaw budget is at least `|V|/2` for nonempty proper `S`.** -/
theorem MCAShawConjecture.card_le_two_mul {S : Finset V} {B : ℝ}
    (h : MCAShawConjecture (F := F) S B) (hne : S.Nonempty) (hproper : ∃ s₀, s₀ ∉ S) :
    (Fintype.card V : ℝ) ≤ 2 * B := by
  have h1 := h.zero_direction_bounds.1 hne
  have h2 := h.zero_direction_bounds.2 hproper
  linarith

/-- **Two-sided incidence control from a Shaw budget (conditional).** A universal Shaw budget `B`
on `S` pins every line–ball incidence to `|F|·|S|/|V| ± (|F|/|V|)·B` (stated after multiplying by
`|V|`), directly from the decomposition `incidence_eq_average_add_shaw`. Since the universal
budget forces `B ≥ |V|/2` for nonempty proper `S` (`MCAShawConjecture.zero_direction_bounds`),
this does not by itself give a prize-scale δ\* statement. -/
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
#print axioms ArkLib.ProximityGap.ShawOperator.shawError_zero_direction_of_mem
#print axioms ArkLib.ProximityGap.ShawOperator.shawError_zero_direction_of_not_mem
#print axioms ArkLib.ProximityGap.ShawOperator.MCAShawConjecture.zero_direction_bounds
#print axioms ArkLib.ProximityGap.ShawOperator.MCAShawConjecture.card_le_two_mul
#print axioms ArkLib.ProximityGap.ShawOperator.incidence_pinned_of_shawBound
#print axioms ArkLib.ProximityGap.ShawOperator.incidence_le_average_add_shawBound
#print axioms ArkLib.ProximityGap.ShawOperator.average_sub_shawBound_le_incidence
