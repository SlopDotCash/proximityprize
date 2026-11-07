/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ShawOperator

/-!
# The Shaw operator's exact closed form: the dual-code character sum (#389, #371)

For a *linear* agreement set `S = H` (an additive subgroup — the `δ=0` base case), the Shaw operator
is **exactly computable** — no unknown:

> **`shawError_subgroup_eq`** — `𝒮(H; s₀, s₁) = |H| · Σ_{ψ ∈ H^⊥ ∩ s₁^⊥, ψ ≠ 0} ψ(s₀)`.

So, for an additive subgroup `H`, the Shaw operator IS the dual-code character sum restricted to
`s₁^⊥`. Axiom-clean.

**What this does NOT give (audit 2026-10-28, PG-076).** The prize agreement set is a *union* of
Hamming balls `S = ⋃_{c∈C} B(c, δn)`. Replacing `[ψ∈H^⊥]` by the Krawtchouk factor `K_{δn}(ψ)`
(the Fourier transform of a Hamming ball) gives `|C|·[ψ∈C^⊥]·K_{δn}(ψ)`, the Fourier transform of
the *convolution* `1_C * 1_B` of the code indicator with a ball indicator; that convolution counts
nearby codewords with multiplicity. It equals
the union indicator `1_S` only when the relevant balls are disjoint (unique-decoding radius), or
after a separate multiplicity correction. Example: the binary length-2 repetition code
`C = {00, 11}` at radius 1 has union of balls equal to all of `F_2^2`, but `1_C * 1_B` has total
mass `2·3 = 6` (the words `01`, `10` are covered twice); at the nontrivial dual character `11` the
union transform is `0` while the convolution transform is `2·(1 − 1 − 1) = −2`. So above unique
decoding the Krawtchouk-weighted dual sum cannot directly replace the overlapping-union Shaw
operator; indicator coverage and list multiplicity must be kept separate. No in-tree theorem here
identifies the prize-ball Shaw operator with a Krawtchouk-weighted dual sum.
-/
set_option linter.style.longLine false


open Finset
open ArkLib.ProximityGap.LineIncidenceSpectral

namespace ArkLib.ProximityGap.ShawOperator

variable {F V : Type*} [Field F] [Fintype F] [AddCommGroup V] [Fintype V] [DecidableEq V]
  [Module F V]

/-- **Subgroup character-orthogonality.** For an additive subgroup `H` (closed under `+`, `-`, with
`0 ∈ H`), `Σ_{s∈H} ψ(s) = |H|` if `ψ` is trivial on `H`, else `0`. -/
theorem char_sum_subgroup {H : Finset V} (h0 : (0 : V) ∈ H)
    (hadd : ∀ a ∈ H, ∀ b ∈ H, a + b ∈ H) (hneg : ∀ a ∈ H, -a ∈ H) (ψ : AddChar V ℂ) :
    (∑ s ∈ H, ψ s) = if (∀ h ∈ H, ψ h = 1) then (H.card : ℂ) else 0 := by
  by_cases htriv : ∀ h ∈ H, ψ h = 1
  · rw [if_pos htriv, Finset.sum_congr rfl (fun s hs => htriv s hs), Finset.sum_const,
      nsmul_eq_mul, mul_one]
  · rw [if_neg htriv]
    push_neg at htriv
    obtain ⟨h₀, hh₀, hne⟩ := htriv
    -- reindex s ↦ s + h₀ is a bijection of H
    have hb : (∑ s ∈ H, ψ (s + h₀)) = ∑ s ∈ H, ψ s := by
      refine Finset.sum_nbij' (fun s => s + h₀) (fun s => s + -h₀) ?_ ?_ ?_ ?_ ?_
      · intro a ha; exact hadd a ha h₀ hh₀
      · intro a ha; exact hadd a ha _ (hneg h₀ hh₀)
      · intro a _; simp
      · intro a _; simp
      · intro a _; rfl
    -- but Σ ψ(s+h₀) = ψ(h₀) · Σ ψ s
    have hfac : (∑ s ∈ H, ψ (s + h₀)) = ψ h₀ * ∑ s ∈ H, ψ s := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun s _ => by rw [AddChar.map_add_eq_mul, mul_comm])
    rw [hb] at hfac
    -- (1 - ψ h₀) · Σ = 0, and ψ h₀ ≠ 1
    have : (1 - ψ h₀) * (∑ s ∈ H, ψ s) = 0 := by linear_combination hfac
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (by linear_combination -h) hne
    · exact h

omit [Fintype F] in
/-- **The Shaw operator's exact closed form for a linear agreement set.** `𝒮(H; s₀, s₁)` is the
dual-code character sum: `|H| · Σ_{ψ ∈ H^⊥ ∩ s₁^⊥, ψ ≠ 0} ψ(s₀)`. -/
theorem shawError_subgroup_eq {H : Finset V} (h0 : (0 : V) ∈ H)
    (hadd : ∀ a ∈ H, ∀ b ∈ H, a + b ∈ H) (hneg : ∀ a ∈ H, -a ∈ H) (s₀ s₁ : V) :
    shawError (F := F) H s₀ s₁
      = ∑ ψ : AddChar V ℂ,
          (if directionChar (F := F) ψ s₁ = 0 ∧ ψ ≠ 0 ∧ (∀ h ∈ H, ψ h = 1)
            then (H.card : ℂ) * ψ s₀ else 0) := by
  rw [shawError]
  refine Finset.sum_congr rfl (fun ψ _ => ?_)
  by_cases hcond : directionChar (F := F) ψ s₁ = 0 ∧ ψ ≠ 0
  · rw [if_pos hcond]
    -- Σ_{s∈H} ψ(s₀−s) = ψ(s₀) · Σ_{s∈H} ψ(−s) = ψ(s₀) · Σ_{s∈H} ψ(s) (neg-bijection)
    have hneg_sum : (∑ s ∈ H, ψ (s₀ - s)) = ψ s₀ * ∑ s ∈ H, ψ s := by
      rw [Finset.mul_sum]
      have hbij : (∑ s ∈ H, ψ (s₀ - s)) = ∑ s ∈ H, ψ (s₀ + s) := by
        refine Finset.sum_nbij' (fun s => -s) (fun s => -s) ?_ ?_ ?_ ?_ ?_
        · intro a ha; exact hneg a ha
        · intro a ha; exact hneg a ha
        · intro a _; simp
        · intro a _; simp
        · intro a _; rw [sub_eq_add_neg]
      rw [hbij]
      exact Finset.sum_congr rfl (fun s _ => by rw [AddChar.map_add_eq_mul])
    rw [hneg_sum, char_sum_subgroup h0 hadd hneg ψ]
    by_cases htriv : ∀ h ∈ H, ψ h = 1
    · rw [if_pos htriv, if_pos ⟨hcond.1, hcond.2, htriv⟩]; ring
    · rw [if_neg htriv, if_neg (fun h => htriv h.2.2), mul_zero]
  · rw [if_neg hcond, if_neg (fun h => hcond ⟨h.1, h.2.1⟩)]

end ArkLib.ProximityGap.ShawOperator

#print axioms ArkLib.ProximityGap.ShawOperator.shawError_subgroup_eq
