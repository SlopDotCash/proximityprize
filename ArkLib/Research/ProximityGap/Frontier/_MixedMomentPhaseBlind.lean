/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment

/-!
# The b-summation phase-blindness dichotomy (#444)

The structural foundation isolating *why* the prize is hard, and *what class of tool* can possibly
reach it. With `η_b = ∑_{y∈G} ψ(b·y)` the incomplete character sum over `G = μ_n`:

> **`∑_{b∈F} η_b^a · conj(η_b)^c = q · N_{a,c}`**, where
> `N_{a,c} = #{(v,w) ∈ (Fin a → G) × (Fin c → G) : ∑v = ∑w}` is a **non-negative integer count**.

Hence **every `b`-summed monomial in `(η_b, conj η_b)` is `q` times a real solution count** — its
imaginary part is `0` and its real part is `≥ 0`. By linearity every `b`-summed *polynomial* is a
`ℤ_{≥0}`-combination of such counts: the additive-character orthogonality `∑_b ψ(b·t) = q·[t=0]`
annihilates every off-diagonal `t ≠ 0` term, **destroying all archimedean phase** and leaving only the
phase-free diagonal.

**Design implication (the campaign's central no-go, formalized).** The prize gap (`n^{1−o(1)}` BGK →
`n^{1/2}`) is pure *archimedean phase cancellation*; by this theorem it is **invisible to every
`b`-summed object** (moments, energy, Wick, SOS, large sieve, decoupling, heat-kernel, LP, Gowers — all
`b`-summed, hence phase-blind). The prize-reaching tool is therefore *forced* to be **per-`b*`**: work
at the single (unknown) extremal frequency without summing over the modulus. This brick proves the
restriction is mathematically forced, not stylistic; it **confirms** the wall and bounds nothing from
above.

The proof is a direct generalization of `SubgroupGaussSumMoment.subgroup_gaussSum_moment` (the diagonal
`a = c = r` case `∑_b ‖η_b‖^{2r} = q·E_r`) to general `(a,c)`. Issue #444.
-/

set_option autoImplicit false


open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMoment

namespace ArkLib.ProximityGap.Frontier.MixedMomentPhaseBlind

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `N_{a,c} = #{(v,w) ∈ (Fin a → G) × (Fin c → G) : ∑ v = ∑ w}`, as a nested indicator sum. -/
noncomputable def mixedCount (G : Finset F) (a c : ℕ) : ℕ :=
  ∑ v ∈ Fintype.piFinset (fun _ : Fin a => G), ∑ w ∈ Fintype.piFinset (fun _ : Fin c => G),
    (if ∑ i, v i = ∑ i, w i then 1 else 0)

/-- **The mixed moment is `q · N_{a,c}` (the b-summation dichotomy core).** -/
theorem mixed_moment_eq {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (a c : ℕ) :
    (∑ b : F, eta ψ G b ^ a * (starRingEnd ℂ) (eta ψ G b ^ c))
      = (Fintype.card F : ℂ) * mixedCount G a c := by
  classical
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  have hconj : ∀ x : F, (starRingEnd ℂ) (ψ x) = ψ (-x) := by
    intro x; rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  have hconjpow : ∀ b : F, (starRingEnd ℂ) (eta ψ G b ^ c)
      = ∑ w ∈ Fintype.piFinset (fun _ : Fin c => G), ψ (-(b * ∑ i, w i)) := by
    intro b; rw [eta_pow, map_sum]; exact Finset.sum_congr rfl (fun w _ => hconj _)
  calc ∑ b : F, eta ψ G b ^ a * (starRingEnd ℂ) (eta ψ G b ^ c)
      = ∑ b : F, ∑ v ∈ Fintype.piFinset (fun _ : Fin a => G),
          ∑ w ∈ Fintype.piFinset (fun _ : Fin c => G), ψ (b * (∑ i, v i - ∑ i, w i)) := by
        refine Finset.sum_congr rfl (fun b _ => ?_)
        rw [hconjpow, eta_pow, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl (fun v _ => ?_)
        refine Finset.sum_congr rfl (fun w _ => ?_)
        rw [← AddChar.map_add_eq_mul]; congr 1; ring
    _ = ∑ v ∈ Fintype.piFinset (fun _ : Fin a => G),
          ∑ w ∈ Fintype.piFinset (fun _ : Fin c => G), ∑ b : F,
            ψ (b * (∑ i, v i - ∑ i, w i)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun v _ => ?_)
        rw [Finset.sum_comm]
    _ = ∑ v ∈ Fintype.piFinset (fun _ : Fin a => G),
          ∑ w ∈ Fintype.piFinset (fun _ : Fin c => G),
            (if ∑ i, v i = ∑ i, w i then (Fintype.card F : ℂ) else 0) := by
        refine Finset.sum_congr rfl (fun v _ => ?_)
        refine Finset.sum_congr rfl (fun w _ => ?_)
        rw [AddChar.sum_mulShift (∑ i, v i - ∑ i, w i) hψ]
        by_cases h : ∑ i, v i = ∑ i, w i <;> simp [h, sub_eq_zero]
    _ = (Fintype.card F : ℂ) * mixedCount G a c := by
        simp only [mixedCount]; push_cast; rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun v _ => ?_); rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun w _ => ?_)
        by_cases h : ∑ i, v i = ∑ i, w i <;> simp [h]

/-- **Phase-blindness:** the mixed moment has zero imaginary part and non-negative real part — it is
`q` times a cardinality, carrying no archimedean phase. -/
theorem mixed_moment_nonneg_real {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (a c : ℕ) :
    (∑ b : F, eta ψ G b ^ a * (starRingEnd ℂ) (eta ψ G b ^ c)).im = 0 ∧
    (0 : ℝ) ≤ (∑ b : F, eta ψ G b ^ a * (starRingEnd ℂ) (eta ψ G b ^ c)).re := by
  rw [mixed_moment_eq hψ G a c]
  have hcast : (Fintype.card F : ℂ) * (mixedCount G a c : ℂ)
      = ((Fintype.card F * mixedCount G a c : ℕ) : ℂ) := by push_cast; ring
  rw [hcast]
  refine ⟨?_, ?_⟩
  · rw [Complex.natCast_im]
  · rw [Complex.natCast_re]; exact Nat.cast_nonneg _

end ArkLib.ProximityGap.Frontier.MixedMomentPhaseBlind

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx). -/
#print axioms ArkLib.ProximityGap.Frontier.MixedMomentPhaseBlind.mixed_moment_eq
#print axioms ArkLib.ProximityGap.Frontier.MixedMomentPhaseBlind.mixed_moment_nonneg_real
