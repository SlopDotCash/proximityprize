/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Archimedean-phase brick: a Hermitian phase sequence has a REAL discrete Fourier transform

The RS proximity-gap prize core `M(n) ≤ C√(n log m)` reduces (issue #444) to the spectral flatness of the
Gauss-sum **phase sequence** `s_k = g(χ_k)/|g(χ_k)| = e^{iθ_k}` over the `m = (p−1)/n` characters
`χ_k ∈ H⊥` (`k ∈ ZMod m`), where `θ_k = arg g(χ_k)` is the **absolute archimedean phase** (= the root
number `ε(χ_k)`).

The first genuinely non-circular arithmetic constraint on that *absolute* phase: for `n = 2^μ` the
Gauss-sum conjugation `g(χ̄_k) = χ_k(−1)·conj(g(χ_k))` with `χ_k(−1) = (−1)^{nk} = +1` forces the
reflection `θ_{−k} = −θ_k`, i.e. the phase sequence is **Hermitian**: `s_{−k} = conj(s_k)`.

This file formalizes the *content* of that reduction: **a Hermitian sequence on `ZMod m` has a real DFT.**
Hence complex spectral flatness reduces to flatness of a *real* sequence — halving the prize object. The
arithmetic input (`s` is Hermitian, from `χ_k(−1)=+1`) is recorded as the hypothesis `hHerm`; the
DFT-is-real conclusion is proved here unconditionally for any Hermitian `s` and any unit-modulus additive
character `ψ`.

`#print axioms` at the bottom must report only `[propext, Classical.choice, Quot.sound]`.
-/

open scoped BigOperators
open Finset Complex

namespace ArkLib.ProximityGap.ArchimedeanPhase

variable {m : ℕ} [NeZero m]

/-- The discrete Fourier transform of `s : ZMod m → ℂ` against an additive character `ψ`, at frequency
`β`: `F(β) = ∑_k s(k) · ψ(k·β)`. -/
noncomputable def dft (ψ : AddChar (ZMod m) ℂ) (s : ZMod m → ℂ) (β : ZMod m) : ℂ :=
  ∑ k : ZMod m, s k * ψ (k * β)

/-- A sequence is **Hermitian** if `s(−k) = conj(s(k))` for all `k` (the reflection forced by the
Gauss-sum conjugation `χ_k(−1)=+1` when `n` is a power of two). -/
def Hermitian (s : ZMod m → ℂ) : Prop := ∀ k : ZMod m, s (-k) = (starRingEnd ℂ) (s k)

/-- **The brick.** If `s` is Hermitian and `ψ` is a unit-modulus additive character with
`ψ(−x) = conj(ψ(x))` (true for the standard additive characters of `ZMod m`, since `|ψ|=1`), then the
DFT `dft ψ s β` is a **real** number for every frequency `β` (it equals its own conjugate). -/
theorem dft_isReal_of_hermitian (ψ : AddChar (ZMod m) ℂ)
    (hψ : ∀ x : ZMod m, ψ (-x) = (starRingEnd ℂ) (ψ x))
    {s : ZMod m → ℂ} (hHerm : Hermitian s) (β : ZMod m) :
    (starRingEnd ℂ) (dft ψ s β) = dft ψ s β := by
  unfold dft
  -- conjugate the sum, then reindex k ↦ -k to recover the original sum
  rw [map_sum]
  -- reindex the RHS by the bijection `k ↦ -k`
  rw [← Equiv.sum_comp (Equiv.neg (ZMod m)) (fun k => s k * ψ (k * β))]
  refine Finset.sum_congr rfl ?_
  intro k _
  -- goal: conj (s k * ψ (k·β)) = s ((Equiv.neg) k) * ψ ((Equiv.neg) k · β)
  simp only [Equiv.neg_apply, map_mul]
  -- conj(s k) = s (-k) [Hermitian];  conj(ψ(k·β)) = ψ(-(k·β)) = ψ((-k)·β)
  rw [hHerm k, neg_mul, hψ (k * β)]

/-- Consequence: the **imaginary part vanishes** — `(dft ψ s β).im = 0` for every `β`. So complex
spectral flatness `max_β |dft ψ s β| ≤ C√(m log m)` is equivalent to flatness of the *real* sequence
`β ↦ (dft ψ s β).re`. This is the prize-object reduction (complex → real flatness) the archimedean-phase
oddness brick provides. -/
theorem dft_im_eq_zero_of_hermitian (ψ : AddChar (ZMod m) ℂ)
    (hψ : ∀ x : ZMod m, ψ (-x) = (starRingEnd ℂ) (ψ x))
    {s : ZMod m → ℂ} (hHerm : Hermitian s) (β : ZMod m) :
    (dft ψ s β).im = 0 := by
  have h := dft_isReal_of_hermitian ψ hψ hHerm β
  -- conj z = z ↔ z.im = 0
  rw [Complex.conj_eq_iff_im] at h
  exact h

/-- **Realification (explicit form).** For a Hermitian `s` and a unit-modulus reflective
character `ψ`, the DFT equals the complex cast of the *explicit real sum* of the per-term
real parts: `dft ψ s β = ↑(∑_k (s k * ψ (k·β)).re)`. Combined with
`dft_im_eq_zero_of_hermitian` this turns the complex prize sup `max_β |dft ψ s β|` into a sup
of an explicitly **real-valued** sum `β ↦ ∑_k (s k * ψ (k·β)).re`, the computable
realification the archimedean-phase oddness brick delivers. (Probe `probe_dft_re_sum.py`:
0 fails over m ∈ {6,8,12,16,17,32}, PROPER thin instances, never the full group.) -/
theorem dft_eq_realSum_of_hermitian (ψ : AddChar (ZMod m) ℂ)
    (hψ : ∀ x : ZMod m, ψ (-x) = (starRingEnd ℂ) (ψ x))
    {s : ZMod m → ℂ} (hHerm : Hermitian s) (β : ZMod m) :
    dft ψ s β = ((∑ k : ZMod m, (s k * ψ (k * β)).re : ℝ) : ℂ) := by
  -- a real complex number equals the cast of its real part
  have him : (dft ψ s β).im = 0 := dft_im_eq_zero_of_hermitian ψ hψ hHerm β
  have hre : dft ψ s β = ((dft ψ s β).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  rw [hre]
  -- now reduce the real part of the DFT sum to the sum of real parts
  congr 1
  unfold dft
  rw [Complex.re_sum]

/-- **Modulus realification.** For a Hermitian `s` and reflective unit-modulus `ψ`, the squared
modulus of the DFT has NO imaginary cross-term: `‖dft ψ s β‖^2 = (dft ψ s β).re ^ 2`. Hence the prize
modulus `|dft ψ s β|` is the absolute value of the single real coordinate `(dft ψ s β).re`, and the
spectral sup `max_β ‖dft ψ s β‖` is a sup of `|real|`. (Probe `probe_dft_normsq_real.py`: 0 fails over
m ∈ {6,8,12,16,17,32}, PROPER thin instances; the Plancherel companion also held but is left to the
standard L² theory.) -/
theorem dft_normSq_eq_re_sq_of_hermitian (ψ : AddChar (ZMod m) ℂ)
    (hψ : ∀ x : ZMod m, ψ (-x) = (starRingEnd ℂ) (ψ x))
    {s : ZMod m → ℂ} (hHerm : Hermitian s) (β : ZMod m) :
    Complex.normSq (dft ψ s β) = (dft ψ s β).re ^ 2 := by
  have him : (dft ψ s β).im = 0 := dft_im_eq_zero_of_hermitian ψ hψ hHerm β
  rw [Complex.normSq_apply, him]
  ring

end ArkLib.ProximityGap.ArchimedeanPhase

#print axioms ArkLib.ProximityGap.ArchimedeanPhase.dft_isReal_of_hermitian
#print axioms ArkLib.ProximityGap.ArchimedeanPhase.dft_im_eq_zero_of_hermitian
#print axioms ArkLib.ProximityGap.ArchimedeanPhase.dft_eq_realSum_of_hermitian
#print axioms ArkLib.ProximityGap.ArchimedeanPhase.dft_normSq_eq_re_sq_of_hermitian
