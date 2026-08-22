/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
Co-authored-by: wakesync <shadow@shad0w.xyz>
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ConcreteMomentAssembly
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVHalfMassDilationForm

/-!
# Door-(iv) Lane-2/3: the TRIVIAL dilation-descent recursion `M(μ_n) ≤ 2·M(μ_{n/2})` (#444)

The dilation form (`_DoorIVHalfMassDilationForm`, `223b4c0d2`) proved the per-frequency split on the
disjoint index-2 cover `G = H ∪ g·H` (`H = μ_{n/2}`, `g` = coset rep ≠ 0):
`‖η_b‖ = ‖eta ψ G b‖ ≤ ‖eta ψ H b‖ + ‖eta ψ H (g·b)‖`.

This file threads that pointwise split onto the **worst-period object** `worstPeriod ψ G`
(`M(G) = max_{b≠0} ‖η_b‖`, `ConcreteMomentAssembly`), producing the descent recursion the whole
dilation thread implicitly leans on but never kernel-anchored:

> **`M(μ_n) = M(H ∪ g·H) ≤ 2·M(μ_{n/2})`.**

The mechanism is elementary but the consequence is the precise *quantitative* reason the dilation
route is **moment-equivalent / saving-free**: for a nonzero frequency `b` (with `g ≠ 0`), BOTH `b` and
`g·b` are nonzero, so each sub-period magnitude `‖eta ψ H ·‖` is `≤ M(H)`; the dilation split then gives
`‖η_b‖ ≤ 2·M(H)` for every nonzero `b`, hence `M(G) ≤ 2·M(H)`.

**Why this LOCKS the dilation route (companion to the probed "structureless" verdict
`_DoorIVTwoDilateNoJointExtreme`, `34bcd204d`).**  Iterating the factor-2 recursion down the dyadic
tower `μ_n ⊃ μ_{n/2} ⊃ ... ⊃ μ_1` (`a = log₂ n` halvings) gives only
`M(μ_n) ≤ 2^a · M(μ_1) = n · M(μ_1)` — i.e. the TRIVIAL `M ≤ n` ceiling (`μ_1 = {1}` ⇒ `M(μ_1) = O(1)`),
**no √-saving whatsoever**.  The prize needs `M(μ_n) ≤ C·√(n·log)`, so any working descent must BEAT
the factor 2 by a coherence-slack factor `< 2` at every level — and that is exactly what the probe
`_DoorIVTwoDilateNoJointExtreme` showed does NOT happen (no co-peak, no excess correlation; the worst-b
half-mass routes back to the marginal envelope).  The factor here is `2` precisely because at the
worst frequency the two dilates co-ray (`ρ(b*) = 1`, `norm_eta_eq_two_dilate_of_coherent`): the split
inequality is an EQUALITY at `b*`, so the trivial factor `2` cannot be shaved by the triangle
inequality alone.

This is a real, certain, citable **Lane-2 capstone rung / Lane-3 constraint lemma**.  It states the
trivial descent quantitatively and pins WHY it is trivial.  It does NOT bound `M(μ_n)` below `2·M(H)`,
makes NO cancellation / completion / moment / anti-concentration / capacity claim, and CORE stays OPEN.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)
open ArkLib.ProximityGap.I031DilationOrbitReduction (nonzeroFreqs mem_nonzeroFreqs)
open ProximityGap.Frontier.ConcreteMomentAssembly (worstPeriod worstPeriod_nonneg)
open ArkLib.ProximityGap.Frontier.DoorIVHalfMassDilationForm

namespace ArkLib.ProximityGap.Frontier.DoorIVDilationDescentRecursion

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Per-frequency sub-period bound.**  For a nonzero frequency `c`, the sub-period magnitude
`‖eta ψ H c‖` is at most the worst period `M(H) = max_{b≠0} ‖η_b‖` over the same subgroup `H`. -/
theorem norm_eta_le_worstPeriod {ψ : AddChar F ℂ} (H : Finset F)
    (hne : (nonzeroFreqs F).Nonempty) {c : F} (hc : c ≠ 0) :
    ‖eta ψ H c‖ ≤ worstPeriod ψ H hne := by
  unfold worstPeriod
  exact Finset.le_sup' (fun b => ‖eta ψ H b‖) (mem_nonzeroFreqs.mpr hc)

/-- **The two-dilate half-mass is `≤ 2·M(H)` at every nonzero frequency.**  For `g ≠ 0` and `b ≠ 0`,
both `b` and `g·b` are nonzero, so each sub-period magnitude is `≤ M(H)` and their sum is `≤ 2·M(H)`. -/
theorem two_dilate_le_two_mul_worstPeriod {ψ : AddChar F ℂ} (H : Finset F)
    (hne : (nonzeroFreqs F).Nonempty) {g b : F} (hg : g ≠ 0) (hb : b ≠ 0) :
    ‖eta ψ H b‖ + ‖eta ψ H (g * b)‖ ≤ 2 * worstPeriod ψ H hne := by
  have h1 : ‖eta ψ H b‖ ≤ worstPeriod ψ H hne := norm_eta_le_worstPeriod H hne hb
  have h2 : ‖eta ψ H (g * b)‖ ≤ worstPeriod ψ H hne :=
    norm_eta_le_worstPeriod H hne (mul_ne_zero hg hb)
  linarith

/-- **Pointwise dilation-descent bound.**  On the disjoint index-2 cover `G = H ∪ g·H`, the period
magnitude at any nonzero frequency `b` is at most twice the half-subgroup worst period:
`‖η_b‖ ≤ 2·M(H)`. -/
theorem norm_eta_union_le_two_mul_worstPeriod {ψ : AddChar F ℂ} (H : Finset F)
    (hne : (nonzeroFreqs F).Nonempty) {g b : F} (hg : g ≠ 0) (hb : b ≠ 0)
    (hdisj : Disjoint H (H.image (fun y => g * y))) :
    ‖eta ψ (H ∪ H.image (fun y => g * y)) b‖ ≤ 2 * worstPeriod ψ H hne :=
  le_trans (norm_eta_le_two_dilate H hg hdisj) (two_dilate_le_two_mul_worstPeriod H hne hg hb)

/-- **★ The trivial dilation-descent recursion `M(μ_n) ≤ 2·M(μ_{n/2})`.**  Taking the max over all
nonzero frequencies of the pointwise bound, the worst period of the index-2 cover `G = H ∪ g·H` is at
most twice the worst period of the half-subgroup `H`:
`worstPeriod ψ (H ∪ g·H) ≤ 2 · worstPeriod ψ H`.

This is the load-bearing descent inequality of the dilation thread.  Iterated `log₂ n` times it gives
only the trivial `M(μ_n) ≤ n·M(μ_1)` ceiling (no √-saving); the prize requires beating the factor `2`
at every level, which the probe `_DoorIVTwoDilateNoJointExtreme` showed does not happen.  No CORE /
cancellation / completion / moment / anti-concentration / capacity claim; CORE stays OPEN. -/
theorem worstPeriod_union_le_two_mul_worstPeriod {ψ : AddChar F ℂ} (H : Finset F)
    (hne : (nonzeroFreqs F).Nonempty) {g : F} (hg : g ≠ 0)
    (hdisj : Disjoint H (H.image (fun y => g * y))) :
    worstPeriod ψ (H ∪ H.image (fun y => g * y)) hne ≤ 2 * worstPeriod ψ H hne := by
  unfold worstPeriod
  rw [Finset.sup'_le_iff]
  intro b hb
  have hb0 : b ≠ 0 := mem_nonzeroFreqs.mp hb
  -- fold the half-subgroup worst period back into the `sup'` form for the RHS bound
  have := norm_eta_union_le_two_mul_worstPeriod (ψ := ψ) H hne hg hb0 hdisj
  simpa [worstPeriod] using this

/-- **Nonnegativity propagates through the recursion.**  Sanity companion: the descent bound is a
genuine inequality between nonnegative reals (both worst periods are `≥ 0`), so `0 ≤ 2·M(H)` and the
recursion is non-vacuous. -/
theorem two_mul_worstPeriod_nonneg {ψ : AddChar F ℂ} (H : Finset F)
    (hne : (nonzeroFreqs F).Nonempty) :
    0 ≤ 2 * worstPeriod ψ H hne := by
  have := worstPeriod_nonneg ψ H hne
  linarith

end ArkLib.ProximityGap.Frontier.DoorIVDilationDescentRecursion
