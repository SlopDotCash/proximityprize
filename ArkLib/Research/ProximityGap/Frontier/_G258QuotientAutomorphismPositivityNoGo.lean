/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Tactic

/-!
# G258: quotient automorphisms preserve positivity and the full Fourier multiset

G257 found conjugate-pair permutations of the quotient Fourier spectrum that reverse the
rank-five and rank-six covariance, but most unconstrained optimizers invert to signed physical
profiles. This left positivity, integrality, and sparse support as a possible repair.

The repair fails for a structural reason. Multiplication by a unit on `ZMod N` relabels a quotient
profile. It preserves nonnegativity, integrality, total mass, and support cardinality. Mathlib's
`dft_comp_unitMul` proves that its DFT is only permuted, so the complete complex Fourier-value
multiset is preserved exactly, not merely its magnitudes or phase histogram.

At the exact proper-subgroup cell `(n,p,m)=(16,1297,81)`, the physical weighted-relation profile is
the indicator of the sixteen-point set `baseSupport`. Relabeling by the unit `53` (inverse `26`)
produces the sixteen-point `movedSupport`. The exact physical-space centered covariances are

```text
                 aligned       relabeled
rank five:       +1261081      -346283
rank six:        +3691265      -1161769.
```

Thus one and the same positivity-preserving, integral, support-size-preserving one-sided relabeling
reverses both ranks while preserving the full Fourier multiset and inverse-character pairing. The
exact subgroup and adjacent-rank profiles producing the four integer correlations are recomputed by
`scripts/probes/g258_quotient_automorphism_positivity_nogo.py`; the Lean file kernel-checks the
structural DFT mechanism, the two supports, and the integer covariance certificates.

This is a route no-go, not a production-prime estimate. It does not preserve the *labelled* support
set. G265 records the essential admissibility correction: a physical primitive-root coordinate
change relabels `W` and `R` simultaneously and therefore preserves the covariance exactly.
G258's one-sided move is a countermodel to label-free marginal data, not an alternative profile of
the fixed sponsor pair. A surviving certificate must use that row-labelled placement, equivalently
the actual joint sponsor-prime covariance, rather than positivity or sparse support as label-free
marginal data.
-/

open Finset ZMod

namespace ArkLib.ProximityGap.Frontier.G258QuotientAutomorphismPositivityNoGo

variable {N : ℕ} [NeZero N]

/-- Relabel a cyclic physical profile by multiplication with a unit. -/
def unitRelabel {α : Type*} (u : (ZMod N)ˣ) (f : ZMod N → α) : ZMod N → α :=
  fun x => f (u.val * x)

/-- Unit relabeling only permutes the DFT coordinates. -/
theorem dft_unitRelabel (u : (ZMod N)ˣ) (f : ZMod N → ℂ) (k : ZMod N) :
    𝓕 (unitRelabel u f) k = 𝓕 f (u⁻¹.val * k) := by
  exact dft_comp_unitMul f u k

/-- A test-function formulation of exact Fourier-multiset preservation. This is stronger than
preserving magnitudes or an empirical phase histogram: every sum depending only on the multiset of
complex DFT values is unchanged. -/
theorem dft_multiset_test_sum_eq (u : (ZMod N)ˣ) (f : ZMod N → ℂ) (h : ℂ → ℂ) :
    ∑ k : ZMod N, h (𝓕 (unitRelabel u f) k) = ∑ k : ZMod N, h (𝓕 f k) := by
  simp_rw [dft_unitRelabel]
  refine Fintype.sum_equiv u⁻¹.mulLeft _ _ ?_
  intro x
  rfl

/-- The frequency permutation also preserves inverse-character pairs. -/
theorem inverse_pair_preserved {M : ℕ} (u : (ZMod M)ˣ) (k : ZMod M) :
    u⁻¹.val * (-k) = -(u⁻¹.val * k) := by
  ring

/-- Unit relabeling preserves the total mass of any additive profile. -/
theorem unitRelabel_sum_eq {M : Type*} [AddCommMonoid M]
    (u : (ZMod N)ˣ) (f : ZMod N → M) :
    ∑ x, unitRelabel u f x = ∑ x, f x := by
  refine Fintype.sum_equiv u.mulLeft _ _ ?_
  intro x
  rfl

abbrev Q := ZMod 81

instance moduleInstance_G258QuotientAutomorphismPositivityNoGo_1 : NeZero 81 := ⟨by norm_num⟩

/-- The physical relabeling unit. Its inverse is `26 mod 81`. -/
def u53 : (ZMod 81)ˣ :=
  ⟨(53 : ZMod 81), (26 : ZMod 81), by decide, by decide⟩

/-- The exact `0/1` weighted-relation quotient support at `(n,p)=(16,1297)`. -/
def baseSupport : Finset Q :=
  {0, 6, 8, 12, 18, 21, 31, 35, 41, 42, 47, 57, 60, 65, 72, 78}

/-- The support after the physical unit relabeling by `53`. -/
def movedSupport : Finset Q :=
  {0, 3, 7, 9, 13, 19, 21, 24, 39, 46, 60, 63, 69, 70, 75, 77}

/-- The exact integral nonnegative base profile. -/
def baseProfile (x : Q) : ℕ :=
  if x ∈ baseSupport then 1 else 0

/-- The relabeled profile. -/
def movedProfile (x : Q) : ℕ :=
  unitRelabel u53 baseProfile x

/-- The fixed support data agree with the structural unit relabeling. -/
theorem movedProfile_eq_supportIndicator : ∀ x : Q,
    movedProfile x = if x ∈ movedSupport then 1 else 0 := by
  decide

/-- Both profiles have exactly sixteen occupied quotient classes. -/
theorem support_cards : baseSupport.card = 16 ∧ movedSupport.card = 16 := by
  decide

/-- Both physical profiles are pointwise integral `0/1` profiles, hence nonnegative. -/
theorem profiles_zero_or_one (x : Q) :
    (baseProfile x = 0 ∨ baseProfile x = 1) ∧
      (movedProfile x = 0 ∨ movedProfile x = 1) := by
  constructor
  · by_cases hx : x ∈ baseSupport
    · right; simp [baseProfile, hx]
    · left; simp [baseProfile, hx]
  · rw [movedProfile_eq_supportIndicator]
    by_cases hx : x ∈ movedSupport
    · right; simp [hx]
    · left; simp [hx]

/-- The exact mass `16` is preserved. -/
theorem profile_masses :
    (∑ x : Q, baseProfile x) = 16 ∧ (∑ x : Q, movedProfile x) = 16 := by
  constructor
  · decide
  · change (∑ x : Q, unitRelabel u53 baseProfile x) = 16
    rw [unitRelabel_sum_eq]
    decide

/-- The concrete profiles have exactly the same complete complex DFT multiset. -/
theorem concrete_dft_multiset_test_sum_eq (h : ℂ → ℂ) :
    ∑ k : Q, h (𝓕 (fun x => (baseProfile x : ℂ)) k) =
      ∑ k : Q, h (𝓕 (fun x => (movedProfile x : ℂ)) k) := by
  rw [show (fun x => (movedProfile x : ℂ)) =
      unitRelabel u53 (fun x => (baseProfile x : ℂ)) by
    funext x
    simp [unitRelabel, movedProfile]]
  symm
  apply dft_multiset_test_sum_eq

/-- Integer centered covariance on a quotient of size `m`. -/
def centeredCov (m massW massR sumWR : ℤ) : ℤ :=
  m * sumWR - massW * massR

/-- Exact rank-five correlation totals from the physical profile computation. -/
theorem rankFive_covariances :
    centeredCov 81 16 496733 113689 = 1261081 ∧
      centeredCov 81 16 496733 93845 = -346283 := by
  norm_num [centeredCov]

/-- Exact rank-six correlation totals from the physical profile computation. -/
theorem rankSix_covariances :
    centeredCov 81 16 2185369 477249 = 3691265 ∧
      centeredCov 81 16 2185369 417335 = -1161769 := by
  norm_num [centeredCov]

/-- The same admissible unit relabeling reverses both rank-five and rank-six signs. -/
theorem same_relabel_reverses_both_ranks :
    0 < centeredCov 81 16 496733 113689 ∧
      centeredCov 81 16 496733 93845 < 0 ∧
      0 < centeredCov 81 16 2185369 477249 ∧
      centeredCov 81 16 2185369 417335 < 0 := by
  norm_num [centeredCov]

/-! ## Axiom audit -/
#print axioms dft_unitRelabel
#print axioms dft_multiset_test_sum_eq
#print axioms concrete_dft_multiset_test_sum_eq
#print axioms same_relabel_reverses_both_ranks

end ArkLib.ProximityGap.Frontier.G258QuotientAutomorphismPositivityNoGo
