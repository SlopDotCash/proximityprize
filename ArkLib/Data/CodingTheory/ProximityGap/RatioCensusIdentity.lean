/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.FarCosetExplosion
import ArkLib.Data.CodingTheory.ProximityGap.LineBallIntersection
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Polynomial.Roots

/-!
# The ratio census at the GRS dual syndromes (#371, vector 1 — face 4 composed)

Companion to `LineBallIntersection.lean` (the coordinate-space ratio-census identity
`hammingNorm_line_add_lineRatioHits_card`, the heavy-fibre census
`lineRatioHeavy_card_mul_le_support`, and the pencil degree bounds) and to
`FarCosetExplosion.lean` (`badScalars_eq_explainable`, `epsMCA_ge_far_incidence`).
Probe: `scripts/probes/probe_ratio_census.py`.

**What is new here.**

1. **The pencil census collapse** (`pencil_lineBall_card_le_one`): completing the
   pencil obstruction — above the degree threshold the ENTIRE line–ball scalar set
   has at most ONE member (the degenerate pencil scalar, unique by
   `degenerate_gamma_unique`).  Honest scope: for the WB-2 doubly-rational family
   (degrees `≤ k + 2w − 1`, full support) the threshold clears the degree exactly when
   `n ≥ k + 3w` — the granularity-ladder regime, REPRODUCED not improved; in the window
   `(n−k)/3 ≤ w < (n−k)/2` this is silent and `SplitLocusBound` (named Prop, probe
   evidence only) is the open core in census form.

2. **The subset-ownership census** (`explainable_card_mul_le_census`,
   `badScalars_card_mul_le_choose`): the `KKH26DimOnePin` pair-ownership incidence count
   generalized from the dimension-one code to EVERY dimension.  For a code annihilated by
   per-`r`-subset dual functionals `λ_T`, agreement of the line `u₀ + γ•u₁` with a
   codeword on a witness set `S` forces `λ_T(u₀) + γ·λ_T(u₁) = 0` for every `T ⊆ S`, so
   each `T` with `λ_T(u₁) ≠ 0` DETERMINES `γ` — the explainable scalars own disjoint
   detecting-subset families inside the dual-syndrome ratio profile, and the census mass
   bound of `LineBallIntersection.lean` (instantiated at index type `Finset ι`) yields
   `#explainable · θ ≤ #{T : λ_T(u₁) ≠ 0} ≤ C(n, r)`.  At `r = 2`, `λ = (1, −1)` this is
   exactly the cross-fibre pair count of `KKH26DimOnePin.lean`.

3. **The GRS instantiation** (`lagrangeDual_sum_eq_zero`, `detect_of_no_interpolant`,
   `rs_badScalars_card_le_choose`): the dual functionals exist for every
   polynomial-evaluation code — the Lagrange functionals
   `λ_T(i) = ∏_{j ∈ T∖i} (xᵢ − xⱼ)⁻¹` (the minimal-support dual codewords, i.e. THE GRS
   SYNDROME FAMILY) annihilate degree-`≤ d` evaluations on `(d+2)`-subsets
   (top-coefficient extraction from Lagrange interpolation), and a direction not
   explainable on `S` is always detected by some `(d+2)`-subset of `S`.  Headline:
   for any degree-`≤ d` evaluation code on an injective domain, any radius `δ` with
   witness size `> d + 1`, and any `FarFromCode` direction,

     `#{γ : mcaEvent} ≤ C(n, d + 2)` — `q`-INDEPENDENT,

   composing verbatim with `badScalars_eq_explainable`/`epsMCA_ge_far_incidence`.

**Honest scope of the census bound.**  `C(n, d+2)` beats the trivial `q` bound only for
enormous fields and is exponentially vacuous at production dimension (`k = 2²⁴`,
`C(n, k+2) ≈ 2ⁿ·...`); at low dimension it is the `KKH26DimOnePin` device in general
form (at `d = 0`, witness size `3`, the `θ`-refined count recovers `(n²−n)/4` exactly).
The open core is untouched and is now localized in TWO census quantities: the
detecting-subset density `θ` inside witness sets (here only `θ ≥ 1` is used), and the
split-locus count `SplitLocusBound`.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.RatioCensusIdentity

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## Part 0: ratio-census fibres (inlined line-ball substrate)

These mirror the historical `LineBallIntersection.lean` ratio-census layer; they are
kept local so this file is self-contained against the substrate churn. -/

section RatioCensus

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The scalar that makes the affine line coordinate `u₀ i + γ * u₁ i` vanish, when
`u₁ i ≠ 0`. -/
def lineZeroRoot (u₀ u₁ : ι → F) (i : ι) : F :=
  -u₀ i / u₁ i

/-- Coordinates whose moving part is nonzero and whose zero-root is exactly `γ`. -/
def lineRatioHits (u₀ u₁ : ι → F) (γ : F) : Finset ι :=
  univ.filter (fun i => u₁ i ≠ 0 ∧ lineZeroRoot u₀ u₁ i = γ)

/-- Zero-slope coordinates that are nonzero for every scalar on the line. -/
def lineStaticNonzero (u₀ u₁ : ι → F) : Finset ι :=
  univ.filter (fun i => u₁ i = 0 ∧ u₀ i ≠ 0)

/-- On a nonzero-slope coordinate, the affine line vanishes exactly at the ratio-census root. -/
theorem line_coord_zero_iff_lineZeroRoot {u₀ u₁ : ι → F} {γ : F} {i : ι}
    (hi : u₁ i ≠ 0) :
    (u₀ + γ • u₁) i = 0 ↔ lineZeroRoot u₀ u₁ i = γ := by
  simp only [lineZeroRoot, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [div_eq_iff hi]
  constructor
  · intro h
    have h' : u₀ i = -(γ * u₁ i) := eq_neg_of_add_eq_zero_left h
    rw [h']; ring
  · intro h
    rw [← h]; ring

/-- **Ratio-census identity, additive form.** -/
theorem hammingNorm_line_add_lineRatioHits_card (u₀ u₁ : ι → F) (γ : F) :
    hammingNorm (u₀ + γ • u₁) + (lineRatioHits u₀ u₁ γ).card
      = (univ.filter (fun i => u₁ i ≠ 0)).card + (lineStaticNonzero u₀ u₁).card := by
  classical
  set N : Finset ι := univ.filter (fun i => (u₀ + γ • u₁) i ≠ 0) with hN
  set W : Finset ι := univ.filter (fun i => u₁ i ≠ 0) with hW
  set H : Finset ι := lineRatioHits u₀ u₁ γ with hH
  set Z : Finset ι := lineStaticNonzero u₀ u₁ with hZ
  have hZeq : N.filter (fun i => u₁ i = 0) = Z := by
    ext i
    simp only [hN, hZ, lineStaticNonzero, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hn, h0⟩
      exact ⟨h0, by simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h0] using hn⟩
    · rintro ⟨h0, hu₀⟩
      exact ⟨by simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h0] using hu₀, h0⟩
  have hNeq : N.filter (fun i => ¬ u₁ i = 0)
      = W.filter (fun i => ¬ lineZeroRoot u₀ u₁ i = γ) := by
    ext i
    simp only [hN, hW, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hn, hi⟩
      refine ⟨hi, ?_⟩
      intro hroot
      exact hn ((line_coord_zero_iff_lineZeroRoot (u₀ := u₀) (u₁ := u₁)
        (γ := γ) (i := i) hi).mpr hroot)
    · rintro ⟨hi, hroot⟩
      refine ⟨?_, hi⟩
      intro hzero
      exact hroot ((line_coord_zero_iff_lineZeroRoot (u₀ := u₀) (u₁ := u₁)
        (γ := γ) (i := i) hi).mp hzero)
  have hHeq : H = W.filter (fun i => lineZeroRoot u₀ u₁ i = γ) := by
    ext i
    simp only [hH, hW, lineRatioHits, Finset.mem_filter, Finset.mem_univ, true_and]
  have hNsplit :
      Z.card + (W.filter (fun i => ¬ lineZeroRoot u₀ u₁ i = γ)).card = N.card := by
    simpa [hZeq, hNeq] using
      (Finset.card_filter_add_card_filter_not (s := N) (p := fun i => u₁ i = 0))
  have hWsplit :
      H.card + (W.filter (fun i => ¬ lineZeroRoot u₀ u₁ i = γ)).card = W.card := by
    simpa [hHeq] using
      (Finset.card_filter_add_card_filter_not (s := W)
        (p := fun i => lineZeroRoot u₀ u₁ i = γ))
  have hnorm : hammingNorm (u₀ + γ • u₁) = N.card := by
    simp [hammingNorm, hN]
  calc
    hammingNorm (u₀ + γ • u₁) + H.card
        = N.card + H.card := by rw [hnorm]
    _ = W.card + Z.card := by omega

/-- The ratio-census fibres have total mass exactly `|supp u₁|`. -/
theorem sum_lineRatioHits_card_eq_support (u₀ u₁ : ι → F) :
    ∑ γ : F, (lineRatioHits u₀ u₁ γ).card
      = (univ.filter (fun i => u₁ i ≠ 0)).card := by
  classical
  set W : Finset ι := univ.filter (fun i => u₁ i ≠ 0) with hW
  have hfiber : ∀ γ : F,
      lineRatioHits u₀ u₁ γ = W.filter (fun i => lineZeroRoot u₀ u₁ i = γ) := by
    intro γ
    ext i
    simp only [lineRatioHits, hW, Finset.mem_filter, Finset.mem_univ, true_and]
  calc
    ∑ γ : F, (lineRatioHits u₀ u₁ γ).card
        = ∑ γ : F, (W.filter (fun i => lineZeroRoot u₀ u₁ i = γ)).card := by
          refine Finset.sum_congr rfl ?_
          intro γ _
          rw [hfiber γ]
    _ = W.card := by
          rw [← Finset.card_eq_sum_card_fiberwise
            (fun i _ => Finset.mem_univ (lineZeroRoot u₀ u₁ i))]

/-- Heavy ratio fibres are few.  This is the direct Markov/counting form of the ratio census. -/
theorem lineRatioHeavy_card_mul_le_support (u₀ u₁ : ι → F) (A : ℕ) :
    (univ.filter (fun γ : F => A ≤ (lineRatioHits u₀ u₁ γ).card)).card * A
      ≤ (univ.filter (fun i => u₁ i ≠ 0)).card := by
  classical
  set G : Finset F := univ.filter (fun γ : F => A ≤ (lineRatioHits u₀ u₁ γ).card) with hG
  calc
    G.card * A = ∑ _γ ∈ G, A := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ γ ∈ G, (lineRatioHits u₀ u₁ γ).card := by
          refine Finset.sum_le_sum ?_
          intro γ hγ
          rw [hG, Finset.mem_filter] at hγ
          exact hγ.2
    _ ≤ ∑ γ : F, (lineRatioHits u₀ u₁ γ).card :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ G)
    _ = (univ.filter (fun i => u₁ i ≠ 0)).card := sum_lineRatioHits_card_eq_support u₀ u₁

/-- **Polynomial ratio-level bound.** The ratio fibre at `γ` injects into the root set of the
nonzero pencil polynomial `P₀ + γ P₁`. -/
theorem lineRatioHits_card_le_natDegree_pencil
    (domain : ι ↪ F) (P₀ P₁ : F[X]) (γ : F)
    (hp : P₀ + C γ * P₁ ≠ 0) :
    (lineRatioHits (fun i => P₀.eval (domain i)) (fun i => P₁.eval (domain i)) γ).card
      ≤ (P₀ + C γ * P₁).natDegree := by
  classical
  let p : F[X] := P₀ + C γ * P₁
  let u₀ : ι → F := fun i => P₀.eval (domain i)
  let u₁ : ι → F := fun i => P₁.eval (domain i)
  set H : Finset ι := lineRatioHits u₀ u₁ γ with hH
  have hsub : H.image domain ⊆ p.roots.toFinset := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, hiH, rfl⟩ := hx
    have hiH' : i ∈ lineRatioHits u₀ u₁ γ := by simpa [hH] using hiH
    rw [lineRatioHits, Finset.mem_filter] at hiH'
    have hzero : (u₀ + γ • u₁) i = 0 :=
      (line_coord_zero_iff_lineZeroRoot (u₀ := u₀) (u₁ := u₁)
        (γ := γ) (i := i) hiH'.2.1).mpr hiH'.2.2
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot.def]
    simpa [p, u₀, u₁, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Polynomial.eval_add, Polynomial.eval_mul] using hzero
  change H.card ≤ p.natDegree
  calc
    H.card = (H.image domain).card := by
      rw [Finset.card_image_of_injective _ (fun _ _ h => domain.injective h)]
    _ ≤ p.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := Polynomial.card_roots' p

/-- Nondegenerate polynomial ratio fibres are bounded by the larger row degree. -/
theorem lineRatioHits_card_le_max_natDegree_pencil
    (domain : ι ↪ F) (P₀ P₁ : F[X]) (γ : F)
    (hp : P₀ + C γ * P₁ ≠ 0) :
    (lineRatioHits (fun i => P₀.eval (domain i)) (fun i => P₁.eval (domain i)) γ).card
      ≤ max P₀.natDegree P₁.natDegree := by
  refine (lineRatioHits_card_le_natDegree_pencil domain P₀ P₁ γ hp).trans ?_
  exact Polynomial.natDegree_add_le_of_le (le_refl P₀.natDegree)
    (Polynomial.natDegree_C_mul_le γ P₁)

/-- Caller-facing degree-budget form of `lineRatioHits_card_le_max_natDegree_pencil`. -/
theorem lineRatioHits_card_le_degreeBound_pencil
    (domain : ι ↪ F) (P₀ P₁ : F[X]) (γ : F) {D : ℕ}
    (hP₀ : P₀.natDegree ≤ D) (hP₁ : P₁.natDegree ≤ D)
    (hp : P₀ + C γ * P₁ ≠ 0) :
    (lineRatioHits (fun i => P₀.eval (domain i)) (fun i => P₁.eval (domain i)) γ).card
      ≤ D :=
  (lineRatioHits_card_le_max_natDegree_pencil domain P₀ P₁ γ hp).trans (max_le hP₀ hP₁)

end RatioCensus

/-! ## Part 1: the pencil census collapse (the ladder-reproduction theorem) -/

section Pencil

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- At most one scalar is degenerate (`P₀ + γ·P₁ = 0` identically) when `P₁ ≠ 0`. -/
theorem degenerate_gamma_unique (P₀ P₁ : F[X]) (hP₁ : P₁ ≠ 0) {γ₁ γ₂ : F}
    (h₁ : P₀ + C γ₁ * P₁ = 0) (h₂ : P₀ + C γ₂ * P₁ = 0) : γ₁ = γ₂ := by
  have hkey : (C γ₁ - C γ₂) * P₁ = 0 := by linear_combination h₁ - h₂
  rcases mul_eq_zero.mp hkey with h | h
  · exact Polynomial.C_inj.mp (sub_eq_zero.mp h)
  · exact absurd h hP₁

/-- **The pencil census collapse**: once the ratio-census threshold strictly exceeds the
degree budget `D`, the line–ball scalar set has at most ONE member — every member must be
the (unique) degenerate pencil scalar.  For the WB-2 doubly-rational family this threshold
condition is exactly the granularity-ladder regime `n ≥ k + 3w`; in the window it fails
and `SplitLocusBound` below is the remaining open quantity. -/
theorem pencil_lineBall_card_le_one
    (domain : ι ↪ F) (P₀ P₁ : F[X]) (hP₁ : P₁ ≠ 0) {D R : ℕ}
    (hP₀d : P₀.natDegree ≤ D) (hP₁d : P₁.natDegree ≤ D)
    (hD : D <
      (univ.filter (fun i => P₁.eval (domain i) ≠ 0)).card
        + (lineStaticNonzero (fun i => P₀.eval (domain i))
            (fun i => P₁.eval (domain i))).card - R) :
    (univ.filter (fun γ : F =>
        hammingNorm ((fun i => P₀.eval (domain i))
          + γ • (fun i => P₁.eval (domain i))) ≤ R)).card ≤ 1 := by
  rw [Finset.card_le_one]
  have hdeg : ∀ γ : F,
      hammingNorm ((fun i => P₀.eval (domain i))
        + γ • (fun i => P₁.eval (domain i))) ≤ R →
        P₀ + C γ * P₁ = 0 := by
    intro γ hγ
    by_contra hne
    -- the pencil is nondegenerate, so its ratio fibre is degree-bounded
    have hhits :
        (lineRatioHits (fun i => P₀.eval (domain i))
          (fun i => P₁.eval (domain i)) γ).card ≤ D :=
      lineRatioHits_card_le_degreeBound_pencil domain P₀ P₁ γ hP₀d hP₁d hne
    -- the ratio-census identity ties weight, fibre, support, and static together
    have hid := hammingNorm_line_add_lineRatioHits_card
      (fun i => P₀.eval (domain i)) (fun i => P₁.eval (domain i)) γ
    omega
  intro γ₁ h₁ γ₂ h₂
  exact degenerate_gamma_unique P₀ P₁ hP₁
    (hdeg γ₁ (Finset.mem_filter.mp h₁).2) (hdeg γ₂ (Finset.mem_filter.mp h₂).2)

/-- **The open improved claim, named** (NOT proven; probe evidence only —
`scripts/probes/probe_ratio_census.py`).  `SplitLocusBound domain D M`: every polynomial
pair of degree `≤ D` (nonzero direction) has at most `M` non-degenerate scalars whose
ratio fibre on the domain reaches the full degree budget `D`.  Probe S2: on smooth 2-power
orbits (`q ≤ 257`, `n ≤ 64`) adversarial split pairs ATTAIN fibre size `D`, but the number
of fully-split scalars stayed `O(1)` in every sample; probe S3: the SPARSE binomial family
(the KKH26 mechanism) concentrates a single fibre to `n/2`, so a small `M` at
window-shaped `D` must use non-sparsity of the WB-2 rational family.  Pinning
`M = poly(n)` there is the H-RC split-locus question — the open core in census form. -/
def SplitLocusBound (domain : ι ↪ F) (D M : ℕ) : Prop :=
  ∀ P₀ P₁ : F[X], P₀.natDegree ≤ D → P₁.natDegree ≤ D → P₁ ≠ 0 →
    (univ.filter (fun γ : F => P₀ + C γ * P₁ ≠ 0 ∧
        D ≤ (lineRatioHits (fun i => P₀.eval (domain i))
          (fun i => P₁.eval (domain i)) γ).card)).card ≤ M

end Pencil

/-! ## Part 2: the subset-ownership census — `KKH26DimOnePin` generalized -/

section Ownership

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- The `r`-subset dual syndrome family of a word `u`: for each `r`-subset `T`, the value
`∑_{i ∈ T} λ_T(i)·u(i)` (and `0` on subsets of the wrong size, so the family is supported
on the `C(n, r)` genuine syndromes). -/
def dualSyndrome (r : ℕ) (lam : Finset ι → ι → F) (u : ι → F) : Finset ι → F :=
  fun T => if T.card = r then ∑ i ∈ T, lam T i * u i else 0

open Classical in
/-- **The ownership bridge**: if the dual functionals annihilate the code and every
witness-sized set contains `≥ θ` subsets detecting the direction, then every explainable
scalar has ratio-census fibre of size `≥ θ` in the dual-syndrome profile — agreement with
a codeword on the witness set forces `λ_T(u₀) + γ·λ_T(u₁) = 0` on every contained `T`, so
each detecting `T` lands in the fibre of `γ`. -/
theorem explainable_lineRatioHits_ge
    (Cd : Set (ι → F)) (δ : ℝ≥0) (u₀ u₁ : ι → F) (r θ : ℕ)
    (lam : Finset ι → ι → F)
    (hkill : ∀ T : Finset ι, T.card = r → ∀ c ∈ Cd, ∑ i ∈ T, lam T i * c i = 0)
    (hdetect : ∀ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι →
        θ ≤ ((S.powersetCard r).filter fun T => ∑ i ∈ T, lam T i * u₁ i ≠ 0).card)
    {γ : F}
    (hexp : ∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
        ∃ w ∈ Cd, ∀ i ∈ S, w i = u₀ i + γ • u₁ i) :
    θ ≤ (lineRatioHits (dualSyndrome r lam u₀) (dualSyndrome r lam u₁) γ).card := by
  obtain ⟨S, hS, w, hwC, hag⟩ := hexp
  refine le_trans (hdetect S hS) (Finset.card_le_card ?_)
  intro T hT
  obtain ⟨hTmem, hTne⟩ := Finset.mem_filter.mp hT
  obtain ⟨hTsub, hTcard⟩ := Finset.mem_powersetCard.mp hTmem
  have hs₁ : dualSyndrome r lam u₁ T ≠ 0 := by
    simpa [dualSyndrome, hTcard] using hTne
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hs₁, ?_⟩
  -- the agreement forces the dual-syndrome line coordinate at `T` to vanish
  have hvanish : dualSyndrome r lam u₀ T + γ * dualSyndrome r lam u₁ T = 0 := by
    have hsum : ∑ i ∈ T, lam T i * (u₀ i + γ * u₁ i) = 0 := by
      rw [← hkill T hTcard w hwC]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hag i (hTsub hi), smul_eq_mul]
    simp only [dualSyndrome, if_pos hTcard]
    calc (∑ i ∈ T, lam T i * u₀ i) + γ * ∑ i ∈ T, lam T i * u₁ i
        = ∑ i ∈ T, lam T i * (u₀ i + γ * u₁ i) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
    _ = 0 := hsum
  -- convert to the `lineZeroRoot` form of the fibre
  show lineZeroRoot (dualSyndrome r lam u₀) (dualSyndrome r lam u₁) T = γ
  unfold lineZeroRoot
  rw [div_eq_iff hs₁]
  linear_combination -hvanish

open Classical in
/-- **The subset-ownership census count** (the `KKH26DimOnePin` pair-ownership incidence
count, generalized to every dimension): `#explainable · θ ≤ #{T : λ_T(u₁) ≠ 0}` — each
explainable scalar owns `≥ θ` detecting subsets, any detecting subset determines its
scalar, ownership is disjoint (the heavy-fibre census of `LineBallIntersection.lean` at
index type `Finset ι`). -/
theorem explainable_card_mul_le_census
    (Cd : Set (ι → F)) (δ : ℝ≥0) (u₀ u₁ : ι → F) (r θ : ℕ)
    (lam : Finset ι → ι → F)
    (hkill : ∀ T : Finset ι, T.card = r → ∀ c ∈ Cd, ∑ i ∈ T, lam T i * c i = 0)
    (hdetect : ∀ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι →
        θ ≤ ((S.powersetCard r).filter fun T => ∑ i ∈ T, lam T i * u₁ i ≠ 0).card) :
    (univ.filter fun γ : F =>
        ∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
          ∃ w ∈ Cd, ∀ i ∈ S, w i = u₀ i + γ • u₁ i).card * θ
      ≤ (univ.filter fun T : Finset ι => dualSyndrome r lam u₁ T ≠ 0).card := by
  refine le_trans (Nat.mul_le_mul_right θ (Finset.card_le_card ?_))
    (lineRatioHeavy_card_mul_le_support
      (dualSyndrome r lam u₀) (dualSyndrome r lam u₁) θ)
  intro γ hγ
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    explainable_lineRatioHits_ge Cd δ u₀ u₁ r θ lam hkill hdetect
      (Finset.mem_filter.mp hγ).2⟩

/-- The dual-syndrome support is contained in the `r`-subsets: `≤ C(n, r)` syndromes. -/
theorem dualSyndrome_supp_card_le (r : ℕ) (lam : Finset ι → ι → F) (u : ι → F) :
    (univ.filter fun T : Finset ι => dualSyndrome r lam u T ≠ 0).card
      ≤ (Fintype.card ι).choose r := by
  classical
  calc (univ.filter fun T : Finset ι => dualSyndrome r lam u T ≠ 0).card
      ≤ ((univ : Finset ι).powersetCard r).card := by
        refine Finset.card_le_card ?_
        intro T hT
        have h := (Finset.mem_filter.mp hT).2
        rw [Finset.mem_powersetCard]
        refine ⟨Finset.subset_univ _, ?_⟩
        by_contra hc
        exact h (by simp [dualSyndrome, hc])
  _ = (Fintype.card ι).choose r := by rw [Finset.card_powersetCard, Finset.card_univ]

open Classical in
/-- **The far-coset composition**: for `FarFromCode` directions the bad-scalar set IS the
explainable set (`badScalars_eq_explainable`), so the ownership census bounds the
`mcaEvent` count itself: `#bad · θ ≤ C(n, r)`. -/
theorem badScalars_card_mul_le_choose
    (Cd : Set (ι → F)) (δ : ℝ≥0) (u₀ u₁ : ι → F) (r θ : ℕ)
    (lam : Finset ι → ι → F)
    (hfar : FarCosetExplosion.FarFromCode Cd δ u₁)
    (hkill : ∀ T : Finset ι, T.card = r → ∀ c ∈ Cd, ∑ i ∈ T, lam T i * c i = 0)
    (hdetect : ∀ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι →
        θ ≤ ((S.powersetCard r).filter fun T => ∑ i ∈ T, lam T i * u₁ i ≠ 0).card) :
    (univ.filter fun γ : F =>
        mcaEvent (F := F) (A := F) Cd δ u₀ u₁ γ).card * θ
      ≤ (Fintype.card ι).choose r := by
  rw [FarCosetExplosion.badScalars_eq_explainable Cd δ hfar]
  exact le_trans
    (explainable_card_mul_le_census Cd δ u₀ u₁ r θ lam hkill hdetect)
    (dualSyndrome_supp_card_le r lam u₁)

end Ownership

/-! ## Part 3: the GRS dual functionals — Lagrange instantiation -/

section Lagrange

variable {ι : Type} [DecidableEq ι]

/-- The Lagrange dual functional on a subset `T`: `λ_T(i) = ∏_{j ∈ T∖i} (v i − v j)⁻¹`.
These are (up to normalization) the minimal-support dual codewords of the evaluation code —
the GRS syndrome family. -/
def lagrangeDual (v : ι → F) : Finset ι → ι → F :=
  fun T i => ∏ j ∈ T.erase i, (v i - v j)⁻¹

/-- The Lagrange dual functional is nonzero at members of an injectively-embedded set. -/
theorem lagrangeDual_ne_zero (v : ι → F) {T : Finset ι} (hvT : Set.InjOn v T)
    {i : ι} (hi : i ∈ T) : lagrangeDual v T i ≠ 0 := by
  unfold lagrangeDual
  rw [Finset.prod_ne_zero_iff]
  intro j hj
  obtain ⟨hji, hjT⟩ := Finset.mem_erase.mp hj
  exact inv_ne_zero (sub_ne_zero.mpr fun h => hji (hvT hjT hi h.symm))

/-- **The GRS annihilation law** (top-coefficient extraction from Lagrange interpolation):
for any polynomial of degree `≤ |T| − 2`,

  `∑_{i ∈ T} λ_T(i) · P(v i) = 0`.

The sum is the top coefficient of the interpolation of `P` on `T`, which equals `P` by
uniqueness — and `P` has no such coefficient. -/
theorem lagrangeDual_sum_eq_zero (v : ι → F) {T : Finset ι} (hvT : Set.InjOn v T)
    (P : F[X]) (hP : P.natDegree + 2 ≤ T.card) :
    ∑ i ∈ T, lagrangeDual v T i * P.eval (v i) = 0 := by
  classical
  have hdeglt : P.degree < (T.card : ℕ) := by
    refine lt_of_le_of_lt P.degree_le_natDegree ?_
    exact_mod_cast (by omega : P.natDegree < T.card)
  have hPI := Lagrange.eq_interpolate hvT hdeglt
  have hco : P.coeff (T.card - 1) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hI : (Lagrange.interpolate T v fun i => P.eval (v i)).coeff (T.card - 1)
      = ∑ i ∈ T, P.eval (v i) * lagrangeDual v T i := by
    rw [Lagrange.interpolate_apply, Polynomial.finset_sum_coeff]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Polynomial.coeff_C_mul]
    congr 1
    have hnd := Lagrange.natDegree_basis hvT hi
    have hlc : (Lagrange.basis T v i).leadingCoeff = lagrangeDual v T i := by
      unfold Lagrange.basis lagrangeDual
      rw [Polynomial.leadingCoeff_prod]
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [Lagrange.basisDivisor, Polynomial.leadingCoeff_mul,
        Polynomial.leadingCoeff_C, Polynomial.leadingCoeff_X_sub_C, mul_one]
    rw [← hnd, Polynomial.coeff_natDegree, hlc]
  have hzero : (0 : F) = ∑ i ∈ T, P.eval (v i) * lagrangeDual v T i := by
    rw [← hI, ← hco]
    conv_lhs => rw [hPI]
  calc ∑ i ∈ T, lagrangeDual v T i * P.eval (v i)
      = ∑ i ∈ T, P.eval (v i) * lagrangeDual v T i :=
        Finset.sum_congr rfl fun i _ => mul_comm _ _
  _ = 0 := hzero.symm

/-- The Lagrange dual functionals annihilate every degree-`≤ d` evaluation code on
`(d + 2)`-subsets — the `hkill` hypothesis of the ownership census, discharged. -/
theorem lagrangeDual_kills (v : ι → F) (hv : Function.Injective v) (d : ℕ)
    (Cd : Set (ι → F))
    (hC : ∀ c ∈ Cd, ∃ q : F[X], q.natDegree ≤ d ∧ ∀ i, c i = q.eval (v i)) :
    ∀ T : Finset ι, T.card = d + 2 → ∀ c ∈ Cd,
      ∑ i ∈ T, lagrangeDual v T i * c i = 0 := by
  intro T hT c hc
  obtain ⟨q, hq, hcq⟩ := hC c hc
  calc ∑ i ∈ T, lagrangeDual v T i * c i
      = ∑ i ∈ T, lagrangeDual v T i * q.eval (v i) :=
        Finset.sum_congr rfl fun i _ => by rw [hcq i]
  _ = 0 := lagrangeDual_sum_eq_zero v hv.injOn q (by omega)

/-- **The detection law**: if NO degree-`≤ d` polynomial explains `u₁` on `S`
(`|S| ≥ d + 2`), then some `(d + 2)`-subset of `S` detects `u₁` — otherwise the
interpolant on a `(d + 1)`-subset would extend to all of `S`. -/
theorem detect_of_no_interpolant (v : ι → F) (hv : Function.Injective v) (d : ℕ)
    (u₁ : ι → F) (S : Finset ι) (hScard : d + 2 ≤ S.card)
    (hno : ¬ ∃ q : F[X], q.natDegree ≤ d ∧ ∀ i ∈ S, u₁ i = q.eval (v i)) :
    ∃ T ∈ S.powersetCard (d + 2), ∑ i ∈ T, lagrangeDual v T i * u₁ i ≠ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨T₀, hT₀sub, hT₀card⟩ := Finset.exists_subset_card_eq
    (show d + 1 ≤ S.card by omega)
  set q := Lagrange.interpolate T₀ v u₁ with hqdef
  have hvT₀ : Set.InjOn v T₀ := hv.injOn
  have hqdeg : q.natDegree ≤ d := by
    rcases eq_or_ne q 0 with h | h
    · simp [h]
    · have hdlt := Lagrange.degree_interpolate_lt u₁ hvT₀
      rw [hT₀card] at hdlt
      have := (Polynomial.natDegree_lt_iff_degree_lt h).mpr (by exact_mod_cast hdlt)
      omega
  refine hno ⟨q, hqdeg, fun i hi => ?_⟩
  by_cases hiT₀ : i ∈ T₀
  · exact (Lagrange.eval_interpolate_at_node u₁ hvT₀ hiT₀).symm
  · -- extend by the (d+2)-subset T = insert i T₀ ⊆ S
    set T := insert i T₀ with hTdef
    have hTsub : T ⊆ S := Finset.insert_subset hi hT₀sub
    have hTcard : T.card = d + 2 := by
      rw [hTdef, Finset.card_insert_of_notMem hiT₀, hT₀card]
    have hvT : Set.InjOn v T := hv.injOn
    have hu : ∑ j ∈ T, lagrangeDual v T j * u₁ j = 0 :=
      hcon T (Finset.mem_powersetCard.mpr ⟨hTsub, hTcard⟩)
    have hq0 : ∑ j ∈ T, lagrangeDual v T j * q.eval (v j) = 0 :=
      lagrangeDual_sum_eq_zero v hvT q (by omega)
    have hdiff : ∑ j ∈ T, lagrangeDual v T j * (u₁ j - q.eval (v j)) = 0 := by
      have hsplit : ∑ j ∈ T, lagrangeDual v T j * (u₁ j - q.eval (v j))
          = (∑ j ∈ T, lagrangeDual v T j * u₁ j)
            - ∑ j ∈ T, lagrangeDual v T j * q.eval (v j) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hsplit, hu, hq0, sub_zero]
    have hsingle : lagrangeDual v T i * (u₁ i - q.eval (v i)) = 0 := by
      have hrest : ∑ j ∈ T₀, lagrangeDual v T j * (u₁ j - q.eval (v j)) = 0 := by
        refine Finset.sum_eq_zero fun j hj => ?_
        rw [hqdef, Lagrange.eval_interpolate_at_node u₁ hvT₀ hj, sub_self, mul_zero]
      rw [hTdef] at hdiff
      rw [Finset.sum_insert hiT₀, hrest, add_zero] at hdiff
      rw [hTdef]
      exact hdiff
    have hlne : lagrangeDual v T i ≠ 0 :=
      lagrangeDual_ne_zero v hvT (hTdef ▸ Finset.mem_insert_self i T₀)
    have hzero := (mul_eq_zero.mp hsingle).resolve_left hlne
    exact sub_eq_zero.mp hzero

open Classical in
/-- **THE RATIO-CENSUS INCIDENCE BOUND FOR EVALUATION CODES** (the headline composition):
for any degree-`≤ d` polynomial-evaluation code on an injective domain, any radius `δ`
whose witness size exceeds `d + 1`, and any `FarFromCode` direction `u₁`:

  `#{γ : mcaEvent} ≤ C(n, d + 2)` — `q`-INDEPENDENT.

This is `KKH26DimOnePin.dimOne_badScalars_card_mul_four_le` generalized from the
dimension-one code to every evaluation degree, through the ratio census at the GRS dual
syndromes.  Composes with `epsMCA_ge_far_incidence` (same filter) for the matching lower
face.  Honest scope: only the trivial detecting density `θ = 1` is used; at production
dimension `C(n, d+2)` is exponentially vacuous — the `θ`-refinement is face 4. -/
theorem rs_badScalars_card_le_choose
    [Fintype ι] [Nonempty ι]
    (v : ι → F) (hv : Function.Injective v) (d : ℕ)
    (Cd : Set (ι → F))
    (hCsub : ∀ c ∈ Cd, ∃ q : F[X], q.natDegree ≤ d ∧ ∀ i, c i = q.eval (v i))
    (hCsup : ∀ q : F[X], q.natDegree ≤ d → (fun i => q.eval (v i)) ∈ Cd)
    (δ : ℝ≥0) (u₀ u₁ : ι → F)
    (hwitness : ((d + 1 : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card ι : ℝ≥0))
    (hfar : FarCosetExplosion.FarFromCode Cd δ u₁) :
    (univ.filter fun γ : F =>
        mcaEvent (F := F) (A := F) Cd δ u₀ u₁ γ).card
      ≤ (Fintype.card ι).choose (d + 2) := by
  have hdetect : ∀ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι →
      1 ≤ ((S.powersetCard (d + 2)).filter
        fun T => ∑ i ∈ T, lagrangeDual v T i * u₁ i ≠ 0).card := by
    intro S hS
    have hScard : d + 2 ≤ S.card := by
      have hlt : ((d + 1 : ℕ) : ℝ≥0) < (S.card : ℝ≥0) := lt_of_lt_of_le hwitness hS
      have hnat : d + 1 < S.card := by exact_mod_cast hlt
      omega
    have hno : ¬ ∃ q : F[X], q.natDegree ≤ d ∧ ∀ i ∈ S, u₁ i = q.eval (v i) := by
      rintro ⟨q, hq, hagree⟩
      obtain ⟨i, hi, hne⟩ := hfar (fun i => q.eval (v i)) (hCsup q hq) S hS
      exact hne (hagree i hi).symm
    obtain ⟨T, hTmem, hTne⟩ := detect_of_no_interpolant v hv d u₁ S hScard hno
    exact Finset.card_pos.mpr ⟨T, Finset.mem_filter.mpr ⟨hTmem, hTne⟩⟩
  have h := badScalars_card_mul_le_choose Cd δ u₀ u₁ (d + 2) 1
    (lagrangeDual v) hfar (lagrangeDual_kills v hv d Cd hCsub) hdetect
  simpa using h

end Lagrange

end ProximityGap.RatioCensusIdentity

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.RatioCensusIdentity.degenerate_gamma_unique
#print axioms ProximityGap.RatioCensusIdentity.pencil_lineBall_card_le_one
#print axioms ProximityGap.RatioCensusIdentity.explainable_lineRatioHits_ge
#print axioms ProximityGap.RatioCensusIdentity.explainable_card_mul_le_census
#print axioms ProximityGap.RatioCensusIdentity.dualSyndrome_supp_card_le
#print axioms ProximityGap.RatioCensusIdentity.badScalars_card_mul_le_choose
#print axioms ProximityGap.RatioCensusIdentity.lagrangeDual_ne_zero
#print axioms ProximityGap.RatioCensusIdentity.lagrangeDual_sum_eq_zero
#print axioms ProximityGap.RatioCensusIdentity.lagrangeDual_kills
#print axioms ProximityGap.RatioCensusIdentity.detect_of_no_interpolant
#print axioms ProximityGap.RatioCensusIdentity.rs_badScalars_card_le_choose
