/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Complex.Norm
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# SW1 lane HD (2026-09-05): Hasse–Davenport coset relations on the Jacobi ladder —
  the k = 2 relation PROVED from Mathlib, and the exact reason the HD interface is a gauge

## Target

Dossier v3 §33 live route (ii) / doctrine-v2 §5 queued swing: Hasse–Davenport (HD) exact
angle relations along subgroup cosets of `ℤ/m` on the ladder object
`J_j = jacobiCoeff χ lam j = J(λ_j, χ)` (`_R19JacobiFourierExpansion.lean`), whose `r = 3`
rung `TripleConvEnergyBound` (`_R23TripleConvEnergyInput.lean`) is the calibrated open core.

The route was already run on 2026-07-10 (`_R297HasseDavenportCosetTriple.lean`,
`_R298MixedDepthCorrelation.lean`, DISPROOF_LOG `466-r3-hasse-davenport-coset-triple-collapse`,
`466-HD1` … `466-HD7-HD8`): the coset collapse `(I3)` was probe-verified and consumed through a
NAMED hypothesis `HDCosetTripleCollapse`, and the identity web was closed as a no-go by a
floating-point rank certificate that lived in a now-deleted `/tmp` directory.  HD3(ii) queued —
and nobody did — "check Mathlib's `JacobiSum`/`gaussSum` API for the duplication formula".

## What this file lands (Mathlib-only, axiom-clean)

1. `jacobiSum_quadChar_eq` — the Jacobi-level duplication identity
   `J(χ, ρ) = χ(4) · J(χ, χ)` (`ρ` = quadratic character, `χ ≠ 1`, odd characteristic).
   Proof: `4·x(1−x) = 1 − (1−2x)²`, the reindexing `y = 1 − 2x`, the square-fibre
   interchange `∑_y f(y²) = ∑_s (1 + ρ(s)) f(s)`, and `∑ χ = 0`.
2. `hasseDavenport_duplication` — the **k = 2 Hasse–Davenport product relation** for Gauss
   sums over `ℂ`: `χ(4) · g(χ) · g(χρ) = g(χ²) · g(ρ)`.  To our knowledge the first
   machine-checked instance of the HD product formula (classical form
   `∏_{a<k} g(χρ^a) = χ(k)^{−k} · g(χ^k) · ∏_{0<a<k} g(ρ^a)` at `k = 2`).
3. `ladder_coset_pair` — **the (I2) coset identity of the ladder, PROVED**
   (it was probe-only in the 2026-07-10 arc):
   `J(λ,χ) · J(λρ,χ) = χ(4) · J(χ,χ) · J(λ², χ²)`.  With `λ = λ_j` and `λρ = λ_{j+m/2}`
   (for even `m`, `λ_{m/2}` is the quadratic character) this is
   `J_j · J_{j+m/2} = κ₂ · J₂(2j)`, `κ₂ = χ(2)² · J(χ,χ)`, `J₂` the ladder of `χ²`.
4. The **interface no-go** for the `_R297` hypothesis package (definitions restated locally,
   nonzero-index convention of `_R21/_R22/_R23`):
   * `hdCosetTripleCollapse_gauge` — the package is invariant under every phase change
     `J ↦ φ·J` with unit coset products (an `(m − m/3)`-dimensional torus of gauges);
   * `not_tripleConvEnergyBound_of_hd_interface` — for every `m ≥ 3`, `q ≥ 1` and every
     `C` with `C·m² < (m−1)²(m−2)²`, the collapse together with ALL classical modulus data
     (`‖J_j‖ = √q`, `‖J₃‖ ≤ √q`, `‖κ‖ = q`) is satisfied by a sequence violating
     `TripleConvEnergyBound J q C`.  Hence no `O(1)` (indeed no `o(m²)`) rung constant follows
     from the HD coset interface: on that interface HD is a gauge, exactly.
5. `pinned_forms_lower_bound` — the dimension-counting half of the HD8 "dimension law"
   (`pinned ≥ max(0, dim θ − nullity)`), as trivial linear algebra.  The other half (maximal
   rank of the projection) is FALSE in general: the probe finds `3` pinned ladder-angle forms
   at `N = 240` (`p = 241`, `n = 8`, `m = 30`), where HD8's formula predicts `0`.

## Honest classification

Items 1–3: exact pins (unconditional identities), the first HD relation in the tree with a
proof.  Item 4: refutation-no-go with an explicit countermodel (interface level).  Item 5:
unconditional component (trivial).  None of this closes `TripleConvEnergyBound`; the coset
identities constrain `O(m)`-many of the `~m²` decompositions per output index (probe: the
`k = 3` stratum carries `≤ 15 %` and `→ 0` of the rung energy, the `k = 2` pair stratum
`≤ 30 %` at prize-shaped cells beyond `m = 6`).  CORE OPEN / ON-BGK.

Probe: `scripts/probes/sw1_hd_coset_relations.py`.  KB: `docs/kb/deltastar-sw1-hd-2026-09-05.md`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset

namespace ArkLib.ProximityGap.Frontier.SW1HD

/-! ## 1. The quadratic character over `ℂ` and the square-fibre interchange -/

section QuadChar

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The quadratic character of `F`, with values in `ℂ`. -/
noncomputable def quadCharC (F : Type*) [Field F] [Fintype F] [DecidableEq F] : MulChar F ℂ :=
  (quadraticChar F).ringHomComp (Int.castRingHom ℂ)

theorem quadCharC_apply (a : F) : quadCharC F a = ((quadraticChar F a : ℤ) : ℂ) := rfl

/-- The complex quadratic character is nontrivial in odd characteristic. -/
theorem quadCharC_ne_one (hF : ringChar F ≠ 2) : quadCharC F ≠ 1 := by
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one hF
  intro h
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  have h1 : quadCharC F a = 1 := by
    rw [h]
    exact MulChar.one_apply (isUnit_iff_ne_zero.mpr ha0)
  rw [quadCharC_apply, ha] at h1
  norm_num at h1

/-- **Square-fibre interchange** over `ℂ`: `∑_t f(t²) = ∑_s (1 + ρ(s)) f(s)`. -/
theorem sum_comp_sq (hF : ringChar F ≠ 2) (f : F → ℂ) :
    ∑ t : F, f (t ^ 2) = ∑ s : F, (1 + quadCharC F s) * f s := by
  classical
  calc ∑ t : F, f (t ^ 2)
      = ∑ s : F, ∑ t ∈ univ.filter (fun t : F => t ^ 2 = s), f (t ^ 2) :=
        (Finset.sum_fiberwise univ (fun t : F => t ^ 2) (fun t => f (t ^ 2))).symm
    _ = ∑ s : F, ((univ.filter (fun t : F => t ^ 2 = s)).card : ℂ) * f s := by
        refine sum_congr rfl fun s _ => ?_
        rw [sum_congr rfl fun t ht => by rw [(mem_filter.mp ht).2], sum_const, nsmul_eq_mul]
    _ = ∑ s : F, (1 + quadCharC F s) * f s := by
        refine sum_congr rfl fun s _ => ?_
        have h := quadraticChar_card_sqrts hF s
        have hset : {x : F | x ^ 2 = s}.toFinset = univ.filter (fun t : F => t ^ 2 = s) := by
          ext x; simp
        rw [hset] at h
        have h' : ((univ.filter (fun t : F => t ^ 2 = s)).card : ℂ) = 1 + quadCharC F s := by
          rw [quadCharC_apply]
          have hc := congrArg (fun z : ℤ => (z : ℂ)) h
          push_cast at hc
          linear_combination hc
        rw [h']

end QuadChar

/-! ## 2. Duplication: the Jacobi-level identity and the k = 2 Hasse–Davenport relation -/

section Duplication

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Jacobi-level duplication**: `J(χ, ρ) = χ(4) · J(χ, χ)` for nontrivial `χ`. -/
theorem jacobiSum_quadChar_eq (hF : ringChar F ≠ 2) {χ : MulChar F ℂ} (hχ : χ ≠ 1) :
    jacobiSum χ (quadCharC F) = χ 4 * jacobiSum χ χ := by
  classical
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  -- step 1: `χ(4)·J(χ,χ) = ∑_x χ(1 − (1 − 2x)²)`
  have step1 : χ 4 * jacobiSum χ χ = ∑ x : F, χ (1 - (1 - 2 * x) ^ 2) := by
    unfold jacobiSum
    rw [mul_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [← map_mul, ← map_mul]
    congr 1
    ring
  -- step 2: reindex `y = 1 − 2x`
  have step2 : ∑ x : F, χ (1 - (1 - 2 * x) ^ 2) = ∑ y : F, χ (1 - y ^ 2) := by
    refine Fintype.sum_bijective (fun x : F => 1 - 2 * x)
      ⟨sub_right_injective.comp (mul_right_injective₀ h2), ?_⟩ _ _ (fun x => rfl)
    · intro y
      refine ⟨(1 - y) * 2⁻¹, ?_⟩
      show 1 - 2 * ((1 - y) * 2⁻¹) = y
      rw [mul_comm (1 - y), ← mul_assoc, mul_inv_cancel₀ h2, one_mul]
      ring
  -- step 3: square-fibre interchange
  have step3 : ∑ y : F, χ (1 - y ^ 2) = ∑ s : F, (1 + quadCharC F s) * χ (1 - s) :=
    sum_comp_sq hF (fun s => χ (1 - s))
  -- step 4: split, and `∑_s χ(1 − s) = 0`
  have step4 : ∑ s : F, (1 + quadCharC F s) * χ (1 - s)
      = ∑ s : F, χ (1 - s) + ∑ s : F, quadCharC F s * χ (1 - s) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun s _ => ?_
    ring
  have step5 : ∑ s : F, χ (1 - s) = 0 := by
    have hre : ∑ s : F, χ (1 - s) = ∑ s : F, χ s := by
      refine Fintype.sum_bijective (fun s : F => 1 - s) ⟨sub_right_injective, ?_⟩ _ _
        (fun s => rfl)
      intro y
      exact ⟨1 - y, by show 1 - (1 - y) = y; ring⟩
    rw [hre]
    exact MulChar.sum_eq_zero_of_ne_one hχ
  rw [jacobiSum_comm, step1, step2, step3, step4, step5, zero_add]
  rfl

/-- **Hasse–Davenport duplication (the `k = 2` product relation)** over `ℂ`:
`χ(4) · g(χ) · g(χρ) = g(χ²) · g(ρ)` for `χ`, `χ²`, `χρ` nontrivial and `ψ` primitive.
Classical form: `∏_{a<2} g(χρ^a) = χ(2)^{−2} · g(χ²) · g(ρ)`. -/
theorem hasseDavenport_duplication (hF : ringChar F ≠ 2) {χ : MulChar F ℂ} (hχ : χ ≠ 1)
    (hχ2 : χ * χ ≠ 1) (hχρ : χ * quadCharC F ≠ 1) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    χ 4 * gaussSum χ ψ * gaussSum (χ * quadCharC F) ψ
      = gaussSum (χ * χ) ψ * gaussSum (quadCharC F) ψ := by
  have hcard : (Fintype.card F : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hg : gaussSum χ ψ ≠ 0 := gaussSum_ne_zero_of_nontrivial hcard hχ hψ
  have hJ := jacobiSum_quadChar_eq hF hχ
  have E1 := jacobiSum_mul_nontrivial hχρ ψ
  have E2 := jacobiSum_mul_nontrivial hχ2 ψ
  have hJne : jacobiSum χ χ ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at E2
    exact mul_ne_zero hg hg E2.symm
  apply mul_right_cancel₀ hJne
  linear_combination (-(gaussSum χ ψ * gaussSum (χ * quadCharC F) ψ)) * hJ
    + gaussSum χ ψ * E1 - gaussSum (quadCharC F) ψ * E2

/-- Nonvanishing of a multiplicative character at `4` in odd characteristic. -/
theorem mulChar_four_ne_zero (hF : ringChar F ≠ 2) (χ : MulChar F ℂ) : χ 4 ≠ 0 := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have h4 : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  have : χ 4 * χ 4⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ h4, map_one]
  exact left_ne_zero_of_mul_eq_one this

/-- **(I2): the `k = 2` Hasse–Davenport coset identity on the ladder, in `MulChar` form.**
`J(λ,χ) · J(λρ,χ) = χ(4) · J(χ,χ) · J(λ², χ²)`.  Taking `λ = λ_j` (so `λρ = λ_{j+m/2}` and
`λ² = λ_{2j}` for the dual family of an even-index subgroup) this is exactly
`J_j · J_{j+m/2} = χ(2)² · J(χ,χ) · J₂(2j)`, the identity recorded probe-only in the
2026-07-10 arc.  Nondegeneracy hypotheses are the classical ones (every Gauss sum that
appears is that of a nontrivial character). -/
theorem ladder_coset_pair (hF : ringChar F ≠ 2) {lam χ : MulChar F ℂ}
    (hlam : lam ≠ 1) (hlam2 : lam * lam ≠ 1) (hlamρ : lam * quadCharC F ≠ 1)
    (hχ : χ ≠ 1) (hχ2 : χ * χ ≠ 1)
    (hlamχ : lam * χ ≠ 1) (hlamχ2 : (lam * χ) * (lam * χ) ≠ 1)
    (hlamρχ : lam * quadCharC F * χ ≠ 1) :
    jacobiSum lam χ * jacobiSum (lam * quadCharC F) χ
      = χ 4 * jacobiSum χ χ * jacobiSum (lam * lam) (χ * χ) := by
  classical
  set ψ : AddChar F ℂ := AddChar.FiniteField.primitiveChar_to_Complex F
  have hψ : ψ.IsPrimitive := AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive F
  have hcard : (Fintype.card F : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hρ : quadCharC F ≠ 1 := quadCharC_ne_one hF
  have hlamχρ : lam * χ * quadCharC F ≠ 1 := by rwa [mul_right_comm]
  have hll : (lam * lam) * (χ * χ) ≠ 1 := by
    rwa [mul_mul_mul_comm] at hlamχ2
  -- the two duplication relations
  have D1 := hasseDavenport_duplication hF hlam hlam2 hlamρ hψ
  have D2 := hasseDavenport_duplication hF hlamχ hlamχ2 hlamχρ hψ
  rw [mul_mul_mul_comm, mul_right_comm lam χ, MulChar.mul_apply] at D2
  -- the four Jacobi–Gauss bridges
  have B1 := jacobiSum_mul_nontrivial hlamχ ψ
  have B2 := jacobiSum_mul_nontrivial hlamρχ ψ
  have B3 := jacobiSum_mul_nontrivial hχ2 ψ
  have B4 := jacobiSum_mul_nontrivial hll ψ
  -- nonvanishing of the denominators
  have hc : gaussSum (lam * χ) ψ ≠ 0 := gaussSum_ne_zero_of_nontrivial hcard hlamχ hψ
  have hd : gaussSum (lam * quadCharC F * χ) ψ ≠ 0 :=
    gaussSum_ne_zero_of_nontrivial hcard hlamρχ hψ
  have hf : gaussSum (χ * χ) ψ ≠ 0 := gaussSum_ne_zero_of_nontrivial hcard hχ2 hψ
  have hh : gaussSum ((lam * lam) * (χ * χ)) ψ ≠ 0 := gaussSum_ne_zero_of_nontrivial hcard hll hψ
  have hr : gaussSum (quadCharC F) ψ ≠ 0 := gaussSum_ne_zero_of_nontrivial hcard hρ hψ
  have hl4 : lam 4 ≠ 0 := mulChar_four_ne_zero hF lam
  have hK : gaussSum (lam * χ) ψ * gaussSum (lam * quadCharC F * χ) ψ * gaussSum (χ * χ) ψ
      * gaussSum ((lam * lam) * (χ * χ)) ψ * gaussSum (quadCharC F) ψ * lam 4 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hc hd) hf) hh) hr) hl4
  apply mul_right_cancel₀ hK
  linear_combination
    (gaussSum (lam * quadCharC F * χ) ψ * jacobiSum (lam * quadCharC F) χ
      * gaussSum (χ * χ) ψ * gaussSum ((lam * lam) * (χ * χ)) ψ
      * gaussSum (quadCharC F) ψ * lam 4) * B1
    + (gaussSum lam ψ * gaussSum χ ψ * gaussSum (χ * χ) ψ
      * gaussSum ((lam * lam) * (χ * χ)) ψ * gaussSum (quadCharC F) ψ * lam 4) * B2
    - (χ 4 * gaussSum (lam * χ) ψ * gaussSum (lam * quadCharC F * χ) ψ
      * gaussSum (quadCharC F) ψ * lam 4 * gaussSum ((lam * lam) * (χ * χ)) ψ
      * jacobiSum (lam * lam) (χ * χ)) * B3
    - (χ 4 * gaussSum (lam * χ) ψ * gaussSum (lam * quadCharC F * χ) ψ
      * gaussSum (quadCharC F) ψ * lam 4 * gaussSum χ ψ * gaussSum χ ψ) * B4
    + (gaussSum χ ψ * gaussSum χ ψ * gaussSum (χ * χ) ψ
      * gaussSum ((lam * lam) * (χ * χ)) ψ * gaussSum (quadCharC F) ψ) * D1
    - (gaussSum χ ψ * gaussSum χ ψ * gaussSum (χ * χ) ψ * gaussSum (lam * lam) ψ
      * gaussSum (quadCharC F) ψ) * D2

end Duplication

/-! ## 3. The `_R297` interface is a gauge: local restatements and the exact no-go -/

section Interface

variable {m : ℕ} [NeZero m]

/-- `selfConv`, restated from `_R21QuarticConvolutionCollapse.lean` (nonzero-index
convention). -/
noncomputable def selfConv (J : ZMod m → ℂ) (c : ZMod m) : ℂ :=
  ∑ j ∈ (Finset.univ \ {(0 : ZMod m)}).filter (fun j => c - j ≠ 0), J j * J (c - j)

/-- `tripleConv`, restated from `_R22SexticConvolutionCollapse.lean`. -/
noncomputable def tripleConv (J : ZMod m → ℂ) (d : ZMod m) : ℂ :=
  ∑ j ∈ Finset.univ \ {(0 : ZMod m)}, selfConv J (d - j) * J j

/-- `TripleConvEnergyBound`, restated from `_R23TripleConvEnergyInput.lean`: the calibrated
`r = 3` open core `∑_d ‖(J∗J∗J)(d)‖² ≤ C·m³·q³`. -/
def TripleConvEnergyBound (J : ZMod m → ℂ) (q : ℕ) (C : ℝ) : Prop :=
  ∑ d : ZMod m, ‖tripleConv J d‖ ^ 2 ≤ C * (m : ℝ) ^ 3 * (q : ℝ) ^ 3

/-- `cosetTripleProduct`, restated from `_R297HasseDavenportCosetTriple.lean`. -/
def cosetTripleProduct (J : ZMod m → ℂ) (u j : ZMod m) : ℂ :=
  J j * J (j + u) * J (j + u + u)

/-- `HDCosetTripleCollapse`, restated from `_R297HasseDavenportCosetTriple.lean`: the named
Hasse–Davenport `(I3)` input `J_j · J_{j+u} · J_{j+2u} = κ · J₃(3j)`. -/
def HDCosetTripleCollapse (J J₃ : ZMod m → ℂ) (u : ZMod m) (κ : ℂ) : Prop :=
  ∀ j : ZMod m, cosetTripleProduct J u j = κ * J₃ (3 * j)

/-- **Gauge invariance.**  The HD coset collapse is invariant under every phase change
`J ↦ φ·J` whose coset products are `1`.  (These `φ` form a torus of dimension `m − m/3`
inside the unit-modulus sequences: the interface sees only coset products.) -/
theorem hdCosetTripleCollapse_gauge {J J₃ : ZMod m → ℂ} {u : ZMod m} {κ : ℂ}
    (h : HDCosetTripleCollapse J J₃ u κ) (φ : ZMod m → ℂ)
    (hφ : ∀ j, φ j * φ (j + u) * φ (j + u + u) = 1) :
    HDCosetTripleCollapse (fun j => φ j * J j) J₃ u κ := by
  intro j
  have hj := h j
  simp only [cosetTripleProduct] at hj ⊢
  linear_combination (J j * J (j + u) * J (j + u + u)) * hφ j + hj

/-- The constant sequence satisfies the HD coset collapse (with `J₃` constant, `κ = B²`). -/
theorem hdCosetTripleCollapse_const (B : ℂ) (u : ZMod m) :
    HDCosetTripleCollapse (fun _ => B) (fun _ => B) u (B * B) := by
  intro j
  simp only [cosetTripleProduct] <;> ring

theorem selfConv_const (B : ℂ) (c : ZMod m) :
    selfConv (fun _ => B) c
      = (((Finset.univ \ {(0 : ZMod m)}).filter (fun j => c - j ≠ 0)).card : ℂ) * (B * B) := by
  simp only [selfConv, sum_const, nsmul_eq_mul]

/-- Each inner index set of `selfConv` has at least `m − 2` elements. -/
theorem card_filter_ge (c : ZMod m) :
    (m : ℝ) - 2
      ≤ (((Finset.univ \ {(0 : ZMod m)}).filter (fun j => c - j ≠ 0)).card : ℝ) := by
  classical
  have hsub : Finset.univ \ ({0, c} : Finset (ZMod m))
      ⊆ (Finset.univ \ {(0 : ZMod m)}).filter (fun j => c - j ≠ 0) := by
    intro j hj
    simp only [mem_sdiff, mem_univ, mem_insert, mem_singleton, true_and, not_or] at hj
    simp only [mem_filter, mem_sdiff, mem_univ, mem_singleton, true_and]
    exact ⟨hj.1, fun h => hj.2 (sub_eq_zero.mp h).symm⟩
  have h1 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ ({0, c} : Finset (ZMod m)))
  have h2 : ({0, c} : Finset (ZMod m)).card ≤ 2 := Finset.card_le_two
  have h3 := Finset.card_le_card hsub
  rw [Finset.card_univ, ZMod.card] at h1
  have h1' : ((Finset.univ \ ({0, c} : Finset (ZMod m))).card : ℝ)
      + (({0, c} : Finset (ZMod m)).card : ℝ) = m := by exact_mod_cast h1
  have h2' : (({0, c} : Finset (ZMod m)).card : ℝ) ≤ 2 := by exact_mod_cast h2
  have h3' : ((Finset.univ \ ({0, c} : Finset (ZMod m))).card : ℝ)
      ≤ (((Finset.univ \ {(0 : ZMod m)}).filter (fun j => c - j ≠ 0)).card : ℝ) := by
    exact_mod_cast h3
  linarith

theorem card_univ_sdiff_zero : ((Finset.univ \ {(0 : ZMod m)}).card : ℝ) = (m : ℝ) - 1 := by
  classical
  have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ ({0} : Finset (ZMod m)))
  rw [Finset.card_univ, ZMod.card, Finset.card_singleton] at h
  have h' : ((Finset.univ \ {(0 : ZMod m)}).card : ℝ) + 1 = m := by exact_mod_cast h
  linarith

theorem tripleConv_const_eq (b : ℝ) (d : ZMod m) :
    tripleConv (fun _ => (b : ℂ)) d
      = ((∑ j ∈ Finset.univ \ {(0 : ZMod m)},
          ((((Finset.univ \ {(0 : ZMod m)}).filter (fun i => (d - j) - i ≠ 0)).card : ℝ)
            * b ^ 3) : ℝ) : ℂ) := by
  simp only [tripleConv, selfConv_const]
  push_cast
  refine sum_congr rfl fun j _ => ?_
  ring

/-- **No cancellation for the constant sequence**: `‖(J∗J∗J)(d)‖ ≥ (m−1)(m−2)·b³`. -/
theorem norm_tripleConv_const_ge {b : ℝ} (hb : 0 ≤ b) (d : ZMod m) :
    ((m : ℝ) - 1) * (((m : ℝ) - 2) * b ^ 3) ≤ ‖tripleConv (fun _ => (b : ℂ)) d‖ := by
  rw [tripleConv_const_eq]
  have hb3 : 0 ≤ b ^ 3 := pow_nonneg hb 3
  have hS : 0 ≤ ∑ j ∈ Finset.univ \ {(0 : ZMod m)},
      ((((Finset.univ \ {(0 : ZMod m)}).filter (fun i => (d - j) - i ≠ 0)).card : ℝ) * b ^ 3) :=
    sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) hb3
  rw [Complex.norm_of_nonneg hS]
  calc ((m : ℝ) - 1) * (((m : ℝ) - 2) * b ^ 3)
      = ∑ _j ∈ Finset.univ \ {(0 : ZMod m)}, ((m : ℝ) - 2) * b ^ 3 := by
        rw [sum_const, nsmul_eq_mul, card_univ_sdiff_zero]
    _ ≤ _ := sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right (card_filter_ge (d - j)) hb3

/-- **Energy of the constant sequence**: `∑_d ‖(J∗J∗J)(d)‖² ≥ m·((m−1)(m−2))²·b⁶`. -/
theorem tripleConv_energy_const_ge {b : ℝ} (hb : 0 ≤ b) (hm : 2 ≤ m) :
    (m : ℝ) * (((m : ℝ) - 1) * (((m : ℝ) - 2) * b ^ 3)) ^ 2
      ≤ ∑ d : ZMod m, ‖tripleConv (fun _ => (b : ℂ)) d‖ ^ 2 := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hL : 0 ≤ ((m : ℝ) - 1) * (((m : ℝ) - 2) * b ^ 3) :=
    mul_nonneg (by linarith) (mul_nonneg (by linarith) (pow_nonneg hb 3))
  calc (m : ℝ) * (((m : ℝ) - 1) * (((m : ℝ) - 2) * b ^ 3)) ^ 2
      = ∑ _d : ZMod m, (((m : ℝ) - 1) * (((m : ℝ) - 2) * b ^ 3)) ^ 2 := by
        rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul]
    _ ≤ ∑ d : ZMod m, ‖tripleConv (fun _ => (b : ℂ)) d‖ ^ 2 :=
        sum_le_sum fun d _ => pow_le_pow_left₀ hL (norm_tripleConv_const_ge hb d) 2

/-- **Interface no-go (HD is a gauge on the `_R297` interface).**  For every `m ≥ 3`, `q ≥ 1`
and every `C` with `C·m² < (m−1)²(m−2)²`, the HD coset collapse together with ALL the
classical modulus data (`‖J_j‖ = √q`, `‖J₃‖ ≤ √q`, `‖κ‖ = q`) is satisfied by a sequence
that violates `TripleConvEnergyBound J q C`.  No rung constant `C = o(m²)` — a fortiori no
`O(1)` constant — is a consequence of the HD coset interface. -/
theorem not_tripleConvEnergyBound_of_hd_interface (q : ℕ) (hq : 1 ≤ q) (hm : 3 ≤ m)
    (u : ZMod m) {C : ℝ}
    (hC : C * (m : ℝ) ^ 2 < ((m : ℝ) - 1) ^ 2 * ((m : ℝ) - 2) ^ 2) :
    ∃ (J J₃ : ZMod m → ℂ) (κ : ℂ),
      HDCosetTripleCollapse J J₃ u κ ∧ (∀ j, ‖J j‖ = Real.sqrt q) ∧
      (∀ c, ‖J₃ c‖ ≤ Real.sqrt q) ∧ ‖κ‖ = q ∧ ¬ TripleConvEnergyBound J q C := by
  set b : ℝ := Real.sqrt q with hbdef
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hbsq : b ^ 2 = q := Real.sq_sqrt (Nat.cast_nonneg q)
  refine ⟨fun _ => (b : ℂ), fun _ => (b : ℂ), (b : ℂ) * (b : ℂ),
    hdCosetTripleCollapse_const _ _, ?_, ?_, ?_, ?_⟩
  · intro j
    exact Complex.norm_of_nonneg hb0
  · intro c
    exact le_of_eq (Complex.norm_of_nonneg hb0)
  · rw [norm_mul, Complex.norm_of_nonneg hb0, ← sq, hbsq]
  · intro hbound
    unfold TripleConvEnergyBound at hbound
    have hE := tripleConv_energy_const_ge (m := m) hb0 (by omega)
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    have hm' : (3 : ℝ) ≤ m := by exact_mod_cast hm
    have hm0 : (0 : ℝ) < m := by linarith
    have hb6 : b ^ 6 = (q : ℝ) ^ 3 := by
      rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, hbsq]
    have hrew : (m : ℝ) * (((m : ℝ) - 1) * (((m : ℝ) - 2) * b ^ 3)) ^ 2
        = (((m : ℝ) - 1) ^ 2 * ((m : ℝ) - 2) ^ 2) * ((m : ℝ) * (q : ℝ) ^ 3) := by
      rw [← hb6]; ring
    have hmq : 0 < (m : ℝ) * (q : ℝ) ^ 3 := mul_pos hm0 (pow_pos hq' 3)
    have key : C * (m : ℝ) ^ 3 * (q : ℝ) ^ 3
        < (m : ℝ) * (((m : ℝ) - 1) * (((m : ℝ) - 2) * b ^ 3)) ^ 2 := by
      rw [hrew]
      calc C * (m : ℝ) ^ 3 * (q : ℝ) ^ 3
          = (C * (m : ℝ) ^ 2) * ((m : ℝ) * (q : ℝ) ^ 3) := by ring
        _ < (((m : ℝ) - 1) ^ 2 * ((m : ℝ) - 2) ^ 2) * ((m : ℝ) * (q : ℝ) ^ 3) :=
            mul_lt_mul_of_pos_right hC hmq
    linarith

end Interface

/-! ## 4. The dimension-counting half of the HD8 "dimension law" -/

section DimensionLaw

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [FiniteDimensional K V] [FiniteDimensional K W]

/-- **Pinned forms, lower bound.**  If the identity web has null space `N ≤ V` and the ladder
angles are the image of the linear projection `π : V → W`, then the number of independent
linear forms on `W` fixed by the web, `dim W − dim π(N)`, is at least
`dim W − min(dim W, dim N)`.  (Equality — HD8's "law" — is a maximal-rank statement that
fails in general: the probe finds `3 > 0` pinned forms at `N = 240`, `n = 8`, `m = 30`.) -/
theorem pinned_forms_lower_bound (π : V →ₗ[K] W) (N : Submodule K V) :
    Module.finrank K W - min (Module.finrank K W) (Module.finrank K N)
      ≤ Module.finrank K W - Module.finrank K (N.map π) :=
  Nat.sub_le_sub_left (le_min (Submodule.finrank_le _) (Submodule.finrank_map_le π N)) _

end DimensionLaw

end ArkLib.ProximityGap.Frontier.SW1HD

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.SW1HD.quadCharC_ne_one
#print axioms ArkLib.ProximityGap.Frontier.SW1HD.sum_comp_sq
#print axioms ArkLib.ProximityGap.Frontier.SW1HD.jacobiSum_quadChar_eq
#print axioms ArkLib.ProximityGap.Frontier.SW1HD.hasseDavenport_duplication
#print axioms ArkLib.ProximityGap.Frontier.SW1HD.ladder_coset_pair
#print axioms ArkLib.ProximityGap.Frontier.SW1HD.hdCosetTripleCollapse_gauge
#print axioms ArkLib.ProximityGap.Frontier.SW1HD.hdCosetTripleCollapse_const
#print axioms ArkLib.ProximityGap.Frontier.SW1HD.norm_tripleConv_const_ge
#print axioms ArkLib.ProximityGap.Frontier.SW1HD.tripleConv_energy_const_ge
#print axioms ArkLib.ProximityGap.Frontier.SW1HD.not_tripleConvEnergyBound_of_hd_interface
#print axioms ArkLib.ProximityGap.Frontier.SW1HD.pinned_forms_lower_bound
