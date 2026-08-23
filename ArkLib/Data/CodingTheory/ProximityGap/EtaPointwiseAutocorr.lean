/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment

/-!
# The POINTWISE (single-frequency) autocorrelation identity for the subgroup Gauss-sum (#444, #389)

For a multiplicative subgroup `G = μ_n ⊆ F^×` and a single frequency `b`, the squared period
`‖η_b‖²` (a single point of the spectrum, NOT the `∑_b` aggregate that the in-tree
`subgroup_gaussSum_secondMoment` / `SubgroupGaussSumTowerL2` machinery controls) satisfies the
exact **group-shift autocorrelation identity**

> **`‖η_b‖² = ∑_{ζ ∈ G} η_{b·(ζ-1)}`.**

The `ζ = 1` term contributes `η_0 = |G|`; the remaining `|G|-1` terms are periods at the
*frequency-shifted* arguments `b·(ζ-1)`, `ζ ∈ G \ {1}`. This is the analytic-side (Fourier) companion
of the set-side autocorrelation double-counts (`PencilAutocorrSumDoubleCount`,
`PencilAutocorrSubgroupExact`), but at a SINGLE frequency `b` rather than summed over shifts.

**Why thinness-essential (rule 3).** The proof reindexes the defining double sum
`‖η_b‖² = ∑_{x∈G}∑_{y∈G} ψ(b(x-y))` by the substitution `x = ζ·y` with `ζ ∈ G`. This requires `G` to be
**closed under multiplication** (a subgroup): for an unstructured thin set `S`, `ζ·y ∉ S` in general, so
the identity `‖η_b‖² = ∑_{ζ∈S} η_{b(ζ-1)}` is FALSE (probe-confirmed). The identity expresses the worst
period² as a sum of periods at the *difference-set frequencies* `b·(G-1)` — a structural fixed-point form
of the worst-case period that lives entirely on the group structure of `μ_n`.

Probe: `scripts/probes/probe_eta_autocorr_groupshift.py` (exact over ℂ, PROPER thin subgroups only,
`m=(p-1)/n ≥ 2`, never `n=q-1`, incl. Fermat primes `257, 65537`, multiple `b`): max error `2.4e-13`
(float roundoff) across all cases. PASS.

**Honest scope (rule 6).** This is an EXACT identity, NOT a bound. It re-expresses `‖η_b‖²` on the
difference-set frequencies but does NOT bound it: bounding `∑_{ζ≠1} η_{b(ζ-1)}` is exactly the open
BGK/Paley cancellation problem (the shifted periods can interfere constructively). No CORE bound, no
capacity / beyond-Johnson / cliff-at-n/2 claim. CORE `M(μ_n) ≤ C√(n log(q/n))` remains OPEN. The value
is structural: it pins the single-frequency period² to a sum over the difference-set spectrum, the
thinness-essential fixed-point form (INV-B in the #444 dossier), now machine-checked.

Axiom-clean. Issues #444, #389.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.EtaPointwiseAutocorr

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] in
/-- **Inner reindex.** For a subgroup `G` (closed under multiplication, `0 ∉ G`), fix `y ∈ G` and
frequency `b`. Reindexing `x = ζ·y` (a bijection of `G` since `G·y⁻¹ = G`) gives
`∑_{x∈G} ψ(b·(x - y)) = ∑_{ζ∈G} ψ((b·(ζ-1))·y)`. -/
theorem inner_reindex {ψ : AddChar F ℂ} {G : Finset F}
    (hbij : ∀ u ∈ G, G.image (fun z => u * z) = G) (h0 : (0 : F) ∉ G)
    (b : F) {y : F} (hy : y ∈ G) :
    (∑ x ∈ G, ψ (b * (x - y))) = ∑ ζ ∈ G, ψ ((b * (ζ - 1)) * y) := by
  classical
  have hyne : y ≠ 0 := fun h => h0 (h ▸ hy)
  -- Right-multiplication by `y` is a bijection of `G`: `G.image (· * y) = G`. Derived from the given
  -- left-multiplication closure `hbij y hy : G.image (y * ·) = G` by commutativity of the field.
  have himgy : G.image (fun ζ => ζ * y) = G := by
    have hL := hbij y hy
    have hcomm : G.image (fun ζ => ζ * y) = G.image (fun z => y * z) := by
      apply Finset.image_congr; intro z _; exact mul_comm z y
    rw [hcomm, hL]
  calc (∑ x ∈ G, ψ (b * (x - y)))
      = ∑ ζ ∈ G.image (fun ζ => ζ * y), ψ (b * (ζ - y)) := by rw [himgy]
    _ = ∑ ζ ∈ G, ψ (b * (ζ * y - y)) := by
        rw [Finset.sum_image]
        intro a _ c _ h; exact mul_right_cancel₀ hyne h
    _ = ∑ ζ ∈ G, ψ ((b * (ζ - 1)) * y) := by
        refine Finset.sum_congr rfl (fun ζ _ => ?_); congr 1; ring

/-- **THE POINTWISE AUTOCORRELATION IDENTITY (headline).** For a multiplicative subgroup `G` (closure
bijection `hbij`, `0 ∉ G`) and any additive character `ψ`, the squared period at a single
frequency `b` equals the sum of periods at the difference-set frequencies `b·(ζ-1)`:

> `‖η_b‖² = ∑_{ζ ∈ G} η_{b·(ζ-1)}`.

The right side is genuinely complex-valued in general; the identity asserts its sum equals the real
`‖η_b‖²`. (The `ζ = 1` term is `η_0 = |G|`.) Thinness-essential: the reindex `x = ζy` needs `G·y⁻¹=G`. -/
theorem eta_normSq_eq_sum_groupShift {ψ : AddChar F ℂ} {G : Finset F}
    (hbij : ∀ u ∈ G, G.image (fun z => u * z) = G) (h0 : (0 : F) ∉ G) (b : F) :
    ((‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) = ∑ ζ ∈ G, eta ψ G (b * (ζ - 1)) := by
  classical
  have hchar : (0 : ℕ) < ringChar F := by
    haveI := ringChar.charP F
    exact Nat.pos_of_ne_zero (CharP.char_ne_zero_of_finite F (ringChar F))
  have hconj : ∀ a : F, (starRingEnd ℂ) (ψ a) = ψ (-a) := by
    intro a; rw [AddChar.starComp_apply hchar, AddChar.inv_apply]
  -- Expand ‖η_b‖² = η_b · conj η_b into the double sum ∑_{x,y∈G} ψ(b(x-y)).
  have hexpand : ((‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) = ∑ y ∈ G, ∑ x ∈ G, ψ (b * (x - y)) := by
    have hmc : eta ψ G b * (starRingEnd ℂ) (eta ψ G b) = ((‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) := by
      rw [RCLike.mul_conj]; norm_cast
    have hconjeta : (starRingEnd ℂ) (eta ψ G b) = ∑ y ∈ G, ψ (-(b * y)) := by
      rw [eta, map_sum]; exact Finset.sum_congr rfl (fun y _ => hconj (b * y))
    have hL : eta ψ G b = ∑ x ∈ G, ψ (b * x) := rfl
    rw [← hmc, hconjeta, hL]
    rw [Finset.sum_mul_sum]
    -- ∑_x ∑_y ψ(b x)·ψ(-(b y)) = ∑_x ∑_y ψ(b(x-y)); then swap to ∑_y ∑_x.
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [← AddChar.map_add_eq_mul]
    congr 1; ring
  rw [hexpand]
  -- Apply the inner reindex for each y, then swap and recognise η.
  calc (∑ y ∈ G, ∑ x ∈ G, ψ (b * (x - y)))
      = ∑ y ∈ G, ∑ ζ ∈ G, ψ ((b * (ζ - 1)) * y) := by
        refine Finset.sum_congr rfl (fun y hy => inner_reindex hbij h0 b hy)
    _ = ∑ ζ ∈ G, ∑ y ∈ G, ψ ((b * (ζ - 1)) * y) := Finset.sum_comm
    _ = ∑ ζ ∈ G, eta ψ G (b * (ζ - 1)) := rfl

#print axioms ArkLib.ProximityGap.EtaPointwiseAutocorr.eta_normSq_eq_sum_groupShift

set_option linter.unusedFintypeInType false in
/-- **Split off the trivial shift.** Peeling the `ζ = 1` term (`η_0 = |G|`) gives the fixed-point
form `‖η_b‖² = |G| + ∑_{ζ ∈ G \ {1}} η_{b(ζ-1)}`: the worst period² is `|G|` plus the periods at
the NONTRIVIAL difference-set frequencies. This is INV-B (#444 dossier), the thinness-essential
fixed-point identity, now exact in Lean. Requires `1 ∈ G` (true for any subgroup). The `[Fintype F]`
instance is consumed transitively via `eta_normSq_eq_sum_groupShift`. -/
theorem eta_normSq_eq_card_add_nontrivial {ψ : AddChar F ℂ} {G : Finset F}
    (hbij : ∀ u ∈ G, G.image (fun z => u * z) = G) (h0 : (0 : F) ∉ G) (h1 : (1 : F) ∈ G) (b : F) :
    ((‖eta ψ G b‖ ^ 2 : ℝ) : ℂ)
      = (G.card : ℂ) + ∑ ζ ∈ G.erase 1, eta ψ G (b * (ζ - 1)) := by
  classical
  rw [eta_normSq_eq_sum_groupShift hbij h0 b]
  rw [← Finset.add_sum_erase G (fun ζ => eta ψ G (b * (ζ - 1))) h1]
  congr 1
  -- the ζ=1 term: η_{b·0} = η_0 = |G|.
  have : b * ((1 : F) - 1) = 0 := by ring
  rw [this, eta]
  simp [AddChar.map_zero_eq_one]

set_option linter.unusedFintypeInType false in
/-- **Defect form of the pointwise autocorrelation identity.** The nontrivial difference-set
shift sum is exactly the real defect between the squared period and the subgroup size:

> `∑_{ζ ∈ G \ {1}} η_{b(ζ-1)} = ‖η_b‖² - |G|`.

This is the named consumer form of the pointwise identity: all open cancellation content is now
localized in one explicit defect term. It is NOT a bound; bounding this defect uniformly is the
BGK/Paley wall. -/
theorem eta_nontrivial_shiftSum_eq_normSq_sub_card {ψ : AddChar F ℂ} {G : Finset F}
    (hbij : ∀ u ∈ G, G.image (fun z => u * z) = G) (h0 : (0 : F) ∉ G) (h1 : (1 : F) ∈ G)
    (b : F) :
    (∑ ζ ∈ G.erase 1, eta ψ G (b * (ζ - 1)))
      = (((‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) - (G.card : ℂ)) := by
  have h := eta_normSq_eq_card_add_nontrivial (ψ := ψ) hbij h0 h1 b
  rw [h]
  ring

#print axioms ArkLib.ProximityGap.EtaPointwiseAutocorr.eta_normSq_eq_card_add_nontrivial
#print axioms ArkLib.ProximityGap.EtaPointwiseAutocorr.eta_nontrivial_shiftSum_eq_normSq_sub_card

end ArkLib.ProximityGap.EtaPointwiseAutocorr
