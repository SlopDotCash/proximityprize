/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# The Gauss-period coset reduction: `B = max` over EXACTLY `(q−1)/n` periods (Issue #407)

This file supplies the small but load-bearing **structural** fact behind the empirically-exact
worst-case incomplete-subgroup-sum law

  `B(μ_n) := max_{b≠0} ‖η_b‖ = (1+o(1))·√(n · log₂((q−1)/n))`,   `η_b = ∑_{y∈μ_n} ψ(b·y)`,

namely the reason the logarithm is `log((q−1)/n)` and **not** `log q`: the frequency function
`b ↦ η_b` is **constant on multiplicative cosets** `b·μ_n`, so it takes at most `(q−1)/n` distinct
nonzero-frequency values — these are precisely the **Gauss periods** of the order-`n` subgroup
(equivalently the eigenvalues of the generalized Paley graph `Cay(F_q, μ_n)`). The worst-case `B` is
therefore a maximum over `m := (q−1)/n` near-Gaussian (variance-`n`) values, whose extreme value is
`√(n·log m) = √(n·log((q−1)/n))`.

This was independently confirmed numerically (`scripts/probes/probe_moment_growth_law_407.py`,
`/tmp/probe_coset.py`): `η` takes its values with multiplicity an exact multiple of `n` (= the coset
size), and `B/√(n·log₂((q−1)/n)) → 1` across `n = 8..128`.

## What is proven here (axiom-clean, elementary)

Coset-invariance of `η` already exists in-tree as `SubgroupGaussSumCosetInv.eta_smul_invariant`
(bidirectional-permutation hypotheses), whose docstring *states* — but does **not prove** — the
"`(q−1)/|G|` distinct values" count. **The new contribution of this file is that count, proven**
(`eta_image_card_mul_le`), together with a minimal-hypothesis re-proof of coset-invariance used to
get it:

- `eta_mul_of_image_eq` — if multiplying the frequency by a unit `x` permutes the index set `G`
  (`x·G = G`), then `η_{b·x} = η_b`. Pure reindexing (`Finset.sum_image`).
- `image_mul_self_of_mem` — for a multiplicatively-closed `0 ∉ G` index set (a finite multiplicative
  subgroup as a `Finset`), every `x ∈ G` satisfies `x·G = G`.
- `eta_mul_invariant` — the combination: `x ∈ G ⟹ η_{b·x} = η_b` (minimal hypotheses: closure + `0∉G`).
- `eta_constant_on_mulCoset` — `η` is constant on each multiplicative coset `{b·x : x ∈ G}`.
- **`eta_image_card_mul_le`** — **the formalized count**: `#{distinct values of η over F^×}·|G| ≤ q−1`,
  hence `B = max_{b≠0}‖η_b‖` is a max over at most `(q−1)/|G| = (p−1)/n` values — the **Gauss periods**.

This count is *exactly* the structural input that fixes the `log((q−1)/n)` scale of the open law (the
residual being the growing-`n` distribution of those periods = the Paley-graph / Kowalski–Untrau open
problem; see `CharSumMomentDeepWall.lean`, `GeneralizedPaleyRamanujan.lean`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #407.
- [KU23]  Kowalski, Untrau. *Ultra-short sums of trace functions*. arXiv:2302.13670.
- [KU25]  Kowalski, Untrau. *Wasserstein metrics and quantitative equidistribution of exponential
  sums over finite fields*. arXiv:2505.22059.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)

namespace ArkLib.ProximityGap.GaussPeriodCosetReduction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Reindexing form.** If multiplication by `x ≠ 0` permutes the index set `G` (`x·G = G` as
`Finset`s), then the subgroup sum is invariant under scaling the frequency by `x`:
`η_{b·x} = η_b`. Proof: `ψ((b·x)·y) = ψ(b·(x·y))`, reindex `z = x·y` over `x·G = G`. -/
theorem eta_mul_of_image_eq (ψ : AddChar F ℂ) (G : Finset F) (b x : F) (hx : x ≠ 0)
    (hxG : G.image (fun y => x * y) = G) :
    eta ψ G (b * x) = eta ψ G b := by
  unfold eta
  conv_rhs => rw [← hxG]
  rw [Finset.sum_image (fun a _ c _ h => mul_left_cancel₀ hx h)]
  exact Finset.sum_congr rfl (fun y _ => by rw [mul_assoc])

/-- **A finite multiplicative subgroup absorbs its own elements: `x·G = G` for `x ∈ G`.** Needs only
that `G` is closed under multiplication and avoids `0` (a finite sub-monoid of `Fˣ` is a subgroup, so
this is the subgroup-permutation property). `x·G ⊆ G` by closure; equality by injectivity of `x·` on
the finite set (`x ≠ 0`). -/
theorem image_mul_self_of_mem (G : Finset F) {x : F} (hxG : x ∈ G)
    (hmul : ∀ a ∈ G, ∀ c ∈ G, a * c ∈ G) (h0 : (0 : F) ∉ G) :
    G.image (fun y => x * y) = G := by
  have hx : x ≠ 0 := fun h => h0 (h ▸ hxG)
  have hsub : G.image (fun y => x * y) ⊆ G := by
    intro z hz
    simp only [Finset.mem_image] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact hmul x hxG y hy
  have hcard : G.card ≤ (G.image (fun y => x * y)).card :=
    le_of_eq (Finset.card_image_of_injOn
      (fun a _ c _ h => mul_left_cancel₀ hx h)).symm
  exact Finset.eq_of_subset_of_card_le hsub hcard

/-- **The coset-invariance theorem.** For a finite multiplicative subgroup `G` (closed, `0 ∉ G`) and
`x ∈ G`, the subgroup Gauss sum is invariant under scaling the frequency by `x`: `η_{b·x} = η_b`.
Hence `b ↦ η_b` factors through the quotient `Fˣ/G`, taking at most `[Fˣ : G] = (q−1)/|G|` distinct
nonzero-frequency values — the **Gauss periods**. This is the structural reason the worst-case law
`B ≈ √(n·log m)` carries `m = (q−1)/n`, i.e. `log((q−1)/n)`, not `log q`. -/
theorem eta_mul_invariant (ψ : AddChar F ℂ) (G : Finset F) (b : F) {x : F} (hxG : x ∈ G)
    (hmul : ∀ a ∈ G, ∀ c ∈ G, a * c ∈ G) (h0 : (0 : F) ∉ G) :
    eta ψ G (b * x) = eta ψ G b := by
  have hx : x ≠ 0 := fun h => h0 (h ▸ hxG)
  exact eta_mul_of_image_eq ψ G b x hx (image_mul_self_of_mem G hxG hmul h0)

/-- **`η` is constant on each multiplicative coset `b·G`.** Every coset element `b·x` (`x ∈ G`) gives
the same Gauss period as the base `η_b`. The number of distinct values of `η_·` over `Fˣ` is thus at
most the number of cosets `[Fˣ : G]`. -/
theorem eta_constant_on_mulCoset (ψ : AddChar F ℂ) (G : Finset F) (b : F)
    (hmul : ∀ a ∈ G, ∀ c ∈ G, a * c ∈ G) (h0 : (0 : F) ∉ G) :
    ∀ x ∈ G, eta ψ G (b * x) = eta ψ G b := by
  intro x hxG
  exact eta_mul_invariant ψ G b hxG hmul h0

/-- **The period count, rigorously: `#{distinct period values}·|G| ≤ q−1`.** Hence the worst-case
incomplete character sum `B = max_{b≠0}‖η_b‖` is a maximum over at most `(q−1)/|G| = (p−1)/n` distinct
values — the **Gauss periods** of the subgroup. Proof: each fiber of `b ↦ η_b` over the nonzero
frequencies is closed under multiplication by `G` (coset-invariance), so it contains the whole coset
`b·G` (size `|G|`, as `g ↦ b·g` is injective for `b ≠ 0`); summing the fiber sizes (which partition
the `q−1` nonzero frequencies) gives `#values·|G| ≤ Σ fiberSize = q−1`. This is the formal content
behind "the `m=(p−1)/n` Gauss periods" used across the L^∞/Paley frontier. -/
theorem eta_image_card_mul_le (ψ : AddChar F ℂ) (G : Finset F)
    (hmul : ∀ a ∈ G, ∀ c ∈ G, a * c ∈ G) (h0 : (0 : F) ∉ G) :
    ((Finset.univ.filter (fun b : F => b ≠ 0)).image (eta ψ G)).card * G.card
      ≤ Fintype.card F - 1 := by
  set S : Finset F := Finset.univ.filter (fun b : F => b ≠ 0) with hS
  set V : Finset ℂ := S.image (eta ψ G) with hV
  -- |S| = q - 1
  have hScard : S.card = Fintype.card F - 1 := by
    rw [hS, Finset.filter_ne']
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  -- each value's fiber contains a full G-coset, so has size ≥ |G|
  have hfiber : ∀ v ∈ V, G.card ≤ (S.filter (fun b => eta ψ G b = v)).card := by
    intro v hv
    rw [hV, Finset.mem_image] at hv
    obtain ⟨b, hbS, hbv⟩ := hv
    have hb0 : b ≠ 0 := by simpa [hS] using hbS
    -- b·G ⊆ fiber_v, and |b·G| = |G|
    have hsub : G.image (fun x => b * x) ⊆ S.filter (fun b' => eta ψ G b' = v) := by
      intro z hz
      simp only [Finset.mem_image] at hz
      obtain ⟨x, hxG, rfl⟩ := hz
      have hx0 : x ≠ 0 := fun h => h0 (h ▸ hxG)
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
        exact mul_ne_zero hb0 hx0
      · rw [eta_mul_invariant ψ G b hxG hmul h0, hbv]
    calc G.card = (G.image (fun x => b * x)).card :=
            (Finset.card_image_of_injOn (fun a _ c _ h => mul_left_cancel₀ hb0 h)).symm
      _ ≤ (S.filter (fun b' => eta ψ G b' = v)).card := Finset.card_le_card hsub
  -- |S| = Σ_{v∈V} |fiber_v| ≥ Σ_{v∈V} |G| = |V|·|G|
  have hpart : S.card = ∑ v ∈ V, (S.filter (fun b => eta ψ G b = v)).card :=
    Finset.card_eq_sum_card_fiberwise (fun b hb => Finset.mem_image_of_mem _ hb)
  have hge : V.card * G.card ≤ S.card := by
    rw [hpart]
    calc V.card * G.card = ∑ _v ∈ V, G.card := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ v ∈ V, (S.filter (fun b => eta ψ G b = v)).card := Finset.sum_le_sum hfiber
  rwa [hScard] at hge

end ArkLib.ProximityGap.GaussPeriodCosetReduction

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.GaussPeriodCosetReduction.eta_mul_of_image_eq
#print axioms ArkLib.ProximityGap.GaussPeriodCosetReduction.image_mul_self_of_mem
#print axioms ArkLib.ProximityGap.GaussPeriodCosetReduction.eta_mul_invariant
#print axioms ArkLib.ProximityGap.GaussPeriodCosetReduction.eta_constant_on_mulCoset
#print axioms ArkLib.ProximityGap.GaussPeriodCosetReduction.eta_image_card_mul_le
