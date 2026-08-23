/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.I031OrbitCountPartition

/-!
# I031 — the UNCONDITIONAL distinct-period count: `≤ (q−1)/n` over `Fₚ*` (#444)

`SubgroupGaussSumOrbitReduction.card_distinct_eta_le` bounds the number of distinct Gauss periods by
`|T|` *for a **supplied** coset-covering transversal `T`*, and `I031OrbitCountPartition.orbit_count`
proves the orbits number **exactly `(q−1)/n`**. This file welds the two into the **unconditional**
metric-entropy statement the I031 route actually wants:

> the number of **distinct Gauss-period values** `η_b` over the `q−1` nonzero frequencies is
> **at most `(q−1)/n`** — *no transversal needs to be supplied*.

Mechanism: the period `b ↦ η_b` is **constant on each `μ_n`-coset** (`eta_dilation_invariant`), so it
**factors through the coset-label map** `cosetLabel n`. An image of a map that factors through `g` has
card `≤ |image g|`; with `|image (cosetLabel n) over Fₚ*| = (q−1)/n` (`orbit_count`) this gives the
bound. The same argument runs for the **moduli** `‖η_b‖` (the actual prize objective).

**Probe (validated before formalizing).** `scripts/probes/probe_i031_distinct_period_count.py`: over
`Fₚ*` at prize-regime primes (`n=2^a`, `n∣p−1`, `p≫n³`, n=4..32), `#{distinct η_b} ≤ (p−1)/n` always
(and is in fact `= (p−1)/n` here — the bound is tight); same for `#{distinct ‖η_b‖}`. NEVER `n=q−1`.

**Honesty (rules 3, 6).** This is the EXACT cardinality of the period-value alphabet; it is NOT a CORE
closure and NOT thinness-essential (it holds for any multiplicative subgroup of any thickness). VALUE =
frontier-movement: it discharges the *"supply a transversal"* hypothesis of
`card_distinct_eta_le`, making the `log p → log(p/n)` metric-entropy collapse an **unconditional**
in-tree fact at the period-alphabet level. The remaining open content (the bounded-constant
deterministic→random sup transfer over the `(q−1)/n` distinct values) is untouched. CORE
(`M(μ_n) ≤ C·√(n·log(p/n))`) stays OPEN.
-/

open Finset Polynomial
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.I031DilationOrbitReduction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Same coset ⟹ equal period.** If `b₁, b₂ ≠ 0` lie in the same `μ_n`-coset
(`cosetLabel n b₁ = cosetLabel n b₂`) then `η_{b₁} = η_{b₂}`. This is the *converse* of
`ratio_mem_of_cosetLabel_eq`: equal labels give `b₂ b₁⁻¹ ∈ μ_n`, and dilation invariance
(`eta_dilation_invariant`) then forces equal periods. -/
theorem eta_eq_of_cosetLabel_eq {ψ : AddChar F ℂ} {n : ℕ} (hn : 0 < n) {b₁ b₂ : F}
    (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) (h : cosetLabel n b₁ = cosetLabel n b₂) :
    eta ψ (nthRootsFinset n (1 : F)) b₂ = eta ψ (nthRootsFinset n (1 : F)) b₁ := by
  -- `b₂ b₁⁻¹ ∈ μ_n`, write `ζ := b₂ b₁⁻¹`, then `b₂ = ζ * b₁` and apply dilation invariance.
  have hζ : b₂ * b₁⁻¹ ∈ nthRootsFinset n (1 : F) :=
    ratio_mem_of_cosetLabel_eq hn hb₁ hb₂ h
  have hb₂eq : b₂ = (b₂ * b₁⁻¹) * b₁ := by
    field_simp
  rw [hb₂eq, eta_dilation_invariant hζ b₁]

/-! ### The unconditional distinct-period count

We bound `|{η_b : b ∈ Fₚ*}| ≤ |{cosetLabel n b : b ∈ Fₚ*}| = (q−1)/n`. The first inequality is a
"factors-through" image bound: define on `Fₚ*` the value map `b ↦ η_b` and the label map
`b ↦ cosetLabel n b`; equal labels give equal values, so the value-image injects into the
label-image. -/

/-- **A map that factors through another has a smaller image** (on a common domain `S`). If
`f a = f a'` whenever `g a = g a'` (for `a, a' ∈ S`), then `(S.image f).card ≤ (S.image g).card`.
Proof: `f` restricted to `S` factors as `h ∘ g` for `h := fun y => f (choose a preimage)`; hence
`S.image f = (S.image g).image h`, whose card is `≤ (S.image g).card` by `card_image_le`. -/
theorem image_card_le_of_factors {F α β : Type*} [DecidableEq F] [DecidableEq α] [DecidableEq β]
    {S : Finset F} {f : F → α} {g : F → β}
    (hfac : ∀ a ∈ S, ∀ a' ∈ S, g a = g a' → f a = f a') :
    (S.image f).card ≤ (S.image g).card := by
  classical
  rcases S.eq_empty_or_nonempty with hS | hS
  · subst hS; simp
  · obtain ⟨a₀, ha₀⟩ := hS
    -- `h y := f a` for some `a ∈ S` with `g a = y` (junk default `f a₀` off `image g`).
    set h : β → α := fun y =>
      if hy : ∃ a, a ∈ S ∧ g a = y then f hy.choose else f a₀ with hh
    -- `SurjOn h (image g) (image f)`: every `f a` is hit by `g a` under `h`.
    apply Finset.card_le_card_of_surjOn h
    intro v hv
    rw [Finset.coe_image, Set.mem_image] at hv
    obtain ⟨a, ha, rfl⟩ := hv
    rw [Set.mem_image]
    refine ⟨g a, ?_, ?_⟩
    · exact Finset.mem_coe.mpr (Finset.mem_image_of_mem g ha)
    · have hex : ∃ a', a' ∈ S ∧ g a' = g a := ⟨a, ha, rfl⟩
      rw [hh]
      simp only [hex, dif_pos]
      exact hfac _ hex.choose_spec.1 _ ha hex.choose_spec.2

/-- **The unconditional distinct-period-VALUE count `≤ (q−1)/n`.** Over the `q−1` nonzero
frequencies, the number of distinct Gauss-period values `η_b` is at most `(Fintype.card F − 1)/n`.
The value map factors through `cosetLabel n` (equal labels ⇒ equal periods, via
`eta_eq_of_cosetLabel_eq`), so its image injects into the label image, of card `(q−1)/n`
(`orbit_count`). -/
theorem card_distinct_eta_le_orbitCount {ψ : AddChar F ℂ} {n : ℕ} {ζ : F}
    (hζprim : IsPrimitiveRoot ζ n) (hn : 0 < n) :
    ((nonzeroFreqs F).image (eta ψ (nthRootsFinset n (1 : F)))).card
      ≤ (Fintype.card F - 1) / n := by
  refine le_trans ?_ (le_of_eq (orbit_count hζprim hn))
  apply image_card_le_of_factors
  intro a ha a' ha' hlabel
  rw [mem_nonzeroFreqs] at ha ha'
  exact (eta_eq_of_cosetLabel_eq hn ha' ha hlabel.symm)

/-- **The unconditional distinct-MODULUS count `≤ (q−1)/n`** (the actual prize objective `‖η_b‖`).
Same factoring: `‖η_b‖` is constant on cosets, so the modulus alphabet has card `≤ (q−1)/n`. -/
theorem card_distinct_etaNorm_le_orbitCount {ψ : AddChar F ℂ} {n : ℕ} {ζ : F}
    (hζprim : IsPrimitiveRoot ζ n) (hn : 0 < n) :
    ((nonzeroFreqs F).image (fun b => ‖eta ψ (nthRootsFinset n (1 : F)) b‖)).card
      ≤ (Fintype.card F - 1) / n := by
  refine le_trans ?_ (le_of_eq (orbit_count hζprim hn))
  apply image_card_le_of_factors
  intro a ha a' ha' hlabel
  rw [mem_nonzeroFreqs] at ha ha'
  rw [eta_eq_of_cosetLabel_eq hn ha' ha hlabel.symm]

end ArkLib.ProximityGap.I031DilationOrbitReduction
