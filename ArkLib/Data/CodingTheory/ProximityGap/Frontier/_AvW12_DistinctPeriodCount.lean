/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.InteriorWorstCaseIncompleteSum

/-!
# Distinct-period count ≤ coset count (#444 / the Linnik–Fermat investigation)

The Fermat-prime probe (user's bad-prime lead, 2026-06-20) found that the period magnitudes
`‖η_b‖` take exactly `(q−1)/n` distinct values — one per `G`-coset — at the structured primes. The
*upper* half of that is unconditionally provable and is the rigorous count-reduction behind the
`log q → log(q/|G|)` tightening of `_AvW8`/`_AvW7`: by coset invariance (`_AvW8.norm_eta_coset_invariant`),
`b ↦ ‖η_b‖` is constant on each `G·b`, so its image over the nonzero frequencies is no larger than
the number of cosets.

This file formalizes that bound in transversal form: given a representative set `R` that **covers
every coset** (every nonzero `b` equals `g·r` for some `g ∈ G`, `r ∈ R`), the distinct period values
over the nonzero frequencies number at most `|R| = (q−1)/|G|`. This is the exact mechanism that lets
the union bound run over cosets, not frequencies — a genuine, proven consequence of the coset
structure surfaced by the bad-prime investigation. NOT the Paley bound itself (open). NOT closure.
-/

namespace ArkLib.ProximityGap.Frontier.AvW12

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Coset invariance (inlined from `_AvW8`).** For `g ≠ 0` with `G` stable under `(g * ·)`,
`‖eta ψ G (g * b)‖ = ‖eta ψ G b‖` (reindex `y ↦ g*y` permutes `G`). -/
theorem norm_eta_coset_invariant (ψ : AddChar F ℂ) (G : Finset F) (g b : F) (hg0 : g ≠ 0)
    (hg : G.image (fun y => g * y) = G) :
    ‖eta ψ G (g * b)‖ = ‖eta ψ G b‖ := by
  have hinj : ∀ a ∈ G, ∀ c ∈ G, g * a = g * c → a = c :=
    fun a _ c _ h => mul_left_cancel₀ hg0 h
  have hval : eta ψ G (g * b) = eta ψ G b := by
    unfold eta
    conv_rhs => rw [← hg, Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro y _
    congr 1
    ring
  rw [hval]

/-- **Distinct periods ≤ coset count (proven).** Let `s` be any finset of frequencies, `G` a finset
stable under multiplication by each of its nonzero elements (a multiplicative subgroup), and `R` a
transversal that *covers* `s`: every `b ∈ s` is `g * r` for some nonzero `g ∈ G` with `G` stable
under `g`, and some `r ∈ R`. Then the period magnitudes over `s` take at most `|R|` distinct values.
(Each `b = g·r` has `‖η_b‖ = ‖η_r‖` by `_AvW8` coset invariance, so the image lands in the image
over `R`.) -/
theorem distinct_periods_le_transversal
    (ψ : AddChar F ℂ) (G : Finset F) (s R : Finset F)
    (hcover : ∀ b ∈ s, ∃ g r, g ≠ 0 ∧ G.image (fun y => g * y) = G ∧ r ∈ R ∧ b = g * r) :
    (s.image (fun b => ‖eta ψ G b‖)) ⊆ (R.image (fun b => ‖eta ψ G b‖)) := by
  intro v hv
  simp only [Finset.mem_image] at hv ⊢
  obtain ⟨b, hbs, hbv⟩ := hv
  obtain ⟨g, r, hg0, hgstab, hrR, hbgr⟩ := hcover b hbs
  refine ⟨r, hrR, ?_⟩
  -- ‖η_b‖ = ‖η_{g·r}‖ = ‖η_r‖
  rw [← hbv, hbgr, norm_eta_coset_invariant ψ G g r hg0 hgstab]

/-- **The cardinality bound (proven).** Under the same covering hypothesis, the number of distinct
period magnitudes over `s` is at most `|R|`. With `R` a coset transversal of `F^×` by `G`, this is
`(q−1)/|G|` — the count the union bound actually runs over. -/
theorem card_distinct_periods_le
    (ψ : AddChar F ℂ) (G : Finset F) (s R : Finset F)
    (hcover : ∀ b ∈ s, ∃ g r, g ≠ 0 ∧ G.image (fun y => g * y) = G ∧ r ∈ R ∧ b = g * r) :
    (s.image (fun b => ‖eta ψ G b‖)).card ≤ R.card :=
  le_trans (Finset.card_le_card (distinct_periods_le_transversal ψ G s R hcover))
    (Finset.card_image_le)

end ArkLib.ProximityGap.Frontier.AvW12

/-! ## Axiom audit (expected: only `propext, Classical.choice, Quot.sound`; no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.Frontier.AvW12.distinct_periods_le_transversal
#print axioms ArkLib.ProximityGap.Frontier.AvW12.card_distinct_periods_le
