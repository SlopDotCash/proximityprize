/-
# AvE5 — The "choose a good prime" escape is a NON-SEQUITUR (quantifier audit)

This brick settles the E5 angle on the proximity prize (#444): is the prize a
**for-all-fields uniform** statement (constants fixed *before* the field is quantified),
or does an **exists-good-field** suffice?

The faithful in-tree target `ProximityGap.mcaConjecture` (ABF26 §4.5,
`GrandChallenges.lean:650`) has shape

  `∃ c₁ c₂ c₃ : ℝ, ∀ (field F) (domain) (k) (δ), … ε_mca(RS[F,…], δ) ≤ bound(c₁,c₂,c₃) `

i.e. the three constants are chosen FIRST, then the bound must hold for EVERY finite
field `F`. So a per-field-tuned bound (BGK effective for almost all primes) does NOT
discharge it: BGK gives, for each `F`, *some* constant — the order `∀F ∃c` — which is
the swapped quantifier and is strictly weaker.

This file abstracts that quantifier shape and proves, with zero domain assumptions, that
`∀F ∃c, P F c` (per-field constant; what prime-selection / density-1-BGK delivers) does
NOT imply `∃c ∀F, P F c` (the uniform prize). The witness is the standard order-swap
counterexample, so the implication genuinely fails — formal confirmation that the
"choose a good prime" route is a non-sequitur for THIS target.
-/

namespace ArkLib.ProximityGap.Frontier.AvE5

/-- Abstract shape of the prize predicate: `P F c` ≈ "the constant `c` makes the MCA bound
hold for field of size `F`". -/
abbrev Pred := ℕ → ℕ → Prop

/-- The **uniform** form (the actual prize, `mcaConjecture` shape): one constant works for
ALL fields. -/
def Uniform (P : Pred) : Prop := ∃ c, ∀ F, P F c

/-- The **per-field** form (what prime selection / density-1 BGK delivers): for each field
there EXISTS a working constant — but it may depend on the field. -/
def PerField (P : Pred) : Prop := ∀ F, ∃ c, P F c

/-- Trivially, the uniform (prize) form implies the per-field form. -/
theorem uniform_imp_perField (P : Pred) (h : Uniform P) : PerField P := by
  obtain ⟨c, hc⟩ := h
  exact fun F => ⟨c, hc F⟩

/-- **The escape is a non-sequitur.** There is a predicate for which the per-field form
holds (a good constant exists for every field — exactly the BGK-for-almost-all-primes
situation) but the uniform prize form FAILS. Hence "choose a good prime" cannot, by pure
quantifier logic, discharge `mcaConjecture`.

Witness: `P F c := F ≤ c` ("the constant must dominate the field size"). For each `F`,
`c := F` works (`PerField`), but no single `c` dominates all `F` (`¬ Uniform`). -/
theorem perField_not_imp_uniform :
    ∃ P : Pred, PerField P ∧ ¬ Uniform P := by
  refine ⟨fun F c => F ≤ c, ?_, ?_⟩
  · intro F; exact ⟨F, Nat.le_refl F⟩
  · rintro ⟨c, hc⟩
    -- `hc (c+1) : c+1 ≤ c`, impossible.
    have := hc (c + 1)
    omega

/-- Therefore `PerField → Uniform` is NOT a theorem (it has a counterexample), i.e. the
implication the "good prime" strategy would need is false in general. -/
theorem no_perField_to_uniform :
    ¬ (∀ P : Pred, PerField P → Uniform P) := by
  intro h
  obtain ⟨P, hper, hnu⟩ := perField_not_imp_uniform
  exact hnu (h P hper)

#print axioms uniform_imp_perField
#print axioms perField_not_imp_uniform
#print axioms no_perField_to_uniform

end ArkLib.ProximityGap.Frontier.AvE5
