/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT and Apache-2.0 licenses as described in LICENSE-MIT and LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.ActualTerminalQuartic
import ArkLib.Research.ProximityGap.Frontier.TerminalFactorCoverage

/-! # Only a quadratic or cubic can support an over-budget second-prime family -/

open Polynomial Finset Code
open scoped NNReal
open ArkLib.ProximityGap.Frontier
open HalfPredecessorBadEventRichPointBridge

namespace ProximityGap.TerminalFactorCoverage

open TerminalCollinearHeadCount

private abbrev p := ArkLib.ProximityGap.PrizeShapePrimeP30Second.P
local instance : Fact p.Prime := ⟨ArkLib.ProximityGap.PrizeShapePrimeP30Second.prime_P⟩

open Classical in
/-- The quartic population clause of the production terminal factor reduction now
holds for every actual word, interpolant, irreducible quartic factor and sample. -/
theorem secondPrime_quartic_population (u : WordStack (ZMod p) (Fin 2) (Fin (2^30))) :
    let fam := canonicalBadScalarRichPointFamily secondDomain (k := 2^26)
      ((715827881 : ℝ≥0)/1073741824) u (by decide)
    let φ := algebraMap (ZMod p) (AlgebraicClosure (ZMod p))
    ∀ (G : Finset (ZMod p)), G ⊆ fam.G → ∀ Q f : Polynomial (Polynomial (AlgebraicClosure (ZMod p))[X]),
      Q ≠ 0 → Supported Q → Irreducible f → f ∣ Q → f.natDegree = 4 →
      (population φ fam G f).card ≤ 268435546 := by
  intro fam φ G hG Q f hQ hs hi hd hy
  let L := population φ fam G f
  have hL : L ⊆ fam.G := Finset.Subset.trans (Finset.filter_subset _ _) hG
  have ht : 357913943 ≤ ⌈(1-(715827881 : ℝ≥0)/1073741824) *
      (Fintype.card (Fin (2^30)) : ℝ≥0)⌉₊ := by
    have h := TwoCorePackingThreshold.agreement_ceiling 715827881 (by decide)
    norm_num only [Fintype.card_fin, TwoCorePackingThreshold.domainLength, Nat.cast_ofNat, Nat.reduceSub] at h
    simpa only [Fintype.card_fin, Nat.reducePow, Nat.cast_ofNat] using h.ge
  exact ActualTerminalQuartic.actual_quartic_label_cap φ (p := p) (by decide) secondDomain _ u
    (Fintype.card_fin _) ht fam Q f hQ hd hi hy (fun j i a hh => (hs j i a hh).2.1) L hL
    (fun z hz => (Finset.mem_filter.mp hz).2)

/-- At the named predecessor an over-budget sample forces 4129 quadratic sections
or 1431655733 cubic sections on one irreducible factor of the actual interpolant. -/
theorem secondPrime_quadratic_or_cubic (u : WordStack (ZMod p) (Fin 2) (Fin (2^30))) :
    let fam := canonicalBadScalarRichPointFamily secondDomain (k := 2^26)
      ((715827881 : ℝ≥0)/1073741824) u (by decide)
    let φ := algebraMap (ZMod p) (AlgebraicClosure (ZMod p))
    ∀ G : Finset (ZMod p), G ⊆ fam.G → G.card = 2147483649 →
      ∃ Q f : Polynomial (Polynomial (AlgebraicClosure (ZMod p))[X]),
        Q ≠ 0 ∧ Supported Q ∧ Irreducible f ∧ f ∣ Q ∧
        ((f.natDegree = 2 ∧ 4129 ≤ (population φ fam G f).card) ∨
         (f.natDegree = 3 ∧ 1431655733 ≤ (population φ fam G f).card)) := by
  intro fam φ G hG hN
  obtain ⟨Q,f,hQ,hs,hi,hd,hcase⟩ := secondPrime_factor_obstruction u G hG hN
  refine ⟨Q,f,hQ,hs,hi,hd,?_⟩
  rcases hcase with h₂ | h₃ | ⟨hy,h₄⟩
  · exact Or.inl h₂
  · exact Or.inr h₃
  · have hc := secondPrime_quartic_population u G hG Q f hQ hs hi hd hy
    exact False.elim ((by decide : ¬ 2147483615 ≤ 268435546) (h₄.trans hc))

end ProximityGap.TerminalFactorCoverage

open ProximityGap.TerminalFactorCoverage in
#print axioms secondPrime_quartic_population
open ProximityGap.TerminalFactorCoverage in
#print axioms secondPrime_quadratic_or_cubic
