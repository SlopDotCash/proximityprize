import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R320C3SmallCenterResultant

/-!
# R326: finite prime exclusion gives exact small-center injectivity

The resultant weld in R320 says that a nonzero four-term collision forces its
characteristic to divide a bounded nonzero integer.  This consumer records the
useful contrapositive: once the finitely many candidate prime divisors have
been excluded, the small-center parametrization is injective.  The statement
is deliberately independent of any unproved global counting assertion.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.R326FinitePrimeExclusionInjectivity

open ArkLib.ProximityGap.Frontier.R320C3SmallCenterResultant

theorem c3_pattern_eq_zero_of_prime_exclusion
    {k prime : ℕ} {F : Type} [Field F] [CharP F prime]
    {ζ : F} (hhalfTurn : ζ ^ (2 ^ k) = -1)
    {leftOffset₁ rightOffset₁ leftComplement₁ rightComplement₁ : ℕ}
    (hleft₁ : leftOffset₁ < 2 * 2 ^ k) (hright₁ : rightOffset₁ < 2 * 2 ^ k)
    (hleftComp₁ : leftComplement₁ < 2 * 2 ^ k)
    (hrightComp₁ : rightComplement₁ < 2 * 2 ^ k)
    (hcollision : ζ ^ leftOffset₁ - ζ ^ rightOffset₁ - (2 : F) * ζ ^ leftComplement₁
        + (2 : F) * ζ ^ rightComplement₁ = 0)
    (hprimeExclusion : ∀ N : ℕ, N ≠ 0 → N ≤ 2 ^ ((k + 1 + 3) * 2 ^ (k + 1)) →
      ¬ prime ∣ N) :
    c3SmallCenterPattern (2 ^ k) leftOffset₁ rightOffset₁ leftComplement₁ rightComplement₁ = 0 := by
  classical
  by_contra hpattern
  obtain ⟨N, hN, hheight, hdivides⟩ := c3SmallCenterPattern_annihilator_exists_with_height
    (k := k) (leftOffset := leftOffset₁) (rightOffset := rightOffset₁)
    (leftComplement := leftComplement₁) (rightComplement := rightComplement₁)
    hpattern hleft₁ hright₁ hleftComp₁ hrightComp₁
  exact hprimeExclusion N hN hheight (hdivides F inferInstance prime inferInstance ζ
    hhalfTurn hcollision)

theorem c3_pattern_eq_zero_of_characteristic_above_height
    {k prime : ℕ} {F : Type} [Field F] [CharP F prime]
    {ζ : F} (hhalfTurn : ζ ^ (2 ^ k) = -1)
    {leftOffset rightOffset leftComplement rightComplement : ℕ}
    (hleft : leftOffset < 2 * 2 ^ k) (hright : rightOffset < 2 * 2 ^ k)
    (hleftComp : leftComplement < 2 * 2 ^ k)
    (hrightComp : rightComplement < 2 * 2 ^ k)
    (hcollision : ζ ^ leftOffset - ζ ^ rightOffset - (2 : F) * ζ ^ leftComplement
        + (2 : F) * ζ ^ rightComplement = 0)
    (hprime : 2 ^ ((k + 1 + 3) * 2 ^ (k + 1)) < prime) :
    c3SmallCenterPattern (2 ^ k) leftOffset rightOffset leftComplement rightComplement = 0 := by
  apply c3_pattern_eq_zero_of_prime_exclusion hhalfTurn hleft hright hleftComp hrightComp
    hcollision
  intro N hN hheight hdiv
  have hpos : 0 < N := Nat.pos_of_ne_zero hN
  have hlt : N < prime := lt_of_le_of_lt hheight hprime
  have hle : prime ≤ N := Nat.le_of_dvd hpos hdiv
  omega

end ArkLib.ProximityGap.Frontier.R326FinitePrimeExclusionInjectivity
