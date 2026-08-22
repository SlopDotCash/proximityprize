/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CollinearityMatchingFrame

/-!
# The matching forcing lemmas: M1 ⟹ vertical, M4 ⟹ horizontal

Campaign #357, the first two cases of the fourteen-case exactness tree (probe C8/C9: of
the 10395 perfect matchings of the twelve determinant terms, exactly 14 occur, each
forcing its stratum through three congruences). This file proves the two immediate ones:

* `m1_forces_vertical` — the matching `(01)(23)(45)(67)(89)(10 11)`: the six term
  equations cancel to `a₁ = b₁+h ∧ a₂ = b₂+h ∧ a₃ = b₃+h` — **all three pairs
  antipodal**: the degenerate vertical line of `Γ_n`.
* `m4_forces_horizontal` — the matching `(02)(13)(48)(59)(6 10)(7 11)`: the equations
  cancel to `a₁+b₁ = a₂+b₂ = a₃+b₃` — **equal products**: the horizontal stratum.

Both are stated at the `ZMod (2^m)` level: the term-pairing hypotheses are the cast
forms of the `Balanced`-matching relations (`ZMod.natCast_eq_natCast_iff'` converts), and
the conclusions are the stratum's defining congruences. The remaining twelve cases (four
family matchings — one antipodal-pair equation + the chord congruence — and eight
second-layer seed systems) follow the same cancellation template.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References

* Issue #357 (the matching-pattern census comments); probe
  `probe_slanted_char0_census.py` C8/C9; `CollinearityMatchingFrame.lean`
  (`Balanced`, `balanced_exists_partner`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.MatchingForcingLemmas

variable {m : ℕ}

local notation "H" => ((2 ^ (m - 1) : ℕ) : ZMod (2 ^ m))

/-- **M1 forces the vertical stratum.** The neighbor matching's term equations cancel to:
all three exponent pairs antipodal. (Terms 0–11 are `a₂+s₃, b₂+s₃ | a₂+s₁, b₂+s₁ |
a₁+s₃, b₁+s₃ | a₃+s₂, b₃+s₂ | a₁+s₂, b₁+s₂ | a₃+s₁, b₃+s₁`, `sᵢ = aᵢ+bᵢ`; M1 pairs
neighbors and the common summand cancels.) -/
theorem m1_forces_vertical
    (A₁ B₁ A₂ B₂ A₃ B₃ : ZMod (2 ^ m))
    (h01 : A₂ + (A₃ + B₃) = B₂ + (A₃ + B₃) + H)
    (h23 : A₂ + (A₁ + B₁) = B₂ + (A₁ + B₁) + H)
    (h45 : A₁ + (A₃ + B₃) = B₁ + (A₃ + B₃) + H)
    (h67 : A₃ + (A₂ + B₂) = B₃ + (A₂ + B₂) + H)
    (h89 : A₁ + (A₂ + B₂) = B₁ + (A₂ + B₂) + H)
    (h1011 : A₃ + (A₁ + B₁) = B₃ + (A₁ + B₁) + H) :
    A₁ = B₁ + H ∧ A₂ = B₂ + H ∧ A₃ = B₃ + H :=
  ⟨by linear_combination h45, by linear_combination h01, by linear_combination h67⟩

/-- **M4 forces the horizontal stratum.** The product matching's equations cancel to:
all three pair-products coincide. (Each positive term is paired with the negative term
of the same exponent; the double sign-shift `H + H = 0` cancels.) -/
theorem m4_forces_horizontal
    (A₁ B₁ A₂ B₂ A₃ B₃ : ZMod (2 ^ m))
    (h02 : A₂ + (A₃ + B₃) = A₂ + (A₁ + B₁) + H + H)
    (h13 : B₂ + (A₃ + B₃) = B₂ + (A₁ + B₁) + H + H)
    (h48 : A₁ + (A₃ + B₃) = A₁ + (A₂ + B₂) + H + H)
    (h59 : B₁ + (A₃ + B₃) = B₁ + (A₂ + B₂) + H + H)
    (h610 : A₃ + (A₂ + B₂) = A₃ + (A₁ + B₁) + H + H)
    (h711 : B₃ + (A₂ + B₂) = B₃ + (A₁ + B₁) + H + H)
    (hHH : H + H = 0) :
    A₁ + B₁ = A₂ + B₂ ∧ A₂ + B₂ = A₃ + B₃ :=
  ⟨by linear_combination - h610 - hHH, by linear_combination - h48 - hHH⟩

/-! ## Source audit -/

#print axioms m1_forces_vertical
#print axioms m4_forces_horizontal

end ArkLib.ProximityGap.MatchingForcingLemmas
