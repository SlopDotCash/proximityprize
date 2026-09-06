/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSixthMoment

/-!
# LANE FS4 (#466, Fable session 2026-07-09): THE DEPTH-3 PATTERN DECOMPOSITION —
  `addEnergy3(μ_n) = trivialCount + wraparound excess`, exactly, for 2-power domains

The structural bridge between the depth-3 additive energy of `G = μ_{2m} = ⟨ζ⟩ ⊂ F*`
(the r53/r55 object) and the FS1/FS2/FS3 annihilator-ledger machinery:

* Every exponent sextuple `(a₁,…,a₆) ∈ [2m)⁶` folds to a **pattern polynomial**
  `P = Σ_{i≤3} μ(aᵢ) − Σ_{i>3} μ(aᵢ) ∈ ℤ[X]`, `μ(a) = X^a` for `a < m` and `−X^{a−m}`
  otherwise, with `deg P < m` and `|coeffs| ≤ 6` (`patternPoly_natDegree_lt`,
  `patternPoly_coeff_abs_le` — precisely the FS3 height-input shape at `b = 3`).
* Since `ζ^m = −1`, the sextuple is an energy solution iff `P(ζ) = 0`
  (`sum_eq_iff_aeval_patternPoly`).
* **The exact decomposition** (`addEnergy3_eq_trivial_add_excess`):
  `addEnergy3 G = #{sextuples : P = 0 in ℤ[X]} + #{sextuples : P ≠ 0 ∧ P(ζ) = 0}`.
  The first term is the CHAR-0 (field-independent!) count; the second is the char-`p`
  wraparound excess — each of whose patterns owns an FS2/FS3 annihilator of dyadic height,
  so the FS1 ledger caps how many primes can see a large second term.

**What remains for the unconditional almost-all-primes r=3 Wick rung:** ONE purely
combinatorial, field-free counting lemma — `trivialCount m ≤ 15n³ − 45n² + 40n` (`n = 2m`;
probes say EQUALITY — the 15 perfect matchings inclusion–exclusion).  No fields, no
characters, no resultants: finite ℤ[X] combinatorics.  Named, not claimed.

Issue #466, lane FS4.  Target axiom set: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial

namespace ArkLib.ProximityGap.Frontier.FS4Depth3PatternDecomposition

open ArkLib.ProximityGap.SubgroupGaussSumSixthMoment

open scoped Classical

/-- The folded monomial: `X^a` for `a < m`, `−X^{a−m}` for `a ≥ m` (using `ζ^m = −1`). -/
noncomputable def monomF (m a : ℕ) : ℤ[X] :=
  if a < m then X ^ a else -(X ^ (a - m))

/-- The pattern polynomial of an exponent sextuple. -/
noncomputable def patternPoly (m a₁ a₂ a₃ a₄ a₅ a₆ : ℕ) : ℤ[X] :=
  (monomF m a₁ + monomF m a₂ + monomF m a₃)
    - (monomF m a₄ + monomF m a₅ + monomF m a₆)

section PolyFacts

/-- Folded monomials have degree `< m` (for in-range exponents). -/
theorem monomF_natDegree_lt {m a : ℕ} (hm : 0 < m) (ha : a < 2 * m) :
    (monomF m a).natDegree < m := by
  unfold monomF
  split_ifs with h
  · simpa [natDegree_X_pow] using h
  · rw [natDegree_neg, natDegree_X_pow]
    omega

/-- Folded monomial coefficients are `0` or `±1`. -/
theorem monomF_coeff_abs_le (m a i : ℕ) : |(monomF m a).coeff i| ≤ 1 := by
  unfold monomF
  split_ifs with h <;> simp [coeff_X_pow] <;> split_ifs <;> simp

/-- The pattern polynomial has degree `< m`. -/
theorem patternPoly_natDegree_lt {m a₁ a₂ a₃ a₄ a₅ a₆ : ℕ} (hm : 0 < m)
    (h₁ : a₁ < 2 * m) (h₂ : a₂ < 2 * m) (h₃ : a₃ < 2 * m)
    (h₄ : a₄ < 2 * m) (h₅ : a₅ < 2 * m) (h₆ : a₆ < 2 * m) :
    (patternPoly m a₁ a₂ a₃ a₄ a₅ a₆).natDegree < m := by
  unfold patternPoly
  have b₁ := monomF_natDegree_lt hm h₁
  have b₂ := monomF_natDegree_lt hm h₂
  have b₃ := monomF_natDegree_lt hm h₃
  have b₄ := monomF_natDegree_lt hm h₄
  have b₅ := monomF_natDegree_lt hm h₅
  have b₆ := monomF_natDegree_lt hm h₆
  calc (patternPoly m a₁ a₂ a₃ a₄ a₅ a₆).natDegree
      = ((monomF m a₁ + monomF m a₂ + monomF m a₃)
          - (monomF m a₄ + monomF m a₅ + monomF m a₆)).natDegree := rfl
    _ < m := by
        refine lt_of_le_of_lt (natDegree_sub_le _ _) ?_
        rw [Nat.max_lt]
        constructor
        · refine lt_of_le_of_lt (natDegree_add_le _ _) ?_
          rw [Nat.max_lt]
          exact ⟨lt_of_le_of_lt (natDegree_add_le _ _) (Nat.max_lt.mpr ⟨b₁, b₂⟩), b₃⟩
        · refine lt_of_le_of_lt (natDegree_add_le _ _) ?_
          rw [Nat.max_lt]
          exact ⟨lt_of_le_of_lt (natDegree_add_le _ _) (Nat.max_lt.mpr ⟨b₄, b₅⟩), b₆⟩

/-- Pattern-polynomial coefficients are bounded by `6 ≤ 2^3` (the FS3 `b = 3` shape). -/
theorem patternPoly_coeff_abs_le (m a₁ a₂ a₃ a₄ a₅ a₆ i : ℕ) :
    |(patternPoly m a₁ a₂ a₃ a₄ a₅ a₆).coeff i| ≤ 2 ^ 3 := by
  have c₁ := monomF_coeff_abs_le m a₁ i
  have c₂ := monomF_coeff_abs_le m a₂ i
  have c₃ := monomF_coeff_abs_le m a₃ i
  have c₄ := monomF_coeff_abs_le m a₄ i
  have c₅ := monomF_coeff_abs_le m a₅ i
  have c₆ := monomF_coeff_abs_le m a₆ i
  unfold patternPoly
  simp only [coeff_sub, coeff_add]
  rw [abs_le] at c₁ c₂ c₃ c₄ c₅ c₆
  rw [abs_le]
  constructor <;> [linarith; linarith]

end PolyFacts

section Eval

variable {F : Type*} [Field F]

/-- Folded-monomial evaluation: `μ(a)(ζ) = ζ^a` whenever `ζ^m = −1`. -/
theorem aeval_monomF {ζ : F} {m : ℕ} (hζ : ζ ^ m = -1) {a : ℕ} (ha : a < 2 * m) :
    aeval ζ (monomF m a) = ζ ^ a := by
  unfold monomF
  split_ifs with h
  · simp
  · push_neg at h
    have : ζ ^ a = ζ ^ (a - m) * ζ ^ m := by
      rw [← pow_add]
      congr 1
      omega
    simp [this, hζ]

/-- The energy condition is pattern-polynomial vanishing. -/
theorem sum_eq_iff_aeval_patternPoly {ζ : F} {m : ℕ} (hζ : ζ ^ m = -1)
    {a₁ a₂ a₃ a₄ a₅ a₆ : ℕ}
    (h₁ : a₁ < 2 * m) (h₂ : a₂ < 2 * m) (h₃ : a₃ < 2 * m)
    (h₄ : a₄ < 2 * m) (h₅ : a₅ < 2 * m) (h₆ : a₆ < 2 * m) :
    (ζ ^ a₁ + ζ ^ a₂ + ζ ^ a₃ = ζ ^ a₄ + ζ ^ a₅ + ζ ^ a₆)
      ↔ aeval ζ (patternPoly m a₁ a₂ a₃ a₄ a₅ a₆) = 0 := by
  unfold patternPoly
  rw [map_sub, map_add, map_add, map_add, map_add,
    aeval_monomF hζ h₁, aeval_monomF hζ h₂, aeval_monomF hζ h₃,
    aeval_monomF hζ h₄, aeval_monomF hζ h₅, aeval_monomF hζ h₆, sub_eq_zero]

end Eval

section Decomposition

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The exponent domain: sextuples over `[0, n)`. -/
def tupleSet (n : ℕ) : Finset (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  range n ×ˢ range n ×ˢ range n ×ˢ range n ×ˢ range n ×ˢ range n

theorem tupleSet_card (n : ℕ) : (tupleSet n).card = n ^ 6 := by
  simp [tupleSet, Finset.card_product]
  ring

/-- The pattern polynomial of a sextuple, uncurried. -/
noncomputable def pp (m : ℕ) (t : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : ℤ[X] :=
  patternPoly m t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2

/-- The CHAR-0 count: sextuples whose pattern polynomial is identically zero.  This is a
field-independent, purely combinatorial quantity. -/
noncomputable def trivialCount (m : ℕ) : ℕ :=
  ((tupleSet (2 * m)).filter (fun t => pp m t = 0)).card

/-- The char-`p` wraparound excess: sextuples with a NONZERO pattern that nevertheless
vanishes at `ζ`. -/
noncomputable def wraparoundExcess (ζ : F) (m : ℕ) : ℕ :=
  ((tupleSet (2 * m)).filter (fun t => pp m t ≠ 0 ∧ aeval ζ (pp m t) = 0)).card

/-- **THE EXACT DECOMPOSITION.**  For `ζ` a primitive `2m`-th root of unity in `F` and
`G = ⟨ζ⟩` (as the image of `a ↦ ζ^a` on `[0, 2m)`),
`addEnergy3 G = trivialCount m + wraparoundExcess ζ m`. -/
theorem addEnergy3_eq_trivial_add_excess {ζ : F} {m : ℕ} (hm : 0 < m)
    (hprim : IsPrimitiveRoot ζ (2 * m)) :
    addEnergy3 ((range (2 * m)).image (ζ ^ ·))
      = trivialCount m + wraparoundExcess ζ m := by
  have hn0 : 0 < 2 * m := by omega
  -- ζ^m = −1
  have hζm : ζ ^ m = -1 := by
    have hsq : ζ ^ m * ζ ^ m = 1 := by
      rw [← pow_add]
      have : m + m = 2 * m := by ring
      rw [this]
      exact hprim.pow_eq_one
    rcases mul_self_eq_one_iff.mp hsq with h | h
    · exact absurd h (hprim.pow_ne_one_of_pos_of_lt hm.ne' (by omega))
    · exact h
  -- reindex each of the six sums over the image
  have hinj : ∀ x ∈ range (2 * m), ∀ y ∈ range (2 * m), ζ ^ x = ζ ^ y → x = y := by
    intro x hx y hy hxy
    exact hprim.pow_inj (mem_range.mp hx) (mem_range.mp hy) hxy
  have himg : ∀ f : F → ℕ,
      ∑ y ∈ (range (2 * m)).image (ζ ^ ·), f y = ∑ a ∈ range (2 * m), f (ζ ^ a) :=
    fun f => Finset.sum_image hinj
  have hexp : addEnergy3 ((range (2 * m)).image (ζ ^ ·))
      = ∑ a₁ ∈ range (2 * m), ∑ a₂ ∈ range (2 * m), ∑ a₃ ∈ range (2 * m),
        ∑ a₄ ∈ range (2 * m), ∑ a₅ ∈ range (2 * m), ∑ a₆ ∈ range (2 * m),
        (if ζ ^ a₁ + ζ ^ a₂ + ζ ^ a₃ = ζ ^ a₄ + ζ ^ a₅ + ζ ^ a₆ then (1 : ℕ) else 0) := by
    rw [addEnergy3, himg]
    refine Finset.sum_congr rfl (fun a₁ _ => ?_)
    rw [himg]
    refine Finset.sum_congr rfl (fun a₂ _ => ?_)
    rw [himg]
    refine Finset.sum_congr rfl (fun a₃ _ => ?_)
    rw [himg]
    refine Finset.sum_congr rfl (fun a₄ _ => ?_)
    rw [himg]
    refine Finset.sum_congr rfl (fun a₅ _ => ?_)
    rw [himg]
  rw [hexp]
  -- pointwise indicator split
  have hpoint : ∀ a₁ ∈ range (2 * m), ∀ a₂ ∈ range (2 * m), ∀ a₃ ∈ range (2 * m),
      ∀ a₄ ∈ range (2 * m), ∀ a₅ ∈ range (2 * m), ∀ a₆ ∈ range (2 * m),
      (if ζ ^ a₁ + ζ ^ a₂ + ζ ^ a₃ = ζ ^ a₄ + ζ ^ a₅ + ζ ^ a₆ then (1 : ℕ) else 0)
        = (if patternPoly m a₁ a₂ a₃ a₄ a₅ a₆ = 0 then (1 : ℕ) else 0)
          + (if patternPoly m a₁ a₂ a₃ a₄ a₅ a₆ ≠ 0
              ∧ aeval ζ (patternPoly m a₁ a₂ a₃ a₄ a₅ a₆) = 0 then (1 : ℕ) else 0) := by
    intro a₁ h₁ a₂ h₂ a₃ h₃ a₄ h₄ a₅ h₅ a₆ h₆
    rw [mem_range] at h₁ h₂ h₃ h₄ h₅ h₆
    have hiff := sum_eq_iff_aeval_patternPoly (m := m) hζm h₁ h₂ h₃ h₄ h₅ h₆
    by_cases hP : patternPoly m a₁ a₂ a₃ a₄ a₅ a₆ = 0
    · have hE : aeval ζ (patternPoly m a₁ a₂ a₃ a₄ a₅ a₆) = 0 := by rw [hP]; simp
      rw [if_pos (hiff.mpr hE), if_pos hP, if_neg (by simp [hP])]
    · by_cases hE : aeval ζ (patternPoly m a₁ a₂ a₃ a₄ a₅ a₆) = 0
      · rw [if_pos (hiff.mpr hE), if_neg hP, if_pos ⟨hP, hE⟩]
      · rw [if_neg (fun h => hE (hiff.mp h)), if_neg hP, if_neg (by simp [hE])]
  -- split the sextuple sum accordingly
  calc ∑ a₁ ∈ range (2 * m), ∑ a₂ ∈ range (2 * m), ∑ a₃ ∈ range (2 * m),
        ∑ a₄ ∈ range (2 * m), ∑ a₅ ∈ range (2 * m), ∑ a₆ ∈ range (2 * m),
        (if ζ ^ a₁ + ζ ^ a₂ + ζ ^ a₃ = ζ ^ a₄ + ζ ^ a₅ + ζ ^ a₆ then (1 : ℕ) else 0)
      = ∑ a₁ ∈ range (2 * m), ∑ a₂ ∈ range (2 * m), ∑ a₃ ∈ range (2 * m),
        ∑ a₄ ∈ range (2 * m), ∑ a₅ ∈ range (2 * m), ∑ a₆ ∈ range (2 * m),
        ((if patternPoly m a₁ a₂ a₃ a₄ a₅ a₆ = 0 then (1 : ℕ) else 0)
          + (if patternPoly m a₁ a₂ a₃ a₄ a₅ a₆ ≠ 0
              ∧ aeval ζ (patternPoly m a₁ a₂ a₃ a₄ a₅ a₆) = 0 then (1 : ℕ) else 0)) := by
        refine Finset.sum_congr rfl (fun a₁ h₁ => ?_)
        refine Finset.sum_congr rfl (fun a₂ h₂ => ?_)
        refine Finset.sum_congr rfl (fun a₃ h₃ => ?_)
        refine Finset.sum_congr rfl (fun a₄ h₄ => ?_)
        refine Finset.sum_congr rfl (fun a₅ h₅ => ?_)
        refine Finset.sum_congr rfl (fun a₆ h₆ => ?_)
        exact hpoint a₁ h₁ a₂ h₂ a₃ h₃ a₄ h₄ a₅ h₅ a₆ h₆
    _ = trivialCount m + wraparoundExcess ζ m := by
        simp only [Finset.sum_add_distrib]
        congr 1
        · rw [trivialCount, Finset.card_filter]
          simp only [tupleSet, Finset.sum_product]
          rfl
        · rw [wraparoundExcess, Finset.card_filter]
          simp only [tupleSet, Finset.sum_product]
          rfl

end Decomposition

-- Axiom audit (expected: [propext, Classical.choice, Quot.sound], no sorryAx)
#print axioms patternPoly_natDegree_lt
#print axioms patternPoly_coeff_abs_le
#print axioms sum_eq_iff_aeval_patternPoly
#print axioms addEnergy3_eq_trivial_add_excess

end ArkLib.ProximityGap.Frontier.FS4Depth3PatternDecomposition
