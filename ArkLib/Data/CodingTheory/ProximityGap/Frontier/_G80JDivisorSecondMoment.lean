/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G80KDivisorFirstMoment

/-!
# LANE G80J (#466, 2026-07-10): the DIVISOR SECOND MOMENT —
  `Σ_{y ≤ M} d(y)² ≤ M·(log₂M + 1)³` (axiom-clean pure Nat; KB §6 target).

## Content

* `sum_sq_card_divisors_eq` : exact identity
  `Σ_{y ≤ M} d(y)² = Σ_{(a,b) ∈ [1,M]²} ⌊M / lcm(a,b)⌋` (double count of common-multiple
  triples).
* `div_lcm_eq` : the per-pair collapse `M / lcm(a,b) = ((M/g)/a')/b'` with `g = gcd(a,b)`,
  `a' = a/g`, `b' = b/g` (from `lcm·g = a·b` and `Nat.div_div_eq_div_mul`).
* `sum_div_le_dyadic'` : the shifted first-moment bound `Σ_{a ∈ [1,M]} X/a ≤ X·(log₂M + 1)`
  for `X ≤ M` (terms with `a > X` vanish; G80K's dyadic bound applies).
* `sum_sq_card_divisors_le` (CAPSTONE) : `Σ_{y ≤ M} d(y)² ≤ M·(log₂M + 1)³` — inject pairs
  into gcd-triples (exact per-pair equality) and apply the dyadic harmonic bound three times.

## Payoff (with G80L)

`E×(A) ≤ Σ_{y ≤ W²} d(y)² ≤ W²·(log₂W² + 1)³` upgrades the energy consumer:
`T(W)⁴ ≤ n·W²·(2log₂W + 2)³`, i.e. `T(W) = O(n^{1/4}·√W·log^{3/4}W)` — NONTRIVIAL below the
`n^{2/3}` threshold where G80M dies (e.g. `T(n^{2/3}) = O(n^{7/12}·log^{3/4}n)`), extending
the unconditional window downward. Still fenced from the prize saddle by G80P. CORE remains
OPEN / ON-BGK.

Issue #466. Axiom-clean.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false


open Finset

namespace ArkLib.ProximityGap.Frontier.G80JDivisorSecondMoment

open ArkLib.ProximityGap.Frontier.G80KDivisorFirstMoment

/-- Exact identity: the divisor second moment is the lcm hyperbola sum. -/
theorem sum_sq_card_divisors_eq (M : ℕ) :
    ∑ y ∈ Finset.Icc 1 M, y.divisors.card ^ 2
      = ∑ ab ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M), M / Nat.lcm ab.1 ab.2 := by
  classical
  -- d(y)² = #{(a,b) ∈ [1,M]² : a ∣ y ∧ b ∣ y} for y ∈ [1,M]
  have hsq : ∀ y ∈ Finset.Icc 1 M, y.divisors.card ^ 2
      = (((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)).filter
          (fun ab => ab.1 ∣ y ∧ ab.2 ∣ y)).card := by
    intro y hy
    rw [Finset.mem_Icc] at hy
    have hdiv : y.divisors = (Finset.Icc 1 M).filter (fun a => a ∣ y) := by
      ext a
      rw [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hdvd, hy0⟩
        have ha0 : a ≠ 0 := by
          rintro rfl
          exact hy0 (Nat.eq_zero_of_zero_dvd hdvd)
        have haM : a ≤ M := le_trans (Nat.le_of_dvd (by omega) hdvd) hy.2
        exact ⟨⟨Nat.one_le_iff_ne_zero.mpr ha0, haM⟩, hdvd⟩
      · rintro ⟨⟨ha1, _⟩, hdvd⟩
        exact ⟨hdvd, by omega⟩
    rw [hdiv, sq, ← Finset.card_product]
    congr 1
    ext ⟨a, b⟩
    simp only [Finset.mem_product, Finset.mem_filter]
    tauto
  calc ∑ y ∈ Finset.Icc 1 M, y.divisors.card ^ 2
      = ∑ y ∈ Finset.Icc 1 M,
          (((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)).filter
            (fun ab => ab.1 ∣ y ∧ ab.2 ∣ y)).card := Finset.sum_congr rfl hsq
    _ = ∑ y ∈ Finset.Icc 1 M, ∑ ab ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
          (if ab.1 ∣ y ∧ ab.2 ∣ y then 1 else 0) :=
        Finset.sum_congr rfl fun y _ => Finset.card_filter _ _
    _ = ∑ ab ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M), ∑ y ∈ Finset.Icc 1 M,
          (if ab.1 ∣ y ∧ ab.2 ∣ y then 1 else 0) := Finset.sum_comm
    _ = ∑ ab ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
          ((Finset.Icc 1 M).filter (fun y => Nat.lcm ab.1 ab.2 ∣ y)).card := by
        refine Finset.sum_congr rfl fun ab _ => ?_
        rw [Finset.card_filter]
        refine Finset.sum_congr rfl fun y _ => ?_
        congr 1
        rw [eq_iff_iff]
        exact ⟨fun ⟨h1, h2⟩ => Nat.lcm_dvd h1 h2,
          fun h => ⟨dvd_trans (Nat.dvd_lcm_left _ _) h,
            dvd_trans (Nat.dvd_lcm_right _ _) h⟩⟩
    _ = ∑ ab ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M), M / Nat.lcm ab.1 ab.2 :=
        Finset.sum_congr rfl fun ab _ => card_dvd_Icc M _

/-- Per-pair collapse: `M / lcm(a,b) = ((M / g) / (a/g)) / (b/g)` with `g = gcd(a,b)`. -/
theorem div_lcm_eq {a b : ℕ} (ha : 1 ≤ a) (M : ℕ) :
    M / Nat.lcm a b = ((M / Nat.gcd a b) / (a / Nat.gcd a b)) / (b / Nat.gcd a b) := by
  have hg : 0 < Nat.gcd a b := Nat.pos_of_ne_zero fun h =>
    absurd (Nat.gcd_eq_zero_iff.mp h).1 (by omega)
  have hlcm : Nat.lcm a b = Nat.gcd a b * (a / Nat.gcd a b) * (b / Nat.gcd a b) := by
    have hgab : Nat.gcd a b ∣ a := Nat.gcd_dvd_left a b
    have hgbb : Nat.gcd a b ∣ b := Nat.gcd_dvd_right a b
    have := Nat.gcd_mul_lcm a b
    -- lcm = a*b/g = g·(a/g)·(b/g)
    have hab : a * b = Nat.gcd a b * (Nat.gcd a b * (a / Nat.gcd a b) * (b / Nat.gcd a b)) := by
      rw [show Nat.gcd a b * (Nat.gcd a b * (a / Nat.gcd a b) * (b / Nat.gcd a b))
          = (Nat.gcd a b * (a / Nat.gcd a b)) * (Nat.gcd a b * (b / Nat.gcd a b)) by ring,
        Nat.mul_div_cancel' hgab, Nat.mul_div_cancel' hgbb]
    have h2 : Nat.gcd a b * Nat.lcm a b
        = Nat.gcd a b * (Nat.gcd a b * (a / Nat.gcd a b) * (b / Nat.gcd a b)) := by
      rw [this, hab]
    exact Nat.eq_of_mul_eq_mul_left hg h2
  rw [hlcm, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_assoc]

/-- Shifted first-moment bound: `Σ_{a ∈ [1,M]} X/a ≤ X·(log₂M + 1)` for `X ≤ M`. -/
theorem sum_div_le_dyadic' {X M : ℕ} (hXM : X ≤ M) :
    ∑ a ∈ Finset.Icc 1 M, X / a ≤ X * (Nat.log 2 M + 1) := by
  have hzero : ∑ a ∈ Finset.Icc 1 M, X / a = ∑ a ∈ Finset.Icc 1 X, X / a := by
    symm
    refine Finset.sum_subset (Finset.Icc_subset_Icc_right hXM) ?_
    intro a ha hna
    rw [Finset.mem_Icc] at ha
    rw [Finset.mem_Icc] at hna
    exact Nat.div_eq_of_lt (by omega)
  rw [hzero]
  calc ∑ a ∈ Finset.Icc 1 X, X / a ≤ X * (Nat.log 2 X + 1) := sum_div_le_dyadic X
    _ ≤ X * (Nat.log 2 M + 1) := by
        have := Nat.log_mono_right (b := 2) hXM
        exact Nat.mul_le_mul_left X (by omega)

/-- **CAPSTONE — the divisor second moment**: `Σ_{y ≤ M} d(y)² ≤ M·(log₂M + 1)³`. -/
theorem sum_sq_card_divisors_le (M : ℕ) :
    ∑ y ∈ Finset.Icc 1 M, y.divisors.card ^ 2 ≤ M * (Nat.log 2 M + 1) ^ 3 := by
  classical
  rw [sum_sq_card_divisors_eq]
  -- inject pairs (a,b) into gcd-triples (g, a/g, b/g) with EXACT per-pair value equality
  have hinj : ∑ ab ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M), M / Nat.lcm ab.1 ab.2
      ≤ ∑ t ∈ (Finset.Icc 1 M) ×ˢ ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)),
          ((M / t.1) / t.2.1) / t.2.2 := by
    set φ : ℕ × ℕ → ℕ × (ℕ × ℕ) := fun ab =>
      (Nat.gcd ab.1 ab.2, (ab.1 / Nat.gcd ab.1 ab.2, ab.2 / Nat.gcd ab.1 ab.2)) with hφ
    have hval : ∀ ab ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        M / Nat.lcm ab.1 ab.2 = ((M / (φ ab).1) / (φ ab).2.1) / (φ ab).2.2 := by
      rintro ⟨a, b⟩ hab
      simp only [Finset.mem_product, Finset.mem_Icc] at hab
      exact div_lcm_eq hab.1.1 M
    have hinjective : Set.InjOn φ
        ((((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M) : Finset (ℕ × ℕ))) : Set (ℕ × ℕ)) := by
      rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd heq
      simp only [hφ, Prod.mk.injEq] at heq
      obtain ⟨hg, ha', hb'⟩ := heq
      have h1 : a = Nat.gcd a b * (a / Nat.gcd a b) :=
        (Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)).symm
      have h2 : c = Nat.gcd c d * (c / Nat.gcd c d) :=
        (Nat.mul_div_cancel' (Nat.gcd_dvd_left c d)).symm
      have h3 : b = Nat.gcd a b * (b / Nat.gcd a b) :=
        (Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)).symm
      have h4 : d = Nat.gcd c d * (d / Nat.gcd c d) :=
        (Nat.mul_div_cancel' (Nat.gcd_dvd_right c d)).symm
      have hac : a = c := by
        calc a = Nat.gcd a b * (a / Nat.gcd a b) := h1
          _ = Nat.gcd c d * (c / Nat.gcd c d) := by rw [ha', hg]
          _ = c := h2.symm
      have hbd : b = d := by
        calc b = Nat.gcd a b * (b / Nat.gcd a b) := h3
          _ = Nat.gcd c d * (d / Nat.gcd c d) := by rw [hb', hg]
          _ = d := h4.symm
      simp [hac, hbd]
    have hmapsto : ∀ ab ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        φ ab ∈ (Finset.Icc 1 M) ×ˢ ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)) := by
      rintro ⟨a, b⟩ hab
      simp only [Finset.mem_product, Finset.mem_Icc] at hab
      obtain ⟨⟨ha1, haM⟩, ⟨hb1, hbM⟩⟩ := hab
      have hg : 0 < Nat.gcd a b := Nat.pos_of_ne_zero fun h =>
        absurd (Nat.gcd_eq_zero_iff.mp h).1 (by omega)
      have hga : Nat.gcd a b ∣ a := Nat.gcd_dvd_left a b
      have hgb : Nat.gcd a b ∣ b := Nat.gcd_dvd_right a b
      have hgleA : Nat.gcd a b ≤ a := Nat.le_of_dvd (by omega) hga
      have ha'1 : 1 ≤ a / Nat.gcd a b := (Nat.one_le_div_iff hg).mpr hgleA
      have hb'1 : 1 ≤ b / Nat.gcd a b :=
        (Nat.one_le_div_iff hg).mpr (Nat.le_of_dvd (by omega) hgb)
      simp only [hφ, Finset.mem_product, Finset.mem_Icc]
      exact ⟨⟨hg, le_trans hgleA haM⟩,
        ⟨⟨ha'1, le_trans (Nat.div_le_self a _) haM⟩,
         ⟨hb'1, le_trans (Nat.div_le_self b _) hbM⟩⟩⟩
    calc ∑ ab ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M), M / Nat.lcm ab.1 ab.2
        = ∑ ab ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
            ((M / (φ ab).1) / (φ ab).2.1) / (φ ab).2.2 :=
          Finset.sum_congr rfl hval
      _ = ∑ t ∈ ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)).image φ,
            ((M / t.1) / t.2.1) / t.2.2 := by
            have himg := Finset.sum_image
              (f := fun t : ℕ × (ℕ × ℕ) => ((M / t.1) / t.2.1) / t.2.2)
              (g := φ) (s := (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)) (by
                intro x hx y hy hxy
                exact hinjective hx hy hxy)
            exact himg.symm
      _ ≤ ∑ t ∈ (Finset.Icc 1 M) ×ˢ ((Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)),
            ((M / t.1) / t.2.1) / t.2.2 := by
          refine Finset.sum_le_sum_of_subset ?_
          intro t ht
          rw [Finset.mem_image] at ht
          obtain ⟨ab, hab, rfl⟩ := ht
          exact hmapsto ab hab
  refine le_trans hinj ?_
  -- three nested dyadic harmonic bounds
  rw [Finset.sum_product]
  have hlvl2 : ∀ g ∈ Finset.Icc 1 M,
      ∑ ab ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M), ((M / g) / ab.1) / ab.2
        ≤ (M / g) * (Nat.log 2 M + 1) ^ 2 := by
    intro g hg
    rw [Finset.sum_product]
    have hinner : ∀ a ∈ Finset.Icc 1 M,
        ∑ b ∈ Finset.Icc 1 M, ((M / g) / a) / b
          ≤ ((M / g) / a) * (Nat.log 2 M + 1) := by
      intro a _
      exact sum_div_le_dyadic' (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))
    calc ∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 M, ((M / g) / a) / b
        ≤ ∑ a ∈ Finset.Icc 1 M, ((M / g) / a) * (Nat.log 2 M + 1) :=
          Finset.sum_le_sum hinner
      _ = (∑ a ∈ Finset.Icc 1 M, (M / g) / a) * (Nat.log 2 M + 1) := by
          rw [Finset.sum_mul]
      _ ≤ ((M / g) * (Nat.log 2 M + 1)) * (Nat.log 2 M + 1) := by
          exact Nat.mul_le_mul_right _ (sum_div_le_dyadic' (Nat.div_le_self _ _))
      _ = (M / g) * (Nat.log 2 M + 1) ^ 2 := by ring
  calc ∑ g ∈ Finset.Icc 1 M,
        ∑ ab ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M), ((M / g) / ab.1) / ab.2
      ≤ ∑ g ∈ Finset.Icc 1 M, (M / g) * (Nat.log 2 M + 1) ^ 2 :=
        Finset.sum_le_sum hlvl2
    _ = (∑ g ∈ Finset.Icc 1 M, M / g) * (Nat.log 2 M + 1) ^ 2 := by
        rw [Finset.sum_mul]
    _ ≤ (M * (Nat.log 2 M + 1)) * (Nat.log 2 M + 1) ^ 2 :=
        Nat.mul_le_mul_right _ (sum_div_le_dyadic M)
    _ = M * (Nat.log 2 M + 1) ^ 3 := by ring

end ArkLib.ProximityGap.Frontier.G80JDivisorSecondMoment

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G80JDivisorSecondMoment.sum_sq_card_divisors_eq
#print axioms
  ArkLib.ProximityGap.Frontier.G80JDivisorSecondMoment.div_lcm_eq
#print axioms
  ArkLib.ProximityGap.Frontier.G80JDivisorSecondMoment.sum_sq_card_divisors_le
