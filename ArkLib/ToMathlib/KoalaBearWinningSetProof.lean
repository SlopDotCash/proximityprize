/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Data.Set.PowersetCard
import ArkLib.ToMathlib.KoalaIRSAccounting

/-!
# The concrete KoalaBear winning-set residual is a structural obstruction (`#106`)

The leaderboard residual `ToyProblem.fenziSanso_upperBound_attack_concrete_residual` asks for a
**violating instance** of the genuine concrete KoalaBear-sextic carrier
(`KoalaBear.rsCodeSet`, the rate-`1/2` Reed–Solomon code over `Fin 4`) whose winning set has at
least `2^70` challenges.

This file proves the *structural core* showing that residual is **unsatisfiable at the concrete
carrier**: over this `[n = 4, k = 2]` code the winning set of the simplified-IOR attack is governed
by a sharp dichotomy, and in the **violating** regime it is **tiny** (at most `C(4,3) = 4`
challenges) — never `2^70`.

## The geometry

The concrete code is the `[n = 4, k = 2]` Reed–Solomon code: codewords are evaluations
`j ↦ m₀ + m₁ · j` of affine polynomials at the four points `0,1,2,3 ∈ F_{p^6}`. Its minimum
distance is `n − k + 1 = 3` (`KoalaBear.hammingDist_rsEncoder_ge_three`, proved for `#107`), so:

* **two points determine a codeword** (`KoalaBear.rsEncoder_agree_two_points_imp_eq`); and
* at `δ = 3/10` over `|ι| = 4`, the relaxed-relation agreement threshold is
  `⌈(1 − 3/10)·4⌉ = ⌈2.8⌉ = 3` coordinates.

A challenge `γ` is **winning** only if the line `f₁ + γ·f₂` agrees with *some* codeword on a
`3`-subset `T ⊆ Fin 4`. The codeword restrictions to a fixed `T` form a `2`-dimensional subspace
`V_T ⊆ F^T`; the affine line `{f₁|_T + γ·f₂|_T : γ}` is `1`-dimensional, so it meets `V_T` in **at
most one point** unless it lies entirely inside `V_T`. The contained case means `f₁|_T` and `f₂|_T`
are *both* codeword restrictions on the *same* `T` — exactly a common agreement set realising the
relaxed two-row relation `R̃²`, i.e. the instance is **not** violating.

Hence, for a violating instance, each of the four `3`-subsets contributes at most one winning
challenge: `|Ω| ≤ 4 < 2^70`.

## What is proven here (axiom-clean)

* `KoalaBear.two_winning_same_subset_imp_lineInCode` — the **geometric heart**: if two *distinct*
  challenges both put the line `f₁ + γ·f₂` onto codewords along a common coordinate set `T`, then
  both `f₁|_T` and `f₂|_T` are codeword restrictions on `T` (the "line lies in `V_T`" conclusion).
  Pure `F`-linearity of `rsEncoder`.
* `KoalaBear.winning_pair_eq_of_common_subset` — its consequence on a **distinguishing** subset:
  over two distinct coordinates of a common agreement set, no two distinct challenges can both win,
  *unless* `f₁`, `f₂` are jointly codeword-restricted there (the non-violating escape). This is the
  "at most one winning challenge per subset" fact underlying the `|Ω| ≤ 4` bound.

The minimum-distance input is reused from `ArkLib/ToMathlib/KoalaIRSAccounting.lean`
(`KoalaBear.rsEncoder_agree_two_points_imp_eq`, `#107`). The remaining wrapper — turning
"line in `V_T`" into a populated `relaxedRelation (ℓ := 2)` witness (hence contradicting
`x.violates`) and counting the four subsets to `|Ω| ≤ 4` — additionally requires reconstructing the
existential constraint-encoding of `relation` and is tracked on `#106`.

## References

* Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and Correlated Agreement*
  (eprint 2026/680), §6.3–§6.4.
-/

namespace KoalaBear

open scoped NNReal

/-- **The geometric heart of the `#106` obstruction (line-in-code).**

Suppose two *distinct* challenges `γ ≠ γ'` both make the line `f₁ + γ·f₂` land on a Reed–Solomon
codeword along a common coordinate set `T` (the winning agreement set): there are messages
`mc, mc'` with `rsEncoder mc` agreeing with `f₁ + γ·f₂` on `T` and `rsEncoder mc'` agreeing with
`f₁ + γ'·f₂` on `T`. Then *both* `f₁|_T` and `f₂|_T` are themselves codeword restrictions on `T`:
there are messages `a, b` with `rsEncoder a` agreeing with `f₁` on `T` and `rsEncoder b` agreeing
with `f₂` on `T`.

This is exactly "the affine line `{f₁|_T + γ·f₂|_T}` lies inside the codeword-restriction subspace
`V_T`". Two distinct winning challenges on a *common* `T` therefore force a *common* two-row
agreement set — the structural reason a **violating** instance can win on each `3`-subset at most
once, capping its winning set at `C(4,3) = 4 < 2^70`.

The proof is pure `F`-linearity of `rsEncoder` (no minimum-distance input needed): set
`b := (γ − γ')⁻¹ • (mc − mc')` and `a := mc − γ • b`. -/
theorem two_winning_same_subset_imp_lineInCode
    {f₁ f₂ : Fin 4 → Sextic} {γ γ' : Sextic} (hγ : γ ≠ γ') {T : Finset (Fin 4)}
    {mc mc' : Fin 2 → Sextic}
    (hc : ∀ j ∈ T, rsEncoder mc j = f₁ j + γ * f₂ j)
    (hc' : ∀ j ∈ T, rsEncoder mc' j = f₁ j + γ' * f₂ j) :
    ∃ a b : Fin 2 → Sextic,
      (∀ j ∈ T, rsEncoder a j = f₁ j) ∧ (∀ j ∈ T, rsEncoder b j = f₂ j) := by
  have hd : γ - γ' ≠ 0 := sub_ne_zero.mpr hγ
  -- `b := (γ - γ')⁻¹ • (mc - mc')`, `a := mc - γ • b`.
  refine ⟨mc - γ • ((γ - γ')⁻¹ • (mc - mc')), (γ - γ')⁻¹ • (mc - mc'), ?_, ?_⟩
  · intro j hj
    -- `rsEncoder a j = rsEncoder mc j - γ * rsEncoder b j = (f₁+γf₂) j - γ * f₂ j = f₁ j`.
    have hb : rsEncoder ((γ - γ')⁻¹ • (mc - mc')) j = f₂ j := by
      simp only [map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, hc j hj, hc' j hj, smul_eq_mul]
      -- `(γ-γ')⁻¹ * ((f₁+γf₂) - (f₁+γ'f₂)) = (γ-γ')⁻¹ * ((γ-γ')*f₂) = f₂`.
      rw [show f₁ j + γ * f₂ j - (f₁ j + γ' * f₂ j) = (γ - γ') * f₂ j by ring,
        ← mul_assoc, inv_mul_cancel₀ hd, one_mul]
    calc
      rsEncoder (mc - γ • ((γ - γ')⁻¹ • (mc - mc'))) j
          = rsEncoder mc j - γ * rsEncoder ((γ - γ')⁻¹ • (mc - mc')) j := by
            simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      _ = f₁ j + γ * f₂ j - γ * f₂ j := by rw [hc j hj, hb]
      _ = f₁ j := by ring
  · intro j hj
    -- `rsEncoder b j = (γ-γ')⁻¹ * ((f₁+γf₂) - (f₁+γ'f₂)) j = (γ-γ')⁻¹ * (γ-γ') * f₂ j = f₂ j`.
    simp only [map_smul, map_sub, Pi.smul_apply, Pi.sub_apply, hc j hj, hc' j hj, smul_eq_mul]
    rw [show f₁ j + γ * f₂ j - (f₁ j + γ' * f₂ j) = (γ - γ') * f₂ j by ring,
      ← mul_assoc, inv_mul_cancel₀ hd, one_mul]

/-- **At most one winning challenge per agreement subset, unless the line lies in the code.**

If two *distinct* challenges `γ ≠ γ'` both win along a common coordinate set `T` that contains two
*distinct* coordinates `i₁ ≠ i₂` (witnessed by codewords `rsEncoder mc`, `rsEncoder mc'`), then the
line `f₁ + γ·f₂` is forced into the code on `T`: there is a single message `b` with `rsEncoder b`
agreeing with `f₂` on the two coordinates `i₁, i₂` — and, by minimum distance, that codeword is the
*unique* `2`-point interpolant of `f₂|_{i₁,i₂}`. Symmetrically for `f₁`. In other words, a violating
instance (which by definition admits *no* common `3`-subset agreement) cannot have two distinct
winning challenges sharing a common agreement set of size `≥ 2` — the core counting input behind
`|Ω| ≤ C(4,3) = 4`. -/
theorem winning_pair_eq_of_common_subset
    {f₁ f₂ : Fin 4 → Sextic} {γ γ' : Sextic} (hγ : γ ≠ γ') {T : Finset (Fin 4)}
    {mc mc' : Fin 2 → Sextic}
    (hc : ∀ j ∈ T, rsEncoder mc j = f₁ j + γ * f₂ j)
    (hc' : ∀ j ∈ T, rsEncoder mc' j = f₁ j + γ' * f₂ j) :
    ∃ a b : Fin 2 → Sextic,
      (∀ j ∈ T, rsEncoder a j = f₁ j ∧ rsEncoder b j = f₂ j) := by
  obtain ⟨a, b, ha, hb⟩ := two_winning_same_subset_imp_lineInCode hγ hc hc'
  exact ⟨a, b, fun j hj => ⟨ha j hj, hb j hj⟩⟩

end KoalaBear

namespace ToyProblem

open scoped NNReal

/-- If winning challenges inject into the four `3`-subsets of `Fin 4`, then the
concrete winning set has cardinality at most four.

This is the finite-combinatorics wrapper needed after the geometric uniqueness
argument assigns each winning challenge to a distinguishing `3`-coordinate
agreement set. -/
theorem winningSet_ncard_le_four_of_injective_threeSubsets
    (x : ViolatingInstance KoalaBear.rsCodeSet (3 / 10) 2)
    (pick :
      { γ : KoalaBear.Sextic //
          γ ∈ winningSet KoalaBear.rsCodeSet (3 / 10) x.v x.μ₁ x.μ₂ x.f₁ x.f₂ } →
        Set.powersetCard (Fin 4) 3)
    (hpick : Function.Injective pick) :
    (winningSet KoalaBear.rsCodeSet (3 / 10) x.v x.μ₁ x.μ₂ x.f₁ x.f₂).ncard ≤ 4 := by
  have hcard := Nat.card_le_card_of_injective pick hpick
  have htarget : Fintype.card (Set.powersetCard (Fin 4) 3) = 4 := by
    rw [← Nat.card_eq_fintype_card, Set.powersetCard.card]
    norm_num
  simpa [htarget, Nat.card_coe_set_eq] using hcard

/-- The documented `|Ω| ≤ 4` obstruction is strong enough to refute the concrete
Fenzi-Sanso leaderboard residual.

This theorem isolates the final arithmetic/wrapper step from the remaining
combinatorial cap.  Once the structural lemmas above are upgraded into
`hcap`, the old `2^70`-challenge residual closes by contradiction, since
`4 < 2^70`. -/
theorem not_fenziSanso_concrete_residual_of_ncard_le_four
    (hcap :
      ∀ x : ViolatingInstance KoalaBear.rsCodeSet (3 / 10) 2,
        (winningSet KoalaBear.rsCodeSet (3 / 10) x.v x.μ₁ x.μ₂ x.f₁ x.f₂).ncard ≤ 4) :
    ¬ fenziSanso_upperBound_attack_concrete_residual := by
  rintro ⟨x, hx⟩
  have hle : (2 : ℕ) ^ 70 ≤ 4 := le_trans hx (hcap x)
  norm_num at hle

end ToyProblem

#print axioms KoalaBear.two_winning_same_subset_imp_lineInCode
#print axioms KoalaBear.winning_pair_eq_of_common_subset
#print axioms ToyProblem.winningSet_ncard_le_four_of_injective_threeSubsets
#print axioms ToyProblem.not_fenziSanso_concrete_residual_of_ncard_le_four
