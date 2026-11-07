/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Data.Set.PowersetCard
import ArkLib.ToMathlib.KoalaIRSAccounting

/-!
# Line-in-code lemmas for the concrete KoalaBear winning set (`#106`): conditional status

The leaderboard residual `ToyProblem.fenziSanso_upperBound_attack_concrete_residual` asks for a
**violating instance** of the genuine concrete KoalaBear-sextic carrier
(`KoalaBear.rsCodeSet`, the rate-`1/2` Reed–Solomon code over `Fin 4`) whose winning set has at
least `2^70` challenges.

**Status (audit 2026-10-28, finding L33).** This file was written to show that this residual is
unsatisfiable, through a cap `|Ω| ≤ C(4,3) = 4` on the winning set of every violating instance.
That claim is **false** for the in-tree relations, which quantify the encoding existentially: the
residual is **proved**, by a violating instance whose winning set is all of `F`
(`ArkLib.KoalaBearAttack.fenziSanso_upperBound_attack_concrete_residual_holds`), and the cap
fails (`ArkLib.KoalaBearAttack.not_forall_winningSet_ncard_le_four`). What this file proves is
valid but weaker: two linearity lemmas and two conditional wrappers. The cap remains plausible
for the paper's fixed-encoding winning set `ToyProblem.winningSetFor KoalaBear.rsEncoder`; that
version is not formalized here.

## The geometry, and where the argument stops

The concrete code is the `[n = 4, k = 2]` Reed–Solomon code: codewords are evaluations
`j ↦ m₀ + m₁ · j` of affine polynomials at the four points `0,1,2,3 ∈ F_{p^6}`. Its minimum
distance is `n − k + 1 = 3` (`KoalaBear.hammingDist_rsEncoder_ge_three`, proved for `#107`), so:

* **two points determine a codeword** (`KoalaBear.rsEncoder_agree_two_points_imp_eq`); and
* at `δ = 3/10` over `|ι| = 4`, the relaxed-relation agreement threshold is
  `⌈(1 − 3/10)·4⌉ = ⌈2.8⌉ = 3` coordinates.

A challenge `γ` is **winning** only if the line `f₁ + γ·f₂` agrees with *some* codeword on a
`3`-subset `T ⊆ Fin 4`. The codeword restrictions to a fixed `T` form a `2`-dimensional subspace
`V_T ⊆ F^T`; the affine line `{f₁|_T + γ·f₂|_T : γ}` is `1`-dimensional, so it meets `V_T` in **at
most one point** unless it lies entirely inside `V_T`. So two distinct winning challenges on a
common `3`-subset `T` force `f₁|_T` and `f₂|_T` to be codeword restrictions on `T`
(`KoalaBear.two_winning_same_subset_imp_lineInCode`).

The original argument then concluded that `T` is a common agreement set realising the relaxed
two-row relation `R̃²`, contradicting the violation. That step needs a single encoder under which
the two reconstructed messages satisfy **both** linear constraints:

* with the code's fixed encoder `rsEncoder` it goes through, because the reconstructed messages
  are linear combinations of the two winning messages and the constraints transport (this is why
  the cap is plausible for `winningSetFor KoalaBear.rsEncoder`);
* with the existential encoder of `ToyProblem.relaxedRelation` it fails: each winning challenge
  may use its own rank-one encoder, which ignores the constraint
  (`ToyProblem.mem_winningSet_iff_exists_agree`), and no single encoder need satisfy both zero
  constraints. In the KoalaBear attack instance every challenge wins on the same subset
  `T = {0, 1, 2}`, where the rows are the codewords `c₁, c₂`
  (`ArkLib.KoalaBearAttack.all_challenges_win`), yet the instance violates `R̃²`
  (`ArkLib.KoalaBearAttack.instance_violates`).

## What is proven here (axiom-clean)

* `KoalaBear.two_winning_same_subset_imp_lineInCode` — the line-in-code lemma: if two *distinct*
  challenges both put the line `f₁ + γ·f₂` onto codewords along a common coordinate set `T`, then
  both `f₁|_T` and `f₂|_T` are codeword restrictions on `T`. Pure `F`-linearity of `rsEncoder`. It
  holds for every `T` and says nothing about the linear constraints.
* `KoalaBear.winning_pair_eq_of_common_subset` — the same conclusion in conjunction form.
* `ToyProblem.winningSet_ncard_le_four_of_injective_threeSubsets` — counting wrapper: an injection
  of the winning set into the four `3`-subsets gives `|Ω| ≤ 4`. No such injection exists for the
  attack instance.
* `ToyProblem.not_fenziSanso_concrete_residual_of_ncard_le_four` — arithmetic wrapper
  `(∀ x, |Ω_x| ≤ 4) → ¬ residual`. Its hypothesis is false, so it is vacuous.

The minimum-distance facts quoted above are proved in `ArkLib/ToMathlib/KoalaIRSAccounting.lean`
(`KoalaBear.rsEncoder_agree_two_points_imp_eq`, `#107`); the lemmas below do not need them.

## References

* Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and Correlated Agreement*
  (eprint 2026/680), §6.3–§6.4.
-/

namespace KoalaBear

open scoped NNReal

/-- **Line-in-code lemma for the `#106` analysis.**

Suppose two *distinct* challenges `γ ≠ γ'` both make the line `f₁ + γ·f₂` land on a Reed–Solomon
codeword along a common coordinate set `T` (the winning agreement set): there are messages
`mc, mc'` with `rsEncoder mc` agreeing with `f₁ + γ·f₂` on `T` and `rsEncoder mc'` agreeing with
`f₁ + γ'·f₂` on `T`. Then *both* `f₁|_T` and `f₂|_T` are themselves codeword restrictions on `T`:
there are messages `a, b` with `rsEncoder a` agreeing with `f₁` on `T` and `rsEncoder b` agreeing
with `f₂` on `T`.

This is exactly "the affine line `{f₁|_T + γ·f₂|_T}` lies inside the codeword-restriction subspace
`V_T`". It concerns the words only, not the linear constraints. For the fixed encoder the
constraints transport to `a, b` as well, which would give a common two-row agreement set and the
at-most-one-winner-per-`3`-subset cap for `winningSetFor rsEncoder` (not formalized here). For the
existential `winningSet` no such transport exists and the cap is false
(`ArkLib.KoalaBearAttack.not_forall_winningSet_ncard_le_four`).

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

/-- **Conjunction form of `two_winning_same_subset_imp_lineInCode`.**

If two *distinct* challenges `γ ≠ γ'` both win along a common coordinate set `T` (witnessed by
codewords `rsEncoder mc`, `rsEncoder mc'`), then there are messages `a, b` with
`rsEncoder a = f₁` and `rsEncoder b = f₂` at every coordinate of `T`.

The statement holds for every `T`, and it is informative only when `|T| ≥ 3`: any two
coordinates of this `[4, 2]` code can be interpolated, so for `|T| ≤ 2` the conclusion holds for
all `f₁, f₂`. (The violation of `R̃²` at `δ = 3/10` concerns common agreement sets of size `≥ 3`,
not `2`.) Even on a `3`-subset the conclusion constrains only the words, not the linear
constraints, so by itself it does not exclude a violating instance of the existential-encoding
relation; see the module docstring. -/
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

This is the finite-combinatorics wrapper that would follow a uniqueness argument
assigning each winning challenge to a distinguishing `3`-coordinate agreement set.
The injection `pick` is a hypothesis. For the existential-encoding `winningSet` used
here it does not exist in general: the KoalaBear attack instance has `|Ω| = |F|`
(`ArkLib.KoalaBearAttack.attackInstance_winningSet_eq_univ`). -/
theorem winningSet_ncard_le_four_of_injective_threeSubsets
    (x : ExistentialEncoding.ViolatingInstance KoalaBear.rsCodeSet (3 / 10) 2)
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

/-- **Conditional wrapper (vacuous).** A uniform cap `|Ω| ≤ 4` on the winning sets of
violating instances would refute the concrete Fenzi–Sanso leaderboard residual, since
`4 < 2^70`.

The cap is **false** for the existential-encoding `winningSet` used here
(`ArkLib.KoalaBearAttack.not_forall_winningSet_ncard_le_four`), and the residual itself
is **proved** (`ArkLib.KoalaBearAttack.fenziSanso_upperBound_attack_concrete_residual_holds`).
The structural lemmas above cannot be upgraded into `hcap`; this valid implication is kept
as a record of the abandoned route. -/
theorem not_fenziSanso_concrete_residual_of_ncard_le_four
    (hcap :
      ∀ x : ExistentialEncoding.ViolatingInstance KoalaBear.rsCodeSet (3 / 10) 2,
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
