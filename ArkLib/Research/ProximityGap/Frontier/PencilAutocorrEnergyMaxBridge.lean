/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Research.ProximityGap.Frontier.PencilAutocorrSumDoubleCount
import ArkLib.Research.ProximityGap.Frontier.PencilAutocorrSubgroupExact
import ArkLib.ToMathlib.SupportSqBound

/-!
# The multiplicative-ENERGY lower bound on the worst autocorrelation (#407/#444)

`PencilAutocorrSumDoubleCount.autocorr_max_pigeonhole` gives the FIRST-moment lower bound on the
worst multiplicative autocorrelation `M = max_{ρ≠1} |S ∩ ρ·S|`:

  `|S|·(|S|−1) ≤ (|G|−1)·M`,   i.e.   `M ≥ |S|(|S|−1)/(|G|−1)`.

This file records the SECOND-moment (energy) relations.  With the two double-counts

  `∑_{ρ∈G} |S ∩ ρ·S| = |S|²`         (`autocorr_sum_eq_sq`),
  `∑_{ρ∈G} |S ∩ ρ·S|² = E_×(S)`      (the multiplicative energy),

the elementary bound `∑ a_ρ² ≤ (max_ρ a_ρ)·(∑ a_ρ)` gives

> `E_×(S) ≤ M₀ · |S|²` where `M₀` bounds `|S ∩ ρ·S|` for ALL `ρ ∈ G`
> (`mulEnergy_le_maxAutocorr_mul_sq`).

**Caveat: the all-shift maximum is trivial.**  The maximum over ALL shifts, including `ρ = 1`, is not
the object `M = max_{ρ≠1}` of the pigeonhole bound.  For EVERY finite `S` the identity shift gives
`|S ∩ 1·S| = |S|` (`autocorr_one_eq_card`), and every overlap is at most `|S|` (`autocorr_le_card`),
so `max_{ρ∈G} |S ∩ ρ·S| = |S|` regardless of energy or subgroup structure
(`card_le_of_forall_autocorr_le`).  Since `E_×(S) ≤ |S|³` always, the all-shift energy bound
`M₀ ≥ E_×(S)/|S|²` is never stronger than this trivial `M₀ ≥ |S|`, and it is NOT a sharpening of the
nontrivial-shift pigeonhole bound.  For example `S = {1, 2}` in `𝔽₇ˣ` has all-shift maximum `2`
while its maximum over nonidentity shifts is `1`.  In particular the subgroup conclusion
`|H| ≤ M₀` (`subgroup_maxAutocorr_ge_card`, `subgroup_maxAutocorr_ge_card_of_support`) follows
immediately from `hM₀ 1`; the energy and support proofs given for it are alternative derivations,
not evidence of a nontrivial rigidity phenomenon.

**The meaningful nontrivial energy bridge.**  Removing the identity contribution from both moment sums
gives, for any `M` bounding the overlaps at every `ρ ≠ 1`,

> `E_×(S) ≤ |S|² + M · |S|(|S| − 1)`,  i.e.  `E_×(S) − |S|² ≤ M · (|S|² − |S|)`
> (`mulEnergy_le_sq_add_maxNontrivial_mul`),

which holds for all finite `S` (including the empty and singleton cases, where both sides reduce to
`|S|²`).  This is the energy counterpart of `autocorr_max_pigeonhole`; it is a genuine constraint on
the nonidentity maximum.

The generic inequalities `sum_sq_le_max_mul_sum`, `mulEnergy_le_maxAutocorr_mul_sq`, and the
support-energy Cauchy–Schwarz floor below are correct and reusable.

**Honest scope.**  This is a sign-free additive/multiplicative-combinatorics structural brick: the
exact second-moment relation between the worst autocorrelation and the multiplicative energy.  It is
NOT a CORE closure, NOT thinness-essential (it holds for any finite group), and makes NO capacity /
beyond-Johnson / growth-law claim (ASYMPTOTIC GUARD untouched).  The all-shift statements do not
sharpen the nontrivial-shift pigeonhole lever (see the caveat above), and the prize
`M(n) ≤ C√(n log(p/n))` lives in the SIGNED character sum, which this does not touch.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.  Issues #407, #444.
-/

open Finset

namespace ProximityGap.Frontier.PencilAutocorrelation

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]

/-- **The elementary second-moment bound.**  For any nonnegative integer family `a : G → ℕ` over a
finite type, `∑ a ρ ^ 2 ≤ (sup over ρ of a ρ) · ∑ a ρ`: each term `a ρ ^ 2 = a ρ · a ρ ≤ M₀ · a ρ`.
This is the kernel of the energy↔max bridge, isolated so the autocorrelation specialization is a
one-line application. -/
theorem sum_sq_le_max_mul_sum (a : G → ℕ) {M₀ : ℕ} (hM₀ : ∀ ρ : G, a ρ ≤ M₀) :
    ∑ ρ : G, a ρ ^ 2 ≤ M₀ * ∑ ρ : G, a ρ := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun ρ _ => ?_)
  rw [pow_two]
  exact Nat.mul_le_mul_right _ (hM₀ ρ)

/-- The identity-shift overlap is the whole set: `|S ∩ 1·S| = |S|`. -/
theorem autocorr_one_eq_card (S : Finset G) : (S ∩ dilate (1 : G) S).card = S.card := by
  have : dilate (1 : G) S = S := by
    unfold dilate; simp
  rw [this, Finset.inter_self]

/-- Every autocorrelation overlap is at most `|S|`. -/
theorem autocorr_le_card (S : Finset G) (ρ : G) : (S ∩ dilate ρ S).card ≤ S.card :=
  Finset.card_le_card Finset.inter_subset_left

/-- **The all-shift maximum is trivially `|S|`.**  Any bound `M₀` on the overlaps at ALL shifts
(including `ρ = 1`) satisfies `|S| ≤ M₀`, for every finite set `S`; together with `autocorr_le_card`
this pins `max_{ρ∈G} |S ∩ ρ·S| = |S|` independently of energy or subgroup structure. -/
theorem card_le_of_forall_autocorr_le (S : Finset G) {M₀ : ℕ}
    (hM₀ : ∀ ρ : G, (S ∩ dilate ρ S).card ≤ M₀) : S.card ≤ M₀ :=
  autocorr_one_eq_card S ▸ hM₀ 1

/-- **The nontrivial-shift energy bridge.**  If `M` bounds the overlaps at every nonidentity shift,
then, removing the identity contribution `|S|²` from the energy and `|S|` from the first moment,

  `E_×(S) ≤ |S|² + M · |S|(|S| − 1)`,

i.e. `E_×(S) − |S|² ≤ M · (|S|² − |S|)`.  This holds for every finite `S` (for `|S| ≤ 1` both sides
are `|S|²`) and is the energy companion of `autocorr_max_pigeonhole`. -/
theorem mulEnergy_le_sq_add_maxNontrivial_mul (S : Finset G) {M : ℕ}
    (hM : ∀ ρ : G, ρ ≠ 1 → (S ∩ dilate ρ S).card ≤ M) :
    ∑ ρ : G, (S ∩ dilate ρ S).card ^ 2 ≤ S.card ^ 2 + M * (S.card * (S.card - 1)) := by
  classical
  have hsplit : ∑ ρ : G, (S ∩ dilate ρ S).card ^ 2
      = (S ∩ dilate (1 : G) S).card ^ 2
        + ∑ ρ ∈ Finset.univ.erase (1 : G), (S ∩ dilate ρ S).card ^ 2 := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : G))]
    ring
  have hnt : ∑ ρ ∈ Finset.univ.erase (1 : G), (S ∩ dilate ρ S).card ^ 2
      ≤ M * ∑ ρ ∈ Finset.univ.erase (1 : G), (S ∩ dilate ρ S).card := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun ρ hρ => ?_)
    rw [pow_two]
    exact Nat.mul_le_mul_right _ (hM ρ (Finset.ne_of_mem_erase hρ))
  rw [PencilAutocorrSumDoubleCount.autocorr_sum_nontrivial_eq] at hnt
  rw [hsplit, autocorr_one_eq_card]
  exact Nat.add_le_add_left hnt _

/-- **The multiplicative-energy upper bound by the worst autocorrelation.**  With the autocorrelation
double-count `∑_ρ |S ∩ ρS| = |S|²`, the energy `E_×(S) = ∑_ρ |S ∩ ρS|²` is at most `M₀·|S|²` where
`M₀` is the worst (over ALL `ρ`, including the trivial shift) autocorrelation:

  `E_×(S) ≤ M₀ · |S|²`. -/
theorem mulEnergy_le_maxAutocorr_mul_sq (S : Finset G) {M₀ : ℕ}
    (hM₀ : ∀ ρ : G, (S ∩ dilate ρ S).card ≤ M₀) :
    ∑ ρ : G, (S ∩ dilate ρ S).card ^ 2 ≤ M₀ * S.card ^ 2 := by
  have hsum := PencilAutocorrSumDoubleCount.autocorr_sum_eq_sq S
  calc
    ∑ ρ : G, (S ∩ dilate ρ S).card ^ 2
        ≤ M₀ * ∑ ρ : G, (S ∩ dilate ρ S).card :=
          sum_sq_le_max_mul_sum (fun ρ => (S ∩ dilate ρ S).card) hM₀
    _ = M₀ * S.card ^ 2 := by rw [hsum]

/-- **Subgroup all-shift bound via energy (an alternative derivation of a trivial fact).**  For a
nonempty multiplicative subgroup `H`, the energy bound `E_×(H) ≤ M₀·|H|²` combined with the exact
energy `E_×(H) = |H|³` gives `|H| ≤ M₀`.  Because `M₀` bounds the overlap at ALL shifts, including
`ρ = 1`, the same conclusion holds for every finite set directly from `hM₀ 1`
(`card_le_of_forall_autocorr_le`); this theorem therefore carries no subgroup-specific rigidity
information about the nonidentity shifts. -/
theorem subgroup_maxAutocorr_ge_card {H : Finset G} {M₀ : ℕ}
    (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    (hinv : ∀ a ∈ H, a⁻¹ ∈ H)
    (hne : H.Nonempty)
    (hM₀ : ∀ ρ : G, (H ∩ dilate ρ H).card ≤ M₀) :
    H.card ≤ M₀ := by
  have hEnergy : ∑ ρ : G, (H ∩ dilate ρ H).card ^ 2 = H.card ^ 3 :=
    subgroup_multiplicativeEnergy_eq_card_cube hmul hinv
  have hbound : ∑ ρ : G, (H ∩ dilate ρ H).card ^ 2 ≤ M₀ * H.card ^ 2 :=
    mulEnergy_le_maxAutocorr_mul_sq H hM₀
  rw [hEnergy] at hbound
  -- |H|^3 ≤ M₀·|H|^2 ⟹ |H| ≤ M₀ (cancel the positive |H|^2)
  have hpos : 0 < H.card ^ 2 := by
    have : 0 < H.card := Finset.card_pos.mpr hne
    positivity
  -- |H|^3 = |H|^2 · |H| and M₀·|H|^2 = |H|^2 · M₀; cancel |H|^2 on the left
  have hcube : H.card ^ 3 = H.card ^ 2 * H.card := by ring
  have hrhs : M₀ * H.card ^ 2 = H.card ^ 2 * M₀ := Nat.mul_comm _ _
  rw [hcube, hrhs] at hbound
  exact Nat.le_of_mul_le_mul_left hbound hpos

/-- **The Cauchy–Schwarz energy FLOOR by autocorrelation support.**  Dual to
`mulEnergy_le_maxAutocorr_mul_sq`: the multiplicative energy is bounded BELOW by `|S|⁴` divided by the
size of the autocorrelation support `{ρ : |S ∩ ρS| ≠ 0}`.  With the double-count `∑_ρ |S ∩ ρS| = |S|²`,
Cauchy–Schwarz `(∑ f)² ≤ #support · ∑ f²` gives

  `|S|⁴ ≤ (#autocorrelation-support) · E_×(S)`.

The fewer shifts carry the autocorrelation mass, the LARGER the energy must be — multiplicative
rigidity is exactly support-concentration of the unsigned overlap. -/
theorem sq_card_pow_le_support_mul_mulEnergy (S : Finset G) :
    (S.card ^ 2) ^ 2
      ≤ (Finset.univ.filter (fun ρ : G => (S ∩ dilate ρ S).card ≠ 0)).card
          * ∑ ρ : G, (S ∩ dilate ρ S).card ^ 2 := by
  have hsum := PencilAutocorrSumDoubleCount.autocorr_sum_eq_sq S
  have hcs := ArkLib.sq_sum_le_card_support_mul_sum_sq (fun ρ : G => (S ∩ dilate ρ S).card)
  rwa [hsum] at hcs

/-- **The support-aware pigeonhole bound for autocorrelation.**  If every nonzero autocorrelation
fiber is bounded by `M₀`, and only `K` shifts have a nonzero fiber, then the first double-count forces

  `|S|² ≤ K · M₀`,

where `K = #{ρ : |S ∩ ρS| ≠ 0}` is the autocorrelation-support size.  This is the exact support
version of the first-moment pigeonhole: a large set cannot have both small overlap fibers and small
dilation-difference support.  For a subgroup the support is `H` and the inequality becomes
`|H|² ≤ |H|·M₀`, hence again `|H| ≤ M₀` after cancellation (which, for the all-shift `M₀`, is
already immediate from the identity shift). -/
theorem sq_card_le_support_mul_maxAutocorr (S : Finset G) {M₀ : ℕ}
    (hM₀ : ∀ ρ : G, (S ∩ dilate ρ S).card ≤ M₀) :
    S.card ^ 2
      ≤ (Finset.univ.filter (fun ρ : G => (S ∩ dilate ρ S).card ≠ 0)).card * M₀ := by
  classical
  let f : G → ℕ := fun ρ => (S ∩ dilate ρ S).card
  let supp : Finset G := Finset.univ.filter (fun ρ : G => f ρ ≠ 0)
  have hsum_all : ∑ ρ : G, f ρ = S.card ^ 2 :=
    PencilAutocorrSumDoubleCount.autocorr_sum_eq_sq S
  have hsum_support : (∑ ρ : G, f ρ) = ∑ ρ ∈ supp, f ρ := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro ρ _ hρ
    simp only [f, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hρ
    exact hρ
  calc
    S.card ^ 2 = ∑ ρ : G, f ρ := hsum_all.symm
    _ = ∑ ρ ∈ supp, f ρ := hsum_support
    _ ≤ ∑ ρ ∈ supp, M₀ := by
      refine Finset.sum_le_sum ?_
      intro ρ _
      exact hM₀ ρ
    _ = supp.card * M₀ := by rw [Finset.sum_const, smul_eq_mul]

/-- **Consumer form of the support-aware autocorrelation pigeonhole.**  If a proposed uniform
autocorrelation cap `M₀` is too small for the actual autocorrelation support, namely
`#support · M₀ < |S|²`, then that cap cannot hold for every shift.  This is the direct contradiction
form needed when a Sidon/incidence argument supplies an upper bound on support size: one must still
pay enough maximum overlap mass to cover the first double-count. -/
theorem not_all_autocorr_le_of_support_mul_lt_sq_card (S : Finset G) {M₀ : ℕ}
    (hcap : (Finset.univ.filter (fun ρ : G => (S ∩ dilate ρ S).card ≠ 0)).card * M₀
      < S.card ^ 2) :
    ¬ ∀ ρ : G, (S ∩ dilate ρ S).card ≤ M₀ := by
  intro hM₀
  have hbound := sq_card_le_support_mul_maxAutocorr S hM₀
  exact Nat.not_lt_of_ge hbound hcap

/-- **Subgroup tightness of the Cauchy–Schwarz energy floor.**  For the prize object `S = H` (a
multiplicative subgroup), the autocorrelation support is EXACTLY `H` (`subgroup_autocorr_support`),
so `#support = |H|`, and the Cauchy–Schwarz floor `|H|⁴ ≤ #support · E_×(H)` becomes
`|H|⁴ ≤ |H| · |H|³ = |H|⁴` — an EQUALITY.  The subgroup SATURATES the Cauchy–Schwarz bound: its
unsigned multiplicative autocorrelation is maximally support-concentrated, the extremal rigid case. -/
theorem subgroup_support_card_eq (H : Finset G)
    (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    (hinv : ∀ a ∈ H, a⁻¹ ∈ H)
    (hne : H.Nonempty) :
    (Finset.univ.filter (fun ρ : G => (H ∩ dilate ρ H).card ≠ 0)).card = H.card := by
  have hset : Finset.univ.filter (fun ρ : G => (H ∩ dilate ρ H).card ≠ 0) = H := by
    ext ρ
    rw [Finset.mem_filter, subgroup_autocorr_support hmul hinv hne ρ]
    exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ ρ, h⟩⟩
  rw [hset]

/-- **Exact subgroup saturation of the support-energy Cauchy–Schwarz floor.**  The preceding two exact
subgroup identities (`#support = |H|` and `E_×(H)=|H|³`) multiply to the equality form of the
Cauchy–Schwarz floor:

  `#support(H) · E_×(H) = |H|⁴`.

Thus the floor in `sq_card_pow_le_support_mul_mulEnergy` is not merely sharp up to constants for the
thin subgroup; it is saturated on the nose.  This is still an unsigned autocorrelation statement, not a
signed Gauss-period / CORE closure. -/
theorem subgroup_support_mul_energy_eq_card_four (H : Finset G)
    (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    (hinv : ∀ a ∈ H, a⁻¹ ∈ H)
    (hne : H.Nonempty) :
    (Finset.univ.filter (fun ρ : G => (H ∩ dilate ρ H).card ≠ 0)).card
        * ∑ ρ : G, (H ∩ dilate ρ H).card ^ 2 = H.card ^ 4 := by
  rw [subgroup_support_card_eq H hmul hinv hne,
    subgroup_multiplicativeEnergy_eq_card_cube hmul hinv]
  ring
/-- **Subgroup all-shift bound from support-aware pigeonhole.**  For a multiplicative subgroup `H`,
the autocorrelation support has size exactly `|H|`; therefore the support-aware pigeonhole bound
gives `|H| ≤ M₀` (for nonempty `H`).  This is the first-moment support counterpart to
`subgroup_maxAutocorr_ge_card`.  As there, `M₀` bounds the identity-shift overlap `|H|`, so the
conclusion is immediate from `hM₀ 1` (`card_le_of_forall_autocorr_le`) and is not a nontrivial
subgroup rigidity statement. -/
theorem subgroup_maxAutocorr_ge_card_of_support {H : Finset G} {M₀ : ℕ}
    (hmul : ∀ a ∈ H, ∀ b ∈ H, a * b ∈ H)
    (hinv : ∀ a ∈ H, a⁻¹ ∈ H)
    (hne : H.Nonempty)
    (hM₀ : ∀ ρ : G, (H ∩ dilate ρ H).card ≤ M₀) :
    H.card ≤ M₀ := by
  have hbound := sq_card_le_support_mul_maxAutocorr H hM₀
  rw [subgroup_support_card_eq H hmul hinv hne] at hbound
  have hpos : 0 < H.card := Finset.card_pos.mpr hne
  have hsq : H.card ^ 2 = H.card * H.card := by ring
  rw [hsq] at hbound
  exact Nat.le_of_mul_le_mul_left hbound hpos



end ProximityGap.Frontier.PencilAutocorrelation

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
open ProximityGap.Frontier.PencilAutocorrelation in
#print axioms sum_sq_le_max_mul_sum
open ProximityGap.Frontier.PencilAutocorrelation in
#print axioms mulEnergy_le_maxAutocorr_mul_sq
open ProximityGap.Frontier.PencilAutocorrelation in
#print axioms card_le_of_forall_autocorr_le
open ProximityGap.Frontier.PencilAutocorrelation in
#print axioms mulEnergy_le_sq_add_maxNontrivial_mul
open ProximityGap.Frontier.PencilAutocorrelation in
#print axioms subgroup_maxAutocorr_ge_card
open ProximityGap.Frontier.PencilAutocorrelation in
#print axioms sq_card_pow_le_support_mul_mulEnergy
open ProximityGap.Frontier.PencilAutocorrelation in
#print axioms sq_card_le_support_mul_maxAutocorr
open ProximityGap.Frontier.PencilAutocorrelation in
#print axioms not_all_autocorr_le_of_support_mul_lt_sq_card
open ProximityGap.Frontier.PencilAutocorrelation in
#print axioms subgroup_maxAutocorr_ge_card_of_support
open ProximityGap.Frontier.PencilAutocorrelation in
#print axioms subgroup_support_card_eq
open ProximityGap.Frontier.PencilAutocorrelation in
#print axioms subgroup_support_mul_energy_eq_card_four
