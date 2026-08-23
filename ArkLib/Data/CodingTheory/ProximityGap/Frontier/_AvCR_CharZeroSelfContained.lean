/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import ArkLib.Data.CodingTheory.ProximityGap.NegationClosedWalkBound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvF1_BesselMfoldSymbolic
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvCR_MutuallyDecoupled
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvCR_NatConvBessel

/-!
# The char-0 Wick bound made FULLY SELF-CONTAINED (#444, avenue CR, capstone)

This brick COMPOSES the now-proven abstract char-0 chain into a single theorem with **no named
hypothesis**, for any family of disjoint negation-closed antipodal-pair directions of `2^k`-th roots:

  `E_r^{char0}(⋃ D) = zeroSumCount (⋃ D) (2r) ≤ (2r−1)‼·n^r`   where `n = 2·(#directions)`.

The chain it composes (each piece already axiom-clean in its own brick):

* `AvCR.mutuallyDecoupled_of_antipodalDirections` — disjoint negation-closed `2^k`-root
  directions are `MutuallyDecoupled` (Lam–Leung, R1).
* `AvF1.zeroSumCount_iUnion_eq_natConv` — the `m`-fold decoupling induction:
  `zeroSumCount (unionUpto D m) N = natConv f m N` given per-direction count `f`.
* `AvCR.natConv_negDirCount_eq_Edef` — the symbolic-`d` natConv↔Bessel bridge (R2):
  `natConv negDirCount d (2r) = AvW0.Edef r d`.
* `AvW0.charZero_wick_bound` — the Bessel coefficient domination:
  `Edef r m ≤ (2r−1)‼·(2m)^r`.

The single combinatorial fact proved here in addition is the **general per-direction count**
`zeroSumCount {w, −w} N = negDirCount N` for any `w ≠ 0` (the `_AvUC` `{1,−1}` count rescaled by
`w`), so the family directions may be the genuine antipodal pairs `{ζ^j, −ζ^j}` of the `2^μ`-th
roots, not just `{1,−1}`.

## Honest scope (#444)

This is the **char-0 layer ONLY**, and is NOT prize closure. Over `𝔽_p` the identity
`E_r^{𝔽_p} = E_r^{char0} + W_r` carries a wraparound excess `W_r` that is positive once `r ≥ r₀(n)`
(`r₀ ≈ ln p` at prize scale): the prize lives at the moment-saddle `r ≈ ln p` where `W_r > 0`, the
BGK wall, untouched here. What IS landed: the char-0 Wick bound is now a self-contained theorem with
**no named hypothesis** — every input (`MutuallyDecoupled`, the Bessel identity, the convolution
bridge) is discharged inside the chain.

The concrete `μ_n = nthRootsFinset (2^μ)` instantiation requires, additionally, exhibiting the `m`
antipodal directions `{ζ^j, −ζ^j}` of a primitive `2^μ`-th root with `unionUpto D m = μ_n`
(disjoint + covering). That root-of-unity bookkeeping is recorded as the hypotheses of the
`charZeroWick_selfContained` capstone (negation-closed, disjoint, `2^k`-root, per-direction count) —
all of which the `μ_n` family satisfies verbatim — rather than re-derived from a primitive root here.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`, no `native_decide`.
-/

set_option linter.style.longLine false
set_option autoImplicit false

open Finset
open scoped Nat
open ArkLib.ProximityGap.NegationClosedWalk
open ArkLib.ProximityGap.Frontier.AvRem
open ArkLib.ProximityGap.Frontier.AvF1
open ArkLib.ProximityGap.Frontier.AvCR
open ArkLib.ProximityGap.Frontier.AvW0

namespace ArkLib.ProximityGap.Frontier.AvCRSelfContained

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## The general per-direction count: `zeroSumCount {w,−w} N = negDirCount N` for `w ≠ 0`.

We reduce to the proven `_AvUC` count for `{1,−1}` by the rescaling bijection `c ↦ (i ↦ c i / w)`,
which sends a `{w,−w}`-tuple to a `{1,−1}`-tuple and (as `w ≠ 0`) preserves the zero-sum property. -/

/-- The antipodal direction `{w, −w}`. -/
def antiPair (w : F) : Finset F := {w, -w}

@[simp] lemma mem_antiPair {w x : F} : x ∈ antiPair w ↔ x = w ∨ x = -w := by
  unfold antiPair; simp [Finset.mem_insert, Finset.mem_singleton]

/-- `antiPair w` is negation-closed. -/
theorem negClosed_antiPair (w : F) : AvCR.NegClosed (antiPair w) := by
  intro x hx
  rw [mem_antiPair] at hx
  rcases hx with rfl | rfl
  · simp [mem_antiPair]
  · simp [mem_antiPair]

omit [DecidableEq F] in
private lemma neg_ne {w : F} [CharZero F] (hw : w ≠ 0) : w ≠ -w := by
  intro h; apply hw
  have : (2:F) * w = 0 := by rw [two_mul]; nth_rewrite 2 [h]; ring
  rcases mul_eq_zero.mp this with h2 | h2
  · exact absurd h2 two_ne_zero
  · exact h2

/-- The `+w` / `−w` position split of a tuple landing in `antiPair w`. -/
private lemma split_card [CharZero F] {N : ℕ} (w : F) (hw : w ≠ 0) (c : Fin N → F)
    (hmem : ∀ i, c i ∈ antiPair w) :
    (Finset.univ.filter (fun i => c i = w)).card
        + (Finset.univ.filter (fun i => c i = -w)).card = N := by
  classical
  set P := Finset.univ.filter (fun i => c i = w) with hP
  set Nn := Finset.univ.filter (fun i => c i = -w) with hN
  have hwne : w ≠ -w := neg_ne hw
  have hdisj : Disjoint P Nn := by
    rw [Finset.disjoint_filter]; intro i _ h1 h2; exact hwne (h1.symm.trans h2)
  have hunion : P ∪ Nn = Finset.univ := by
    apply Finset.eq_univ_of_forall; intro i
    rcases mem_antiPair.mp (hmem i) with h1 | h1
    · exact Finset.mem_union_left _ (by rw [hP]; simp [h1])
    · exact Finset.mem_union_right _ (by rw [hN]; simp [h1])
  have := Finset.card_union_of_disjoint hdisj
  rw [hunion] at this
  simp only [Finset.card_univ, Fintype.card_fin] at this; omega

/-- **The general single-direction count.** For any `w ≠ 0` in a characteristic-`0` field, the
antipodal direction `{w, −w}` has zero-sum count `negDirCount N` (central binomial on even `N`,
`0` on odd `N`). Same argument as the `_AvUC` `{1,−1}` count: a zero-sum `{w,−w}`-tuple has
`#{+w}·w − #{−w}·w = 0`, so (as `w ≠ 0`, char `0`) `#{+w} = #{−w}`, bijecting zero-sum tuples with
`(N/2)`-subsets of positions. -/
theorem zeroSumCount_antiPair [CharZero F] (w : F) (hw : w ≠ 0) (N : ℕ) :
    zeroSumCount (antiPair w) N = negDirCount N := by
  classical
  -- The sum of a tuple in {w,-w} is (#pos - #neg)·w; zero iff #pos = #neg.
  have hsum_eq : ∀ (c : Fin N → F), (∀ i, c i ∈ antiPair w) →
      (∑ i, c i = ((Finset.univ.filter (fun i => c i = w)).card : F) * w
                - ((Finset.univ.filter (fun i => c i = -w)).card : F) * w) := by
    intro c hmem
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => c i = w) c]
    have hpart1 : ∑ i ∈ Finset.univ.filter (fun i => c i = w), c i
        = ((Finset.univ.filter (fun i => c i = w)).card : F) * w := by
      rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2), Finset.sum_const,
        nsmul_eq_mul]
    have hwne : w ≠ -w := neg_ne hw
    have hcongr : Finset.univ.filter (fun i => ¬ c i = w) = Finset.univ.filter (fun i => c i = -w) := by
      apply Finset.filter_congr; intro i _
      rcases mem_antiPair.mp (hmem i) with h1 | h1 <;> rw [h1]
      · constructor
        · intro hcon; exact absurd rfl hcon
        · intro hcon; exact absurd hcon hwne
      · constructor
        · intro _; rfl
        · intro _ hcon; exact hwne (by rw [hcon])
    have hpart2 : ∑ i ∈ Finset.univ.filter (fun i => ¬ c i = w), c i
        = -(((Finset.univ.filter (fun i => c i = -w)).card : F) * w) := by
      rw [hcongr, Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2), Finset.sum_const,
        nsmul_eq_mul, mul_neg]
    rw [hpart1, hpart2]; ring
  rcases Nat.even_or_odd N with ⟨r, hr⟩ | ⟨r, hr⟩
  · -- even: bijection with r-subsets of Fin (2r).
    have hr2 : N = 2 * r := by omega
    subst hr2
    rw [negDirCount_two_mul, Nat.centralBinom_eq_two_mul_choose]
    unfold zeroSumCount
    have hcarduniv : ((2 * r).choose r)
        = (Finset.powersetCard r (Finset.univ : Finset (Fin (2 * r)))).card := by
      rw [Finset.card_powersetCard]; simp
    rw [hcarduniv]
    refine Finset.card_bij'
      (fun c _ => (Finset.univ.filter (fun i => c i = w)))
      (fun S _ => (fun i => if i ∈ S then w else -w))
      ?_ ?_ ?_ ?_
    · -- forward: zero-sum tuple ↦ r-subset
      intro c hc
      simp only [Finset.mem_filter, Fintype.mem_piFinset] at hc
      obtain ⟨hmem, hsum⟩ := hc
      simp only [Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ _, ?_⟩
      have hsplit := split_card w hw c hmem
      have heq : ((Finset.univ.filter (fun i => c i = w)).card : F) * w
          = ((Finset.univ.filter (fun i => c i = -w)).card : F) * w := by
        have := hsum_eq c hmem; rw [hsum] at this; linear_combination -this
      have hcardeq : (Finset.univ.filter (fun i => c i = w)).card
          = (Finset.univ.filter (fun i => c i = -w)).card := by
        have hwc : ((Finset.univ.filter (fun i => c i = w)).card : F)
            = ((Finset.univ.filter (fun i => c i = -w)).card : F) :=
          mul_right_cancel₀ hw heq
        exact_mod_cast hwc
      omega
    · -- backward: r-subset ↦ tuple lands in piFinset, zero-sum
      intro S hS
      simp only [Finset.mem_powersetCard] at hS
      obtain ⟨_, hScard⟩ := hS
      simp only [Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨?_, ?_⟩
      · intro i; by_cases h : i ∈ S <;> simp [h, mem_antiPair]
      · have hval : ∑ i, (if i ∈ S then w else -w)
            = (S.card : F) * w - (((Finset.univ : Finset (Fin (2*r))) \ S).card : F) * w := by
          rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
          rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
          have hnot : (Finset.univ.filter (fun i => i ∉ S)) = (Finset.univ : Finset (Fin (2*r))) \ S := by
            ext i; simp [Finset.mem_sdiff]
          rw [hnot]; simp only [nsmul_eq_mul, mul_neg]; ring
        rw [hval, Finset.card_sdiff_of_subset (Finset.subset_univ S)]
        have hcardu : (Finset.univ : Finset (Fin (2*r))).card = 2 * r := by simp
        rw [hcardu, hScard]
        have h2r : (2 * r - r : ℕ) = r := by omega
        rw [h2r]; ring
    · -- left inverse
      intro c hc
      simp only [Finset.mem_filter, Fintype.mem_piFinset] at hc
      obtain ⟨hmem, _⟩ := hc
      funext i
      have hmemf : (i ∈ Finset.univ.filter (fun j => c j = w)) ↔ c i = w := by simp [Finset.mem_filter]
      simp only [hmemf]
      by_cases h : c i = w
      · rw [if_pos h, h]
      · have hci : c i = -w := (mem_antiPair.mp (hmem i)).resolve_left h
        rw [if_neg h, hci]
    · -- right inverse
      intro S hS
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hwne : w ≠ -w := neg_ne hw
      by_cases h : i ∈ S
      · simp [h]
      · rw [if_neg h]; constructor <;> intro hh
        · exact absurd hh (fun hcon => hwne hcon.symm)
        · exact absurd hh h
  · -- odd: no zero-sum tuple (count 0).
    have hr2 : N = 2 * r + 1 := by omega
    subst hr2
    rw [negDirCount_odd]
    unfold zeroSumCount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro c hc
    simp only [Fintype.mem_piFinset] at hc
    intro hsum
    have hsplit := split_card w hw c hc
    have heq : ((Finset.univ.filter (fun i => c i = w)).card : F) * w
        = ((Finset.univ.filter (fun i => c i = -w)).card : F) * w := by
      have := hsum_eq c hc; rw [hsum] at this; linear_combination -this
    have hcardeq : (Finset.univ.filter (fun i => c i = w)).card
        = (Finset.univ.filter (fun i => c i = -w)).card := by
      have hwc : ((Finset.univ.filter (fun i => c i = w)).card : F)
          = ((Finset.univ.filter (fun i => c i = -w)).card : F) := mul_right_cancel₀ hw heq
      exact_mod_cast hwc
    omega

/-! ## THE CAPSTONE: the fully self-contained char-0 Wick bound (no named hypothesis). -/

/-- **THE CAPSTONE — char-0 Wick bound, FULLY SELF-CONTAINED.** Given a family `D : Fin m → Finset F`
of `m` directions over a field of characteristic `0`, such that
* each `D j` is an antipodal pair `{w_j, −w_j}` with `w_j ≠ 0` (so `negClosed` + count `negDirCount`),
* the `w_j` directions are pairwise disjoint,
* every element of every `D j` is a `2^k`-th root of unity,

the zero-sum count of the union of all `m` directions satisfies the Wick bound

  `zeroSumCount (unionUpto D m) (2r) ≤ (2r−1)‼·(2m)^r`.

This composes the whole abstract char-0 chain with **no named hypothesis**: the per-direction count
is `zeroSumCount_antiPair`, mutual decoupling is `mutuallyDecoupled_of_antipodalDirections`, the
`m`-fold identity is `zeroSumCount_iUnion_eq_natConv`, the natConv↔Bessel bridge is
`natConv_negDirCount_eq_Edef`, and the coefficient domination is `charZeroWick_bound_allR`.

For `μ_n = nthRootsFinset (2^μ)` with `n = 2m`, the `m` antipodal directions `{ζ^j, −ζ^j}` of a
primitive `2^μ`-th root `ζ` satisfy the three hypotheses verbatim, with `unionUpto D m = μ_n`;
plugging that in gives `E_r^{char0}(μ_n) ≤ (2r−1)‼·n^r`. -/
theorem charZeroWick_selfContained [CharZero F] {k m : ℕ} (D : Fin m → Finset F)
    (w : Fin m → F) (hw : ∀ j, w j ≠ 0) (hD : ∀ j, D j = antiPair (w j))
    (hdisj : ∀ i j : Fin m, i ≠ j → Disjoint (D i) (D j))
    (hroot : ∀ (j : Fin m), ∀ x ∈ D j, x ^ (2 ^ k) = 1)
    (r : ℕ) :
    (zeroSumCount (unionUpto D m) (2 * r) : ℚ)
      ≤ ((2 * r - 1)‼ : ℚ) * ((2 * m : ℕ) : ℚ) ^ r := by
  classical
  -- (1) per-direction count is uniformly `negDirCount`.
  have hf : ∀ (j : ℕ) (h : j < m) (N : ℕ),
      zeroSumCount (D ⟨j, h⟩) N = negDirCount N := by
    intro j h N
    rw [hD ⟨j, h⟩]; exact zeroSumCount_antiPair (w ⟨j, h⟩) (hw ⟨j, h⟩) N
  -- (2) each direction negation-closed.
  have hNC : ∀ j : Fin m, AvCR.NegClosed (D j) := by
    intro j; rw [hD j]; exact negClosed_antiPair (w j)
  -- (3) mutually decoupled (Lam–Leung).
  have hdec : MutuallyDecoupled D :=
    mutuallyDecoupled_of_antipodalDirections D hNC hdisj hroot
  -- (4) the m-fold Bessel identity: zeroSumCount (⋃ D) (2r) = Edef r m.
  have hbessel : (zeroSumCount (unionUpto D m) (2 * r) : ℚ) = AvW0.Edef r m :=
    bessel_mfold_symbolic_d m D hf hdec r
  -- (5) Edef r m ≤ (2r−1)‼·(2m)^r  (the in-tree Bessel-coefficient domination).
  rw [hbessel]
  exact AvW0.charZero_wick_bound r m

#print axioms zeroSumCount_antiPair
#print axioms charZeroWick_selfContained

end ArkLib.ProximityGap.Frontier.AvCRSelfContained
