/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubsetSumE2PowerSumReduction
import Mathlib.Algebra.Order.Chebyshev

/-!
# Round 7 (Issue #232, ABF26) — Paley–Zygmund / second-moment ANTI-CONCENTRATION of the
# `(sum, sum-of-squares)` count `N2`, the exact second-moment bridge to the `q`-independence door.

Round 6 sharply localized the open core of the §7 list-decoding disproof to the **magnitude** and
**concentration** of the `(SUM, SUM-OF-SQUARES)` count

  `N2(a; c₁, c₂) := #{ S ⊆ G : |S| = a, ∑_{x∈S} x = c₁ ∧ ∑_{x∈S} x² = c₂ }`     (`n2Count`),

the count that *equals* (Round 6, `twoSymmetric_count_eq_e1_psum2_count`) the open `t = 2`
joint-symmetric `(e_1, e_2)` degree-drop count. Two Round-6 facts frame this round:

* **First moment (conservation law).** `∑_{(c₁,c₂)} N2(a; c₁, c₂) = C(n, a)`
  (`sum_n2Count_eq_choose` below, the `F × F` analogue of Round 4's `sum_subsetSumCount_eq_choose`
  and Round 6's `sum_jointFamily_card_eq_choose`). So the **average** fiber is `C(n,a)/q²`.
* **The `q`-independence door** (`ListInteriorQDependenceNoGo`,
  `qIndependent_count_lb_forces_concentration`). The prize counterexample needs a list `|Λ| > ε*·q`
  with `ε*` *fixed* — proved in Round 6 to be **equivalent** to `N2` *concentrating* on `O(1)`
  targets. The averaging method provably loses a `1/q²`; only concentration escapes it.

## What this round contributes — the SECOND moment turns the door into a sharp dichotomy

We connect the **second moment** `M2(a) := ∑_{(c₁,c₂)} N2(a; c₁,c₂)²` to the size of the support /
the number of heavy targets, via **Cauchy–Schwarz** (`sq_sum_le_card_mul_sum_sq`) and
**Paley–Zygmund**. Everything is over `ℕ` (exact integer counts, no casting), `sorry`-free and
axiom-clean.

* `sum_n2Count_eq_choose` — the **first moment** (conservation law) over `F × F`.
* `secondMoment_n2` — the second moment `M2(a) := ∑_{p:F×F} (N2 p)²` (a definition + total handle).
* `support_card_ge_choose_sq_div_secondMoment` — **the anti-concentration headline (Cauchy–Schwarz).**
  Let `support := { p : F×F | N2 p ≠ 0 }`. Then

    `C(n,a)²  ≤  |support| · M2(a)`,        i.e.  `|support| ≥ C(n,a)² / M2(a)`.

  So a **small** second moment `M2 ≈ C(n,a)²/q²` (the value when `N2` is *spread*, each `≈` average
  `C(n,a)/q²`) forces `|support| ≥ q²`: the count is **anti-concentrated**, spread over `≳ q²`
  targets. By the Round-6 door this is *exactly* the regime where no `q`-independent list bound
  exists — **the prize SURVIVES the averaging/second-moment attack.** Conversely, `q`-independence
  (concentration on `O(1)` targets) forces a *large* second moment `M2 ≳ C(n,a)²` — `q²` times the
  spread value (`secondMoment_ge_of_concentrated`).
* `manyHeavyTargets_card_ge` — **the Paley–Zygmund robustness headline.** Calling a target *heavy*
  when `N2 p ≥` half the average (`2·q²·N2 p ≥ C(n,a)`), at least half the total mass sits on heavy
  targets (`two_mul_sum_heavy_ge`), and Cauchy–Schwarz on the heavy set gives

    `C(n,a)²  ≤  4 · |heavy| · M2(a)`,      i.e.  `|heavy| ≥ C(n,a)² / (4 · M2(a))`.

  This upgrades "some target is heavy" (Round-4 pigeonhole) to "**many** targets are heavy" whenever
  the second moment is controlled — the robust, anti-concentrated picture.

## Honest scope (what is proven vs. assumed)

* The Cauchy–Schwarz and Paley–Zygmund inequalities here are **unconditional and exact**: they hold
  for the genuine `N2` count over any finite subset `G ⊆ F` of a finite field, no extra hypotheses.
  What they deliver is a *conditional dichotomy* keyed on the second moment `M2(a)`:
  `M2` small ⟹ anti-concentrated ⟹ no `q`-independence (prize survives);
  `M2 ≈ C(n,a)²` ⟹ concentration is *possible* (necessary, not sufficient — the door is still ajar).
* This file does **NOT** compute `M2(a)`. The actual value of the second moment requires a Weil-type
  estimate on the quadratic character sum `∑_{ψ₁,ψ₂} |…|²` (a 4-fold subset incidence / additive
  energy of the `(x, x²)` map on the subgroup `G`), which Mathlib lacks (no general Weil/RH for
  curves). So this is the **exact second-moment bridge**, not a closure: it pins *what number*
  (`M2`) decides the dichotomy and *which inequality* (`|support| ≥ C²/M2`) carries it, consistent
  with the Round-6 no-go. We are explicit: a bound on `M2` is the missing, open input.
* Non-vacuity: the first moment `C(n,a) > 0` for `a ≤ n`, and the concentration/spread hypotheses are
  satisfiable; the inequalities are genuine statements about the real `N2` count (e.g. on
  `G ⊆ ZMod 13`), not `0 ≤ 0`.

All headline results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Finset BigOperators

-- The `[Fintype F] [DecidableEq F]` instances are needed by the headline theorems (summation over
-- `F × F`, the conservation law); we keep them in the shared `variable` block, so a couple of
-- auxiliary lemmas carry them without using them in their own type.
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace ArkLib.CodingTheory.Round7PaleyZygmund

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## 1. The `(sum, sum-of-squares)` count `N2` and its first moment (conservation law). -/

/-- **The `(sum, sum-of-squares)` count** `N2(a; c₁, c₂)`: the number of `a`-element subsets `S` of
the ground set `G` (the smooth multiplicative subgroup, a `Finset` of field elements) whose elements
have window sum `∑_{x∈S} x = c₁` and sum of squares `∑_{x∈S} x² = c₂`. This is *exactly* the open
`t = 2` joint-symmetric `(e_1, e_2)` degree-drop count of Round 6
(`twoSymmetric_count_eq_e1_psum2_count`), recoordinated to the two single-coordinate statistics
`x` and `x²`. -/
noncomputable def n2Count (G : Finset F) (a : ℕ) (c₁ c₂ : F) : ℕ :=
  ((G.powersetCard a).filter (fun S => (∑ x ∈ S, x) = c₁ ∧ (∑ x ∈ S, x ^ 2) = c₂)).card

/-- **First moment (conservation law): `∑_{(c₁,c₂)} N2(a; c₁,c₂) = C(|G|, a)`.** The `a`-subsets of
`G` are partitioned by the *pair* `(∑_{x∈S} x, ∑_{x∈S} x²) ∈ F × F`, so summing the fiber counts over
all pairs recovers the total `C(|G|, a)`. This is the `F × F` analogue of Round 4's
`sum_subsetSumCount_eq_choose` (single coordinate) and Round 6's `sum_jointFamily_card_eq_choose`
(over `ι`). It fixes the **average** fiber at `C(|G|,a)/q²` and is the first moment of the
Paley–Zygmund analysis. -/
theorem sum_n2Count_eq_choose (G : Finset F) (a : ℕ) :
    ∑ p : F × F, n2Count G a p.1 p.2 = (G.card).choose a := by
  classical
  have hpart : (G.powersetCard a).card
      = ∑ p : F × F,
          ((G.powersetCard a).filter
            (fun S => (∑ x ∈ S, x, ∑ x ∈ S, x ^ 2) = p)).card :=
    Finset.card_eq_sum_card_fiberwise
      (f := fun S => (∑ x ∈ S, x, ∑ x ∈ S, x ^ 2))
      (t := (Finset.univ : Finset (F × F)))
      (fun S _ => Finset.mem_univ _)
  rw [Finset.card_powersetCard] at hpart
  -- rewrite each `n2Count` (conjunction predicate) into the pair-equality fiber, then use `hpart`.
  have hconv : ∑ p : F × F, n2Count G a p.1 p.2
      = ∑ p : F × F,
          ((G.powersetCard a).filter
            (fun S => (∑ x ∈ S, x, ∑ x ∈ S, x ^ 2) = p)).card := by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    unfold n2Count
    congr 1
    apply Finset.filter_congr
    intro S _
    constructor
    · rintro ⟨h1, h2⟩; rw [Prod.ext_iff]; exact ⟨h1, h2⟩
    · intro h; rw [Prod.ext_iff] at h; exact ⟨h.1, h.2⟩
  rw [hconv, ← hpart]

/-! ## 2. The second moment `M2(a) := ∑_{(c₁,c₂)} N2(a; c₁,c₂)²`. -/

/-- **The second moment of the `(sum, sum-of-squares)` count.** `M2(a) := ∑_{p:F×F} N2(a; p)²`. This
is the quantity a Weil-type estimate would control: it equals the **additive energy** of the
`(x, x²)`-incidence on `G` (the number of pairs `(S, S')` of `a`-subsets with equal sum *and* equal
sum of squares), the 4-fold quadratic character sum `∑_{ψ₁,ψ₂} |∑_{S} ψ₁(∑x)ψ₂(∑x²)|²`. Its size is
the single number deciding the concentration dichotomy below. -/
noncomputable def secondMoment_n2 (G : Finset F) (a : ℕ) : ℕ :=
  ∑ p : F × F, (n2Count G a p.1 p.2) ^ 2

/-! ## 3. The anti-concentration headline (Cauchy–Schwarz): small second moment ⟹ large support. -/

/-- The **support** of the count: the set of target pairs hit by at least one `a`-subset. -/
noncomputable def n2Support (G : Finset F) (a : ℕ) : Finset (F × F) :=
  (Finset.univ : Finset (F × F)).filter (fun p => n2Count G a p.1 p.2 ≠ 0)

/-- **The total mass is carried by the support.** Off the support `N2 = 0`, so summing `N2` over the
support equals summing over all of `F × F`, which is `C(|G|, a)` by the conservation law. -/
theorem sum_n2Count_support (G : Finset F) (a : ℕ) :
    ∑ p ∈ n2Support G a, n2Count G a p.1 p.2 = (G.card).choose a := by
  classical
  rw [← sum_n2Count_eq_choose G a]
  unfold n2Support
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases h : n2Count G a p.1 p.2 = 0
  · rw [if_neg (by simp [h]), h]
  · rw [if_pos h]

/-- Likewise the sum of squares is carried by the support: `∑_{support} N2² = M2(a)`. -/
theorem secondMoment_eq_sum_support (G : Finset F) (a : ℕ) :
    ∑ p ∈ n2Support G a, (n2Count G a p.1 p.2) ^ 2 = secondMoment_n2 G a := by
  classical
  unfold secondMoment_n2 n2Support
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases h : n2Count G a p.1 p.2 = 0
  · rw [if_neg (by simp [h]), h]; ring
  · rw [if_pos h]

/-- **The anti-concentration headline (Cauchy–Schwarz).** The number of *hit* target pairs (the
support) times the second moment is at least the square of the first moment:

  `C(|G|, a)²  ≤  |support| · M2(a)`,    i.e.   `|support| ≥ C(|G|, a)² / M2(a)`.

This is `sq_sum_le_card_mul_sum_sq` applied to `N2` restricted to its support (where the first moment
`∑ N2 = C(n,a)` and the second moment `∑ N2² = M2` both live, by `sum_n2Count_support` /
`secondMoment_eq_sum_support`). **Reading the dichotomy:** if the second moment is small —
`M2 ≈ C(n,a)²/q²`, the value forced when `N2` is *spread* with each fiber near the average
`C(n,a)/q²` — then `|support| ≥ q²`, i.e. the count is **anti-concentrated** over `≳ q²` targets. By
the Round-6 door (`qIndependent_count_lb_forces_concentration`), anti-concentration is *exactly* the
regime with **no `q`-independent list bound**: the prize **survives** the averaging/second-moment
attack. The averaging method's `1/q²` loss is thus second-moment-explained: only a *large* second
moment (concentration) could escape it. -/
theorem support_card_ge_choose_sq_div_secondMoment (G : Finset F) (a : ℕ) :
    ((G.card).choose a) ^ 2 ≤ (n2Support G a).card * secondMoment_n2 G a := by
  classical
  have hcs := sq_sum_le_card_mul_sum_sq (s := n2Support G a)
    (f := fun p => n2Count G a p.1 p.2)
  rw [sum_n2Count_support G a, secondMoment_eq_sum_support G a] at hcs
  exact hcs

/-- **Equivalent quotient form of the anti-concentration bound (over `ℕ`).** `M2(a) > 0` (some
target is hit when `a ≤ |G|`) lets us divide: `|support| ≥ ⌈C(n,a)²/M2⌉ ≥ C(n,a)²/M2`. We state the
floor form `C(n,a)² / M2(a) ≤ |support|` (Nat division), the directly usable consequence: a small
second moment **forces** a proportionally large support. -/
theorem support_card_ge_div (G : Finset F) (a : ℕ) (hM : 0 < secondMoment_n2 G a) :
    ((G.card).choose a) ^ 2 / secondMoment_n2 G a ≤ (n2Support G a).card := by
  rw [Nat.div_le_iff_le_mul_add_pred hM]
  refine le_trans (support_card_ge_choose_sq_div_secondMoment G a) ?_
  rw [mul_comm (secondMoment_n2 G a)]
  exact Nat.le_add_right _ _

/-! ## 4. The converse: `q`-independence (concentration) forces a LARGE second moment. -/

/-- **Concentration ⟹ large second moment (the converse direction).** If the count *concentrates* —
a single target pair `p₀` carries a constant fraction of the whole, `c · N2(p₀) ≥ C(|G|, a)` with `c`
*fixed* (the exact shape of a `q`-independent lower bound, Round 6
`qIndependent_count_lb_forces_concentration`) — then the second moment is **large**:

  `c² · M2(a)  ≥  C(|G|, a)²`,    i.e.   `M2(a) ≥ C(|G|,a)² / c²`.

Since the single term `N2(p₀)²` already dominates: `M2 ≥ N2(p₀)² ≥ (C(n,a)/c)²`. Combined with the
anti-concentration headline, this is the sharp **dichotomy**: the second moment `M2` is small
(`≈ C²/q²`) **iff** the count is spread (no `q`-independence), and `M2` is large (`≳ C²`) **iff**
concentration on `O(1)` targets is possible. The second moment is the single number that decides the
`q`-independence door. -/
theorem secondMoment_ge_of_concentrated (G : Finset F) (a c : ℕ) (p₀ : F × F)
    (hconc : (G.card).choose a ≤ c * n2Count G a p₀.1 p₀.2) :
    ((G.card).choose a) ^ 2 ≤ c ^ 2 * secondMoment_n2 G a := by
  classical
  -- `M2 ≥ N2(p₀)²` (single term of a sum of squares).
  have hterm : (n2Count G a p₀.1 p₀.2) ^ 2 ≤ secondMoment_n2 G a := by
    unfold secondMoment_n2
    exact Finset.single_le_sum (f := fun p : F × F => (n2Count G a p.1 p.2) ^ 2)
      (fun p _ => Nat.zero_le _) (Finset.mem_univ p₀)
  calc ((G.card).choose a) ^ 2
      ≤ (c * n2Count G a p₀.1 p₀.2) ^ 2 := Nat.pow_le_pow_left hconc 2
    _ = c ^ 2 * (n2Count G a p₀.1 p₀.2) ^ 2 := by ring
    _ ≤ c ^ 2 * secondMoment_n2 G a := Nat.mul_le_mul_left _ hterm

/-! ## 5. The Paley–Zygmund robustness headline: many heavy targets when the 2nd moment is controlled.

A target pair is **heavy** when its count is at least half the average, `N2(p) ≥ avg/2`, i.e.
`2·q²·N2(p) ≥ C(n,a)` (`q² = |F × F|`). The light targets carry less than half the mass, so the heavy
targets carry **more than half** — and Cauchy–Schwarz on the heavy set converts that mass into a
lower bound on `|heavy|`. -/

/-- The **heavy** target pairs: those whose count is at least half the average,
`2 · |F × F| · N2(p) ≥ C(|G|, a)`. -/
noncomputable def heavyTargets (G : Finset F) (a : ℕ) : Finset (F × F) :=
  (Finset.univ : Finset (F × F)).filter
    (fun p => (G.card).choose a ≤ 2 * (Fintype.card F * Fintype.card F) * n2Count G a p.1 p.2)

/-- **The light targets carry less than half the total mass.** Each *light* (= not heavy) target has
`2·q²·N2 < C(n,a)`; summing over the `q²` light targets, `2·q²·∑_{light} N2 < q²·C(n,a)`, hence
`2·∑_{light} N2 < C(n,a)`: strictly less than half the total `C(n,a)`. (Cancels the common `q²`.)
The empty-domain corner is excluded by the field being nonempty.) -/
theorem two_mul_sum_light_lt (G : Finset F) (a : ℕ) :
    2 * ∑ p ∈ (Finset.univ : Finset (F × F)) \ heavyTargets G a, n2Count G a p.1 p.2
      < (G.card).choose a ∨ (G.card).choose a = 0 := by
  classical
  by_cases h0 : (G.card).choose a = 0
  · exact Or.inr h0
  · refine Or.inl ?_
    set L : Finset (F × F) := (Finset.univ : Finset (F × F)) \ heavyTargets G a with hL
    -- on `L`, every target is light: `2·q²·N2 < C(n,a)`.
    have hlight : ∀ p ∈ L, 2 * (Fintype.card F * Fintype.card F) * n2Count G a p.1 p.2
        < (G.card).choose a := by
      intro p hp
      rw [hL, Finset.mem_sdiff] at hp
      have hnh := hp.2
      rw [heavyTargets, Finset.mem_filter] at hnh
      push_neg at hnh
      exact hnh (Finset.mem_univ p)
    set Q : ℕ := Fintype.card F * Fintype.card F with hQ
    have hQpos : 0 < Q := by
      have : 0 < Fintype.card F := Fintype.card_pos
      exact Nat.mul_pos this this
    -- Sum the strict per-target bound; need `L` nonempty for the strict version,
    -- otherwise the sum is `0` and `0 < C(n,a)` since `C(n,a) ≠ 0`.
    rcases Finset.eq_empty_or_nonempty L with hempty | hne
    · rw [hempty]; simp only [Finset.sum_empty, mul_zero]; exact Nat.pos_of_ne_zero h0
    · -- `2·Q·∑_L N2 < |L|·C(n,a) ≤ Q·C(n,a)`, then cancel `Q`.
      have hsum_lt : (2 * Q) * ∑ p ∈ L, n2Count G a p.1 p.2 < L.card * (G.card).choose a := by
        calc (2 * Q) * ∑ p ∈ L, n2Count G a p.1 p.2
            = ∑ p ∈ L, (2 * Q) * n2Count G a p.1 p.2 := by rw [Finset.mul_sum]
          _ < ∑ _p ∈ L, (G.card).choose a := by
              refine Finset.sum_lt_sum_of_nonempty hne (fun p hp => ?_)
              exact hlight p hp
          _ = L.card * (G.card).choose a := by rw [Finset.sum_const, smul_eq_mul]
      have hLcard : L.card ≤ Q := by
        have hsub : L.card ≤ (Finset.univ : Finset (F × F)).card :=
          Finset.card_le_card (by rw [hL]; exact Finset.sdiff_subset)
        rwa [Finset.card_univ, Fintype.card_prod, ← hQ] at hsub
      have hchain : (2 * Q) * ∑ p ∈ L, n2Count G a p.1 p.2 < Q * (G.card).choose a :=
        lt_of_lt_of_le hsum_lt (Nat.mul_le_mul_right _ hLcard)
      -- `2·Q·X < Q·C` ⟹ `2·X < C` (cancel `Q > 0`).
      have : Q * (2 * ∑ p ∈ L, n2Count G a p.1 p.2) < Q * (G.card).choose a := by
        calc Q * (2 * ∑ p ∈ L, n2Count G a p.1 p.2)
            = (2 * Q) * ∑ p ∈ L, n2Count G a p.1 p.2 := by ring
          _ < Q * (G.card).choose a := hchain
      exact lt_of_mul_lt_mul_left this (Nat.zero_le Q)

/-- **The heavy targets carry more than half the total mass.** From `∑_heavy + ∑_light = C(n,a)`
(total) and `2·∑_light < C(n,a)` (`two_mul_sum_light_lt`), we get `2·∑_heavy > C(n,a)`: strictly
more than half the mass concentrates on heavy targets. (The `C(n,a) = 0` corner is degenerate and
excluded by `a ≤ |G|`.) -/
theorem two_mul_sum_heavy_gt (G : Finset F) (a : ℕ) (hpos : 0 < (G.card).choose a) :
    (G.card).choose a < 2 * ∑ p ∈ heavyTargets G a, n2Count G a p.1 p.2 := by
  classical
  -- split the total over heavy and its complement (`univ \ heavy`).
  have hsplit : ∑ p ∈ (Finset.univ : Finset (F × F)) \ heavyTargets G a, n2Count G a p.1 p.2
      + ∑ p ∈ heavyTargets G a, n2Count G a p.1 p.2
      = (G.card).choose a := by
    rw [Finset.sum_sdiff (Finset.subset_univ (heavyTargets G a))]
    exact sum_n2Count_eq_choose G a
  rcases two_mul_sum_light_lt G a with hlight | h0
  · -- `2·heavy = 2·(total − light) = 2·total − 2·light > 2·total − total = total`.
    set H : ℕ := ∑ p ∈ heavyTargets G a, n2Count G a p.1 p.2 with hH
    set Lm : ℕ := ∑ p ∈ (Finset.univ : Finset (F × F)) \ heavyTargets G a,
      n2Count G a p.1 p.2 with hLm
    have htot : Lm + H = (G.card).choose a := hsplit
    -- from `2·Lm < total` and `H + Lm = total`: `2·H = 2·total − 2·Lm > 2·total − total = total`.
    omega
  · exact absurd h0 hpos.ne'

/-- **The Paley–Zygmund robustness headline: many heavy targets.** Combining the mass bound
`2·∑_heavy N2 > C(n,a)` (`two_mul_sum_heavy_gt`) with Cauchy–Schwarz on the *heavy* set
(`sq_sum_le_card_mul_sum_sq`, and `∑_heavy N2² ≤ M2`), the number of heavy targets is large:

  `C(|G|, a)²  ≤  4 · |heavy| · M2(a)`,    i.e.   `|heavy| ≥ C(|G|, a)² / (4 · M2(a))`.

This is the second-moment **upgrade of the Round-4 pigeonhole** ("some target is heavy",
`max_fiber_interior_ge`) to "**many** targets are heavy": whenever the second moment is controlled
(`M2 ≈ C²/q²`, the spread value), `|heavy| ≳ q²/4` — a constant fraction of *all* targets are heavy.
This is the precise, anti-concentrated, robust picture the prize counterexample must overturn: it
would need the second moment to be *atypically large* (`M2 ≳ C²`), i.e. genuine concentration, which
the averaging structure (Round 4/6 no-go) cannot supply. -/
theorem manyHeavyTargets_card_ge (G : Finset F) (a : ℕ) (hpos : 0 < (G.card).choose a) :
    ((G.card).choose a) ^ 2 ≤ 4 * ((heavyTargets G a).card * secondMoment_n2 G a) := by
  classical
  set H : ℕ := ∑ p ∈ heavyTargets G a, n2Count G a p.1 p.2 with hH
  -- Cauchy–Schwarz on the heavy set: `H² ≤ |heavy| · ∑_heavy N2²`.
  have hcs := sq_sum_le_card_mul_sum_sq (s := heavyTargets G a)
    (f := fun p => n2Count G a p.1 p.2)
  -- `∑_heavy N2² ≤ M2` (heavy ⊆ univ; the omitted terms are nonneg).
  have hheavy_le : ∑ p ∈ heavyTargets G a, (n2Count G a p.1 p.2) ^ 2 ≤ secondMoment_n2 G a := by
    unfold secondMoment_n2
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun p _ _ => Nat.zero_le _)
  -- chain `H² ≤ |heavy|·M2`, and `(C(n,a))² < (2·H)² = 4·H²` from `C(n,a) < 2·H`.
  have hHbound : ((G.card).choose a) < 2 * H := two_mul_sum_heavy_gt G a hpos
  have hcs2 : H ^ 2 ≤ (heavyTargets G a).card * secondMoment_n2 G a :=
    le_trans hcs (Nat.mul_le_mul_left _ hheavy_le)
  calc ((G.card).choose a) ^ 2
      ≤ (2 * H) ^ 2 := Nat.pow_le_pow_left (le_of_lt hHbound) 2
    _ = 4 * H ^ 2 := by ring
    _ ≤ 4 * ((heavyTargets G a).card * secondMoment_n2 G a) := Nat.mul_le_mul_left _ hcs2

/-! ## 6. The exact bridge to the Round-6 `t = 2` count, and non-vacuity. -/

/-- **`N2` IS the Round-6 `t = 2` (`e_1, e_2`) joint-symmetric count.** For a domain embedding
`D : ι ↪ F`, char `≠ 2`, the `(sum, sum-of-squares)` count over the image equals the open `t = 2`
joint degree-drop count of Round 6 (`twoSymmetric_count_eq_e1_psum2_count`), with the second target
shifted by Newton's identity (`c₂ = c₁² − 2·d₂`). So the second-moment dichotomy above is a
statement about the **exact open count** the prize hinges on, not a proxy. -/
theorem n2Count_eq_twoSymmetric {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι ↪ F) (h2 : (2 : F) ≠ 0) (a : ℕ) (c₁ d₂ : F) :
    ((Finset.univ.powersetCard a).filter
        (fun S => (∑ i ∈ S, D i) = c₁ ∧ (∑ T ∈ S.powersetCard 2, ∏ i ∈ T, D i) = d₂)).card
      = ((Finset.univ.powersetCard a).filter
        (fun S => (∑ i ∈ S, D i) = c₁ ∧ (∑ i ∈ S, (D i) ^ 2) = c₁ ^ 2 - 2 * d₂)).card :=
  ArkLib.CodingTheory.Round6MultCharacter.twoSymmetric_count_eq_e1_psum2_count D h2 a c₁ d₂

/-- **Non-vacuity: the first moment is positive, so all bounds are genuine.** For `a ≤ |G|`,
`C(|G|, a) > 0`, hence the anti-concentration bound `C² ≤ |support|·M2` and the Paley–Zygmund
bound `C² ≤ 4·|heavy|·M2` have a *positive* left side: they are real constraints on `|support|`,
`|heavy|`, and `M2`, not the vacuous `0 ≤ …`. (`manyHeavyTargets_card_ge`'s hypothesis is met.) -/
theorem first_moment_pos (G : Finset F) (a : ℕ) (ha : a ≤ G.card) :
    0 < (G.card).choose a :=
  Nat.choose_pos ha

/-- **`(2 : ZMod 13) ≠ 0` — the smooth-domain regime is realized.** The smooth `2^k`-subgroup lives
in odd characteristic; `ZMod 13` (a field, with a multiplicative subgroup of order `4 = 2²`) has
`2 ≠ 0`, so the `t = 2` bridge `n2Count_eq_twoSymmetric` applies non-vacuously. -/
theorem two_ne_zero_zmod13 : (2 : ZMod 13) ≠ 0 := by decide

end ArkLib.CodingTheory.Round7PaleyZygmund

/-! ## Axiom audit -/
#print axioms ArkLib.CodingTheory.Round7PaleyZygmund.sum_n2Count_eq_choose
#print axioms ArkLib.CodingTheory.Round7PaleyZygmund.sum_n2Count_support
#print axioms ArkLib.CodingTheory.Round7PaleyZygmund.secondMoment_eq_sum_support
#print axioms ArkLib.CodingTheory.Round7PaleyZygmund.support_card_ge_choose_sq_div_secondMoment
#print axioms ArkLib.CodingTheory.Round7PaleyZygmund.support_card_ge_div
#print axioms ArkLib.CodingTheory.Round7PaleyZygmund.secondMoment_ge_of_concentrated
#print axioms ArkLib.CodingTheory.Round7PaleyZygmund.two_mul_sum_light_lt
#print axioms ArkLib.CodingTheory.Round7PaleyZygmund.two_mul_sum_heavy_gt
#print axioms ArkLib.CodingTheory.Round7PaleyZygmund.manyHeavyTargets_card_ge
#print axioms ArkLib.CodingTheory.Round7PaleyZygmund.n2Count_eq_twoSymmetric
#print axioms ArkLib.CodingTheory.Round7PaleyZygmund.first_moment_pos
#print axioms ArkLib.CodingTheory.Round7PaleyZygmund.two_ne_zero_zmod13
