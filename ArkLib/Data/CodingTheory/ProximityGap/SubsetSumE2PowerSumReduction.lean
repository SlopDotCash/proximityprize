/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ListInteriorT2TwoSymmetric
import ArkLib.Data.CodingTheory.ProximityGap.SubsetSumEsymmVanishing

/-!
# Round 6 (Issue #232, ABF26) — the `t = 2` joint count via the Newton identity `e_2 = (e_1² − p_2)/2`,
# turning the `(e_1, e_2)` joint-symmetric fiber into an `(e_1, p_2) = (sum, sum-of-squares)` fiber.

Rounds 1–5 reduced the open core of the §7 list-decoding disproof to a **field-independent
super-polynomial lower bound** on the count of `(k+t)`-subsets `S` of the smooth `2^k`-subgroup `G`
with the top `t` symmetric functions `e_1, …, e_t` *jointly* prescribed. Round 5
(`ListInteriorT2TwoSymmetric.lean`, `degDrop_t2_iff_two_symmetric`) pinned the **exact** `t = 2`
joint degree-drop condition:

  `{ S : |S| = k+2,  e_1(D_S) = c_1  ∧  e_2(D_S) = c_2 }`,

with `e_1(D_S) = ∑_{i∈S} D i`, `e_2(D_S) = ∑_{T∈S.powersetCard 2} ∏_{i∈T} D i`. Round 5 also recorded
that the *additive* slice-rank / Croot–Lev–Pach route is a dead end on a multiplicative subgroup. The
state-of-the-art memory note flags the **multiplicative** character-sum / Weil / Stepanov tools as the
untried angle, because `G` is the root set of `X^n − 1`.

## What this round contributes (the new `t = 2` reduction brick)

The order-2 elementary symmetric function and the order-2 **power sum** `p_2(S) := ∑_{i∈S} (D i)²`
are tied by **Newton's identity** (`e_1² = p_2 + 2·e_2`, a pure char-independent ring identity over a
finite set). We formalize this exactly and use it to **re-coordinate the `t = 2` joint fiber**:

* `sq_window_sum_eq` — the Newton identity at order 2 over a `Finset`:
  `(∑_{i∈S} D i)² = ∑_{i∈S} (D i)² + 2·(∑_{T∈S.powersetCard 2} ∏_{i∈T} D i)`,
  i.e. `e_1² = p_2 + 2·e_2`. Proved by `Finset.induction` (no char hypothesis, no division).
* `esymm_two_eq_e1_sq_sub_psum2` — solved form `2·e_2 = e_1² − p_2`, hence on the joint fiber
  `e_2 = c_2` is equivalent to `p_2 = e_1² − 2·c_2 = c_1² − 2·c_2` (once `e_1 = c_1`).
* `twoSymmetric_fiber_eq_e1_psum2_fiber` — **the headline re-coordinatization**: the `(e_1, e_2)`
  joint fiber `{|S|=a, e_1=c_1 ∧ e_2=c_2}` is *literally the same Finset* as the
  `(e_1, p_2)` joint fiber `{|S|=a, e_1=c_1 ∧ p_2=c_1²−2c_2}`. Hence the two counts are **equal**
  (`twoSymmetric_count_eq_e1_psum2_count`). This converts the open `t = 2` count into a count over the
  **additive sum** `∑ x` *and* the **quadratic power sum** `∑ x²` — a two-dimensional incidence count
  that is exactly the object a 2-character Gauss/Weil exponential sum
  `∑_{ψ₁,ψ₂} ψ₁(∑x − c₁) ψ₂(∑x² − c₂')` controls. The Round-5 `e_2` (sum over pairs of products) is
  replaced by `p_2` (sum of squares), which is **linear in the per-coordinate map `x ↦ x²`** — the
  shape multiplicative/additive character sums see directly, unlike the pair-product `e_2`.
* `degDrop_t2_iff_e1_psum2` — the degree-drop criterion re-expressed in the new coordinates:
  both top coeffs of `p_S` vanish ↔ `e_1(D_S) = −g_{k+1}/c ∧ p_2(D_S) = (g_{k+1}/c)² − 2·g_k/c`.
* `twoSymmetric_psum2_interior_list_card_ge` — the interior RS-list lower bound driven by the
  `(e_1, p_2)` fiber count (the Round-5 bridge, recoordinated). Field-independent in the count.

## Honest scope (what this is and is NOT)

* This is the **exact algebraic reduction** `e_2 ↔ (e_1, p_2)`. It is `sorry`-free and axiom-clean.
  It is genuinely new over Round 5: Round 5 left the second constraint as the pair-product `e_2`;
  here the second constraint is the **power sum** `p_2 = ∑ x²`, which is a *single-coordinate*
  statistic — the necessary shape for a Weil-type two-character sum.
* It does **NOT** prove the `t = 2` count is super-polynomial (the prize-deciding bound). It opens the
  multiplicative-character route by exhibiting the count as a `(∑x, ∑x²)` joint fiber; the actual
  bound would need a **Weil estimate** `|N(c₁,c₂) − C(n,a)/q²| ≤ (error)` with the error term
  `O(d · √q · …)` controlled — and that error term is genuinely *not* established here. We are honest:
  the character-sum machinery (Gauss sums, Weil's bound on `∑ ψ(f(x))` for `f` of bounded degree) is
  **not** formalized in this file; what is formalized is the *reduction that makes those tools
  applicable*, i.e. the precise object they would estimate.
* The Round-5 NO-GO survives verbatim: the pigeonhole floor `max fiber ≥ C(n,a)/q` from the order-≤4
  symmetry group still lower-bounds the `(e_1, p_2)` fiber (it is a sub-fiber of the `e_1`-fiber), so
  no `poly(n)` *upper* bound follows from symmetry alone. The open magnitude question is unchanged in
  difficulty; what changed is the **coordinates** in which it is posed — from pair-products to a sum
  of squares, the additive-character-friendly form.

All headline results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Polynomial BigOperators Finset

namespace ArkLib.CodingTheory.Round6MultCharacter

open ArkLib.CodingTheory.Round4InteriorList
open ArkLib.CodingTheory.Round5SliceRankT2

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F]

/-! ## 1. The Newton identity at order 2 over a `Finset`: `e_1² = p_2 + 2·e_2`. -/

/-- **The order-2 power sum of the roots over `S`.** `p_2(D_S) := ∑_{i∈S} (D i)²`. This is the
sum-of-squares statistic — a *single-coordinate* function `x ↦ x²` summed over `S`, hence the shape an
additive/multiplicative character sum sees directly (unlike the pair-product `e_2`). -/
noncomputable def psum2 (D : ι ↪ F) (S : Finset ι) : F := ∑ i ∈ S, (D i) ^ 2

omit [Fintype ι] in
/-- **Newton's identity at order 2 (the squared window sum).** For any finite set `S`,

  `(∑_{i∈S} D i)² = ∑_{i∈S} (D i)² + 2 · (∑_{T∈S.powersetCard 2} ∏_{i∈T} D i)`,

i.e. `e_1² = p_2 + 2·e_2`. This is a pure ring identity (no char hypothesis, no division), proved by
`Finset.induction`. The inductive step uses `powersetCard_succ_insert`: the pairs of `insert a S` are
the pairs of `S` together with `{a, j}` for `j ∈ S`, contributing `D a · (∑_{j∈S} D j)`. -/
theorem sq_window_sum_eq (D : ι ↪ F) (S : Finset ι) :
    (∑ i ∈ S, D i) ^ 2
      = (∑ i ∈ S, (D i) ^ 2) + 2 * (∑ T ∈ S.powersetCard 2, ∏ i ∈ T, D i) := by
  classical
  induction S using Finset.induction with
  | empty => simp [Finset.powersetCard_eq_empty.mpr (by simp : (∅ : Finset ι).card < 2)]
  | insert a s ha ih =>
    -- `powersetCard 2 (insert a s) = powersetCard 2 s ∪ image (insert a) (powersetCard 1 s)`
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    -- the pair-sum over `insert a s`
    have hpairs : (∑ T ∈ (insert a s).powersetCard 2, ∏ i ∈ T, D i)
        = (∑ T ∈ s.powersetCard 2, ∏ i ∈ T, D i) + D a * (∑ j ∈ s, D j) := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, Finset.powersetCard_succ_insert ha]
      -- the union is disjoint: members of `image (insert a) (powersetCard 1 s)` contain `a`,
      -- members of `powersetCard 2 s` are subsets of `s` not containing `a`.
      have hdisj : Disjoint (s.powersetCard (1 + 1))
          ((s.powersetCard 1).image (insert a)) := by
        rw [Finset.disjoint_left]
        intro T hT hT'
        rw [Finset.mem_powersetCard] at hT
        rw [Finset.mem_image] at hT'
        obtain ⟨U, hU, rfl⟩ := hT'
        rw [Finset.mem_powersetCard] at hU
        exact ha (hT.1 (Finset.mem_insert_self a U))
      rw [Finset.sum_union hdisj]
      congr 1
      -- the `image (insert a)` sum: each `U` of card 1 gives `∏_{insert a U} = D a · ∏_U`,
      -- and `insert a` is injective on subsets of `s` (since `a ∉ s`).
      rw [Finset.sum_image]
      · -- `∑_{U ∈ powersetCard 1 s} ∏_{i ∈ insert a U} D i = D a * ∑_{j ∈ s} D j`
        rw [Finset.powersetCard_one, Finset.sum_map, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        have haj : a ≠ j := fun h => ha (h ▸ hj)
        simp only [Function.Embedding.coeFn_mk]
        rw [Finset.prod_insert (by simp [haj]), Finset.prod_singleton]
      · -- injectivity of `insert a` on `powersetCard 1 s` (subsets avoiding `a`)
        intro U hU V hV hUV
        rw [Finset.mem_coe, Finset.mem_powersetCard] at hU hV
        have haU : a ∉ U := fun h => ha (hU.1 h)
        have haV : a ∉ V := fun h => ha (hV.1 h)
        have := congrArg (fun X => Finset.erase X a) hUV
        simpa [Finset.erase_insert haU, Finset.erase_insert haV] using this
    rw [hpairs]
    -- combine with the inductive hypothesis on `(∑_s D)²`.
    linear_combination ih

omit [Fintype ι] in
/-- **Newton's identity solved for `e_2`: `2·e_2 = e_1² − p_2`.** Rearranges `sq_window_sum_eq`. Over a
finite set this is char-free; dividing by `2` (valid when `2 ≠ 0` in `F`) gives `e_2 = (e_1²−p_2)/2`,
but we keep the multiplied form to stay char-independent. -/
theorem two_esymm_two_eq (D : ι ↪ F) (S : Finset ι) :
    2 * (∑ T ∈ S.powersetCard 2, ∏ i ∈ T, D i)
      = (∑ i ∈ S, D i) ^ 2 - ∑ i ∈ S, (D i) ^ 2 := by
  have h := sq_window_sum_eq D S
  linear_combination -h

/-! ## 2. Re-coordinatizing the `t = 2` joint fiber: `(e_1, e_2) ↔ (e_1, p_2)`.

On the joint fiber where `e_1 = c_1` is *already imposed*, the constraint `e_2 = c_2` is equivalent to
the **power-sum** constraint `p_2 = c_1² − 2·c_2` (from `e_1² = p_2 + 2·e_2`). So the `(e_1, e_2)`
fiber and the `(e_1, p_2)` fiber are the *same set of subsets* — we prove literal Finset equality. -/

/-- **The two joint fibers coincide (the headline re-coordinatization).** For a ground set `G`,
agreement size `a`, and targets `c₁ c₂`, the set of `a`-subsets with `e_1 = c₁ ∧ e_2 = c₂` equals the
set of `a`-subsets with `e_1 = c₁ ∧ p_2 = c₁² − 2·c₂`. The first is the Round-5 `t = 2` fiber; the
second is the **sum / sum-of-squares** fiber. Equal as `Finset`s, so equal counts.

The hypothesis `(2 : F) ≠ 0` (i.e. `char F ≠ 2`) is **automatic in the regime of interest**: a smooth
multiplicative subgroup of order `n = 2^k` exists in `F` only when `2^k ∣ |F| − 1`, which forces `|F|`
odd, hence `char F ≠ 2`. The forward inclusion (`e_2 = c₂ ⟹ p_2 = c₁²−2c₂`) is char-free; only the
backward inclusion cancels the `2`. -/
theorem twoSymmetric_fiber_eq_e1_psum2_fiber [DecidableEq F] (D : ι ↪ F) (h2 : (2 : F) ≠ 0)
    (a : ℕ) (c₁ c₂ : F) :
    (Finset.univ.powersetCard a).filter
        (fun S => (∑ i ∈ S, D i) = c₁ ∧ (∑ T ∈ S.powersetCard 2, ∏ i ∈ T, D i) = c₂)
      = (Finset.univ.powersetCard a).filter
        (fun S => (∑ i ∈ S, D i) = c₁ ∧ (∑ i ∈ S, (D i) ^ 2) = c₁ ^ 2 - 2 * c₂) := by
  classical
  apply Finset.filter_congr
  intro S _hS
  constructor
  · rintro ⟨h1, he2⟩
    refine ⟨h1, ?_⟩
    -- p_2 = e_1² − 2·e_2 = c₁² − 2·c₂  (char-free)
    have hnewton := sq_window_sum_eq D S
    rw [h1, he2] at hnewton
    linear_combination -hnewton
  · rintro ⟨h1, hp2⟩
    refine ⟨h1, ?_⟩
    -- from `e_1² = p_2 + 2·e_2`, `e_1 = c₁`, `p_2 = c₁² − 2c₂`: `2·e_2 = 2·c₂`, cancel `2`.
    have hnewton := sq_window_sum_eq D S
    rw [h1, hp2] at hnewton
    have h2e2 : 2 * (∑ T ∈ S.powersetCard 2, ∏ i ∈ T, D i) = 2 * c₂ := by
      linear_combination -hnewton
    exact mul_left_cancel₀ h2 h2e2

/-- **The `t = 2` count equals the `(sum, sum-of-squares)` count.** Cardinality form of
`twoSymmetric_fiber_eq_e1_psum2_fiber`: the open Round-5 `t = 2` joint-symmetric subset count is
*exactly* the count of `a`-subsets with prescribed window sum `e_1 = c₁` and prescribed sum of squares
`p_2 = c₁² − 2c₂`. This is the object a two-dimensional Gauss/Weil exponential sum
`∑_{ψ₁,ψ₂} ψ₁(∑x − c₁)·ψ₂(∑x² − (c₁²−2c₂))` estimates — the count is now phrased over two
*single-coordinate* statistics (`x` and `x²`), the additive-character-friendly form, rather than the
pair-product `e_2`. -/
theorem twoSymmetric_count_eq_e1_psum2_count [DecidableEq F] (D : ι ↪ F) (h2 : (2 : F) ≠ 0)
    (a : ℕ) (c₁ c₂ : F) :
    ((Finset.univ.powersetCard a).filter
        (fun S => (∑ i ∈ S, D i) = c₁ ∧ (∑ T ∈ S.powersetCard 2, ∏ i ∈ T, D i) = c₂)).card
      = ((Finset.univ.powersetCard a).filter
        (fun S => (∑ i ∈ S, D i) = c₁ ∧ (∑ i ∈ S, (D i) ^ 2) = c₁ ^ 2 - 2 * c₂)).card := by
  rw [twoSymmetric_fiber_eq_e1_psum2_fiber D h2 a c₁ c₂]

/-! ## 3. The degree-drop criterion in the new `(e_1, p_2)` coordinates.

We rephrase Round-5's `degDrop_t2_iff_two_symmetric` (both top coeffs of `p_S` vanish ↔
`e_1 = −g_{k+1}/c ∧ e_2 = g_k/c`) through the Newton identity into `(e_1, p_2)` coordinates. -/

/-- **The `t = 2` degree-drop criterion in `(e_1, p_2)` coordinates.** With `g` of leading coefficient
`c ≠ 0`, `(2 : F) ≠ 0`, and `S` of card `k+2`, both top coefficients of `p_S` vanish **iff** the
window sum and the **sum of squares** hit their fixed targets:

  `e_1(D_S) = ∑_{i∈S} D i = −g.coeff(k+1)/c`   **and**
  `p_2(D_S) = ∑_{i∈S} (D i)² = (g.coeff(k+1)/c)² − 2·g.coeff(k)/c`.

This is `degDrop_t2_iff_two_symmetric` (Round 5) recoordinated by `twoSymmetric_fiber_eq_e1_psum2_fiber`:
the second target `p_2 = e_1² − 2·e_2 = (−g_{k+1}/c)² − 2·(g_k/c)`. The `t = 2` degree-drop family is
thus the **sum / sum-of-squares** joint fiber — the additive-character-friendly form. -/
theorem degDrop_t2_iff_e1_psum2 (D : ι ↪ F) (g : F[X]) {k : ℕ}
    (hc0 : g.leadingCoeff ≠ 0) (h2 : (2 : F) ≠ 0) (S : Finset ι) (hS : S.card = k + 2) :
    ((pSt D g g.leadingCoeff S).coeff (k + 1) = 0 ∧ (pSt D g g.leadingCoeff S).coeff k = 0)
      ↔ ((∑ i ∈ S, D i) = -(g.coeff (k + 1)) / g.leadingCoeff
          ∧ (∑ i ∈ S, (D i) ^ 2)
              = (-(g.coeff (k + 1)) / g.leadingCoeff) ^ 2 - 2 * ((g.coeff k) / g.leadingCoeff)) := by
  rw [degDrop_t2_iff_two_symmetric D g hc0 S hS]
  constructor
  · rintro ⟨h1, he2⟩
    refine ⟨h1, ?_⟩
    have hnewton := sq_window_sum_eq D S
    rw [h1, he2] at hnewton
    linear_combination -hnewton
  · rintro ⟨h1, hp2⟩
    refine ⟨h1, ?_⟩
    have hnewton := sq_window_sum_eq D S
    rw [h1, hp2] at hnewton
    have h2e2 : 2 * (∑ T ∈ S.powersetCard 2, ∏ i ∈ T, D i)
        = 2 * ((g.coeff k) / g.leadingCoeff) := by linear_combination -hnewton
    exact mul_left_cancel₀ h2 h2e2

/-! ## 4. The interior RS-list lower bound driven by the `(e_1, p_2)` (sum / sum-of-squares) count. -/

open Classical in
/-- **The `t = 2` interior-list lower bound from the (sum, sum-of-squares) count.** For `0 < k`,
`k ≤ n = |ι|`, `(2 : F) ≠ 0`, `g` of natDegree exactly `k+2`, and any finite set `𝒞` of `(k+2)`-subsets
in the **sum / sum-of-squares** joint fiber, the RS list at the interior radius `δ = 1 − (k+2)/n` has
size at least `|𝒞|`:

  `|𝒞| ≤ #{ v ∈ RS[D,k] : agree(v, w) ≥ k+2 }`,   `w i = g(D i)`.

This is `twoSymmetric_interior_list_card_ge` (Round 5) recoordinated: the fiber condition is now on
`∑ D i` and `∑ (D i)²` (two single-coordinate statistics), the object a 2-character Weil sum estimates.
Field-independent in the count `|𝒞|`. -/
theorem twoSymmetric_psum2_interior_list_card_ge [Fintype F] [DecidableEq F]
    (D : ι ↪ F) (g : F[X]) {k : ℕ}
    (hgdeg : g.natDegree = k + 2) (hg0 : g ≠ 0) (h2 : (2 : F) ≠ 0)
    (hk : 0 < k) (hkn : k ≤ Fintype.card ι)
    (𝒞 : Finset (Finset ι))
    (hcard : ∀ S ∈ 𝒞, S.card = k + 2)
    (hfiber : ∀ S ∈ 𝒞,
      (∑ i ∈ S, D i) = -(g.coeff (k + 1)) / g.leadingCoeff
      ∧ (∑ i ∈ S, (D i) ^ 2)
          = (-(g.coeff (k + 1)) / g.leadingCoeff) ^ 2 - 2 * ((g.coeff k) / g.leadingCoeff)) :
    𝒞.card ≤
      (Finset.univ.filter (fun v : ι → F =>
        v ∈ ReedSolomon.code D k ∧
          k + 2 ≤ agreeCount v (fun i => g.eval (D i)))).card := by
  -- translate each member's `(e_1, p_2)` membership into the Round-5 `(e_1, e_2)` membership.
  apply twoSymmetric_interior_list_card_ge D g hgdeg hg0 hk hkn 𝒞 hcard
  intro S hSmem
  obtain ⟨h1, hp2⟩ := hfiber S hSmem
  refine ⟨h1, ?_⟩
  have hnewton := sq_window_sum_eq D S
  rw [h1, hp2] at hnewton
  have h2e2 : 2 * (∑ T ∈ S.powersetCard 2, ∏ i ∈ T, D i)
      = 2 * ((g.coeff k) / g.leadingCoeff) := by linear_combination -hnewton
  exact mul_left_cancel₀ h2 h2e2

/-! ## 5. The surviving pigeonhole floor in the power-sum coordinate (the Round-5 NO-GO persists).

The `(e_1, p_2)` joint fiber is a *sub*-fiber of the `e_1`-fiber (`subsetSumCount`), so the Round-4/5
pigeonhole floor `max_{c₁} q·N(a, c₁) ≥ C(n, a)` still upper-bounds every recoordinated joint fiber.
Recoordinatization does **not** by itself lower the count: the magnitude question is unchanged in
difficulty; only the coordinates (sum-of-squares vs. pair-products) are now Weil-friendly. -/

open ArkLib.ProximityGap.Round4NewtonVietaUpper in
/-- **The (sum, sum-of-squares) joint fiber is contained in the `e_1` (subset-sum) fiber.** Adding
the power-sum constraint `p_2 = target₂` can only shrink the `e_1 = target₁` fiber, so its count is
at most `subsetSumCount G a target₁`. Hence the Round-4/5 pigeonhole floor `max ≥ C(n,a)/q` survives
the recoordinatization: no `poly(n)` *upper* bound on the `t = 2` count follows from symmetry. -/
theorem e1_psum2_card_le_subsetSumCount [DecidableEq F] (G : Finset F) (a : ℕ)
    (target₁ target₂ : F) :
    ((G.powersetCard a).filter
        (fun S => (∑ x ∈ S, x) = target₁ ∧ (∑ x ∈ S, x ^ 2) = target₂)).card
      ≤ subsetSumCount G a target₁ := by
  classical
  unfold subsetSumCount
  apply Finset.card_le_card
  intro S hS
  rw [Finset.mem_filter] at hS ⊢
  exact ⟨hS.1, hS.2.1⟩

/-! ## 6. Non-vacuity: the (sum, sum-of-squares) condition is satisfiable; `2 ≠ 0` is realized. -/

set_option linter.unusedSectionVars false in
/-- **The recoordinated degree-drop family is non-vacuous.** Any `(k+2)`-set `S` in the
sum / sum-of-squares fiber yields a singleton degree-drop family, so
`twoSymmetric_psum2_interior_list_card_ge` gives the genuine `1 ≤ #{codewords at interior agreement
k+2}`. We expose the singleton via Round 5's `degDrop_t2_singleton_card` after recoordinating. -/
theorem degDrop_t2_psum2_singleton_card (D : ι ↪ F) (g : F[X]) {k : ℕ}
    (hgdeg : g.natDegree = k + 2) (hg0 : g ≠ 0) (h2 : (2 : F) ≠ 0)
    (hk : 0 < k) (S : Finset ι) (hS : S.card = k + 2)
    (hfiber : (∑ i ∈ S, D i) = -(g.coeff (k + 1)) / g.leadingCoeff
      ∧ (∑ i ∈ S, (D i) ^ 2)
          = (-(g.coeff (k + 1)) / g.leadingCoeff) ^ 2 - 2 * ((g.coeff k) / g.leadingCoeff)) :
    ∃ 𝒮 : DegDropFamily D g k 2, 𝒮.carrier.card = 1 := by
  apply degDrop_t2_singleton_card D g hgdeg hg0 hk S hS
  obtain ⟨h1, hp2⟩ := hfiber
  refine ⟨h1, ?_⟩
  have hnewton := sq_window_sum_eq D S
  rw [h1, hp2] at hnewton
  have h2e2 : 2 * (∑ T ∈ S.powersetCard 2, ∏ i ∈ T, D i)
      = 2 * ((g.coeff k) / g.leadingCoeff) := by linear_combination -hnewton
  exact mul_left_cancel₀ h2 h2e2

/-- **`(2 : F) ≠ 0` is realized in the smooth-domain regime (concrete witness `F = ZMod 13`).** The
smooth `2^k`-subgroup lives in fields of odd characteristic; `ZMod 13` (a field, `13` prime, with a
multiplicative subgroup of order `4 = 2²`) has `(2 : ZMod 13) ≠ 0`. So the `t = 2` `(e_1, p_2)`
recoordinatization is non-vacuously applicable. -/
theorem two_ne_zero_zmod13 : (2 : ZMod 13) ≠ 0 := by decide

end ArkLib.CodingTheory.Round6MultCharacter

/-! ## Axiom audit -/
#print axioms ArkLib.CodingTheory.Round6MultCharacter.sq_window_sum_eq
#print axioms ArkLib.CodingTheory.Round6MultCharacter.two_esymm_two_eq
#print axioms ArkLib.CodingTheory.Round6MultCharacter.twoSymmetric_fiber_eq_e1_psum2_fiber
#print axioms ArkLib.CodingTheory.Round6MultCharacter.twoSymmetric_count_eq_e1_psum2_count
#print axioms ArkLib.CodingTheory.Round6MultCharacter.degDrop_t2_iff_e1_psum2
#print axioms ArkLib.CodingTheory.Round6MultCharacter.twoSymmetric_psum2_interior_list_card_ge
#print axioms ArkLib.CodingTheory.Round6MultCharacter.e1_psum2_card_le_subsetSumCount
#print axioms ArkLib.CodingTheory.Round6MultCharacter.degDrop_t2_psum2_singleton_card
#print axioms ArkLib.CodingTheory.Round6MultCharacter.two_ne_zero_zmod13
