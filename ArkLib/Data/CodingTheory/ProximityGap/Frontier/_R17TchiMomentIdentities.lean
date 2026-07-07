/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R15IncidenceMomentInterchange
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R16LegendreCosetFace

/-!
# LANE JOINT (#466 round 17): joint second moments of the `T_χ` family — exact identities

Round 15/16 reduced corrected Problem B per-χ (`_R16UnconditionalIncidenceBound`: the triangle
`|T_χ| ≤ n` spends the whole phase budget; `|T_χ| ≲ √n·polylog` IS the wall).  This file
computes EXACTLY what cross-χ and cross-offset (cross-`s₀`) averaging buys, for
`T_χ(s₀) = shiftedCharSum χ G s₀ = ∑_{x∈G} χ(s₀−x)` (definition reused from
`_R16LegendreCosetFace`, NOT redefined).  All identities verified exactly in
`scratchpad/probe_r17_tchi_moments.py` (n = 8/16/32, p = 41/73/97/113/193/257, every
character and every offset class) and `probe_r17_fourth_beta4.py` (β≈4 cells
p = 12289/65537/59393/786433).

* **(a) full-family second moment at FIXED offset** (`sum_family_shiftedCharSum`): for `q`
  prime and any `s₀`,
  `∑_{χ mod q} T_{χ̄}(s₀)·T_χ(s₀) = (q−1)·(|G| − [s₀ ∈ G])`
  (stated in the conjugation-free inverse form `∑_χ (∑_x χ((s₀−x)⁻¹))·(∑_y χ(s₀−y))`,
  valid over any domain with enough roots of unity; over ℂ the two forms agree since
  `χ(u⁻¹) = conj(χ(u))` on units).  Cross-χ averaging is PERFECTLY flat: the family of
  `q−1` characters shares total mass `(q−1)·(n − [s₀∈G])`, i.e. mean `|T_χ|² ≤ n` — Wick
  exactly, no log-sized slack.  The deg-subfamily `{χ : χ^deg = χ₀}` partial sum equals
  `deg·#{(x,y) ∈ G² : s₀−x, s₀−y ≠ 0, (s₀−x)/(s₀−y) ∈ (F_q^×)^deg}` — an incidence count
  between the shifted set and power cosets (probe-verified at every cell; the Lean statement
  here is the full family, the subfamily form is the probe's).

* **(b) per-χ second moment over ALL offsets** (`sum_shiftedCharSum_mul_conj`): for ANY
  nontrivial `χ : MulChar F ℂ` on any finite field `F` and ANY finite `G ⊆ F`:
  `∑_{s₀∈F} T_χ(s₀)·conj(T_χ(s₀)) = |G|·q − |G|²`.
  This generalizes `_R16LegendreCosetFace.sum_sq_shiftedQuadSum` (quadratic character, ℤ) to
  the whole `T_χ` family: EVERY face of the round-15 Gauss decomposition has average offset
  mass exactly `< n` (Wick).  Ingredients landed: `mulChar_mul_conj` (`|χ(a)|² = 1` on
  units) and the general two-point orthogonality `sum_mulChar_mul_conj_shift`
  (`∑_a χ(a)·conj(χ(a+b)) = −1` for `b ≠ 0` — the arbitrary-χ form of
  `quadraticChar_two_point`).

* **(c) fourth moment: the named object** (`quarticShiftEnergy`, exact expansion
  `quarticShiftEnergy_expand`): `E₄(χ,G) := ∑_{s₀} |T_χ(s₀)|⁴` expands exactly into the
  **χ-twisted additive quadruple count**
  `∑_{x₁,x₂,y₁,y₂∈G} ∑_{s₀} χ((s₀−x₁)(s₀−x₂))·conj(χ((s₀−y₁)(s₀−y₂)))` — for each
  quadruple a complete character sum of the quartic rational function
  `(s−x₁)(s−x₂)/((s−y₁)(s−y₂))`.  The pairing layer `{x₁,x₂} = {y₁,y₂}` contributes the
  Wick main term (`≈2pn²` complex χ / `≈3pn²` real χ); non-degenerate quadruples are
  Weil-bounded by `3√p` each; the χ = χ₀ degeneration of the quadruple count is the shift
  coincidence count (the `E₂(μ_n)`/Problem-A energy layer).  Probe at β≈4:
  `E₄/Wick ∈ [0.89, 1.06]` across all cells and character orders — **the fourth moment of
  every `T_χ` face OBEYS Wick empirically at β=4** (and provably up to the Weil error
  `n⁴·3√p`, which is `O(main)` exactly at β=4 — the knife edge).  The k=2 stall quantified:
  depth-2 Wick only yields `max|T_χ| ≤ (C·p·n²)^{1/4} ≈ n^{β/4+1/2}` (`= n^{3/2}` at β=4,
  WORSE than the trivial `n`); the moment method needs Wick at depth `r ≈ ln p`, where the
  Weil error `n^{2r}√p` has long since swamped the main term `p·(r n)^r`-ish.  Ledger name:
  **χ-twisted quartic shift energy**.

No closure claimed: (a)+(b) prove both cheap averagings are exactly Wick-flat — there is no
log-sized slack hiding in cross-χ or cross-offset second moments; (c) shows the fourth
moment is Wick-true but value-useless.  Open content stays worst-offset/worst-coset vs
average at depth ~ln p.  Issue #466, round 17, JOINT lane.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.Frontier.R16LegendreCosetFace (shiftedCharSum)

namespace ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities

local notation "conj'" => starRingEnd ℂ

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## Ingredients: unit-circle values and general two-point orthogonality -/

/-- Values of a multiplicative character into ℂ at nonzero arguments lie on the unit
circle: `χ(a)·conj(χ(a)) = 1`. -/
theorem mulChar_mul_conj (χ : MulChar F ℂ) {a : F} (ha : a ≠ 0) :
    χ a * conj' (χ a) = 1 := by
  have hpow : χ a ^ (Fintype.card F - 1) = 1 := by
    rw [← map_pow, FiniteField.pow_card_sub_one_eq_one a ha, map_one]
  have hcard : Fintype.card F - 1 ≠ 0 := by
    have h2 : 1 < Fintype.card F := Fintype.one_lt_card
    omega
  have hnorm : ‖χ a‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hpow hcard
  rw [Complex.mul_conj]
  norm_cast
  rw [Complex.normSq_eq_norm_sq, hnorm, one_pow]

/-- **General two-point orthogonality** (the arbitrary-χ form of
`quadraticChar_two_point`): for a NONTRIVIAL multiplicative character `χ : F → ℂ` and
`b ≠ 0`, `∑_a χ(a)·conj(χ(a+b)) = −1`. -/
theorem sum_mulChar_mul_conj_shift {χ : MulChar F ℂ} (hχ : χ ≠ 1) {b : F} (hb : b ≠ 0) :
    ∑ a : F, χ a * conj' (χ (a + b)) = -1 := by
  classical
  -- restrict to a ≠ 0
  have h0 : ∑ a : F, χ a * conj' (χ (a + b))
      = ∑ a ∈ ({0}ᶜ : Finset F), χ a * conj' (χ (a + b)) := by
    rw [← Finset.sum_subset (Finset.subset_univ _)]
    intro a _ ha
    simp only [Finset.mem_compl, Finset.mem_singleton, not_not] at ha
    subst ha
    rw [χ.map_nonunit (by simp), zero_mul]
  rw [h0]
  -- each term equals conj χ(1 + b·a⁻¹)
  have hterm : ∀ a ∈ ({0}ᶜ : Finset F),
      χ a * conj' (χ (a + b)) = conj' (χ (1 + b * a⁻¹)) := by
    intro a ha
    have ha0 : a ≠ 0 := by simpa using (Finset.mem_compl.mp ha)
    have hab : a + b = a * (1 + b * a⁻¹) := by
      rw [mul_add, mul_one, mul_comm b a⁻¹, mul_inv_cancel_left₀ ha0]
    rw [hab, map_mul, map_mul, ← mul_assoc, mulChar_mul_conj χ ha0, one_mul]
  rw [Finset.sum_congr rfl hterm]
  -- reindex t = 1 + b·a⁻¹ : {0}ᶜ ≃ {1}ᶜ
  have hre : ∑ a ∈ ({0}ᶜ : Finset F), conj' (χ (1 + b * a⁻¹))
      = ∑ t ∈ ({1}ᶜ : Finset F), conj' (χ t) := by
    refine Finset.sum_nbij' (fun a => 1 + b * a⁻¹) (fun t => b * (t - 1)⁻¹) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      have ha0 : a ≠ 0 := by simpa using (Finset.mem_compl.mp ha)
      simp only [Finset.mem_compl, Finset.mem_singleton]
      intro h
      have hba : b * a⁻¹ = 0 := by linear_combination h
      rcases mul_eq_zero.mp hba with h' | h'
      · exact hb h'
      · exact ha0 (inv_eq_zero.mp h')
    · intro t ht
      have ht1 : t ≠ 1 := by simpa using (Finset.mem_compl.mp ht)
      have ht1' : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
      simp only [Finset.mem_compl, Finset.mem_singleton]
      exact mul_ne_zero hb (inv_ne_zero ht1')
    · intro a ha
      have ha0 : a ≠ 0 := by simpa using (Finset.mem_compl.mp ha)
      show b * ((1 + b * a⁻¹) - 1)⁻¹ = a
      have h1 : (1 : F) + b * a⁻¹ - 1 = b * a⁻¹ := by ring
      rw [h1, mul_inv, inv_inv, mul_inv_cancel_left₀ hb]
    · intro t ht
      have ht1 : t ≠ 1 := by simpa using (Finset.mem_compl.mp ht)
      have ht1' : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
      show 1 + b * (b * (t - 1)⁻¹)⁻¹ = t
      rw [mul_inv, inv_inv, mul_inv_cancel_left₀ hb]
      ring
    · intro a _; rfl
  rw [hre]
  -- ∑_{t≠1} χ(t) = −1 (nontriviality), then push through conj
  have hsplit := Finset.sum_compl_add_sum ({1} : Finset F) (f := fun t => χ t)
  rw [Finset.sum_singleton, MulChar.sum_eq_zero_of_ne_one hχ, map_one] at hsplit
  have hsum : ∑ t ∈ ({1}ᶜ : Finset F), χ t = -1 := by
    linear_combination hsplit
  rw [← map_sum, hsum, map_neg, map_one]

/-- Diagonal two-point sum: `∑_a χ(a)·conj(χ(a)) = q − 1`. -/
theorem sum_mulChar_mul_conj_self (χ : MulChar F ℂ) :
    ∑ a : F, χ a * conj' (χ a) = (Fintype.card F : ℂ) - 1 := by
  classical
  have h2 : ∑ a : F, χ a * conj' (χ a)
      = ∑ a ∈ ({0}ᶜ : Finset F), χ a * conj' (χ a) := by
    symm
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro a _ ha
    have : a = 0 := by simpa using ha
    subst this
    rw [χ.map_nonunit (by simp), zero_mul]
  have h1 : ∑ a ∈ ({0}ᶜ : Finset F), χ a * conj' (χ a)
      = ∑ _a ∈ ({0}ᶜ : Finset F), (1 : ℂ) :=
    Finset.sum_congr rfl fun a ha =>
      mulChar_mul_conj χ (by simpa using (Finset.mem_compl.mp ha))
  rw [h2, h1, Finset.sum_const, Finset.card_compl, Finset.card_singleton,
    nsmul_eq_mul, mul_one, Nat.cast_sub Fintype.card_pos, Nat.cast_one]

/-! ## (b) The exact second moment over ALL offsets, arbitrary nontrivial χ -/

/-- **(b) Exact per-χ second moment over all offsets** (generalizes
`_R16LegendreCosetFace.sum_sq_shiftedQuadSum` from the quadratic character over ℤ to EVERY
nontrivial `χ : MulChar F ℂ`, i.e. to every `T_χ` face of the round-15 Gauss
decomposition): `∑_{s₀∈F} T_χ(s₀)·conj(T_χ(s₀)) = |G|·q − |G|²`. -/
theorem sum_shiftedCharSum_mul_conj {χ : MulChar F ℂ} (hχ : χ ≠ 1) (G : Finset F) :
    ∑ s₀ : F, shiftedCharSum χ G s₀ * conj' (shiftedCharSum χ G s₀)
      = (G.card : ℂ) * (Fintype.card F : ℂ) - (G.card : ℂ) ^ 2 := by
  classical
  have expand : ∀ s₀ : F, shiftedCharSum χ G s₀ * conj' (shiftedCharSum χ G s₀)
      = ∑ x ∈ G, ∑ y ∈ G, χ (s₀ - x) * conj' (χ (s₀ - y)) := by
    intro s₀
    rw [shiftedCharSum, map_sum, Finset.sum_mul_sum]
  calc ∑ s₀ : F, shiftedCharSum χ G s₀ * conj' (shiftedCharSum χ G s₀)
      = ∑ s₀ : F, ∑ x ∈ G, ∑ y ∈ G, χ (s₀ - x) * conj' (χ (s₀ - y)) := by
        exact Finset.sum_congr rfl fun s₀ _ => expand s₀
    _ = ∑ x ∈ G, ∑ y ∈ G, ∑ s₀ : F, χ (s₀ - x) * conj' (χ (s₀ - y)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ x ∈ G, ∑ y ∈ G,
          (if x = y then (Fintype.card F : ℂ) - 1 else -1) := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        have hsub : ∑ s₀ : F, χ (s₀ - x) * conj' (χ (s₀ - y))
            = ∑ a : F, χ a * conj' (χ (a + (x - y))) := by
          refine Fintype.sum_equiv (Equiv.subRight x) _ _ fun s₀ => ?_
          simp only [Equiv.subRight_apply]
          rw [show s₀ - y = s₀ - x + (x - y) from by ring]
        rw [hsub]
        by_cases hxy : x = y
        · subst hxy
          simp only [sub_self, add_zero, if_true]
          exact sum_mulChar_mul_conj_self χ
        · rw [if_neg hxy]
          exact sum_mulChar_mul_conj_shift hχ (sub_ne_zero.mpr hxy)
    _ = (G.card : ℂ) * (Fintype.card F : ℂ) - (G.card : ℂ) ^ 2 := by
        have hinner : ∀ x ∈ G, (∑ y ∈ G,
            (if x = y then (Fintype.card F : ℂ) - 1 else -1))
            = (Fintype.card F : ℂ) - (G.card : ℂ) := by
          intro x hx
          have hsplit : ∀ y ∈ G, (if x = y then (Fintype.card F : ℂ) - 1 else -1)
              = -1 + (if x = y then (Fintype.card F : ℂ) else 0) := by
            intro y _; split_ifs <;> ring
          rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_const,
            Finset.sum_ite_eq G x (fun _ => (Fintype.card F : ℂ)), if_pos hx]
          ring
        rw [Finset.sum_congr rfl hinner, Finset.sum_const]
        ring

/-! ## (a) The full-family second moment at a FIXED offset -/

section Family

variable {q : ℕ} [NeZero q] (R : Type*) [CommRing R] [IsDomain R]
  [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod q)ˣ)]

/-- **(a) Full-family second moment at a fixed offset** (conjugation-free inverse form —
over ℂ, `χ((s₀−x)⁻¹) = conj(χ(s₀−x))` on units by `mulChar_mul_conj`, so this is
`∑_χ |T_χ(s₀)|²`): for `q` PRIME, any evaluation set `G ⊆ F_q` and ANY offset `s₀`,
`∑_{χ mod q} (∑_{x∈G} χ((s₀−x)⁻¹))·(∑_{y∈G} χ(s₀−y)) = (q−1)·(|G| − [s₀ ∈ G])`.
Cross-χ averaging is exactly Wick-flat: mean `|T_χ(s₀)|²` over the family is `≤ |G|`. -/
theorem sum_family_shiftedCharSum (hq : q.Prime) (G : Finset (ZMod q)) (s₀ : ZMod q) :
    ∑ χ : DirichletCharacter R q,
        (∑ x ∈ G, χ ((s₀ - x)⁻¹)) * (∑ y ∈ G, χ (s₀ - y))
      = (q.totient : R) * ((G.card : R) - if s₀ ∈ G then 1 else 0) := by
  haveI : Fact q.Prime := ⟨hq⟩
  classical
  -- expand the product and pull the character sum inside
  have hswap : ∑ χ : DirichletCharacter R q,
      (∑ x ∈ G, χ ((s₀ - x)⁻¹)) * (∑ y ∈ G, χ (s₀ - y))
      = ∑ x ∈ G, ∑ y ∈ G, ∑ χ : DirichletCharacter R q,
          χ ((s₀ - x)⁻¹) * χ (s₀ - y) := by
    simp_rw [Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
  rw [hswap]
  -- evaluate the inner character sum by orthogonality
  have hinner : ∀ x ∈ G, ∀ y ∈ G, (∑ χ : DirichletCharacter R q,
      χ ((s₀ - x)⁻¹) * χ (s₀ - y))
      = if x ≠ s₀ ∧ x = y then (q.totient : R) else 0 := by
    intro x _ y _
    by_cases hx : x = s₀
    · -- spike column x = s₀: every term vanishes since χ(0⁻¹) = χ(0) = 0
      subst hx
      rw [if_neg (by simp)]
      have hz : ∀ χ : DirichletCharacter R q, χ ((x - x)⁻¹) * χ (x - y) = 0 := by
        intro χ
        rw [sub_self, inv_zero, χ.map_nonunit (by simp), zero_mul]
      rw [Finset.sum_congr rfl fun χ _ => hz χ, Finset.sum_const, smul_zero]
    · -- unit column: orthogonality
      have hne : s₀ - x ≠ 0 := sub_ne_zero.mpr fun h => hx h.symm
      have hu : IsUnit (s₀ - x) := isUnit_iff_ne_zero.mpr hne
      rw [DirichletCharacter.sum_char_inv_mul_char_eq R hu (s₀ - y)]
      have hiff : s₀ - x = s₀ - y ↔ x = y := by
        constructor
        · intro h; linear_combination -h
        · intro h; rw [h]
      by_cases hxy : x = y
      · rw [if_pos (hiff.mpr hxy), if_pos ⟨fun h => hx h, hxy⟩]
      · rw [if_neg (fun h => hxy (hiff.mp h)), if_neg (fun h => hxy h.2)]
  rw [Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => hinner x hx y hy]
  -- count the surviving diagonal
  have hrow : ∀ x ∈ G, (∑ y ∈ G, if x ≠ s₀ ∧ x = y then (q.totient : R) else 0)
      = if x ≠ s₀ then (q.totient : R) else 0 := by
    intro x hx
    by_cases hxs : x = s₀
    · subst hxs
      rw [if_neg (by simp)]
      refine Finset.sum_eq_zero fun y _ => ?_
      rw [if_neg (by tauto)]
    · rw [if_pos hxs]
      have : ∀ y ∈ G, (if x ≠ s₀ ∧ x = y then (q.totient : R) else 0)
          = if x = y then (q.totient : R) else 0 := by
        intro y _
        by_cases hxy : x = y
        · rw [if_pos ⟨hxs, hxy⟩, if_pos hxy]
        · rw [if_neg (fun h => hxy h.2), if_neg hxy]
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq G x fun _ => (q.totient : R),
        if_pos hx]
  rw [Finset.sum_congr rfl hrow]
  -- final count: |{x ∈ G : x ≠ s₀}| = |G| − [s₀ ∈ G]
  by_cases hs : s₀ ∈ G
  · rw [if_pos hs]
    have hsplit : ∀ x ∈ G, (if x ≠ s₀ then (q.totient : R) else 0)
        = (q.totient : R) - (if x = s₀ then (q.totient : R) else 0) := by
      intro x _
      by_cases hxs : x = s₀
      · rw [if_neg (by simpa using hxs), if_pos hxs]; ring
      · rw [if_pos hxs, if_neg hxs]; ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.sum_ite_eq' G s₀ fun _ => (q.totient : R), if_pos hs]
    ring
  · rw [if_neg hs]
    have hall : ∀ x ∈ G, (if x ≠ s₀ then (q.totient : R) else 0) = (q.totient : R) := by
      intro x hx
      rw [if_pos (show x ≠ s₀ from fun h => hs (by rwa [h] at hx))]
    rw [Finset.sum_congr rfl hall, Finset.sum_const]
    ring

end Family

/-! ## (c) The fourth moment: the χ-twisted quartic shift energy (named + exact expansion) -/

/-- **The χ-twisted quartic shift energy** `E₄(χ,G) = ∑_{s₀} |T_χ(s₀)|⁴` (over ℂ,
`|T|⁴ = (T·conj T)²`).  This is the joint fourth moment of the `T_χ` face; see the module
docstring for the Wick main term / Weil error / k=2 stall analysis. -/
noncomputable def quarticShiftEnergy (χ : MulChar F ℂ) (G : Finset F) : ℂ :=
  ∑ s₀ : F, (shiftedCharSum χ G s₀ * conj' (shiftedCharSum χ G s₀)) ^ 2

/-- Pointwise exact expansion of `|T_χ(s₀)|⁴` into the χ-twisted quadruple sum. -/
theorem shiftedCharSum_quartic_expand (χ : MulChar F ℂ) (G : Finset F) (s₀ : F) :
    (shiftedCharSum χ G s₀ * conj' (shiftedCharSum χ G s₀)) ^ 2
      = ∑ x₁ ∈ G, ∑ x₂ ∈ G, ∑ y₁ ∈ G, ∑ y₂ ∈ G,
          (χ (s₀ - x₁) * conj' (χ (s₀ - y₁)))
            * (χ (s₀ - x₂) * conj' (χ (s₀ - y₂))) := by
  have expand : shiftedCharSum χ G s₀ * conj' (shiftedCharSum χ G s₀)
      = ∑ x ∈ G, ∑ y ∈ G, χ (s₀ - x) * conj' (χ (s₀ - y)) := by
    rw [shiftedCharSum, map_sum, Finset.sum_mul_sum]
  rw [pow_two, expand, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun x₁ _ => Finset.sum_congr rfl fun x₂ _ =>
    Finset.sum_mul_sum _ _ _ _

/-- **(c) Exact expansion of the fourth moment**: the χ-twisted quartic shift energy equals
the χ-twisted additive quadruple count
`∑_{s₀} ∑_{x₁,y₁,x₂,y₂ ∈ G} χ(s₀−x₁)·conj(χ(s₀−y₁))·χ(s₀−x₂)·conj(χ(s₀−y₂))` — per
quadruple, a complete character sum of the quartic rational function
`(s−x₁)(s−x₂)/((s−y₁)(s−y₂))`.  The `{x₁,x₂} = {y₁,y₂}` pairing layer is the Wick main
term; the χ = χ₀ layer of the count is the `E₂` shift-coincidence energy. -/
theorem quarticShiftEnergy_expand (χ : MulChar F ℂ) (G : Finset F) :
    quarticShiftEnergy χ G
      = ∑ s₀ : F, ∑ x₁ ∈ G, ∑ x₂ ∈ G, ∑ y₁ ∈ G, ∑ y₂ ∈ G,
          (χ (s₀ - x₁) * conj' (χ (s₀ - y₁)))
            * (χ (s₀ - x₂) * conj' (χ (s₀ - y₂))) :=
  Finset.sum_congr rfl fun s₀ _ => shiftedCharSum_quartic_expand χ G s₀

/-! ## (d) Deep-rung point obstruction -/

/-- The `2r`-th real moment of a shifted thin character-sum face.  This is the deep-rung
object that would be needed to turn the r=2 Weil lane into a corrected Problem-B proof. -/
noncomputable def shiftedCharMoment (χ : MulChar F ℂ) (G : Finset F) (r : ℕ) : ℝ :=
  ∑ s₀ : F, ‖shiftedCharSum χ G s₀‖ ^ (2 * r)

/-- The deleted-offset version of `shiftedCharMoment`.  For corrected Problem B the intended
deleted set is `D = {0} ∪ μ_n`; using the full-line moment without this deletion includes the
trivial `s₀ = 0` spike for characters that are constant on `μ_n`. -/
noncomputable def shiftedCharMomentAway
    (χ : MulChar F ℂ) (G D : Finset F) (r : ℕ) : ℝ :=
  ∑ s₀ ∈ Finset.univ \ D, ‖shiftedCharSum χ G s₀‖ ^ (2 * r)

/-- The corrected-away Wick target for a single shifted character-sum face.  The intended
application is `D = {0} ∪ μ_n`; this avoids the full-line diagonal spike and is the object that
`probe_r17_tchi_high_moments.py --away` finds stable through the tested deep rungs. -/
def ShiftedCharAwayWickAt (χ : MulChar F ℂ) (G D : Finset F) (r : ℕ) : Prop :=
  shiftedCharMomentAway χ G D r
    ≤ (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r

/-- Full corrected-away Wick tower for a shifted character-sum face. -/
def ShiftedCharAwayWick (χ : MulChar F ℂ) (G D : Finset F) : Prop :=
  ∀ r : ℕ, ShiftedCharAwayWickAt χ G D r

/-- A single large offset gives a lower bound for every deep moment. -/
theorem shiftedCharMoment_point_le (χ : MulChar F ℂ) (G : Finset F) (r : ℕ) (s₀ : F) :
    ‖shiftedCharSum χ G s₀‖ ^ (2 * r) ≤ shiftedCharMoment χ G r := by
  classical
  unfold shiftedCharMoment
  simpa using
    (Finset.single_le_sum
      (s := (Finset.univ : Finset F))
      (f := fun s : F => ‖shiftedCharSum χ G s‖ ^ (2 * r))
      (fun s _ => by positivity) (Finset.mem_univ s₀))

/-- A large pointwise value forces a corresponding lower bound for every deep moment. -/
theorem pow_le_shiftedCharMoment_of_le_point
    (χ : MulChar F ℂ) (G : Finset F) (r : ℕ) {A : ℝ} (hA0 : 0 ≤ A) {s₀ : F}
    (hA : A ≤ ‖shiftedCharSum χ G s₀‖) :
    A ^ (2 * r) ≤ shiftedCharMoment χ G r := by
  exact le_trans (pow_le_pow_left₀ hA0 hA (2 * r)) (shiftedCharMoment_point_le χ G r s₀)

/-- A single large non-deleted offset gives a lower bound for every deleted deep moment. -/
theorem shiftedCharMomentAway_point_le
    (χ : MulChar F ℂ) (G D : Finset F) (r : ℕ) {s₀ : F} (hs₀ : s₀ ∉ D) :
    ‖shiftedCharSum χ G s₀‖ ^ (2 * r) ≤ shiftedCharMomentAway χ G D r := by
  classical
  unfold shiftedCharMomentAway
  have hs : s₀ ∈ Finset.univ \ D := Finset.mem_sdiff.mpr ⟨Finset.mem_univ s₀, hs₀⟩
  exact
    (Finset.single_le_sum
      (s := Finset.univ \ D)
      (f := fun s : F => ‖shiftedCharSum χ G s‖ ^ (2 * r))
      (fun s _ => by positivity) hs)

/-- Deleted-moment version of `pow_le_shiftedCharMoment_of_le_point`. -/
theorem pow_le_shiftedCharMomentAway_of_le_point
    (χ : MulChar F ℂ) (G D : Finset F) (r : ℕ) {A : ℝ} (hA0 : 0 ≤ A)
    {s₀ : F} (hs₀ : s₀ ∉ D) (hA : A ≤ ‖shiftedCharSum χ G s₀‖) :
    A ^ (2 * r) ≤ shiftedCharMomentAway χ G D r := by
  exact le_trans (pow_le_pow_left₀ hA0 hA (2 * r))
    (shiftedCharMomentAway_point_le χ G D r hs₀)

/-- Any Wick-shaped deep moment bound immediately forces a pointwise bound.  This formalizes the
round-17 bottleneck seen in `probe_r17_tchi_high_moments.py`: deep moment control is already a
worst-offset statement in disguise. -/
theorem shiftedCharSum_pow_le_of_moment_le
    (χ : MulChar F ℂ) (G : Finset F) (r : ℕ) {B : ℝ}
    (hmom : shiftedCharMoment χ G r ≤ B) (s₀ : F) :
    ‖shiftedCharSum χ G s₀‖ ^ (2 * r) ≤ B :=
  le_trans (shiftedCharMoment_point_le χ G r s₀) hmom

/-- The named corrected-away Wick target gives the expected pointwise power bound on every
non-deleted offset. -/
theorem shiftedCharSum_pow_le_of_awayWickAt
    (χ : MulChar F ℂ) (G D : Finset F) (r : ℕ)
    (hwick : ShiftedCharAwayWickAt χ G D r) {s₀ : F} (hs₀ : s₀ ∉ D) :
    ‖shiftedCharSum χ G s₀‖ ^ (2 * r)
      ≤ (Fintype.card F : ℝ) * (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r :=
  le_trans (shiftedCharMomentAway_point_le χ G D r hs₀) hwick

end ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.mulChar_mul_conj
#print axioms ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.sum_mulChar_mul_conj_shift
#print axioms ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.sum_mulChar_mul_conj_self
#print axioms ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.sum_shiftedCharSum_mul_conj
#print axioms ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.sum_family_shiftedCharSum
#print axioms ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.shiftedCharSum_quartic_expand
#print axioms ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.quarticShiftEnergy_expand
#print axioms ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.shiftedCharMoment_point_le
#print axioms ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.pow_le_shiftedCharMoment_of_le_point
#print axioms ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.shiftedCharMomentAway_point_le
#print axioms
  ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.pow_le_shiftedCharMomentAway_of_le_point
#print axioms ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.shiftedCharSum_pow_le_of_moment_le
#print axioms ArkLib.ProximityGap.Frontier.R17TchiMomentIdentities.shiftedCharSum_pow_le_of_awayWickAt
