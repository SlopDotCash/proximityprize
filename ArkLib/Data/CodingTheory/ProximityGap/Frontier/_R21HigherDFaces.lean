/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R18FourthMomentTwist

/-!
# LANE HIGHERD (#466 round 21): ALL order-d faces of `FourthMomentTwistBound` reduce to ONE
# uniform triple-linear Hasse input — the Möbius-lite substitution is ORDER-BLIND and the
# Weil constant does NOT grow with d

Round 20 discharged the quadratic (order-2) face of `QuarticWeilInput` down to
`LegendreCubicHasse`.  The remaining faces — `χ` of order `d = 4, 8, …, m` in `chiFamily` —
carried the worry that the kernel `(t−x₁)(t−x₂)(t−y₁)^{d−1}(t−y₂)^{d−1}` has degree `2d`
(genus growing with `d`), so the per-tuple Weil constant might grow like `d ~ m` and break
the rung arithmetic.  This file settles the structure:

## (a) The substitution is ORDER-BLIND and hypothesis-free (probe-exact, then PROVEN)

Substituting `t = y₂ + 1/s` (the R20 Möbius-lite map, now aimed at `y₂`):
`t − a = ((y₂−a)s + 1)/s`, and the four `s`-Jacobian factors collect into
`(χ(s⁻¹)·conj χ(s⁻¹))² = 1` — pure unit-circle cancellation, needing NO order-`d`
divisibility at all.  The exact identity, for EVERY `MulChar F ℂ` and EVERY tuple
(no distinctness, no nondegeneracy, no nontriviality):

  `quadTerm χ ((x₁,x₂),(y₁,y₂)) = ∑_s χ((u s+1)(v s+1))·conj χ(w s+1) − 1`,
  `u = y₂−x₁`, `v = y₂−x₂`, `w = y₂−y₁`.

PROVEN below (`quadTerm_eq_tripleSum_sub_one`, axiom-clean).  Writing `conj χ = χ^{d−1}`
for order-`d` `χ`, the right side is `∑_s χ(L₁L₂L₃^{d−1})`: degree `d+1`, but only **3
distinct linear roots** for every non-pair-match tuple — so the Weil bound is
`(3−1)√p = 2√p` **uniformly in d**.  Genus grows with `d`; the Weil CONSTANT does not.
`Cw = 2` (not `~m`), and the rung constant `6` survives the whole family unchanged.

## (b) Probe (`probe_r21_higherd.py`, scratchpad; p = 4177/12289 (n=8), 65537 (n=16))

* identity error ≤ 1e-11 over 300 random tuples per cell, orders d = 2,4,8,16 — EXACT;
* `∑_t|T_χ|⁴/(n²p)` = 2.67–3.02 (d=2), 1.84–2.00 (d=4,8,16) — Wick-uniform in d, and
  SMALLER for d > 2 (fewer degenerate tuples: 2n² vs 3n²); constant 6 keeps ≥ 2× room;
* per-nondegenerate-tuple `max‖S‖/√p` = 1.01–2.01 across ALL orders — never above
  `2√p + 1`, confirming the 3-root Weil shape with constant 2, uniform in d.

## (c) The order-d degeneracy classification

Kernel `= c·h^d` iff all root multiplicities `≡ 0 (mod d)`.  Multiplicity pattern:
`x`-roots carry 1, `y`-roots carry `d−1 ≡ −1`.  Exhausting coincidences:
* pair-match (`(x₁,x₂) = (y₁,y₂)` or the swap): matched roots carry `1+(d−1) = d ≡ 0` —
  degenerate for EVERY d (`d ∣ d`, `pairMatch_mult_divisible`);
* the diagonal clause (`x₁ = x₂ ∧ y₁ = y₂`, `x ≠ y`): multiplicities `2` and `2(d−1) ≡ −2`
  — degenerate iff `d ∣ 2` iff `d = 2` (`diag_mult_divisible_iff_two`).  The R18 predicate's
  third clause is d=2-SPECIFIC; for d ≥ 3 degeneracy is exactly `IsPairMatch` (≤ 2n² tuples);
* all mixed coincidences give some multiplicity in `{1, 2, d+1, 2d−1} ∌ 0 (mod d)` for the
  relevant d — nondegenerate.
Since `IsPairMatch ⊆ IsDegenerate` (proven), quantifying the named input over
`¬IsDegenerate` is SAFE for every order simultaneously (it excludes a superset, and for
d ≥ 3 the extra excluded diagonal tuples are ≤ n² of the trivial layer, absorbed in `6`).

## PROVEN here (axiom-clean)

* `quadTerm_eq_tripleSum_sub_one` — the order-blind substitution identity (exact, ∀ χ, ∀ z).
* `IsPairMatch` + `isDegenerate_of_isPairMatch` + `card_filter_pairMatch_le` (≤ 2n²).
* `pairMatch_mult_divisible` / `diag_mult_divisible_iff_two` — the (c) arithmetic cores.
* `TripleLinearHasse` — THE named order-uniform Hasse input (`‖tripleSum‖ ≤ 2√p` per
  nondegenerate tuple; for order-2 χ this is implied by `LegendreCubicHasse` via R20's
  normal form, for order d it is Weil for `∑ χ(L₁L₂L₃^{d−1})`, 3 roots, genus ≤ d−1).
* `quarticWeilInput_of_tripleLinearHasse` (needs only `4 ≤ p`) and
  `fourthMomentTwistBound_of_tripleLinearHasse`: the ENTIRE r=2 rung
  `FourthMomentTwistBound G X 6` — all orders at once — from the `TripleLinearHasse`
  family, constants uniform in d.  `K(m)`'s `(m−1)⁴` is untouched: no `Cw(d)` growth enters.

## HONEST residual accounting (no closure claimed)

`TripleLinearHasse` is NOT proven for any χ here.  It is Weil for the curve
`y^d = L₁L₂L₃^{d−1}` (genus ≤ d−1, a superelliptic/Kummer curve) — true mathematics,
absent from Mathlib.  For the order-2 member it coincides (up to the R20 normal form) with
`LegendreCubicHasse`.  What this file changes: the r=2 rung now rests on ONE named
per-order input family with a UNIFORM constant 2, instead of an unstructured `(m−1)`-growth
worry — the complete formalization surface of the rung.

Issue #466, round 21, HIGHERD lane.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.Frontier.R16LegendreCosetFace (shiftedCharSum)

namespace ArkLib.ProximityGap.Frontier.R21HigherDFaces

open ArkLib.ProximityGap.Frontier.R18FourthMomentTwist

local notation "conj'" => starRingEnd ℂ

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## The reduced triple-linear kernel -/

/-- The reduced kernel sum after the `t = y₂ + 1/s` substitution:
`∑_s χ((u s + 1)(v s + 1)) · conj χ(w s + 1)`.  For `χ` of order `d` this is
`∑_s χ((us+1)(vs+1)(ws+1)^{d−1})` — degree `d+1`, but only 3 distinct linear roots. -/
noncomputable def tripleSum (χ : MulChar F ℂ) (u v w : F) : ℂ :=
  ∑ s : F, χ ((u * s + 1) * (v * s + 1)) * conj' (χ (w * s + 1))

/-- **THE ORDER-BLIND SUBSTITUTION IDENTITY** (exact, hypothesis-free): for EVERY
multiplicative character and EVERY tuple,
`quadTerm χ ((x₁,x₂),(y₁,y₂)) = tripleSum χ (y₂−x₁) (y₂−x₂) (y₂−y₁) − 1`.
The `s`-Jacobian collects into `(χ(s⁻¹)·conj χ(s⁻¹))² = 1` — unit-circle cancellation
only; no order-`d` divisibility is used anywhere. -/
theorem quadTerm_eq_tripleSum_sub_one (χ : MulChar F ℂ) (x₁ x₂ y₁ y₂ : F) :
    quadTerm χ ((x₁, x₂), (y₁, y₂))
      = tripleSum χ (y₂ - x₁) (y₂ - x₂) (y₂ - y₁) - 1 := by
  classical
  unfold quadTerm tripleSum
  dsimp only
  -- Step A: drop t = y₂ (its term vanishes: conj χ(0) = 0)
  have hA : ∑ t : F, (χ (t - x₁) * χ (t - x₂))
        * (conj' (χ (t - y₁)) * conj' (χ (t - y₂)))
      = ∑ t ∈ Finset.univ.erase y₂, (χ (t - x₁) * χ (t - x₂))
        * (conj' (χ (t - y₁)) * conj' (χ (t - y₂))) := by
    rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ y₂)]
    have h0 : χ (y₂ - y₂) = 0 := by
      rw [sub_self]
      exact χ.map_nonunit (by simp)
    rw [h0]
    simp
  -- Step B: reindex s = (t − y₂)⁻¹
  have hB : ∑ t ∈ Finset.univ.erase y₂, (χ (t - x₁) * χ (t - x₂))
        * (conj' (χ (t - y₁)) * conj' (χ (t - y₂)))
      = ∑ s ∈ Finset.univ.erase (0 : F),
          χ (((y₂ - x₁) * s + 1) * ((y₂ - x₂) * s + 1))
            * conj' (χ ((y₂ - y₁) * s + 1)) := by
    refine Finset.sum_nbij' (fun t => (t - y₂)⁻¹) (fun s => y₂ + s⁻¹) ?_ ?_ ?_ ?_ ?_
    · intro t ht
      exact Finset.mem_erase.mpr
        ⟨inv_ne_zero (sub_ne_zero.mpr (Finset.mem_erase.mp ht).1), Finset.mem_univ _⟩
    · intro s hs
      have hs0 : s ≠ 0 := (Finset.mem_erase.mp hs).1
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro h
      have hinv : s⁻¹ = 0 := by linear_combination h
      exact hs0 (inv_eq_zero.mp hinv)
    · intro t ht
      have htd : t - y₂ ≠ 0 := sub_ne_zero.mpr (Finset.mem_erase.mp ht).1
      change y₂ + ((t - y₂)⁻¹)⁻¹ = t
      rw [inv_inv]; ring
    · intro s hs
      change (y₂ + s⁻¹ - y₂)⁻¹ = s
      rw [show y₂ + s⁻¹ - y₂ = s⁻¹ by ring, inv_inv]
    · intro t ht
      have htd : t - y₂ ≠ 0 := sub_ne_zero.mpr (Finset.mem_erase.mp ht).1
      -- each linear factor: t − a = ((y₂−a)·(t−y₂)⁻¹ + 1)·(t−y₂)
      have e : ∀ a : F, t - a = ((y₂ - a) * (t - y₂)⁻¹ + 1) * (t - y₂) := by
        intro a
        field_simp
        ring
      have hunit : χ (t - y₂) * conj' (χ (t - y₂)) = 1 := mulChar_mul_conj χ htd
      calc (χ (t - x₁) * χ (t - x₂)) * (conj' (χ (t - y₁)) * conj' (χ (t - y₂)))
          = (χ (((y₂ - x₁) * (t - y₂)⁻¹ + 1) * (t - y₂))
                * χ (((y₂ - x₂) * (t - y₂)⁻¹ + 1) * (t - y₂)))
              * (conj' (χ (((y₂ - y₁) * (t - y₂)⁻¹ + 1) * (t - y₂)))
                * conj' (χ (t - y₂))) := by
            rw [← e x₁, ← e x₂, ← e y₁]
        _ = (χ ((y₂ - x₁) * (t - y₂)⁻¹ + 1) * χ ((y₂ - x₂) * (t - y₂)⁻¹ + 1)
              * conj' (χ ((y₂ - y₁) * (t - y₂)⁻¹ + 1)))
            * (χ (t - y₂) * conj' (χ (t - y₂))) ^ 2 := by
            simp only [map_mul]
            ring
        _ = χ (((y₂ - x₁) * (t - y₂)⁻¹ + 1) * ((y₂ - x₂) * (t - y₂)⁻¹ + 1))
              * conj' (χ ((y₂ - y₁) * (t - y₂)⁻¹ + 1)) := by
            rw [hunit, one_pow, mul_one, map_mul]
  -- Step C: complete the reduced sum at s = 0 (value χ(1)·conj χ(1) = 1)
  have hC : ∑ s ∈ Finset.univ.erase (0 : F),
        χ (((y₂ - x₁) * s + 1) * ((y₂ - x₂) * s + 1)) * conj' (χ ((y₂ - y₁) * s + 1))
      = (∑ s : F, χ (((y₂ - x₁) * s + 1) * ((y₂ - x₂) * s + 1))
          * conj' (χ ((y₂ - y₁) * s + 1))) - 1 := by
    have h := Finset.sum_erase_add Finset.univ
      (fun s : F => χ (((y₂ - x₁) * s + 1) * ((y₂ - x₂) * s + 1))
        * conj' (χ ((y₂ - y₁) * s + 1)))
      (Finset.mem_univ (0 : F))
    simp only [mul_zero, zero_add, mul_one, map_one] at h
    linear_combination h
  rw [hA, hB, hC]

/-! ## The order-d degeneracy layer -/

/-- **The order-d ≥ 3 degeneracy predicate**: the kernel
`(t−x₁)(t−x₂)(t−y₁)^{d−1}(t−y₂)^{d−1}` is a perfect d-th power (for d ≥ 3) iff the `x`-pair
matches the `y`-pair as a multiset.  This is the R18 `IsDegenerate` WITHOUT its
d=2-specific third (diagonal) clause. -/
def IsPairMatch (z : (F × F) × (F × F)) : Prop :=
  (z.1.1 = z.2.1 ∧ z.1.2 = z.2.2) ∨ (z.1.1 = z.2.2 ∧ z.1.2 = z.2.1)

instance : DecidablePred (IsPairMatch (F := F)) := fun z => by
  unfold IsPairMatch; infer_instance

/-- Pair-match tuples are degenerate in the R18 sense — quantifying the named Weil input
over `¬IsDegenerate` excludes a SUPERSET of the order-d ≥ 3 degeneracies, so one predicate
serves every order simultaneously. -/
theorem isDegenerate_of_isPairMatch (z : (F × F) × (F × F)) (h : IsPairMatch z) :
    IsDegenerate z := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

/-- At most `2n²` pair-match tuples (vs `3n²` for the d=2 predicate). -/
theorem card_filter_pairMatch_le (G : Finset F) :
    (((G ×ˢ G) ×ˢ (G ×ˢ G)).filter IsPairMatch).card ≤ 2 * G.card ^ 2 := by
  classical
  have hsub : ((G ×ˢ G) ×ˢ (G ×ˢ G)).filter IsPairMatch
      ⊆ ((G ×ˢ G).image (fun a => (a, a)))
        ∪ ((G ×ˢ G).image (fun a => (a, (a.2, a.1)))) := by
    intro z hz
    obtain ⟨hzQ, hpm⟩ := Finset.mem_filter.mp hz
    obtain ⟨hz1, _⟩ := Finset.mem_product.mp hzQ
    rcases hpm with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨z.1, hz1, ?_⟩)
      exact Prod.ext_iff.mpr ⟨rfl, Prod.ext_iff.mpr ⟨ha, hb⟩⟩
    · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z.1, hz1, ?_⟩)
      exact Prod.ext_iff.mpr ⟨rfl, Prod.ext_iff.mpr ⟨hb, ha⟩⟩
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_union_le _ _) ?_
  have ha : ((G ×ˢ G).image (fun a : F × F => (a, a))).card ≤ G.card ^ 2 := by
    refine le_trans (Finset.card_image_le) ?_
    rw [Finset.card_product]; ring_nf; omega
  have hb : ((G ×ˢ G).image (fun a : F × F => (a, (a.2, a.1)))).card ≤ G.card ^ 2 := by
    refine le_trans (Finset.card_image_le) ?_
    rw [Finset.card_product]; ring_nf; omega
  omega

/-! ## The (c) arithmetic cores: which multiplicity patterns are ≡ 0 (mod d) -/

/-- Pair-match multiplicity core: a matched root carries multiplicity `1 + (d−1) = d`,
divisible by `d` for EVERY order — pair-match is degenerate at all orders. -/
theorem pairMatch_mult_divisible (d : ℕ) : d ∣ (1 + (d - 1)) ∨ d = 0 := by
  rcases Nat.eq_zero_or_pos d with h | h
  · exact Or.inr h
  · refine Or.inl ?_
    have h1 : 1 + (d - 1) = d := by omega
    rw [h1]

/-- Diagonal-clause multiplicity core: the diagonal tuple's roots carry multiplicities
`2` and `2(d−1)`; both are `≡ 0 (mod d)` iff `d ∣ 2` iff `d = 2` (for `d ≥ 2`) — the R18
third clause is d=2-SPECIFIC, and for `d ≥ 3` degeneracy is exactly `IsPairMatch`. -/
theorem diag_mult_divisible_iff_two (d : ℕ) (hd : 2 ≤ d) :
    (d ∣ 2 ∧ d ∣ 2 * (d - 1)) ↔ d = 2 := by
  constructor
  · rintro ⟨h2, _⟩
    have hle : d ≤ 2 := Nat.le_of_dvd (by norm_num) h2
    omega
  · rintro rfl
    exact ⟨dvd_refl 2, ⟨1, by omega⟩⟩

/-! ## The named order-uniform Hasse input and the reduction -/

/-- **THE NAMED OPEN INPUT (order-uniform)**: every R18-nondegenerate tuple has reduced
triple-linear sum `≤ 2√p`.  For `χ` of order `d` this is Weil for `∑_s χ(L₁L₂L₃^{d−1})`
(the superelliptic curve `y^d = L₁L₂L₃^{d−1}`, 3 distinct roots, bound `(3−1)√p` UNIFORM
in `d`).  Probe max observed (orders 2,4,8,16): `2.01√p` for `tripleSum − 1`, i.e. within
`2√p + 1`.  For the order-2 member this follows from `LegendreCubicHasse` via the R20
normal form. -/
def TripleLinearHasse (χ : MulChar F ℂ) (G : Finset F) : Prop :=
  ∀ z ∈ (G ×ˢ G) ×ˢ (G ×ˢ G), ¬ IsDegenerate z →
    ‖tripleSum χ (z.2.2 - z.1.1) (z.2.2 - z.1.2) (z.2.2 - z.2.1)‖
      ≤ 2 * Real.sqrt (Fintype.card F)

/-- **THE ROUND-21 REDUCTION (per character)**: the order-uniform triple-linear Hasse input
implies the R18 `QuarticWeilInput` (constant 3) whenever `p ≥ 4`:
`‖quadTerm‖ = ‖tripleSum − 1‖ ≤ 2√p + 1 ≤ 3√p`. -/
theorem quarticWeilInput_of_tripleLinearHasse (χ : MulChar F ℂ) (G : Finset F)
    (hp4 : (4 : ℝ) ≤ (Fintype.card F : ℝ)) (hH : TripleLinearHasse χ G) :
    QuarticWeilInput χ G := by
  intro z hz hnd
  obtain ⟨⟨a₁, a₂⟩, ⟨b₁, b₂⟩⟩ := z
  have hid := quadTerm_eq_tripleSum_sub_one χ a₁ a₂ b₁ b₂
  have hW := hH ((a₁, a₂), (b₁, b₂)) hz hnd
  have hsq2 : (2 : ℝ) ≤ Real.sqrt (Fintype.card F) := by
    have h4 : Real.sqrt 4 ≤ Real.sqrt (Fintype.card F) := Real.sqrt_le_sqrt hp4
    rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)] at h4
  calc ‖quadTerm χ ((a₁, a₂), (b₁, b₂))‖
      = ‖tripleSum χ (b₂ - a₁) (b₂ - a₂) (b₂ - b₁) - 1‖ := by rw [hid]
    _ ≤ ‖tripleSum χ (b₂ - a₁) (b₂ - a₂) (b₂ - b₁)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ ≤ 2 * Real.sqrt (Fintype.card F) + 1 := by
        have : ‖(1 : ℂ)‖ = 1 := by simp
        rw [this]
        linarith [hW]
    _ ≤ 3 * Real.sqrt (Fintype.card F) := by linarith [hsq2]

/-- **THE LANE RESULT**: the ENTIRE r=2 rung `FourthMomentTwistBound G X 6` — all orders
`d ∣ m` simultaneously — from the `TripleLinearHasse` family, with constants UNIFORM in
`d`.  No `Cw(d)` growth enters `K(m)`: its `(m−1)⁴` is untouched. -/
theorem fourthMomentTwistBound_of_tripleLinearHasse
    (G : Finset F) (X : Finset (MulChar F ℂ))
    (hH : ∀ χ ∈ X, TripleLinearHasse χ G)
    (hp4 : (4 : ℝ) ≤ (Fintype.card F : ℝ))
    (hp : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ)) :
    ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung.FourthMomentTwistBound G X 6 :=
  fourthMomentTwistBound_of_quarticWeilInput G X
    (fun χ hχ => quarticWeilInput_of_tripleLinearHasse χ G hp4 (hH χ hχ)) hp

end ArkLib.ProximityGap.Frontier.R21HigherDFaces

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.R21HigherDFaces.quadTerm_eq_tripleSum_sub_one
#print axioms ArkLib.ProximityGap.Frontier.R21HigherDFaces.isDegenerate_of_isPairMatch
#print axioms ArkLib.ProximityGap.Frontier.R21HigherDFaces.card_filter_pairMatch_le
#print axioms ArkLib.ProximityGap.Frontier.R21HigherDFaces.pairMatch_mult_divisible
#print axioms ArkLib.ProximityGap.Frontier.R21HigherDFaces.diag_mult_divisible_iff_two
#print axioms
  ArkLib.ProximityGap.Frontier.R21HigherDFaces.quarticWeilInput_of_tripleLinearHasse
#print axioms
  ArkLib.ProximityGap.Frontier.R21HigherDFaces.fourthMomentTwistBound_of_tripleLinearHasse
