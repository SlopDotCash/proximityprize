/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CaptureKernel

/-!
# K4 discharged on the unique-decoding window: the depth-0 case of the capture kernel

`Hab25CaptureKernel.lean` (O79) reduced the BCIKS20 Steps 5–7 capture kernel to two named
per-cell inputs, K1 (decode family) and **K4 (affine pinning)**:

> K4: `T < |Ecell| → ∃ v₀ v₁ (natDegree < k), ∀ γ ∈ Ecell, P γ = v₀ + C γ * v₁`.

The genuinely deep production of K4 is the Hensel-lift induction (BCIKS20 Claims 5.7–5.9 +
Appendix C, the #138/#139 stream). This file proves its **base case** — the depth-0 layer
where no lifting is needed: on the unique-decoding-flavoured window

> `2·n + k ≤ 3·t`,  `t = ⌈(1−δ)·n⌉₊`  (equivalently `3(n−t) ≤ d−1` for `d = n−k+1`),

K4 holds with **no threshold antecedent** and the pencil is *constructed*, not assumed:
any two cell members determine it, every further member is forced onto it by a
three-witness-set root count. This is the polynomial-side analogue, on the kernel's own
`McaDecode` surface, of the O84 codeword-side mechanism (`TheoremQUDExtraction`):

* `mcaDecode_P_eq_of_window` — **the uniqueness half**: on `n + k ≤ 2·t`, any two
  `McaDecode` witnesses of the same `(u, γ)` carry the *same* polynomial (two witness sets
  intersect in ≥ `2t − n ≥ k` points; the difference has degree `< k` and ≥ `k` roots).
* `exists_pencil_of_decode_family_window` — **K4 on the window, antecedent-free**: a decode
  family on any cell with ≥ 2 scalars is affinely pinned. The pencil through two members
  `v₁ = (γ₁−γ₂)⁻¹·(P γ₁ − P γ₂)`, `v₀ = P γ₁ − γ₁·v₁` interpolates the stack rows on
  `S₁ ∩ S₂` (`u 1` from the difference, `u 0` from back-substitution), and any third
  member's decode agrees with the specialization on `S₁ ∩ S₂ ∩ S₃` (≥ `3t − 2n ≥ k`
  points), forcing equality.
* `hsteps57_of_window` — the literal `hsteps57` hypothesis of `claim1_dichotomy` from K1
  alone on the window (K4's `∃` is produced, with the threshold antecedent absorbed).
* `cell_card_le_of_decode_family_window` — the composed cell bound: on the window, K1
  alone gives `|Ecell| ≤ T` for any `T ≥ n`.
* `window3_implies_window2` — the 3-intersection window implies the uniqueness window, so
  in the K4 regime of this file the decode family is *forced* (per-`γ` unique), matching
  the probe's `multi_decode = 0`.

What remains of K4 is exactly the regime past this window — `3(n−t) > d−1`, the
Johnson-range content where the probe's negative control breaks the constructed pencil
(59/600 planted stacks) and the genuine Hensel machinery (branch polynomials over
`F⟦X⟧`, Claim 5.8 degree bound, Claim 5.9 `Z`-linearity, Appendix C inseparable shell)
becomes load-bearing.

Falsify-first probe (`scripts/probes/probe_k4_ud_window.py`, exit 0): exhaustive GF(5),
`n=4, k=1, t=3` (all 390,625 stacks; 48,000 multi-scalar bad sets in-window) — 0 uniqueness
violations, 0 pencil failures, 0 pencil mismatches; planted+random GF(7), `n=6, k=2, t=5`
(400 multi-scalar cells) — 0 violations; negative control outside the window (`t=4`):
59/600 planted stacks break the constructed pencil — the window hypothesis is
load-bearing, not bookkeeping.

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedSectionVars false

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Finset
open CodingTheory.ProximityGap.Hab25Core
open _root_.ProximityGap Code
open CodingTheory.ProximityGap.Hab25Core.Hab25Johnson
open scoped NNReal ENNReal ProbabilityTheory Polynomial

variable {ι₀ : Type} [Fintype ι₀] [Nonempty ι₀] [DecidableEq ι₀]
variable {F₀ : Type} [Field F₀] [Fintype F₀] [DecidableEq F₀]

/-- The agreement floor of an `McaDecode` witness set, in ℕ. -/
theorem McaDecode.floor_le_card {domain : ι₀ ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) ι₀} {γ : F₀} (d : McaDecode domain k δ u γ) :
    ⌈(1 - δ) * (Fintype.card ι₀ : ℝ≥0)⌉₊ ≤ d.S.card :=
  Nat.ceil_le.mpr d.hcard

/-- `degree < k` and `0 < k` give `natDegree < k` (including the zero polynomial). -/
theorem natDegree_lt_of_degree_lt_of_pos {k : ℕ} (hk : 0 < k) {p : F₀[X]}
    (h : p.degree < k) : p.natDegree < k := by
  rcases eq_or_ne p 0 with rfl | hp
  · simpa using hk
  · exact (Polynomial.natDegree_lt_iff_degree_lt hp).mpr h

/-- A polynomial of degree `< k` vanishing on `≥ k` points of a witness-set image is zero.
The root-count workhorse shared by both halves below. -/
theorem eq_zero_of_degree_lt_of_vanishes_on {domain : ι₀ ↪ F₀} {k : ℕ}
    {g : F₀[X]} (hdeg : g.degree < k) (S : Finset ι₀) (hcard : k ≤ S.card)
    (hvan : ∀ i ∈ S, g.eval (domain i) = 0) : g = 0 := by
  classical
  rcases eq_or_ne g 0 with rfl | hg
  · rfl
  · refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' g (S.image domain)
      (fun x hx => ?_) ?_
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact hvan i hi
    · rw [Finset.card_image_of_injective _ domain.injective]
      exact lt_of_lt_of_le ((Polynomial.natDegree_lt_iff_degree_lt hg).mpr hdeg) hcard

/-- **The uniqueness half of K4 (depth-0).** On the window `n + k ≤ 2·t`
(`t = ⌈(1−δ)·n⌉₊`, i.e. two witness sets must share `≥ k` points), any two `McaDecode`
witnesses of the same `(u, γ)` decode to the *same* polynomial: the per-`γ` decode family
is forced, and any two affine pinnings of the same cell coincide. -/
theorem mcaDecode_P_eq_of_window {domain : ι₀ ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) ι₀} {γ : F₀}
    (hwin : Fintype.card ι₀ + k ≤ 2 * ⌈(1 - δ) * (Fintype.card ι₀ : ℝ≥0)⌉₊)
    (d d' : McaDecode domain k δ u γ) : d.P = d'.P := by
  classical
  have h1 := d.floor_le_card
  have h2 := d'.floor_le_card
  have hu : (d.S ∪ d'.S).card ≤ Fintype.card ι₀ := Finset.card_le_univ _
  have hi := Finset.card_union_add_card_inter d.S d'.S
  have hk_inter : k ≤ (d.S ∩ d'.S).card := by omega
  have hdeg : (d.P - d'.P).degree < k :=
    lt_of_le_of_lt (Polynomial.degree_sub_le _ _) (max_lt d.hdeg d'.hdeg)
  have hzero : d.P - d'.P = 0 := by
    refine eq_zero_of_degree_lt_of_vanishes_on (domain := domain) hdeg (d.S ∩ d'.S)
      hk_inter fun i hi => ?_
    have hia := d.hagree i (Finset.mem_inter.mp hi).1
    have hib := d'.hagree i (Finset.mem_inter.mp hi).2
    rw [Polynomial.eval_sub, hia, hib, sub_self]
  exact sub_eq_zero.mp hzero

/-- The 3-intersection window implies the uniqueness window: in the K4 regime of this
file, the per-`γ` decode polynomial is forced. -/
theorem window3_implies_window2 {k : ℕ} {δ : ℝ≥0}
    (hwin : 2 * Fintype.card ι₀ + k ≤ 3 * ⌈(1 - δ) * (Fintype.card ι₀ : ℝ≥0)⌉₊) :
    Fintype.card ι₀ + k ≤ 2 * ⌈(1 - δ) * (Fintype.card ι₀ : ℝ≥0)⌉₊ := by
  have ht : ⌈(1 - δ) * (Fintype.card ι₀ : ℝ≥0)⌉₊ ≤ Fintype.card ι₀ := by
    refine Nat.ceil_le.mpr ?_
    calc (1 - δ) * (Fintype.card ι₀ : ℝ≥0) ≤ 1 * (Fintype.card ι₀ : ℝ≥0) := by
          gcongr
          exact tsub_le_self
      _ = (Fintype.card ι₀ : ℝ≥0) := one_mul _
  omega

/-- **K4 on the unique-decoding window, antecedent-free (the kernel's depth-0 case).**
On `2·n + k ≤ 3·t`, any decode family on any cell with at least two scalars is affinely
pinned: the pencil through two members captures every member. The Hensel lift is not
needed at depth 0 — the pencil is constructed by field algebra and forced by root
counting on the triple witness intersection (`≥ 3t − 2n ≥ k` points). -/
theorem exists_pencil_of_decode_family_window {domain : ι₀ ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) ι₀} (hk : 0 < k) (Ecell : Finset F₀) (P : F₀ → F₀[X])
    (hdec : ∀ γ ∈ Ecell, ∃ d : McaDecode domain k δ u γ, d.P = P γ)
    (hwin : 2 * Fintype.card ι₀ + k ≤ 3 * ⌈(1 - δ) * (Fintype.card ι₀ : ℝ≥0)⌉₊)
    (h2 : 1 < Ecell.card) :
    ∃ v₀ v₁ : F₀[X], v₀.natDegree < k ∧ v₁.natDegree < k ∧
      ∀ γ ∈ Ecell, P γ = v₀ + Polynomial.C γ * v₁ := by
  classical
  obtain ⟨γ₁, hγ₁, γ₂, hγ₂, hne⟩ := Finset.one_lt_card.mp h2
  obtain ⟨d₁, hd₁⟩ := hdec γ₁ hγ₁
  obtain ⟨d₂, hd₂⟩ := hdec γ₂ hγ₂
  have hsub : γ₁ - γ₂ ≠ 0 := sub_ne_zero.mpr hne
  set v₁ : F₀[X] := Polynomial.C (γ₁ - γ₂)⁻¹ * (P γ₁ - P γ₂) with hv₁
  set v₀ : F₀[X] := P γ₁ - Polynomial.C γ₁ * v₁ with hv₀
  -- degree bounds
  have hP₁ : (P γ₁).natDegree < k :=
    natDegree_lt_of_degree_lt_of_pos hk (hd₁ ▸ d₁.hdeg)
  have hP₂ : (P γ₂).natDegree < k :=
    natDegree_lt_of_degree_lt_of_pos hk (hd₂ ▸ d₂.hdeg)
  have hv₁deg : v₁.natDegree < k := by
    refine lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _) ?_
    exact lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (max_lt hP₁ hP₂)
  have hv₀deg : v₀.natDegree < k := by
    refine lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) ?_
    exact max_lt hP₁ (lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _) hv₁deg)
  -- evaluation of the pencil rows on the double intersection
  have hrows : ∀ i ∈ d₁.S ∩ d₂.S,
      v₁.eval (domain i) = u 1 i ∧ v₀.eval (domain i) = u 0 i := by
    intro i hi
    have hia : (P γ₁).eval (domain i) = u 0 i + γ₁ * u 1 i := by
      have := d₁.hagree i (Finset.mem_inter.mp hi).1
      rw [hd₁] at this
      simpa [smul_eq_mul] using this
    have hib : (P γ₂).eval (domain i) = u 0 i + γ₂ * u 1 i := by
      have := d₂.hagree i (Finset.mem_inter.mp hi).2
      rw [hd₂] at this
      simpa [smul_eq_mul] using this
    have h1 : v₁.eval (domain i) = u 1 i := by
      rw [hv₁, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, hia, hib]
      field_simp
      ring
    refine ⟨h1, ?_⟩
    rw [hv₀, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, hia, h1]
    ring
  -- every cell member is forced onto the pencil
  refine ⟨v₀, v₁, hv₀deg, hv₁deg, fun γ hγ => ?_⟩
  obtain ⟨d, hd⟩ := hdec γ hγ
  -- triple-intersection cardinality
  have h1 := d₁.floor_le_card
  have h2c := d₂.floor_le_card
  have h3 := d.floor_le_card
  have hu₁ : (d₁.S ∪ d₂.S).card ≤ Fintype.card ι₀ := Finset.card_le_univ _
  have hi₁ := Finset.card_union_add_card_inter d₁.S d₂.S
  have hu₂ : ((d₁.S ∩ d₂.S) ∪ d.S).card ≤ Fintype.card ι₀ := Finset.card_le_univ _
  have hi₂ := Finset.card_union_add_card_inter (d₁.S ∩ d₂.S) d.S
  have hk_inter : k ≤ ((d₁.S ∩ d₂.S) ∩ d.S).card := by omega
  -- the discrepancy polynomial vanishes there
  have hdegg : (P γ - (v₀ + Polynomial.C γ * v₁)).degree < k := by
    rcases eq_or_ne (P γ - (v₀ + Polynomial.C γ * v₁)) 0 with hz | hz
    · rw [hz, Polynomial.degree_zero]
      exact WithBot.bot_lt_coe k
    · rw [← Polynomial.natDegree_lt_iff_degree_lt hz]
      refine lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (max_lt ?_ ?_)
      · exact natDegree_lt_of_degree_lt_of_pos hk (hd ▸ d.hdeg)
      · exact lt_of_le_of_lt (Polynomial.natDegree_add_le _ _)
          (max_lt hv₀deg (lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _) hv₁deg))
  have hzero : P γ - (v₀ + Polynomial.C γ * v₁) = 0 := by
    refine eq_zero_of_degree_lt_of_vanishes_on (domain := domain) hdegg
      ((d₁.S ∩ d₂.S) ∩ d.S) hk_inter fun i hi => ?_
    have hi12 := (Finset.mem_inter.mp hi).1
    have hiS := (Finset.mem_inter.mp hi).2
    obtain ⟨hr₁, hr₀⟩ := hrows i hi12
    have hia : (P γ).eval (domain i) = u 0 i + γ * u 1 i := by
      have := d.hagree i hiS
      rw [hd] at this
      simpa [smul_eq_mul] using this
    rw [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, hia, hr₀, hr₁, sub_self]
  exact sub_eq_zero.mp hzero

/-- **The literal `hsteps57` from K1 alone, on the window.** K4's threshold antecedent is
absorbed: a positive threshold below the cell size yields ≥ 2 members, and the pencil
exists unconditionally there. This is the exact hypothesis shape of `claim1_dichotomy`,
produced rather than assumed. -/
theorem hsteps57_of_window {domain : ι₀ ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) ι₀} (hk : 0 < k) (Ecell : Finset F₀) {T : ℕ} (hT : 1 ≤ T)
    (P : F₀ → F₀[X])
    (hdec : ∀ γ ∈ Ecell, ∃ d : McaDecode domain k δ u γ, d.P = P γ)
    (hwin : 2 * Fintype.card ι₀ + k ≤ 3 * ⌈(1 - δ) * (Fintype.card ι₀ : ℝ≥0)⌉₊) :
    T < Ecell.card →
      ∃ a b : F₀[X], a.natDegree < k ∧ b.natDegree < k ∧
        ∀ γ ∈ Ecell, AffineCaptured domain k δ u γ (a, b) := by
  intro hTcard
  obtain ⟨v₀, v₁, h₀, h₁, hp⟩ :=
    exists_pencil_of_decode_family_window hk Ecell P hdec hwin (by omega)
  refine ⟨v₀, v₁, h₀, h₁, fun γ hγ => ?_⟩
  obtain ⟨d, hd⟩ := hdec γ hγ
  exact d.affineCaptured (hd.trans (hp γ hγ))

/-- **The cell bound from K1 alone, on the window.** Composing the depth-0 K4 with the
proven `claim1_dichotomy` through the O79 seam: any decoded cell obeys `|Ecell| ≤ T` for
any threshold `T ≥ n`, with no pinning hypothesis left. -/
theorem cell_card_le_of_decode_family_window {domain : ι₀ ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) ι₀} (hk : 0 < k) (Ecell : Finset F₀) (T : ℕ)
    (P : F₀ → F₀[X])
    (hn : Fintype.card ι₀ ≤ T)
    (hdec : ∀ γ ∈ Ecell, ∃ d : McaDecode domain k δ u γ, d.P = P γ)
    (hwin : 2 * Fintype.card ι₀ + k ≤ 3 * ⌈(1 - δ) * (Fintype.card ι₀ : ℝ≥0)⌉₊) :
    Ecell.card ≤ T := by
  have hT : 1 ≤ T := le_trans Fintype.card_pos hn
  exact claim1_dichotomy domain k δ u Ecell T hn (hsteps57_of_window hk Ecell hT P hdec hwin)

/-- **The family-level uniqueness consequence.** On the (weaker) 2-intersection window,
two decode families of the same stack on the same cell coincide pointwise — the K4 pencil,
when it exists, is unique and independent of decode choices. -/
theorem decode_family_eq_on_of_window {domain : ι₀ ↪ F₀} {k : ℕ} {δ : ℝ≥0}
    {u : WordStack F₀ (Fin 2) ι₀} (Ecell : Finset F₀) (P P' : F₀ → F₀[X])
    (hdec : ∀ γ ∈ Ecell, ∃ d : McaDecode domain k δ u γ, d.P = P γ)
    (hdec' : ∀ γ ∈ Ecell, ∃ d : McaDecode domain k δ u γ, d.P = P' γ)
    (hwin : Fintype.card ι₀ + k ≤ 2 * ⌈(1 - δ) * (Fintype.card ι₀ : ℝ≥0)⌉₊) :
    ∀ γ ∈ Ecell, P γ = P' γ := by
  intro γ hγ
  obtain ⟨d, hd⟩ := hdec γ hγ
  obtain ⟨d', hd'⟩ := hdec' γ hγ
  rw [← hd, ← hd']
  exact mcaDecode_P_eq_of_window hwin d d'

/-- The window is satisfiable in shape (no unsatisfiable-hypothesis leaf): at
`ι₀ = Fin 4`, `δ = 0`, `k = 1` the 3-intersection window reads `9 ≤ 12`. -/
theorem k4_ud_window_satisfiable :
    2 * Fintype.card (Fin 4) + 1 ≤
      3 * ⌈((1 : ℝ≥0) - 0) * (Fintype.card (Fin 4) : ℝ≥0)⌉₊ := by
  norm_num

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

/-! ## Axiom audit — all kernel-clean. -/
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.mcaDecode_P_eq_of_window
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.window3_implies_window2
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.exists_pencil_of_decode_family_window
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.hsteps57_of_window
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.cell_card_le_of_decode_family_window
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.decode_family_eq_on_of_window
#print axioms CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.k4_ud_window_satisfiable
