/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26DimOnePin

/-!
# The dimension ladder, rung two: the unconditional `δ*` pin at the `r = 3` KKH26 slice (#371)

`KKH26DimOnePin.lean` discharged the `InteriorCeiling` obligation at the slice
`(r, m) = (2, 1)` (the dimension-one code) by the *pair-ownership* incidence count, producing
the first unconditional `δ*` pin at the KKH26 ceiling.  **This file climbs the ladder one
rung**: at the slice `(r, m) = (3, 1)` the code `evalCode g (2^μ) 1` has dimension two
(affine words `c₀ + c₁·x` on the smooth domain `x_i = g^i`), and the ownership argument
generalizes from *pairs* to *triples*: for every `μ ≥ 3` and every `ε*` in the (nonempty)
band

  `[(n(n−1)(n−2)/12)/p , (2³·C(2^{μ−1},3))/p)`,   `n = 2^μ`,

we get `mcaDeltaStar(evalCode g (2^μ) 1, ε*) = 1 − 3/2^μ` — **exactly**, axiom-clean, and
strictly *beyond the Johnson radius* `1 − √ρ` at *every* valid `μ` (`ρ = 2/2^μ` the rate;
`(3/2^μ)² < ρ ⟺ 9 < 2^{μ+1}`, automatic for `μ ≥ 3`).

**The mechanism (the triple-ownership count).**  For the dimension-two code, a bad scalar's
witness set `S` (`|S| ≥ 4` strictly below the ceiling) carries `u₀ + γ·u₁` affine in `x` on
`S`, while `u₁` itself cannot be affine on `S` (affinity of `u₁` plus affinity of the line
point forces a joint pair).  The determining object is the collinearity determinant

  `colDet y (i,j,k) = (x_j − x_i)(y_k − y_i) − (x_k − x_i)(y_j − y_i)`:

on every triple of `S` the line constraint reads `colDet u₀ + γ·colDet u₁ = 0`, so **any
triple with `colDet u₁ ≠ 0` determines `γ`** — the pair sets of the `r = 2` proof become
triple sets, disjoint across distinct bad scalars.  Splitting `S` along the `u₁`-line through
two of its points (`Af` on the line, `Cf` off it; `Cf ≠ ∅` by non-affinity) shows each bad
scalar owns all `3·|Af|(|Af|−1)·|Cf| ≥ 12` arrangements of (two distinct on-line points, one
off-line point), each non-collinear.  Only `n(n−1)(n−2)` ordered distinct triples exist, so

  `#bad · 12 ≤ n(n−1)(n−2)`,  i.e.  `#bad ≤ n(n−1)(n−2)/12`,

strictly below the in-tree KKH26 ceiling count `2³·C(2^{μ−1},3)` for every `μ ≥ 3`
(`dimTwo_band_nonempty`; at `n = 8`: `28 < 32`).  Probe:
`scripts/probes/probe_dim2_interior_ceiling.py` (three independent badness checkers agree
byte-exactly; max hill-climbed bad count `8 ≤ 28` at `n = 8`; ceiling bad count `40` =
exactly the `TwoPowerSubsetSumSpectrum` law `N(μ,3) = 2³C(4,3) + 2C(4,1) = 32 + 8`).

**Honest scope.**  This pins `δ*` for the dimension-two member of the family only; the
production-dimension conjecture remains open.  What is new beyond the `r = 2` rung: the
ownership device survives the dimension climb — the witness geometry (level sets → affine
graphs) richens, the determining tuple grows (pairs → triples), and the counting still
separates from the spectrum.  The visible ladder pattern (recorded, not proven): at slice
`r`, bad witnesses are degree-`(r−2)` graphs, the determining tuple is an `r`-point
non-degeneracy minor, ownership `≥ K(r) = r·(r−1)!·(s−r+1)`-ish arrangements against a tuple
space `n^{(r)}`, against a ceiling `2^r·C(2^{μ−1},r)` — the two sides separate at every fixed
`r` for large `μ`, but the per-`r` constant degrades; the full-window sweep is *not* a
corollary.

The concrete instantiation `deltaStar_dimTwo_pin_F12289` pins `δ* = 5/8` for the
dimension-two (rate `1/4`) code on the 8-point smooth domain `⟨4043⟩ ⊆ F₁₂₂₈₉ˣ` (the NTT
prime), `ε* = 28/12289` — with Johnson radius `1 − 1/2 = 0.5 < 5/8 < 3/4` = capacity:
a second exact `δ*` value strictly inside the open window, at a *different rate* than the
`r = 2` instance.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26
open ProximityGap.KKH26DeltaStarReduction

namespace ArkLib.ProximityGap.KKH26DimTwo

/-! ## The dimension-two code: membership characterization -/

/-- Membership in the degree-`1` evaluation code is exactly affinity in `x_i = g^i`. -/
theorem mem_evalCode_one_iff {p : ℕ} {g : ZMod p} {n : ℕ} {w : Fin n → ZMod p} :
    w ∈ evalCode g n 1 ↔ ∃ c₀ c₁ : ZMod p, ∀ i, w i = c₀ + c₁ * g ^ (i : ℕ) := by
  constructor
  · rintro ⟨q, hq, hw⟩
    refine ⟨q.coeff 0, q.coeff 1, fun i => ?_⟩
    rw [hw i]
    conv_lhs => rw [Polynomial.eq_X_add_C_of_natDegree_le_one hq]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    ring
  · rintro ⟨c₀, c₁, hw⟩
    refine ⟨Polynomial.C c₁ * Polynomial.X + Polynomial.C c₀,
      Polynomial.natDegree_linear_le, fun i => ?_⟩
    rw [hw i]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    ring

/-- Affine words belong to the dimension-two code. -/
theorem affine_mem_evalCode_one {p : ℕ} {g : ZMod p} {n : ℕ} (c₀ c₁ : ZMod p) :
    (fun i : Fin n => c₀ + c₁ * g ^ (i : ℕ)) ∈ evalCode g n 1 :=
  mem_evalCode_one_iff.mpr ⟨c₀, c₁, fun _ => rfl⟩

/-! ## The collinearity determinant -/

/-- **The collinearity determinant** of the word `y` on the index triple `(i, j, k)` over the
smooth domain `x_i = g^i`: the `3×3` determinant of the rows `(x_t, y_t, 1)`, expanded.  It
vanishes iff the three graph points are collinear (for distinct `x`'s), it is linear in `y`,
and it is alternating in the indices. -/
def colDet {p : ℕ} (g : ZMod p) {n : ℕ} (y : Fin n → ZMod p) (i j k : Fin n) : ZMod p :=
  (g ^ (j : ℕ) - g ^ (i : ℕ)) * (y k - y i) - (g ^ (k : ℕ) - g ^ (i : ℕ)) * (y j - y i)

private lemma colDet_swap₁₂ {p : ℕ} (g : ZMod p) {n : ℕ} (y : Fin n → ZMod p) (i j k : Fin n) :
    colDet g y j i k = -(colDet g y i j k) := by
  unfold colDet; ring

private lemma colDet_swap₂₃ {p : ℕ} (g : ZMod p) {n : ℕ} (y : Fin n → ZMod p) (i j k : Fin n) :
    colDet g y i k j = -(colDet g y i j k) := by
  unfold colDet; ring

/-- A non-vanishing collinearity determinant forces pairwise-distinct indices. -/
private lemma colDet_distinct {p : ℕ} {g : ZMod p} {n : ℕ} {y : Fin n → ZMod p}
    {i j k : Fin n} (h : colDet g y i j k ≠ 0) : i ≠ j ∧ i ≠ k ∧ j ≠ k := by
  refine ⟨?_, ?_, ?_⟩
  · intro he; apply h; subst he; unfold colDet; ring
  · intro he; apply h; subst he; unfold colDet; ring
  · intro he; apply h; subst he; unfold colDet; ring

/-- Affine words have vanishing collinearity determinants (given affinity at the three
indices). -/
private lemma colDet_eq_zero_of_affine {p : ℕ} {g : ZMod p} {n : ℕ} {y : Fin n → ZMod p}
    {c₀ c₁ : ZMod p} {i j k : Fin n}
    (hi : y i = c₀ + c₁ * g ^ (i : ℕ)) (hj : y j = c₀ + c₁ * g ^ (j : ℕ))
    (hk : y k = c₀ + c₁ * g ^ (k : ℕ)) :
    colDet g y i j k = 0 := by
  unfold colDet
  rw [hi, hj, hk]
  ring

/-- **The line constraint, determinant form.**  If the line point `u₀ + γ·u₁` is affine at
the three indices, then `colDet u₀ + γ·colDet u₁ = 0` on the triple — any non-degenerate
triple (`colDet u₁ ≠ 0`) therefore *determines* the scalar `γ`. -/
private lemma colDet_line_eq_zero {p : ℕ} {g : ZMod p} {n : ℕ}
    {u₀ u₁ : Fin n → ZMod p} {γ c₀ c₁ : ZMod p} {i j k : Fin n}
    (hi : u₀ i + γ * u₁ i = c₀ + c₁ * g ^ (i : ℕ))
    (hj : u₀ j + γ * u₁ j = c₀ + c₁ * g ^ (j : ℕ))
    (hk : u₀ k + γ * u₁ k = c₀ + c₁ * g ^ (k : ℕ)) :
    colDet g u₀ i j k + γ * colDet g u₁ i j k = 0 := by
  unfold colDet
  linear_combination (g ^ (j : ℕ) - g ^ (i : ℕ)) * hk - (g ^ (j : ℕ) - g ^ (i : ℕ)) * hi
    - (g ^ (k : ℕ) - g ^ (i : ℕ)) * hj + (g ^ (k : ℕ) - g ^ (i : ℕ)) * hi

/-- **Two-point interpolation.**  A vanishing collinearity determinant against a base pair
`(a, b)` with `x_a ≠ x_b` places `y i` on the affine line through the two base graph
points. -/
private lemma interp_of_colDet_eq_zero {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ}
    {y : Fin n → ZMod p} {a b i : Fin n}
    (hd : g ^ (b : ℕ) - g ^ (a : ℕ) ≠ 0)
    (h0 : colDet g y a b i = 0) :
    y i = (y a - (y b - y a) * (g ^ (b : ℕ) - g ^ (a : ℕ))⁻¹ * g ^ (a : ℕ))
        + (y b - y a) * (g ^ (b : ℕ) - g ^ (a : ℕ))⁻¹ * g ^ (i : ℕ) := by
  have hc : (y b - y a) * (g ^ (b : ℕ) - g ^ (a : ℕ))⁻¹ * (g ^ (b : ℕ) - g ^ (a : ℕ))
      = y b - y a := by
    rw [mul_assoc, inv_mul_cancel₀ hd, mul_one]
  have key : (g ^ (b : ℕ) - g ^ (a : ℕ))
      * (((y a - (y b - y a) * (g ^ (b : ℕ) - g ^ (a : ℕ))⁻¹ * g ^ (a : ℕ))
          + (y b - y a) * (g ^ (b : ℕ) - g ^ (a : ℕ))⁻¹ * g ^ (i : ℕ)) - y i) = 0 := by
    unfold colDet at h0
    linear_combination (g ^ (i : ℕ) - g ^ (a : ℕ)) * hc - h0
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h hd
  · exact (sub_eq_zero.mp h).symm

/-! ## The triple-ownership count -/

/-- `4 ≤ (α² − α)·ξ` whenever `α ≥ 2`, `ξ ≥ 1`, `α + ξ ≥ 4` (the worst split of a 4-point
witness set into on-line and off-line parts). -/
private lemma four_le_offDiag_mul {α ξ : ℕ} (hα : 2 ≤ α) (hξ : 1 ≤ ξ) (hsum : 4 ≤ α + ξ) :
    4 ≤ (α * α - α) * ξ := by
  rcases Nat.lt_or_ge ξ 2 with h | h
  · -- `ξ = 1`, hence `α ≥ 3`
    have hξ1 : ξ = 1 := by omega
    subst hξ1
    obtain ⟨k, rfl⟩ : ∃ k, α = k + 3 := ⟨α - 3, by omega⟩
    have hexp : (k + 3) * (k + 3) = k * k + 6 * k + 9 := by ring
    rw [Nat.mul_one]
    omega
  · -- `ξ ≥ 2`, `α ≥ 2`
    obtain ⟨k, rfl⟩ : ∃ k, α = k + 2 := ⟨α - 2, by omega⟩
    have hexp : (k + 2) * (k + 2) = k * k + 4 * k + 4 := by ring
    have h2 : 2 ≤ (k + 2) * (k + 2) - (k + 2) := by omega
    calc (4 : ℕ) = 2 * 2 := by norm_num
    _ ≤ ((k + 2) * (k + 2) - (k + 2)) * ξ := Nat.mul_le_mul h2 h

private lemma sq_sub_self (m : ℕ) : m * m - m = m * (m - 1) := by
  rcases m with _ | k
  · simp
  · have h : (k + 1) * (k + 1) = (k + 1) * k + (k + 1) := by ring
    simp only [Nat.add_sub_cancel]
    omega

open Classical in
/-- **The triple-ownership count.**  For the dimension-two code at agreement threshold `> 3`
(i.e. `(1−δ)·n > 3`), every stack `(u₀, u₁)` has at most `n(n−1)(n−2)/12` bad scalars: each
bad scalar owns at least twelve ordered non-collinear triples (for `u₁`) inside its witness
set, any such triple determines the scalar through the line constraint
`colDet u₀ + γ·colDet u₁ = 0`, distinct bad scalars own disjoint triple sets, and only
`n(n−1)(n−2)` ordered distinct triples exist.  Stated multiplicatively to avoid
`ℕ`-division. -/
theorem dimTwo_badScalars_card_mul_twelve_le
    {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ} [NeZero n]
    (hginj : ∀ i j : Fin n, g ^ (i : ℕ) = g ^ (j : ℕ) → i = j)
    {δ : ℝ≥0} (hδ : (3 : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (u₀ u₁ : Fin n → ZMod p) :
    (Finset.filter (fun γ : ZMod p =>
        mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n 1) δ u₀ u₁ γ)
        Finset.univ).card * 12 ≤ n * (n - 1) * (n - 2) := by
  classical
  set B := Finset.filter (fun γ : ZMod p =>
      mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n 1) δ u₀ u₁ γ)
      Finset.univ with hBdef
  -- Step 1: for every bad scalar, a witness set with the three working properties:
  -- size ≥ 4, the line point affine on it, and a non-collinear `u₁`-triple inside it.
  have hwit : ∀ γ ∈ B, ∃ S : Finset (Fin n), 4 ≤ S.card ∧
      (∃ c₀ c₁ : ZMod p, ∀ i ∈ S, u₀ i + γ * u₁ i = c₀ + c₁ * g ^ (i : ℕ)) ∧
      ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, colDet g u₁ a b c ≠ 0 := by
    intro γ hγ
    obtain ⟨S, hScard, ⟨w, hwC, hagree⟩, hnojoint⟩ := (Finset.mem_filter.mp hγ).2
    obtain ⟨d₀, d₁, hw⟩ := mem_evalCode_one_iff.mp hwC
    have hlin : ∀ i ∈ S, u₀ i + γ * u₁ i = d₀ + d₁ * g ^ (i : ℕ) := by
      intro i hi
      have h := hagree i hi
      rw [hw i, smul_eq_mul] at h
      exact h.symm
    have h4 : 4 ≤ S.card := by
      have h3 : (3 : ℝ≥0) < (S.card : ℝ≥0) := lt_of_lt_of_le hδ hScard
      have h3' : (3 : ℕ) < S.card := by exact_mod_cast h3
      omega
    refine ⟨S, h4, ⟨d₀, d₁, hlin⟩, ?_⟩
    by_contra hcon
    push Not at hcon
    -- `u₁` is affine on `S`: interpolate it, and build the joint pair.
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
    have hd : g ^ (b : ℕ) - g ^ (a : ℕ) ≠ 0 :=
      sub_ne_zero.mpr (fun h => hab (hginj b a h).symm)
    set c₁ : ZMod p := (u₁ b - u₁ a) * (g ^ (b : ℕ) - g ^ (a : ℕ))⁻¹ with hc₁def
    set c₀ : ZMod p := u₁ a - c₁ * g ^ (a : ℕ) with hc₀def
    have haff : ∀ i ∈ S, u₁ i = c₀ + c₁ * g ^ (i : ℕ) := fun i hi =>
      interp_of_colDet_eq_zero hd (hcon a ha b hb i hi)
    refine hnojoint ⟨fun i => (d₀ - γ * c₀) + (d₁ - γ * c₁) * g ^ (i : ℕ),
      affine_mem_evalCode_one _ _,
      fun i => c₀ + c₁ * g ^ (i : ℕ), affine_mem_evalCode_one _ _,
      fun i hi => ⟨?_, ?_⟩⟩
    · show (d₀ - γ * c₀) + (d₁ - γ * c₁) * g ^ (i : ℕ) = u₀ i
      linear_combination γ * (haff i hi) - hlin i hi
    · show c₀ + c₁ * g ^ (i : ℕ) = u₁ i
      exact (haff i hi).symm
  choose Sf hSf using hwit
  -- the per-scalar owned triple set: all non-collinear `u₁`-triples inside the witness set
  set Pt : {x // x ∈ B} → Finset (Fin n × Fin n × Fin n) := fun γ =>
    ((Sf γ.1 γ.2) ×ˢ (Sf γ.1 γ.2) ×ˢ (Sf γ.1 γ.2)).filter
      (fun t => ¬ colDet g u₁ t.1 t.2.1 t.2.2 = 0) with hPt
  -- Step 2: each bad scalar owns at least 12 such triples.
  have hP12 : ∀ γ : {x // x ∈ B}, 12 ≤ (Pt γ).card := by
    intro γ
    obtain ⟨h4S, _, a, ha, b, hb, c, hc, hnc⟩ := hSf γ.1 γ.2
    obtain ⟨hab, _, _⟩ := colDet_distinct hnc
    have hd : g ^ (b : ℕ) - g ^ (a : ℕ) ≠ 0 :=
      sub_ne_zero.mpr (fun h => hab (hginj b a h).symm)
    set Af := (Sf γ.1 γ.2).filter (fun i => colDet g u₁ a b i = 0) with hAdef
    set Cf := (Sf γ.1 γ.2).filter (fun i => ¬ colDet g u₁ a b i = 0) with hCdef
    have haA : a ∈ Af := Finset.mem_filter.mpr ⟨ha, by unfold colDet; ring⟩
    have hbA : b ∈ Af := Finset.mem_filter.mpr ⟨hb, by unfold colDet; ring⟩
    have hcC : c ∈ Cf := Finset.mem_filter.mpr ⟨hc, hnc⟩
    have hA2 : 2 ≤ Af.card := by
      have hsub : ({a, b} : Finset (Fin n)) ⊆ Af := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact haA
        · rw [Finset.mem_singleton.mp hx]; exact hbA
      calc (2 : ℕ) = ({a, b} : Finset (Fin n)).card := (Finset.card_pair hab).symm
      _ ≤ Af.card := Finset.card_le_card hsub
    have hC1 : 1 ≤ Cf.card := Finset.card_pos.mpr ⟨c, hcC⟩
    have hsum : Af.card + Cf.card = (Sf γ.1 γ.2).card := by
      rw [hAdef, hCdef]
      exact Finset.card_filter_add_card_filter_not _
    -- the on-line part is an affine graph; the off-line part avoids that line
    set c₁ : ZMod p := (u₁ b - u₁ a) * (g ^ (b : ℕ) - g ^ (a : ℕ))⁻¹ with hc₁def
    set c₀ : ZMod p := u₁ a - c₁ * g ^ (a : ℕ) with hc₀def
    have haff : ∀ i ∈ Af, u₁ i = c₀ + c₁ * g ^ (i : ℕ) := fun i hi =>
      interp_of_colDet_eq_zero hd (Finset.mem_filter.mp hi).2
    have hCne : ∀ j ∈ Cf, u₁ j ≠ c₀ + c₁ * g ^ (j : ℕ) := by
      intro j hj heq
      exact (Finset.mem_filter.mp hj).2
        (colDet_eq_zero_of_affine (haff a haA) (haff b hbA) heq)
    -- the key non-collinearity: two distinct on-line points and one off-line point
    have hkey : ∀ i ∈ Af, ∀ i' ∈ Af, i ≠ i' → ∀ j ∈ Cf,
        colDet g u₁ i i' j ≠ 0 := by
      intro i hi i' hi' hii' j hj
      have e : colDet g u₁ i i' j
          = (g ^ ((i' : Fin n) : ℕ) - g ^ ((i : Fin n) : ℕ))
            * (u₁ j - (c₀ + c₁ * g ^ ((j : Fin n) : ℕ))) := by
        unfold colDet
        rw [haff i hi, haff i' hi']
        ring
      rw [e]
      exact mul_ne_zero (sub_ne_zero.mpr (fun h => hii' (hginj i' i h).symm))
        (sub_ne_zero.mpr (hCne j hj))
    -- the three arrangement families, disjoint, each of size `(α²−α)·ξ`
    set D := Af.offDiag ×ˢ Cf with hDdef
    set m₁ : (Fin n × Fin n) × Fin n → Fin n × Fin n × Fin n :=
      fun q => (q.1.1, q.1.2, q.2) with hm₁def
    set m₂ : (Fin n × Fin n) × Fin n → Fin n × Fin n × Fin n :=
      fun q => (q.1.1, q.2, q.1.2) with hm₂def
    set m₃ : (Fin n × Fin n) × Fin n → Fin n × Fin n × Fin n :=
      fun q => (q.2, q.1.1, q.1.2) with hm₃def
    have hm₁ : Function.Injective m₁ := by
      intro q r h
      obtain ⟨⟨q1, q2⟩, q3⟩ := q
      obtain ⟨⟨r1, r2⟩, r3⟩ := r
      simp only [hm₁def, Prod.mk.injEq] at h
      simp [h.1, h.2.1, h.2.2]
    have hm₂ : Function.Injective m₂ := by
      intro q r h
      obtain ⟨⟨q1, q2⟩, q3⟩ := q
      obtain ⟨⟨r1, r2⟩, r3⟩ := r
      simp only [hm₂def, Prod.mk.injEq] at h
      simp [h.1, h.2.1, h.2.2]
    have hm₃ : Function.Injective m₃ := by
      intro q r h
      obtain ⟨⟨q1, q2⟩, q3⟩ := q
      obtain ⟨⟨r1, r2⟩, r3⟩ := r
      simp only [hm₃def, Prod.mk.injEq] at h
      simp [h.1, h.2.1, h.2.2]
    have hmemD : ∀ q ∈ D, q.1.1 ∈ Af ∧ q.1.2 ∈ Af ∧ q.1.1 ≠ q.1.2 ∧ q.2 ∈ Cf := by
      intro q hq
      obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hq
      obtain ⟨ha1, ha2, hne⟩ := Finset.mem_offDiag.mp hq1
      exact ⟨ha1, ha2, hne, hq2⟩
    have hAC : ∀ i : Fin n, i ∈ Af → i ∈ Cf → False := fun i h1 h2 =>
      (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2
    have hSfA : Af ⊆ Sf γ.1 γ.2 := Finset.filter_subset _ _
    have hSfC : Cf ⊆ Sf γ.1 γ.2 := Finset.filter_subset _ _
    -- the three families land inside the owned set
    have hsub₁ : D.image m₁ ⊆ Pt γ := by
      intro t ht
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨ha1, ha2, hne, hqC⟩ := hmemD q hq
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨hSfA ha1, Finset.mem_product.mpr ⟨hSfA ha2, hSfC hqC⟩⟩, ?_⟩
      exact hkey _ ha1 _ ha2 hne _ hqC
    have hsub₂ : D.image m₂ ⊆ Pt γ := by
      intro t ht
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨ha1, ha2, hne, hqC⟩ := hmemD q hq
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨hSfA ha1, Finset.mem_product.mpr ⟨hSfC hqC, hSfA ha2⟩⟩, ?_⟩
      show ¬ colDet g u₁ q.1.1 q.2 q.1.2 = 0
      rw [colDet_swap₂₃]
      exact fun hzero => hkey _ ha1 _ ha2 hne _ hqC (neg_eq_zero.mp hzero)
    have hsub₃ : D.image m₃ ⊆ Pt γ := by
      intro t ht
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨ha1, ha2, hne, hqC⟩ := hmemD q hq
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨hSfC hqC, Finset.mem_product.mpr ⟨hSfA ha1, hSfA ha2⟩⟩, ?_⟩
      show ¬ colDet g u₁ q.2 q.1.1 q.1.2 = 0
      rw [colDet_swap₁₂, colDet_swap₂₃, neg_neg]
      exact hkey _ ha1 _ ha2 hne _ hqC
    -- the three families are pairwise disjoint (position of the off-line entry)
    have hclass₁ : ∀ t ∈ D.image m₁, t.2.1 ∈ Af ∧ t.1 ∈ Af := by
      intro t ht
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨ha1, ha2, _, _⟩ := hmemD q hq
      exact ⟨ha2, ha1⟩
    have hclass₂ : ∀ t ∈ D.image m₂, t.2.1 ∈ Cf ∧ t.1 ∈ Af := by
      intro t ht
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨_, _, _, hqC⟩ := hmemD q hq
      exact ⟨hqC, (hmemD q hq).1⟩
    have hclass₃ : ∀ t ∈ D.image m₃, t.1 ∈ Cf := by
      intro t ht
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ht
      exact (hmemD q hq).2.2.2
    have hd12 : Disjoint (D.image m₁) (D.image m₂) := by
      rw [Finset.disjoint_left]
      intro t h1 h2
      exact hAC _ (hclass₁ t h1).1 (hclass₂ t h2).1
    have hd13 : Disjoint (D.image m₁) (D.image m₃) := by
      rw [Finset.disjoint_left]
      intro t h1 h2
      exact hAC _ (hclass₁ t h1).2 (hclass₃ t h2)
    have hd23 : Disjoint (D.image m₂) (D.image m₃) := by
      rw [Finset.disjoint_left]
      intro t h1 h2
      exact hAC _ (hclass₂ t h1).2 (hclass₃ t h2)
    -- count
    have hDcard : D.card = (Af.card * Af.card - Af.card) * Cf.card := by
      rw [hDdef, Finset.card_product, Finset.offDiag_card]
    have h4D : 4 ≤ D.card := by
      rw [hDcard]
      exact four_le_offDiag_mul hA2 hC1 (by omega)
    have hUcard : (D.image m₁ ∪ D.image m₂ ∪ D.image m₃).card
        = D.card + D.card + D.card := by
      rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hd13, hd23⟩),
        Finset.card_union_of_disjoint hd12,
        Finset.card_image_of_injective _ hm₁, Finset.card_image_of_injective _ hm₂,
        Finset.card_image_of_injective _ hm₃]
    calc (12 : ℕ) ≤ D.card + D.card + D.card := by omega
    _ = (D.image m₁ ∪ D.image m₂ ∪ D.image m₃).card := hUcard.symm
    _ ≤ (Pt γ).card := Finset.card_le_card
        (Finset.union_subset (Finset.union_subset hsub₁ hsub₂) hsub₃)
  -- Step 3: the owned triple sets of distinct bad scalars are disjoint (any non-degenerate
  -- triple inside a common witness determines the scalar).
  have hPdisj : ∀ γ₁ ∈ B.attach, ∀ γ₂ ∈ B.attach, γ₁ ≠ γ₂ →
      Disjoint (Pt γ₁) (Pt γ₂) := by
    intro γ₁ _ γ₂ _ hne
    rw [Finset.disjoint_left]
    intro t hq1 hq2
    obtain ⟨hmem1, hu1⟩ := Finset.mem_filter.mp hq1
    obtain ⟨hmem2, _⟩ := Finset.mem_filter.mp hq2
    obtain ⟨h11, h1r⟩ := Finset.mem_product.mp hmem1
    obtain ⟨h12, h13⟩ := Finset.mem_product.mp h1r
    obtain ⟨h21, h2r⟩ := Finset.mem_product.mp hmem2
    obtain ⟨h22, h23⟩ := Finset.mem_product.mp h2r
    obtain ⟨c₀, c₁, hlin1⟩ := (hSf γ₁.1 γ₁.2).2.1
    obtain ⟨d₀, d₁, hlin2⟩ := (hSf γ₂.1 γ₂.2).2.1
    have e1 := colDet_line_eq_zero (hlin1 _ h11) (hlin1 _ h12) (hlin1 _ h13)
    have e2 := colDet_line_eq_zero (hlin2 _ h21) (hlin2 _ h22) (hlin2 _ h23)
    have key : (γ₁.1 - γ₂.1) * colDet g u₁ t.1 t.2.1 t.2.2 = 0 := by
      linear_combination e1 - e2
    rcases mul_eq_zero.mp key with h | h
    · exact hne (Subtype.ext (sub_eq_zero.mp h))
    · exact hu1 h
  -- Step 4: assemble through the distinct-triple space.
  have hbig : B.attach.card * 12 ≤ (B.attach.biUnion Pt).card := by
    rw [Finset.card_biUnion hPdisj]
    calc B.attach.card * 12 = ∑ _γ ∈ B.attach, 12 := by
          rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun γ _ => hP12 γ)
  have hsubE : (B.attach.biUnion Pt) ⊆
      (Finset.univ : Finset (Fin n)).biUnion
        (fun i => {i} ×ˢ ((Finset.univ.erase i).offDiag)) := by
    intro t ht
    obtain ⟨γ, _, htP⟩ := Finset.mem_biUnion.mp ht
    have hne : colDet g u₁ t.1 t.2.1 t.2.2 ≠ 0 := (Finset.mem_filter.mp htP).2
    obtain ⟨h12, h13, h23⟩ := colDet_distinct hne
    refine Finset.mem_biUnion.mpr ⟨t.1, Finset.mem_univ _, ?_⟩
    refine Finset.mem_product.mpr ⟨Finset.mem_singleton_self _, ?_⟩
    exact Finset.mem_offDiag.mpr ⟨Finset.mem_erase.mpr ⟨h12.symm, Finset.mem_univ _⟩,
      Finset.mem_erase.mpr ⟨h13.symm, Finset.mem_univ _⟩, h23⟩
  have hdisjE : ∀ i ∈ (Finset.univ : Finset (Fin n)), ∀ j ∈ (Finset.univ : Finset (Fin n)),
      i ≠ j → Disjoint ({i} ×ˢ ((Finset.univ.erase i).offDiag))
        ({j} ×ˢ ((Finset.univ.erase j).offDiag)) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro t ht1 ht2
    have h1 := Finset.mem_singleton.mp (Finset.mem_product.mp ht1).1
    have h2 := Finset.mem_singleton.mp (Finset.mem_product.mp ht2).1
    exact hij (h1.symm.trans h2)
  have hEcard : ((Finset.univ : Finset (Fin n)).biUnion
      (fun i => {i} ×ˢ ((Finset.univ.erase i).offDiag))).card = n * (n - 1) * (n - 2) := by
    rw [Finset.card_biUnion hdisjE]
    have hper : ∀ i : Fin n, ({i} ×ˢ ((Finset.univ.erase i).offDiag)).card
        = (n - 1) * (n - 2) := by
      intro i
      rw [Finset.card_product, Finset.card_singleton, one_mul, Finset.offDiag_card,
        Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
        sq_sub_self]
      have h21 : n - 1 - 1 = n - 2 := by omega
      rw [h21]
    calc ∑ i ∈ (Finset.univ : Finset (Fin n)),
          ({i} ×ˢ ((Finset.univ.erase i).offDiag)).card
        = ∑ _i ∈ (Finset.univ : Finset (Fin n)), (n - 1) * (n - 2) :=
          Finset.sum_congr rfl (fun i _ => hper i)
    _ = n * ((n - 1) * (n - 2)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    _ = n * (n - 1) * (n - 2) := by rw [mul_assoc]
  calc B.card * 12 = B.attach.card * 12 := by rw [Finset.card_attach]
  _ ≤ (B.attach.biUnion Pt).card := hbig
  _ ≤ ((Finset.univ : Finset (Fin n)).biUnion
        (fun i => {i} ×ˢ ((Finset.univ.erase i).offDiag))).card :=
      Finset.card_le_card hsubE
  _ = n * (n - 1) * (n - 2) := hEcard

open Classical in
/-- **The dimension-two `ε_mca` bound:** at agreement threshold `> 3`, the MCA error of the
dimension-two code is at most `(n(n−1)(n−2)/12)/p` — uniformly in `δ`. -/
theorem dimTwo_epsMCA_le
    {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ} [NeZero n]
    (hginj : ∀ i j : Fin n, g ^ (i : ℕ) = g ^ (j : ℕ) → i = j)
    {δ : ℝ≥0} (hδ : (3 : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0)) :
    epsMCA (F := ZMod p) (A := ZMod p) (evalCode g n 1) δ
      ≤ ((n * (n - 1) * (n - 2) / 12 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Nonempty (ZMod p) := ⟨0⟩
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card, ZMod.card p]
  simp only [ENNReal.coe_natCast]
  gcongr
  have h12 := dimTwo_badScalars_card_mul_twelve_le (g := g) hginj hδ (u 0) (u 1)
  have hle : (Finset.filter (fun γ : ZMod p =>
      mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n 1) δ (u 0) (u 1) γ)
      Finset.univ).card ≤ n * (n - 1) * (n - 2) / 12 :=
    (Nat.le_div_iff_mul_le (by norm_num)).mpr h12
  exact_mod_cast hle

/-! ## The `InteriorCeiling` discharge at `(r, m) = (3, 1)` -/

/-- Injectivity of `i ↦ g^i` below the order of `g` (local copy of the
`KKH26WitnessSpread` cancellation argument). -/
private lemma pow_inj_below_order {F : Type*} [Field F] {h : F} (h0 : h ≠ 0) {N : ℕ}
    (hN : orderOf h = N) :
    ∀ i, i < N → ∀ j, j < N → h ^ i = h ^ j → i = j := by
  have main : ∀ i j, i ≤ j → j < N → h ^ i = h ^ j → i = j := by
    intro i j hij hj heq
    have hadd : i + (j - i) = j := by omega
    have h2 : h ^ i * h ^ (j - i) = h ^ i * 1 := by
      rw [mul_one, ← pow_add, hadd, heq]
    have h3 : h ^ (j - i) = 1 := mul_left_cancel₀ (pow_ne_zero i h0) h2
    have h4 : N ∣ j - i := hN ▸ orderOf_dvd_of_pow_eq_one h3
    have h5 : j - i = 0 :=
      Nat.eq_zero_of_dvd_of_lt h4 (lt_of_le_of_lt (Nat.sub_le j i) hj)
    omega
  intro i hi j hj heq
  rcases le_total i j with hle | hle
  · exact main i j hle hj heq
  · exact (main j i hle hi heq.symm).symm

/-- **The interior ceiling holds unconditionally at the dimension-two slice:** for every
`ε* ≥ (n(n−1)(n−2)/12)/p` and every `δ` below the KKH26 ceiling `1 − 3/2^μ`, the agreement
threshold exceeds `3`, so the triple-ownership bound applies. -/
theorem interiorCeiling_dimTwo
    {p : ℕ} [Fact p.Prime] {μ : ℕ} {g : ZMod p} {n : ℕ} (hn : n = 2 ^ μ)
    [NeZero n] (hg : orderOf g = 2 ^ μ) (εstar : ℝ≥0∞)
    (hband : ((n * (n - 1) * (n - 2) / 12 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) ≤ εstar) :
    InteriorCeiling p n g μ 1 3 εstar := by
  intro δ hδ
  have hcode : ((3 : ℕ) - 2) * 1 = 1 := by norm_num
  rw [hcode]
  have hg0 : g ≠ 0 := by
    rintro rfl
    have h1 : (0 : ZMod p) ^ (2 ^ μ) = 1 := by
      rw [← hg]; exact pow_orderOf_eq_one 0
    rw [zero_pow (by positivity : (2 : ℕ) ^ μ ≠ 0)] at h1
    exact zero_ne_one h1
  have hginj : ∀ i j : Fin n, g ^ (i : ℕ) = g ^ (j : ℕ) → i = j := by
    intro i j hij
    have hi : (i : ℕ) < 2 ^ μ := by have := i.isLt; omega
    have hj : (j : ℕ) < 2 ^ μ := by have := j.isLt; omega
    exact Fin.ext (pow_inj_below_order hg0 hg _ hi _ hj hij)
  refine le_trans (dimTwo_epsMCA_le (g := g) hginj ?_) hband
  have hc3 : ((3 : ℕ) : ℝ≥0) = (3 : ℝ≥0) := by norm_num
  rw [hc3] at hδ
  have hsum : δ + (3 : ℝ≥0) / (2 : ℝ≥0) ^ μ < 1 := lt_tsub_iff_right.mp hδ
  have hlt : (3 : ℝ≥0) / (2 : ℝ≥0) ^ μ < 1 - δ := by
    rw [lt_tsub_iff_right]
    calc (3 : ℝ≥0) / (2 : ℝ≥0) ^ μ + δ = δ + (3 : ℝ≥0) / (2 : ℝ≥0) ^ μ := by ring
    _ < 1 := hsum
  have hpow0 : (0 : ℝ≥0) < (2 : ℝ≥0) ^ μ := by positivity
  have hmul : (3 : ℝ≥0) < (1 - δ) * (2 : ℝ≥0) ^ μ := by
    have h := mul_lt_mul_of_pos_right hlt hpow0
    rwa [div_mul_cancel₀ _ (ne_of_gt hpow0)] at h
  have hcard : ((Fintype.card (Fin n) : ℕ) : ℝ≥0) = (2 : ℝ≥0) ^ μ := by
    rw [Fintype.card_fin, hn]
    push_cast
    ring
  rw [hcard]
  exact hmul

/-! ## The `ε*` band is nonempty, and the pinned radius is in the open window -/

/-- **Band nonemptiness:** the triple-incidence bound `n(n−1)(n−2)/12` sits strictly below
the KKH26 ceiling count `2³·C(2^{μ−1}, 3)` for every `μ ≥ 3` (at `n = 8`: `28 < 32`). -/
theorem dimTwo_band_nonempty {μ : ℕ} (hμ : 3 ≤ μ) :
    2 ^ μ * (2 ^ μ - 1) * (2 ^ μ - 2) / 12 < 2 ^ 3 * (2 ^ (μ - 1)).choose 3 := by
  obtain ⟨ν, rfl⟩ : ∃ ν, μ = ν + 3 := ⟨μ - 3, (Nat.sub_add_cancel hμ).symm⟩
  have hy : 1 ≤ 2 ^ ν := Nat.one_le_two_pow
  obtain ⟨a, ha⟩ : ∃ a, 2 ^ ν = a + 1 := ⟨2 ^ ν - 1, by omega⟩
  have hpow : (2 : ℕ) ^ (ν + 3) = 8 * a + 8 := by rw [pow_add, ha]; ring
  have hpow1 : (2 : ℕ) ^ (ν + 3 - 1) = 4 * a + 4 := by
    have h21 : ν + 3 - 1 = ν + 2 := by omega
    rw [h21, pow_add, ha]; ring
  rw [Nat.div_lt_iff_lt_mul (by norm_num : (0 : ℕ) < 12), hpow, hpow1]
  have hdesc : (4 * a + 4).descFactorial 3 = (4 * a + 4) * (4 * a + 3) * (4 * a + 2) := by
    have e1 : 4 * a + 4 - 1 = 4 * a + 3 := by omega
    have e2 : 4 * a + 4 - 2 = 4 * a + 2 := by omega
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero, e1, e2]
    ring
  have hdvd : 6 ∣ (4 * a + 4).descFactorial 3 := by
    have h := Nat.factorial_dvd_descFactorial (4 * a + 4) 3
    rwa [show Nat.factorial 3 = 6 from rfl] at h
  have h6 : 6 * (4 * a + 4).choose 3 = (4 * a + 4) * (4 * a + 3) * (4 * a + 2) := by
    rw [Nat.choose_eq_descFactorial_div_factorial, show Nat.factorial 3 = 6 from rfl,
      Nat.mul_div_cancel' hdvd]
    exact hdesc
  have e3 : 8 * a + 8 - 1 = 8 * a + 7 := by omega
  have e4 : 8 * a + 8 - 2 = 8 * a + 6 := by omega
  rw [e3, e4]
  have hrhs : 2 ^ 3 * (4 * a + 4).choose 3 * 12 = 16 * (6 * (4 * a + 4).choose 3) := by
    ring
  rw [hrhs, h6]
  have hpos : 0 < 512 * a ^ 3 + 960 * a ^ 2 + 496 * a + 48 := by positivity
  calc (8 * a + 8) * (8 * a + 7) * (8 * a + 6)
      < (8 * a + 8) * (8 * a + 7) * (8 * a + 6)
        + (512 * a ^ 3 + 960 * a ^ 2 + 496 * a + 48) := Nat.lt_add_of_pos_right hpos
  _ = 16 * ((4 * a + 4) * (4 * a + 3) * (4 * a + 2)) := by ring

/-- **Beyond Johnson (squared form):** at every valid `μ ≥ 3` the ceiling's distance to `1`
is strictly below the Johnson distance `√ρ` (`ρ = 2/2^μ` the rate of the dimension-two
code), stated square-free as `(3/2^μ)² < ρ`.  Hence the pinned radius `1 − 3/2^μ` lies
strictly beyond the Johnson radius `1 − √ρ` — the entire `r = 3` rung is in-window. -/
theorem dimTwo_ceiling_beyond_johnson_sq {μ : ℕ} (hμ : 3 ≤ μ) :
    ((3 : ℝ≥0) / (2 : ℝ≥0) ^ μ) ^ 2 < (2 : ℝ≥0) / (2 : ℝ≥0) ^ μ := by
  have hpow0 : (0 : ℝ≥0) < (2 : ℝ≥0) ^ μ := by positivity
  rw [div_pow, div_lt_div_iff₀ (by positivity) hpow0]
  calc (3 : ℝ≥0) ^ 2 * (2 : ℝ≥0) ^ μ < (2 : ℝ≥0) ^ 4 * (2 : ℝ≥0) ^ μ := by
        refine mul_lt_mul_of_pos_right ?_ hpow0
        norm_num
  _ = (2 : ℝ≥0) ^ (4 + μ) := by rw [pow_add]
  _ ≤ (2 : ℝ≥0) ^ (μ * 2 + 1) := pow_le_pow_right₀ one_le_two (by omega)
  _ = 2 * ((2 : ℝ≥0) ^ μ) ^ 2 := by rw [← pow_mul, pow_succ, mul_comm]

/-- **Below capacity:** the pinned radius `1 − 3/2^μ` is strictly below capacity
`1 − ρ = 1 − 2/2^μ` for every `μ ≥ 2`. -/
theorem dimTwo_ceiling_below_capacity {μ : ℕ} (hμ : 2 ≤ μ) :
    (1 : ℝ≥0) - (3 : ℝ≥0) / (2 : ℝ≥0) ^ μ < 1 - (2 : ℝ≥0) / (2 : ℝ≥0) ^ μ := by
  have hpow0 : (0 : ℝ≥0) < (2 : ℝ≥0) ^ μ := by positivity
  have h3le : (3 : ℝ≥0) / (2 : ℝ≥0) ^ μ ≤ 1 := by
    rw [div_le_one hpow0]
    calc (3 : ℝ≥0) ≤ 2 ^ 2 := by norm_num
    _ ≤ 2 ^ μ := pow_le_pow_right₀ one_le_two hμ
  have hlt : (2 : ℝ≥0) / (2 : ℝ≥0) ^ μ < (3 : ℝ≥0) / (2 : ℝ≥0) ^ μ := by
    rw [div_lt_div_iff₀ hpow0 hpow0]
    exact mul_lt_mul_of_pos_right (by norm_num) hpow0
  have h2le : (2 : ℝ≥0) / (2 : ℝ≥0) ^ μ ≤ 1 := le_trans hlt.le h3le
  rw [← NNReal.coe_lt_coe, NNReal.coe_sub h2le, NNReal.coe_sub h3le, NNReal.coe_one]
  have hltR := NNReal.coe_lt_coe.mpr hlt
  linarith

/-! ## THE PIN -/

/-- **THE SECOND RUNG OF THE DIMENSION LADDER.**  For the dimension-two code on the smooth
`2^μ`-point domain (`μ ≥ 3`) and every `ε*` in the band
`[(n(n−1)(n−2)/12)/p, (2³·C(2^{μ−1},3))/p)` — nonempty by `dimTwo_band_nonempty` —

  `mcaDeltaStar(evalCode g (2^μ) 1, ε*) = 1 − 3/2^μ`

with **no open obligation**: the good side is the triple-ownership incidence bound, the bad
side is the in-tree KKH26 witness spread.  The pinned value lies strictly inside the open
window (beyond Johnson, below capacity) at *every* valid `μ`. -/
theorem kkh26_dimTwo_deltaStar_pin
    {p : ℕ} [Fact p.Prime] {μ : ℕ} (hμ : 3 ≤ μ) {g : ZMod p} {n : ℕ} (hn : n = 2 ^ μ)
    [NeZero n] (hg : orderOf g = 2 ^ μ)
    (hp : ((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) < p) (εstar : ℝ≥0∞)
    (hlo : ((n * (n - 1) * (n - 2) / 12 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) ≤ εstar)
    (hhi : εstar < ((2 ^ 3 * (2 ^ (μ - 1)).choose 3 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n 1) εstar
      = 1 - (3 : ℝ≥0) / ((2 : ℝ≥0) ^ μ) := by
  have hr : (3 : ℕ) ≤ 2 ^ (μ - 1) := by
    calc (3 : ℕ) ≤ 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (μ - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcode : ((3 : ℕ) - 2) * 1 = 1 := by norm_num
  have h := kkh26_deltaStar_pin_of_interior_ceiling (p := p) (n := n) (μ := μ) (m := 1)
    (r := 3) (g := g) (hμ := by omega) (hm := le_rfl) (hn := by rw [hn, mul_one])
    (hg := by rw [mul_one]; exact hg) (hp := hp) (hr2 := by norm_num) (hr := hr)
    (εstar := εstar) (hεstar := hhi)
    (hceiling := interiorCeiling_dimTwo hn hg εstar hlo)
  rw [hcode] at h
  have hc3 : ((3 : ℕ) : ℝ≥0) = (3 : ℝ≥0) := by norm_num
  rw [hc3] at h
  exact h

/-- **The canonical pin:** at `ε* = (n(n−1)(n−2)/12)/p` itself the pin always fires — band
membership is definitional on the left and `dimTwo_band_nonempty` on the right. -/
theorem kkh26_dimTwo_deltaStar_pin_canonical
    {p : ℕ} [Fact p.Prime] {μ : ℕ} (hμ : 3 ≤ μ) {g : ZMod p} {n : ℕ} (hn : n = 2 ^ μ)
    [NeZero n] (hg : orderOf g = 2 ^ μ)
    (hp : ((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) < p) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n 1)
        (((n * (n - 1) * (n - 2) / 12 : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞))
      = 1 - (3 : ℝ≥0) / ((2 : ℝ≥0) ^ μ) := by
  refine kkh26_dimTwo_deltaStar_pin hμ hn hg hp _ le_rfl ?_
  have hp0 : (p : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpt : (p : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top p
  have hlt' : ((n * (n - 1) * (n - 2) / 12 : ℕ) : ℝ≥0∞)
      < ((2 ^ 3 * (2 ^ (μ - 1)).choose 3 : ℕ) : ℝ≥0∞) := by
    rw [hn]
    exact_mod_cast dimTwo_band_nonempty hμ
  exact ENNReal.div_lt_div_right hp0 hpt hlt'

end ArkLib.ProximityGap.KKH26DimTwo

/-! ## The concrete instantiation: `δ* = 5/8` at the NTT prime `p = 12289` -/

namespace ArkLib.ProximityGap.KKH26DimTwo

section Concrete

local instance fact_prime_12289 : Fact (Nat.Prime 12289) := ⟨by norm_num⟩

/-- **The concrete pin at the NTT prime:** `δ* = 5/8` exactly, for the dimension-two code on
the 8-point smooth domain `⟨4043⟩ ⊆ F₁₂₂₈₉ˣ` at `ε* = 28/12289`.  The rate is `ρ = 1/4`, the
Johnson radius is `1 − 1/2 = 0.5 < 5/8`, capacity `3/4 > 5/8`: a second exact `δ*` value
strictly inside the open window — at a different rate than the `r = 2` instance — machine-
checked end to end. -/
theorem deltaStar_dimTwo_pin_F12289 :
    mcaDeltaStar (F := ZMod 12289) (A := ZMod 12289)
        (evalCode (4043 : ZMod 12289) 8 1) ((28 : ℝ≥0∞) / (12289 : ℝ≥0∞))
      = 5 / 8 := by
  haveI : NeZero (8 : ℕ) := ⟨by norm_num⟩
  have h := kkh26_dimTwo_deltaStar_pin_canonical (p := 12289) (μ := 3)
    (g := (4043 : ZMod 12289)) (n := 8) (by norm_num) (by norm_num)
    ArkLib.ProximityGap.KKH26DimOne.orderOf_4043 (by norm_num)
  have e1 : ((8 * (8 - 1) * (8 - 2) / 12 : ℕ) : ℝ≥0∞) = (28 : ℝ≥0∞) := by norm_num
  have e2 : ((12289 : ℕ) : ℝ≥0∞) = (12289 : ℝ≥0∞) := by norm_num
  have e3 : (1 : ℝ≥0) - (3 : ℝ≥0) / ((2 : ℝ≥0) ^ 3) = 5 / 8 := by
    have hd : (3 : ℝ≥0) / ((2 : ℝ≥0) ^ 3) = 3 / 8 := by norm_num
    rw [hd]
    refine tsub_eq_of_eq_add ?_
    norm_num
  rw [e1, e2, e3] at h
  exact h

end Concrete

end ArkLib.ProximityGap.KKH26DimTwo

/-! ## Axiom audit — kernel-clean. -/
#print axioms ArkLib.ProximityGap.KKH26DimTwo.dimTwo_badScalars_card_mul_twelve_le
#print axioms ArkLib.ProximityGap.KKH26DimTwo.dimTwo_epsMCA_le
#print axioms ArkLib.ProximityGap.KKH26DimTwo.interiorCeiling_dimTwo
#print axioms ArkLib.ProximityGap.KKH26DimTwo.dimTwo_band_nonempty
#print axioms ArkLib.ProximityGap.KKH26DimTwo.dimTwo_ceiling_beyond_johnson_sq
#print axioms ArkLib.ProximityGap.KKH26DimTwo.dimTwo_ceiling_below_capacity
#print axioms ArkLib.ProximityGap.KKH26DimTwo.kkh26_dimTwo_deltaStar_pin
#print axioms ArkLib.ProximityGap.KKH26DimTwo.kkh26_dimTwo_deltaStar_pin_canonical
#print axioms ArkLib.ProximityGap.KKH26DimTwo.deltaStar_dimTwo_pin_F12289
