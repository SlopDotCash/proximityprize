/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.StepanovNonVanishing
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R22SuperellipticIndependence

/-!
# LANE NORMFOLD (#466 round 24): `DBlockIndependence` at `d = 4` — PROVEN (tower route)

Round 22 named the `d`-block Stepanov independence `DBlockIndependence F d q D g` and proved
the `d = 2` instance from the in-tree #232 core `obstruction_forces_trivial`.  The prize family
(`TripleLinearHasse`) needs only **2-power** `d`, so `d = 4` is the first genuinely new case.
This file proves it, **unconditionally and axiom-clean**, at the predicted budget
`4·D + 3·deg g < q`, via the tower route the r22 map flagged: `Y⁴ − c = (Y²)² − c` is a tower
of two quadratic extensions, so the `d = 2` core iterates.

## The two-step proof (probe `probe_r24_normfold.py`, identities verified over ℚ and F₁₃)

**Step 1 (fold to `d = 2`, uses the in-tree core ONCE).**  Write `w = g^e`, `e = (q−1)/4`,
`S_j = A_j(X, X^q)`.  From the 4-block relation `R = S₀ + wS₁ + w²S₂ + w³S₃ = 0`, multiplying
by the alternating conjugate `S₀ − wS₁ + w²S₂ − w³S₃` gives the exact identity
`(S₀ + w²S₂)² − w²(S₁ + w²S₃)² = 0` — a `d = 2`-shaped relation in `v = w² = g^((q−1)/2)`.
Multiplying by `g` and folding `g^q = g(X^q)` (`pow_card_eq_subq_map_C`) exhibits it as
`subq B₀ + g^((q−1)/2)·subq B₁ = 0` for the two-variable **norm blocks**
`B₀ = g(X)A₀² + g(Y)(A₂² − 2A₁A₃)`, `B₁ = g(X)(2A₀A₂ − A₁²) − g(Y)A₃²`
(these are exactly `g·Nm_{K₄/K₂(θ²)}(∑ A_j θ^j)` written on the basis `1, θ²`).  Blocks of
`B₀, B₁` are `≤ deg g + 2D`, so `obstruction_forces_trivial` applies when
`2(deg g + 2D) + deg g = 4D + 3·deg g < q`, and yields `B₀ = B₁ = 0` in `F[X][Y]`.

**Step 2 (quartic descent, NO field extension needed).**  `B₀ = B₁ = 0` are the two components
of `Nm_{K(θ)/K(t)}(α) = 0` (`t = θ²`, `α = (A₀ + A₂t) + θ(A₁ + A₃t)`).  The classical uniqueness
argument builds `K(t)` and `K(θ)`; here it is replaced by **two polynomial identities** (checked
by `ring` inside `linear_combination`): with `u = a₀a₁ − ca₂a₃`, `v = a₁a₂ − a₀a₃`,
`n = a₁² − ca₃²`, `E₀ = a₀² + c(a₂² − 2a₁a₃)`, `E₁ = 2a₀a₂ − a₁² − ca₃²`,

  `u² + cv² = (a₁² + ca₃²)E₀ − 2ca₁a₃E₁`   and   `2uv − n² = (a₁² + ca₃²)E₁ − 2a₁a₃E₀`

(these are `(PQ̄)² − t·Nm(Q)² = Q̄²(P² − tQ²)` expanded on the basis `1, t` — the conjugate-
multiply trick done at the level of coefficients).  Hence `E₀ = E₁ = 0` forces, in ANY field
where `c` and `−c` are both non-squares: `v = 0` (else `−c = (u/v)²`), then `u = 0`, then
`n = 0`, then `a₃ = 0` (else `c = (a₁/a₃)²`), `a₁ = 0`, `a₂ = 0` (else `−c = (a₀/a₂)²`),
`a₀ = 0`.  Applied over `K = Frac(F(X)[Y])` with `c = g(Y)/g(X)`: both `±g(X)·g(Y)` are
unit-multiples of the squarefree positive-degree `g(Y) ∈ F(X)[Y]`, so both non-square by the
in-tree `squarefree_pos_not_isSquare_frac`.  (The `−c` case is exactly the `4 ∣ d` Kummer
side condition `c ∉ −4K⁴` in disguise, discharged here concretely.)

## What this file proves (all axiom-clean, real locked build)

* `quartic_descent` — the extension-free descent lemma over any field.
* `quartic_norm_forces_trivial` — the `d = 4` genus statement in `F[X][Y]` (the quartic
  analogue of the in-tree `genus_squarefree_forces_trivial`).
* `dBlockIndependence_four` — **`DBlockIndependence F 4 q D g` for every squarefree `g` of
  positive degree, `q` odd, `4 ∣ q − 1`, at budget `4D + 3·deg g < q`** — the first `d > 2`
  instance of the r22 target, the norm-fold lane's deliverable.

Open (named, honest): `d = 8, 16, …` iterate the same two steps but each doubling needs a NEW
descent lemma (the `d = 2k` descent has `k` component equations); odd `d ≥ 3` needs the full
cubic norm form (no tower).  `d = 4` is what the r=2 rung's first new face consumes.
-/

namespace ArkLib.ProximityGap.Frontier.R24DBlockIndependence

open Polynomial ArkLib.ProximityGap.StepanovNonVanishing
open ArkLib.ProximityGap.Frontier.R22SuperellipticIndependence

set_option linter.unusedFintypeInType false

variable {F : Type*} [Field F]

/-! ## 1. The quartic descent — pure field algebra, no extension construction -/

/-- **Quartic descent (extension-free).**  Over any field `K`, if `c` and `−c` are both
non-squares, then the two component equations of the quartic norm form
`E₀ = a₀² + c(a₂² − 2a₁a₃) = 0`, `E₁ = 2a₀a₂ − a₁² − ca₃² = 0` force
`a₀ = a₁ = a₂ = a₃ = 0`.  The two `linear_combination` identities below are the
conjugate-multiply trick `(PQ̄)² − t·Nm(Q)² = Q̄²(P² − tQ²)` in `K(√c)`, expanded on the
basis `1, √c` — so no extension field is ever built. -/
theorem quartic_descent {K : Type*} [Field K] (c a0 a1 a2 a3 : K)
    (hc : ¬ IsSquare c) (hnc : ¬ IsSquare (-c))
    (h0 : a0 ^ 2 + c * (a2 ^ 2 - 2 * a1 * a3) = 0)
    (h1 : 2 * a0 * a2 - a1 ^ 2 - c * a3 ^ 2 = 0) :
    a0 = 0 ∧ a1 = 0 ∧ a2 = 0 ∧ a3 = 0 := by
  -- (A): u² + c·v² = 0
  have hA : (a0 * a1 - c * a2 * a3) ^ 2 + c * (a1 * a2 - a0 * a3) ^ 2 = 0 := by
    linear_combination (a1 ^ 2 + c * a3 ^ 2) * h0 - 2 * c * a1 * a3 * h1
  -- (B): 2·u·v = n²
  have hB : 2 * (a0 * a1 - c * a2 * a3) * (a1 * a2 - a0 * a3) - (a1 ^ 2 - c * a3 ^ 2) ^ 2 = 0 := by
    linear_combination (a1 ^ 2 + c * a3 ^ 2) * h1 - 2 * a1 * a3 * h0
  -- v = 0, else −c = (u/v)²
  have hv : a1 * a2 - a0 * a3 = 0 := by
    by_contra hv
    apply hnc
    refine ⟨(a0 * a1 - c * a2 * a3) / (a1 * a2 - a0 * a3), ?_⟩
    field_simp
    linear_combination -hA
  -- u = 0
  have hu : a0 * a1 - c * a2 * a3 = 0 := by
    have hu2 : (a0 * a1 - c * a2 * a3) ^ 2 = 0 := by
      linear_combination hA - c * (a1 * a2 - a0 * a3) * hv
    exact (pow_eq_zero_iff two_ne_zero).mp hu2
  -- n = 0
  have hn : a1 ^ 2 - c * a3 ^ 2 = 0 := by
    have hn2 : (a1 ^ 2 - c * a3 ^ 2) ^ 2 = 0 := by
      linear_combination -hB + 2 * (a1 * a2 - a0 * a3) * hu
    exact (pow_eq_zero_iff two_ne_zero).mp hn2
  -- a₃ = 0, else c = (a₁/a₃)²
  have ha3 : a3 = 0 := by
    by_contra ha3
    apply hc
    refine ⟨a1 / a3, ?_⟩
    field_simp
    linear_combination -hn
  subst ha3
  have ha1 : a1 = 0 := by
    have : a1 ^ 2 = 0 := by linear_combination hn
    exact (pow_eq_zero_iff two_ne_zero).mp this
  subst ha1
  -- a₂ = 0, else −c = (a₀/a₂)²
  have ha2 : a2 = 0 := by
    by_contra ha2
    apply hnc
    refine ⟨a0 / a2, ?_⟩
    field_simp
    linear_combination -h0
  have ha0 : a0 = 0 := by
    have : a0 ^ 2 = 0 := by
      linear_combination h0 - c * a2 * ha2
    exact (pow_eq_zero_iff two_ne_zero).mp this
  exact ⟨ha0, rfl, ha2, rfl⟩

/-! ## 2. The quartic genus statement in `F[X][Y]` -/

set_option maxHeartbeats 1000000 in
-- The fraction-field descent performs several large polynomial-map normalizations.
/-- **The `d = 4` genus statement, PROVEN** (quartic analogue of the in-tree
`genus_squarefree_forces_trivial`).  Over a finite field `F`, if the two norm-block
equations `g(X)·A₀² + g(Y)·(A₂² − 2A₁A₃) = 0` and `g(X)·(2A₀A₂ − A₁²) − g(Y)·A₃² = 0`
hold in `F[X][Y]` with `g` squarefree of positive degree, then `A₀ = A₁ = A₂ = A₃ = 0`.
Route: map into `K = Frac(F(X)[Y])`, set `c = g(Y)/g(X)`; both `±c` are non-squares
(`±g(X)g(Y)` is a unit multiple of the squarefree positive-degree `g(Y) ∈ F(X)[Y]`), then
`quartic_descent`. -/
theorem quartic_norm_forces_trivial [Fintype F]
    (g : F[X]) (hg : Squarefree g) (hdeg : 0 < g.natDegree)
    (A0 A1 A2 A3 : Polynomial (Polynomial F))
    (h0 : C g * A0 ^ 2 + (g.map C) * (A2 ^ 2 - 2 * A1 * A3) = 0)
    (h1 : C g * (2 * A0 * A2 - A1 ^ 2) - (g.map C) * A3 ^ 2 = 0) :
    A0 = 0 ∧ A1 = 0 ∧ A2 = 0 ∧ A3 = 0 := by
  set ι : F[X] →+* RatFunc F := algebraMap F[X] (RatFunc F) with hιdef
  have hιinj : Function.Injective ι := IsFractionRing.injective F[X] (RatFunc F)
  set φ : Polynomial (Polynomial F) →+* Polynomial (RatFunc F) := Polynomial.mapRingHom ι with hφ
  have hφinj : Function.Injective φ := Polynomial.map_injective ι hιinj
  set G : Polynomial (RatFunc F) := g.map (algebraMap F (RatFunc F)) with hGdef
  have hφC : φ (C g) = C (ι g) := by rw [hφ, coe_mapRingHom, Polynomial.map_C]
  have hφmap : φ (g.map (C : F →+* F[X])) = G := by
    rw [hφ, coe_mapRingHom, Polynomial.map_map, hGdef]; congr 1
  -- g ≠ 0 data
  have hg0 : g ≠ 0 := fun h => by simp [h] at hdeg
  have hιg0 : ι g ≠ 0 := fun h => hg0 (hιinj (h.trans (map_zero ι).symm))
  -- G is squarefree of positive degree over F(X)
  have hGsf : Squarefree G := by
    rw [hGdef]
    exact (PerfectField.separable_iff_squarefree.mpr hg).map.squarefree
  have hGdeg : 0 < G.natDegree := by
    rw [hGdef, natDegree_map_eq_of_injective (algebraMap F (RatFunc F)).injective]; exact hdeg
  -- the fraction field of F(X)[Y]
  set ψ : Polynomial (RatFunc F) →+* FractionRing (Polynomial (RatFunc F)) :=
    (algebraMap (Polynomial (RatFunc F)) (FractionRing (Polynomial (RatFunc F)))) with hψdef
  have hψinj : Function.Injective ψ :=
    IsFractionRing.injective (Polynomial (RatFunc F)) (FractionRing (Polynomial (RatFunc F)))
  set a0 := ψ (φ A0) with ha0def
  set a1 := ψ (φ A1) with ha1def
  set a2 := ψ (φ A2) with ha2def
  set a3 := ψ (φ A3) with ha3def
  set γK := ψ (C (ι g)) with hγKdef
  set GK := ψ G with hGKdef
  have hγK0 : γK ≠ 0 := fun h => by
    have h2 : (C (ι g) : Polynomial (RatFunc F)) = 0 := hψinj (h.trans (map_zero ψ).symm)
    rw [C_eq_zero] at h2
    exact hιg0 h2
  set c := GK / γK with hcdef
  have hGKc : GK = c * γK := by rw [hcdef, div_mul_cancel₀ _ hγK0]
  -- map the hypotheses through ψ ∘ φ
  have h0φ : C (ι g) * (φ A0) ^ 2 + G * ((φ A2) ^ 2 - 2 * (φ A1) * (φ A3)) = 0 := by
    have h := congrArg φ h0
    rw [map_add, map_mul, map_mul, map_sub, map_pow, map_pow, map_mul, map_mul, map_ofNat,
      map_zero, hφC, hφmap] at h
    exact h
  have h1φ : C (ι g) * (2 * (φ A0) * (φ A2) - (φ A1) ^ 2) - G * (φ A3) ^ 2 = 0 := by
    have h := congrArg φ h1
    rw [map_sub, map_mul, map_mul, map_sub, map_mul, map_mul, map_pow, map_pow, map_ofNat,
      map_zero, hφC, hφmap] at h
    exact h
  have h0K : γK * a0 ^ 2 + GK * (a2 ^ 2 - 2 * a1 * a3) = 0 := by
    have h := congrArg ψ h0φ
    rw [map_add, map_mul, map_mul, map_sub, map_pow, map_pow, map_mul, map_mul, map_ofNat,
      map_zero] at h
    exact h
  have h1K : γK * (2 * a0 * a2 - a1 ^ 2) - GK * a3 ^ 2 = 0 := by
    have h := congrArg ψ h1φ
    rw [map_sub, map_mul, map_mul, map_sub, map_mul, map_mul, map_pow, map_pow, map_ofNat,
      map_zero] at h
    exact h
  -- normalize to the descent shape
  have h0' : a0 ^ 2 + c * (a2 ^ 2 - 2 * a1 * a3) = 0 := by
    apply mul_left_cancel₀ hγK0
    rw [mul_zero]
    linear_combination h0K - (a2 ^ 2 - 2 * a1 * a3) * hGKc
  have h1' : 2 * a0 * a2 - a1 ^ 2 - c * a3 ^ 2 = 0 := by
    apply mul_left_cancel₀ hγK0
    rw [mul_zero]
    linear_combination h1K + a3 ^ 2 * hGKc
  -- non-square conditions: ±(scalar unit)·G is squarefree of positive degree in F(X)[Y]
  have hnotsq : ∀ δ : RatFunc F, δ ≠ 0 → ¬ IsSquare (ψ (C δ * G)) := by
    intro δ hδ
    have hsf2 : Squarefree (C δ * G) := by
      have hassoc : Associated (C δ * G) G :=
        ⟨(isUnit_C.mpr (Ne.isUnit (inv_ne_zero hδ))).unit, by
          rw [IsUnit.unit_spec]
          rw [mul_comm (C δ) G, mul_assoc, ← C_mul, mul_inv_cancel₀ hδ, C_1, mul_one]⟩
      exact hassoc.squarefree_iff.mpr hGsf
    have hdeg2 : 0 < (C δ * G).natDegree := by
      rw [natDegree_C_mul hδ]; exact hGdeg
    exact squarefree_pos_not_isSquare_frac (C δ * G) hsf2 hdeg2
  have hc : ¬ IsSquare c := by
    rintro ⟨r, hr⟩
    apply hnotsq (ι g) hιg0
    refine ⟨γK * r, ?_⟩
    rw [map_mul]
    linear_combination γK * hGKc + γK * γK * hr
  have hnc : ¬ IsSquare (-c) := by
    rintro ⟨r, hr⟩
    apply hnotsq (-(ι g)) (neg_ne_zero.mpr hιg0)
    refine ⟨γK * r, ?_⟩
    rw [show (C (-(ι g)) : Polynomial (RatFunc F)) = -(C (ι g)) from by rw [map_neg], neg_mul,
      map_neg, map_mul]
    linear_combination -γK * hGKc + γK * γK * hr
  obtain ⟨hz0, hz1, hz2, hz3⟩ := quartic_descent c a0 a1 a2 a3 hc hnc h0' h1'
  refine ⟨hφinj (hψinj ?_), hφinj (hψinj ?_), hφinj (hψinj ?_), hφinj (hψinj ?_)⟩ <;>
    simp only [map_zero]
  · exact hz0
  · exact hz1
  · exact hz2
  · exact hz3

/-! ## 3. Block-degree bookkeeping for the norm blocks -/

/-- Blocks of a product (instance-clean copy of `_R21StepanovS1.blocks_mul_le`, which
carries spurious `[Fintype F] [DecidableEq F]` section variables). -/
theorem blocks_mul_le {A B : Polynomial (Polynomial F)} {DA DB : ℕ}
    (hA : ∀ j, (A.coeff j).natDegree ≤ DA) (hB : ∀ j, (B.coeff j).natDegree ≤ DB) :
    ∀ j, ((A * B).coeff j).natDegree ≤ DA + DB := by
  intro j
  rw [coeff_mul]
  refine natDegree_sum_le_of_forall_le _ _ fun x _ => ?_
  exact natDegree_mul_le.trans (add_le_add (hA _) (hB _))

/-- Blocks of a difference (common bound). -/
theorem blocks_sub_le {A B : Polynomial (Polynomial F)} {a : ℕ}
    (hA : ∀ j, (A.coeff j).natDegree ≤ a) (hB : ∀ j, (B.coeff j).natDegree ≤ a) :
    ∀ j, ((A - B).coeff j).natDegree ≤ a := by
  intro j
  rw [coeff_sub]
  exact (natDegree_sub_le _ _).trans (max_le (hA j) (hB j))

/-- Blocks of `C g * A` are bounded by `deg g +` block bound. -/
theorem blocks_C_mul_le (g : F[X]) {A : Polynomial (Polynomial F)} {a : ℕ}
    (hA : ∀ j, (A.coeff j).natDegree ≤ a) :
    ∀ j, ((C g * A).coeff j).natDegree ≤ g.natDegree + a := by
  intro j
  rw [coeff_C_mul]
  exact natDegree_mul_le.trans (add_le_add le_rfl (hA j))

/-- Blocks of `ĝ * A` (the `Y`-lift `g.map C`) keep the block bound of `A`. -/
theorem blocks_mapC_mul_le (g : F[X]) {A : Polynomial (Polynomial F)} {a : ℕ}
    (hA : ∀ j, (A.coeff j).natDegree ≤ a) :
    ∀ j, (((g.map (C : F →+* F[X])) * A).coeff j).natDegree ≤ a := by
  have hmapblk : ∀ j, ((g.map (C : F →+* F[X])).coeff j).natDegree ≤ 0 := by
    intro j; rw [coeff_map]; exact le_of_eq (natDegree_C _)
  intro j
  simpa using blocks_mul_le hmapblk hA j

/-- Blocks of `2·A·B`. -/
theorem blocks_two_mul_mul_le {A B : Polynomial (Polynomial F)} {a b : ℕ}
    (hA : ∀ j, (A.coeff j).natDegree ≤ a) (hB : ∀ j, (B.coeff j).natDegree ≤ b) :
    ∀ j, ((2 * A * B).coeff j).natDegree ≤ a + b := by
  have h2A : ∀ j, ((2 * A).coeff j).natDegree ≤ a := by
    intro j
    rw [two_mul, coeff_add]
    exact (natDegree_add_le _ _).trans (max_le (hA j) (hA j))
  exact blocks_mul_le h2A hB

/-! ## 4. The main theorem: `DBlockIndependence` at `d = 4` -/

set_option maxHeartbeats 1000000 in
-- The final fold combines the quartic norm algebra with degree-budget bookkeeping.
/-- **`DBlockIndependence F 4 q D g`, PROVEN** — the first `d > 2` instance of the round-22
target, at the predicted budget `4D + 3·deg g < q`.  Requires `q` odd (the in-tree `d = 2`
core) and `4 ∣ q − 1` (so `w = g^((q−1)/4)` is exact and `(q−1)/2 = 2(q−1)/4`).

Step 1 folds the 4-block relation, via the alternating conjugate and `g^q = g(X^q)`, into a
`d = 2` relation whose blocks are the quartic norm blocks `B₀, B₁`; the in-tree
`obstruction_forces_trivial` then gives `B₀ = B₁ = 0`.  Step 2 is `quartic_norm_forces_trivial`. -/
theorem dBlockIndependence_four [Fintype F]
    (g : F[X]) (hg : Squarefree g) (hdeg : 0 < g.natDegree)
    (hq_odd : Odd (Fintype.card F)) (h4 : 4 ∣ (Fintype.card F - 1))
    {D : ℕ} (hD : 4 * D + 3 * g.natDegree < Fintype.card F) :
    DBlockIndependence F 4 (Fintype.card F) D g := by
  intro A hblk hsum j
  set q := Fintype.card F with hqdef
  obtain ⟨e, he⟩ := h4
  have hq1 : 1 ≤ q := Fintype.card_pos
  have hqe : q = 4 * e + 1 := by omega
  have h2e : (q - 1) / 2 = 2 * e := by omega
  have h4e : (q - 1) / 4 = e := by omega
  -- the folded 4-block relation
  have hsum4 : subq q (A 0) + g ^ e * subq q (A 1) + g ^ (2 * e) * subq q (A 2)
      + g ^ (3 * e) * subq q (A 3) = 0 := by
    have h := hsum
    rw [Fin.sum_univ_four] at h
    have h0v : ((0 : Fin 4) : ℕ) = 0 := rfl
    have h1v : ((1 : Fin 4) : ℕ) = 1 := rfl
    have h2v : ((2 : Fin 4) : ℕ) = 2 := rfl
    have h3v : ((3 : Fin 4) : ℕ) = 3 := rfl
    rw [h0v, h1v, h2v, h3v, h4e] at h
    linear_combination h
  -- the norm blocks
  set B0 : Polynomial (Polynomial F) :=
    C g * (A 0) ^ 2 + (g.map C) * ((A 2) ^ 2 - 2 * (A 1) * (A 3)) with hB0def
  set B1 : Polynomial (Polynomial F) :=
    C g * (2 * (A 0) * (A 2) - (A 1) ^ 2) - (g.map C) * (A 3) ^ 2 with hB1def
  -- fold subq through the blocks
  have hgq : subq q (g.map (C : F →+* F[X])) = g ^ q := (pow_card_eq_subq_map_C g).symm
  have hSB0 : subq q B0 = g * (subq q (A 0)) ^ 2
      + g ^ q * ((subq q (A 2)) ^ 2 - 2 * (subq q (A 1)) * (subq q (A 3))) := by
    rw [hB0def]
    change subqHom q _ = _
    rw [map_add, map_mul, map_mul, map_sub, map_pow, map_pow, map_mul, map_mul, map_ofNat]
    rw [subqHom_apply, subqHom_apply, subqHom_apply, subqHom_apply, subqHom_apply,
      subqHom_apply, subq_C, hgq]
  have hSB1 : subq q B1 = g * (2 * (subq q (A 0)) * (subq q (A 2)) - (subq q (A 1)) ^ 2)
      - g ^ q * (subq q (A 3)) ^ 2 := by
    rw [hB1def]
    change subqHom q _ = _
    rw [map_sub, map_mul, map_mul, map_sub, map_mul, map_mul, map_pow, map_pow, map_ofNat]
    rw [subqHom_apply, subqHom_apply, subqHom_apply, subqHom_apply, subqHom_apply,
      subqHom_apply, subq_C, hgq]
  -- the d = 2 relation for the norm blocks
  have hR : subq q B0 + g ^ ((q - 1) / 2) * subq q B1 = 0 := by
    have hkey : (subq q (A 0) + g ^ (2 * e) * subq q (A 2)) ^ 2
        - g ^ (2 * e) * (subq q (A 1) + g ^ (2 * e) * subq q (A 3)) ^ 2 = 0 := by
      linear_combination (subq q (A 0) - g ^ e * subq q (A 1) + g ^ (2 * e) * subq q (A 2)
        - g ^ (3 * e) * subq q (A 3)) * hsum4
    have hgq4 : g ^ q = g ^ (4 * e + 1) := by rw [← hqe]
    rw [hSB0, hSB1, h2e, hgq4]
    linear_combination g * hkey
  -- budget: blocks of B₀, B₁ ≤ deg g + 2D
  have hsq : ∀ i : Fin 4, ∀ k, (((A i) ^ 2).coeff k).natDegree ≤ 2 * D := fun i =>
    blocks_pow_le (hblk i) 2
  have h13 : ∀ k, ((2 * (A 1) * (A 3)).coeff k).natDegree ≤ 2 * D := by
    intro k
    have := blocks_two_mul_mul_le (hblk 1) (hblk 3) k
    omega
  have h02 : ∀ k, ((2 * (A 0) * (A 2)).coeff k).natDegree ≤ 2 * D := by
    intro k
    have := blocks_two_mul_mul_le (hblk 0) (hblk 2) k
    omega
  have hb0 : ∀ k, (B0.coeff k).natDegree ≤ g.natDegree + 2 * D := by
    intro k
    rw [hB0def, coeff_add]
    have ht1 := blocks_C_mul_le g (hsq 0) k
    have ht2 := blocks_mapC_mul_le g (blocks_sub_le (hsq 2) h13) k
    exact (natDegree_add_le _ _).trans (max_le ht1 (by omega))
  have hb1 : ∀ k, (B1.coeff k).natDegree ≤ g.natDegree + 2 * D := by
    intro k
    rw [hB1def, coeff_sub]
    have ht1 := blocks_C_mul_le g (blocks_sub_le h02 (hsq 1)) k
    have ht2 := blocks_mapC_mul_le g (hsq 3) k
    exact (natDegree_sub_le _ _).trans (max_le ht1 (by omega))
  have hcomb : ∀ k, ((C g * B0 ^ 2 - (g.map C) * B1 ^ 2).coeff k).natDegree < q :=
    combined_blocks_lt_general g
      (show 2 * (g.natDegree + 2 * D) + g.natDegree < q by omega) B0 B1 hb0 hb1
  -- the d = 2 core fires once
  obtain ⟨hB0z, hB1z⟩ := obstruction_forces_trivial g hg hdeg hq_odd B0 B1 hcomb hR
  -- the quartic descent finishes
  obtain ⟨h0z, h1z, h2z, h3z⟩ := quartic_norm_forces_trivial g hg hdeg (A 0) (A 1) (A 2) (A 3)
    (hB0def.symm.trans hB0z) (hB1def.symm.trans hB1z)
  fin_cases j
  · exact h0z
  · exact h1z
  · exact h2z
  · exact h3z

end ArkLib.ProximityGap.Frontier.R24DBlockIndependence

/-! ## Axiom audit -/
open ArkLib.ProximityGap.Frontier.R24DBlockIndependence in
#print axioms quartic_descent
open ArkLib.ProximityGap.Frontier.R24DBlockIndependence in
#print axioms quartic_norm_forces_trivial
open ArkLib.ProximityGap.Frontier.R24DBlockIndependence in
#print axioms dBlockIndependence_four
