/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
/-
Round 15, Angle 2 — the multiplicity-`m ≥ 2` Guruswami–Sudan FRONT END
(Hasse/shift constraint counting), self-contained over Mathlib only.

PROVED here, end to end:

* (a) `shift2` — the bivariate coordinate shift `Q(X, Y) ↦ Q(X + a, Y + b)` on `F[X][Y]`,
  realized as inner `eval₂RingHom C (X + C a)` on coefficients followed by outer composition
  with `Y + b`.  "Vanishing to order `m` at `(a, b)`" is encoded as: every coefficient of
  `shift2 a b Q` of total degree `< m` is zero.  These are exactly `(m+1).choose 2` linear
  conditions per point (`gsSupport_two_card`).
* (b) `hasse_interpolation_exists` / `hasse_interpolation_exists_choose` — the dimension
  count: if `n * (m+1).choose 2 < #gsSupport(D, k)` then a NONZERO `Q ∈ F[X][Y]`, all of
  whose monomials `X^i Y^j` satisfy `i + (k-1)·j < D`, exists vanishing to order `m` at all
  `n` points `(α s, w s)`.  Same rank–nullity engine as the multiplicity-1 (Sudan) case, with
  the constraint space enlarged from point evaluations to the shifted-coefficient functionals.
* (c) `pow_X_sub_C_dvd_eval_of_hasseVanish` — the root-order payoff: if `Q` vanishes to
  order `m` at `(a, b)` and `f(a) = b`, then `(X - C a)^m ∣ Q.eval f`.  Proof: conjugate by
  the shift `X ↦ X + a` (a ring isomorphism with inverse `X ↦ X - a`), reduce to
  `X^m ∣ (shift2 a b Q).eval u` for `u` with `u(0) = 0`, and read divisibility off the
  vanishing coefficients term by term.
* The multiplicity-`m` factor step `factor_of_order_agreement` — order-`m` vanishing on an
  agreement set `A` with `D ≤ m·#A` forces `(Y - C f) ∣ Q` (product of coprime
  `(X - C α)^m` exceeds the degree budget), and the assembled
  `gs_decoder_pipeline` — from the dimension count alone, an interpolant exists such that
  EVERY `f` of degree `≤ k-1` agreeing with the received word on `t` points with `m·t ≥ D`
  yields the factor `(Y - C f) ∣ Q`.
* (d) concrete instances over `ZMod 5` with `m = 2` exhibiting every hypothesis
  (`gs_hasse_instance_ZMod5`, `gs_pipeline_instance_ZMod5`), so nothing is vacuous.

NOT proved (honest scope): the `Y`-degree list-size cap (a separate, multiplicity-independent
brick), parameter optimization of `(D, m)` against `n, k` (the Johnson-radius arithmetic), and
any claim past the Johnson radius.  This file is exactly the `m ≥ 2` linear-algebra front end
plus its root-order/factor payoff, verified end to end.
-/
import Mathlib

set_option maxHeartbeats 1600000

open Polynomial

namespace GSHasse

/-! ### 1. Rank–nullity existence brick -/

theorem exists_ne_zero_map_eq_zero_of_finrank_lt
    {F V W : Type*} [Field F] [AddCommGroup V] [Module F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (L : V →ₗ[F] W) (h : Module.finrank F W < Module.finrank F V) :
    ∃ v : V, v ≠ 0 ∧ L v = 0 := by
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    by_contra hne
    exact hcon v hne hv
  exact absurd (LinearMap.finrank_le_finrank_of_injective hinj) (not_le.mpr h)

/-! ### 2. The weighted-degree monomial support and its exact count -/

/-- Monomial support of the GS interpolation space: pairs `(i, j)` with
`i + (k-1)·j < D`, organized as rows indexed by the `Y`-degree `j`. -/
def gsSupport (D k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range D).biUnion fun j => (Finset.range (D - (k - 1) * j)).image fun i => (i, j)

lemma gsSupport_weight_lt {D k : ℕ} {p : ℕ × ℕ} (hp : p ∈ gsSupport D k) :
    p.1 + (k - 1) * p.2 < D := by
  simp only [gsSupport, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image] at hp
  obtain ⟨j', hj', i', hi', heq⟩ := hp
  have h1 : p.1 = i' := by rw [← heq]
  have h2 : p.2 = j' := by rw [← heq]
  rw [h1, h2]
  omega

lemma mem_gsSupport {D k : ℕ} (hk : 2 ≤ k) {p : ℕ × ℕ} :
    p ∈ gsSupport D k ↔ p.1 + (k - 1) * p.2 < D := by
  refine ⟨gsSupport_weight_lt, fun h => ?_⟩
  have hj : p.2 ≤ (k - 1) * p.2 := Nat.le_mul_of_pos_left p.2 (by omega)
  simp only [gsSupport, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
  exact ⟨p.2, by omega, p.1, by omega, Prod.mk.eta⟩

/-- Exact count of the monomial support: `∑_{j<D} (D - (k-1)·j)`. -/
lemma gsSupport_card (D k : ℕ) :
    (gsSupport D k).card = ∑ j ∈ Finset.range D, (D - (k - 1) * j) := by
  have hdisj : ∀ j₁ ∈ Finset.range D, ∀ j₂ ∈ Finset.range D, j₁ ≠ j₂ →
      Disjoint ((Finset.range (D - (k - 1) * j₁)).image fun i => (i, j₁))
        ((Finset.range (D - (k - 1) * j₂)).image fun i => (i, j₂)) := by
    intro j₁ _ j₂ _ hne
    rw [Finset.disjoint_left]
    rintro p hp₁ hp₂
    simp only [Finset.mem_image, Finset.mem_range] at hp₁ hp₂
    obtain ⟨i₁, _, rfl⟩ := hp₁
    obtain ⟨i₂, _, heq⟩ := hp₂
    exact hne (congrArg Prod.snd heq).symm
  rw [gsSupport, Finset.card_biUnion hdisj]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.card_image_of_injective _ fun a b hab => congrArg Prod.fst hab,
    Finset.card_range]

/-- The triangular count: `∑_{j<m} (m - j) = (m+1).choose 2`. -/
lemma sum_range_sub_eq_choose (m : ℕ) :
    ∑ j ∈ Finset.range m, (m - j) = (m + 1).choose 2 := by
  have h1 : ∑ j ∈ Finset.range m, (m - j) = ∑ j ∈ Finset.range m, (j + 1) := by
    rw [← Finset.sum_range_reflect (fun j => j + 1) m]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    omega
  have h2 : ∑ j ∈ Finset.range (m + 1), j = ∑ j ∈ Finset.range m, (j + 1) := by
    rw [Finset.sum_range_succ' (fun j => j) m]
    simp
  have h3 := Finset.sum_range_id_mul_two (m + 1)
  rw [h1, ← h2, Nat.choose_two_right]
  omega

/-- The total-degree-`< m` index set is `gsSupport m 2`, of size exactly `(m+1).choose 2` —
the number of Hasse/divided-power conditions per interpolation point. -/
lemma gsSupport_two_card (m : ℕ) : (gsSupport m 2).card = (m + 1).choose 2 := by
  rw [gsSupport_card]
  have h : ∑ j ∈ Finset.range m, (m - (2 - 1) * j) = ∑ j ∈ Finset.range m, (m - j) :=
    Finset.sum_congr rfl fun j _ => by omega
  rw [h, sum_range_sub_eq_choose]

/-! ### 3. Bivariate polynomial from a coefficient vector -/

variable {F : Type*} [Field F]

/-- The bivariate polynomial (element of `F[X][Y]`, outer variable `Y`) with coefficient
`c' (i, j)` on the monomial `X^i·Y^j`, for `(i, j)` ranging over `S`. -/
noncomputable def coeffPoly (S : Finset (ℕ × ℕ)) (c' : ℕ × ℕ → F) :
    Polynomial (Polynomial F) :=
  ∑ p ∈ S, Polynomial.monomial p.2 (Polynomial.monomial p.1 (c' p))

lemma coeffPoly_coeff (S : Finset (ℕ × ℕ)) (c' : ℕ × ℕ → F) (i j : ℕ) :
    ((coeffPoly S c').coeff j).coeff i = if (i, j) ∈ S then c' (i, j) else 0 := by
  unfold coeffPoly
  rw [Polynomial.finset_sum_coeff, Polynomial.finset_sum_coeff]
  have step : ∀ p ∈ S,
      ((Polynomial.monomial p.2 (Polynomial.monomial p.1 (c' p))).coeff j).coeff i
        = if p = (i, j) then c' p else 0 := by
    intro p _
    rcases eq_or_ne p.2 j with h2 | h2
    · rw [Polynomial.coeff_monomial, if_pos h2, Polynomial.coeff_monomial]
      rcases eq_or_ne p.1 i with h1 | h1
      · rw [if_pos h1, if_pos (by rw [← h1, ← h2])]
      · rw [if_neg h1, if_neg fun hpe => h1 (by rw [hpe])]
    · rw [Polynomial.coeff_monomial, if_neg h2, Polynomial.coeff_zero,
        if_neg fun hpe => h2 (by rw [hpe])]
  rw [Finset.sum_congr rfl step, Finset.sum_ite_eq' S (i, j) fun p => c' p]

/-- Extension of a coefficient vector on `↥S` to all of `ℕ × ℕ` by zero. -/
def extendS (S : Finset (ℕ × ℕ)) (c : ↥S → F) : ℕ × ℕ → F :=
  fun p => if h : p ∈ S then c ⟨p, h⟩ else 0

lemma extendS_add (S : Finset (ℕ × ℕ)) (c d : ↥S → F) :
    extendS S (c + d) = extendS S c + extendS S d := by
  funext p
  by_cases h : p ∈ S <;> simp [extendS, h]

lemma extendS_smul (S : Finset (ℕ × ℕ)) (a : F) (c : ↥S → F) :
    extendS S (a • c) = a • extendS S c := by
  funext p
  by_cases h : p ∈ S <;> simp [extendS, h]

lemma coeffPoly_add (S : Finset (ℕ × ℕ)) (c' d' : ℕ × ℕ → F) :
    coeffPoly S (c' + d') = coeffPoly S c' + coeffPoly S d' := by
  unfold coeffPoly
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Pi.add_apply, map_add]

lemma coeffPoly_smul (S : Finset (ℕ × ℕ)) (a : F) (c' : ℕ × ℕ → F) :
    coeffPoly S (a • c') = a • coeffPoly S c' := by
  unfold coeffPoly
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Polynomial.smul_monomial, Pi.smul_apply]

/-! ### 4. (a) The bivariate shift and order-`m` vanishing -/

/-- The inner shift `X ↦ X + a` on `F[X]`, as a ring homomorphism. -/
noncomputable def innerShiftRH (a : F) : Polynomial F →+* Polynomial F :=
  Polynomial.eval₂RingHom Polynomial.C (Polynomial.X + Polynomial.C a)

lemma innerShiftRH_apply (a : F) (g : Polynomial F) :
    innerShiftRH a g = Polynomial.eval₂ Polynomial.C (Polynomial.X + Polynomial.C a) g := rfl

lemma innerShiftRH_eq_comp (a : F) (g : Polynomial F) :
    innerShiftRH a g = g.comp (Polynomial.X + Polynomial.C a) := rfl

lemma innerShiftRH_eq_taylor (a : F) (g : Polynomial F) :
    innerShiftRH a g = Polynomial.taylor a g := by
  rw [Polynomial.taylor_apply, innerShiftRH_eq_comp]

lemma innerShiftRH_C (a c : F) : innerShiftRH a (Polynomial.C c) = Polynomial.C c := by
  rw [innerShiftRH_apply, Polynomial.eval₂_C]

lemma innerShiftRH_smul (a c : F) (p : Polynomial F) :
    innerShiftRH a (c • p) = c • innerShiftRH a p := by
  rw [Polynomial.smul_eq_C_mul, Polynomial.smul_eq_C_mul, map_mul, innerShiftRH_C]

/-- **(a) The bivariate shift** `Q(X, Y) ↦ Q(X + a, Y + b)` on `F[X][Y]` (outer variable `Y`):
shift `X` inside every coefficient, then compose the outer variable with `Y + b`.
`Q` vanishes to order `m` at `(a, b)` iff every coefficient of `shift2 a b Q` of total degree
`< m` is zero. -/
noncomputable def shift2 (a b : F) (Q : Polynomial (Polynomial F)) :
    Polynomial (Polynomial F) :=
  (Q.map (innerShiftRH a)).comp (Polynomial.X + Polynomial.C (Polynomial.C b))

lemma shift2_add (a b : F) (Q R : Polynomial (Polynomial F)) :
    shift2 a b (Q + R) = shift2 a b Q + shift2 a b R := by
  unfold shift2
  rw [Polynomial.map_add, Polynomial.add_comp]

lemma map_smul_innerShiftRH (a c : F) (Q : Polynomial (Polynomial F)) :
    (c • Q).map (innerShiftRH a) = c • Q.map (innerShiftRH a) := by
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_map, Polynomial.coeff_smul, Polynomial.coeff_smul,
    Polynomial.coeff_map, innerShiftRH_smul]

lemma shift2_smul (a b c : F) (Q : Polynomial (Polynomial F)) :
    shift2 a b (c • Q) = c • shift2 a b Q := by
  unfold shift2
  rw [map_smul_innerShiftRH, Polynomial.smul_comp]

/-! ### 5. The Hasse-constraint linear map and the dimension count -/

/-- The linear map sending a coefficient vector supported on `S` to ALL order-`m` shifted
coefficients at the `n` points `(α s, w s)`: index `(s, (i, j))` with `i + j < m` reads the
`X^i Y^j`-coefficient of `Q(X + α s, Y + w s)`.  Its kernel is the order-`m` interpolation
space. -/
noncomputable def hasseConstraints (S : Finset (ℕ × ℕ)) {n : ℕ} (α w : Fin n → F) (m : ℕ) :
    (↥S → F) →ₗ[F] (Fin n × ↥(gsSupport m 2) → F) where
  toFun c q :=
    ((shift2 (α q.1) (w q.1) (coeffPoly S (extendS S c))).coeff
      (q.2 : ℕ × ℕ).2).coeff (q.2 : ℕ × ℕ).1
  map_add' c d := by
    funext q
    simp only [Pi.add_apply]
    rw [extendS_add, coeffPoly_add, shift2_add, Polynomial.coeff_add, Polynomial.coeff_add]
  map_smul' a c := by
    funext q
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    rw [extendS_smul, coeffPoly_smul, shift2_smul, Polynomial.coeff_smul,
      Polynomial.coeff_smul, smul_eq_mul]

lemma hasseConstraints_apply (S : Finset (ℕ × ℕ)) {n : ℕ} (α w : Fin n → F) (m : ℕ)
    (c : ↥S → F) (q : Fin n × ↥(gsSupport m 2)) :
    hasseConstraints S α w m c q
      = ((shift2 (α q.1) (w q.1) (coeffPoly S (extendS S c))).coeff
          (q.2 : ℕ × ℕ).2).coeff (q.2 : ℕ × ℕ).1 := rfl

/-- **(b) Multiplicity-`m` Guruswami–Sudan interpolation existence.**  If
`n · #{(i,j) : i+j < m} < #gsSupport(D, k)`, then a nonzero bivariate `Q ∈ F[X][Y]`, all of
whose monomials `X^i Y^j` satisfy `i + (k-1)·j < D`, exists vanishing to order `m` at every
point `(α s, w s)`.  No distinctness of the points is needed. -/
theorem hasse_interpolation_exists (k D m n : ℕ) (α w : Fin n → F)
    (hcount : n * (gsSupport m 2).card < (gsSupport D k).card) :
    ∃ Q : Polynomial (Polynomial F), Q ≠ 0 ∧
      (∀ i j : ℕ, (Q.coeff j).coeff i ≠ 0 → i + (k - 1) * j < D) ∧
      ∀ s : Fin n, ∀ i j : ℕ, i + j < m →
        ((shift2 (α s) (w s) Q).coeff j).coeff i = 0 := by
  have hrank : Module.finrank F (Fin n × ↥(gsSupport m 2) → F)
      < Module.finrank F (↥(gsSupport D k) → F) := by
    rw [Module.finrank_pi, Module.finrank_pi, Fintype.card_coe, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_coe]
    exact hcount
  obtain ⟨c, hc0, hLc⟩ := exists_ne_zero_map_eq_zero_of_finrank_lt
    (hasseConstraints (gsSupport D k) α w m) hrank
  refine ⟨coeffPoly (gsSupport D k) (extendS (gsSupport D k) c), ?_, ?_, ?_⟩
  · -- nonzero
    obtain ⟨q, hq⟩ : ∃ q : ↥(gsSupport D k), c q ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hc0 (funext hall)
    intro h0
    apply hq
    have h1 := coeffPoly_coeff (gsSupport D k) (extendS (gsSupport D k) c)
      (q : ℕ × ℕ).1 (q : ℕ × ℕ).2
    rw [h0] at h1
    simp only [Polynomial.coeff_zero, Prod.mk.eta] at h1
    rw [if_pos q.2] at h1
    have h2 : extendS (gsSupport D k) c (q : ℕ × ℕ) = c q := dif_pos q.2
    rw [h2] at h1
    exact h1.symm
  · -- weighted-degree bound on every monomial
    intro i j hne
    rw [coeffPoly_coeff] at hne
    by_cases hmem : (i, j) ∈ gsSupport D k
    · exact gsSupport_weight_lt hmem
    · exact absurd (if_neg hmem) hne
  · -- order-`m` vanishing at all n points
    intro s i j hij
    have hmem : (i, j) ∈ gsSupport m 2 :=
      (mem_gsSupport (le_refl 2)).mpr (by simpa using hij)
    have hL := congrFun hLc (s, ⟨(i, j), hmem⟩)
    rw [hasseConstraints_apply, Pi.zero_apply] at hL
    exact hL

/-- Convenience form of (b): the per-point constraint count stated as `(m+1).choose 2`. -/
theorem hasse_interpolation_exists_choose (k D m n : ℕ) (α w : Fin n → F)
    (hcount : n * (m + 1).choose 2 < (gsSupport D k).card) :
    ∃ Q : Polynomial (Polynomial F), Q ≠ 0 ∧
      (∀ i j : ℕ, (Q.coeff j).coeff i ≠ 0 → i + (k - 1) * j < D) ∧
      ∀ s : Fin n, ∀ i j : ℕ, i + j < m →
        ((shift2 (α s) (w s) Q).coeff j).coeff i = 0 :=
  hasse_interpolation_exists k D m n α w (by rwa [gsSupport_two_card])

/-! ### 6. (c) The root-order payoff -/

/-- **(c) Root-order payoff.**  If `Q` vanishes to order `m` at `(a, b)` (in the shifted-
coefficient sense) and `f(a) = b`, then `(X - C a)^m` divides the univariate restriction
`Q(X, f(X)) = Q.eval f`. -/
theorem pow_X_sub_C_dvd_eval_of_hasseVanish {a b : F} {m : ℕ}
    {Q : Polynomial (Polynomial F)} {f : Polynomial F} (hf : f.eval a = b)
    (hv : ∀ i j : ℕ, i + j < m → ((shift2 a b Q).coeff j).coeff i = 0) :
    (Polynomial.X - Polynomial.C a) ^ m ∣ Q.eval f := by
  -- Step A: the inner shift commutes with outer evaluation.
  have hA : ∀ P : Polynomial (Polynomial F),
      innerShiftRH a (P.eval f) = (P.map (innerShiftRH a)).eval (innerShiftRH a f) := by
    intro P
    induction P using Polynomial.induction_on' with
    | add p q hp hq =>
        rw [Polynomial.eval_add, map_add, hp, hq, Polynomial.map_add, Polynomial.eval_add]
    | monomial n p =>
        simp [Polynomial.eval_monomial, Polynomial.map_monomial, map_mul, map_pow]
  -- The shifted evaluation point `u`, with constant term zero.
  set u : Polynomial F := innerShiftRH a f - Polynomial.C b with hu_def
  have hfu : innerShiftRH a f = u + Polynomial.C b := by rw [hu_def]; ring
  have hu0 : u.coeff 0 = 0 := by
    have h1 : (innerShiftRH a f).coeff 0 = b := by
      rw [innerShiftRH_eq_comp, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp,
        Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, zero_add, hf]
    rw [hu_def, Polynomial.coeff_sub, h1, Polynomial.coeff_C_zero, sub_self]
  have hXu : (Polynomial.X : Polynomial F) ∣ u := Polynomial.X_dvd_iff.mpr hu0
  -- Step B: the shifted evaluation equals `(shift2 a b Q).eval u`.
  have hB : innerShiftRH a (Q.eval f) = (shift2 a b Q).eval u := by
    rw [hA, hfu]
    show (Q.map (innerShiftRH a)).eval (u + Polynomial.C b)
      = ((Q.map (innerShiftRH a)).comp
          (Polynomial.X + Polynomial.C (Polynomial.C b))).eval u
    rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  -- Step C: `X^m` divides the shifted evaluation, term by term.
  have hC : (Polynomial.X : Polynomial F) ^ m ∣ (shift2 a b Q).eval u := by
    rw [Polynomial.eval_eq_sum_range]
    refine Finset.dvd_sum fun j _ => ?_
    by_cases hjm : m ≤ j
    · exact ((pow_dvd_pow _ hjm).trans (pow_dvd_pow_of_dvd hXu j)).mul_left _
    · push Not at hjm
      have hcoeff : (Polynomial.X : Polynomial F) ^ (m - j) ∣ (shift2 a b Q).coeff j := by
        rw [Polynomial.X_pow_dvd_iff]
        intro d hd
        exact hv d j (by omega)
      have hupow : (Polynomial.X : Polynomial F) ^ j ∣ u ^ j := pow_dvd_pow_of_dvd hXu j
      have hmul := mul_dvd_mul hcoeff hupow
      rwa [← pow_add, Nat.sub_add_cancel hjm.le] at hmul
  -- Step D: pull back through the inverse shift `X ↦ X - a`.
  have hD : (Polynomial.X : Polynomial F) ^ m ∣ innerShiftRH a (Q.eval f) := hB ▸ hC
  have h1 := map_dvd (innerShiftRH (-a)) hD
  have h2 : innerShiftRH (-a) ((Polynomial.X : Polynomial F) ^ m)
      = (Polynomial.X - Polynomial.C a) ^ m := by
    rw [map_pow]
    congr 1
    rw [innerShiftRH_apply, Polynomial.eval₂_X, Polynomial.C_neg]
    ring
  have h3 : innerShiftRH (-a) (innerShiftRH a (Q.eval f)) = Q.eval f := by
    rw [innerShiftRH_eq_taylor, innerShiftRH_eq_taylor, Polynomial.taylor_taylor,
      neg_add_cancel, Polynomial.taylor_zero]
  rwa [h2, h3] at h1

/-! ### 7. The multiplicity-`m` factor step and the assembled pipeline -/

/-- Weighted-degree transfer (as in the multiplicity-1 brick): the support-form weighted
degree bound gives `deg(Q.eval f) < D` for `deg f ≤ k - 1`. -/
theorem natDegree_eval_lt {Q : Polynomial (Polynomial F)} {f : Polynomial F} {k D : ℕ}
    (hD : 0 < D)
    (hwdeg : ∀ j, Q.coeff j ≠ 0 → (Q.coeff j).natDegree + j * (k - 1) < D)
    (hf : f.natDegree ≤ k - 1) :
    (Q.eval f).natDegree < D := by
  have hterm : ∀ j ∈ Q.support, (Q.coeff j * f ^ j).natDegree ≤ D - 1 := by
    intro j hj
    have hcj : Q.coeff j ≠ 0 := mem_support_iff.mp hj
    have h1 : (Q.coeff j * f ^ j).natDegree ≤ (Q.coeff j).natDegree + (f ^ j).natDegree :=
      natDegree_mul_le
    have h2 : (f ^ j).natDegree ≤ j * f.natDegree := natDegree_pow_le
    have h3 : j * f.natDegree ≤ j * (k - 1) := Nat.mul_le_mul_left j hf
    have h4 : (Q.coeff j).natDegree + j * (k - 1) < D := hwdeg j hcj
    omega
  calc (Q.eval f).natDegree
      = (∑ j ∈ Q.support, Q.coeff j * f ^ j).natDegree := by
        rw [eval_eq_sum]; rfl
    _ ≤ D - 1 := natDegree_sum_le_of_forall_le _ _ hterm
    _ < D := by omega

/-- Conversion from the monomial-support weighted-degree form (the interpolation output) to
the `natDegree` form (the factor-step input). -/
lemma wdeg_natDegree_of_support {Q : Polynomial (Polynomial F)} {k D : ℕ}
    (h : ∀ i j : ℕ, (Q.coeff j).coeff i ≠ 0 → i + (k - 1) * j < D) :
    ∀ j, Q.coeff j ≠ 0 → (Q.coeff j).natDegree + j * (k - 1) < D := by
  intro j hj
  have hlc : (Q.coeff j).coeff (Q.coeff j).natDegree ≠ 0 := by
    rw [← Polynomial.leadingCoeff]
    exact Polynomial.leadingCoeff_ne_zero.mpr hj
  have h2 := h _ j hlc
  rw [mul_comm j (k - 1)]
  exact h2

/-- **The multiplicity-`m` factor step.**  If `Q` obeys the `(1, k-1)`-weighted degree bound
`< D` (`natDegree` form), `deg f ≤ k - 1`, and `Q` vanishes to order `m` at `(α, f(α))` for
all `α` in a set `A` with `D ≤ m·#A`, then `(Y - C f) ∣ Q`: the product
`∏_{α ∈ A} (X - C α)^m` of pairwise-coprime factors divides `Q.eval f`, whose degree is below
`m·#A` — so `Q.eval f = 0`. -/
theorem factor_of_order_agreement {Q : Polynomial (Polynomial F)} {f : Polynomial F}
    {k D m : ℕ} (hD : 0 < D)
    (hwdeg : ∀ j, Q.coeff j ≠ 0 → (Q.coeff j).natDegree + j * (k - 1) < D)
    (hf : f.natDegree ≤ k - 1)
    {A : Finset F} (hA : D ≤ m * A.card)
    (hord : ∀ α ∈ A, ∀ i j : ℕ, i + j < m →
      ((shift2 α (f.eval α) Q).coeff j).coeff i = 0) :
    (Polynomial.X - Polynomial.C f) ∣ Q := by
  classical
  rw [dvd_iff_isRoot]
  by_contra hne
  have hne' : Q.eval f ≠ 0 := hne
  have hdvd_each : ∀ α ∈ A, (Polynomial.X - Polynomial.C α) ^ m ∣ Q.eval f := fun α hα =>
    pow_X_sub_C_dvd_eval_of_hasseVanish rfl (hord α hα)
  have hprod : (∏ α ∈ A, (Polynomial.X - Polynomial.C α) ^ m) ∣ Q.eval f :=
    Finset.prod_dvd_of_coprime
      (fun x _ y _ hxy => (Polynomial.isCoprime_X_sub_C_of_isUnit_sub
        (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hxy))).pow)
      hdvd_each
  have hdegprod : (∏ α ∈ A, (Polynomial.X - Polynomial.C α) ^ m).natDegree = m * A.card := by
    rw [Polynomial.natDegree_prod _ _
      (fun α _ => pow_ne_zero m (Polynomial.X_sub_C_ne_zero α))]
    rw [Finset.sum_congr rfl fun α _ => by
      rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]]
    rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have hle := Polynomial.natDegree_le_of_dvd hprod hne'
  rw [hdegprod] at hle
  have hlt := natDegree_eval_lt hD hwdeg hf
  omega

/-- **The assembled `m ≥ 2` GS pipeline (front end + factor step).**  From the dimension
count `n·(m+1).choose 2 < #gsSupport(D, k)` alone (with `α` injective), there is a nonzero
interpolant `Q` of `(1, k-1)`-weighted degree `< D` such that for EVERY polynomial `f` of
degree `≤ k - 1` agreeing with the received word on at least `D/m` of the `n` points,
`(Y - C f)` divides `Q`.  Feeding the `Y`-degree cap then bounds the list size. -/
theorem gs_decoder_pipeline [DecidableEq F] (k D m n : ℕ) (hD : 0 < D)
    (α w : Fin n → F) (hinj : Function.Injective α)
    (hcount : n * (m + 1).choose 2 < (gsSupport D k).card) :
    ∃ Q : Polynomial (Polynomial F), Q ≠ 0 ∧
      (∀ i j : ℕ, (Q.coeff j).coeff i ≠ 0 → i + (k - 1) * j < D) ∧
      ∀ f : Polynomial F, f.natDegree ≤ k - 1 →
        D ≤ m * (Finset.univ.filter fun s : Fin n => f.eval (α s) = w s).card →
        (Polynomial.X - Polynomial.C f) ∣ Q := by
  obtain ⟨Q, hne, hwdeg, hvan⟩ := hasse_interpolation_exists_choose k D m n α w hcount
  refine ⟨Q, hne, hwdeg, fun f hfdeg hagree => ?_⟩
  set Af := Finset.univ.filter fun s : Fin n => f.eval (α s) = w s with hAf
  refine factor_of_order_agreement (m := m) hD (wdeg_natDegree_of_support hwdeg) hfdeg
    (A := Af.image α) ?_ ?_
  · rw [Finset.card_image_of_injective _ hinj]
    exact hagree
  · intro x hx i j hij
    rw [Finset.mem_image] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    rw [hAf, Finset.mem_filter] at hs
    rw [hs.2]
    exact hvan s i j hij

/-! ### 8. (d) Concrete instances over `ZMod 5`, multiplicity `m = 2` -/

instance primeFact_GSHasseMultiplicity_1 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

lemma gsSupport_card_four_two : (gsSupport 4 2).card = 10 := by
  rw [gsSupport_card]
  decide

lemma gsSupport_card_two_two : (gsSupport 2 2).card = 3 := by
  rw [gsSupport_card]
  decide

/-- **(d) Concrete order-2 interpolant over `ZMod 5`** (`k = 2`, `D = 4`, `m = 2`, `n = 2`
points on the parabola `w = α²`): since `2·3 = 6 < 10 = #gsSupport 4 2`, a nonzero `Q` of
`(1,1)`-weighted degree `< 4` vanishing to order `2` at both points exists — every hypothesis
of the front end is exhibited by a concrete inhabitant. -/
theorem gs_hasse_instance_ZMod5 :
    ∃ Q : Polynomial (Polynomial (ZMod 5)), Q ≠ 0 ∧
      (∀ i j : ℕ, (Q.coeff j).coeff i ≠ 0 → i + (2 - 1) * j < 4) ∧
      ∀ s : Fin 2, ∀ i j : ℕ, i + j < 2 →
        ((shift2 ((s.val : ZMod 5)) ((s.val : ZMod 5) ^ 2) Q).coeff j).coeff i = 0 := by
  exact hasse_interpolation_exists 2 4 2 2 (fun s => (s.val : ZMod 5))
    (fun s => (s.val : ZMod 5) ^ 2)
    (by rw [gsSupport_card_two_two, gsSupport_card_four_two]; norm_num)

/-- **(d') Concrete pipeline instance over `ZMod 5`**: with `m = 2` and the two points
`(0,0), (1,1)` on the line `w = α`, the assembled pipeline produces a nonzero `Q` with the
genuine factor `(Y - C X) ∣ Q` — the full multiplicity-2 chain fires end to end. -/
theorem gs_pipeline_instance_ZMod5 :
    ∃ Q : Polynomial (Polynomial (ZMod 5)), Q ≠ 0 ∧
      (Polynomial.X - Polynomial.C (Polynomial.X : Polynomial (ZMod 5))) ∣ Q := by
  have hinj : Function.Injective (fun s : Fin 2 => (s.val : ZMod 5)) := by decide
  obtain ⟨Q, hne, _, hfac⟩ := gs_decoder_pipeline (F := ZMod 5) 2 4 2 2 (by norm_num)
    (fun s => (s.val : ZMod 5)) (fun s => (s.val : ZMod 5)) hinj
    (by rw [gsSupport_card_four_two]; norm_num)
  refine ⟨Q, hne, hfac Polynomial.X (by simp) ?_⟩
  have hfilter : (Finset.univ.filter fun s : Fin 2 =>
      (Polynomial.X : Polynomial (ZMod 5)).eval ((s.val : ZMod 5)) = (s.val : ZMod 5))
      = Finset.univ := by
    rw [Finset.filter_eq_self]
    intro s _
    simp
  rw [hfilter]
  simp

end GSHasse

#print axioms GSHasse.hasse_interpolation_exists
#print axioms GSHasse.hasse_interpolation_exists_choose
#print axioms GSHasse.pow_X_sub_C_dvd_eval_of_hasseVanish
#print axioms GSHasse.factor_of_order_agreement
#print axioms GSHasse.gs_decoder_pipeline
#print axioms GSHasse.gs_hasse_instance_ZMod5
#print axioms GSHasse.gs_pipeline_instance_ZMod5
