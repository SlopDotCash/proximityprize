/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
/-
Round 15 — the END-TO-END Sudan (multiplicity-1) list-size bound, self-contained over
Mathlib only (no ArkLib imports; the three round-14 pipeline bricks are re-proved inline).

PROVED here, end to end:
* `sudan_interpolation_exists` (front end, re-proved inline): for `n` points with
  `n < #gsSupport D k = Σ_{j<D} (D - (k-1)·j)` there is a NONZERO `Q ∈ F[X][Y]` whose
  monomials `X^i·Y^j` all satisfy `i + (k-1)·j < D`, vanishing at every point `(α s, w s)`.
* `factor_of_agreement` (root-order step, re-proved inline): such a `Q` plus a degree-`≤ k-1`
  polynomial `f` vanishing-compatible on `≥ D` distinct points forces `(Y - C f) ∣ Q`.
* `card_le_natDegreeY_of_sub_C_dvd` (Y-degree list cap, re-proved inline): distinct `Y`-roots
  of a nonzero `Q` over `RatFunc F` are at most `deg_Y Q`.
* `natDegreeY_le` (new glue): the weighted-degree bound forces `deg_Y Q ≤ (D-1)/(k-1)`.
* **`sudan_list_bound` (MAIN)**: for ANY field `F`, ANY `n` distinct evaluation points
  `α : Fin n → F`, ANY received word `w`, ANY `k ≥ 2`, `0 < D ≤ t` with
  `n < Σ_{j<D} (D - (k-1)·j)`: every finite set `L` of polynomials of degree `≤ k-1`, each
  agreeing with `w` on `≥ t` points, has `L.card ≤ (D-1)/(k-1)`.  This is the Table-1
  positive (Sudan) list bound, unconditional given the explicit arithmetic side conditions.
* `sudan_list_bound_ZMod13` (concrete instance): `F = ZMod 13`, `n = 12`, `k = 2`,
  `D = t = 5` (so `12 < 15 = Σ` and `t ≥ D`): every list of degree-`≤ 1` polynomials with
  `≥ 5` agreements has size `≤ 4`.  Agreement `5` is strictly below the unique-decoding
  threshold (`t ≥ 7` would be needed since `2t > n + k - 1 = 13`), so this is a genuine
  list-decoding radius, and `t² = 25 > n(k-1) = 12` (Johnson-side feasibility).
* `two_element_list_witness` (non-vacuity): an explicit received word over `ZMod 13` with an
  explicit TWO-element list `{X, 0}` each member agreeing on `≥ 5` of the 12 points — so the
  radius really is in the list (non-unique) regime and every hypothesis of the main theorem
  is exhibited by a concrete inhabitant.

NOT proved (honest scope): multiplicity `m ≥ 2` interpolation (Guruswami–Sudan proper),
hence NOT the full Johnson radius — the `m = 1` Sudan radius reached here is governed
exactly by the two arithmetic conditions `n < Σ_{j<D}(D-(k-1)j)` and `D ≤ t`
(asymptotically `t ≳ √(2(k-1)n)`, i.e. relative radius `1 - √(2ρ)`, weaker than Johnson's
`1 - √ρ`).  No claim is made past Johnson.  Also not proved: any tightness/optimality of
the `(D-1)/(k-1)` cap.
-/
import Mathlib

set_option maxHeartbeats 1000000

open Polynomial

namespace R15

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

/-- Monomial support of the Sudan interpolation space: pairs `(i, j)` with
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

lemma coeffPoly_evalEval (S : Finset (ℕ × ℕ)) (c' : ℕ × ℕ → F) (a b : F) :
    ((coeffPoly S c').eval (Polynomial.C b)).eval a
      = ∑ p ∈ S, c' p * (a ^ p.1 * b ^ p.2) := by
  unfold coeffPoly
  rw [Polynomial.eval_finset_sum, Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Polynomial.eval_monomial, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C]
  ring

/-! ### 4. The evaluation linear map and interpolation existence -/

/-- The linear map sending a coefficient vector supported on `S` to the values of the
associated bivariate polynomial at the `n` points `(α s, w s)`. -/
noncomputable def evalAtPoints (S : Finset (ℕ × ℕ)) {n : ℕ} (α w : Fin n → F) :
    (↥S → F) →ₗ[F] (Fin n → F) where
  toFun c s := ∑ p ∈ S.attach, c p * (α s ^ (p : ℕ × ℕ).1 * w s ^ (p : ℕ × ℕ).2)
  map_add' c d := by
    funext s
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    funext s
    simp [Finset.mul_sum, mul_assoc]

lemma evalAtPoints_apply (S : Finset (ℕ × ℕ)) {n : ℕ} (α w : Fin n → F)
    (c : ↥S → F) (s : Fin n) :
    evalAtPoints S α w c s
      = ∑ p ∈ S.attach, c p * (α s ^ (p : ℕ × ℕ).1 * w s ^ (p : ℕ × ℕ).2) := rfl

/-- **Sudan (multiplicity-1) interpolation existence.** -/
theorem sudan_interpolation_exists (k D n : ℕ) (α w : Fin n → F)
    (hcount : n < (gsSupport D k).card) :
    ∃ Q : Polynomial (Polynomial F), Q ≠ 0 ∧
      (∀ i j : ℕ, (Q.coeff j).coeff i ≠ 0 → i + (k - 1) * j < D) ∧
      ∀ s : Fin n, ((Q.eval (Polynomial.C (w s))).eval (α s)) = 0 := by
  have hrank : Module.finrank F (Fin n → F)
      < Module.finrank F (↥(gsSupport D k) → F) := by
    rw [Module.finrank_pi, Module.finrank_pi, Fintype.card_coe, Fintype.card_fin]
    exact hcount
  obtain ⟨c, hc0, hLc⟩ :=
    exists_ne_zero_map_eq_zero_of_finrank_lt (evalAtPoints (gsSupport D k) α w) hrank
  set c' : ℕ × ℕ → F := fun p => if h : p ∈ gsSupport D k then c ⟨p, h⟩ else 0 with hc'
  refine ⟨coeffPoly (gsSupport D k) c', ?_, ?_, ?_⟩
  · -- nonzero
    obtain ⟨q, hq⟩ : ∃ q : ↥(gsSupport D k), c q ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hc0 (funext hall)
    intro h0
    apply hq
    have h1 := coeffPoly_coeff (gsSupport D k) c' (q : ℕ × ℕ).1 (q : ℕ × ℕ).2
    rw [h0] at h1
    simp only [Polynomial.coeff_zero, Prod.mk.eta] at h1
    rw [if_pos q.2] at h1
    have h2 : c' (q : ℕ × ℕ) = c q := by
      rw [hc']
      exact dif_pos q.2
    rw [h2] at h1
    exact h1.symm
  · -- weighted-degree bound on every monomial
    intro i j hne
    rw [coeffPoly_coeff] at hne
    by_cases hmem : (i, j) ∈ gsSupport D k
    · exact gsSupport_weight_lt hmem
    · exact absurd (if_neg hmem) hne
  · -- vanishing at all n points
    intro s
    rw [coeffPoly_evalEval]
    have hL := congrFun hLc s
    rw [evalAtPoints_apply, Pi.zero_apply] at hL
    refine Eq.trans ?_ hL
    have hsum : ∑ p ∈ gsSupport D k, c' p * (α s ^ p.1 * w s ^ p.2)
        = ∑ p ∈ (gsSupport D k).attach,
            c' (p : ℕ × ℕ) * (α s ^ (p : ℕ × ℕ).1 * w s ^ (p : ℕ × ℕ).2) :=
      (Finset.sum_attach _ _).symm
    rw [hsum]
    refine Finset.sum_congr rfl fun p _ => ?_
    have h2 : c' (p : ℕ × ℕ) = c p := by
      rw [hc']
      exact dif_pos p.2
    rw [h2]

/-! ### 5. Root-order step: agreement ⟹ linear factor -/

/-- Weighted-degree transfer: the univariate restriction `Q(X, f(X))` has degree `< D`. -/
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

/-- **Root-order / factor step (multiplicity 1).** `≥ D` vanishing points of the degree-`< D`
univariate restriction force `(Y - C f) ∣ Q`. -/
theorem factor_of_agreement {Q : Polynomial (Polynomial F)} {f : Polynomial F} {k D : ℕ}
    (hD : 0 < D)
    (hwdeg : ∀ j, Q.coeff j ≠ 0 → (Q.coeff j).natDegree + j * (k - 1) < D)
    (hf : f.natDegree ≤ k - 1)
    {A : Finset F} (hA : D ≤ A.card)
    (hroot : ∀ a ∈ A, (Q.eval f).eval a = 0) :
    (X - C f) ∣ Q := by
  classical
  rw [dvd_iff_isRoot]
  by_contra hne
  have hne' : Q.eval f ≠ 0 := hne
  have hsub : A ⊆ (Q.eval f).roots.toFinset := by
    intro a ha
    rw [Multiset.mem_toFinset, mem_roots']
    exact ⟨hne', hroot a ha⟩
  have hcard : A.card ≤ (Q.eval f).natDegree := by
    calc A.card ≤ (Q.eval f).roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card (Q.eval f).roots := Multiset.toFinset_card_le _
      _ ≤ (Q.eval f).natDegree := card_roots' _
  have hlt : (Q.eval f).natDegree < D := natDegree_eval_lt hD hwdeg hf
  omega

/-! ### 6. Y-degree list cap -/

/-- **Y-degree list cap.** If `Q ≠ 0` in `(F[X])[Y]` and every `f ∈ S` gives a linear
factor `Y - C f` of `Q`, then `|S| ≤ deg_Y Q`. -/
theorem card_le_natDegreeY_of_sub_C_dvd
    (Q : Polynomial (Polynomial F)) (hQ : Q ≠ 0)
    (S : Finset (Polynomial F))
    (hdvd : ∀ f ∈ S, (X - C f) ∣ Q) :
    S.card ≤ Q.natDegree := by
  classical
  set φ : Polynomial F →+* RatFunc F := algebraMap (Polynomial F) (RatFunc F) with hφdef
  have hφ : Function.Injective φ := RatFunc.algebraMap_injective F
  set Q' : Polynomial (RatFunc F) := Q.map φ with hQ'def
  have hQ'ne : Q' ≠ 0 := by
    intro h
    exact hQ (Polynomial.map_injective φ hφ (by simpa [hQ'def] using h))
  have hroot : ∀ f ∈ S, φ f ∈ Q'.roots := by
    intro f hf
    have hdvd' : (X - C (φ f)) ∣ Q' := by
      have h1 := map_dvd (Polynomial.mapRingHom φ) (hdvd f hf)
      simpa [Polynomial.coe_mapRingHom, Polynomial.map_sub] using h1
    rw [Polynomial.mem_roots hQ'ne]
    exact Polynomial.dvd_iff_isRoot.mp hdvd'
  have hsub : S.image (fun f => φ f) ⊆ Q'.roots.toFinset := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨f, hf, rfl⟩
    exact Multiset.mem_toFinset.mpr (hroot f hf)
  calc S.card
      = (S.image (fun f => φ f)).card :=
        (Finset.card_image_of_injective S hφ).symm
    _ ≤ Q'.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card Q'.roots := Q'.roots.toFinset_card_le
    _ ≤ Q'.natDegree := Q'.card_roots'
    _ = Q.natDegree := Polynomial.natDegree_map_eq_of_injective hφ Q

/-! ### 7. New glue: evaluation bridge and the Y-degree numeric cap -/

/-- Expansion of the double evaluation `Q(a, f(a))` as a sum over the `Y`-support. -/
lemma eval_eval_eq_sum (Q : Polynomial (Polynomial F)) (f : Polynomial F) (a : F) :
    (Q.eval f).eval a = ∑ j ∈ Q.support, (Q.coeff j).eval a * f.eval a ^ j := by
  have h : Q.eval f = ∑ j ∈ Q.support, Q.coeff j * f ^ j := by
    rw [eval_eq_sum]; rfl
  rw [h, Polynomial.eval_finset_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_pow]

/-- The double evaluation `Q(a, f(a))` depends on `f` only through the value `f(a)`. -/
lemma evalEval_congr (Q : Polynomial (Polynomial F)) (f : Polynomial F) {a b : F}
    (h : f.eval a = b) :
    (Q.eval f).eval a = (Q.eval (Polynomial.C b)).eval a := by
  rw [eval_eval_eq_sum, eval_eval_eq_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_C, h]

/-- The per-monomial weighted-degree bound forces `deg_Y Q ≤ (D-1)/(k-1)` (for `k ≥ 2`),
since the leading `Y`-coefficient contributes a monomial with `(k-1)·deg_Y Q < D`. -/
lemma natDegreeY_le {Q : Polynomial (Polynomial F)} {k D : ℕ} (hk : 2 ≤ k) (hQ : Q ≠ 0)
    (hwdeg : ∀ i j : ℕ, (Q.coeff j).coeff i ≠ 0 → i + (k - 1) * j < D) :
    Q.natDegree ≤ (D - 1) / (k - 1) := by
  have hk1 : 0 < k - 1 := by omega
  have hlead : Q.coeff Q.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ
  have hi : (Q.coeff Q.natDegree).coeff (Q.coeff Q.natDegree).natDegree ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hlead
  have h := hwdeg _ _ hi
  have h1 : (k - 1) * Q.natDegree < D := lt_of_le_of_lt (Nat.le_add_left _ _) h
  have h2 : Q.natDegree * (k - 1) ≤ D - 1 := Nat.le_sub_one_of_lt (by rwa [Nat.mul_comm])
  exact (Nat.le_div_iff_mul_le hk1).mpr h2

/-! ### 8. MAIN: the end-to-end Sudan list bound -/

/-- **End-to-end Sudan (multiplicity-1) list bound.**  Let `F` be a field, `α : Fin n → F`
injective evaluation points, `w : Fin n → F` a received word, `k ≥ 2`, `0 < D ≤ t`, and
suppose `n < Σ_{j<D} (D - (k-1)·j)` (the interpolation count).  Then ANY finite set `L` of
polynomials of degree `≤ k-1`, each agreeing with `w` on at least `t` of the points (the
agreement set being supplied as a Finset of indices), satisfies `L.card ≤ (D-1)/(k-1)`.

Pipeline: interpolate a nonzero weighted-degree-`< D` polynomial `Q` vanishing at all
points; each listed `f` makes `Q(X, f(X))` vanish on `≥ t ≥ D` distinct field points while
having degree `< D`, so `(Y - C f) ∣ Q`; distinct `f` are distinct `Y`-roots over
`RatFunc F`, capped by `deg_Y Q ≤ (D-1)/(k-1)`. -/
theorem sudan_list_bound (k D t n : ℕ) (hk : 2 ≤ k) (hD : 0 < D)
    (α w : Fin n → F) (hα : Function.Injective α)
    (hcount : n < ∑ j ∈ Finset.range D, (D - (k - 1) * j))
    (hDt : D ≤ t)
    (L : Finset (Polynomial F))
    (hdeg : ∀ f ∈ L, f.natDegree ≤ k - 1)
    (hagree : ∀ f ∈ L, ∃ A : Finset (Fin n), t ≤ A.card ∧ ∀ i ∈ A, f.eval (α i) = w i) :
    L.card ≤ (D - 1) / (k - 1) := by
  classical
  obtain ⟨Q, hQ0, hwdeg_mono, hvanish⟩ :=
    sudan_interpolation_exists k D n α w (by rw [gsSupport_card]; exact hcount)
  -- per-coefficient weighted-degree bound
  have hwdeg : ∀ j, Q.coeff j ≠ 0 → (Q.coeff j).natDegree + j * (k - 1) < D := by
    intro j hj
    have hi : (Q.coeff j).coeff (Q.coeff j).natDegree ≠ 0 :=
      Polynomial.leadingCoeff_ne_zero.mpr hj
    have h := hwdeg_mono _ j hi
    rwa [Nat.mul_comm (k - 1) j] at h
  -- every listed polynomial yields a linear factor of Q
  have hfac : ∀ f ∈ L, (X - C f) ∣ Q := by
    intro f hf
    obtain ⟨A, hAcard, hAagree⟩ := hagree f hf
    have hcard : D ≤ (A.image α).card := by
      rw [Finset.card_image_of_injective _ hα]
      omega
    refine factor_of_agreement hD hwdeg (hdeg f hf) hcard ?_
    intro x hx
    obtain ⟨i, hiA, rfl⟩ := Finset.mem_image.mp hx
    rw [evalEval_congr Q f (hAagree i hiA)]
    exact hvanish i
  -- cap the list by deg_Y Q, then by (D-1)/(k-1)
  exact le_trans (card_le_natDegreeY_of_sub_C_dvd Q hQ0 L hfac)
    (natDegreeY_le hk hQ0 hwdeg_mono)

/-- Filter form (when `F` has decidable equality): the agreement hypothesis stated as a
cardinality of `{i | f(α i) = w i}`. -/
theorem sudan_list_bound_filter [DecidableEq F] (k D t n : ℕ) (hk : 2 ≤ k) (hD : 0 < D)
    (α w : Fin n → F) (hα : Function.Injective α)
    (hcount : n < ∑ j ∈ Finset.range D, (D - (k - 1) * j))
    (hDt : D ≤ t)
    (L : Finset (Polynomial F))
    (hdeg : ∀ f ∈ L, f.natDegree ≤ k - 1)
    (hagree : ∀ f ∈ L, t ≤ (Finset.univ.filter fun i => f.eval (α i) = w i).card) :
    L.card ≤ (D - 1) / (k - 1) :=
  sudan_list_bound k D t n hk hD α w hα hcount hDt L hdeg fun f hf =>
    ⟨Finset.univ.filter fun i => f.eval (α i) = w i, hagree f hf,
      fun i hi => (Finset.mem_filter.mp hi).2⟩

/-! ### 9. Concrete instantiation: `ZMod 13`, `n = 12`, `k = 2`, `D = t = 5` -/

instance primeFact_SudanListBound_1 : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- Injectivity of the evaluation points `0, 1, …, 11` in `ZMod 13`. -/
lemma alpha12_injective :
    Function.Injective (fun i : Fin 12 => ((i.val : ℕ) : ZMod 13)) := by
  intro i j h
  have h' : ((i.val : ℕ) : ZMod 13) = ((j.val : ℕ) : ZMod 13) := h
  have hi : ((i.val : ℕ) : ZMod 13).val = i.val :=
    ZMod.val_cast_of_lt (lt_trans i.isLt (by norm_num))
  have hj : ((j.val : ℕ) : ZMod 13).val = j.val :=
    ZMod.val_cast_of_lt (lt_trans j.isLt (by norm_num))
  exact Fin.ext (by rw [← hi, ← hj, h'])

/-- **Concrete Sudan instance.** Over `ZMod 13` with the 12 evaluation points `0,…,11`:
any list of polynomials of degree `≤ 1` each agreeing with an arbitrary received word on
`≥ 5` points has size `≤ 4`.  (Here `D = t = 5`, `12 < Σ_{j<5}(5-j) = 15`; agreement `5`
is strictly below the unique-decoding threshold `7`, so this is a genuine list radius.) -/
theorem sudan_list_bound_ZMod13
    (w : Fin 12 → ZMod 13) (L : Finset (Polynomial (ZMod 13)))
    (hdeg : ∀ f ∈ L, f.natDegree ≤ 1)
    (hagree : ∀ f ∈ L,
      5 ≤ (Finset.univ.filter fun i : Fin 12 =>
        f.eval ((i.val : ZMod 13)) = w i).card) :
    L.card ≤ 4 := by
  have h := sudan_list_bound_filter (F := ZMod 13) 2 5 5 12 (by norm_num) (by norm_num)
    (fun i : Fin 12 => ((i.val : ℕ) : ZMod 13)) w alpha12_injective (by decide)
    (le_refl 5) L hdeg hagree
  exact h

/-! ### 10. Non-vacuity: an explicit two-element list at this radius -/

/-- Explicit received word: agrees with `X` on indices `0,…,5` and with `0` on `6,…,11`
(and on `0`). -/
def wWit : Fin 12 → ZMod 13 := fun i => if i.val < 6 then ((i.val : ℕ) : ZMod 13) else 0

/-- **Non-vacuity / genuine list regime.**  For the explicit received word `wWit` over
`ZMod 13`, the explicit TWO-element list `{X, 0}` satisfies every hypothesis of
`sudan_list_bound_ZMod13` (degrees `≤ 1`, each member agreeing on `≥ 5` of the 12 points),
and the theorem fires to give the bound `≤ 4`.  In particular the chosen radius admits
non-unique decoding, and all hypotheses of the main theorem are concretely inhabited. -/
theorem two_element_list_witness :
    ∃ (w : Fin 12 → ZMod 13) (L : Finset (Polynomial (ZMod 13))),
      L.card = 2 ∧
      (∀ f ∈ L, f.natDegree ≤ 1) ∧
      (∀ f ∈ L,
        5 ≤ (Finset.univ.filter fun i : Fin 12 =>
          f.eval ((i.val : ZMod 13)) = w i).card) ∧
      L.card ≤ 4 := by
  have hdeg : ∀ f ∈ ({Polynomial.X, 0} : Finset (Polynomial (ZMod 13))),
      f.natDegree ≤ 1 := by
    intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · exact le_of_eq Polynomial.natDegree_X
    · rw [Finset.mem_singleton.mp hf, Polynomial.natDegree_zero]
      omega
  have hagree : ∀ f ∈ ({Polynomial.X, 0} : Finset (Polynomial (ZMod 13))),
      5 ≤ (Finset.univ.filter fun i : Fin 12 =>
        f.eval ((i.val : ZMod 13)) = wWit i).card := by
    intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · -- f = X agrees on indices 0,…,5; we exhibit five of them
      have hsub : ({0, 1, 2, 3, 4} : Finset (Fin 12)) ⊆
          Finset.univ.filter fun i : Fin 12 =>
            (Polynomial.X).eval ((i.val : ZMod 13)) = wWit i := by
        intro x hx
        fin_cases hx <;> simp [wWit]
      calc (5 : ℕ) = ({0, 1, 2, 3, 4} : Finset (Fin 12)).card := by decide
        _ ≤ _ := Finset.card_le_card hsub
    · -- f = 0 agrees on indices 6,…,11 (and 0); we exhibit five of them
      rw [Finset.mem_singleton.mp hf]
      have hsub : ({6, 7, 8, 9, 10} : Finset (Fin 12)) ⊆
          Finset.univ.filter fun i : Fin 12 =>
            (0 : Polynomial (ZMod 13)).eval ((i.val : ZMod 13)) = wWit i := by
        intro x hx
        fin_cases hx <;> simp [wWit]
      calc (5 : ℕ) = ({6, 7, 8, 9, 10} : Finset (Fin 12)).card := by decide
        _ ≤ _ := Finset.card_le_card hsub
  refine ⟨wWit, {Polynomial.X, 0}, ?_, hdeg, hagree,
    sudan_list_bound_ZMod13 wWit _ hdeg hagree⟩
  exact Finset.card_pair Polynomial.X_ne_zero

end R15

#print axioms R15.sudan_interpolation_exists
#print axioms R15.factor_of_agreement
#print axioms R15.card_le_natDegreeY_of_sub_C_dvd
#print axioms R15.natDegreeY_le
#print axioms R15.sudan_list_bound
#print axioms R15.sudan_list_bound_filter
#print axioms R15.sudan_list_bound_ZMod13
#print axioms R15.two_element_list_witness
