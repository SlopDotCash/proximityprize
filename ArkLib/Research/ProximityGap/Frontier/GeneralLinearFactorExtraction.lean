/-
Copyright (c) 2026 Proximity Prize contributors. All rights reserved.
SPDX-License-Identifier: MIT OR Apache-2.0
-/
import ArkLib.Research.ProximityGap.Frontier.TerminalLinearComponent
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeSectionResultant
import ArkLib.Research.ProximityGap.Frontier.SecondPrimeCoordinateWeight

/-! # Arbitrary-degree value-linear factor extraction and affine head divisors

Generalizes `SecondPrimeLinearFactor.extraction_of_geometry` from hardcoded degree `34` to
arbitrary total `(Z, Y)`-degree `s ≥ 1`, and proves:
- the universal nonaffine value-linear cap `(r + 1) * s` whenever `4 * n ≤ r * (t - d)`,
  specializing immediately to the `17 * m` bound of `quarter-common-factor-degrees.md` (`r = 16`)
  and the `21 * m` bound of `half-sparse-gauss-window.md` (`r = 20`);
- the exact cutoff extraction criterion for `EighthRichHeadSafety`, `QuarterCoreWeightedJets`,
  and `TangentHeadWindows`;
- the monic affine head factor `Y - (A(X) + Z B(X))`, its irreducibility, total degree `1`,
  coordinate weight `d`, and divisibility of any surface vanishing on more than `s` points of the
  head (including pairwise coprimality of distinct heads to track residual degree and weight).
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.GeneralLinearFactorExtraction

open Finset Polynomial Code
open _root_.ProximityGap.TerminalLinearComponent
open ArkLib.ProximityGap.Frontier.HalfPredecessorBadEventRichPointBridge
open ArkLib.ProximityGap.Frontier.HalfPredecessorLineCoreGeometry
open ArkLib.ProximityGap.Frontier.HalfPredecessorSecantLines
open ArkLib.ProximityGap.Frontier.WeightedSylvesterDegree
open ArkLib.ProximityGap.Frontier.SecondPrimeCoordinateWeight
open scoped NNReal

section PureArithmetic

/-- Exact integer triple-agreement inequality from the incidence and miss-count bounds of
`TerminalLinearComponent.triple_incidence_bounds` at arbitrary total `(Z, Y)`-degree `s ≥ 1`
and sample size `L > s`. -/
theorem triple_agreement_of_product_gap {n d t s L c v : ℕ}
    (hsL : s < L) (hdt : d < t) (hc : c ≤ n)
    (hgap : (s * (L - s) + 3 * L * (s - 1)) * n < L * (L - s) * (t - d))
    (hinc : L * t ≤ (L - s) * c + s * n)
    (htrip : (L - s) * c ≤ (L - s) * v + 3 * ((s - 1) * c)) :
    d < v := by
  have h1 : L * t ≤ L * c + s * n := by
    have hsc : (L - s) * c ≤ L * c := Nat.mul_le_mul_right c (Nat.sub_le L s)
    omega
  have h2 : (L - s) * c ≤ (L - s) * v + 3 * ((s - 1) * n) := by
    have hcn : (s - 1) * c ≤ (s - 1) * n := Nat.mul_le_mul_left (s - 1) hc
    omega
  have h1' : (L - s) * (L * t) ≤ (L - s) * (L * c + s * n) := Nat.mul_le_mul_left (L - s) h1
  have h2' : L * ((L - s) * c) ≤ L * ((L - s) * v + 3 * ((s - 1) * n)) := Nat.mul_le_mul_left L h2
  have hcomb : L * (L - s) * t ≤ L * (L - s) * v + (s * (L - s) + 3 * L * (s - 1)) * n := by
    nlinarith only [h1', h2']
  have hsplit : L * (L - s) * d + L * (L - s) * (t - d) = L * (L - s) * t := by
    rw [← Nat.mul_add, Nat.add_sub_of_le hdt.le]
  have hmul : L * (L - s) * d < L * (L - s) * v := by omega
  have hpos : 0 < L * (L - s) := Nat.mul_pos (by omega) (by omega)
  exact Nat.lt_of_mul_lt_mul_left hmul

/-- Whenever `4 * n ≤ r * (t - d)`, sample size `L = (r + 1) * s + 1` strictly satisfies the
product gap for every total `(Z, Y)`-degree `s ≥ 1`. -/
theorem product_gap_of_ratio {n d t r s : ℕ}
    (hn : 0 < n) (hr : 0 < r) (hs : 1 ≤ s) (hdt : d < t)
    (hratio : 4 * n ≤ r * (t - d)) :
    let L := (r + 1) * s + 1
    (s * (L - s) + 3 * L * (s - 1)) * n < L * (L - s) * (t - d) := by
  intro L
  have hLs : L - s = r * s + 1 := by
    dsimp [L]
    rw [Nat.add_mul, one_mul]
    omega
  have hcoef : s * (L - s) + 3 * L * (s - 1) < 4 * L * s := by
    have hsub : 3 * L * (s - 1) + 3 * L = 3 * L * s := by
      have : s - 1 + 1 = s := by omega
      calc 3 * L * (s - 1) + 3 * L = 3 * L * (s - 1 + 1) := by ring
        _ = 3 * L * s := by rw [this]
    have hLpos : 0 < L := by dsimp [L]; omega
    have hsle : s ≤ L := by dsimp [L]; nlinarith
    have hmul : s * (L - s) + s * s = s * L := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hsle]
    nlinarith only [hsub, hmul, hLpos, hs]
  have hleft : (s * (L - s) + 3 * L * (s - 1)) * n < 4 * L * s * n :=
    Nat.mul_lt_mul_of_pos_right hcoef hn
  have hmid : 4 * L * s * n ≤ L * (r * s) * (t - d) := by
    calc 4 * L * s * n = L * s * (4 * n) := by ring
      _ ≤ L * s * (r * (t - d)) := Nat.mul_le_mul_left (L * s) hratio
      _ = L * (r * s) * (t - d) := by ring
  have hright : L * (r * s) * (t - d) < L * (L - s) * (t - d) := by
    rw [hLs]
    have hpos : 0 < L * (t - d) := Nat.mul_pos (by dsimp [L]; omega) (by omega)
    nlinarith only [hpos]
  exact hleft.trans_le (hmid.trans hright.le)

/-- Sufficient floor-division condition matching the parameter checks of `EighthRichHeadSafety`
and `QuarterCoreWeightedJets` (with safety slack `+ 4`). -/
theorem product_gap_of_floor {n d t s L : ℕ}
    (hs : 1 ≤ s) (hsL : s < L)
    (hfloor : d + s * n / L + 3 * (s * n / (L - s)) + 4 ≤ t) :
    (s * (L - s) + 3 * L * (s - 1)) * n < L * (L - s) * (t - d) := by
  have hLpos : 0 < L := by omega
  have hLspos : 0 < L - s := by omega
  have h1 : s * n < L * (s * n / L + 1) := Nat.lt_mul_div_succ (s * n) hLpos
  have h2 : s * n < (L - s) * (s * n / (L - s) + 1) := Nat.lt_mul_div_succ (s * n) hLspos
  have h3 : (s - 1) * n ≤ s * n := Nat.mul_le_mul_right n (Nat.sub_le s 1)
  have h1' : (L - s) * (s * n) < (L - s) * (L * (s * n / L + 1)) :=
    Nat.mul_lt_mul_of_pos_left h1 hLspos
  have h2' : 3 * L * ((s - 1) * n) < 3 * L * ((L - s) * (s * n / (L - s) + 1)) :=
    Nat.mul_lt_mul_of_pos_left (h3.trans_lt h2) (by omega)
  have hsum : (s * (L - s) + 3 * L * (s - 1)) * n <
      L * (L - s) * (s * n / L + 3 * (s * n / (L - s)) + 4) := by
    nlinarith only [h1', h2']
  have htd : s * n / L + 3 * (s * n / (L - s)) + 4 ≤ t - d := by omega
  exact hsum.trans_le (Nat.mul_le_mul_left (L * (L - s)) htd)

end PureArithmetic

section LinearFactorExtraction

variable {I F K : Type} [Fintype I] [Nonempty I] [DecidableEq I]
variable [Field F] [Fintype F] [DecidableEq F] [Field K]
variable {dom : I ↪ F} {δ : ℝ≥0} {u : WordStack F (Fin 2) I}

omit [Nonempty I] [Fintype F] in
/-- Arbitrary-degree generalization of `SecondPrimeLinearFactor.extraction_of_geometry`:
for any total `(Z, Y)`-degree `s ≥ 1` and sample size `L > s` satisfying the product gap,
every `L`-element subset with at most `s` off-identity agreements and at most `s - 1` on-identity
misses contains at least `s + 1` labels on a single base-field secant. -/
theorem extraction_of_geometry_general {d n t s L : ℕ}
    (fam : BadScalarRichPointFamily dom (d + 1) δ u)
    (hs : 1 ≤ s) (hsL : s < L) (hdt : d < t)
    (hn : Fintype.card I = n)
    (ht : t ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
    (hgap : (s * (L - s) + 3 * L * (s - 1)) * n < L * (L - s) * (t - d))
    (M : Finset F) (hM : M ⊆ fam.G) (hcard : M.card = L) (U : Finset I)
    (hoff : ∀ x ∉ U, (M.filter fun z => x ∈ fullAgreement dom (u 0) (u 1) z (fam.q z)).card ≤ s)
    (hon : ∀ x ∈ U, (M.filter fun z => x ∉ fullAgreement dom (u 0) (u 1) z (fam.q z)).card ≤ s - 1) :
    ∃ W ⊆ M, s + 1 ≤ W.card ∧ ∀ a ∈ W, ∀ b ∈ W, ∀ c ∈ W,
      d < (fullAgreement dom (u 0) (u 1) a (fam.q a) ∩
        fullAgreement dom (u 0) (u 1) b (fam.q b) ∩
        fullAgreement dom (u 0) (u 1) c (fam.q c)).card := by
  have hsm : s - 1 + 1 = s := by omega
  have hqm : L - s + (s - 1) + 1 = L := by omega
  obtain ⟨hU, W, hWM, hW, htr⟩ := triple_incidence_bounds M
    (fun z => fullAgreement dom (u 0) (u 1) z (fam.q z)) U (L - s) (s - 1) t
    (by omega) (by rw [hqm]; exact hcard)
    (fun z hz => ht.trans (fam.threshold_le z (hM hz)))
    (by simpa only [hsm] using hoff) hon
  rw [hqm, hsm, hn] at hU
  refine ⟨W, hWM, by omega, ?_⟩
  intro a ha b hb c hc
  have hUle : U.card ≤ n := hn ▸ Finset.card_le_univ U
  exact triple_agreement_of_product_gap hsL hdt hUle hgap hU (htr a ha b hb c hc)

/-- Any irreducible value-linear factor of total `(Z, Y)`-degree at most `s ≥ 1` carrying at least
`L` witnesses (where `L > s` satisfies the product gap) is an actual base-field affine head. -/
theorem linear_factor_is_head_of_gap {d n t s L : ℕ} (φ : F →+* K)
    (fam : BadScalarRichPointFamily dom (d + 1) δ u)
    (hs : 1 ≤ s) (hsL : s < L) (hdt : d < t)
    (hn : Fintype.card I = n)
    (ht : t ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
    (hgap : (s * (L - s) + 3 * L * (s - 1)) * n < L * (L - s) * (t - d))
    (f : K[X][X][X]) (hf : Irreducible f) (hdeg : f.natDegree = 1)
    (htot : TotalDegreeLe f s)
    (G : Finset F) (hG : G ⊆ fam.G) (hlarge : L ≤ G.card)
    (hcarries : ∀ z ∈ G, f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0) :
    ∃ l ∈ lineParameters fam, G ⊆ pointsOn fam l := by
  have hsm : s - 1 + 1 = s := by omega
  have hB : (f.coeff 0).natDegree ≤ (s - 1) + 1 := by
    rw [hsm]
    by_cases h0 : f.coeff 0 = 0
    · simp [h0]
    · have := htot 0 h0; omega
  have hA : (f.coeff 1).natDegree ≤ s - 1 := by
    by_cases h1 : f.coeff 1 = 0
    · simp [h1]
    · have := htot 1 h1; omega
  apply secant_of_agreement_selection (d := d) (m := s - 1) (N := L) φ fam f hf hdeg hB hA _
    G hG hlarge hcarries
  intro M S U hM hS hoff hon
  have hqm : L - s + (s - 1) + 1 = L := by omega
  obtain ⟨hU, W, hWM, hW, htr⟩ := triple_incidence_bounds M S U (L - s) (s - 1) t
    (by omega) (by rw [hqm]; exact hM) (fun z hz => ht.trans (hS z hz))
    (by simpa only [hsm] using hoff) hon
  rw [hqm, hsm, hn] at hU
  refine ⟨W, hWM, hW, ?_⟩
  intro a ha b hb c hc
  exact triple_agreement_of_product_gap hsL hdt (hn ▸ Finset.card_le_univ U) hgap hU
    (htr a ha b hb c hc)

/-- Ratio-form extraction: whenever `4 * n ≤ r * (t - d)`, any irreducible value-linear factor
of total `(Z, Y)`-degree at most `s ≥ 1` with more than `(r + 1) * s` labels is an actual
base-field affine head. Equivalently, any nonaffine value-linear factor carries at most
`(r + 1) * s` labels. -/
theorem linear_factor_is_head_or_card_le_of_ratio {d n t r s : ℕ} (φ : F →+* K)
    (fam : BadScalarRichPointFamily dom (d + 1) δ u)
    (hr : 0 < r) (hs : 1 ≤ s) (hdt : d < t)
    (hn : Fintype.card I = n)
    (ht : t ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
    (hratio : 4 * n ≤ r * (t - d))
    (f : K[X][X][X]) (hf : Irreducible f) (hdeg : f.natDegree = 1)
    (htot : TotalDegreeLe f s)
    (G : Finset F) (hG : G ⊆ fam.G)
    (hcarries : ∀ z ∈ G, f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0) :
    (∃ l ∈ lineParameters fam, G ⊆ pointsOn fam l) ∨ G.card ≤ (r + 1) * s := by
  by_cases hbig : (r + 1) * s < G.card
  · left
    have hnPos : 0 < n := hn ▸ Fintype.card_pos
    have hgap := product_gap_of_ratio hnPos hr hs hdt hratio
    exact linear_factor_is_head_of_gap φ fam hs (by nlinarith) hdt hn ht hgap
      f hf hdeg htot G hG hbig hcarries
  · right; omega

/-- Quarter-rate `17 * s` nonaffine value-linear cap (`4 * n ≤ 16 * (t - d)`), matching
`docs/research/proximity-gap/quarter-common-factor-degrees.md`. -/
theorem quarter_nonaffine_linear_cap {d n t s : ℕ} (φ : F →+* K)
    (fam : BadScalarRichPointFamily dom (d + 1) δ u)
    (hs : 1 ≤ s) (hdt : d < t) (hn : Fintype.card I = n)
    (ht : t ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
    (hratio : 4 * n ≤ 16 * (t - d))
    (f : K[X][X][X]) (hf : Irreducible f) (hdeg : f.natDegree = 1)
    (htot : TotalDegreeLe f s)
    (G : Finset F) (hG : G ⊆ fam.G)
    (hcarries : ∀ z ∈ G, f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0) :
    (∃ l ∈ lineParameters fam, G ⊆ pointsOn fam l) ∨ G.card ≤ 17 * s :=
  linear_factor_is_head_or_card_le_of_ratio (r := 16) φ fam (by decide) hs hdt hn ht hratio
    f hf hdeg htot G hG hcarries

/-- Half-rate `21 * s` nonaffine value-linear cap (`4 * n ≤ 20 * (t - d)`), matching
`docs/research/proximity-gap/half-sparse-gauss-window.md`. -/
theorem half_nonaffine_linear_cap {d n t s : ℕ} (φ : F →+* K)
    (fam : BadScalarRichPointFamily dom (d + 1) δ u)
    (hs : 1 ≤ s) (hdt : d < t) (hn : Fintype.card I = n)
    (ht : t ≤ ⌈(1 - δ) * (Fintype.card I : ℝ≥0)⌉₊)
    (hratio : 4 * n ≤ 20 * (t - d))
    (f : K[X][X][X]) (hf : Irreducible f) (hdeg : f.natDegree = 1)
    (htot : TotalDegreeLe f s)
    (G : Finset F) (hG : G ⊆ fam.G)
    (hcarries : ∀ z ∈ G, f.eval₂ (evalRingHom (C (φ z))) ((fam.q z).map φ) = 0) :
    (∃ l ∈ lineParameters fam, G ⊆ pointsOn fam l) ∨ G.card ≤ 21 * s :=
  linear_factor_is_head_or_card_le_of_ratio (r := 20) φ fam (by decide) hs hdt hn ht hratio
    f hf hdeg htot G hG hcarries

end LinearFactorExtraction

section AffineHeadDivisors

variable {F K : Type} [Field F] [Field K]

/-- The affine head polynomial `A(X) + Z · B(X)` over `K[X][Z]` associated to a base-field
line parameter `l = (A, B)`. -/
noncomputable def headPoly (φ : F →+* K) (l : LineParameter F) : Polynomial K[X] :=
  C (l.1.map φ) + Polynomial.X * C (l.2.map φ)

/-- The monic value-linear trivariate factor `Y - (A(X) + Z · B(X))` over `K[X][Z][Y]`. -/
noncomputable def headFactor (φ : F →+* K) (l : LineParameter F) : K[X][X][X] :=
  Polynomial.X - C (headPoly φ l)

theorem headPoly_natDegree_le (φ : F →+* K) (l : LineParameter F) :
    (headPoly φ l).natDegree ≤ 1 := by
  unfold headPoly
  apply (natDegree_add_le ..).trans (max_le (by simp) _)
  rw [mul_comm]
  exact (natDegree_C_mul_le ..).trans (le_of_eq natDegree_X)

theorem headPoly_eval (φ : F →+* K) (l : LineParameter F) (z : F) :
    (headPoly φ l).eval (C (φ z)) = (l.1 + C z * l.2).map φ := by
  simp [headPoly, mul_comm (l.2.map φ)]

theorem headFactor_monic (φ : F →+* K) (l : LineParameter F) :
    (headFactor φ l).Monic :=
  monic_X_sub_C _

theorem headFactor_natDegree (φ : F →+* K) (l : LineParameter F) :
    (headFactor φ l).natDegree = 1 :=
  natDegree_X_sub_C _

theorem headFactor_irreducible (φ : F →+* K) (l : LineParameter F) :
    Irreducible (headFactor φ l) :=
  irreducible_X_sub_C _

theorem headFactor_totalDegree (φ : F →+* K) (l : LineParameter F) :
    Bivariate.totalDegree (headFactor φ l) = 1 := by
  classical
  have h1 : (headFactor φ l).coeff 1 = 1 := by
    simp [headFactor]
  have h0 : ((headFactor φ l).coeff 0).natDegree ≤ 1 := by
    simpa [headFactor] using headPoly_natDegree_le φ l
  have hle : Bivariate.totalDegree (headFactor φ l) ≤ 1 := by
    unfold Bivariate.totalDegree
    apply Finset.sup_le
    intro j hj
    have hjle : j ≤ 1 := (le_natDegree_of_mem_supp j hj).trans_eq (headFactor_natDegree φ l)
    interval_cases j
    · simpa using h0
    · simp [h1]
  have hge : 1 ≤ Bivariate.totalDegree (headFactor φ l) := by
    have hmem : (1 : ℕ) ∈ (headFactor φ l).support := by
      simp [mem_support_iff, h1]
    have := Bivariate.coeff_totalDegree_le (headFactor φ l) hmem
    omega
  omega

theorem headFactor_weight_ge (φ : F →+* K) (l : LineParameter F) (d : ℕ) :
    d ≤ weight d (headFactor φ l) := by
  have h1 : (((headFactor φ l).coeff 1).coeff 0).coeff 0 ≠ 0 := by
    simp [headFactor]
  have h := coeff_weight_le d (headFactor φ l) h1
  omega

theorem headFactor_injective (φ : F →+* K) : Function.Injective (headFactor φ) := by
  intro l₁ l₂ heq
  have h0 := congrArg (fun p : K[X][X][X] => -(p.coeff 0)) heq
  simp only [headFactor, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, neg_neg] at h0
  have hc0 := congrArg (fun p : Polynomial K[X] => p.coeff 0) h0
  have hc1 := congrArg (fun p : Polynomial K[X] => p.coeff 1) h0
  simp only [headPoly, coeff_add, coeff_C_zero, coeff_X_mul_zero, add_zero,
    coeff_C_succ, coeff_X_mul, zero_add] at hc0 hc1
  exact Prod.ext (Polynomial.map_injective φ φ.injective hc0)
    (Polynomial.map_injective φ φ.injective hc1)

theorem headFactor_not_associated (φ : F →+* K) {l₁ l₂ : LineParameter F} (hne : l₁ ≠ l₂) :
    ¬ Associated (headFactor φ l₁) (headFactor φ l₂) := by
  intro hassoc
  exact hne (headFactor_injective φ
    (eq_of_monic_of_associated (headFactor_monic φ l₁) (headFactor_monic φ l₂) hassoc))

/-- If a surface `Q` of total `(Z, Y)`-degree at most `s` vanishes on more than `s` points of a
base-field affine head `l`, then the monic linear factor `headFactor φ l` divides `Q`. -/
theorem headFactor_dvd_of_many_points (φ : F →+* K) (Q : K[X][X][X]) {s : ℕ}
    (hQ : TotalDegreeLe Q s) (l : LineParameter F) (G : Finset F)
    (hlarge : s < G.card)
    (hroot : ∀ z ∈ G, Q.eval₂ (evalRingHom (C (φ z))) ((l.1 + C z * l.2).map φ) = 0) :
    headFactor φ l ∣ Q := by
  classical
  rw [headFactor, dvd_iff_isRoot, IsRoot.def]
  have hdeg : (Q.eval (headPoly φ l)).natDegree ≤ s := by
    rw [Q.as_sum_range_C_mul_X_pow, eval_finsetSum]
    apply natDegree_sum_le_of_forall_le
    intro j _
    rw [eval_mul, eval_C, eval_pow, eval_X]
    by_cases h : Q.coeff j = 0
    · simp [h]
    · have hpow : ((headPoly φ l) ^ j).natDegree ≤ j :=
        natDegree_pow_le.trans (by simpa [mul_comm] using Nat.mul_le_mul_left j (headPoly_natDegree_le φ l))
      exact natDegree_mul_le.trans ((Nat.add_le_add_left hpow _).trans (hQ j h))
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero (Q.eval (headPoly φ l))
    (f := fun z : G => C (φ (z : F)))
    (C_injective.comp (φ.injective.comp Subtype.val_injective))
  · intro z
    have hspec : Q.eval₂ (evalRingHom (C (φ z))) ((headPoly φ l).eval (C (φ z))) =
        (Q.eval (headPoly φ l)).eval (C (φ z)) := eval₂_at_apply (evalRingHom _) (headPoly φ l)
    rw [← hspec, headPoly_eval]
    exact hroot z z.property
  · simpa using hdeg.trans_lt hlarge

/-- Distinct affine head factors dividing a surface `Q` divide `Q` jointly as a product. -/
theorem prod_headFactor_dvd (φ : F →+* K) (Q : K[X][X][X]) (H : Finset (LineParameter F))
    (hdvd : ∀ l ∈ H, headFactor φ l ∣ Q) :
    (∏ l ∈ H, headFactor φ l) ∣ Q := by
  classical
  induction H using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have haDvd : headFactor φ a ∣ Q := hdvd a (Finset.mem_insert_self a s)
    have hsDvd : (∏ l ∈ s, headFactor φ l) ∣ Q :=
      ih (fun l hl => hdvd l (Finset.mem_insert_of_mem hl))
    have hprime : Prime (headFactor φ a) := (headFactor_irreducible φ a).prime
    obtain ⟨R, hR⟩ := hsDvd
    have hdvdProd : headFactor φ a ∣ (∏ l ∈ s, headFactor φ l) * R := hR ▸ haDvd
    rcases hprime.dvd_or_dvd hdvdProd with hbad | hR'
    · exfalso
      obtain ⟨b, hb, hab⟩ := (hprime.dvd_finsetProd_iff _).mp hbad
      have hassoc : Associated (headFactor φ a) (headFactor φ b) :=
        (headFactor_irreducible φ a).associated_of_dvd (headFactor_irreducible φ b) hab
      exact headFactor_not_associated φ (fun (heq : a = b) => ha (heq ▸ hb)) hassoc
    · obtain ⟨T, hT⟩ := hR'
      refine ⟨T, ?_⟩
      rw [hR, hT]
      ring

/-- Total `(Z, Y)`-degree, value degree, and `(1, 0, d)`-weight of a product of `j` distinct affine
head factors. -/
theorem prod_headFactor_degrees (φ : F →+* K) (H : Finset (LineParameter F)) (d : ℕ) :
    (∏ l ∈ H, headFactor φ l) ≠ 0 ∧
    (∏ l ∈ H, headFactor φ l).natDegree = H.card ∧
    Bivariate.totalDegree (∏ l ∈ H, headFactor φ l) = H.card ∧
    H.card * d ≤ weight d (∏ l ∈ H, headFactor φ l) := by
  classical
  induction H using Finset.induction_on with
  | empty =>
    refine ⟨by simp, by simp, ?_, by simp⟩
    apply Nat.eq_zero_of_le_zero
    unfold Bivariate.totalDegree
    apply Finset.sup_le
    intro j hj
    have hj0 : j = 0 := by
      by_contra hne
      exact (mem_support_iff.mp hj) (by simp [coeff_one, hne])
    subst hj0
    simp
  | @insert a s ha ih =>
    obtain ⟨hne, hdeg, htot, hwt⟩ := ih
    have haNe : headFactor φ a ≠ 0 := (headFactor_irreducible φ a).ne_zero
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    refine ⟨mul_ne_zero haNe hne, ?_, ?_, ?_⟩
    · rw [natDegree_mul haNe hne, headFactor_natDegree, hdeg]; omega
    · rw [Bivariate.totalDegree_mul haNe hne, headFactor_totalDegree, htot]; omega
    · rw [weight_mul d _ _ haNe hne]
      have h1 := headFactor_weight_ge φ a d
      nlinarith

/-- Extracting `j` distinct affine heads from a nonzero surface `Q` yields a cofactor `R` whose
value degree, total `(Z, Y)`-degree, and `(1, 0, d)`-weight drop by `j`, `j`, and at least `j * d`
respectively. -/
theorem quotient_by_heads (φ : F →+* K) (Q : K[X][X][X]) (hQ : Q ≠ 0)
    (H : Finset (LineParameter F)) (hdvd : ∀ l ∈ H, headFactor φ l ∣ Q) (d : ℕ) :
    ∃ R : K[X][X][X],
      Q = (∏ l ∈ H, headFactor φ l) * R ∧
      R ≠ 0 ∧
      H.card + R.natDegree = Q.natDegree ∧
      H.card + Bivariate.totalDegree R = Bivariate.totalDegree Q ∧
      H.card * d + weight d R ≤ weight d Q := by
  obtain ⟨R, hQR⟩ := prod_headFactor_dvd φ Q H hdvd
  obtain ⟨hPne, hPdeg, hPtot, hPwt⟩ := prod_headFactor_degrees φ H d
  have hRne : R ≠ 0 := right_ne_zero_of_mul (hQR ▸ hQ)
  refine ⟨R, hQR, hRne, ?_, ?_, ?_⟩
  · rw [hQR, natDegree_mul hPne hRne, hPdeg]
  · rw [hQR, Bivariate.totalDegree_mul hPne hRne, hPtot]
  · rw [hQR, weight_mul d _ _ hPne hRne]
    omega

/-- Any irreducible factor `f` of `Q` that is not associated to any head in `H` divides the
residual cofactor `R`. -/
theorem factor_dvd_quotient_by_heads (φ : F →+* K) (Q R : K[X][X][X])
    (H : Finset (LineParameter F)) (hQR : Q = (∏ l ∈ H, headFactor φ l) * R)
    (f : K[X][X][X]) (hf : Irreducible f) (hfQ : f ∣ Q)
    (hnotHead : ∀ l ∈ H, ¬ Associated f (headFactor φ l)) :
    f ∣ R := by
  have hprime : Prime f := hf.prime
  rcases hprime.dvd_or_dvd (hQR ▸ hfQ) with hbad | hR
  · exfalso
    obtain ⟨l, hl, hfl⟩ := (hprime.dvd_finsetProd_iff _).mp hbad
    exact hnotHead l hl (hf.associated_of_dvd (headFactor_irreducible φ l) hfl)
  · exact hR

/-- `TotalDegreeLe f (Bivariate.totalDegree f)` holds unconditionally for any trivariate surface. -/
theorem totalDegreeLe_self (f : K[X][X][X]) : TotalDegreeLe f (Bivariate.totalDegree f) := by
  classical
  intro j hj
  have h := Bivariate.coeff_totalDegree_le f (mem_support_iff.mpr hj)
  omega

/-- A positive-value-degree polynomial has total `(Z, Y)`-degree at least `1`. -/
theorem one_le_totalDegree_of_pos_natDegree {f : K[X][X][X]} (hpos : 0 < f.natDegree) :
    1 ≤ Bivariate.totalDegree f := by
  classical
  have hne : f ≠ 0 := fun h => by simp [h] at hpos
  have hmem : f.natDegree ∈ f.support := mem_support_iff.mpr (leadingCoeff_ne_zero.mpr hne)
  have h := Bivariate.coeff_totalDegree_le f hmem
  omega

end AffineHeadDivisors

#print axioms triple_agreement_of_product_gap
#print axioms product_gap_of_ratio
#print axioms product_gap_of_floor
#print axioms extraction_of_geometry_general
#print axioms linear_factor_is_head_of_gap
#print axioms linear_factor_is_head_or_card_le_of_ratio
#print axioms quarter_nonaffine_linear_cap
#print axioms half_nonaffine_linear_cap
#print axioms headFactor_dvd_of_many_points
#print axioms prod_headFactor_dvd
#print axioms quotient_by_heads
#print axioms factor_dvd_quotient_by_heads

end ArkLib.ProximityGap.Frontier.GeneralLinearFactorExtraction
