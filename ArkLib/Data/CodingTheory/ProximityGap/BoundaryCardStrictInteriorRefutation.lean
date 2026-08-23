/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.BoundaryCardResidualRefutation

/-!
# The strict-interior leaf of the boundary quantization split is also false

`BoundaryCardResidualRefutation` and `BoundaryCardResidualAffineLineRefutation` refute the bare
closed-boundary residual `ProximityGap.BoundaryCardResidual` at **square** Johnson endpoints
(`deg · n` a perfect square, `ZMod 5`, `deg = 1`).  The in-tree quantization split
(`ArkLib.BoundaryCardResidual`) reduces the **non-lattice** bulk of the boundary to the
strict-interior supply

* `BoundaryCardStrictInteriorFalseAsStated` — for every stack `u` and every strict sub-radius
  `δ' < δ` sharing the boundary's floor, a *nonempty* good set at `δ'` implies `jointAgreement`
  at `δ'`,

leaving that supply as a hypothesis.  **This file shows the supply is false as stated**, so the
quantization split bottoms out in *two* unsatisfiable nonemptiness leaves: the lattice leaf
(refuted in-tree) and the strict-interior leaf (refuted here).

## The witness (probed in `scripts/probes/probe_boundary_strict_interior.py`)

* coordinate domain `ι = Fin 4` and field `F = ZMod 5` (reused from the square refutation);
* Reed–Solomon degree `deg = 2`, so codewords are evaluations of *linear* polynomials;
* affine-line stack width `k = 1` with `uSq 0 = 0` and `uSq 1 = (domain ·)²`;
* boundary `δ = 1 − √(2/4)`; here `deg · n = 8` is **not** a perfect square, so the endpoint is
  genuinely non-lattice (`⌊δ·4⌋ = 1 < δ·4 ≈ 1.17`);
* strict sub-radius `δ' = 1/4 < δ` with the same floor `⌊δ'·4⌋ = 1`.

The parameter `z = 0` collapses the curve to the zero codeword, so the good set at `δ'` is
nonempty.  But `jointAgreement` at `δ'` needs an agreement set of size `≥ 4 − ⌊δ'·4⌋ = 3`, and
no linear polynomial agrees with `x ↦ x²` on three of the four points `{0,1,2,3} ⊆ ZMod 5`
(a quadratic with three roots), checked by kernel `decide`.

## Ground truth after this file

* **Refuted as stated**: `BoundaryCardResidual` at square endpoints (in-tree, `k ∈ {1, 2}`),
  `BoundaryCardResidual` at a *non-square* endpoint (`not_boundaryCardResidual_nonSquareEndpoint`
  here), and the strict-interior supply `BoundaryCardStrictInteriorFalseAsStated`
  (`not_boundaryCardStrictInteriorFalseAsStated` here).  Nonemptiness of the good set is *never* a
  sufficient boundary hypothesis, on or off the `1/n`-lattice.
* **Corrected statement**: the boundary obligation must carry the §5 *probability threshold* at a
  floor-matched strict radius — `Pr[good at δ'] > k · errorBound δ'` with `errorBound δ' > 0` —
  not bare nonemptiness.  The probe confirms the witness does not violate it
  (`Pr = 1/5 ≤ k·ε = 4/5`).
* **Proven piece**: `correlatedAgreementCurves_boundary_of_floorEq_strict` — the corrected route
  is *sufficient for the keystone consumer*: the closed-boundary
  `δ_ε_correlatedAgreementCurves` follows verbatim from the strict-interior
  `δ_ε_correlatedAgreementCurves` at any floor-matched `δ' ` with the **same** `ε`, because both
  the probability premise (via the good-set step function) and the `jointAgreement` conclusion
  (via the agreement-floor step function) are step functions of `⌊δ·n⌋`.  At non-lattice
  endpoints such a `δ'` always exists (`exists_lt_floor_eq_of_floor_lt`), so the honest boundary
  export is the strict theorem with the strict radius's `errorBound`, never with
  `errorBound (1 − √ρ) = 0`.
-/

namespace ArkLib

namespace BoundaryQuantizationCorrected

open ProximityGap Code NNReal Finset Function ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory LinearCode

/-- **The corrected boundary route: floor-matched transport of the full
`δ_ε_correlatedAgreementCurves` statement.**  If `δ'` and `δ` have the same distance floor
`⌊δ'·n⌋ = ⌊δ·n⌋`, then the curve correlated-agreement statement at `δ'` implies the one at `δ`
with the *same* error parameter `ε`: the probability premise transports because the
good-coefficient set is a step function of the floor, and the `jointAgreement` conclusion
transports because the agreement-set size bound is too.

Taking `δ = 1 − √ρ` (non-lattice) and `δ' < δ` floor-matched (always available off the lattice by
`ArkLib.BoundaryCardResidual.exists_lt_floor_eq_of_floor_lt`), this is the honest replacement for
the refuted nonemptiness boundary residuals: the closed-boundary keystone conclusion holds with
`ε = errorBound δ' > 0`, i.e. with the strict radius's genuine threshold rather than the vacuous
`errorBound (1 − √ρ) = 0`. -/
theorem correlatedAgreementCurves_boundary_of_floorEq_strict
    {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {k deg : ℕ} {domain : ι ↪ F} {δ δ' : ℝ≥0} {ε : ℝ≥0}
    (hfloor : Nat.floor (δ' * Fintype.card ι) = Nat.floor (δ * Fintype.card ι))
    (hCA : δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := (ReedSolomon.code domain deg : Set (ι → F))) (δ := δ') (ε := ε)) :
    δ_ε_correlatedAgreementCurves (k := k) (A := F) (F := F) (ι := ι)
      (C := (ReedSolomon.code domain deg : Set (ι → F))) (δ := δ) (ε := ε) := by
  classical
  intro u hprob
  have hPrδ := prob_close_curve_eq_card_goodCoeffsCurve_div_card
    (k := k) (deg := deg) (domain := domain) (δ := δ) u
  have hPrδ' := prob_close_curve_eq_card_goodCoeffsCurve_div_card
    (k := k) (deg := deg) (domain := domain) (δ := δ') u
  have hgood :
      RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ'
        = RS_goodCoeffsCurve (k := k) (deg := deg) (domain := domain) u δ :=
    ArkLib.BoundaryCardResidual.goodCoeffsCurve_eq_of_floor_eq (deg := deg)
      (domain := domain) u hfloor
  refine (ArkLib.BoundaryCardResidual.jointAgreement_iff_of_floor_eq
    (deg := deg) (domain := domain) u hfloor.symm).mpr (hCA u ?_)
  rw [hPrδ', hgood, ← hPrδ]
  exact hprob

end BoundaryQuantizationCorrected

namespace BoundaryCardStrictInteriorRefutation

open ArkLib ArkLib.BoundaryCardResidual ArkLib.BoundaryCardResidualRefutation
  ProximityGap Code
open scoped BigOperators NNReal ENNReal ProbabilityTheory LinearCode

private instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- Squared-domain stack: `u 0 = 0` and `u 1 = (domain ·)²`.  Against the degree-`2` (linear)
Reed–Solomon code, word `1` agrees with any codeword on at most two coordinates. -/
def uSq : WordStack F (Fin 2) I :=
  fun t i => if t = 1 then domain i ^ 2 else 0

/-- `deg · n = 2 · 4 = 8` is not a perfect square: this witness sits on the genuinely
**non-lattice** branch of the boundary dichotomy. -/
theorem not_isSquare_deg_mul_card : ¬ IsSquare (2 * Fintype.card I) := by
  rw [show 2 * Fintype.card I = 8 by norm_num [I]]
  rintro ⟨r, hr⟩
  rcases Nat.lt_or_ge r 3 with h | h
  · interval_cases r <;> omega
  · have h9 : 9 ≤ r * r := Nat.mul_le_mul h h
    omega

theorem sqrtRate_le_one : ReedSolomon.sqrtRate 2 domain ≤ 1 := by
  simp only [ReedSolomon.sqrtRate]
  have hrate : (LinearCode.rate (ReedSolomon.code domain 2) : ℝ≥0) ≤ 1 := by
    exact_mod_cast
      (DivergenceOfSets.reedSolomon_rate_le_one (deg := 2) (domain := domain))
  simpa using NNReal.sqrt_le_sqrt.mpr hrate

theorem sqrtRate_mul_card_eq_sqrt_eight :
    ReedSolomon.sqrtRate 2 domain * Fintype.card I = NNReal.sqrt 8 := by
  have hsq := ArkLib.BoundaryCardResidual.sqrtRate_mul_card_sq_eq_deg_mul_card
    (domain := domain) (deg := 2) (by norm_num [I])
  have h8 : ((2 * Fintype.card I : ℕ) : ℝ≥0) = 8 := by norm_num [I]
  rw [h8] at hsq
  rw [← hsq, NNReal.sqrt_sq]

theorem two_lt_sqrt_eight : (2 : ℝ≥0) < NNReal.sqrt 8 := by
  rw [← not_le, NNReal.sqrt_le_iff_le_sq]
  norm_num

theorem sqrt_eight_lt_three : NNReal.sqrt 8 < 3 := by
  rw [← not_le, NNReal.le_sqrt_iff_sq_le]
  norm_num

theorem sqrt_eight_le_four : NNReal.sqrt 8 ≤ 4 :=
  (sqrt_eight_lt_three.trans (by norm_num)).le

/-- The non-lattice boundary floor: `⌊(1 − √(2/4)) · 4⌋ = ⌊4 − √8⌋ = 1`. -/
theorem boundary_floor_eq_one :
    Nat.floor ((1 - ReedSolomon.sqrtRate 2 domain) * Fintype.card I) = 1 := by
  have hdistrib : (1 - ReedSolomon.sqrtRate 2 domain) * (Fintype.card I : ℝ≥0)
      = (Fintype.card I : ℝ≥0) - ReedSolomon.sqrtRate 2 domain * Fintype.card I := by
    rw [tsub_mul, one_mul]
  have hcard4 : (Fintype.card I : ℝ≥0) = 4 := by norm_num [I]
  rw [hdistrib, sqrtRate_mul_card_eq_sqrt_eight, hcard4,
    Nat.floor_eq_iff (zero_le _)]
  constructor
  · rw [le_tsub_iff_right sqrt_eight_le_four]
    have h : ((1 : ℕ) : ℝ≥0) + NNReal.sqrt 8 < 1 + 3 := by
      push_cast
      exact add_lt_add_of_le_of_lt le_rfl sqrt_eight_lt_three
    calc ((1 : ℕ) : ℝ≥0) + NNReal.sqrt 8 ≤ 1 + 3 := h.le
      _ = 4 := by norm_num
  · rw [tsub_lt_iff_right sqrt_eight_le_four]
    calc (4 : ℝ≥0) = 2 + 2 := by norm_num
      _ < ((1 : ℕ) : ℝ≥0) + 1 + NNReal.sqrt 8 := by
          rw [show ((1 : ℕ) : ℝ≥0) + 1 = 2 by norm_num]
          exact add_lt_add_of_le_of_lt le_rfl two_lt_sqrt_eight

/-- The matched strict sub-radius floor: `⌊(1/4) · 4⌋ = 1`. -/
theorem quarter_floor_eq_one :
    Nat.floor ((1 / 4 : ℝ≥0) * Fintype.card I) = 1 := by
  have h : ((1 / 4 : ℝ≥0)) * (Fintype.card I : ℝ≥0) = 1 := by
    norm_num [I]
  rw [h, Nat.floor_one]

theorem floor_quarter_eq_floor_boundary :
    Nat.floor ((1 / 4 : ℝ≥0) * Fintype.card I)
      = Nat.floor ((1 - ReedSolomon.sqrtRate 2 domain) * Fintype.card I) := by
  rw [quarter_floor_eq_one, boundary_floor_eq_one]

/-- `δ' = 1/4` lies strictly below the boundary `δ = 1 − √(1/2) ≈ 0.293`. -/
theorem quarter_lt_boundary :
    (1 / 4 : ℝ≥0) < 1 - ReedSolomon.sqrtRate 2 domain := by
  have hs : ReedSolomon.sqrtRate 2 domain < 3 / 4 := by
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ≥0) < 4)]
    have h4 : (4 : ℝ≥0) = (Fintype.card I : ℝ≥0) := by norm_num [I]
    rw [h4, sqrtRate_mul_card_eq_sqrt_eight]
    exact sqrt_eight_lt_three
  rw [lt_tsub_iff_right]
  calc (1 / 4 : ℝ≥0) + ReedSolomon.sqrtRate 2 domain
      < 1 / 4 + 3 / 4 := add_lt_add_of_le_of_lt le_rfl hs
    _ = 1 := by norm_num

/-- The boundary endpoint is genuinely non-lattice: the floor sits strictly below `δ · n`.
This places the witness on exactly the branch served by
`ArkLib.BoundaryCardResidual.boundaryCardResidual_of_not_lattice`. -/
theorem boundary_floor_lt :
    (Nat.floor ((1 - ReedSolomon.sqrtRate 2 domain) * Fintype.card I) : ℝ≥0)
      < (1 - ReedSolomon.sqrtRate 2 domain) * Fintype.card I :=
  ArkLib.BoundaryCardResidual.boundary_not_lattice_of_not_isSquare_deg_mul_card
    (domain := domain) rfl sqrtRate_le_one (by norm_num [I]) not_isSquare_deg_mul_card

/-- The good-coefficient set at the strict sub-radius `δ' = 1/4` is nonempty: the parameter
`z = 0` collapses the curve to `uSq 0 = 0`, the zero codeword. -/
theorem good_nonempty_quarter :
    0 < (RS_goodCoeffsCurve (k := 1) (deg := 2) (domain := domain) uSq
      (1 / 4 : ℝ≥0)).card := by
  classical
  refine Finset.card_pos.mpr ⟨0, ?_⟩
  have hzero_mem : (0 : I → F) ∈ (ReedSolomon.code domain 2 : Set (I → F)) :=
    (ReedSolomon.code domain 2).zero_mem
  have hrel :
      δᵣ((0 : I → F), (ReedSolomon.code domain 2 : Set (I → F))) ≤ (1 / 4 : ℝ≥0) := by
    rw [Code.relDistFromCode_eq_distFromCode_div,
      Code.distFromCode_of_mem (ReedSolomon.code domain 2 : Set (I → F)) hzero_mem]
    simp
  have hsum :
      (∑ t : Fin 2, (0 : F) ^ (t : ℕ) • uSq t) = (0 : I → F) := by
    funext i
    fin_cases i <;> simp [uSq]
  simpa [RS_goodCoeffsCurve, hsum] using hrel

/-- **Kernel-checked obstruction**: no linear polynomial `a·x + b` over `ZMod 5` agrees with
`x ↦ x²` on three of the four points `{0,1,2,3}` (a nonzero quadratic has at most two roots;
here checked by exhaustive `decide`). -/
theorem quad_no_three_fit :
    ∀ S : Finset I, 3 ≤ S.card → ∀ a b : F,
      ∃ x ∈ S, ((x : ℕ) : F) ^ 2 ≠ a * ((x : ℕ) : F) + b := by
  decide

/-- `jointAgreement` fails for `uSq` at the strict sub-radius `δ' = 1/4`: the floor forces a
three-coordinate agreement set, but word `1` is the squaring word, which no linear codeword
matches on three points. -/
theorem not_jointAgreement_quarter :
    ¬ jointAgreement (C := ReedSolomon.code domain 2)
      (δ := (1 / 4 : ℝ≥0)) (W := uSq) := by
  classical
  rintro ⟨S, hS, v, hv⟩
  have hS_three : 3 ≤ S.card := by
    rw [ge_iff_le, ← Code.relDist_floor_bound_iff_complement_bound
      (Fintype.card I) S.card (1 / 4 : ℝ≥0)] at hS
    rw [quarter_floor_eq_one] at hS
    norm_num [I] at hS
    exact hS
  have hmem : v 1 ∈ (ReedSolomon.code domain 2 : Set (I → F)) := (hv 1).1
  change v 1 ∈ ReedSolomon.code domain 2 at hmem
  rw [ReedSolomon.mem_code_iff_exists_polynomial_of_ne_zero] at hmem
  obtain ⟨p, hpdeg, hpeval⟩ := hmem
  have hplin : p = Polynomial.C (p.coeff 1) * Polynomial.X + Polynomial.C (p.coeff 0) :=
    Polynomial.eq_X_add_C_of_natDegree_le_one (by omega)
  have hagree : ∀ x ∈ S, ((x : ℕ) : F) ^ 2 = p.coeff 1 * ((x : ℕ) : F) + p.coeff 0 := by
    intro x hx
    have hx_filter := (Finset.mem_filter.mp ((hv 1).2 hx)).2
    have hx_sq : v 1 x = domain x ^ 2 := by simpa [uSq] using hx_filter
    have hx_eval : v 1 x = p.eval (domain x) := congrFun hpeval x
    have heval : p.eval (domain x) = p.coeff 1 * domain x + p.coeff 0 := by
      conv_lhs => rw [hplin]
      simp
    calc ((x : ℕ) : F) ^ 2 = v 1 x := hx_sq.symm
      _ = p.eval (domain x) := hx_eval
      _ = p.coeff 1 * ((x : ℕ) : F) + p.coeff 0 := heval
  obtain ⟨x, hxS, hne⟩ := quad_no_three_fit S hS_three (p.coeff 1) (p.coeff 0)
  exact hne (hagree x hxS)

/-- `jointAgreement` also fails at the boundary radius itself, by the same-floor step-function
transport. -/
theorem not_jointAgreement_boundary :
    ¬ jointAgreement (C := ReedSolomon.code domain 2)
      (δ := 1 - ReedSolomon.sqrtRate 2 domain) (W := uSq) := by
  intro h
  exact not_jointAgreement_quarter
    ((ArkLib.BoundaryCardResidual.jointAgreement_iff_of_floor_eq
      (deg := 2) (domain := domain) uSq
      floor_quarter_eq_floor_boundary.symm).mp h)

/-- The good set at the boundary radius is also nonempty (same floor, same good set). -/
theorem good_nonempty_boundary :
    0 < (RS_goodCoeffsCurve (k := 1) (deg := 2) (domain := domain) uSq
      (1 - ReedSolomon.sqrtRate 2 domain)).card := by
  rw [ArkLib.BoundaryCardResidual.goodCoeffsCurve_eq_of_floor_eq (deg := 2)
    (domain := domain) uSq floor_quarter_eq_floor_boundary.symm]
  exact good_nonempty_quarter

/-- **The strict-interior supply of the quantization split is false.**  The witness satisfies
every hypothesis of `BoundaryCardStrictInteriorFalseAsStated` at `δ' = 1/4 < δ = 1 − √(1/2)` with
matching floors and a nonempty good set, yet `jointAgreement` at `δ'` fails.  Together with the
in-tree square-endpoint refutations of `BoundaryCardLatticeResidual`, **both** leaves of the
boundary quantization split are unsatisfiable as bare nonemptiness statements. -/
theorem not_boundaryCardStrictInteriorFalseAsStated :
    ¬ ArkLib.BoundaryCardResidual.BoundaryCardStrictInteriorFalseAsStated
      (k := 1) (deg := 2) (domain := domain)
      (δ := 1 - ReedSolomon.sqrtRate 2 domain) := by
  intro h
  exact not_jointAgreement_quarter
    (h uSq (1 / 4) quarter_lt_boundary floor_quarter_eq_floor_boundary
      good_nonempty_quarter)

/-- **The bare closed-boundary residual is false at a non-square endpoint too.**  The in-tree
refutations live at square endpoints (`deg · n = 4`); this witness has `deg · n = 8` non-square,
so nonemptiness fails as a boundary hypothesis on *both* branches of the lattice dichotomy. -/
theorem not_boundaryCardResidual_nonSquareEndpoint :
    ¬ BoundaryCardResidual (k := 1) (deg := 2) (domain := domain)
      (δ := 1 - ReedSolomon.sqrtRate 2 domain) := by
  intro h
  exact not_jointAgreement_boundary (h Nat.one_pos uSq rfl good_nonempty_boundary)

end BoundaryCardStrictInteriorRefutation

end ArkLib

/-! ## Axiom audit -/
#print axioms
  ArkLib.BoundaryQuantizationCorrected.correlatedAgreementCurves_boundary_of_floorEq_strict
#print axioms ArkLib.BoundaryCardStrictInteriorRefutation.not_isSquare_deg_mul_card
#print axioms ArkLib.BoundaryCardStrictInteriorRefutation.boundary_floor_lt
#print axioms ArkLib.BoundaryCardStrictInteriorRefutation.good_nonempty_quarter
#print axioms ArkLib.BoundaryCardStrictInteriorRefutation.quad_no_three_fit
#print axioms ArkLib.BoundaryCardStrictInteriorRefutation.not_jointAgreement_quarter
#print axioms ArkLib.BoundaryCardStrictInteriorRefutation.not_jointAgreement_boundary
#print axioms
  ArkLib.BoundaryCardStrictInteriorRefutation.not_boundaryCardStrictInteriorFalseAsStated
#print axioms
  ArkLib.BoundaryCardStrictInteriorRefutation.not_boundaryCardResidual_nonSquareEndpoint
