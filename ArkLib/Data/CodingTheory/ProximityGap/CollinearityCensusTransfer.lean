/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.FoldedSumThreshold
import ArkLib.Data.CodingTheory.ProximityGap.PairSumRigidityModP

/-!
# The census is a characteristic-zero object: the full collinearity transfer

Campaign #357, the transfer half of the wide-circuit census program, supplied generically
for **all strata at once**. The pencil criterion (`dependent_iff_collinear`) reduces every
wide circuit of the window's collision matroid to the collinearity of three pair-points of
the configuration `Γ_n`; for the `μ_{2^m}` instantiation (points `g^{a_i}, g^{b_i}`) the
collinearity determinant expands into an explicit **12-term ±1-weighted root-of-unity
sum** (`detGamma_expand`). Composing with the generic two-layer engine
(`foldedSum_vanishing_iff_char0`) and the minimal-polynomial converse:

* `detGamma_modp_iff_foldedSum` — over `F_p` with `p > (2^(m−1)·12)^(2^(m−1))`: the
  collinearity equation holds iff the folded 12-term polynomial vanishes — a
  `p`-independent `ℤ[X]`-object.
* `foldedSum_eval_field` / `foldedSum_eq_zero_iff_eval_zero` — the engine's fold is
  faithful over **any** field with a primitive `2^m`-th root, and over a characteristic-zero
  field the folded polynomial vanishes **iff** the weighted sum does (minimal polynomial:
  `Φ_{2^m} = minpoly ℚ ζ` plus the degree bound kill the folded polynomial).
* `collinearity_transfer` — **the headline**: the collinearity verdict of every
  exponent-triple is identical over every `F_p` above the threshold and over every
  characteristic-zero field with a primitive `2^m`-th root.
* `collinearity_p_independent` — the prime-to-prime form: any two primes above the
  threshold agree on every collinearity verdict.

**What this does for the census program**: the wide-circuit census of `Γ_n` over `F_p` —
horizontal, vertical, *and the open slanted stratum* — is **pinned to characteristic zero**
above one explicit uniform threshold. The remaining open census work (the slanted 12-term
matching classification) is now a purely characteristic-zero problem with its mod-`p`
transfer pre-discharged; the vertical-stratum transfer (`PairSumRigidityModP`) is the
4-term special case of this statement.

## Honest scope

The threshold `(2^(m−1)·12)^(2^(m−1))` is the crude uniform resultant bound (the sharp
per-scale spectrum is the finite divisor set of the corresponding resultants, as in
`pair_sum_collision_dvd_resultant` — same recipe, not repeated here). Below the threshold
a characteristic-`p` surplus layer exists and is real: the probe lane's measured surplus
primes (e.g. `p = 17` at `n = 8, 16`) are exactly the interesting small-field exceptions.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References

* Issue #357 rounds 8–10 (the pencil law, the parabola stratification, the strata
  scoreboard); `FoldedSumThreshold.lean` (the generic engine);
  `MCADualPencilLaw.dependent_iff_collinear` (the consumer interface).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial Finset
open ArkLib.ProximityGap.WindowTwoLayer
open ArkLib.ProximityGap.PairSumRigidityModP
open ArkLib.ProximityGap.ResultantLiftLoop52

namespace ArkLib.ProximityGap.CollinearityCensusTransfer

variable {ι : Type*}

/-! ## The fold is faithful over any field -/

/-- **Field-generic fold faithfulness** (the engine's `foldedSum_eval`, freed from
`ZMod p`): evaluating the folded polynomial at a primitive `2^m`-th root of unity of any
field recovers the weighted sum. -/
theorem foldedSum_eval_field {L : Type*} [Field L] {m : ℕ} (hm : 1 ≤ m) {ζ : L}
    (hζ : IsPrimitiveRoot ζ (2 ^ m)) (S : Finset ι) (e : ι → ℕ) (w : ι → ℤ) :
    ((foldedSum m S e w).map (Int.castRingHom L)).eval ζ
      = ∑ x ∈ S, (w x : L) * ζ ^ (e x) := by
  classical
  have hhalf : ζ ^ (2 ^ (m - 1)) = -1 := pow_half_eq_neg_one_field hm hζ
  have hLHS : ((foldedSum m S e w).map (Int.castRingHom L)).eval ζ
      = ∑ t ∈ range (2 ^ (m - 1)), ((foldedCoeff m S e w t : L)) * ζ ^ t := by
    rw [foldedSum, Polynomial.map_sum, Polynomial.eval_finset_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Polynomial.map_mul, Polynomial.map_pow, map_C, map_X, eval_mul, eval_pow, eval_C,
      eval_X]
    norm_cast
  have hpow_mod : ∀ d : ℕ, ζ ^ d = ζ ^ (d % 2 ^ m) := by
    intro d
    conv_lhs => rw [← Nat.div_add_mod d (2 ^ m)]
    rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  have hfold : ∀ d : ℕ, 2 ^ (m - 1) ≤ d → ζ ^ d = -(ζ ^ (d - 2 ^ (m - 1))) := by
    intro d hge
    have : ζ ^ d = ζ ^ (d - 2 ^ (m - 1)) * ζ ^ (2 ^ (m - 1)) := by
      rw [← pow_add]
      congr 1
      omega
    rw [this, hhalf, mul_neg_one]
  have hRHS : ∑ x ∈ S, (w x : L) * ζ ^ (e x)
      = ∑ t ∈ range (2 ^ (m - 1)), ((foldedCoeff m S e w t : L)) * ζ ^ t := by
    have hmaps : ∀ x ∈ S,
        (if e x % 2 ^ m < 2 ^ (m - 1) then e x % 2 ^ m
         else e x % 2 ^ m - 2 ^ (m - 1)) ∈ range (2 ^ (m - 1)) := by
      intro x _
      by_cases hc : e x % 2 ^ m < 2 ^ (m - 1)
      · simpa [hc] using hc
      · have hlt : e x % 2 ^ m < 2 ^ m := Nat.mod_lt _ (by positivity)
        have hsplit : 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
          have h := pow_succ 2 (m - 1)
          rw [Nat.sub_add_cancel hm] at h
          omega
        simp only [hc, if_false, Finset.mem_range]
        omega
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun x => (w x : L) * ζ ^ (e x))]
    refine Finset.sum_congr rfl fun t ht => ?_
    have htlt : t < 2 ^ (m - 1) := Finset.mem_range.mp ht
    have hsplit : 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
      have h := pow_succ 2 (m - 1)
      rw [Nat.sub_add_cancel hm] at h
      omega
    have hfiber : S.filter (fun x =>
        (if e x % 2 ^ m < 2 ^ (m - 1) then e x % 2 ^ m
         else e x % 2 ^ m - 2 ^ (m - 1)) = t)
      = S.filter (fun x => e x % 2 ^ m = t)
        ∪ S.filter (fun x => e x % 2 ^ m = t + 2 ^ (m - 1)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hx, hfoldx⟩
        by_cases hc : e x % 2 ^ m < 2 ^ (m - 1)
        · left; exact ⟨hx, by simpa [hc] using hfoldx⟩
        · right
          refine ⟨hx, ?_⟩
          rw [if_neg hc] at hfoldx
          have hlt : e x % 2 ^ m < 2 ^ m := Nat.mod_lt _ (by positivity)
          omega
      · rintro (⟨hx, hr⟩ | ⟨hx, hr⟩)
        · exact ⟨hx, by simp [hr, htlt]⟩
        · refine ⟨hx, ?_⟩
          have hc : ¬ e x % 2 ^ m < 2 ^ (m - 1) := by omega
          rw [if_neg hc, hr]
          omega
    have hdisj : Disjoint (S.filter (fun x => e x % 2 ^ m = t))
        (S.filter (fun x => e x % 2 ^ m = t + 2 ^ (m - 1))) := by
      rw [Finset.disjoint_left]
      intro x h1 h2
      have e1 := (Finset.mem_filter.mp h1).2
      have e2 := (Finset.mem_filter.mp h2).2
      have hpos : 0 < 2 ^ (m - 1) := pow_pos (by norm_num) _
      omega
    rw [hfiber, Finset.sum_union hdisj]
    have hplus : ∑ x ∈ S.filter (fun x => e x % 2 ^ m = t), (w x : L) * ζ ^ (e x)
        = ((∑ x ∈ S.filter (fun x => e x % 2 ^ m = t), w x : ℤ) : L) * ζ ^ t := by
      have hterm : ∀ x ∈ S.filter (fun x => e x % 2 ^ m = t),
          (w x : L) * ζ ^ (e x) = (w x : L) * ζ ^ t := by
        intro x hx
        have hr := (Finset.mem_filter.mp hx).2
        rw [hpow_mod, hr]
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
      norm_cast
    have hminus : ∑ x ∈ S.filter (fun x => e x % 2 ^ m = t + 2 ^ (m - 1)),
          (w x : L) * ζ ^ (e x)
        = -(((∑ x ∈ S.filter (fun x => e x % 2 ^ m = t + 2 ^ (m - 1)), w x : ℤ) : L)
            * ζ ^ t) := by
      have hterm : ∀ x ∈ S.filter (fun x => e x % 2 ^ m = t + 2 ^ (m - 1)),
          (w x : L) * ζ ^ (e x) = -((w x : L) * ζ ^ t) := by
        intro x hx
        have hr := (Finset.mem_filter.mp hx).2
        have hsub : t + 2 ^ (m - 1) - 2 ^ (m - 1) = t := by omega
        rw [hpow_mod, hr, hfold _ (Nat.le_add_left _ _), hsub, mul_neg]
      rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, ← Finset.sum_mul]
      norm_cast
    rw [hplus, hminus, foldedCoeff]
    push_cast
    ring
  rw [hLHS, hRHS]

/-! ## The characteristic-zero converse: vanishing at a root kills the fold -/

/-- Over a characteristic-zero field, if the weighted sum vanishes at a primitive
`2^m`-th root, the folded polynomial vanishes identically: `Φ_{2^m}` is the minimal
polynomial of `ζ` over `ℚ` and the fold's degree is below `φ(2^m)`. -/
theorem foldedSum_eq_zero_of_eval_zero {L : Type*} [Field L] [CharZero L] {m : ℕ}
    (hm : 1 ≤ m) {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ m)) (S : Finset ι) (e : ι → ℕ)
    (w : ι → ℤ) (h0 : ∑ x ∈ S, (w x : L) * ζ ^ (e x) = 0) :
    foldedSum m S e w = 0 := by
  by_contra hR0
  have heval : ((foldedSum m S e w).map (Int.castRingHom L)).eval ζ = 0 := by
    rw [foldedSum_eval_field hm hζ S e w, h0]
  have hdvd : cyclotomic (2 ^ m) ℚ ∣ (foldedSum m S e w).map (Int.castRingHom ℚ) := by
    rw [cyclotomic_eq_minpoly_rat hζ (by positivity)]
    apply minpoly.dvd
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, Polynomial.map_map,
      show (algebraMap ℚ L).comp (Int.castRingHom ℚ) = Int.castRingHom L from
        RingHom.ext_int _ _]
    exact heval
  have hcop := diff_coprime_cyclotomic_rat hm _ (foldedSum_natDegree_lt m S e w) hR0
  rw [Polynomial.map_cyclotomic_int] at hcop
  have hunit : IsUnit (cyclotomic (2 ^ m) ℚ) := hcop.isUnit_of_dvd' hdvd dvd_rfl
  have hdeg0 := Polynomial.natDegree_eq_zero_of_isUnit hunit
  rw [natDegree_cyclotomic] at hdeg0
  have hpos : 0 < (2 ^ m).totient := Nat.totient_pos.mpr (by positivity)
  omega

/-- The two-sided characteristic-zero form: the folded polynomial vanishes **iff** the
weighted sum does, at any primitive `2^m`-th root of any characteristic-zero field. -/
theorem foldedSum_eq_zero_iff_eval_zero {L : Type*} [Field L] [CharZero L] {m : ℕ}
    (hm : 1 ≤ m) {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ m)) (S : Finset ι) (e : ι → ℕ)
    (w : ι → ℤ) :
    foldedSum m S e w = 0 ↔ ∑ x ∈ S, (w x : L) * ζ ^ (e x) = 0 := by
  constructor
  · intro h
    rw [← foldedSum_eval_field hm hζ S e w, h]
    simp
  · exact foldedSum_eq_zero_of_eval_zero hm hζ S e w

/-! ## The 12-term collinearity family -/

/-- The exponent table of the collinearity determinant: the six products `e_i·m_j` of the
expansion `det = e₂m₃ − e₂m₁ − e₁m₃ − e₃m₂ + e₁m₂ + e₃m₁`, two root-of-unity terms each
(`e_i = ζ^{a_i} + ζ^{b_i}`, `m_j = ζ^{a_j+b_j}`). -/
def censusExp (a₁ b₁ a₂ b₂ a₃ b₃ : ℕ) : Fin 12 → ℕ :=
  ![a₂ + (a₃ + b₃), b₂ + (a₃ + b₃),
    a₂ + (a₁ + b₁), b₂ + (a₁ + b₁),
    a₁ + (a₃ + b₃), b₁ + (a₃ + b₃),
    a₃ + (a₂ + b₂), b₃ + (a₂ + b₂),
    a₁ + (a₂ + b₂), b₁ + (a₂ + b₂),
    a₃ + (a₁ + b₁), b₃ + (a₁ + b₁)]

/-- The sign table of the collinearity determinant. -/
def censusWt : Fin 12 → ℤ := ![1, 1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1]

/-- The family's `ℓ¹` weight is `12`. -/
theorem l1Weight_censusWt : l1Weight (univ : Finset (Fin 12)) censusWt = 12 := by
  decide

/-- **The 12-term expansion of the collinearity determinant.** For pair-points
`(e_i, m_i) = (ζ^{a_i} + ζ^{b_i}, ζ^{a_i+b_i})` of `Γ_n`, the collinearity determinant
`(e₂−e₁)(m₃−m₁) − (m₂−m₁)(e₃−e₁)` is the weighted root-of-unity sum of the census
family. -/
theorem detGamma_expand {L : Type*} [CommRing L] (ζ : L) (a₁ b₁ a₂ b₂ a₃ b₃ : ℕ) :
    ∑ x : Fin 12, ((censusWt x : ℤ) : L) * ζ ^ (censusExp a₁ b₁ a₂ b₂ a₃ b₃ x)
      = (ζ ^ a₂ + ζ ^ b₂ - (ζ ^ a₁ + ζ ^ b₁)) * (ζ ^ (a₃ + b₃) - ζ ^ (a₁ + b₁))
        - (ζ ^ (a₂ + b₂) - ζ ^ (a₁ + b₁)) * (ζ ^ a₃ + ζ ^ b₃ - (ζ ^ a₁ + ζ ^ b₁)) := by
  simp only [censusExp, censusWt, Fin.sum_univ_succ, Finset.univ_eq_empty,
    Finset.sum_empty, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.succ_zero_eq_one]
  push_cast
  ring

/-! ## The transfer theorems -/

/-- **Mod-`p` collinearity is the characteristic-zero fold.** Over `F_p` with
`p > (2^(m−1)·12)^(2^(m−1))`: the pencil-criterion collinearity equation of an
exponent-triple holds iff the folded 12-term polynomial — a `p`-independent
`ℤ[X]`-object — vanishes. -/
theorem detGamma_modp_iff_foldedSum {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m)) (a₁ b₁ a₂ b₂ a₃ b₃ : ℕ)
    (hp : (2 ^ (m - 1) * 12) ^ 2 ^ (m - 1) < p) :
    ((g ^ a₂ + g ^ b₂ - (g ^ a₁ + g ^ b₁)) * (g ^ (a₃ + b₃) - g ^ (a₁ + b₁))
        = (g ^ (a₂ + b₂) - g ^ (a₁ + b₁)) * (g ^ a₃ + g ^ b₃ - (g ^ a₁ + g ^ b₁)))
      ↔ foldedSum m (univ : Finset (Fin 12)) (censusExp a₁ b₁ a₂ b₂ a₃ b₃)
          censusWt = 0 := by
  rw [← sub_eq_zero, ← detGamma_expand g a₁ b₁ a₂ b₂ a₃ b₃]
  exact foldedSum_vanishing_iff_char0 hm hg univ _ _
    (by rw [l1Weight_censusWt]; exact hp)

/-- The characteristic-zero companion: over any characteristic-zero field with a primitive
`2^m`-th root, the collinearity equation holds iff the same folded polynomial vanishes. -/
theorem detGamma_char0_iff_foldedSum {L : Type*} [Field L] [CharZero L] {m : ℕ}
    (hm : 1 ≤ m) {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ m)) (a₁ b₁ a₂ b₂ a₃ b₃ : ℕ) :
    ((ζ ^ a₂ + ζ ^ b₂ - (ζ ^ a₁ + ζ ^ b₁)) * (ζ ^ (a₃ + b₃) - ζ ^ (a₁ + b₁))
        = (ζ ^ (a₂ + b₂) - ζ ^ (a₁ + b₁)) * (ζ ^ a₃ + ζ ^ b₃ - (ζ ^ a₁ + ζ ^ b₁)))
      ↔ foldedSum m (univ : Finset (Fin 12)) (censusExp a₁ b₁ a₂ b₂ a₃ b₃)
          censusWt = 0 := by
  rw [← sub_eq_zero, ← detGamma_expand ζ a₁ b₁ a₂ b₂ a₃ b₃]
  exact (foldedSum_eq_zero_iff_eval_zero hm hζ univ _ _).symm

/-- **THE CENSUS IS A CHARACTERISTIC-ZERO OBJECT.** The collinearity verdict of every
exponent-triple of `Γ_n` is identical over every `F_p` above the explicit threshold and
over every characteristic-zero field with a primitive `2^m`-th root: the wide-circuit
census — horizontal, vertical, and slanted strata at once — transfers verbatim. -/
theorem collinearity_transfer {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m))
    {L : Type*} [Field L] [CharZero L] {ζ : L} (hζ : IsPrimitiveRoot ζ (2 ^ m))
    (a₁ b₁ a₂ b₂ a₃ b₃ : ℕ) (hp : (2 ^ (m - 1) * 12) ^ 2 ^ (m - 1) < p) :
    ((g ^ a₂ + g ^ b₂ - (g ^ a₁ + g ^ b₁)) * (g ^ (a₃ + b₃) - g ^ (a₁ + b₁))
        = (g ^ (a₂ + b₂) - g ^ (a₁ + b₁)) * (g ^ a₃ + g ^ b₃ - (g ^ a₁ + g ^ b₁)))
      ↔ ((ζ ^ a₂ + ζ ^ b₂ - (ζ ^ a₁ + ζ ^ b₁)) * (ζ ^ (a₃ + b₃) - ζ ^ (a₁ + b₁))
        = (ζ ^ (a₂ + b₂) - ζ ^ (a₁ + b₁)) * (ζ ^ a₃ + ζ ^ b₃ - (ζ ^ a₁ + ζ ^ b₁))) :=
  (detGamma_modp_iff_foldedSum hm hg a₁ b₁ a₂ b₂ a₃ b₃ hp).trans
    (detGamma_char0_iff_foldedSum hm hζ a₁ b₁ a₂ b₂ a₃ b₃).symm

/-- The prime-to-prime form: any two primes above the threshold agree on every
collinearity verdict of `Γ_n`. -/
theorem collinearity_p_independent {p q : ℕ} [Fact p.Prime] [Fact q.Prime] {m : ℕ}
    (hm : 1 ≤ m) {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m))
    {g' : ZMod q} (hg' : IsPrimitiveRoot g' (2 ^ m)) (a₁ b₁ a₂ b₂ a₃ b₃ : ℕ)
    (hp : (2 ^ (m - 1) * 12) ^ 2 ^ (m - 1) < p)
    (hq : (2 ^ (m - 1) * 12) ^ 2 ^ (m - 1) < q) :
    ((g ^ a₂ + g ^ b₂ - (g ^ a₁ + g ^ b₁)) * (g ^ (a₃ + b₃) - g ^ (a₁ + b₁))
        = (g ^ (a₂ + b₂) - g ^ (a₁ + b₁)) * (g ^ a₃ + g ^ b₃ - (g ^ a₁ + g ^ b₁)))
      ↔ ((g' ^ a₂ + g' ^ b₂ - (g' ^ a₁ + g' ^ b₁)) * (g' ^ (a₃ + b₃) - g' ^ (a₁ + b₁))
        = (g' ^ (a₂ + b₂) - g' ^ (a₁ + b₁))
            * (g' ^ a₃ + g' ^ b₃ - (g' ^ a₁ + g' ^ b₁))) :=
  (detGamma_modp_iff_foldedSum hm hg a₁ b₁ a₂ b₂ a₃ b₃ hp).trans
    (detGamma_modp_iff_foldedSum hm hg' a₁ b₁ a₂ b₂ a₃ b₃ hq).symm

/-! ## Source audit -/

#print axioms foldedSum_eval_field
#print axioms foldedSum_eq_zero_iff_eval_zero
#print axioms detGamma_expand
#print axioms detGamma_modp_iff_foldedSum
#print axioms collinearity_transfer
#print axioms collinearity_p_independent

end ArkLib.ProximityGap.CollinearityCensusTransfer
