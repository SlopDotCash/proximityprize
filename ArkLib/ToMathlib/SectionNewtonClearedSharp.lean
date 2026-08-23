/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.SectionNewtonCleared

/-!
# The sharp (quadratic) cleared Newton filtration (#304 — Finding F15 and its repair)

**Finding F15 (self-audit)**: the budget of `SectionNewtonCleared.gamma_cleared` is
**exponential in `t`** — `pow_cleared` bounds every factor of `(S t)^i` by the *worst*
coefficient budget (`i · (G + 2t·dξ)`), so the main recursion multiplies the full previous
budget by `d = deg Q` at every order.  At real Guruswami–Sudan parameters (`T ~ poly(n)`)
the count hypothesis `|M| > clearedBudget T` is then unsatisfiable: the unsharpened window
is honest but **vacuous in the genuine regime**.

**The repair — superadditivity of squares.**  The degree of a convolution product is the
*sum over the composition parts*, not `i` times the maximum:

* nonzero parts: `Σ α·(bⱼ² + bⱼ) ≤ α·(b² + b)` (squares are superadditive), with `2α·pq ≥ 2α`
  of slack whenever two parts are nonzero — absorbing the `ξ̄`-pad;
* zero parts contribute the seed degree `dv` each, at most `i ≤ d` times — tracked
  *additively* (`i·dv`), never multiplied into the running budget;
* **the truncation corner saves the degree exactly as it saves the exponent**: at
  `b = t + 1` all parts are `≤ t`, so two parts are nonzero, `pq ≥ t`, and
  `Σ ≤ α·(t² + t + 2)` — leaving `2αt`-grade slack for the new order's data.

Result: `gamma_cleared_sharp` — the `(A.4)` clearing at exponent `2t − 1` with the
**quadratic** budget `sharpBudget … t = dv + α·(t² + t)`, `α := DZ + d·dv + 3·dξ + 1`.
The window count `|M| > sharpBudget T` is polynomial in the GS parameters.

## References
* [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity Gaps for Reed–Solomon
  Codes*, §5 (Claim 5.8), Appendix A.2/A.4.
-/

set_option linter.style.longLine false

namespace ArkLib.SectionNewtonCleared

open PowerSeries ProximityPrize.HenselSeriesCoeff

variable {F : Type*} [Field F] (ξ : Polynomial F)

local notation "𝔞" => algebraMap (Polynomial F) (Localization.Away ξ)

/-- The sharp slope: the per-order corner slack absorbs the data degree, the zero-part
seeds, and the `ξ̄`-pads. -/
def sharpSlope (d dv DZ dξ : ℕ) : ℕ := DZ + d * dv + 3 * dξ + 1

/-- **The sharp budget**: quadratic in the order. -/
def sharpBudget (d dv DZ dξ : ℕ) (t : ℕ) : ℕ :=
  dv + sharpSlope d dv DZ dξ * (t ^ 2 + t)

theorem sharpBudget_mono (d dv DZ dξ : ℕ) : Monotone (sharpBudget d dv DZ dξ) := by
  intro a b hab
  unfold sharpBudget
  have h2 : a ^ 2 + a ≤ b ^ 2 + b :=
    Nat.add_le_add (Nat.pow_le_pow_left hab 2) hab
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ h2) _

variable (QA : Polynomial (PowerSeries (Localization.Away ξ))) (v : Polynomial F)

/-- **The sharp power filtration**: the degree of `coeff b ((S t)^i)` is governed by the
*sum over composition parts* — `α·(b² + b)` for the nonzero parts plus `i·dv'` for the zero
parts — never `i` times the worst budget. -/
theorem pow_cleared_sharp {t : ℕ} {α dv' : ℕ} (hα : ξ.natDegree ≤ α)
    (hγ : ∀ j ≤ t, Cleared ξ (coeff j (γ QA (𝔞 v))) (2 * j - 1)
      (dv' + α * (j ^ 2 + j))) :
    ∀ i, ∀ b ≤ t, Cleared ξ (coeff b ((S QA (𝔞 v) t) ^ i)) (2 * b - 1)
      (i * dv' + α * (b ^ 2 + b)) := by
  intro i
  induction i with
  | zero =>
      intro b hb
      rcases Nat.eq_zero_or_pos b with rfl | hb0
      · rw [pow_zero]
        have h1 : coeff 0 (1 : PowerSeries (Localization.Away ξ)) = 1 := by simp
        rw [h1]
        exact (Cleared.one _).mono (Nat.zero_le _)
      · rw [pow_zero]
        have h0 : coeff b (1 : PowerSeries (Localization.Away ξ)) = 0 := by
          rw [PowerSeries.coeff_one, if_neg (by omega)]
        rw [h0]
        exact Cleared.zero _ _
  | succ i ih =>
      intro b hb
      rw [pow_succ', PowerSeries.coeff_mul]
      apply Cleared.sum
      intro p hp
      have hpq : p.1 + p.2 = b := Finset.mem_antidiagonal.mp hp
      have hp1 : p.1 ≤ t := by omega
      have hSγ : coeff p.1 (S QA (𝔞 v) t) = coeff p.1 (γ QA (𝔞 v)) :=
        (coeff_γ_eq_S QA (𝔞 v) hp1).symm
      rw [hSγ]
      have hterm := (hγ p.1 hp1).mul (ih p.2 (by omega))
      have hexp : (2 * p.1 - 1) + (2 * p.2 - 1) ≤ 2 * b - 1 := by omega
      refine hterm.padTo hexp ?_
      have hsucc : (i + 1) * dv' = i * dv' + dv' := by ring
      rcases Nat.eq_zero_or_pos (2 * b - 1 - ((2 * p.1 - 1) + (2 * p.2 - 1))) with hz | hpos
      · -- exact exponent: one part is zero, squares-sum is exact or better
        rw [hz, zero_mul, add_zero]
        have hsq : α * (p.1 ^ 2 + p.1) + α * (p.2 ^ 2 + p.2) ≤ α * (b ^ 2 + b) := by
          have h : p.1 ^ 2 + p.1 + (p.2 ^ 2 + p.2) ≤ b ^ 2 + b := by nlinarith
          calc α * (p.1 ^ 2 + p.1) + α * (p.2 ^ 2 + p.2)
              = α * (p.1 ^ 2 + p.1 + (p.2 ^ 2 + p.2)) := by ring
            _ ≤ α * (b ^ 2 + b) := Nat.mul_le_mul_left _ h
        omega
      · -- padded: both parts nonzero, `2α·pq ≥ 2α ≥ dξ` of slack
        have hp1pos : 1 ≤ p.1 := by omega
        have hp2pos : 1 ≤ p.2 := by omega
        have hpad : (2 * b - 1 - ((2 * p.1 - 1) + (2 * p.2 - 1))) ≤ 1 := by omega
        have hpadcost : (2 * b - 1 - ((2 * p.1 - 1) + (2 * p.2 - 1))) * ξ.natDegree
            ≤ α := by
          calc (2 * b - 1 - ((2 * p.1 - 1) + (2 * p.2 - 1))) * ξ.natDegree
              ≤ 1 * ξ.natDegree := Nat.mul_le_mul_right _ hpad
            _ = ξ.natDegree := one_mul _
            _ ≤ α := hα

        have hsq : α * (p.1 ^ 2 + p.1) + α * (p.2 ^ 2 + p.2) + α ≤ α * (b ^ 2 + b) := by
          have h : p.1 ^ 2 + p.1 + (p.2 ^ 2 + p.2) + 1 ≤ b ^ 2 + b := by nlinarith
          calc α * (p.1 ^ 2 + p.1) + α * (p.2 ^ 2 + p.2) + α
              = α * (p.1 ^ 2 + p.1 + (p.2 ^ 2 + p.2) + 1) := by ring
            _ ≤ α * (b ^ 2 + b) := Nat.mul_le_mul_left _ h
        omega

/-- **The sharp top-corner filtration**: at `b = t + 1` all parts are `≤ t`, so two parts
are nonzero with `pq ≥ t`: the parts-sum is at most `α·(t² + t + 2)`, an order of slack
below the next budget. -/
theorem powTop_cleared_sharp {t : ℕ} {α dv' : ℕ} (hα : ξ.natDegree ≤ α)
    (hγ : ∀ j ≤ t, Cleared ξ (coeff j (γ QA (𝔞 v))) (2 * j - 1)
      (dv' + α * (j ^ 2 + j))) :
    ∀ i, Cleared ξ (coeff (t + 1) ((S QA (𝔞 v) t) ^ i)) (2 * t)
      (i * dv' + α * (t ^ 2 + t + 2)) := by
  intro i
  induction i with
  | zero =>
      rw [pow_zero]
      have h0 : coeff (t + 1) (1 : PowerSeries (Localization.Away ξ)) = 0 := by
        rw [PowerSeries.coeff_one, if_neg (by omega)]
      rw [h0]
      exact Cleared.zero _ _
  | succ i ih =>
      rw [pow_succ', PowerSeries.coeff_mul]
      apply Cleared.sum
      intro p hp
      have hpq : p.1 + p.2 = t + 1 := Finset.mem_antidiagonal.mp hp
      have hsucc : (i + 1) * dv' = i * dv' + dv' := by ring
      rcases Nat.lt_or_ge t p.1 with hp1 | hp1
      · have hzero : coeff p.1 (S QA (𝔞 v) t) = 0 := coeff_S_eq_zero_of_lt QA (𝔞 v) hp1
        rw [hzero, zero_mul]
        exact Cleared.zero _ _
      · have hSγ : coeff p.1 (S QA (𝔞 v) t) = coeff p.1 (γ QA (𝔞 v)) :=
          (coeff_γ_eq_S QA (𝔞 v) hp1).symm
        rw [hSγ]
        rcases Nat.lt_or_ge t p.2 with hp2 | hp2
        · -- the seed corner: `p.1 = 0`, recurse on the top coefficient
          have hp10 : p.1 = 0 := by omega
          have hp2eq : p.2 = t + 1 := by omega
          rw [hp10, hp2eq]
          have hterm := (hγ 0 (Nat.zero_le t)).mul ih
          have hexp : (2 * 0 - 1) + 2 * t = 2 * t := by omega
          rw [hexp] at hterm
          refine hterm.mono ?_
          have h00 : α * (0 ^ 2 + 0) = 0 := by ring_nf
          omega
        · -- two nonzero parts `≤ t`: `pq ≥ t`, exponent exact
          have hp1pos : 1 ≤ p.1 := by omega
          have hp2pos : 1 ≤ p.2 := by omega
          have hterm := (hγ p.1 hp1).mul (pow_cleared_sharp ξ QA v hα hγ i p.2 hp2)
          have hexp : (2 * p.1 - 1) + (2 * p.2 - 1) = 2 * t := by omega
          rw [hexp] at hterm
          refine hterm.mono ?_
          have hsq : α * (p.1 ^ 2 + p.1) + α * (p.2 ^ 2 + p.2)
              ≤ α * (t ^ 2 + t + 2) := by
            have h : p.1 ^ 2 + p.1 + (p.2 ^ 2 + p.2) ≤ t ^ 2 + t + 2 := by nlinarith
            calc α * (p.1 ^ 2 + p.1) + α * (p.2 ^ 2 + p.2)
                = α * (p.1 ^ 2 + p.1 + (p.2 ^ 2 + p.2)) := by ring
              _ ≤ α * (t ^ 2 + t + 2) := Nat.mul_le_mul_left _ h
          omega

/-- **THE SHARP CLEARED FILTRATION** (the F15 repair): the `(A.4)` clearing at exponent
`2t − 1` with the **quadratic** budget `dv + (DZ + d·dv + 3·dξ + 1)·(t² + t)`. -/
theorem gamma_cleared_sharp {DZ : ℕ}
    (hQdeg : ∀ i j, ∃ q : Polynomial F, q.natDegree ≤ DZ ∧ 𝔞 q = coeff j (QA.coeff i))
    (hresp : Polynomial.eval (𝔞 v) (Polynomial.derivative (Q₀ QA)) = 𝔞 ξ) :
    ∀ t, Cleared ξ (coeff t (γ QA (𝔞 v))) (2 * t - 1)
      (sharpBudget QA.natDegree v.natDegree DZ ξ.natDegree t) := by
  have hαξ : ξ.natDegree
      ≤ sharpSlope QA.natDegree v.natDegree DZ ξ.natDegree := by
    unfold sharpSlope
    omega
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    cases t with
    | zero =>
        have h0 : coeff 0 (γ QA (𝔞 v)) = 𝔞 v := by
          rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_γ]
        rw [h0]
        exact (Cleared.of_algebraMap v).mono (by unfold sharpBudget; omega)
    | succ t =>
        have hγ : ∀ j ≤ t, Cleared ξ (coeff j (γ QA (𝔞 v))) (2 * j - 1)
            (v.natDegree
              + sharpSlope QA.natDegree v.natDegree DZ ξ.natDegree * (j ^ 2 + j)) :=
          fun j hj => (ih j (by omega)).mono (le_of_eq (by unfold sharpBudget; rfl))
        rcases Nat.eq_zero_or_pos t with rfl | ht1
        · -- the base order: the truncation corner is literally zero
          have hrec := coeff_γ_succ_eq QA (𝔞 v) 0
          rw [hresp] at hrec
          rw [hrec, neg_mul, show 2 * (0 + 1) - 1 = 0 + 1 from by omega]
          have hsum0 : Cleared ξ (coeff (0 + 1) (Polynomial.eval (S QA (𝔞 v) 0) QA)) 0
              (DZ + QA.natDegree * v.natDegree) := by
            rw [coeff_eval_eq_sum_range]
            apply Cleared.sum
            intro i hi
            have hile : i ≤ QA.natDegree := by
              have := Finset.mem_range.mp hi
              omega
            rw [PowerSeries.coeff_mul]
            apply Cleared.sum
            intro p hp
            have hpq : p.1 + p.2 = 0 + 1 := Finset.mem_antidiagonal.mp hp
            rcases Nat.eq_zero_or_pos p.2 with hp20 | hp2pos
            · -- the data term against the constant seed power
              have hp11 : p.1 = 1 := by omega
              obtain ⟨q, hqdeg, hqmap⟩ := hQdeg i p.1
              have hcoeffQ : Cleared ξ (coeff p.1 (QA.coeff i)) 0 DZ := by
                rw [← hqmap]
                exact (Cleared.of_algebraMap q).mono hqdeg
              have hS0 : coeff p.2 ((S QA (𝔞 v) 0) ^ i) = 𝔞 (v ^ i) := by
                rw [hp20, coeff_zero_eq_constantCoeff_apply, map_pow]
                have hc : constantCoeff (S QA (𝔞 v) 0) = 𝔞 v := by
                  rw [S, PowerSeries.constantCoeff_C]
                rw [hc, map_pow]
              rw [hS0]
              have hpow : Cleared ξ (𝔞 (v ^ i)) 0 (QA.natDegree * v.natDegree) :=
                (Cleared.of_algebraMap (v ^ i)).mono
                  (Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_right _ hile))
              have := hcoeffQ.mul hpow
              simpa using this
            · -- the truncation corner at the base order is zero
              have hp21 : p.2 = 1 := by omega
              have hS1 : coeff p.2 ((S QA (𝔞 v) 0) ^ i) = 0 := by
                rw [hp21, S, ← map_pow, PowerSeries.coeff_C, if_neg (by omega)]
              rw [hS1, mul_zero]
              exact Cleared.zero _ _
          have hfinal := (hsum0.inverse_xi_mul).neg
          refine hfinal.mono ?_
          unfold sharpBudget sharpSlope
          nlinarith [Nat.zero_le (v.natDegree), Nat.zero_le DZ]
        -- the inner sum clears at `2t` with the corner budget
        have hsum : Cleared ξ (coeff (t + 1) (Polynomial.eval (S QA (𝔞 v) t) QA)) (2 * t)
            (DZ + (QA.natDegree * v.natDegree
              + sharpSlope QA.natDegree v.natDegree DZ ξ.natDegree * (t ^ 2 + t + 2))
              + (2 * t + 1) * ξ.natDegree) := by
          rw [coeff_eval_eq_sum_range]
          apply Cleared.sum
          intro i hi
          have hile : i ≤ QA.natDegree := by
            have := Finset.mem_range.mp hi
            omega
          rw [PowerSeries.coeff_mul]
          apply Cleared.sum
          intro p hp
          have hpq : p.1 + p.2 = t + 1 := Finset.mem_antidiagonal.mp hp
          obtain ⟨q, hqdeg, hqmap⟩ := hQdeg i p.1
          have hcoeffQ : Cleared ξ (coeff p.1 (QA.coeff i)) 0 DZ := by
            rw [← hqmap]
            exact (Cleared.of_algebraMap q).mono hqdeg
          have hidv : i * v.natDegree ≤ QA.natDegree * v.natDegree :=
            Nat.mul_le_mul_right _ hile
          rcases Nat.lt_or_ge t p.2 with hp2 | hp2
          · -- top corner
            have hp2eq : p.2 = t + 1 := by omega
            rw [hp2eq]
            have hterm := hcoeffQ.mul (powTop_cleared_sharp ξ QA v hαξ hγ i)
            have hexp : 0 + 2 * t = 2 * t := by omega
            rw [hexp] at hterm
            refine hterm.mono ?_
            omega
          · -- generic coefficient, padded
            have hterm := hcoeffQ.mul (pow_cleared_sharp ξ QA v hαξ hγ i p.2 hp2)
            have hexp : 0 + (2 * p.2 - 1) ≤ 2 * t := by omega
            refine hterm.padTo hexp ?_
            have hsq : sharpSlope QA.natDegree v.natDegree DZ ξ.natDegree * (p.2 ^ 2 + p.2)
                ≤ sharpSlope QA.natDegree v.natDegree DZ ξ.natDegree
                  * (t ^ 2 + t + 2) :=
              Nat.mul_le_mul_left _ (by nlinarith)
            have hpadcost : (2 * t - (0 + (2 * p.2 - 1))) * ξ.natDegree
                ≤ (2 * t + 1) * ξ.natDegree :=
              Nat.mul_le_mul_right _ (by omega)
            omega
        have hrec := coeff_γ_succ_eq QA (𝔞 v) t
        rw [hresp] at hrec
        rw [hrec, neg_mul, show 2 * (t + 1) - 1 = 2 * t + 1 from by omega]
        refine ((hsum.inverse_xi_mul).neg).mono ?_
        -- the per-order slack `α·(2t + 2) − 2α ≥ …` absorbs data, seeds, pads
        unfold sharpBudget
        have hexpand : sharpSlope QA.natDegree v.natDegree DZ ξ.natDegree
              * ((t + 1) ^ 2 + (t + 1))
            = sharpSlope QA.natDegree v.natDegree DZ ξ.natDegree * (t ^ 2 + t + 2)
              + sharpSlope QA.natDegree v.natDegree DZ ξ.natDegree * (2 * t) := by ring
        have hslack : DZ + QA.natDegree * v.natDegree + (2 * t + 1) * ξ.natDegree
            ≤ v.natDegree
              + sharpSlope QA.natDegree v.natDegree DZ ξ.natDegree * (2 * t) := by
          have hα3 : 3 * ξ.natDegree + DZ + QA.natDegree * v.natDegree + 1
              ≤ sharpSlope QA.natDegree v.natDegree DZ ξ.natDegree := by
            unfold sharpSlope
            omega
          have hkey : (DZ + QA.natDegree * v.natDegree + (2 * t + 1) * ξ.natDegree)
              ≤ (3 * ξ.natDegree + DZ + QA.natDegree * v.natDegree + 1) * (2 * t) := by
            have hsplit : (3 * ξ.natDegree + DZ + QA.natDegree * v.natDegree + 1) * (2 * t)
                = 3 * ξ.natDegree * (2 * t)
                  + (DZ + QA.natDegree * v.natDegree + 1) * (2 * t) := by ring
            have h6 : (2 * t + 1) * ξ.natDegree ≤ 3 * ξ.natDegree * (2 * t) := by
              have h61 : 2 * t + 1 ≤ 3 * (2 * t) := by omega
              calc (2 * t + 1) * ξ.natDegree ≤ (3 * (2 * t)) * ξ.natDegree :=
                    Nat.mul_le_mul_right _ h61
                _ = 3 * ξ.natDegree * (2 * t) := by ring
            have h7 : DZ + QA.natDegree * v.natDegree
                ≤ (DZ + QA.natDegree * v.natDegree + 1) * (2 * t) := by
              have h2t : 1 ≤ 2 * t := by omega
              calc DZ + QA.natDegree * v.natDegree
                  ≤ (DZ + QA.natDegree * v.natDegree + 1) * 1 := by omega
                _ ≤ (DZ + QA.natDegree * v.natDegree + 1) * (2 * t) :=
                    Nat.mul_le_mul_left _ h2t
            omega
          calc DZ + QA.natDegree * v.natDegree + (2 * t + 1) * ξ.natDegree
              ≤ (3 * ξ.natDegree + DZ + QA.natDegree * v.natDegree + 1) * (2 * t) := hkey
            _ ≤ sharpSlope QA.natDegree v.natDegree DZ ξ.natDegree * (2 * t) :=
              Nat.mul_le_mul_right _ hα3
            _ ≤ v.natDegree
                + sharpSlope QA.natDegree v.natDegree DZ ξ.natDegree * (2 * t) :=
              Nat.le_add_left _ _
        omega

/-- **The sharp witness pack**. -/
theorem exists_numerator_sharp {DZ : ℕ}
    (hQdeg : ∀ i j, ∃ q : Polynomial F, q.natDegree ≤ DZ ∧ 𝔞 q = coeff j (QA.coeff i))
    (hresp : Polynomial.eval (𝔞 v) (Polynomial.derivative (Q₀ QA)) = 𝔞 ξ) (t : ℕ) :
    ∃ N : Polynomial F,
      N.natDegree ≤ sharpBudget QA.natDegree v.natDegree DZ ξ.natDegree t ∧
      𝔞 N = (𝔞 ξ) ^ (2 * t - 1) * coeff t (γ QA (𝔞 v)) ∧
      (N = 0 → coeff t (γ QA (𝔞 v)) = 0) := by
  obtain ⟨N, hdeg, hmap⟩ := gamma_cleared_sharp ξ QA v hQdeg hresp t
  exact ⟨N, hdeg, hmap, fun h0 => eq_zero_of_cleared_witness ξ hmap h0⟩

/-- **The sharp window exit** — `coeff_gamma_eq_zero_of_eval_vanish` at the quadratic
budget. -/
theorem coeff_gamma_eq_zero_of_eval_vanish_sharp {DZ : ℕ}
    (hQdeg : ∀ i j, ∃ q : Polynomial F, q.natDegree ≤ DZ ∧ 𝔞 q = coeff j (QA.coeff i))
    (hresp : Polynomial.eval (𝔞 v) (Polynomial.derivative (Q₀ QA)) = 𝔞 ξ)
    (t : ℕ) (M : Finset F)
    (hcard : sharpBudget QA.natDegree v.natDegree DZ ξ.natDegree t < M.card)
    (hvan : ∀ N : Polynomial F,
      N.natDegree ≤ sharpBudget QA.natDegree v.natDegree DZ ξ.natDegree t →
      𝔞 N = (𝔞 ξ) ^ (2 * t - 1) * coeff t (γ QA (𝔞 v)) →
      ∀ z ∈ M, N.eval z = 0) :
    coeff t (γ QA (𝔞 v)) = 0 := by
  classical
  obtain ⟨N, hdeg, hmap, hexit⟩ := exists_numerator_sharp ξ QA v hQdeg hresp t
  refine hexit ?_
  by_contra hN0
  have hroots : M.card ≤ N.natDegree := by
    have hsub : M ⊆ N.roots.toFinset := by
      intro z hz
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hN0]
      exact hvan N hdeg hmap z hz
    calc M.card ≤ N.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card N.roots := N.roots.toFinset_card_le
      _ ≤ N.natDegree := N.card_roots'
  omega

end ArkLib.SectionNewtonCleared

/-! ## Axiom audit — every declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, with no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms ArkLib.SectionNewtonCleared.sharpBudget_mono
#print axioms ArkLib.SectionNewtonCleared.pow_cleared_sharp
#print axioms ArkLib.SectionNewtonCleared.powTop_cleared_sharp
#print axioms ArkLib.SectionNewtonCleared.gamma_cleared_sharp
#print axioms ArkLib.SectionNewtonCleared.exists_numerator_sharp
#print axioms ArkLib.SectionNewtonCleared.coeff_gamma_eq_zero_of_eval_vanish_sharp
