/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.RepCountStepanovOrderTwo

/-!
# The sharp order-2 Stepanov bound for the 2-power (NTT) domain (#389)

The in-tree order-2 bound `RepCountStepanovOrderTwo.repCount_two_mul_le_of_pow_ne_one`
gives `2·r(c) ≤ n+1` via `deg Q ≤ n+1`, `Q = (c−X)^{n+1} + X^{n+1} − c`.  For the
deployed NTT domains `μ_n` with **`n` even** the two leading terms cancel — the
coefficient of `X^{n+1}` is `(−1)^{n+1} + 1 = 0` — so `deg Q ≤ n` and the bound
sharpens by one:

> **`repCount_two_mul_le_of_even`** — for `μ_n` with `n` even, `c ≠ 0`, `c^n ≠ 1`,
> the leading coefficient vanishes and `2·r(c) ≤ n`, i.e. `r(c) ≤ n/2`.

This is the *sharp* order-2 representation bound on the prize-relevant 2-power
domain (one unit below the odd-`n` / general-field statement).  Honest scope: it
sharpens only the additive constant of the order-2 lane (`E(μ_n) ≤ (1 + n/2)|G|²`
vs `(1 + (n+1)/2)|G|²`); it does **not** change the cube order and does not advance
`δ*` — the asymptotic improvement still requires the confluent (order-`n^{1/3}`)
construction.  Its role is to record the exact endpoint of the explicit order-2
auxiliary on the deployed domain.

Issue #389.
-/

open Polynomial

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

variable {F : Type*} [Field F] [DecidableEq F]

/-- The top coefficient of the order-2 auxiliary vanishes when `n` is even:
`coeff_{n+1}((c−X)^{n+1} + X^{n+1} − c) = (−1)^{n+1} + 1 = 0`. -/
theorem orderTwoAux_coeff_top_eq_zero (c : F) {n : ℕ} (hn : Even n) :
    (((C c - X) ^ (n + 1) + X ^ (n + 1) - C c : F[X])).coeff (n + 1) = 0 := by
  obtain ⟨m, rfl⟩ := hn
  have hodd : Odd (m + m + 1) := ⟨m, by ring⟩
  have hmonic : ((X - C c) ^ (m + m + 1) : F[X]).coeff (m + m + 1) = 1 := by
    have := (monic_X_sub_C c).pow (m + m + 1)
    rw [Polynomial.Monic, Polynomial.leadingCoeff,
      Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one] at this
    exact this
  have hcX : ((C c - X) ^ (m + m + 1) : F[X]).coeff (m + m + 1) = -1 := by
    have h1 : (C c - X : F[X]) = -(X - C c) := by ring
    rw [h1, neg_pow, hodd.neg_one_pow, neg_one_mul, Polynomial.coeff_neg, hmonic]
  have hX : ((X ^ (m + m + 1) : F[X])).coeff (m + m + 1) = 1 := by
    rw [Polynomial.coeff_X_pow, if_pos rfl]
  have hC : ((C c : F[X])).coeff (m + m + 1) = 0 := by
    rw [Polynomial.coeff_C, if_neg (by omega)]
  rw [Polynomial.coeff_sub, Polynomial.coeff_add, hcX, hX, hC, sub_zero]
  ring

/-- **The sharp order-2 Stepanov bound for `n` even** (the deployed 2-power NTT
domain): `2·r(c) ≤ n`. -/
theorem repCount_two_mul_le_of_even {G : Finset F} {n : ℕ} (hn : 1 ≤ n) (hne : Even n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) {c : F} (hc0 : c ≠ 0) (hcn : c ^ n ≠ 1) :
    repCount G c * 2 ≤ n := by
  classical
  set Q : F[X] := (C c - X) ^ (n + 1) + X ^ (n + 1) - C c with hQ
  have hQ0 : Q ≠ 0 := by
    intro h
    have hev0 : Q.eval 0 = 0 := by rw [h, eval_zero]
    rw [hQ] at hev0
    simp only [eval_sub, eval_add, eval_pow, eval_C, eval_X, sub_zero,
      zero_pow (by omega : n + 1 ≠ 0), add_zero] at hev0
    rw [pow_succ] at hev0
    have : c * (c ^ n - 1) = 0 := by linear_combination hev0
    rcases mul_eq_zero.mp this with h1 | h2
    · exact hc0 h1
    · exact hcn (by linear_combination h2)
  have hdegle : Q.natDegree ≤ n + 1 := by rw [hQ]; compute_degree!
  have hdeg : Q.natDegree ≤ n := by
    by_contra hcon
    push_neg at hcon
    have heq : Q.natDegree = n + 1 := by omega
    have hlead : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hQ0
    rw [Polynomial.leadingCoeff, heq] at hlead
    apply hlead
    rw [hQ]
    exact orderTwoAux_coeff_top_eq_zero c hne
  have hmult : ∀ y ∈ G.filter (fun y => c - y ∈ G), 2 ≤ rootMultiplicity y Q := by
    intro y hy
    rw [Finset.mem_filter] at hy
    obtain ⟨hyG, hcyG⟩ := hy
    have hyn : y ^ n = 1 := (hGmem y).mp hyG
    have hcyn : (c - y) ^ n = 1 := (hGmem (c - y)).mp hcyG
    have hev : Q.eval y = 0 := by
      rw [hQ]
      simp only [eval_sub, eval_add, eval_pow, eval_C, eval_X]
      rw [pow_succ (c - y) n, pow_succ y n, hcyn, hyn]
      ring
    have hd : Q.derivative.eval y = 0 := by
      rw [hQ]
      simp only [derivative_sub, derivative_add, derivative_pow, derivative_C,
        derivative_X, derivative_one, Nat.add_sub_cancel, mul_one, sub_zero, zero_sub,
        mul_neg, eval_add, eval_sub, eval_neg, eval_mul, eval_pow, eval_C, eval_X,
        eval_natCast]
      rw [hcyn, hyn]
      ring
    have hr1 : (X - C y) ∣ Q := dvd_iff_isRoot.mpr hev
    obtain ⟨g, hg⟩ := hr1
    have hgy : g.eval y = 0 := by
      have hQd : Q.derivative = g + (X - C y) * g.derivative := by
        rw [hg, derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero,
          one_mul]
      rw [hQd] at hd
      simpa [sub_self] using hd
    obtain ⟨g2, hg2⟩ := dvd_iff_isRoot.mpr hgy
    have hdvd : (X - C y) ^ 2 ∣ Q := ⟨g2, by rw [hg, hg2]; ring⟩
    exact (le_rootMultiplicity_iff hQ0).mpr hdvd
  calc repCount G c * 2
      = (G.filter (fun y => c - y ∈ G)).card * 2 := rfl
    _ ≤ Q.natDegree :=
        StepanovContradictionEngine.stepanov_card_mul_M_le_natDegree Q hQ0 _ 2 hmult
    _ ≤ n := hdeg

/-- The sharp bound as `r(c) ≤ n/2` (n even, deployed 2-power domain). -/
theorem repCount_le_div_two_of_even {G : Finset F} {n : ℕ} (hn : 1 ≤ n) (hne : Even n)
    (hGmem : ∀ z, z ∈ G ↔ z ^ n = 1) {c : F} (hc0 : c ≠ 0) (hcn : c ^ n ≠ 1) :
    repCount G c ≤ n / 2 := by
  have h := repCount_two_mul_le_of_even hn hne hGmem hc0 hcn
  omega

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.orderTwoAux_coeff_top_eq_zero
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.repCount_two_mul_le_of_even
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.repCount_le_div_two_of_even
