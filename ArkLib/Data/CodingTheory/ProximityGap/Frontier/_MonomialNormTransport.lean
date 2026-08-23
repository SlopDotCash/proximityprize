/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._CyclicPowerRangeTorsion

/-!
# The `(BRIDGE)` norm-transport: a monomial-Weyl-sum bound divides cleanly to a period bound (#444)

`_CyclicPowerRangeTorsion.sum_pow_eq_smul_sum_torsion` lands the bridge as an **equation** over a
finite cyclic group `G` (think `G = F_p^*`, `m·n = #G`):
```
        Σ_x F(x^m)  =  m • Σ_{y : y^n = 1} F y .                                   (BRIDGE on μ_n)
```
For `F y = e_p(b·y)` this reads `S_b := Σ_{x∈F_p^*} e_p(b·x^m) = m · η_b`, with `η_b` the prize period
over the literal `n`-th roots of unity `μ_n`.

The entire equidistribution ladder of `_MonomialWeylBridge` (Weil `(m−1)√p`, BGK `n^{1−o(1)}`, the
open prize `√(n·log(q/n))`) is phrased as bounds on the **period** `|η_b|`, but every classical input
(Weil, BGK, …) is naturally a bound on the **complete monomial sum** `|S_b|`. The bridge equation says
they differ by the exact factor `m`. The docstring states the transport "up to the factor `m`" as
**prose**; this file makes it a reusable theorem:
```
        |S_b| ≤ B   and   0 < m   ⟹   |η_b| ≤ B / m .                              (TRANSPORT)
```
So any monomial-Weyl-sum bound `B` on `Σ_x F(x^m)` transports verbatim, divided by `m`, to a bound on
the prize period `Σ_{y∈μ_n} F y`. This is the inequality face of `(BRIDGE)`: it is what lets a future
formalized Weil/BGK/Burgess bound on the degree-`m` complete sum become a bound on `M(n)` with the
`m` removed exactly (no slack).

**Probe** `scripts/probes/probe_monomial_norm_transport.py` (0 fails / 7 prize-regime instances incl.
the prize Fermat prime `p = 65537, n = 16, β = 4` and `p = 12289, n = 64`): both the equation
`m·η_b = S_b` (worst err `3.7e-8`) and the transport `|η_b| = |S_b|/m` (worst err `9.0e-12`) hold
exactly; a bound `B` on `|S_b|` divides cleanly to `B/m` on `|η_b|`.

The sup-norm form `max'_norm_sum_torsion_eq` lands the transport on the LITERAL prize quantity
`M(n) = max_{b≠0} |η_b|`: `max_b ‖Σ_{y∈μ_n} F_b y‖ = (max_b ‖Σ_x F_b(x^m)‖) / m`, so the prize
sup-norm IS the complete-monomial-sum sup-norm over `m`, no slack.

**Honest scope.** This is a structural NORM-transport over `ℂ`, NON-MOMENT, field-universal (it works
for any `M = ℂ`-valued `F`). It is **NOT** a CORE closure: it proves nothing about the *size* of either
side — it only transports a HYPOTHETICAL monomial bound `B` to the period, dividing by `m`. The open
analytic prize (producing the sub-Weil `B`, i.e. `|S_b| ≤ C·m·√(n·log(q/n))` thinness-essentially) is
entirely untouched; supplying `B` is the wall. ASYMPTOTIC GUARD: no capacity / beyond-Johnson claim is
made — `B` is an arbitrary hypothesis, the cliff-at-n/2 is untouched. Issue #444.
-/

namespace ProximityGap.Frontier.MonomialNormTransport

open Finset

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] [IsCyclic G]

/-- **The `(BRIDGE)` equation specialised to `ℂ` with `m • z` written as `(m:ℂ) * z`.**
`Σ_x F(x^m) = (m : ℂ) · Σ_{y : y^n = 1} F y` for `m·n = #G`. (`nsmul = (↑m) * ·` over `ℂ`.) -/
theorem sum_pow_eq_natCast_mul_sum_torsion (m n : ℕ) (F : G → ℂ) (hmn : m * n = Nat.card G) :
    ∑ x, F (x ^ m) = (m : ℂ) * ∑ y ∈ (univ.filter (fun y : G => y ^ n = 1)), F y := by
  rw [ProximityGap.Frontier.CyclicPowerRangeTorsion.sum_pow_eq_smul_sum_torsion m n F hmn,
    nsmul_eq_mul]

/-- **The period norm IS the monomial-sum norm divided by `m`** (exact, no slack), `0 < m`.
`‖Σ_{y:y^n=1} F y‖ = ‖Σ_x F(x^m)‖ / m`. The equality form of `(TRANSPORT)`. -/
theorem norm_sum_torsion_eq (m n : ℕ) (F : G → ℂ) (hmn : m * n = Nat.card G) (hm : 0 < m) :
    ‖∑ y ∈ (univ.filter (fun y : G => y ^ n = 1)), F y‖
      = ‖∑ x, F (x ^ m)‖ / m := by
  have hmne : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [sum_pow_eq_natCast_mul_sum_torsion m n F hmn, norm_mul, Complex.norm_natCast]
  rw [mul_comm, mul_div_assoc]
  rw [div_self (by positivity : (m : ℝ) ≠ 0), mul_one]

/-- **`(TRANSPORT)`: a monomial-Weyl-sum bound `B` divides cleanly to the period bound `B / m`.**
If `‖Σ_x F(x^m)‖ ≤ B` and `0 < m`, then `‖Σ_{y:y^n=1} F y‖ ≤ B / m`. This is the reusable
inequality the equidistribution ladder consumes: any bound on the complete degree-`m` monomial sum
transports, divided by `m`, to a bound on the prize period over `μ_n`. -/
theorem norm_sum_torsion_le_of_monomial_le (m n : ℕ) (F : G → ℂ) (hmn : m * n = Nat.card G)
    (hm : 0 < m) {B : ℝ} (hB : ‖∑ x, F (x ^ m)‖ ≤ B) :
    ‖∑ y ∈ (univ.filter (fun y : G => y ^ n = 1)), F y‖ ≤ B / m := by
  rw [norm_sum_torsion_eq m n F hmn hm]
  exact div_le_div_of_nonneg_right hB (by exact_mod_cast hm.le)

/-- **Contrapositive direction (a period lower bound forces a monomial lower bound).** If the period
exceeds `L / m`, the monomial sum exceeds `L`. Useful when the *house* period `M(n)` is the known
quantity and one wants the implied size of the complete monomial sum. -/
theorem norm_monomial_gt_of_torsion_gt (m n : ℕ) (F : G → ℂ) (hmn : m * n = Nat.card G)
    (hm : 0 < m) {L : ℝ}
    (hL : L / m < ‖∑ y ∈ (univ.filter (fun y : G => y ^ n = 1)), F y‖) :
    L < ‖∑ x, F (x ^ m)‖ := by
  rw [norm_sum_torsion_eq m n F hmn hm] at hL
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  calc L = (L / m) * m := by field_simp
    _ < (‖∑ x, F (x ^ m)‖ / m) * m := by
          exact mul_lt_mul_of_pos_right hL hmr
    _ = ‖∑ x, F (x ^ m)‖ := by field_simp

/-- **Sup-norm `(TRANSPORT)`: the prize `max`-period IS the monomial-sum `max` divided by `m`.**
For a finite nonempty set `s` of frequencies and a family `F : ι → G → ℂ`,
`max_{b∈s} ‖Σ_{y∈μ_n} F b y‖ = (max_{b∈s} ‖Σ_x F b (x^m)‖) / m`. This is the literal shape of the
prize quantity `M(n) = max_{b≠0} |η_b|`: it equals the complete-monomial-sum sup-norm over `m`, with
no slack. So a uniform-in-`b` bound on the degree-`m` monomial sum transports, divided by `m`, to a
bound on the full prize `M(n)`. -/
theorem max'_norm_sum_torsion_eq {ι : Type*} (m n : ℕ) (F : ι → G → ℂ)
    (hmn : m * n = Nat.card G) (hm : 0 < m) (s : Finset ι) (hs : s.Nonempty) :
    (s.image (fun b => ‖∑ y ∈ (univ.filter (fun y : G => y ^ n = 1)), F b y‖)).max'
        (hs.image _)
      = (s.image (fun b => ‖∑ x, F b (x ^ m)‖)).max' (hs.image _) / m := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  -- div-by-m is monotone on ℝ (m > 0), so it commutes with the finset max'.
  have hmono : Monotone (fun t : ℝ => t / m) := fun a b hab =>
    div_le_div_of_nonneg_right hab hmr.le
  -- antisymmetry, each direction by the elementwise exact transport `norm_sum_torsion_eq`.
  apply le_antisymm
  · -- period-max ≤ monomial-max/m: every period-norm = (its monomial-norm)/m ≤ (max monomial-norm)/m.
    apply Finset.max'_le
    intro v hv
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
    rw [norm_sum_torsion_eq m n (F b) hmn hm]
    exact hmono (Finset.le_max' (s.image (fun b => ‖∑ x, F b (x ^ m)‖)) _
      (Finset.mem_image.mpr ⟨b, hb, rfl⟩))
  · -- monomial-max/m ≤ period-max: clear the /m, then bound the monomial-max elementwise.
    rw [div_le_iff₀ hmr]
    apply Finset.max'_le
    intro v hv
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
    have hper : ‖∑ x, F b (x ^ m)‖
        = ‖∑ y ∈ (univ.filter (fun y : G => y ^ n = 1)), F b y‖ * m := by
      rw [norm_sum_torsion_eq m n (F b) hmn hm, div_mul_cancel₀ _ hmr.ne']
    rw [hper]
    exact mul_le_mul_of_nonneg_right
      (Finset.le_max' (s.image (fun b => ‖∑ y ∈ (univ.filter (fun y : G => y ^ n = 1)), F b y‖)) _
        (Finset.mem_image.mpr ⟨b, hb, rfl⟩)) hmr.le

end ProximityGap.Frontier.MonomialNormTransport

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.MonomialNormTransport.sum_pow_eq_natCast_mul_sum_torsion
#print axioms ProximityGap.Frontier.MonomialNormTransport.norm_sum_torsion_eq
#print axioms ProximityGap.Frontier.MonomialNormTransport.norm_sum_torsion_le_of_monomial_le
#print axioms ProximityGap.Frontier.MonomialNormTransport.norm_monomial_gt_of_torsion_gt
#print axioms ProximityGap.Frontier.MonomialNormTransport.max'_norm_sum_torsion_eq
