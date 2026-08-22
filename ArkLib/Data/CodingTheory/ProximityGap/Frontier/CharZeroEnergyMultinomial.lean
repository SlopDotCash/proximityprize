/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.Order.Antidiag.Pi

/-!
# The combinatorial Wick bound for the char-0 additive energy of `μ_{2^μ}` (#464)

The in-tree `EnergyRelationAntipodal.energy_relation_count_antipodal` proves the *structural*
half of the bound `E_r(μ_{2^m}, ℂ) ≤ (2r−1)!!·n^r`: every additive `r`-relation among `2^k`-th
roots is **antipodally balanced**.  Its docstring flags the *combinatorial* half — actually
counting the antipodally-balanced configurations — as the remaining work.  This file supplies the
exact combinatorial core of that half, fully self-contained (no Lam–Leung needed).

The char-0 additive energy admits the **exact** closed form (verified numerically three ways —
direct complex brute force, wraparound-free `mod p`, and the closed-form DP; see
`docs/kb/deltastar-464-char0-energy-exact-closed-form-2026-06-27.md`)

```
   V_{2r}(n) = #{(u_1..u_{2r}) ∈ μ_n^{2r} : Σ u_i = 0}
             = Σ_{m_1+…+m_{n/2}=r} (2r)! / ∏ (m_k!)²
             = C(2r,r) · Σ_{m ∈ piAntidiag (univ : Finset (Fin (n/2))) r} (multinomial univ m)²,
```

where the last equality uses `(2r)!/∏(m_k!)² = C(2r,r)·(r!/∏ m_k!)² = C(2r,r)·multinomial²`.

The genuinely new, self-contained inequality proved here is

> `multinomial_sq_sum_le` :
>   `Σ_{m ∈ piAntidiag univ r} (multinomial univ m)² ≤ r! · h^r`
>   (`h = n/2`),

from which the Wick bound follows in closed form:

> `centralBinom_mul_multinomial_sq_sum_le` :
>   `C(2r,r) · Σ_{m} (multinomial univ m)² ≤ C(2r,r) · r! · h^r`,

and `C(2r,r)·r!·h^r = (2r)!/r! · h^r = (2r−1)!!·(2h)^r = (2r−1)!!·n^r`, i.e. exactly Wick.

The proof of `multinomial_sq_sum_le` is one elementary observation: `multinomial univ m ≤ r!`
(its denominator `∏(m_k!) ≥ 1`), so `multinomial² ≤ r!·multinomial`, and
`Σ_m multinomial univ m = h^r` by the multinomial theorem (`Finset.sum_pow_eq_sum_piAntidiag`
with `f ≡ 1`).

Significance: this pins the **char-0 half** of the δ* energy wall in closed form (always `≤ Wick`),
isolating the entire open problem in the mod-`p` *wraparound* surplus `W_r`, with the exact budget
`W_r ≤ p·(Wick − V_{2r}) + n^{2r}`.  See `docs/kb/deltastar-OPEN-MATHEMATICS-2026-06-27.md`.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset
open scoped Nat

namespace ArkLib.ProximityGap.Frontier.CharZeroEnergyMultinomial

/-- **Each multinomial is at most `r!`.** For a tuple `m : Fin h → ℕ` summing to `r`, the
multinomial coefficient `r!/∏(m_k!)` is at most `r!`, since its denominator is a positive integer.
-/
theorem multinomial_le_factorial {h r : ℕ} {m : Fin h → ℕ}
    (hm : ∑ i, m i = r) :
    Nat.multinomial (univ : Finset (Fin h)) m ≤ r ! := by
  have hspec : (∏ i ∈ (univ : Finset (Fin h)), (m i)!) * Nat.multinomial univ m
      = (∑ i ∈ univ, m i)! := Nat.multinomial_spec univ m
  rw [hm] at hspec
  have hpos : 1 ≤ ∏ i ∈ (univ : Finset (Fin h)), (m i)! :=
    Finset.one_le_prod' (fun i _ => (m i).factorial_pos)
  calc Nat.multinomial univ m
      = 1 * Nat.multinomial univ m := (one_mul _).symm
    _ ≤ (∏ i ∈ univ, (m i)!) * Nat.multinomial univ m :=
        Nat.mul_le_mul_right _ hpos
    _ = r ! := hspec

/-- **The multinomial theorem with all weights `1`.** The multinomials over tuples of `Fin h`
summing to `r` add up to `h^r`. -/
theorem sum_multinomial_eq_pow (h r : ℕ) :
    ∑ m ∈ piAntidiag (univ : Finset (Fin h)) r, Nat.multinomial univ m = h ^ r := by
  have := Finset.sum_pow_eq_sum_piAntidiag (univ : Finset (Fin h)) (fun _ => (1 : ℕ)) r
  simp only [one_pow, Finset.prod_const_one, mul_one, Finset.sum_const, smul_eq_mul,
    Finset.card_univ, Fintype.card_fin, mul_one] at this
  -- `this : (h : ℕ) ^ r = ∑ m ∈ piAntidiag univ r, multinomial univ m`
  exact this.symm

/-- **The combinatorial Wick core.** The sum of squared multinomials over tuples of `Fin h`
summing to `r` is at most `r! · h^r`.  This is the self-contained combinatorial half of the
char-0 energy bound `E_r(μ_{2^m}) ≤ (2r−1)!!·n^r` (with `h = n/2`). -/
theorem multinomial_sq_sum_le (h r : ℕ) :
    ∑ m ∈ piAntidiag (univ : Finset (Fin h)) r, (Nat.multinomial univ m) ^ 2
      ≤ r ! * h ^ r := by
  calc ∑ m ∈ piAntidiag (univ : Finset (Fin h)) r, (Nat.multinomial univ m) ^ 2
      ≤ ∑ m ∈ piAntidiag (univ : Finset (Fin h)) r, r ! * Nat.multinomial univ m := by
        refine Finset.sum_le_sum (fun m hm => ?_)
        have hsum : ∑ i, m i = r := (Finset.mem_piAntidiag.mp hm).1
        have hle : Nat.multinomial univ m ≤ r ! := multinomial_le_factorial hsum
        calc (Nat.multinomial univ m) ^ 2
            = Nat.multinomial univ m * Nat.multinomial univ m := sq _
          _ ≤ r ! * Nat.multinomial univ m := Nat.mul_le_mul_right _ hle
    _ = r ! * ∑ m ∈ piAntidiag (univ : Finset (Fin h)) r, Nat.multinomial univ m := by
        rw [Finset.mul_sum]
    _ = r ! * h ^ r := by rw [sum_multinomial_eq_pow]

/-- **The Wick bound in central-binomial form.** Multiplying the combinatorial core by the
central binomial coefficient `C(2r,r)` gives the char-0 energy bound:
`V_{2r} = C(2r,r)·Σ multinomial² ≤ C(2r,r)·r!·h^r = (2r)!/r!·h^r = (2r−1)!!·(2h)^r = (2r−1)!!·n^r`.
-/
theorem centralBinom_mul_multinomial_sq_sum_le (h r : ℕ) :
    Nat.centralBinom r *
        ∑ m ∈ piAntidiag (univ : Finset (Fin h)) r, (Nat.multinomial univ m) ^ 2
      ≤ Nat.centralBinom r * (r ! * h ^ r) :=
  Nat.mul_le_mul_left _ (multinomial_sq_sum_le h r)

/-- The central-binomial Wick normalisation:
`C(2r,r) · r! = (2r)!/r!`, i.e. `C(2r,r)·r!·r! = (2r)!`.
This certifies that `centralBinom r * (r! * h^r)` is exactly `(2r)!/r! · h^r`,
the closed Wick value `(2r−1)!!·(2h)^r`. -/
theorem centralBinom_mul_factorial_sq (r : ℕ) :
    Nat.centralBinom r * (r ! * r !) = (2 * r)! := by
  rw [Nat.centralBinom_eq_two_mul_choose]
  have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_mul_of_pos_left r (by norm_num) :
      r ≤ 2 * r)
  -- (2r).choose r * r! * (2r-r)! = (2r)!  with 2r - r = r
  have hsub : 2 * r - r = r := by omega
  rw [hsub] at h
  calc (2 * r).choose r * (r ! * r !)
      = (2 * r).choose r * r ! * r ! := by ring
    _ = (2 * r)! := h

/-! ## Axiom audit -/
#print axioms multinomial_sq_sum_le
#print axioms centralBinom_mul_multinomial_sq_sum_le
#print axioms centralBinom_mul_factorial_sq

end ArkLib.ProximityGap.Frontier.CharZeroEnergyMultinomial
