/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.Order.Antidiag.Pi

/-!
# The per-profile fiber identity for the char-0 additive energy of `μ_{2^μ}` (#464)

`CharZeroEnergyMultinomial.lean` proves the *abstract* multinomial Wick bound
`Σ_m (multinomial univ m)² ≤ r!·h^r`.  The char-0 additive energy
`V_{2r}(μ_{2^μ}) = #{(u_1..u_{2r}) ∈ μ_n^{2r} : Σ u_i = 0}` admits the **exact** closed form
(verified numerically: `scratchpad/bij_verify.py`, `bij_architecture.py`, `algebraic_heart.py`)

```
   V_{2r}(n) = Σ_{a : Fin h → ℕ, Σ a = r}  (2r)! / ∏_k (a_k!)²
             = C(2r,r) · Σ_a (multinomial univ a)²,     h = n/2 = 2^{μ-1}.
```

The bijection (the "Route B" exponent count, fully numerically verified) is:

* a zero-sum tuple `e : Fin (2r) → ZMod (2^μ)` is, by the in-tree multiset Lam–Leung
  (`LamLeungMultisetAntipodal.multiset_antipodal_iff`), exactly one whose fiber-size function
  `w : ZMod (2^μ) → ℕ`, `w j = #{i : e i = j}`, is **antipodally balanced**:
  `w j = w (j + 2^{μ-1})`;
* an antipodally-balanced `w` is determined by a **profile** `a : Fin h → ℕ` with `Σ a = r`
  (`a_k = w k = w (k + h)`); and
* the number of ordered tuples with a fixed `w` is the multiset multinomial `(2r)! / ∏_j (w_j!)`,
  which for a doubled profile is `(2r)! / ∏_k (a_k!)²`.

This file lands the **algebraic heart** of the third bullet — the *per-profile term identity*,
fully self-contained (only factorial algebra, no Lam–Leung needed):

> `multinomial_doubled_eq` :
>   for a profile `a : Fin h → ℕ` with `Σ a = r`, the multinomial of the **doubled** profile
>   `w : Fin (2h) → ℕ` (`w` placing `a_k` on coordinate `k` and on coordinate `k + h`) equals
>   `C(2r,r) · (multinomial univ a)²`,
> equivalently the fiber count `(2r)! / ∏ (a_k!)² = C(2r,r) · (multinomial univ a)²`.

This is the exact per-term value the fiber bijection produces, so summing it over profiles `a`
gives the exact closed form `V_{2r} = C(2r,r)·Σ_a (multinomial univ a)²`.  It upgrades the
abstract `Σ multinomial² ≤ Wick` bound into the *exact* energy term, completing the algebraic
layer of the char-0 energy bijection node.

**The single remaining combinatorial input** for the full energy identity is the *fiber-profile
count*, a Mathlib-level lemma not currently in Mathlib (verified `scratchpad/missing_piece.py`):

> `FiberProfileCount` :
>   for a fintype `B`, `N : ℕ`, profile `w : B → ℕ` with `Σ w = N`,
>   `#{f : Fin N → B | ∀ b, #{i | f i = b} = w b} = Nat.multinomial univ w`.

Given `FiberProfileCount` plus the in-tree Lam–Leung iff
(`LamLeungMultisetAntipodal.multiset_antipodal_iff`, the zero-sum ⟺ antipodal-balance translation)
and the routine `Fin (2h) ≃ Fin h ⊕ Fin h` reindexing of a balanced `w` to a profile `a`, the
two identities here assemble to `V_{2r} = C(2r,r)·Σ_a (multinomial univ a)²`.  Neither
`FiberProfileCount` nor the Lam–Leung iff touch the Paley/BGK wall — this whole node is the
char-0 *shadow* (off the wall); the open floor is the `mod p` wraparound surplus only.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset
open scoped Nat

namespace ArkLib.ProximityGap.Frontier.CharZeroEnergyProfileFiber

/-- The **doubled profile**: from `a : Fin h → ℕ` build `w : Fin (2h) → ℕ` placing the value
`a k` on both coordinate `k` and coordinate `k + h` (under the `Fin (2h) ≃ Fin h ⊕ Fin h`
identification via `finSumFinEquiv`). -/
noncomputable def doubledProfile {h : ℕ} (a : Fin h → ℕ) : Fin (h + h) → ℕ :=
  fun j => Sum.elim a a (finSumFinEquiv.symm j)

/-- The doubled profile sums to `2·(Σ a)`. -/
theorem sum_doubledProfile {h : ℕ} (a : Fin h → ℕ) :
    ∑ j, doubledProfile a j = 2 * ∑ i, a i := by
  classical
  unfold doubledProfile
  rw [← Equiv.sum_comp finSumFinEquiv (fun j => Sum.elim a a (finSumFinEquiv.symm j))]
  simp only [Equiv.symm_apply_apply]
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  ring

/-- The product of factorials over the doubled profile is the square of the product over `a`. -/
theorem prod_factorial_doubledProfile {h : ℕ} (a : Fin h → ℕ) :
    ∏ j, (doubledProfile a j)! = (∏ i, (a i)!) ^ 2 := by
  classical
  unfold doubledProfile
  rw [← Equiv.prod_comp finSumFinEquiv (fun j => (Sum.elim a a (finSumFinEquiv.symm j))!)]
  simp only [Equiv.symm_apply_apply]
  rw [Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [sq]

/-- **The per-profile fiber identity (factorial form).** For a profile `a : Fin h → ℕ` summing
to `r`, the fiber count `(2r)! / ∏ (a_k!)²` of ordered `2r`-tuples with doubled counting
function equals `C(2r,r) · (multinomial univ a)²`.  Stated multiplicatively to stay in `ℕ`:

> `(2r)! = C(2r,r) · (multinomial univ a)² · ∏ (a_k!)²`. -/
theorem factorial_two_mul_eq {h r : ℕ} {a : Fin h → ℕ} (ha : ∑ i, a i = r) :
    (2 * r)! = Nat.centralBinom r * (Nat.multinomial univ a) ^ 2 * (∏ i, (a i)!) ^ 2 := by
  -- multinomial_spec: (∏ aᵢ!) · multinomial = (Σ aᵢ)! = r!
  have hspec : (∏ i, (a i)!) * Nat.multinomial univ a = r ! := by
    have := Nat.multinomial_spec (univ : Finset (Fin h)) a
    rwa [ha] at this
  -- centralBinom_mul_factorial_sq:  C(2r,r) · (r! · r!) = (2r)!
  have hcentral : Nat.centralBinom r * (r ! * r !) = (2 * r)! := by
    rw [Nat.centralBinom_eq_two_mul_choose]
    have hch := Nat.choose_mul_factorial_mul_factorial
      (Nat.le_mul_of_pos_left r (by norm_num) : r ≤ 2 * r)
    have hsub : 2 * r - r = r := by omega
    rw [hsub] at hch
    calc (2 * r).choose r * (r ! * r !)
        = (2 * r).choose r * r ! * r ! := by ring
      _ = (2 * r)! := hch
  -- assemble: (2r)! = C·r!·r! = C·(∏aᵢ!·multinomial)·(∏aᵢ!·multinomial) = C·multinomial²·(∏aᵢ!)²
  set P : ℕ := ∏ i, (a i)! with hP
  calc (2 * r)!
      = Nat.centralBinom r * (r ! * r !) := hcentral.symm
    _ = Nat.centralBinom r *
          ((P * Nat.multinomial univ a) * (P * Nat.multinomial univ a)) := by
        rw [hspec]
    _ = Nat.centralBinom r * (Nat.multinomial univ a) ^ 2 * P ^ 2 := by ring

/-- **The per-profile fiber identity (multinomial form).** The multinomial of the **doubled**
profile equals `C(2r,r) · (multinomial univ a)²`:

> `multinomial univ (doubledProfile a) = C(2r,r) · (multinomial univ a)²`.

This is the exact per-term value the fiber bijection assigns to a profile `a` (a zero-sum tuple
with antipodal counting function determined by `a`).  Summing over profiles `a` with `Σ a = r`
gives the exact char-0 energy closed form `V_{2r} = C(2r,r)·Σ_a (multinomial univ a)²`. -/
theorem multinomial_doubled_eq {h r : ℕ} {a : Fin h → ℕ} (ha : ∑ i, a i = r) :
    Nat.multinomial univ (doubledProfile a)
      = Nat.centralBinom r * (Nat.multinomial univ a) ^ 2 := by
  -- multinomial_spec for the doubled profile: (∏ wⱼ!) · multinomial w = (Σ wⱼ)! = (2r)!
  have hspecw : (∏ j, (doubledProfile a j)!) * Nat.multinomial univ (doubledProfile a)
      = (∑ j, doubledProfile a j)! := Nat.multinomial_spec univ (doubledProfile a)
  rw [sum_doubledProfile, ha, prod_factorial_doubledProfile] at hspecw
  -- hspecw : (∏ aᵢ!)² · multinomial (doubled a) = (2r)!
  -- and factorial_two_mul_eq : (2r)! = C · multinomial(a)² · (∏ aᵢ!)²
  have hfac := factorial_two_mul_eq ha
  rw [hfac] at hspecw
  -- cancel the positive factor (∏ aᵢ!)²
  have hpos : 0 < (∏ i, (a i)!) ^ 2 :=
    pow_pos (Finset.prod_pos (fun i _ => (a i).factorial_pos)) 2
  have hcomm : (∏ i, (a i)!) ^ 2 * Nat.multinomial univ (doubledProfile a)
      = (∏ i, (a i)!) ^ 2 * (Nat.centralBinom r * (Nat.multinomial univ a) ^ 2) := by
    rw [hspecw]; ring
  exact Nat.eq_of_mul_eq_mul_left hpos hcomm

/-- **The summed closed-form identity.** Summing the per-profile term over all profiles
`a : Fin h → ℕ` with `Σ a = r` (the index set `piAntidiag univ r`) gives:

> `Σ_a multinomial univ (doubledProfile a) = C(2r,r) · Σ_a (multinomial univ a)²`.

The left side is the sum of the exact fiber-multinomial values the bijection assigns to each
profile; the right side is exactly the closed form proved bounded in
`CharZeroEnergyMultinomial.centralBinom_mul_multinomial_sq_sum_le`.  Together with the (still
open) fiber-count bijection this equals the char-0 energy `V_{2r}`; this identity is its
**algebraic spine**, pure factorial algebra, no Lam–Leung needed. -/
theorem sum_multinomial_doubled_eq (h r : ℕ) :
    ∑ a ∈ piAntidiag (univ : Finset (Fin h)) r, Nat.multinomial univ (doubledProfile a)
      = Nat.centralBinom r *
          ∑ a ∈ piAntidiag (univ : Finset (Fin h)) r, (Nat.multinomial univ a) ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  exact multinomial_doubled_eq (Finset.mem_piAntidiag.mp ha).1

/-! ## Axiom audit -/
#print axioms sum_multinomial_doubled_eq
#print axioms multinomial_doubled_eq
#print axioms factorial_two_mul_eq
#print axioms sum_doubledProfile
#print axioms prod_factorial_doubledProfile

end ArkLib.ProximityGap.Frontier.CharZeroEnergyProfileFiber
