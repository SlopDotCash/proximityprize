/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic.NormNum.Prime
import ArkLib.Data.CodingTheory.ProximityGap.TwoBranchSupplyCountermodel
import ArkLib.Data.CodingTheory.ProximityGap.EsymmFiber

/-!
# The smooth-domain two-regime supply law is FALSE at `C₀ = 2`

`TwoBranchSupplyCountermodel.lean` proposed `SmoothDomainTwoRegimeLaw C₀` (the capped supply
law restricted to prime fields and multiplicative subgroup domains) as the production-relevant
open target, on the grounds that every known superlinear supply mechanism needs additive
structure.  The coset supply family already in tree (`EsymmFiber.rootsOfUnity_dyadic_supply`)
is a multiplicative mechanism, and it refutes the law already at `C₀ = 2`:

* `p = 65537`, `n = 32`, `γ = 65529` of exact order `32`, `k = 14`, `m = 1`, received word
  `w = X^16` on `μ₃₂`.
* Every degree-`< 14` polynomial agrees with `X^16` on at most `16` domain points (root count),
  so the cap `16 ≤ 2k + m + 1 = 30` holds.
* `rootsOfUnity_dyadic_supply` with `d = 4`, `r = 8`, `s = 4` gives at least
  `C(8, 4) = 70` explainable `16`-cores (unions of four of the eight `μ₄`-cosets).
* `C(32, 16) = 601080390 < 65537² `, so the Nat quotient in the law is `0` and the
  `C₀ = 2` upper bound is `2·32 = 64 < 70`.

The configuration is strictly interior (`14 < 16` and `16² = 256 < 14·32 = 448`).  Since
`SmoothDomainTwoRegimeLaw` is a specialization of `CappedSupplyTwoRegimeLaw`, the latter is
refuted at `C₀ = 2` too.  This refutes the named universal Props at `C₀ = 2`; it is not a
statement about any particular production threshold such as `n = 2^30`, and it is not a Lean
inconsistency (the laws were only ever proposed `Prop`s, never assumed).

Source: 2026-10-28 repository audit, finding PG-308 (kernel receipt reproduced here).
-/

open Polynomial Finset
open ProximityGap.SpikeFloor ProximityGap.EsymmFiber

namespace ProximityGap.TwoBranch

namespace SmoothDomainRefutation

private instance : Fact (Nat.Prime 65537) := ⟨by norm_num⟩

/-- The generator `65529` of the order-`32` subgroup of `(ZMod 65537)ˣ`. -/
private def gamma : ZMod 65537 := 65529

private theorem gamma_order : orderOf gamma = 32 := by
  rw [orderOf_eq_iff (by decide : 0 < 32)]
  constructor
  · decide +kernel
  · intro j hj hjpos
    interval_cases j <;> decide +kernel

private theorem primitive : IsPrimitiveRoot gamma 32 :=
  IsPrimitiveRoot.iff_orderOf.mpr gamma_order

end SmoothDomainRefutation

open SmoothDomainRefutation in
/-- **`SmoothDomainTwoRegimeLaw 2` is false**: on the proper smooth subgroup `μ₃₂ ⊆ 𝔽₆₅₅₃₇`,
`k = 14`, `m = 1`, the capped word `X^16` has at least `70 > 64` explainable `16`-cores. -/
theorem smoothDomainTwoRegimeLaw_two_false : ¬ SmoothDomainTwoRegimeLaw 2 := by
  classical
  intro hlaw
  let dom : Fin 32 ↪ ZMod 65537 := domRU primitive
  let w : Fin 32 → ZMod 65537 := fun i => (dom i) ^ 16
  have hcap : ∀ c ∈ (rsCode dom 14 : Submodule (ZMod 65537) (Fin 32 → ZMod 65537)),
      (Finset.univ.filter fun i => c i = w i).card ≤ 2 * 14 + 1 + 1 := by
    intro c hc
    rcases hc with ⟨P, hP, rfl⟩
    have hdeg : P.degree < (X ^ 16 : (ZMod 65537)[X]).degree := by
      rw [degree_X_pow]
      exact lt_trans hP (by norm_num)
    have hbound := branch_agreement_card_le dom hdeg Finset.univ
    rw [natDegree_X_pow] at hbound
    have hbound' : (Finset.univ.filter fun i => P.eval (dom i) = w i).card ≤ 16 := by
      simpa only [w, Polynomial.eval_pow, Polynomial.eval_X] using hbound
    change (Finset.univ.filter fun i => P.eval (dom i) = w i).card ≤ 2 * 14 + 1 + 1
    omega
  have hupper := hlaw 65537 32 gamma gamma_order dom (fun _ => rfl) 14 1 w hcap
  have hlower := rootsOfUnity_dyadic_supply primitive (k := 14) (m := 1)
    (d := 4) (r := 8) (by norm_num) (by norm_num) (by norm_num)
    (1 : ZMod 65537) one_ne_zero (0 : (ZMod 65537)[X]) (by exact WithBot.bot_lt_coe 14)
    (s := 4) (by norm_num)
  have hlower' : 70 ≤
      (((Finset.univ : Finset (Fin 32)).powersetCard (14 + 1 + 1)).filter
        (fun T => ∃ c ∈ (rsCode dom 14 : Submodule (ZMod 65537) (Fin 32 → ZMod 65537)),
          ∀ i ∈ T, c i = w i)).card := by
    refine Nat.le_trans (show 70 ≤ Nat.choose 8 4 by decide) ?_
    simp only [map_one, one_mul, add_zero, Polynomial.eval_pow, Polynomial.eval_X] at hlower
    convert hlower using 3
  have hnum : (32 : ℕ).choose 16 = 601080390 := by
    rw [Nat.choose_eq_factorial_div_factorial (by decide : 16 ≤ 32)]
    norm_num [Nat.factorial]
  have hquot : (601080390 : ℕ) / 65537 ^ (1 + 1) = 0 := by decide +kernel
  norm_num only [show 14 + 1 + 1 = 16 by decide, hnum, hquot] at hupper hlower'
  omega

/-- **`CappedSupplyTwoRegimeLaw 2` is false**, as it specializes to
`SmoothDomainTwoRegimeLaw 2`. -/
theorem cappedSupplyTwoRegimeLaw_two_false : ¬ CappedSupplyTwoRegimeLaw 2 := by
  intro h
  apply smoothDomainTwoRegimeLaw_two_false
  intro p hp n hn γ _ dom _ k m w hcap
  exact h p n dom k m w hcap

end ProximityGap.TwoBranch

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.TwoBranch.smoothDomainTwoRegimeLaw_two_false
#print axioms ProximityGap.TwoBranch.cappedSupplyTwoRegimeLaw_two_false
