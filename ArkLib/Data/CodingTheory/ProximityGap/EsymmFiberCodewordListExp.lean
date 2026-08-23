/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.EsymmFiberCodewordList

/-!
# Exponential form of the smooth-domain codeword list lower bound

This tiny companion module keeps the cheap central-binomial corollary separate from the heavier
`EsymmFiberCodewordList` proof.  The imported theorem gives a list lower bound
`(2s).choose s`; here we expose the more legible exponential form `> 4^s / s`.
-/

open Finset Polynomial

namespace ProximityGap.EsymmFiber

open ProximityGap.SpikeFloor ProximityGap.Ownership

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {n : ℕ} [NeZero n]

open scoped Classical in
/-- **Central-binomial exponential form of the codeword-list lower bound.**  In the balanced
dyadic split `r = 2s`, the actual agreement-`k+m+1` Reed-Solomon codeword list for the degree-`t`
power word has size `> 4^s / s`.  This is the list-size analogue of
`rootsOfUnity_dyadic_supply_exp`: the exponential object is not merely many explainable cores,
but many distinct degree-`<k` codewords. -/
theorem rootsOfUnity_dyadic_codeword_list_exp {ζ : F} (hζ : IsPrimitiveRoot ζ n)
    {k m d s : ℕ} (hk : 1 ≤ k) (hd : m + 2 ≤ d) (hs4 : 4 ≤ s) (hnr : n = d * (2 * s))
    (wt : F) (hwt : wt ≠ 0) (lowPart : Polynomial F) (hlow : lowPart.degree < (k : WithBot ℕ))
    (hsd : s * d = k + m + 1) :
    4 ^ s < s * ((Finset.univ : Finset (Fin n → F)).filter (fun c =>
        c ∈ (rsCode (domRU hζ) k : Submodule F (Fin n → F))
          ∧ k + m + 1 ≤ (Finset.univ.filter (fun i =>
              c i = (C wt * X ^ (k + m + 1) + lowPart).eval (domRU hζ i))).card)).card := by
  have hge := rootsOfUnity_dyadic_codeword_list_ge hζ hk hd hnr wt hwt lowPart hlow hsd
  calc 4 ^ s < s * Nat.centralBinom s := Nat.four_pow_lt_mul_centralBinom s hs4
    _ = s * (2 * s).choose s := by rw [Nat.centralBinom]
    _ ≤ s * _ := Nat.mul_le_mul le_rfl hge

end ProximityGap.EsymmFiber

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.EsymmFiber.rootsOfUnity_dyadic_codeword_list_exp
