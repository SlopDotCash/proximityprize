/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ExplainableCoreSupplyInstance
import ArkLib.Data.CodingTheory.ProximityGap.FrobeniusSubfieldBlowup

/-!
# THE EXACT FROBENIUS SUPPLY VALUE (#389): route 1's pair counting is TIGHT

Welds the two halves into the first **exact** explainable-core count at a
sub-Johnson band:

* upper — the in-tree route-1 engine `explainable_cores_card_of_agreement_le`
  (pair counting against `k`-subset determination), fed the agreement cap
  `A = p` proven in `FrobeniusSubfieldBlowup` (`frob_agreement_card_le`);
* lower — the secant floor `frobenius_supply_floor` (every pair of domain
  points lies on an explainable secant).

> **`frobenius_supply_exact`** — for the Frobenius word `w(z) = z^p` over any
> `𝔽_p`-affine-closed domain, at the band `(k, m) = (2, p−3)` (level `t = p`):
> `#(explainable p-cores) · C(p,2) = C(n,2)` — exactly `n(n−1)/(p(p−1))`.

Consequences: the route-1 closure bound `B = C(n,k)·C(A−k,m+1)/C(k+m+1,k)` is
attained with EQUALITY at this instance — there is no slack in the any-domain
counting; the gap to the prime-`q` probed truth (linear supply) is genuinely
domain-arithmetic, not combinatorial.  Issue #389.
-/

open Finset Polynomial

namespace ProximityGap.FrobeniusBlowup

open ProximityGap.SpikeFloor ProximityGap.Ownership

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {p : ℕ} [hp : Fact p.Prime] [CharP F p]
variable {n : ℕ} [NeZero n] {dom : Fin n ↪ F}

open Classical in
/-- The Frobenius word satisfies the route-1 agreement cap at `A = p`. -/
theorem frob_agreeSet_card_le :
    ∀ c ∈ (rsCode dom 2 : Submodule F (Fin n → F)),
      (agreeSet c (frobWord dom p)).card ≤ p := by
  rintro c ⟨P, hPdeg, rfl⟩
  have h := frob_agreement_card_le (dom := dom) (p := p) P hPdeg
  have hset : agreeSet (fun i => P.eval (dom i)) (frobWord dom p)
      = Finset.univ.filter (fun i => P.eval (dom i) = (dom i) ^ p) := by
    ext i
    simp [agreeSet, frobWord]
  rw [hset]
  convert h using 3

/-- `2·C(a,2) = a² − a`. -/
private lemma choose_two_mul_two (a : ℕ) : a.choose 2 * 2 = a * a - a := by
  rw [Nat.choose_two_right]
  rcases a with _ | b
  · simp
  · have he : 2 ∣ (b + 1) * b := by
      rcases Nat.even_mul_succ_self b with ⟨c, hc⟩
      exact ⟨c, by rw [mul_comm (b + 1) b, hc]; ring⟩
    rw [Nat.add_sub_cancel, Nat.div_mul_cancel he]
    have hsq : (b + 1) * (b + 1) = (b + 1) * b + (b + 1) := by ring
    omega

open Classical in
/-- **THE EXACT SUB-JOHNSON SUPPLY VALUE** — for the Frobenius word at the band
`(k, m) = (2, p − 3)` (level `t = p`), the explainable-core count is exactly
`n(n−1)/(p(p−1))`: the route-1 pair-counting closure is TIGHT. -/
theorem frobenius_supply_exact (hcl : AffClosed dom p) (hp3 : 3 ≤ p) :
    (frobFamily dom p).card * (p * p - p) = n * n - n := by
  have hm : 2 + (p - 3) + 1 = p := by omega
  -- upper half: the route-1 engine at `m = p−3`, `A = p`
  have hupper := explainable_cores_card_of_agreement_le (dom := dom)
    (k := 2) (m := p - 3) (w := frobWord dom p) (A := p)
    (by norm_num) frob_agreeSet_card_le
  rw [hm] at hupper
  have hch : (p - 2).choose (p - 3 + 1) = 1 := by
    have h32 : p - 3 + 1 = p - 2 := by omega
    rw [h32, Nat.choose_self]
  rw [hch, mul_one] at hupper
  -- transfer the engine's filter to `frobFamily`
  have hfam : (frobFamily dom p).card * p.choose 2 ≤ n.choose 2 := by
    unfold frobFamily
    convert hupper using 4
  -- multiply through by 2 on both halves and squeeze
  have e1 := choose_two_mul_two p
  have e2 := choose_two_mul_two n
  have h3 : (frobFamily dom p).card * p.choose 2 * 2 ≤ n.choose 2 * 2 :=
    Nat.mul_le_mul_right 2 hfam
  have hupper2 : (frobFamily dom p).card * (p * p - p) ≤ n * n - n := by
    calc (frobFamily dom p).card * (p * p - p)
        = (frobFamily dom p).card * (p.choose 2 * 2) := by rw [e1]
      _ = (frobFamily dom p).card * p.choose 2 * 2 := by ring
      _ ≤ n.choose 2 * 2 := h3
      _ = n * n - n := e2
  have hlower := frobenius_supply_floor hcl
  rw [mul_comm (p * p - p) (frobFamily dom p).card] at hlower
  omega

open Classical in
/-- The same exact value in binomial form: `E · C(p,2) = C(n,2)`. -/
theorem frobenius_supply_exact_choose (hcl : AffClosed dom p) (hp3 : 3 ≤ p) :
    (frobFamily dom p).card * p.choose 2 = n.choose 2 := by
  have h := frobenius_supply_exact hcl hp3
  have h2 : (frobFamily dom p).card * (p.choose 2 * 2) = n.choose 2 * 2 := by
    rw [choose_two_mul_two, choose_two_mul_two]
    exact h
  have h3 : (frobFamily dom p).card * p.choose 2 * 2 = n.choose 2 * 2 := by
    rw [← h2]; ring
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h3

end ProximityGap.FrobeniusBlowup

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.FrobeniusBlowup.frob_agreeSet_card_le
#print axioms ProximityGap.FrobeniusBlowup.frobenius_supply_exact
#print axioms ProximityGap.FrobeniusBlowup.frobenius_supply_exact_choose
