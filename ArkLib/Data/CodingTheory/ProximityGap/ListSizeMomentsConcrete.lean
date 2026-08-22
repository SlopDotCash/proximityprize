/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ListSizeMoments
import ArkLib.Data.CodingTheory.ProximityGap.BallVolume

/-!
# Direction A, made concrete: explicit moment list bounds (#232)

Ties together the moment identities (`ListSizeMoments.lean`) and the ball-volume closed form
(`BallVolume.lean`): the abstract ball volume `V(r)` is replaced by `Σ_{i≤r} C(n,i)(q-1)^i`, so the
first-moment worst-case list bound becomes a fully explicit inequality in `n = |ι|`, `q = |F|`, `r`.

* `ballVol_closed` — `V(r) = Σ_{i≤r} C(n,i)·(q-1)^i` (bridging `hammingDist 0 = hammingNorm`).
* `exists_large_list_concrete` — some received word has list size `≥ |C|·Σ_{i≤r}C(n,i)(q-1)^i / qⁿ`,
  the explicit averaged lower bound (concrete form of `exists_large_list`).
* `covering_lower_bound_concrete` — the Paley-Zygmund/Cauchy-Schwarz covered-set lower bound with
  the same closed-form volume substituted.
* `covering_lower_bound_linear_concrete` — the linear-code version with the exact second moment
  rewritten as the weight-enumerator pair-ball sum.
-/

namespace ArkLib.CodingTheory.ListMoments

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Fintype F] [DecidableEq F] [Field F]

/-- **The ball volume in closed form.** `V(r) = Σ_{i=0}^{r} C(n,i)·(q-1)^i`. -/
theorem ballVol_closed (r : ℕ) :
    ballVol ι F r
      = ∑ i ∈ Finset.range (r + 1), (Fintype.card ι).choose i * (Fintype.card F - 1) ^ i := by
  unfold ballVol
  simp only [hammingDist_zero_left]
  exact ArkLib.CodingTheory.BallVolume.ballVol_eq r

/-- **Concrete worst-case list lower bound.** At radius `r`, some received word `f` has a decoding
list of size at least the explicit average `|C|·Σ_{i≤r}C(n,i)(q-1)^i / qⁿ`; clearing `qⁿ`:
`|C|·(Σ_{i≤r}C(n,i)(q-1)^i) ≤ qⁿ·|Λ(C,r,f)|`. Fully explicit in `n, q, r` — direction A's averaged
lower half of `δ*` as a closed-form inequality. -/
theorem exists_large_list_concrete (C : Finset (ι → F)) (r : ℕ) :
    ∃ f : ι → F,
      C.card * (∑ i ∈ Finset.range (r + 1), (Fintype.card ι).choose i * (Fintype.card F - 1) ^ i)
        ≤ Fintype.card (ι → F) * (lam C r f).card := by
  rw [← ballVol_closed]
  exact exists_large_list C r

/-- **Concrete covered-set lower bound.** The number of received words covered by radius-`r`
decoding balls satisfies the Paley-Zygmund/Cauchy-Schwarz lower bound with the Hamming volume
written as the closed binomial sum `Σ_{i≤r} C(n,i)(q-1)^i`. -/
theorem covering_lower_bound_concrete (C : Finset (ι → F)) (r : ℕ) :
    (C.card * (∑ i ∈ Finset.range (r + 1),
      (Fintype.card ι).choose i * (Fintype.card F - 1) ^ i)) ^ 2
      ≤ (Finset.univ.filter (fun f => 1 ≤ (lam C r f).card)).card
          * ∑ f : ι → F, (lam C r f).card ^ 2 := by
  rw [← ballVol_closed]
  exact covering_lower_bound C r

/-- **Concrete linear-code covered-set lower bound.** For a linear code, the concrete covered-set
lower bound uses the closed-form ball volume on the left and the exact weight-enumerator pair-ball
sum for the second moment on the right. -/
theorem covering_lower_bound_linear_concrete {C : Finset (ι → F)}
    (hadd : ∀ a ∈ C, ∀ b ∈ C, a + b ∈ C) (hsub : ∀ a ∈ C, ∀ b ∈ C, a - b ∈ C) (r : ℕ) :
    (C.card * (∑ i ∈ Finset.range (r + 1),
      (Fintype.card ι).choose i * (Fintype.card F - 1) ^ i)) ^ 2
      ≤ (Finset.univ.filter (fun f => 1 ≤ (lam C r f).card)).card
          * (C.card • ∑ v ∈ C,
            (Finset.univ.filter
              (fun g => hammingDist (0 : ι → F) g ≤ r ∧ hammingDist v g ≤ r)).card) := by
  rw [← ballVol_closed]
  exact covering_lower_bound_linear hadd hsub r

#print axioms ballVol_closed
#print axioms exists_large_list_concrete
#print axioms covering_lower_bound_concrete
#print axioms covering_lower_bound_linear_concrete

end ArkLib.CodingTheory.ListMoments
