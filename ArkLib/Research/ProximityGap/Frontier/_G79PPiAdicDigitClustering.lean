/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Round8CosetConcentration
import Mathlib.Tactic

/-!
# G79P: falling-factorial digit clustering underlying the π-adic depth claim

A NEW exact structure on the prize object, and a sharpening of the valuation-blindness fence
(F3) to an exact depth.  Write `π = ζ_p − 1` (the ramified uniformizer of `ℤ[ζ_p]`,
`v_π(p) = p−1`) and expand each Gauss period by binomials,
`ζ^y = (1+π)^y = Σ_k C(y,k)·π^k`:

```text
η_b − n  =  Σ_{k≥1} c_k(b)·π^k,     c_k(b) = Σ_{x∈μ_n} C(bx mod p, k)  ∈ ℤ.
```

The mod-`p` content of the digit `c_k` is the falling-factorial sum
`k!·c_k ≡ Σ_{x∈μ_n} ∏_{i<k}(bx − i) (mod p)`.  This file PROVES, over any field and any
finite subgroup `H ≤ Fˣ` of order `n` (consumed at `F = 𝔽_p`, `H = μ_n`):

* `sum_polyEval_eq` — for ANY polynomial of degree `≤ n`, the subgroup sum reads exactly the
  constant and top coefficients: `Σ_{x∈H} P(x) = n·P₀ + n·Pₙ`.
* `sum_fallingFactorial_eq_zero` — `Σ_{x∈H} ∏_{i<k}(bx − i) = 0` for `1 ≤ k < n`:
  ALL π-adic digits of `η_b − n` below level `n` vanish mod `p`.
* `sum_fallingFactorial_card_eq` (HEADLINE) — `Σ_{x∈H} ∏_{i<n}(bx − i) = n·bⁿ`:
  the level-`n` digit is EXACTLY `n·bⁿ/n!` mod `p` — nonzero for every `b ≠ 0` at `F = 𝔽_p`
  (`p ∤ n·n!` as `n < p`), and it factors through the COSET character `b ↦ bⁿ`.

Probe `/tmp/arklib-reports/g79_padic_digits_probe.py` verifies (n=8: p=17,41;
n=16: p=97,113,193,257; all b): integer digits `1..n−1` vanish mod p, the level-`n` digit
equals `n·bⁿ/n!` and never vanishes, and the digit stream reconstructs `η_b` to 1e-13.

## The documented corollary (the `ℤ[ζ_p]` bookkeeping, not formalized here)

Since `v_π(c_k·π^k) = (p−1)·v_p(c_k) + k` and `p−1 ≥ n`, digit vanishing below `n` gives
`v_π(η_b − n) ≥ n`, and the nonvanishing level-`n` digit pins

> **`v_π(η_b − n) = n` EXACTLY, uniformly in `b ≠ 0`.**

Consequences.
* **Valuation blindness has exact depth `n`.**  Every Gauss period is `π`-adically
  indistinguishable from its DC value `n` to depth `n`; any `p`-adic/valuation functional
  reading precision `o(n)` sees all periods as identical, and the FIRST sensitive digit
  reads only the coset label `bⁿ` — never the archimedean size.  This sharpens the F3
  fence (valuation-arch-blindness) from a direction statement to an exact-depth statement:
  the sup norm `M` lives entirely in the digit tail `k ≥ n`, whose head is coset-graded.
* **Discriminant tightness.**  Pairwise `v_π(η_b − η_{b'}) ≥ n` re-derives
  `v_p(disc) ≥ m−1` for the degree-`m` period field — matching the exact
  conductor-discriminant value `p^{m−1}`: the clustering already saturates the
  discriminant, so no further p-adic rigidity hides there.

HONEST SCOPE. An exact structural face plus a proposed fence sharpening—NOT a closure and NOT a
new bound on `M`. The falling-factorial identities are axiom-clean over any field. The π-adic
packaging, including the binomial-series bridge and `v_π(p) = p−1`, is documented arithmetic and
is not a Lean theorem in this file. CORE remains OPEN / ON-BGK.

Issue #466.  Target axiom set: `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.Frontier.G79PiAdicDigitClustering

open Finset Polynomial
open ArkLib.ProximityGap.Round8CosetConcentration

variable {F : Type*} [Field F] [DecidableEq F]

/-- Level-`n` power sum: on a subgroup of order `n`, `Σ_{x∈H} xⁿ = n` (each term is `1`). -/
theorem sum_pow_card_eq_card (H : Subgroup Fˣ) [Fintype H] :
    ∑ x ∈ sgFinset H, x ^ (Fintype.card H) = (Fintype.card H : F) := by
  classical
  unfold sgFinset
  rw [Finset.sum_image (by
    intro a _ b _ h
    simp only at h
    exact Subtype.ext (Units.ext h))]
  have hone : ∀ u : H, ((u : Fˣ) : F) ^ (Fintype.card H) = 1 := by
    intro u
    have hu : u ^ (Fintype.card H) = 1 := pow_card_eq_one
    have h2 : (u : Fˣ) ^ (Fintype.card H) = 1 := by
      calc (u : Fˣ) ^ (Fintype.card H) = ((u ^ (Fintype.card H) : H) : Fˣ) := by norm_cast
        _ = 1 := by rw [hu]; rfl
    rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
  rw [Finset.sum_congr rfl (fun u _ => hone u)]
  simp

/-- **The subgroup sum reads exactly the constant and top coefficients**: for `deg P ≤ n`,
`Σ_{x∈H} P(x) = n·P₀ + n·Pₙ` (`n = |H|`; the interior monomial sums vanish). -/
theorem sum_polyEval_eq (H : Subgroup Fˣ) [Fintype H]
    (P : Polynomial F) (hdeg : P.natDegree ≤ Fintype.card H) :
    ∑ x ∈ sgFinset H, P.eval x =
      (Fintype.card H : F) * P.coeff 0 +
        (Fintype.card H : F) * P.coeff (Fintype.card H) := by
  classical
  have hnpos : 0 < Fintype.card H := Fintype.card_pos
  have heval : ∀ x : F, P.eval x =
      ∑ j ∈ range (Fintype.card H + 1), P.coeff j * x ^ j :=
    fun x => P.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg) x
  rw [Finset.sum_congr rfl fun x _ => heval x, Finset.sum_comm, Finset.sum_range_succ]
  have hg : ∀ j ∈ range (Fintype.card H),
      (∑ x ∈ sgFinset H, P.coeff j * x ^ j) =
        if j = 0 then (Fintype.card H : F) * P.coeff 0 else 0 := by
    intro j hj
    rw [← Finset.mul_sum]
    by_cases hj0 : j = 0
    · subst hj0
      rw [if_pos rfl]
      have hsum : (∑ x ∈ sgFinset H, x ^ (0 : ℕ)) = ((sgFinset H).card : F) := by
        simp
      rw [hsum, sgFinset_card]
      ring
    · rw [if_neg hj0,
        sgFinset_sum_pow_eq_zero H hj0 (Finset.mem_range.mp hj), mul_zero]
  have htop : (∑ x ∈ sgFinset H, P.coeff (Fintype.card H) * x ^ (Fintype.card H)) =
      (Fintype.card H : F) * P.coeff (Fintype.card H) := by
    rw [← Finset.mul_sum, sum_pow_card_eq_card H]
    ring
  rw [Finset.sum_congr rfl hg, htop, Finset.sum_ite_eq' (range (Fintype.card H)) 0
    (fun _ => (Fintype.card H : F) * P.coeff 0),
    if_pos (Finset.mem_range.mpr hnpos)]

/-- The dilated falling-factorial polynomial `∏_{i<k} (b·X − i)`. -/
noncomputable def fallingPoly (b : F) (k : ℕ) : Polynomial F :=
  ∏ i ∈ range k, (Polynomial.C b * Polynomial.X - Polynomial.C (i : F))

theorem fallingPoly_eval (b x : F) (k : ℕ) :
    (fallingPoly b k).eval x = ∏ i ∈ range k, (b * x - (i : F)) := by
  unfold fallingPoly
  rw [Polynomial.eval_prod]
  exact Finset.prod_congr rfl fun i _ => by simp

theorem fallingPoly_natDegree_le (b : F) (k : ℕ) :
    (fallingPoly b k).natDegree ≤ k := by
  unfold fallingPoly
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  have hfac : ∀ i ∈ range k,
      (Polynomial.C b * Polynomial.X - Polynomial.C (i : F)).natDegree ≤ 1 := by
    intro i _
    refine (Polynomial.natDegree_sub_le _ _).trans ?_
    refine max_le ((Polynomial.natDegree_C_mul_le _ _).trans (by simp)) ?_
    simp
  refine le_trans (Finset.sum_le_sum hfac) ?_
  simp

/-- The falling factorial has zero constant term for `k ≥ 1` (the `i = 0` factor). -/
theorem fallingPoly_coeff_zero (b : F) (k : ℕ) (hk : k ≠ 0) :
    (fallingPoly b k).coeff 0 = 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, fallingPoly_eval]
  refine Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.pos_of_ne_zero hk)) ?_
  simp

/-- Monic normalization: for `b ≠ 0`, `fallingPoly b k = C(bᵏ) · ∏_{i<k}(X − C(i/b))`. -/
theorem fallingPoly_eq_C_mul_monic (b : F) (hb : b ≠ 0) (k : ℕ) :
    fallingPoly b k =
      Polynomial.C (b ^ k) *
        ∏ i ∈ range k, (Polynomial.X - Polynomial.C ((i : F) * b⁻¹)) := by
  unfold fallingPoly
  have hfac : ∀ i ∈ range k,
      Polynomial.C b * Polynomial.X - Polynomial.C (i : F) =
        Polynomial.C b * (Polynomial.X - Polynomial.C ((i : F) * b⁻¹)) := by
    intro i _
    rw [mul_sub, ← Polynomial.C_mul]
    congr 2
    field_simp
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const,
    Polynomial.C_pow]
  simp [Finset.card_range]

/-- The top coefficient of the level-`k` falling factorial is `bᵏ`. -/
theorem fallingPoly_coeff_top (b : F) (k : ℕ) :
    (fallingPoly b k).coeff k = b ^ k := by
  by_cases hb : b = 0
  · subst hb
    by_cases hk : k = 0
    · subst hk
      simp [fallingPoly]
    · have h0 : fallingPoly (0 : F) k = 0 := by
        unfold fallingPoly
        refine Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.pos_of_ne_zero hk)) ?_
        simp
      rw [h0, zero_pow hk]
      simp
  · rw [fallingPoly_eq_C_mul_monic b hb k, Polynomial.coeff_C_mul]
    have hmonic : (∏ i ∈ range k,
        (Polynomial.X - Polynomial.C ((i : F) * b⁻¹))).Monic :=
      Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
    have hdeg : (∏ i ∈ range k,
        (Polynomial.X - Polynomial.C ((i : F) * b⁻¹))).natDegree = k := by
      rw [Polynomial.natDegree_prod_of_monic _ _
        (fun i _ => Polynomial.monic_X_sub_C _)]
      calc
        ∑ i ∈ range k, (Polynomial.X - Polynomial.C ((i : F) * b⁻¹)).natDegree =
            ∑ _i ∈ range k, 1 := by
          apply Finset.sum_congr rfl
          intro i _
          exact Polynomial.natDegree_X_sub_C _
        _ = k := by simp
    have hcoeff : (∏ i ∈ range k,
        (Polynomial.X - Polynomial.C ((i : F) * b⁻¹))).coeff k = 1 := by
      have := hmonic.coeff_natDegree
      rw [hdeg] at this
      exact this
    rw [hcoeff, mul_one]

/-- **Digit vanishing below level `n`**: `Σ_{x∈H} ∏_{i<k}(bx − i) = 0` for `1 ≤ k < |H|`.
Up to the unit `k!`, these are the π-adic digits of `η_b − n` below level `n`: all zero
mod `p`, for every `b`. -/
theorem sum_fallingFactorial_eq_zero (H : Subgroup Fˣ) [Fintype H]
    (b : F) (k : ℕ) (hk : k ≠ 0) (hlt : k < Fintype.card H) :
    ∑ x ∈ sgFinset H, ∏ i ∈ range k, (b * x - (i : F)) = 0 := by
  have h := sum_polyEval_eq H (fallingPoly b k)
    (le_of_lt (lt_of_le_of_lt (fallingPoly_natDegree_le b k) hlt))
  have hcoefftop : (fallingPoly b k).coeff (Fintype.card H) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (fallingPoly_natDegree_le b k) hlt)
  rw [fallingPoly_coeff_zero b k hk, hcoefftop, mul_zero, add_zero] at h
  rw [← Finset.sum_congr rfl (fun x _ => fallingPoly_eval b x k)]
  exact h

/-- **HEADLINE: the level-`n` digit is exactly `n·bⁿ`** (before the `1/n!` unit):
`Σ_{x∈H} ∏_{i<n}(bx − i) = n·bⁿ`, `n = |H|`.  At `F = 𝔽_p` this is nonzero for every
`b ≠ 0` and factors through the coset character `b ↦ bⁿ`: the first `π`-adic digit at which
Gauss periods separate carries exactly the coset label — and nothing else. -/
theorem sum_fallingFactorial_card_eq (H : Subgroup Fˣ) [Fintype H] (b : F) :
    ∑ x ∈ sgFinset H, ∏ i ∈ range (Fintype.card H), (b * x - (i : F)) =
      (Fintype.card H : F) * b ^ (Fintype.card H) := by
  have h := sum_polyEval_eq H (fallingPoly b (Fintype.card H))
    (fallingPoly_natDegree_le b (Fintype.card H))
  have hnpos : 0 < Fintype.card H := Fintype.card_pos
  rw [fallingPoly_coeff_zero b (Fintype.card H) (Nat.pos_iff_ne_zero.mp hnpos),
    fallingPoly_coeff_top b (Fintype.card H), mul_zero, zero_add] at h
  rw [← Finset.sum_congr rfl (fun x _ => fallingPoly_eval b x (Fintype.card H))]
  exact h

end ArkLib.ProximityGap.Frontier.G79PiAdicDigitClustering

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G79PiAdicDigitClustering.sum_pow_card_eq_card
#print axioms
  ArkLib.ProximityGap.Frontier.G79PiAdicDigitClustering.sum_polyEval_eq
#print axioms
  ArkLib.ProximityGap.Frontier.G79PiAdicDigitClustering.sum_fallingFactorial_eq_zero
#print axioms
  ArkLib.ProximityGap.Frontier.G79PiAdicDigitClustering.sum_fallingFactorial_card_eq
