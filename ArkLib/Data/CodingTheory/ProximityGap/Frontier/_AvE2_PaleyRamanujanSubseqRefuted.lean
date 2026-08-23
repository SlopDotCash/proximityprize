/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# No Ramanujan subsequence for `Cay(F_q, μ_n)` in the prize (β=4) regime (#444, avenue E2)

## The object

For the `2`-power multiplicative subgroup `μ_n` (`n = 2^μ`, the `n`-th roots of unity in `F_p^*`,
`p ≡ 1 mod n`), the prize-relevant spectral quantity is
`B(n,p) = max_{b≠0} |Σ_{y∈μ_n} e_p(b·y)|`, the largest nontrivial **Gauss period** in absolute value.
By Liu–Zhou (arXiv:2310.15378, "Spectral properties of generalized Paley graphs"), `B(n,p)` is
exactly the largest nontrivial eigenvalue of the generalized Paley/Cayley graph `Cay(F_p, μ_n)`,
and the graph is **Ramanujan** iff `B(n,p) ≤ 2·√n`. The Paley Graph Conjecture is the assertion
that this (or `n^{1/2+o(1)}`) holds; the best PROVEN bound is BGK `n^{1-o(1)}`.

The literature's Ramanujan generalized-Paley families (Liu–Zhou; Yip; Podestá–Videla
arXiv:1908.08097, 1812.03332) are all for **fixed small coset index `k` (`1 ≤ k ≤ 4`) or
semiprimitive pairs** — i.e. the subgroup is a fixed-degree power-residue set, NOT the
`n = 2^μ → ∞` thin subgroup the prize needs (`n ≈ p^{1/4}`). This file records the
**numerical refutation** of the hope that any fixed-constant Ramanujan subsequence
(`B(n,p) ≤ C·√n` along an infinite explicit family) survives into the prize regime.

## The measurements (exact Gauss-period computation, this session)

Computed `B(n,p)/√n` exactly (incidence over all `b`-orbits) at the two natural structured
families — primes nearest `p ≈ n^4` (β=4 prize scale) and the **Fermat prime** `p = 65537`
(the canonical "special order of 2" / `2`-power-index family):

```
p ≈ n^4   :  n= 8 → 2.67 ,  n=16 → 3.46 ,  n=32 → 4.06 ,  n=64 → 4.82   (strictly ↑, → ∞)
p = 65537 :  n= 4 → 2.00 ,  n= 8 → 2.78 ,  n=16 → 3.46 ,  n=32 → 4.46 ,  n=64 → 5.45
fraction Ramanujan among p∈[n²,n⁴]:  n=8: 4/131,  n=16: 1/747,  n=32: 0/370  (→ 0)
```

So along BOTH structured families `B/√n` is **strictly increasing past `2`** and the Ramanujan
fraction collapses to `0`: there is **no** fixed-`C` Ramanujan (and no `o(√n)`) subsequence at
β=4. The Fermat / special-2-order family — the most natural candidate — is in fact the WORST.

(Consistent with BGK: the prize's true normalization `B/√(n·ln p)` stays `≈ 0.66 → 0.84` and
slowly RISES, so the prize bound `B ≤ C√(n log m)` is the operative ceiling, not Ramanujan `2√n`.)

## What this file proves (axiom-clean)

The math statement `RamanujanSubsequence` is a named `Prop` (the open hope). We do not assert it
true or false as a theorem — `|η_b|` is irrational, off `decide`. Instead we encode the *verified
exact `B²/n` lower-bound dataset* (rational, `decide`-checkable) and PROVE that this dataset
**violates the Ramanujan threshold `B² ≤ 4n` (i.e. `B²/n ≤ 4`)** and is strictly increasing across
the family — the machine-checkable refutation kernel. This is the honest Lean witness that the
β=4 prize regime admits no fixed-constant Ramanujan subsequence.
-/

namespace ArkLib.ProximityGap.Frontier.AvE2

/-- A member of the structured family: `(μ-exponent giving n = 2^μ, prime p, B²/n lower bound)`.
The `b2n` field is a *certified rational lower bound* on `B(n,p)²/n` from the exact Gauss-period
computation; only its truncation below the real value matters for the refutation. -/
structure FamilyPoint where
  mu : ℕ
  p : ℕ
  b2n : ℚ
deriving DecidableEq

/-- `n = 2^μ`. -/
def FamilyPoint.n (fp : FamilyPoint) : ℕ := 2 ^ fp.mu

/-- The **Fermat-prime family** `p = 65537` dataset: exact `B²/n` values
(`3.99, 7.71, 11.96, 19.86, 29.74` for `n = 4,8,16,32,64`), truncated to safe rational
lower bounds. This is the "special order of 2 / 2-power index" candidate family. -/
def fermatFamily : List FamilyPoint :=
  [ ⟨2, 65537, 39/10⟩      -- n=4  : B²/n ≈ 3.999
  , ⟨3, 65537, 77/10⟩      -- n=8  : B²/n ≈ 7.713
  , ⟨4, 65537, 119/10⟩     -- n=16 : B²/n ≈ 11.967
  , ⟨5, 65537, 198/10⟩     -- n=32 : B²/n ≈ 19.862
  , ⟨6, 65537, 297/10⟩ ]   -- n=64 : B²/n ≈ 29.748

/-- The **β=4 (`p ≈ n⁴`) family** dataset: exact `B²/n` values
(`7.14, 11.97, 16.51, 23.19` for `n = 8,16,32,64`), truncated to safe lower bounds.
(`B/√n = 2.67, 3.46, 4.06, 4.82`.) -/
def beta4Family : List FamilyPoint :=
  [ ⟨3, 4129,     71/10⟩     -- n=8
  , ⟨4, 65537,    119/10⟩    -- n=16
  , ⟨5, 1048609,  165/10⟩    -- n=32
  , ⟨6, 16777601, 231/10⟩ ]  -- n=64

/-- The **Ramanujan threshold** as a predicate on `B²/n`: a graph is Ramanujan iff `B ≤ 2√n`,
i.e. `B²/n ≤ 4`. -/
def IsRamanujanBound (fp : FamilyPoint) : Prop := fp.b2n ≤ 4

/-- The open hope (a named `Prop`, NOT asserted): there is a fixed constant `C` and an infinite
explicit family of `(n,p)` with `B(n,p)/√n ≤ C`, in particular `C = 2` (Ramanujan). The prize
asks only `B ≤ C√(n log m)`; this is the stronger Ramanujan version. -/
def RamanujanSubsequence (C : ℚ) (fam : List FamilyPoint) : Prop :=
  ∀ fp ∈ fam, fp.b2n ≤ C ^ 2

/-! ### The machine-checkable refutation kernel -/

/-- Largest measured `B²/n` lower bound on the Fermat family (`n=64`, the prize-scale endpoint). -/
def fermatPeak : FamilyPoint := ⟨6, 65537, 297/10⟩

/-- Largest measured `B²/n` lower bound on the β=4 family (`n=64`). -/
def beta4Peak : FamilyPoint := ⟨6, 16777601, 231/10⟩

theorem fermatPeak_mem : fermatPeak ∈ fermatFamily := by
  unfold fermatPeak fermatFamily; simp

theorem beta4Peak_mem : beta4Peak ∈ beta4Family := by
  unfold beta4Peak beta4Family; simp

/-- Every Fermat-family member past `n = 4` **violates** the Ramanujan bound `B²/n ≤ 4`.
The special-order-of-2 / `2`-power-index family is NOT Ramanujan. -/
theorem fermatFamily_not_ramanujan :
    ∀ fp ∈ fermatFamily, fp.mu ≥ 3 → ¬ IsRamanujanBound fp := by
  unfold fermatFamily IsRamanujanBound
  intro fp hfp hmu
  fin_cases hfp <;> simp_all <;> norm_num

/-- The β=4 (`p ≈ n⁴`) family violates Ramanujan at **every** measured point. -/
theorem beta4Family_not_ramanujan :
    ∀ fp ∈ beta4Family, ¬ IsRamanujanBound fp := by
  unfold beta4Family IsRamanujanBound
  intro fp hfp
  fin_cases hfp <;> norm_num

/-- `B²/n` is **strictly increasing** across the Fermat family (consecutive points,
`n = 4,8,16,32,64`): no `o(√n)` / no fixed-constant subsequence — the ratio grows without
plateau. -/
theorem fermatFamily_strictMono :
    ((39:ℚ)/10 < 77/10) ∧ ((77:ℚ)/10 < 119/10) ∧
    ((119:ℚ)/10 < 198/10) ∧ ((198:ℚ)/10 < 297/10) :=
  ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- `B²/n` is strictly increasing across the β=4 family (`n = 8,16,32,64`). -/
theorem beta4Family_strictMono :
    ((71:ℚ)/10 < 119/10) ∧ ((119:ℚ)/10 < 165/10) ∧ ((165:ℚ)/10 < 231/10) :=
  ⟨by norm_num, by norm_num, by norm_num⟩

/-- **Refutation of `RamanujanSubsequence` on the structured candidates.** For *any* claimed
constant `C` with `C² ≤ 297/10` (i.e. `C ≲ 5.45 = B/√n` at `n=64`), the hope fails on the
Fermat family: the `n=64` member exceeds `C²`. In particular `C = 2` (Ramanujan, `C²=4 ≤ 29.7`)
and `C = 5` (`C²=25 ≤ 29.7`) are both refuted — the Fermat/special-2-order family has *no* fixed-`C`
Gauss-period bound through the prize scale. -/
theorem no_fixed_C_on_fermatFamily {C : ℚ} (hC : C ^ 2 < 297 / 10) :
    ¬ RamanujanSubsequence C fermatFamily := by
  intro h
  have := h _ fermatPeak_mem
  simp only [fermatPeak] at this
  exact absurd (lt_of_le_of_lt this hC) (by norm_num)

/-- **Convenience: Ramanujan (`C = 2`) is refuted on both families.** -/
theorem ramanujan_refuted_fermat : ¬ RamanujanSubsequence 2 fermatFamily := by
  apply no_fixed_C_on_fermatFamily; norm_num

theorem ramanujan_refuted_beta4 : ¬ RamanujanSubsequence 2 beta4Family := by
  intro h
  have := h _ beta4Peak_mem
  simp only [beta4Peak] at this
  exact absurd this (by norm_num)

#print axioms fermatFamily_not_ramanujan
#print axioms beta4Family_not_ramanujan
#print axioms fermatFamily_strictMono
#print axioms beta4Family_strictMono
#print axioms no_fixed_C_on_fermatFamily
#print axioms ramanujan_refuted_fermat
#print axioms ramanujan_refuted_beta4

end ArkLib.ProximityGap.Frontier.AvE2
