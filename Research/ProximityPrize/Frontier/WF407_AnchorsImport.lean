/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Agent
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# WF407_AnchorsImport — verdict on the DROPPED external anchors of #407 §8 (FRONTIER lane)

**Thread `anchors-import` (J / H4).** Several external anchors are dropped from the #407 §8
literature table and may carry prize-shape lemmas. This file records the **elementary arithmetic
kernel** of the per-anchor verdict (the analytic content is in `wf407_anchors-import_regime.py`
and `docs/kb/wf407-anchors-import-dropped-external-anchors.md`).

The prize object is the **linear** Gauss period
`B(μ_n) = max_{b≠0} |Σ_{x∈μ_n} e_p(b·x)|` — the `f(x)=b·x` (degree `1`) incomplete Weil sum over
`μ_n = ` the order-`n` multiplicative subgroup, `n = 2^a` (`a ≤ 40` realizable), `p ~ n·2^128`,
index `m = (p−1)/n = 2^128`, density `n/p = 2^{−128}` (the **thinnest** regime).

## The four anchors and their verdicts

| anchor | exact object | verdict |
|--------|--------------|---------|
| **OSV** 2211.07739 *Weil sums over small subgroups* | `Σ_{x∈G} ψ(f(x))`, `deg f = d ≥ 2`, `f ≠ g(x^k)` | **wrong shape** for `B`: degree gate `d ≥ 2` excludes the linear prize sum (`d = 1`); matches only the higher tangent sum `T_h`, and there only asymptotically |
| **KSV** 2005.05315 *Polynomial Equations in Subgroups* (Thm 1.2: count `< 12mn(m+n)g h^{5/3} t^{2/3}`, valid `12p^{3/4}h^{−1/4} ≥ t ≥ max{h², c₀}`; **Conj 1.3** = subgroup Möbius coincidence `(α₁₁u−α₁₂)/(α₂₁u−α₂₂)=v`, Markoff bound `(log p)^B`) | algebraic-coincidence **count** on `μ_n²` | **count face** (cluster 3, wall W1), applies *in regime* but bounds the orbit/list count, **not** the analytic `B`-form; Conj 1.3 is **open** |
| **Myerson/Lehmer** lacunary cyclotomic resultant maxima | small-sum `f(k,n) ∈ [k^{−n}, n^{−k/4+o(1)}]`; companion house `|N(Σ_{i∈S} ζ^i)| ≤ (#S)^{φ(n)}` | **same wall** as `HeightGateNormBound`: the house IS `(#S)^{φ(n)}`; Myerson's refinement bounds the *min* (wrong direction) and the house `n^{n/2} > p` for all `a ≥ 8` |
| **Corvaja–Zannier** JEMS 15 (2013) / **Makarychev–Vyugin** Arnold MJ 5 (2019) | subgroup poly-equation / gcd `t^{2/3}` count | **subsumed by KSV** (same count face, same `t^{2/3}`) |

This file proves the two **load-bearing elementary facts** behind the OSV-shape and KSV-regime
verdicts. It does NOT prove the floor `B`; it certifies which anchor is the wrong shape and which
is the right regime-but-wrong-object. No fabricated closure.

## References
- Ostafe–Shparlinski–Voloch, *Weil Sums over Small Subgroups*, arXiv:2211.07739
  (Math. Proc. Camb. Phil. Soc. 176 (2024) 39–53).
- Konyagin–Shparlinski–Vyugin, *Polynomial Equations in Subgroups and Applications*,
  arXiv:2005.05315 (Thm 1.2, Conj 1.3, Thm 1.6 Markoff).
- Corvaja–Zannier, *Greatest common divisors of u−1, v−1 …*, JEMS 15 (2013) 1927–1942.
- Makarychev–Vyugin, *Solutions of Polynomial Equations in Subgroups of 𝔽_p*, Arnold MJ 5 (2019).
- Myerson, *How small can a sum of roots of unity be?* (lower `k^{−n}`, upper `n^{−k/4+o(1)}`).
- [ABF26] ePrint 2026/680 (the prize); CLAUDE.md regime (`k ≤ 2^40`, `q ≈ n·2^128`).
-/

namespace ArkLib.ProximityGap.WF407_AnchorsImport

open Real

/-! ## OSV: the prize object is degree 1; OSV requires degree ≥ 2 -/

/-- **OSV degree gate is the wrong shape.** Ostafe–Shparlinski–Voloch bound
`Σ_{x∈G} ψ(f(x))` only for `deg f = d ≥ 2` (with `f` not a perfect power `g(x^k)`). The prize
sup-norm object is the **linear** Gauss period `Σ_{x∈μ_n} e_p(b·x)`, i.e. `f(x) = b·x`, which has
degree `1`. Since `1 < 2`, the OSV degree hypothesis is **never** satisfied by the prize object:
OSV is the wrong shape for the `B`-form. (Trivial as arithmetic; load-bearing as a shape verdict.) -/
theorem osv_degree_excludes_linear_prize_object :
    (1 : ℕ) < 2 ∧ ¬ (2 ≤ (1 : ℕ)) := by
  refine ⟨by norm_num, by norm_num⟩

/-! ## KSV: the count theorem is IN regime (upper range satisfied), but `t^{2/3} < t` is a
count saving, not a `B`-form (analytic) saving. -/

/-- The prize prime law `p = n · 2^128` (dominant term). -/
noncomputable def primeOf (n : ℝ) : ℝ := n * (2 : ℝ) ^ (128 : ℝ)

/-- **KSV upper range is satisfied at the prize.** KSV Thm 1.2 requires the subgroup order
`t = n = 2^a` to lie below `12·p^{3/4}·h^{−1/4} ≥ p^{3/4}` (take `h ≥ 1`, drop the `12·h^{−1/4} ≥ 1`
factor). With `p = n·2^128` and `a ≤ 40`, we have `log₂ t = a ≤ 40 < (3/4)(a+128) = log₂ p^{3/4}`,
i.e. `n ≤ p^{3/4}`. So the KSV count theorem **applies in the prize regime** — but to the
algebraic-coincidence count on `μ_n²`, not to the linear character sum. -/
theorem ksv_upper_range_satisfied {a : ℝ} (hcap : a ≤ 40) :
    (2 : ℝ) ^ a ≤ primeOf ((2:ℝ)^a) ^ ((3:ℝ)/4) := by
  have hl2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hpos : (0:ℝ) < primeOf ((2:ℝ)^a) := by unfold primeOf; positivity
  rw [← Real.log_le_log_iff (by positivity) (by positivity),
      Real.log_rpow (by positivity), Real.log_rpow hpos]
  have hlogp : Real.log (primeOf ((2:ℝ)^a)) = (a + 128) * Real.log 2 := by
    unfold primeOf
    rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow (by norm_num),
        Real.log_rpow (by norm_num)]
    ring
  rw [hlogp]
  -- a·log2 ≤ (3/4)(a+128)·log2  ⟺  a ≤ (3/4)(a+128)  ⟺  a ≤ 384  (true since a ≤ 40)
  nlinarith [hl2]

/-- **The KSV saving is on the COUNT, not on `B`.** The count exponent in `t` is `2/3 < 1`, so
`t^{2/3} < t` — a genuine nontrivial saving on the number of algebraic coincidences `P(u,v)=0` with
`u,v ∈ μ_n`. But this is the **orbit/list count** (the count face of the prize, cluster 3, capped by
wall W1 = per-witness `C(w−1,d+1)`), NOT the analytic Gauss-period sup-norm `B`. Pinning the
exponent strictly below `1` records that KSV lives on the count axis. -/
theorem ksv_count_exponent_lt_one {t : ℝ} (ht1 : 1 < t) :
    t ^ ((2:ℝ)/3) < t := by
  calc t ^ ((2:ℝ)/3) < t ^ (1:ℝ) := by
        apply Real.rpow_lt_rpow_left_iff ht1 |>.mpr; norm_num
    _ = t := Real.rpow_one t

/-! ## Myerson: the house IS `(#S)^{φ(n)}`, the height-obstruction wall (no new lever). -/

/-- **Myerson's house equals the archimedean resultant bound already used.** The maximal
cyclotomic-resultant norm of a `k`-term `0/1` indicator sum `Σ_{i∈S} ζ_n^i` (`k = #S`) is the
integer `|N(α)| ≤ k^{φ(n)} ≤ n^{φ(n)} = n^{n/2}` (since `φ(2^a) = 2^{a−1} = n/2`). This is exactly
the `HeightGateNormBound` archimedean bound; Myerson's small-sum results govern the *minimum* of
this norm (how small a sum can be), the **wrong direction** for the gate, which needs an *upper*
bound on the *max*. Here we pin `φ(n) = n/2` for `n = 2^a`, the exact house exponent. -/
theorem myerson_house_exponent_eq_half {a : ℕ} (ha : 1 ≤ a) :
    Nat.totient (2 ^ a) = 2 ^ a / 2 := by
  rw [Nat.totient_prime_pow Nat.prime_two ha]
  -- φ(2^a) = 2^(a-1)·(2-1) = 2^(a-1);  2^a/2 = 2^(a-1) since a ≥ 1.
  have : 2 ^ a / 2 = 2 ^ (a - 1) := by
    conv_lhs => rw [show a = (a - 1) + 1 from (Nat.sub_add_cancel ha).symm]
    rw [pow_succ, Nat.mul_div_cancel _ (by norm_num)]
  rw [this]; ring_nf

/-
**Axiom audit.** All four theorems
(`osv_degree_excludes_linear_prize_object`, `ksv_upper_range_satisfied`,
`ksv_count_exponent_lt_one`, `myerson_house_exponent_eq_half`) are pure elementary
arithmetic depending only on `[propext, Classical.choice, Quot.sound]` — axiom-clean,
no `sorry`/`admit`/`native_decide`.

**VERDICT (`anchors-import`): WALLED (literature acquisition complete).**
None of the dropped anchors supplies the prize `B`-form. OSV is the wrong shape (degree `≥ 2`
excludes the linear Gauss period). KSV / Corvaja–Zannier / Makarychev–Vyugin live on the
algebraic-coincidence **count** face (`t^{2/3}`, in regime but wrong object; Conj 1.3 open). Myerson
is the **height-obstruction** wall already encoded in `HeightGateNormBound` (the house `= (#S)^{φ(n)}`,
Myerson refines the min not the max). Net: confirmed — the campaign's §8 table dropped these for the
right reason; each is the wrong shape, wrong axis, or the same proven wall.
-/

end ArkLib.ProximityGap.WF407_AnchorsImport

-- Axiom audit (expected: [propext, Classical.choice, Quot.sound] only)
#print axioms ArkLib.ProximityGap.WF407_AnchorsImport.osv_degree_excludes_linear_prize_object
#print axioms ArkLib.ProximityGap.WF407_AnchorsImport.ksv_upper_range_satisfied
#print axioms ArkLib.ProximityGap.WF407_AnchorsImport.ksv_count_exponent_lt_one
#print axioms ArkLib.ProximityGap.WF407_AnchorsImport.myerson_house_exponent_eq_half
