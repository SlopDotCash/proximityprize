/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
/-
P7-HGG: Helleseth–Golomb–Gong cross-correlation vs the prize incomplete Gauss sum.

CLAIM (P7, the named candidate non-CA route from ePrint 2026/858): the proximity-prize
period is a Gauss-sum-sequence correlation peak; HGG / Sidelnikov / decimation cross-
correlation theory delivers the Ramanujan-scale sup-norm
    M(mu_n) = max_{b != 0} | sum_{x in mu_n} e_p(b x) | <= sqrt(2 n log m),
pinning delta*.

VERDICT: **NO-GAIN / REDUCES-TO-BGK.**  HGG cross-correlation delivers genuine
sqrt(N) square-root cancellation, but N is the period of a COMPLETE trace sum over the
FULL field F_{p^n}^x (the Weil/Sidelnikov regime: sqrt of the GROUP SUMMED OVER), NOT
the prize's INCOMPLETE sum over a THIN subgroup mu_n of the PRIME field F_p.

WHAT HGG ACTUALLY BOUNDS (arXiv:2407.16072, Helleseth–Gong / Golomb–Gong lineage):
  C_d(tau) = sum_{x in F_{p^n}^x} omega^{Tr(c x) - Tr(x^d)},   omega = e^{2 pi i / p},
  Tr the absolute trace to F_p, d coprime to N = p^n - 1, sum over the FULL group.
  Sharp 3-valued spectra (Gold/Kasami-Welch p=2; Trachtenberg-Helleseth general p):
    C_d in { -1, -1 +- p^{(n+e)/2} },  so  C_max ~ p^{(n+e)/2} ~ sqrt(N).        (HGG)
  STRONGEST FORM (Niho reduction, Lemma 4): C_d(tau)+1 = (N(a)-1) p^m, where N(a) <= 2s-1
  counts roots of a FIXED low-degree equation on the norm-1 'unit circle'
    U = { x in F_{p^{2m}} : x * x^{p^m} = 1 },  |U| = p^m + 1 ~ sqrt(ambient).

TWO STRUCTURAL OBSTRUCTIONS (numerically pinned in
  scripts/probes/probe_p7_hgg_crosscorr_vs_period.py and
  scripts/probes/probe_p7_hgg_niho_normsubgroup.py):

 (O1) FIELD/COMPLETION MISMATCH.  sqrt(N) is sqrt of the AMBIENT field.  In the prize
      regime p ~ n^beta, beta in [4,5], the would-be HGG bound is sqrt(p) = n^{beta/2}
      = n^{2..2.5}, which EXCEEDS the trivial subgroup bound n.  Vacuous.            (probe)
 (O2) ASPECT-RATIO INCOMPATIBILITY.  HGG's solvable structure (bounded #roots of a
      fixed-degree equation) lives on the norm subgroup U at relative dimension
      log_ambient(|U|) = 1/2 (half-dimension).  The prize subgroup is THIN:
      log_p(n) = 1/beta in [1/5, 1/4] < 1/2.  A thin subgroup is NOT a norm-1 subgroup;
      HGG's sqrt(N)-cancellation = sqrt of U's own ambient = no thin-subgroup gain.

The lemmas below formalize the arithmetic facts that make the no-go rigorous.
The analytic sqrt(N) facts are cited from HGG (above) and the two probes.
-/
import Mathlib.Tactic

namespace P7HGG

/-! ### O1 — the HGG/Weil complete-sum scale `sqrt p` is not below the trivial bound `n`.

HGG square-root cancellation bounds a COMPLETE sum at the AMBIENT scale `sqrt p`.
For a thin subgroup `mu_n` (`n^2 ≤ p`, certainly true for the prize `n ≤ p^{1/4}`) the
complete scale `sqrt p` is at least `n`, i.e. it never improves on the trivial subgroup
bound `M ≤ n`.  Hence HGG delivers no usable subgroup gain in the prize regime. -/

/-- The HGG/Weil complete-sum scale dominates the trivial subgroup bound: if the subgroup
is thin (`n^2 ≤ p`) then `n ≤ sqrt p`. -/
theorem hgg_complete_bound_vacuous
    (n p : ℕ) (hthin : n ^ 2 ≤ p) :
    n ≤ Nat.sqrt p := by
  rw [Nat.le_sqrt']
  simpa [pow_two] using hthin

/-- **Strict O1, in the genuine prize regime.**  When `p` exceeds `(n+1)^2` — which holds
with enormous room in the prize band `p ~ n^beta`, `beta ∈ [4,5]` (there `p = n^4 ≥
(n+1)^2` for all `n ≥ 2`) — the HGG complete scale `sqrt p` STRICTLY exceeds `n`, so it is
strictly worse than the trivial bound.  This quantifies "vacuous": HGG's sqrt-cancellation
cannot even match the trivial subgroup bound in the prize regime. -/
theorem hgg_complete_bound_strictly_worse
    (n p : ℕ) (hbeta : (n + 1) ^ 2 ≤ p) :
    n < Nat.sqrt p := by
  have : n + 1 ≤ Nat.sqrt p := by
    rw [Nat.le_sqrt']; simpa [pow_two] using hbeta
  omega

/-- The prize aspect `p = n^4` (`beta = 4`, the lower edge of the prize band) does satisfy
the strict hypothesis for all `n ≥ 2`: `(n+1)^2 ≤ n^4`. -/
theorem prize_beta4_satisfies_strict
    (n : ℕ) (hn : 2 ≤ n) :
    (n + 1) ^ 2 ≤ n ^ 4 := by
  have h1 : n ^ 2 ≤ n ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  nlinarith [hn, h1, Nat.mul_le_mul hn hn]

/-- Hence at `beta = 4` the HGG complete scale strictly exceeds the trivial bound `n`. -/
theorem hgg_vacuous_at_beta4
    (n : ℕ) (hn : 2 ≤ n) :
    n < Nat.sqrt (n ^ 4) :=
  hgg_complete_bound_strictly_worse n (n ^ 4) (prize_beta4_satisfies_strict n hn)

/-! ### O2 — a thin subgroup is not the norm-1 ("unit circle") subgroup HGG uses.

HGG's strongest mechanism (Niho reduction) lives on the norm-1 subgroup
`U = {x ∈ F_{p^{2m}} : N(x) = 1}` of order `q + 1` where `q = p^m` and the ambient group
has order `q^2 - 1`.  Thus `|U|^2 = (q+1)^2 ≥ q^2 - 1 = |ambient|`: a norm subgroup is
HALF-DIMENSION (`|U| ≳ sqrt(ambient)`).  A thin subgroup of size `n` with `n^2 < A`
(ambient `A`) therefore CANNOT equal a norm-1 subgroup of that ambient: the thin
constraint `n^2 < A` contradicts the half-dimension identity `(q+1)^2 ≥ A`. -/

/-- Half-dimension identity for the norm-1 subgroup: with `q = p^m`, the unit circle has
order `q + 1`, the ambient (multiplicative) group has order `q^2 - 1`, and
`(q+1)^2 ≥ q^2 - 1` always — i.e. the norm subgroup squared is at least the ambient. -/
theorem norm_subgroup_half_dimension
    (q : ℕ) (hq : 1 ≤ q) :
    q ^ 2 - 1 ≤ (q + 1) ^ 2 := by
  have h1 : q ^ 2 - 1 ≤ q ^ 2 := Nat.sub_le _ _
  nlinarith [h1, Nat.zero_le q]

/-- **O2 — thinness excludes the norm-subgroup identification.**  If a candidate subgroup
of size `n` is thin relative to the ambient `A` in the strict sense `n^2 < A`, then `n`
cannot be the order `q+1` of a norm-1 subgroup of an ambient `A = q^2 - 1` (`q ≥ 2`):
that would force `n^2 = (q+1)^2 ≥ q^2 - 1 = A`, contradicting `n^2 < A`. -/
theorem thin_not_norm_subgroup
    (n q A : ℕ) (hq : 2 ≤ q)
    (hambient : A = q ^ 2 - 1)
    (hnorm : n = q + 1)
    (hthin : n ^ 2 < A) :
    False := by
  subst hambient hnorm
  have hge : q ^ 2 - 1 ≤ (q + 1) ^ 2 := norm_subgroup_half_dimension q (by omega)
  omega

/-- The prize subgroup IS thin in this strict sense at the prize aspect `A = n^4`
(`beta = 4`): `n^2 < n^4` for `n ≥ 2`.  Combined with `thin_not_norm_subgroup`, no prize
subgroup is a norm-1/unit-circle subgroup, so HGG's Niho machinery does not apply. -/
theorem prize_subgroup_thin_strict
    (n : ℕ) (hn : 2 ≤ n) :
    n ^ 2 < n ^ 4 :=
  Nat.pow_lt_pow_right (by omega) (by omega)

end P7HGG

#print axioms P7HGG.hgg_complete_bound_vacuous
#print axioms P7HGG.hgg_complete_bound_strictly_worse
#print axioms P7HGG.prize_beta4_satisfies_strict
#print axioms P7HGG.hgg_vacuous_at_beta4
#print axioms P7HGG.norm_subgroup_half_dimension
#print axioms P7HGG.thin_not_norm_subgroup
#print axioms P7HGG.prize_subgroup_thin_strict
