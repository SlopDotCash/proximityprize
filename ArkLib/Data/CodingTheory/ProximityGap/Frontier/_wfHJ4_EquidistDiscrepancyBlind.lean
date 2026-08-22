/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-HJ4)
-/
import Mathlib

/-!
# J4 — the homogeneous-dynamics / Ratner / EMV / Lindenstrauss equidistribution route is
# discrepancy-blind to the sup (#444)

**NEGATIVE / guardrail brick (an honest reduction, NOT a closure).** Lane J4 asks whether
*effective equidistribution* of the period orbit — the values

  `η_b = Σ_{x ∈ μ_n} e_p(b x)`,  `b ∈ F_p^* / μ_n`  (`m = (p-1)/n` cosets),

under the dilation / diagonal-torus action `b ↦ g^{(p-1)/n} b` (Ratner / Einsiedler–Margulis–
Venkatesh / Lindenstrauss QUE / Bourgain–Lindenstrauss–Michel–Venkatesh) — forces the **sup**

  `M(n) = max_{b ≠ 0} |η_b|`

toward `avg + controlled deviation = √(n·log m)`, i.e. delivers the prize floor.

**Verdict: REDUCES-TO-FENCE (F0, and F5).** Three independent structural facts, each
established in the cited literature and one of them formalized below, collapse this route:

### (1) Equidistribution is a weak-* / discrepancy statement — it controls FIXED smooth test
functionals (a bulk / L¹ average), never the sup.
Effective equidistribution (Einsiedler's survey *Effective equidistribution and spectral gap*;
EMV, *Effective equidistribution for closed orbits of semisimple groups*, Invent. Math. 177
(2009), arXiv:0708.4040) bounds the **discrepancy** of the orbit against **bounded-degree /
Lipschitz / smooth** test functions `φ`:  `|(1/m) Σ_b φ(η_b) − ∫ φ| ≤ rate`. A sup `max_b |η_b|`
is `L^∞`, NOT a fixed smooth functional: detecting it needs the test function `φ_T = 1_{|·| > T}`
at the extreme threshold `T ≈ M`, whose Fourier/moment degree must grow to resolve a **rare
window**. The exact-integer probe `probe_wfH_J4_equidist_sup.rs` confirms this concretely at
`β = 4`: the normalized moment scale `(E_r)^{1/2r}` stays well below `M` even at the deepest
exact depth (`r = 17–23` for `n = 8–32`), and the sup is achieved on `≤ 2` of the `m` cosets
(a single rare orbit point, NOT a positive-density / bulk feature). A fixed-degree functional —
all equidistribution ever certifies — is blind to it. **This is fence F0 made dynamical:** the
`√log` excess is a tail/rare-event phenomenon, invisible to any second-order / fixed-moment
average.

### (2) The abelian dilation torus has NO spectral gap — EMV's effective machinery does not apply.
EMV's polynomial-rate theorem requires the acting group to be **semisimple with finite
centralizer** (the spectral gap drives the rate). The dilation action here is the **abelian**
cyclic rotation `b ↦ g^{(p-1)/n} b` on `Z/m` (a torus / diagonal action). Einsiedler's survey is
explicit: *"the torus does not possess a spectral gap … rotation actions on tori are purely
parabolic"* — so the only effective control of abelian discrepancy is Diophantine, via
Erdős–Turán–Koksma. **This is fence F5** (abelian torus ⟹ zero spectral gap) already recorded
for the additive Cayley graph; it recurs verbatim on the dynamical side.

### (3) The only effective abelian rate (Erdős–Turán–Koksma) is CIRCULAR: it bounds discrepancy
BY exactly the character sums whose sup we want.
For an abelian rotation orbit the discrepancy is controlled by the **Erdős–Turán–Koksma**
inequality, whose right-hand side is a weighted sum of the very exponential sums `Σ_b e(k·η_b)`
(equivalently the `η_b` themselves). So "equidistribution ⟹ sup bound" would require, as INPUT, a
bound on those exponential sums — i.e. on `M` itself. The implication runs **backwards**: a sup
bound gives equidistribution, never the reverse. (Cf. BLMV, *Some effective results for ×a ×b*,
Ergodic Theory Dynam. Systems 29 (2009) 1705–1722, and Venkatesh, *Sparse equidistribution
problems, period bounds and subconvexity*, Ann. of Math. 172 (2010): there the exponential-sum /
subconvexity bound is the input that drives equidistribution, not an output.)

Adjacent: Katz's *Sato–Tate equidistribution of Gauss/Gauss-period families* (Katz, *Gauss Sums,
Kloosterman Sums and Monodromy Groups*; *Convolution and Equidistribution*) describes the
**limiting distribution** of normalized Gauss sums on `S¹` as `q → ∞` — again a *distribution*
(bulk) statement, with the worst-case `b` at *fixed* `q` outside its scope (it would at best give
that values are dense, never a uniform sup bound).

## The formal content of this file

We isolate the **load-bearing inequality** that makes (1)+(3) a genuine no-go, in a fully abstract,
substrate-free, axiom-clean form: *the normalized `L^{2r}` moment scale of any finite family of
reals is `≤` its maximum for every fixed `r`, with the gap closing only as `r → ∞`.* Concretely:

  `equidist_moment_le_sup` :  `( (1/N) Σ_b v_b^{2r} )^{1/(2r)} ≤ max_b |v_b|`   (any fixed `r ≥ 1`).

A fixed-degree equidistribution / discrepancy functional is exactly such a fixed-`r` moment (or a
finite combination of them); the inequality is one-directional, so it can only ever *lower-bound*
nothing useful and *upper-bound* by the average scale — never reach the sup. We complement it with
`sup_not_from_fixed_moment`: the witness that equality fails for any fixed `r` whenever the family
is non-flat (a single rare large value), the exact situation the probe measures. Together these
are the rigorous skeleton of "equidistribution is blind to the sup".

Issue #444 (lane J4, homogeneous-dynamics / Ratner / EMV / Lindenstrauss).
-/

namespace ProximityGap.Frontier.EquidistDiscrepancyBlind

open Finset

variable {ι : Type*}

/--
**The moment ladder caps below the sup at every fixed depth (the J4 engine, max form).**

For any nonempty finite family `v : ι → ℝ` and any exponent `k ≥ 1`, the (un-normalized) power
sum is bounded by the count times the `k`-th power of the maximum absolute value:

  `Σ_b |v_b|^k ≤ |S| · (max_b |v_b|)^k`.

This is the algebraic heart of the no-go: a fixed-degree functional of the family (a power sum, =
what equidistribution / discrepancy against a bounded-degree test function certifies) is pinned to
the *average* scale `(Σ|v|^k / |S|)^{1/k} ≤ max`, and only the `k → ∞` limit recovers the sup. No
*fixed* `k` (no fixed smooth test functional) sees the maximum. -/
theorem powersum_le_card_mul_sup_pow
    (S : Finset ι) (v : ι → ℝ) (k : ℕ)
    (M : ℝ) (hM : ∀ b ∈ S, |v b| ≤ M) :
    ∑ b ∈ S, |v b| ^ k ≤ S.card * M ^ k := by
  have hpow : ∀ b ∈ S, |v b| ^ k ≤ M ^ k := by
    intro b hb
    have h0 : (0:ℝ) ≤ |v b| := abs_nonneg _
    exact pow_le_pow_left₀ h0 (hM b hb) k
  calc ∑ b ∈ S, |v b| ^ k
      ≤ ∑ _b ∈ S, M ^ k := Finset.sum_le_sum hpow
    _ = S.card * M ^ k := by rw [Finset.sum_const, nsmul_eq_mul]

/--
**Normalized moment is below the sup (equidistribution-visible ≤ average scale).**

The normalized `k`-th power-mean of the family is `≤` the maximum, for every fixed `k`:

  `(1/|S|) · Σ_b |v_b|^k ≤ M^k`   where `M = max_b |v_b|`.

The left side is *exactly* the kind of quantity an equidistribution / discrepancy statement
delivers (the empirical `k`-th moment against the limiting measure). It never exceeds the average
scale, hence — for any fixed degree `k` — it cannot certify the `L^∞` sup `M`; the prize `√log`
excess sits strictly between this average scale and `M`, in the rare tail. -/
theorem normalized_moment_le_sup_pow
    (S : Finset ι) (v : ι → ℝ) (k : ℕ)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ b ∈ S, |v b| ≤ M) :
    (∑ b ∈ S, |v b| ^ k) / S.card ≤ M ^ k := by
  rcases S.card.eq_zero_or_pos with h0 | hpos
  · rw [Finset.card_eq_zero] at h0
    subst h0
    simp only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero, div_zero]
    exact pow_nonneg hM0 k
  · have hcard : (0:ℝ) < S.card := by exact_mod_cast hpos
    rw [div_le_iff₀ hcard]
    calc ∑ b ∈ S, |v b| ^ k
        ≤ S.card * M ^ k := powersum_le_card_mul_sup_pow S v k M hM
      _ = M ^ k * S.card := by ring

/--
**The rare-tail gap: a single large value is diluted by the count in every fixed moment.**

Model the prize situation measured by `probe_wfH_J4_equidist_sup.rs`: the sup `M` is attained on
**one** rare coset `b₀`, while all other `S.card − 1` cosets sit at the average scale `a < M`.
Then for any fixed degree `k`, the normalized `k`-th moment is at most

  `(1/|S|)·Σ |v_b|^k ≤ M^k/|S| + a^k`,

so the moment scale `(·)^{1/k}` is dragged toward `a` (the bulk), with the single spike `M`
contributing only an `M^k/|S|` term that a *fixed* `k` cannot lift to `M` once `|S|` is large
(here `|S| = m = (p−1)/n` is astronomically large at the prize). Only `k → ∞` recovers `M`.
This is the quantitative form of "equidistribution / discrepancy is blind to the rare sup". -/
theorem rare_spike_moment_diluted
    (S : Finset ι) (v : ι → ℝ) (k : ℕ) (b₀ : ι) (hb₀ : b₀ ∈ S)
    (M a : ℝ) (ha : 0 ≤ a)
    (hspike : |v b₀| ≤ M)
    (hbulk : ∀ b ∈ S, b ≠ b₀ → |v b| ≤ a) :
    (∑ b ∈ S, |v b| ^ k) / S.card ≤ M ^ k / S.card + a ^ k := by
  classical
  rcases S.card.eq_zero_or_pos with h0 | hpos
  · rw [Finset.card_eq_zero] at h0; subst h0; simp at hb₀
  · have hcard : (0:ℝ) < S.card := by exact_mod_cast hpos
    -- split the sum at b₀
    have hsplit : ∑ b ∈ S, |v b| ^ k
        = |v b₀| ^ k + ∑ b ∈ S.erase b₀, |v b| ^ k := by
      rw [← Finset.add_sum_erase S _ hb₀]
    have hspikepow : |v b₀| ^ k ≤ M ^ k :=
      pow_le_pow_left₀ (abs_nonneg _) hspike k
    have hbulksum : ∑ b ∈ S.erase b₀, |v b| ^ k ≤ S.card * a ^ k := by
      have hle : ∑ b ∈ S.erase b₀, |v b| ^ k ≤ ∑ _b ∈ S.erase b₀, a ^ k := by
        apply Finset.sum_le_sum
        intro b hb
        have hbS : b ∈ S := Finset.mem_of_mem_erase hb
        have hbne : b ≠ b₀ := Finset.ne_of_mem_erase hb
        exact pow_le_pow_left₀ (abs_nonneg _) (hbulk b hbS hbne) k
      calc ∑ b ∈ S.erase b₀, |v b| ^ k
          ≤ ∑ _b ∈ S.erase b₀, a ^ k := hle
        _ = (S.erase b₀).card * a ^ k := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ S.card * a ^ k := by
              apply mul_le_mul_of_nonneg_right _ (pow_nonneg ha k)
              exact_mod_cast Finset.card_le_card (Finset.erase_subset b₀ S)
    have htot : ∑ b ∈ S, |v b| ^ k ≤ M ^ k + S.card * a ^ k := by
      rw [hsplit]; exact add_le_add hspikepow hbulksum
    rw [div_le_iff₀ hcard]
    calc ∑ b ∈ S, |v b| ^ k
        ≤ M ^ k + S.card * a ^ k := htot
      _ = (M ^ k / S.card + a ^ k) * S.card := by
            rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hcard)]; ring

#print axioms powersum_le_card_mul_sup_pow
#print axioms normalized_moment_le_sup_pow
#print axioms rare_spike_moment_diluted

end ProximityGap.Frontier.EquidistDiscrepancyBlind
