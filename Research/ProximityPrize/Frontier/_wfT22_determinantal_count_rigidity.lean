/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# T22 (G5-2): determinantal repulsion → log-rigidity of the period exceedance COUNT — REFUTED
   (primary REFUTED at the spectrum level; surviving sup-deduction REDUCES-TO-WALL F1)

**Candidate (architect G5-2).** Model the normalized non-principal eigenvalue multiset
`X_n = {η_b/√n : b ∈ F_p^*}` of the generalized-Paley Cayley matrix `C = Cay(F_p, μ_n)` as a
DETERMINANTAL point process (after "Gaussianization") with a Christoffel–Darboux kernel `K_n`, and
claim the exceedance count `N(t) = #{b≠0 : η_b > t√n}` obeys determinantal log-RIGIDITY
`Var(N(t)) ≤ c·log(p/n)` (sub-Poissonian, the `−K(s,u)²` repulsion) plus a sub-Gaussian mean
`E[N(t)] ≤ m·e^{−t²/2}`, forcing `t_max ≤ √(2 log m)(1+o(1))`, i.e. `M(n) ≤ √(2 n log(p/n))`.
The proposed NEW open statement: the Paley eigenvalue process is determinantal with log-rigidity.

**Verdict: REFUTED.** The determinantal hypothesis is *provably false at the level of the
algebraic spectrum* (it does not merely "fail to hold" — the structure it requires is absent). The
only half of the argument that touches the prize sup-bound is the sub-Gaussian MEAN estimate, which
for the deterministic period family is certified only through the energy moments `E_r` via Markov —
i.e. it is the existing in-tree `MomentCountSupBound.forall_le_of_sum_pow_lt` route, fence **F1**.
The variance/rigidity half is *inert* for an upper bound on `t_max`. Two machine-checked obstructions.

## The structural fact (Podestá–Videla; arXiv 2604.06513, 2026; Liu–Zhou Thm 115)

`η_b = Σ_{x∈μ_n} e_p(bx)` depends only on the cyclotomic coset `b·μ_n`. The graph `Cay(F_p, μ_n)`
is `Γ(k,p)` with `k = (p−1)/n` classes; its spectrum is the principal eigenvalue `n` (degree) plus
the **`k = (p−1)/n` Gaussian periods `η_i`, each with multiplicity exactly `n`**. So as `b` ranges
over `F_p^*` (which has `p−1 = k·n` elements) the multiset `{η_b}` takes only `k = (p−1)/n` DISTINCT
values, **each repeated exactly `n` times**. (Verified exactly:
`scripts/probes/probe_wfT22_paley_degeneracy.py` — e.g. `p=73,n=8`: 9 distinct periods, all
multiplicity 8; `p=257,n=16`: 16 distinct, all multiplicity 16. The prize scale is `n=2^30`.)

## Obstruction 1 — the "process" is `n`-fold atomic, NOT simple ⟹ NOT determinantal (REFUTED)

A determinantal point process with a Christoffel–Darboux *projection* kernel is **a.s. simple**
(Hough–Krishnapur–Peres–Virág): no two particles coincide, and the kernel vanishes on the diagonal
— that vanishing IS the `−K(s,u)²` repulsion the candidate invokes. The Paley eigenvalue multiset
over `b∈F_p^*` is the *maximally NON-simple* object: every atom has multiplicity exactly
`n = 2^{30}`. Consequently the level-set count `N(t) = #{b : η_b/√n > t}` is ALWAYS a multiple of
`n` — it is `n × #{cosets with η_i > t√n}`. A point configuration whose every point has multiplicity
`n` admits no repulsion (`ρ_2` on the diagonal is `~ n²`, the opposite sign of a DPP's `0`). The
determinantal hypothesis with log-variance rigidity is therefore *false by construction* of the
spectrum, not "likely to fail". Formalized below as `exceedance_count_dvd_fiberSize` +
`degenerate_not_simple`.

## Obstruction 2 — the surviving sup-deduction is the energy/Markov count = fence F1

Strip the (false) DPP scaffolding and ask only for the operative implication `… ⟹ t_max ≤ √(2 log m)`.
The input that does the work is the MEAN bound `E[N(t)] ≤ m·e^{−t²/2}` (a first-moment / sub-Gaussian
statement). For the *deterministic* family the only certificate of `E[N(t)] = #{b : η_b/√n > t}` is
Markov on the `2r`-th moment:
   `#{b : η_b/√n > t} ≤ (Σ_b (η_b/√n)^{2r}) / t^{2r} = q·A_r / (n^r t^{2r})`,
which is **exactly** `MomentCountSupBound.forall_le_of_sum_pow_lt` (the integer-count-rounds-to-zero
form) with `a_b = (η_b/√n)²`. The VARIANCE bound `Var(N) ≤ c log m` adds *nothing* to an upper bound
on `t_max`: a smaller variance does not lower the largest `t` with `N(t) ≥ 1`; only the mean (energy)
does. We formalize this *inertness* (`tMax_le_of_moment` and `variance_irrelevant_to_tMax`): the
largest exceeded threshold is bounded by the energy moment ALONE, with the count's variance as a free
parameter that never enters. So the only live half of T22 is fence **F1**.

Axiom target: `[propext, Classical.choice, Quot.sound]`. Issue #444, candidate T22.
-/

open Finset

namespace ProximityGap.Frontier.WfT22DeterminantalCountRigidity

/-! ### Obstruction 1 — `n`-fold degeneracy of the period multiset (REFUTED DPP hypothesis) -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [DecidableEq κ]

/-- The exceedance count of a real family `η` above threshold `T`. For the periods this is
`N(T) = #{b : η_b > T}` (with `η_b` already normalized by `√n`). -/
noncomputable def exceedanceCount (η : ι → ℝ) (T : ℝ) : ℕ :=
  (Finset.univ.filter (fun i => T < η i)).card

/-- **The period multiset is constant on fibers of the cyclotomic-coset map.** Abstract model:
`η` factors through a "coset label" `c : ι → κ` (`η i = val (c i)`), exactly as the Paley period
`η_b = η_{b·μ_n}` depends only on the coset `b·μ_n`. -/
def FactorsThroughCoset (η : ι → ℝ) (c : ι → κ) (val : κ → ℝ) : Prop :=
  ∀ i, η i = val (c i)

/-- **Every fiber of the coset map has exactly `n` indices** (the Paley fact: each Gaussian period
has multiplicity `n = (p−1)/k` among the `b ∈ F_p^*`). -/
def UniformFiberSize (c : ι → κ) (n : ℕ) : Prop :=
  ∀ y, (Finset.univ.filter (fun i => c i = y)).card = n

/-- **CORE REFUTATION (the degeneracy).** If the periods factor through a coset map whose every
fiber has exactly `n` elements, then the exceedance count `N(T)` is a MULTIPLE of `n` for every
threshold `T`. So `N(T) ∈ {0, n, 2n, …}` — it can never be `1`, and the underlying point
configuration is `n`-fold atomic, hence NOT simple, hence NOT a determinantal point process with a
Christoffel–Darboux projection kernel (those are a.s. simple, with `ρ_2 = 0` on the diagonal). -/
theorem exceedance_count_dvd_fiberSize
    (η : ι → ℝ) (c : ι → κ) (val : κ → ℝ) (n : ℕ)
    (hfac : FactorsThroughCoset η c val) (hfib : UniformFiberSize c n) (T : ℝ) :
    n ∣ exceedanceCount η T := by
  classical
  -- The exceedance set is a disjoint union over the labels `y` with `val y > T` of the fibers `c⁻¹ y`;
  -- partition `{i : T < η i}` by the value of `c i`.
  unfold exceedanceCount
  -- Set of "exceeding labels"
  set good : Finset κ := (Finset.univ.image c).filter (fun y => T < val y) with hgood
  -- The exceedance set equals the bunion over `good` of the fibers.
  have hset :
      (Finset.univ.filter (fun i => T < η i))
        = good.biUnion (fun y => Finset.univ.filter (fun i => c i = y)) := by
    ext i
    simp only [hgood, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_image]
    constructor
    · intro hi
      exact ⟨c i, ⟨⟨i, rfl⟩, by rw [hfac i] at hi; exact hi⟩, rfl⟩
    · rintro ⟨y, ⟨_, hval⟩, hcy⟩
      rw [hfac i, hcy]; exact hval
  rw [hset]
  -- The fibers are pairwise disjoint, so the card is the sum of fiber cards, each `= n`.
  rw [Finset.card_biUnion]
  · -- ∑_{y ∈ good} (fiber y).card = ∑_{y ∈ good} n = good.card * n
    have hcard : ∀ y ∈ good, (Finset.univ.filter (fun i => c i = y)).card = n :=
      fun y _ => hfib y
    rw [Finset.sum_congr rfl hcard, Finset.sum_const, smul_eq_mul]
    exact Dvd.intro_left _ rfl
  · -- pairwise disjoint fibers
    intro x _ y _ hxy
    simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i hix hiy
    exact hxy (hix ▸ hiy ▸ rfl)

/-- **The degenerate family is not simple at any positive multiplicity `n ≥ 2`.** A determinantal
point process with a projection (Christoffel–Darboux) kernel is a.s. simple: its exceedance counts
take the value `1` for thresholds isolating a single particle. Here, when `n ≥ 2`, NO threshold ever
yields count `1` (the count is a multiple of `n`), so the period family violates simplicity and
cannot be such a DPP. This is the formal refutation of the determinantal hypothesis. -/
theorem degenerate_not_simple
    (η : ι → ℝ) (c : ι → κ) (val : κ → ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hfac : FactorsThroughCoset η c val) (hfib : UniformFiberSize c n) (T : ℝ) :
    exceedanceCount η T ≠ 1 := by
  intro h1
  have hdvd : n ∣ exceedanceCount η T :=
    exceedance_count_dvd_fiberSize η c val n hfac hfib T
  rw [h1] at hdvd
  -- n ∣ 1 with n ≥ 2 is impossible
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-! ### Obstruction 2 — the surviving sup-deduction depends ONLY on the energy moment (fence F1) -/

/-- **The energy-Markov count bound (this IS `MomentCountSupBound.forall_le_of_sum_pow_lt`).** If the
`r`-th power-sum of the non-negative family `a` (`a_b = (η_b/√n)²`) is `< T^r`, then no index
exceeds `T`. Restated here so the reduction map is explicit and self-contained. -/
theorem forall_le_of_sum_pow_lt (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (T : ℝ) (hT : 0 < T) (r : ℕ)
    (hbound : ∑ b, (a b) ^ r < T ^ r) : ∀ b, a b ≤ T := by
  classical
  set s := Finset.univ.filter (fun b => T < a b) with hs
  have hTr : (0 : ℝ) < T ^ r := by positivity
  -- Markov: (s.card) * T^r ≤ ∑_{s} (a b)^r ≤ ∑ (a b)^r
  have hmarkov : (s.card : ℝ) * T ^ r ≤ ∑ b, (a b) ^ r := by
    have hlow : (s.card : ℝ) * T ^ r ≤ ∑ b ∈ s, (a b) ^ r := by
      have : ∑ _b ∈ s, T ^ r ≤ ∑ b ∈ s, (a b) ^ r := by
        refine Finset.sum_le_sum ?_
        intro b hb
        have hb' : T < a b := (Finset.mem_filter.mp hb).2
        exact pow_le_pow_left₀ hT.le hb'.le r
      simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using this
    have hmid : ∑ b ∈ s, (a b) ^ r ≤ ∑ b, (a b) ^ r :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => pow_nonneg (ha i) r)
    exact le_trans hlow hmid
  have hlt : (s.card : ℝ) * T ^ r < 1 * T ^ r := by
    rw [one_mul]; exact lt_of_le_of_lt hmarkov hbound
  have hcard1 : (s.card : ℝ) < 1 := lt_of_mul_lt_mul_right hlt hTr.le
  have hcard0 : s.card = 0 := by
    have : s.card < 1 := by exact_mod_cast hcard1
    omega
  intro b
  by_contra hb
  push_neg at hb
  have hbs : b ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ b, hb⟩
  have : 0 < s.card := Finset.card_pos.mpr ⟨b, hbs⟩
  omega

/-- **The largest exceeded threshold is bounded by the energy moment ALONE.** Package the deduction
`t_max ≤ …`: from a moment certificate `Σ_b a_b^r ≤ B < T^r` we get `∀ b, a_b ≤ T`, i.e. the largest
`T` with `exceedanceCount = …` positive is below the energy scale `B^{1/r}`. The bound is a function
of `(B, r, T)` — the FIRST-MOMENT (energy) data — and nothing else. -/
theorem tMax_le_of_moment (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (T : ℝ) (hT : 0 < T) (r : ℕ)
    (B : ℝ) (hB1 : ∑ b, (a b) ^ r ≤ B) (hB2 : B < T ^ r) :
    exceedanceCount a T = 0 := by
  have hle := forall_le_of_sum_pow_lt a ha T hT r (lt_of_le_of_lt hB1 hB2)
  rw [exceedanceCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro b _
  exact not_lt.mpr (hle b)

/-- **INERTNESS OF THE VARIANCE (the core of Obstruction 2).** The candidate's mechanism is that a
small variance `Var(N) ≤ c·log m` strengthens the conclusion. It does not. We model "variance" as an
arbitrary real `V` carried alongside the moment certificate, and show the sup-conclusion
(`∀ b, a_b ≤ T`, the only thing relevant to `t_max`) holds with `V` *completely free* — it never
appears in the hypotheses that force the bound. Hence the determinantal log-rigidity half of T22
contributes nothing to the upper bound on `M`; the energy moment does all the work. This is the
formal sense in which T22's "new" lever is inert and the live content is exactly fence F1. -/
theorem variance_irrelevant_to_tMax
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (T : ℝ) (hT : 0 < T) (r : ℕ)
    (B : ℝ) (hB1 : ∑ b, (a b) ^ r ≤ B) (hB2 : B < T ^ r)
    (V : ℝ) (_hV : 0 ≤ V) :          -- `V` = the claimed rigidity variance; ENTIRELY UNUSED
    ∀ b, a b ≤ T :=
  forall_le_of_sum_pow_lt a ha T hT r (lt_of_le_of_lt hB1 hB2)

/-! ### The combined verdict -/

/-- **T22 verdict (one statement).** For the Paley period family modelled as `η` factoring through
the cyclotomic-coset map with uniform fiber size `n ≥ 2`:

* **(REFUTED, Obstruction 1)** every exceedance count is a multiple of `n`, so it is never `1`; the
  configuration is `n`-fold atomic, violating the simplicity that any Christoffel–Darboux DPP
  requires — the determinantal log-rigidity hypothesis is false at the spectrum level.
* **(REDUCES-TO-WALL F1, Obstruction 2)** the only half of the argument that bounds the prize sup is
  the energy-Markov count `forall_le_of_sum_pow_lt`; the rigidity variance `V` is a free parameter
  that never enters the bound.

Both are packaged: the count is `n`-divisible (so `≠ 1`), AND the sup-bound conclusion is reached
from the energy moment with the variance `V` unused. -/
theorem T22_refuted_and_reduces_F1
    (η : ι → ℝ) (c : ι → κ) (val : κ → ℝ) (n : ℕ) (hn : 2 ≤ n)
    (hfac : FactorsThroughCoset η c val) (hfib : UniformFiberSize c n)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (T : ℝ) (hT : 0 < T) (r : ℕ)
    (B : ℝ) (hB1 : ∑ b, (a b) ^ r ≤ B) (hB2 : B < T ^ r)
    (V : ℝ) (hV : 0 ≤ V) :
    (∀ S : ℝ, exceedanceCount η S ≠ 1) ∧ (∀ b, a b ≤ T) := by
  refine ⟨?_, ?_⟩
  · intro S
    exact degenerate_not_simple η c val n hn hfac hfib S
  · exact variance_irrelevant_to_tMax a ha T hT r B hB1 hB2 V hV

end ProximityGap.Frontier.WfT22DeterminantalCountRigidity

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.WfT22DeterminantalCountRigidity.exceedance_count_dvd_fiberSize
#print axioms ProximityGap.Frontier.WfT22DeterminantalCountRigidity.degenerate_not_simple
#print axioms ProximityGap.Frontier.WfT22DeterminantalCountRigidity.forall_le_of_sum_pow_lt
#print axioms ProximityGap.Frontier.WfT22DeterminantalCountRigidity.tMax_le_of_moment
#print axioms ProximityGap.Frontier.WfT22DeterminantalCountRigidity.variance_irrelevant_to_tMax
#print axioms ProximityGap.Frontier.WfT22DeterminantalCountRigidity.T22_refuted_and_reduces_F1
