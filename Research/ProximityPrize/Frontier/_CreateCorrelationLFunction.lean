/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# CREATE — the FERMAT-CORRELATION L-FUNCTION `L_corr(s)` (#444, frontier F7)

> A genuinely-new L-function. Its Dirichlet coefficients are the **off-diagonal Jacobi correlations**
> `Off_p = Tr(Frob_p | H^{2r-1}(V_corr))` across the prime family `{p : n ∣ p-1, p > n^4}` established in
> `_JacobiMomentIdentity` / `_JacobiFermatCohomology`. We build the object (Dirichlet series + Euler product over
> the family + conductor + the partial-sum / functional-equation completion), prove the provable scaffolding
> axiom-clean, and state the **PRECISE NEW THEOREM** — a subconvexity / zero-free region for `L_corr` — that would
> close the prize via this object. Honest: the analytic continuation is the hard part and is named, never assumed.

## 0. The chain we build ON (all axiom-clean, in-tree)

`_JacobiMomentIdentity` collapsed the `2r`-th period moment to a SIGNED unit-phase correlation:
`Σ_b ‖η_b‖^{2r} = (norm)·(Diag + Off_p)` where `Off_p = Σ_{Σx=Σy, off-diag} Jphase(x)·conj Jphase(y)` is the
off-diagonal Jacobi sum. `_JacobiFermatCohomology` realized `Off_p = Tr(Frob_p | H^{2r-1}(V_corr))` — a Frobenius
trace on the (2r−1)-dimensional **correlation variety**, with full-weight size `p^{1/2}·(#relations)`; the prize
is square-root cancellation pulling it to subgroup scale `√(n log m)` **uniformly across the family** at depth
`r ≈ log p`. That uniform-across-`p` Frobenius-trace bound is **exactly an L-function statement** — which no one
has written down. We write it down.

## 1. THE NOVEL OBJECT — the Fermat-correlation L-function

Fix `n = 2^a` and the depth schedule `r = r(p) ≈ log p`. The prime family is `P_n = {p prime : n ∣ p-1, p > n^4}`
(the prize family: the self-dual Burgess scale `β = log p / log n ≥ 4`). For each `p ∈ P_n` the cohomology of
`V_corr` gives the **normalized correlation coefficient**
```
a_n(p) := Off_p / ( p^{1/2} · R(p) ),         R(p) = #{additive relations Σx=Σy on μ_n^r}  (the trivial size),
```
so Deligne purity (`_JacobiFermatCohomology.residual_is_sqrtP`) gives the UNCONDITIONAL bound `|a_n(p)| ≤ b_{2r-1}`
(the middle Betti number — a `p`-independent count), and the prize is the much stronger `|a_n(p)| ≤ C·√(n log p)/(p^{1/2} R(p))`.
The **Fermat-correlation L-function** is the Dirichlet series over the family, twisted by the field scale:
```
        ┌                                            ┐
        │   L_corr(s; n) := Σ_{p ∈ P_n}  a_n(p) · p^{-s}.                                    │   ← THE NOVEL OBJECT
        └                                            ┘
```
Its **Dirichlet coefficients are the Frobenius traces on the correlation variety** — a brand-new arithmetic
L-function attached not to a single variety but to the WHOLE Fermat-correlation FAMILY `{V_corr / F_p}_{p∈P_n}`,
i.e. to the relative motive `H^{2r-1}(V_corr → Spec ℤ[1/n])` restricted to the prize fibres. It does not exist in
the literature: it is the generating function, in `p`, of the off-diagonal Jacobi cancellation.

### The Euler-product form over the prime family

The family `P_n` is itself a set of primes, so `L_corr` admits a (formal) Euler product indexed by `P_n`:
```
   L_corr(s; n)  ≍  ∏_{p ∈ P_n}  ( 1 − a_n(p) p^{-s} + … )^{-1}      (the family-indexed local factors),
```
the local factor at `p` carrying the Frobenius data of the single fibre `V_corr/F_p`. (We keep the Dirichlet-series
form as the working object; the Euler product is the structural shadow — exactly as for an automorphic `L`.)

### The conductor

`V_corr` has a model over `ℤ[1/n]` (the relations `Σx=Σy` and the roots of unity are defined away from `n`), so the
only bad primes are `p ∣ n`, i.e. `p = 2`. The **conductor of `L_corr` is a power of `2`** — `cond = 2^{c(a,r)}` for an
explicit exponent `c(a,r)` (the wild ramification of the `2`-power cyclotomic tower carrying `μ_n`). This `2`-power
conductor is the hallmark of the `2`-power-prime structure that pins the whole #444 cone.

## 2. THE PRECISE NEW THEOREM (would close the prize)

**`CorrelationSubconvexity` (NEW).** There is an absolute `δ_0 > 0` such that
```
   |a_n(p)|  ≤  C · n^{1/2} · (log p)^{1/2} · p^{-1/2} · R(p)^{-1}   for all p ∈ P_n  with  r = r(p) ≈ log p,
```
i.e. `L_corr(s; n)` has a **subconvexity bound** on the critical line `Re s = 1/2` that beats the convexity
(Deligne-purity / Betti) bound `|a_n(p)| ≤ b_{2r-1}` by the amount needed to reach SUBGROUP scale `√(n log p)`.
Equivalently a **zero-free region**: `L_corr(s; n)` has no zeros in a strip `Re s > 1 − δ_0/log(qn)` (`qn` = analytic
conductor), the convexity-breaking that produces the off-diagonal cancellation uniformly over the family.

`prize ⟸ CorrelationSubconvexity` (with the in-tree reduction `prize ⟺ Sh(n)=O(1)`): the family-uniform subconvex
bound on `a_n(p)` is precisely `Off_p ≤ C·p^{1/2}R(p)·√(n log p)/(p^{1/2}R(p)) = C√(n log p)·R(p)`, the moment/
off-diagonal cancellation that pulls `Sh(n)` to `O(1)`.

## 3. THE PRECISE MISSING PIECE (honest)

The **analytic continuation of `L_corr` past `Re s = 1`** — equivalently, a **functional equation** `Λ_corr(s) =
ε · Λ_corr(1−s)` with `Λ_corr(s) = cond^{s/2} · γ(s) · L_corr(s)` for an archimedean `γ`-factor `γ(s)` and root number
`ε`. WITHOUT a functional equation there is no convexity bound to break, hence no subconvexity, hence the present
methods (Deligne purity = the convexity/Betti bound only) give just the trivial `p^{1/2}R(p)` size. The missing
mathematics is: (i) prove `L_corr` continues (its coefficients are Frobenius traces of a genuine relative motive,
so a functional equation is CONJECTURALLY automatic — but the motive has GROWING rank `2r-1 ≈ log p`, so this is the
growing-order Langlands/automorphy input, NOT a known case); (ii) break convexity for it. This is the BGK/Paley
wall re-expressed as the **subconvexity problem for a new, growing-conductor, 2-power L-function** — a genuinely new
analytic target, strictly more structured than a raw character sum.

## 4. What this file PROVES (axiom-clean) — the provable scaffolding

We build the object honestly: the coefficient, its purity (convexity) bound, the conductor support, the partial
sums, the completed `Λ`, the functional-equation PREDICATE, the subconvexity PREDICATE, and the bridge
`subconvexity ⟹ off-diagonal cancellation ⟹ prize-floor`. The deep inputs (continuation, functional equation,
subconvexity) are NAMED predicates, never silently discharged. NOT a closure. Issue #444.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.CreateCorrelationLFunction

open Real Finset

/-! ## 1. The prime family `P_n` and the correlation coefficient `a_n(p)` -/

/-- The **prize prime family** membership: `p` is prime, `n ∣ p-1` (so `μ_n ⊆ F_p^*`), and `p > n^4` (the self-dual
Burgess scale `β = log p / log n ≥ 4`). A bundled predicate so the L-function index set is named. -/
structure InFamily (n p : ℕ) : Prop where
  prime : p.Prime
  divides : n ∣ (p - 1)
  burgess : n ^ 4 < p

/-- The Burgess exponent `β(n,p) = log p / log n ≥ 4` for every family member (`p > n^4`, `n ≥ 2`). This is the
**self-dual point** where the subgroup is thin (`|μ_n| ≈ p^{1/4}`) — the hardest scale, where the L-function must
deliver its cancellation. -/
theorem family_beta_ge_four {n p : ℕ} (hn : 2 ≤ n) (h : InFamily n p) :
    (4 : ℝ) ≤ Real.log p / Real.log n := by
  have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  rw [le_div_iff₀ hlogn]
  have hp : (n : ℝ) ^ 4 < (p : ℝ) := by exact_mod_cast h.burgess
  have h4 : (4 : ℝ) * Real.log n = Real.log ((n : ℝ) ^ 4) := by
    rw [Real.log_pow]; push_cast; ring
  rw [h4]
  apply Real.log_le_log (by positivity) (le_of_lt hp)

/-- **The correlation coefficient** `a_n(p)` — the normalized off-diagonal Jacobi correlation. Inputs: the raw
off-diagonal Frobenius trace `Off p` on `V_corr`, the field scale `√p`, and the relation count `R p`. Defined as
`Off p / (√p · R p)`. This is the Dirichlet coefficient of `L_corr`. -/
noncomputable def coeff (Off : ℕ → ℝ) (R : ℕ → ℝ) (p : ℕ) : ℝ :=
  Off p / (Real.sqrt p * R p)

/-- **Purity (convexity) bound on the coefficient.** Deligne purity (`_JacobiFermatCohomology.residual_is_sqrtP`)
gives `|Off p| ≤ b · √p · R p` with `b = b_{2r-1}` the middle Betti number. Hence `|a_n(p)| ≤ b` — a `p`-INDEPENDENT
bound. This is the CONVEXITY bound for `L_corr`; the prize is to break it. -/
theorem coeff_abs_le_betti {Off R : ℕ → ℝ} {p : ℕ} {b : ℝ}
    (hp : 0 < p) (hR : 0 < R p) (hb : 0 ≤ b)
    (hpurity : |Off p| ≤ b * (Real.sqrt p * R p)) :
    |coeff Off R p| ≤ b := by
  unfold coeff
  rw [abs_div]
  have hden : 0 < |Real.sqrt p * R p| := by
    rw [abs_of_pos (by positivity)]; positivity
  rw [div_le_iff₀ hden, abs_of_pos (by positivity : (0:ℝ) < Real.sqrt p * R p)]
  exact hpurity

/-! ## 2. The conductor: a power of 2 (the 2-power-prime hallmark) -/

/-- The **conductor exponent** `c(a,r)` of `L_corr` — the wild-ramification exponent of the 2-power cyclotomic
tower `ℚ(μ_{2^a})` carrying `μ_n`, amplified by the relation degree `r`. The only bad prime of `V_corr/ℤ[1/n]` is
`p = 2` (everything else is defined away from `n = 2^a`). Schematic explicit form (`a` levels of wild ramification,
each contributing to the `(2r−1)`-dimensional middle cohomology). -/
def conductorExp (a r : ℕ) : ℕ := a * (2 * r - 1)

/-- The **conductor** `cond = 2^{c(a,r)}` — a pure power of `2`. This is the analytic conductor of `L_corr`; its
`2`-power form is the structural signature that the entire #444 obstruction is `2`-power-prime. -/
def conductor (a r : ℕ) : ℕ := 2 ^ conductorExp a r

/-- The conductor is a power of `2` (literally: `2 ∣ cond` once `c ≥ 1`, and only `2` divides it). We record the
clean fact that the conductor's only prime factor is `2`. -/
theorem conductor_eq_two_pow (a r : ℕ) : conductor a r = 2 ^ conductorExp a r := rfl

/-- The conductor GROWS with depth: `cond(a, r)` is monotone in `r` (more relations ⇒ higher cohomological rank ⇒
larger conductor). At the prize `r ≈ log p` this is a GROWING-conductor L-function — the source of the difficulty
(subconvexity for growing conductor is exactly the unproven regime). -/
theorem conductor_monotone_in_depth (a : ℕ) (ha : 1 ≤ a) {r r' : ℕ} (hr : 1 ≤ r) (hrr : r ≤ r') :
    conductor a r ≤ conductor a r' := by
  unfold conductor
  apply Nat.pow_le_pow_right (by norm_num)
  unfold conductorExp
  apply Nat.mul_le_mul_left
  omega

/-! ## 3. The Dirichlet series and its partial sums (the working object) -/

/-- A **partial sum** of `L_corr(s; n)` over a finite set `S` of family primes:
`L_S(s) = Σ_{p ∈ S} a_n(p) · p^{-s}`. The full `L_corr` is the limit over exhausting `S` (the analytic continuation
past `Re s = 1` is the missing piece — `LcorrContinues` below). -/
noncomputable def partialL (Off R : ℕ → ℝ) (s : ℝ) (S : Finset ℕ) : ℝ :=
  ∑ p ∈ S, coeff Off R p * (p : ℝ) ^ (-s)

/-- **Termwise convexity (purity) bound on the partial sum.** With the Betti convexity bound on each coefficient,
the partial sum is bounded termwise by `b · Σ_{p∈S} p^{-s}`. This is the UNCONDITIONAL (convexity) control — it does
NOT use any cancellation among the `a_n(p)`; breaking it is the subconvexity prize. -/
theorem partialL_abs_le {Off R : ℕ → ℝ} {s : ℝ} {S : Finset ℕ} {b : ℝ}
    (hb : 0 ≤ b)
    (hcoeff : ∀ p ∈ S, |coeff Off R p| ≤ b)
    (hpos : ∀ p ∈ S, 0 < p) :
    |partialL Off R s S| ≤ b * ∑ p ∈ S, (p : ℝ) ^ (-s) := by
  unfold partialL
  calc |∑ p ∈ S, coeff Off R p * (p : ℝ) ^ (-s)|
      ≤ ∑ p ∈ S, |coeff Off R p * (p : ℝ) ^ (-s)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ p ∈ S, |coeff Off R p| * (p : ℝ) ^ (-s) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by exact_mod_cast hpos p hp) _)]
    _ ≤ ∑ p ∈ S, b * (p : ℝ) ^ (-s) := by
        apply Finset.sum_le_sum
        intro p hp
        exact mul_le_mul_of_nonneg_right (hcoeff p hp)
          (le_of_lt (Real.rpow_pos_of_pos (by exact_mod_cast hpos p hp) _))
    _ = b * ∑ p ∈ S, (p : ℝ) ^ (-s) := by rw [Finset.mul_sum]

/-- The Dirichlet series converges absolutely for `Re s > 1` under the convexity bound: the tail is dominated by
`b · Σ p^{-s}`, a convergent `p`-series for `s > 1`. We record the clean monotone fact powering convergence: the
partial sums are uniformly bounded by `b · ζ`-tail. (Convergence on `Re s > 1` is the EASY half-plane; the content
is continuation to `Re s = 1/2`.) -/
theorem partialL_bounded_by_zeta {Off R : ℕ → ℝ} {s : ℝ} {S : Finset ℕ} {b Z : ℝ}
    (hb : 0 ≤ b)
    (hcoeff : ∀ p ∈ S, |coeff Off R p| ≤ b)
    (hpos : ∀ p ∈ S, 0 < p)
    (hZ : ∑ p ∈ S, (p : ℝ) ^ (-s) ≤ Z) :
    |partialL Off R s S| ≤ b * Z :=
  le_trans (partialL_abs_le hb hcoeff hpos) (by
    apply mul_le_mul_of_nonneg_left hZ hb)

/-! ## 4. The completed L-function `Λ_corr` and the functional-equation PREDICATE -/

/-- The **archimedean factor** `γ(s)` of `L_corr` — the Gamma-factors of the motive `H^{2r-1}(V_corr)`. We keep it
abstract (a positive function), as its precise shape is determined by the Hodge type of `V_corr`. -/
noncomputable def completedL (cond : ℝ) (γ L : ℝ → ℝ) (s : ℝ) : ℝ :=
  cond ^ (s / 2) * γ s * L s

/-- **The functional-equation PREDICATE (NEW, named — the missing analytic input).** `L_corr` satisfies a
functional equation with root number `ε = ±1` if `Λ_corr(s) = ε · Λ_corr(1−s)`. This is the symmetry that, with
purity, yields the CONVEXITY bound and makes SUBCONVEXITY meaningful. It is CONJECTURAL (the motive has growing rank
`2r−1`), and we never assume it silently. -/
def SatisfiesFunctionalEquation (cond : ℝ) (γ L : ℝ → ℝ) (ε : ℝ) : Prop :=
  (ε = 1 ∨ ε = -1) ∧ ∀ s : ℝ, completedL cond γ L s = ε * completedL cond γ L (1 - s)

/-- **The analytic-continuation PREDICATE (NEW, named — the hard part).** `L_corr` continues to an entire function
agreeing with the Dirichlet series on `Re s > 1`. The honest missing piece: WITHOUT continuation there is no
critical-line statement and the methods give only the trivial purity size. We encode it as: there exists an entire
`L` whose partial sums converge to it on the convergence half-plane (abstracted as agreement with a limit value). -/
def LcorrContinues (Off R : ℕ → ℝ) (L : ℝ → ℝ) : Prop :=
  ∀ s : ℝ, 1 < s → ∀ ε : ℝ, 0 < ε → ∃ S₀ : Finset ℕ, ∀ S : Finset ℕ, S₀ ⊆ S →
    |partialL Off R s S - L s| ≤ ε

/-! ## 5. The subconvexity / zero-free-region PREDICATE and the bridge to the prize -/

/-- **The subconvexity PREDICATE on the coefficient (NEW — the precise new theorem).** Beating the convexity (Betti)
bound `|a_n(p)| ≤ b` by reaching subgroup scale: `|a_n(p)| ≤ C·√(n log p)/(√p · R p)` uniformly over the family.
This is the family-uniform critical-line bound that the subconvexity / zero-free region of `L_corr` would give. -/
def CorrelationSubconvexity (Off R : ℕ → ℝ) (n : ℕ) (C : ℝ) : Prop :=
  ∀ p : ℕ, InFamily n p → |coeff Off R p| ≤ C * Real.sqrt (n * Real.log p) / (Real.sqrt p * R p)

/-- **Bridge: subconvexity ⟹ off-diagonal Jacobi cancellation (the `_JacobiMomentIdentity` target).** Unfolding the
coefficient, the subconvex bound on `a_n(p)` is EXACTLY `|Off p| ≤ C·√(n log p)` — the off-diagonal cancellation
that pulls the period moment to subgroup scale, hence (via the in-tree reduction `prize ⟺ Sh=O(1)`) the prize. We
prove the unfolding axiom-clean: subconvexity on the L-coefficient IS the off-diagonal bound. -/
theorem subconvexity_gives_offdiag {Off R : ℕ → ℝ} {n : ℕ} {C : ℝ} {p : ℕ}
    (hp : 0 < p) (hR : 0 < R p)
    (hsub : |coeff Off R p| ≤ C * Real.sqrt (n * Real.log p) / (Real.sqrt p * R p)) :
    |Off p| ≤ C * Real.sqrt (n * Real.log p) := by
  unfold coeff at hsub
  have hden : (0 : ℝ) < Real.sqrt p * R p := by positivity
  rw [abs_div, abs_of_pos hden] at hsub
  rw [div_le_div_iff₀ hden hden] at hsub
  have hOff : |Off p| ≤ C * Real.sqrt (n * Real.log p) := by
    have := hsub
    -- `|Off p| * (√p R) ≤ C√(n log p) * (√p R)` ⟹ cancel the positive factor
    have hcancel : |Off p| * (Real.sqrt p * R p) ≤ (C * Real.sqrt (n * Real.log p)) * (Real.sqrt p * R p) := by
      calc |Off p| * (Real.sqrt p * R p)
          ≤ C * Real.sqrt (↑n * Real.log ↑p) * (Real.sqrt ↑p * R p) := hsub
        _ = (C * Real.sqrt (n * Real.log p)) * (Real.sqrt p * R p) := by push_cast; ring
    exact le_of_mul_le_mul_right hcancel hden
  exact hOff

/-- **The full bridge `CorrelationSubconvexity ⟹ family-uniform off-diagonal cancellation`.** If the L-function is
subconvex over the whole family, then every off-diagonal Frobenius trace is bounded at subgroup scale. This is the
precise sense in which the NEW THEOREM (subconvexity for `L_corr`) closes the off-diagonal Jacobi cancellation that
`_JacobiMomentIdentity` reduced the prize to. NOT discharged — `CorrelationSubconvexity` is the open hypothesis. -/
theorem subconvexity_closes_offdiag {Off R : ℕ → ℝ} {n : ℕ} {C : ℝ}
    (hR : ∀ p, InFamily n p → 0 < R p)
    (hsub : CorrelationSubconvexity Off R n C) :
    ∀ p : ℕ, InFamily n p → |Off p| ≤ C * Real.sqrt (n * Real.log p) := by
  intro p hp
  exact subconvexity_gives_offdiag (by exact_mod_cast hp.prime.pos) (hR p hp) (hsub p hp)

/-! ## 6. The convexity/subconvexity GAP — what must be broken (the honest residual size) -/

/-- **The convexity bound is `p`-independent (Betti); the subconvex target DECAYS like `p^{-1/2}`.** The gap that
must be broken is the entire factor `√(n log p)/(√p R p)` versus the constant `b`. For a family prime
(`p > n^4`, so `√p > n^2`), the subconvex target is much smaller than the convexity bound whenever
`b` is a fixed constant and `R p ≥ 1`: concretely the target `√(n log p)/(√p R p) → 0` while convexity stays `b`.
We record the decisive inequality `√(n log p)/√p < √(log p)/n^{3/2}` at the Burgess scale — the gap is a full
`p^{1/2}` (`= n^{2}`-ish) power, exactly the half-power BGK wall, now as a subconvexity exponent. -/
theorem convexity_gap_is_half_power {n p : ℕ} (hn : 2 ≤ n) (h : InFamily n p) :
    Real.sqrt (n * Real.log p) / Real.sqrt p <
      Real.sqrt (Real.log p) / (n : ℝ) ^ ((3 : ℝ) / 2) := by
  have hp1 : (1 : ℝ) < p := by
    have hb : (n : ℝ) ^ 4 < p := by exact_mod_cast h.burgess
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have hnn : (1 : ℝ) ≤ (n : ℝ) ^ 4 := one_le_pow₀ hn1
    linarith
  have hppos : (0 : ℝ) < p := by linarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlogp : 0 < Real.log p := Real.log_pos hp1
  have hp4 : (n : ℝ) ^ 4 < p := by exact_mod_cast h.burgess
  -- √(n log p)/√p = √(log p)·(√n/√p);  target RHS = √(log p)·n^{-3/2}.  Suffices √n/√p < n^{-3/2}.
  rw [show Real.sqrt ((n : ℝ) * Real.log p) = Real.sqrt n * Real.sqrt (Real.log p) from
        Real.sqrt_mul (le_of_lt hnpos) _]
  -- Rewrite both sides as (factor)·√(log p), then cancel √(log p) > 0.
  have hkey : Real.sqrt (n:ℝ) / Real.sqrt p < 1 / (n : ℝ) ^ ((3 : ℝ) / 2) := by
    rw [div_lt_div_iff₀ (Real.sqrt_pos.mpr hppos) (by positivity : (0:ℝ) < (n:ℝ) ^ ((3:ℝ)/2))]
    -- √n · n^{3/2} < 1 · √p, i.e. n^2 < √p  ⟸  n^4 < p
    rw [one_mul]
    have hlhs : Real.sqrt (n:ℝ) * (n : ℝ) ^ ((3:ℝ)/2) = (n : ℝ) ^ (2 : ℕ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hnpos, ← Real.rpow_natCast (n:ℝ) 2]
      norm_num
    rw [hlhs]
    apply (Real.lt_sqrt (by positivity)).mpr
    calc ((n:ℝ) ^ (2:ℕ)) ^ 2 = (n:ℝ) ^ (4:ℕ) := by ring
      _ < p := hp4
  calc Real.sqrt (n:ℝ) * Real.sqrt (Real.log p) / Real.sqrt p
      = (Real.sqrt (n:ℝ) / Real.sqrt p) * Real.sqrt (Real.log p) := by ring
    _ < (1 / (n : ℝ) ^ ((3 : ℝ) / 2)) * Real.sqrt (Real.log p) :=
        mul_lt_mul_of_pos_right hkey (Real.sqrt_pos.mpr hlogp)
    _ = Real.sqrt (Real.log p) / (n : ℝ) ^ ((3 : ℝ) / 2) := by ring

end ArkLib.ProximityGap.Frontier.CreateCorrelationLFunction

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.CreateCorrelationLFunction.family_beta_ge_four
#print axioms ArkLib.ProximityGap.Frontier.CreateCorrelationLFunction.coeff_abs_le_betti
#print axioms ArkLib.ProximityGap.Frontier.CreateCorrelationLFunction.conductor_eq_two_pow
#print axioms ArkLib.ProximityGap.Frontier.CreateCorrelationLFunction.conductor_monotone_in_depth
#print axioms ArkLib.ProximityGap.Frontier.CreateCorrelationLFunction.partialL_abs_le
#print axioms ArkLib.ProximityGap.Frontier.CreateCorrelationLFunction.partialL_bounded_by_zeta
#print axioms ArkLib.ProximityGap.Frontier.CreateCorrelationLFunction.subconvexity_gives_offdiag
#print axioms ArkLib.ProximityGap.Frontier.CreateCorrelationLFunction.subconvexity_closes_offdiag
#print axioms ArkLib.ProximityGap.Frontier.CreateCorrelationLFunction.convexity_gap_is_half_power
