/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# LANE G94 (#466, 2026-07-10): the Jacobi-cocycle chaining metric — DETERMINISTIC-GAUGE
  COLLAPSE. The tool-shape doctrine's one surviving chaining shape was "generic chaining
  (Talagrand γ₂) under a metric the Jacobi cocycle could conceivably supply, different from the
  Euclidean one that G70 proved BGK-tight." This lane CONSTRUCTS the candidate metrics, probes
  them, and proves the door closed **metric-independently**: for a deterministic field, the
  sub-Gaussian-increment certificate collapses to a diameter bound, and every metric satisfying
  it has chaining gauge γ₂ ≥ spread/(2√(log 2)) ≥ (sup)/(2√(log 2)) − ε. No Jacobi-cocycle (or
  any other) metric can place γ₂ below the sup it is supposed to certify.

## The candidates constructed and probed (`probe_g94_jacobi_cocycle_metric.py`)

Field: `η_b = Σ_{x∈μ_n} e_p(bx)` on the `m = (p−1)/n` cosets (real, since `−1 ∈ μ_n`). Jacobi
apparatus: recurrence coefficients `(a_k, b_k)` of the empirical spectral measure (dossier §2.4
form D; spacing law `b_j² − b_{j−1}² ≤ (1+ε)n` re-confirmed: ramp max `0.59n/0.79n/0.99n` at
`n = 8/16/32`), the transfer-matrix cocycle `T_k(z) = [[(z−a_{k−1})/b_k, −b_{k−1}/b_k],[1,0]]`,
`A_K = T_K⋯T_1`. Metrics tried (`n ∈ {8,16,32}`, 8 instances, primes ≡ 1 mod n at `β ≈ 3.2`,
including the structured Fermat trap 65537):

- `d_val = |η_b − η_{b'}|` (the G70/OC-CHAIN Euclidean baseline);
- `d_cd(N)`: Christoffel–Darboux orthonormal-polynomial embedding `‖φ_N(η_b) − φ_N(η_{b'})‖`;
- `d_tm(K) = ‖A_K(η_b) − A_K(η_{b'})‖_F` (transfer-matrix product metric);
- `d_proj(K)`: RP¹ angle between cocycle directions `A_K(η)·(1,0)`;
- `d_hyp(K)`: hyperbolic distance between truncated m-functions `m_K(η + ih)`;
- `d_lyap(K)`: finite-Lyapunov `|L_K(η_b) − L_K(η_{b'})|`;
- `d_orbit`: ℓ² over the multiply-by-2 coset-orbit path (the ONE candidate not factoring
  through values; it contains the j = 0 value increment, so it dominates `d_val` and collapses
  by the same theorem).

**Probe verdict (all 8 instances):** after rescaling each metric to the LARGEST scale at which
the deterministic sub-Gaussian tail condition holds (dom → √(log 2)), the greedy-admissible-net
γ₂ satisfies `γ₂_norm/spread ∈ [0.74, 0.89]` at best — always above the theorem floor `0.6005`
and always achieved by the plain value metric `d_val` (`γ₂_norm/M ≈ 1.39–1.54`); every genuine
cocycle candidate is strictly WORSE (factors 3 to 10⁷: the transfer/projective/Lyapunov data
nearly coincide at pairs with macroscopic `|Δη|` — e.g. `Δη = 6.65` at `d_tm = 0.165`, ratio
40 — the lone-spike failure shape realized inside the real instance). The lone-spike
countermodel itself (one atom at `√(2n log m)`): every candidate gives `γ₂_norm/spike = 1.20`.
NO metric with sub-Gaussian increments places γ₂ below `√(n log p)`-scale: the "MAJOR finding"
branch is empty, and the best case `γ₂ ≍ √(n log p) ≍ M` is exactly the G69/G70 BGK-tight
tautology (the certificate reproduces the sup).

## What this file PROVES (the metric-independent no-go)

For a DETERMINISTIC field `X : T → ℝ` the honest reading of the chaining tail condition
`P(|X_b − X_{b'}| > t) ≤ 2·exp(−t²/d(b,b')²)` is: for every `t` below the realized increment
the right side must be ≥ 1 (a deterministic event has probability 1). We prove:

1. `detSubGaussianPair_iff_tail`: the division-safe algebraic form used here is EQUIVALENT to
   that tail inequality whenever `d > 0` (and, unlike the naive `exp(−t²/d²)` form under Lean's
   `x/0 = 0` convention, correctly forces `Δ = 0` at `d = 0`: `detSubGaussianPair_zero_dist`).
2. `abs_le_of_detSubGaussianPair`: the condition forces DOMINATION `|Δ| ≤ √(log 2)·d`.
3. `fieldSpread_le_sqrtLog2_mul_metricDiam`: domination bounds the field spread by the metric
   diameter — the chaining CONCLUSION holds with no chaining (`chaining_redundant_of_detSubG`).
4. `metricDiam_le_two_mul_gamma2Net`: a genuine finite net-form γ₂ (admissible sequences
   `|T_k| ≤ 2^(2^k)`, singleton root, value `sup_b Σ_k 2^{k/2}·dist(b, T_k)`, infimum over all
   admissible sequences) is bounded BELOW by half the diameter — the standard first-level γ₂
   estimate, formalized, r-uniform in the truncation depth `K`.
5. **HEADLINE `no_subSpread_gamma2_certificate`**: sub-Gaussian increments w.r.t. ANY metric
   `d` (nonneg + symmetric + triangle) force `spread(X) ≤ 2√(log 2)·γ₂(T,d)`. Contrapositive:
   γ₂ can NEVER sit below `spread/(2√(log 2))`; on the period field `spread ≥ M`, so no metric
   — Jacobi-cocycle-derived or otherwise — yields a sub-sup chaining certificate.
6. `gamma2_certificate_is_conclusion`: any hoped-for certificate `γ₂ ≤ B` + sub-Gaussianity
   IMPLIES `spread ≤ 2√(log 2)·B` — i.e. the certificate already contains the conclusion; the
   chaining step adds nothing (the route is circular at the deterministic level).
7. `cocycle_metric_dichotomy`: every metric either has a concrete sub-Gaussianity failure
   witness pair, or its γ₂ is pinned above the spread. No third option.
8. `loneSpike_defeats_every_gauge`: the standing-filter countermodel
   (`466-r2-cmk-lonespike-refuted`) in chaining gauge: the lone-spike field forces
   `s ≤ 2√(log 2)·γ₂` for every admissible metric — the gauge sees the spike or fails.
9. `valueFactored_domination_descends` / `valueFactored_null_on_equal_periods`: the formal
   footprint of the probe's structural fact that every Jacobi-cocycle metric factors through
   the period VALUES (the apparatus reads `b` only through the evaluation energy `η_b`): the
   certificate descends to a metric on the 1-D value cloud — exactly the OC-CHAIN/G70 surface
   already proven entropy-tight.

## HONEST SCOPE

This is a NO-GO map, not a prize step. It closes the "Jacobi cocycle supplies a DIFFERENT
chaining metric" door in the only reading available for the deterministic period field at fixed
`(p, n)`: sub-Gaussianity-as-tail-bound degenerates to domination, and then chaining is
redundant and γ₂ is pinned at/above the sup. It does NOT close (and explicitly names) the one
surviving formulation: increment sub-Gaussianity over GENUINE randomness (a probabilistic model
of the field certified by moments to depth ~log p) — that is exactly the open Wick atom /
independence form (dossier §2.4), untouched here. It does not re-derive G70 (which is the
entropy-integral floor for the specific Euclidean metric); the present collapse is
metric-universal and complementary. CORE OPEN / ON-BGK.

**Non-overlap:** G70 = flat-Dudley floor on the Euclidean cloud; A2/I031 = index-entropy of the
canonical/quotient increment metric; A10 = tower-index coherence obstruction;
`_DyadicJacobiCocycleNonContraction` = unimodularity of the multiplicative Gauss-sum cocycle;
`_DoorIVCocycleNoRandomEdge` = no dispersion edge over random phases. This lane = the
metric-universal deterministic-gauge collapse + the cocycle-metric probe map. All disjoint.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false


namespace ArkLib.CodingTheory.ProximityGap.Frontier.G94JacobiCocycleMetric

open scoped BigOperators

noncomputable section

/-! ## §1 The deterministic sub-Gaussian increment condition -/

/-- **Deterministic sub-Gaussian pair condition** (division-safe algebraic form). For a
deterministic increment `Δ` and claimed metric distance `d`, the chaining tail condition
`P(|Δ| > t) ≤ 2·exp(−t²/d²)` — with the left side equal to `1` for every `0 < t < |Δ|` — is the
requirement `1 ≤ 2·exp(−t²/d²)`, i.e. `t² ≤ (log 2)·d²`. We take the algebraic form as the
definition; `detSubGaussianPair_iff_tail` proves it equivalent to the exponential-tail form for
`d > 0`, and it correctly forces `Δ = 0` at `d = 0` (where the naive `t²/d²` form would be
vacuously true under the `x/0 = 0` convention). -/
def DetSubGaussianPair (Δ d : ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → t < |Δ| → t ^ 2 ≤ Real.log 2 * d ^ 2

/-- The algebraic form is EQUIVALENT to the honest exponential tail inequality
`1 ≤ 2·exp(−t²/d²)` (the deterministic reading of `P(|Δ| > t) ≤ 2·exp(−t²/d²)`) whenever
`d > 0`. This pins the definition to the standard chaining hypothesis, so nothing is smuggled
in by the algebraic reformulation. -/
theorem detSubGaussianPair_iff_tail {Δ d : ℝ} (hd : 0 < d) :
    DetSubGaussianPair Δ d ↔
      ∀ t : ℝ, 0 < t → t < |Δ| → (1 : ℝ) ≤ 2 * Real.exp (-(t ^ 2) / d ^ 2) := by
  have hd2 : (0 : ℝ) < d ^ 2 := by positivity
  constructor
  · intro h t ht htΔ
    have h1 : t ^ 2 / d ^ 2 ≤ Real.log 2 := by
      rw [div_le_iff₀ hd2]
      calc t ^ 2 ≤ Real.log 2 * d ^ 2 := h t ht htΔ
        _ = Real.log 2 * d ^ 2 := rfl
    have h2 : -Real.log 2 ≤ -(t ^ 2) / d ^ 2 := by
      rw [neg_div]
      linarith
    have h3 : Real.exp (-Real.log 2) ≤ Real.exp (-(t ^ 2) / d ^ 2) := Real.exp_le_exp.mpr h2
    have h4 : Real.exp (-Real.log 2) = 1 / 2 := by
      rw [Real.exp_neg, Real.exp_log two_pos]
      norm_num
    linarith
  · intro h t ht htΔ
    have h1 : (1 : ℝ) / 2 ≤ Real.exp (-(t ^ 2) / d ^ 2) := by linarith [h t ht htΔ]
    have h2 : Real.log (1 / 2) ≤ -(t ^ 2) / d ^ 2 := by
      rw [Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 1 / 2)]
      exact h1
    have h3 : Real.log (1 / 2) = -Real.log 2 := by
      rw [one_div, Real.log_inv]
    rw [h3, neg_div, neg_le_neg_iff] at h2
    rw [div_le_iff₀ hd2] at h2
    linarith


/-- **The domination collapse.** For a deterministic field, the sub-Gaussian tail condition is
exactly increment DOMINATION: `|Δ| ≤ √(log 2)·d`. This is the fulcrum of the whole no-go: the
chaining hypothesis, honestly read on a deterministic field, is a pointwise Lipschitz bound. -/
theorem abs_le_of_detSubGaussianPair {Δ d : ℝ} (hd : 0 ≤ d)
    (h : DetSubGaussianPair Δ d) : |Δ| ≤ Real.sqrt (Real.log 2) * d := by
  by_contra hlt
  push Not at hlt
  set s : ℝ := Real.sqrt (Real.log 2) * d with hs
  have hs0 : 0 ≤ s := mul_nonneg (Real.sqrt_nonneg _) hd
  set t : ℝ := (s + |Δ|) / 2 with ht
  have h1 : s < t := by rw [ht]; linarith
  have h2 : t < |Δ| := by rw [ht]; linarith
  have h3 : 0 < t := lt_of_le_of_lt hs0 h1
  have h4 : t ^ 2 ≤ Real.log 2 * d ^ 2 := h t h3 h2
  have h5 : s ^ 2 = Real.log 2 * d ^ 2 := by
    rw [hs, mul_pow, Real.sq_sqrt (Real.log_nonneg one_le_two)]
  have h6 : s ^ 2 < t ^ 2 := by nlinarith
  linarith

/-- At `d = 0` the condition correctly forces a ZERO increment (no vacuous escape hatch): a
metric that collapses two frequencies to distance 0 while their periods differ is NOT
sub-Gaussian. This is the formal home of the probe's "hard failure" test. -/
theorem detSubGaussianPair_zero_dist {Δ : ℝ} (h : DetSubGaussianPair Δ 0) : Δ = 0 := by
  have := abs_le_of_detSubGaussianPair le_rfl h
  simp only [mul_zero] at this
  exact abs_eq_zero.mp (le_antisymm this (abs_nonneg Δ))

/-! ## §2 Field spread and metric diameter on a finite frequency index -/

variable {T : Type*} [Fintype T] [Nonempty T]

/-- The spread of a deterministic field over a finite index: `sup_{b,b'} |X b − X b'|`. On the
Gauss-period field this is `max η − min η ≥ M` (the coset sums average to `−1/m`, so the sup
magnitude is realized inside the spread). -/
def fieldSpread (X : T → ℝ) : ℝ :=
  (Finset.univ : Finset (T × T)).sup' Finset.univ_nonempty fun q => |X q.1 - X q.2|

/-- The diameter of a candidate metric over the finite index. -/
def metricDiam (d : T → T → ℝ) : ℝ :=
  (Finset.univ : Finset (T × T)).sup' Finset.univ_nonempty fun q => d q.1 q.2

lemma abs_sub_le_fieldSpread (X : T → ℝ) (b b' : T) : |X b - X b'| ≤ fieldSpread X :=
  Finset.le_sup' (f := fun q : T × T => |X q.1 - X q.2|) (Finset.mem_univ (b, b'))

lemma fieldSpread_le {X : T → ℝ} {c : ℝ} (h : ∀ b b', |X b - X b'| ≤ c) :
    fieldSpread X ≤ c :=
  Finset.sup'_le _ _ fun q _ => h q.1 q.2

lemma dist_le_metricDiam (d : T → T → ℝ) (b b' : T) : d b b' ≤ metricDiam d :=
  Finset.le_sup' (f := fun q : T × T => d q.1 q.2) (Finset.mem_univ (b, b'))

/-- **Domination bounds the spread by the diameter** — and hence the CONCLUSION of any chaining
argument holds before any chaining is done. -/
theorem fieldSpread_le_sqrtLog2_mul_metricDiam
    (X : T → ℝ) (d : T → T → ℝ) (hd0 : ∀ b b', 0 ≤ d b b')
    (hsub : ∀ b b', DetSubGaussianPair (X b - X b') (d b b')) :
    fieldSpread X ≤ Real.sqrt (Real.log 2) * metricDiam d := by
  apply fieldSpread_le
  intro b b'
  calc |X b - X b'| ≤ Real.sqrt (Real.log 2) * d b b' :=
        abs_le_of_detSubGaussianPair (hd0 b b') (hsub b b')
    _ ≤ Real.sqrt (Real.log 2) * metricDiam d :=
        mul_le_mul_of_nonneg_left (dist_le_metricDiam d b b') (Real.sqrt_nonneg _)

/-- **Chaining is redundant under domination**: from any root frequency `b₀`, the one-step
bound `|X b − X b₀| ≤ √(log 2)·d(b, b₀)` already delivers what the full generic-chaining
telescope would — the increment hypothesis IS the conclusion, pointwise. -/
theorem chaining_redundant_of_detSubG
    (X : T → ℝ) (d : T → T → ℝ) (hd0 : ∀ b b', 0 ≤ d b b')
    (hsub : ∀ b b', DetSubGaussianPair (X b - X b') (d b b')) (b₀ b : T) :
    |X b - X b₀| ≤ Real.sqrt (Real.log 2) * d b b₀ :=
  abs_le_of_detSubGaussianPair (hd0 b b₀) (hsub b b₀)

/-! ## §3 A genuine finite net-form γ₂ and its diameter floor -/

/-- Distance from a point to a finite net (`0` on the empty net; admissible nets are nonempty,
so the junk value is never used in the theorems). -/
def setDist (d : T → T → ℝ) (b : T) (N : Finset T) : ℝ :=
  if h : N.Nonempty then N.inf' h fun c => d b c else 0

lemma setDist_singleton (d : T → T → ℝ) (b c : T) : setDist d b {c} = d b c := by
  simp [setDist]

lemma setDist_nonneg (d : T → T → ℝ) (b : T) (N : Finset T) (h : ∀ c, 0 ≤ d b c) :
    0 ≤ setDist d b N := by
  rw [setDist]
  split_ifs with hN
  · exact Finset.le_inf' hN _ fun c _ => h c
  · exact le_rfl

/-- **Talagrand-admissible net sequence**: every net nonempty, cardinalities `≤ 2^(2^k)`, and a
singleton root `|T₀| = 1` — the standard admissibility constraint in the net formulation of the
generic-chaining functional. -/
def IsAdmissibleNets (f : ℕ → Finset T) : Prop :=
  (∀ k, (f k).Nonempty) ∧ (∀ k, (f k).card ≤ 2 ^ 2 ^ k) ∧ (f 0).card = 1

/-- The (depth-`K`-truncated) chaining value of a net sequence:
`sup_b Σ_{k ≤ K} 2^{k/2} · dist(b, T_k)`. -/
def netValue (d : T → T → ℝ) (K : ℕ) (f : ℕ → Finset T) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun b =>
    ∑ k ∈ Finset.range (K + 1), Real.sqrt (2 ^ k) * setDist d b (f k)

/-- **The net-form γ₂ functional** (truncation depth `K`): the infimum of chaining values over
all admissible net sequences. For finite `T` and `2^(2^K) ≥ |T|` the truncation is exact (nets
can exhaust `T`), so the theorems below cover the honest γ₂ regime; all statements are uniform
in `K`. -/
def gamma2Net (d : T → T → ℝ) (K : ℕ) : ℝ :=
  sInf { v | ∃ f, IsAdmissibleNets f ∧ v = netValue d K f }

lemma gamma2Net_set_nonempty (d : T → T → ℝ) (K : ℕ) :
    { v | ∃ f, IsAdmissibleNets f ∧ v = netValue d K f }.Nonempty := by
  obtain ⟨b₀⟩ := (inferInstance : Nonempty T)
  exact ⟨netValue d K fun _ => {b₀},
    ⟨fun _ => {b₀},
      ⟨fun k => Finset.singleton_nonempty b₀,
       fun k => by simpa using Nat.one_le_pow (2 ^ k) 2 (by norm_num),
       Finset.card_singleton b₀⟩, rfl⟩⟩

/-- **The γ₂ diameter floor, per admissible sequence.** For any admissible nets and any metric
(nonneg, symmetric, triangle), the chaining value is at least half the diameter: the singleton
root `T₀ = {c₀}` contributes `d(b, c₀)` to every point's chain sum, and the diameter pair
routes through `c₀` by the triangle inequality. This is the standard first-level lower estimate
`γ₂(T, d) ≥ Δ(T)/2`, formalized. -/
theorem metricDiam_le_two_mul_netValue
    (d : T → T → ℝ) (K : ℕ) (f : ℕ → Finset T) (hf : IsAdmissibleNets f)
    (hd0 : ∀ b b', 0 ≤ d b b') (hsymm : ∀ b b', d b b' = d b' b)
    (htri : ∀ b c b', d b b' ≤ d b c + d c b') :
    metricDiam d ≤ 2 * netValue d K f := by
  obtain ⟨hne, _hcard, hroot⟩ := hf
  obtain ⟨c₀, hc₀⟩ := Finset.card_eq_one.mp hroot
  have key : ∀ b : T, d b c₀ ≤ netValue d K f := by
    intro b
    have h0 : Real.sqrt ((2 : ℝ) ^ (0 : ℕ)) * setDist d b (f 0) = d b c₀ := by
      rw [pow_zero, Real.sqrt_one, one_mul, hc₀, setDist_singleton]
    have hterms : ∀ k ∈ Finset.range (K + 1),
        0 ≤ Real.sqrt ((2 : ℝ) ^ k) * setDist d b (f k) := fun k _ =>
      mul_nonneg (Real.sqrt_nonneg _) (setDist_nonneg d b (f k) fun c => hd0 b c)
    have hsum : Real.sqrt ((2 : ℝ) ^ (0 : ℕ)) * setDist d b (f 0) ≤
        ∑ k ∈ Finset.range (K + 1), Real.sqrt ((2 : ℝ) ^ k) * setDist d b (f k) :=
      Finset.single_le_sum hterms (Finset.mem_range.mpr (Nat.succ_pos K))
    have hval : (∑ k ∈ Finset.range (K + 1), Real.sqrt ((2 : ℝ) ^ k) * setDist d b (f k)) ≤
        netValue d K f :=
      Finset.le_sup'
        (f := fun b => ∑ k ∈ Finset.range (K + 1), Real.sqrt ((2 : ℝ) ^ k) * setDist d b (f k))
        (Finset.mem_univ b)
    calc d b c₀ = Real.sqrt ((2 : ℝ) ^ (0 : ℕ)) * setDist d b (f 0) := h0.symm
      _ ≤ ∑ k ∈ Finset.range (K + 1), Real.sqrt ((2 : ℝ) ^ k) * setDist d b (f k) := hsum
      _ ≤ netValue d K f := hval
  obtain ⟨q, _, hq⟩ := Finset.exists_mem_eq_sup'
    (Finset.univ_nonempty : (Finset.univ : Finset (T × T)).Nonempty) fun q : T × T => d q.1 q.2
  rw [metricDiam, hq]
  calc d q.1 q.2 ≤ d q.1 c₀ + d c₀ q.2 := htri _ _ _
    _ = d q.1 c₀ + d q.2 c₀ := by rw [hsymm c₀ q.2]
    _ ≤ netValue d K f + netValue d K f := add_le_add (key q.1) (key q.2)
    _ = 2 * netValue d K f := by ring

/-- **The γ₂ diameter floor.** `Δ(T, d) ≤ 2·γ₂(T, d)` for every metric and every truncation
depth. -/
theorem metricDiam_le_two_mul_gamma2Net
    (d : T → T → ℝ) (K : ℕ)
    (hd0 : ∀ b b', 0 ≤ d b b') (hsymm : ∀ b b', d b b' = d b' b)
    (htri : ∀ b c b', d b b' ≤ d b c + d c b') :
    metricDiam d ≤ 2 * gamma2Net d K := by
  have h : metricDiam d / 2 ≤ gamma2Net d K := by
    apply le_csInf (gamma2Net_set_nonempty d K)
    rintro v ⟨f, hf, rfl⟩
    linarith [metricDiam_le_two_mul_netValue d K f hf hd0 hsymm htri]
  linarith

/-! ## §4 HEADLINE: the deterministic chaining-gauge collapse -/

/-- **HEADLINE — no sub-spread γ₂ certificate exists, for ANY metric.** If a deterministic
field has sub-Gaussian increments (honest tail reading) with respect to a metric `d`, then the
chaining gauge is pinned ABOVE the field spread: `spread(X) ≤ 2√(log 2)·γ₂(T, d)`. On the
Gauss-period field `spread ≥ M − o(M)`, so no metric — in particular no metric manufactured
from the Jacobi cocycle (transfer products, projective directions, m-functions, Lyapunov data,
CD-kernel embeddings, orbit paths) — can carry a chaining certificate `γ₂ ≪ M`. The one door
the tool-shape doctrine left ajar ("the Jacobi cocycle could conceivably supply a DIFFERENT
metric") closes metric-independently at the deterministic level; what survives is only
sub-Gaussianity over genuine randomness = the open Wick atom, named and untouched. -/
theorem no_subSpread_gamma2_certificate
    (X : T → ℝ) (d : T → T → ℝ) (K : ℕ)
    (hd0 : ∀ b b', 0 ≤ d b b') (hsymm : ∀ b b', d b b' = d b' b)
    (htri : ∀ b c b', d b b' ≤ d b c + d c b')
    (hsub : ∀ b b', DetSubGaussianPair (X b - X b') (d b b')) :
    fieldSpread X ≤ 2 * Real.sqrt (Real.log 2) * gamma2Net d K := by
  have h1 := fieldSpread_le_sqrtLog2_mul_metricDiam X d hd0 hsub
  have h2 := metricDiam_le_two_mul_gamma2Net d K hd0 hsymm htri
  have hs : 0 ≤ Real.sqrt (Real.log 2) := Real.sqrt_nonneg _
  calc fieldSpread X ≤ Real.sqrt (Real.log 2) * metricDiam d := h1
    _ ≤ Real.sqrt (Real.log 2) * (2 * gamma2Net d K) := mul_le_mul_of_nonneg_left h2 hs
    _ = 2 * Real.sqrt (Real.log 2) * gamma2Net d K := by ring

/-- **The certificate IS the conclusion.** Any hoped-for pair (sub-Gaussian increments,
`γ₂ ≤ B`) — e.g. `B ≍ √(n log p)` computed from second-order Jacobi data — already implies the
spread bound `spread ≤ 2√(log 2)·B` outright. The chaining route is circular for a
deterministic field: proving its hypotheses is proving the prize inequality. -/
theorem gamma2_certificate_is_conclusion
    (X : T → ℝ) (d : T → T → ℝ) (K : ℕ) (B : ℝ)
    (hd0 : ∀ b b', 0 ≤ d b b') (hsymm : ∀ b b', d b b' = d b' b)
    (htri : ∀ b c b', d b b' ≤ d b c + d c b')
    (hsub : ∀ b b', DetSubGaussianPair (X b - X b') (d b b'))
    (hB : gamma2Net d K ≤ B) :
    fieldSpread X ≤ 2 * Real.sqrt (Real.log 2) * B := by
  have h := no_subSpread_gamma2_certificate X d K hd0 hsymm htri hsub
  have hs : 0 ≤ 2 * Real.sqrt (Real.log 2) := by positivity
  calc fieldSpread X ≤ 2 * Real.sqrt (Real.log 2) * gamma2Net d K := h
    _ ≤ 2 * Real.sqrt (Real.log 2) * B := mul_le_mul_of_nonneg_left hB hs

/-- **The dichotomy** (doctrine-facing form): every candidate metric on the frequency index
either exhibits a concrete pair WITNESSING failure of the sub-Gaussian increment condition
(the lone-spike shape the probe measures: macroscopic `|Δη|` at tiny cocycle distance), or its
chaining gauge is pinned at/above the field spread. There is no third branch in which the
Jacobi cocycle (or anything else) supplies a metric that is both sub-Gaussian and sub-sup. -/
theorem cocycle_metric_dichotomy
    (X : T → ℝ) (d : T → T → ℝ) (K : ℕ)
    (hd0 : ∀ b b', 0 ≤ d b b') (hsymm : ∀ b b', d b b' = d b' b)
    (htri : ∀ b c b', d b b' ≤ d b c + d c b') :
    (∃ b b', ¬ DetSubGaussianPair (X b - X b') (d b b')) ∨
      fieldSpread X ≤ 2 * Real.sqrt (Real.log 2) * gamma2Net d K := by
  by_cases h : ∀ b b', DetSubGaussianPair (X b - X b') (d b b')
  · exact Or.inr (no_subSpread_gamma2_certificate X d K hd0 hsymm htri h)
  · push Not at h
    exact Or.inl h

/-! ## §5 The lone-spike countermodel in chaining gauge -/

/-- The lone-spike field on `m + 2` frequencies: one atom of height `s` (the
`√(2n log m)`-scale extremal object of `466-r2-cmk-lonespike-refuted`), all other values `0`. -/
def loneSpike (m : ℕ) (s : ℝ) : Fin (m + 2) → ℝ := fun i => if i = 0 then s else 0

/-- The lone-spike spread is exactly the spike height. -/
theorem loneSpike_spread {m : ℕ} {s : ℝ} (hs : 0 ≤ s) :
    fieldSpread (loneSpike m s) = s := by
  apply le_antisymm
  · apply fieldSpread_le
    intro b b'
    by_cases hb : b = 0 <;> by_cases hb' : b' = 0 <;>
      simp [loneSpike, hb, hb', abs_of_nonneg hs, hs]
  · have h10 : (1 : Fin (m + 2)) ≠ 0 := by
      simp
    have h := abs_sub_le_fieldSpread (loneSpike m s) 0 1
    simpa [loneSpike, h10, abs_of_nonneg hs] using h


/-- **The lone spike defeats every chaining gauge** (the standing filter
`466-r2-cmk-lonespike-refuted`, chaining-gauge form): for ANY metric under which the lone-spike
field has sub-Gaussian increments, the γ₂ functional is forced up to the spike height,
`s ≤ 2√(log 2)·γ₂`. The probe measures exactly this on every candidate: `γ₂_norm/spike = 1.20`
for `d_val`, `d_cd`, `d_tm`, `d_lyap` alike. A positivity/quadrature/cocycle upgrade that
cannot beat this countermodel cannot beat the moment bound — and none can. -/
theorem loneSpike_defeats_every_gauge {m : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (d : Fin (m + 2) → Fin (m + 2) → ℝ) (K : ℕ)
    (hd0 : ∀ b b', 0 ≤ d b b') (hsymm : ∀ b b', d b b' = d b' b)
    (htri : ∀ b c b', d b b' ≤ d b c + d c b')
    (hsub : ∀ b b', DetSubGaussianPair (loneSpike m s b - loneSpike m s b') (d b b')) :
    s ≤ 2 * Real.sqrt (Real.log 2) * gamma2Net d K := by
  have h := no_subSpread_gamma2_certificate (loneSpike m s) d K hd0 hsymm htri hsub
  rwa [loneSpike_spread hs] at h

/-! ## §6 Value-factoring: the formal footprint of "the cocycle reads `b` only through `η_b`" -/

/-- A metric on the frequency index FACTORS THROUGH THE VALUES when it is a function of the
pair of period values alone. Every Jacobi-cocycle candidate has this shape by construction: the
Jacobi matrix `(a_k, b_k)` is built from the empirical spectral measure (a symmetric function
of ALL periods), and the frequency `b` enters the transfer products, m-functions, Lyapunov
data, and CD embeddings only as the evaluation energy `η_b`. (Probe-verified structurally; the
one non-factoring candidate, the dilation-orbit path metric, dominates the value increment
term-by-term and collapses by §4 directly.) -/
def ValueFactored (d : T → T → ℝ) (X : T → ℝ) : Prop :=
  ∃ ρ : ℝ → ℝ → ℝ, ∀ b b', d b b' = ρ (X b) (X b')

/-- A value-factored metric with reflexive zeros is NULL on frequencies with equal periods: it
cannot separate the `n`-fold-degenerate fibers of the period spectrum (every `η` value is taken
by a whole coset). Whatever chaining sees through such a metric, it sees on the 1-D VALUE cloud
— exactly the OC-CHAIN/G70 surface already proven entropy-tight. -/
theorem valueFactored_null_on_equal_periods {d : T → T → ℝ} {X : T → ℝ}
    (hfac : ValueFactored d X) (hrefl : ∀ b, d b b = 0)
    {b b' : T} (h : X b = X b') : d b b' = 0 := by
  obtain ⟨ρ, hρ⟩ := hfac
  have h1 : d b b' = ρ (X b') (X b') := by rw [hρ b b', h]
  have h2 : d b' b' = ρ (X b') (X b') := hρ b' b'
  rw [h1, ← h2, hrefl]

/-- **Domination descends to the value cloud.** If a value-factored metric certifies
sub-Gaussian increments for the field, then the certificate is a statement about the metric
`ρ` on the 1-D period-value cloud: `|x − y| ≤ √(log 2)·ρ(x, y)` on realized values. The
Jacobi-cocycle chaining problem is therefore the SAME problem G70 closed for the Euclidean
value metric, transported along `ρ` — with the diameter floor of §3–§4 unchanged. -/
theorem valueFactored_domination_descends {d : T → T → ℝ} {X : T → ℝ} {ρ : ℝ → ℝ → ℝ}
    (hfac : ∀ b b', d b b' = ρ (X b) (X b'))
    (hd0 : ∀ b b', 0 ≤ d b b')
    (hsub : ∀ b b', DetSubGaussianPair (X b - X b') (d b b')) (b b' : T) :
    |X b - X b'| ≤ Real.sqrt (Real.log 2) * ρ (X b) (X b') := by
  rw [← hfac b b']
  exact abs_le_of_detSubGaussianPair (hd0 b b') (hsub b b')

/-! ## §7 Honesty marker -/

/-- This lane is a no-go map plus a probe; it is NOT a prize closure. -/
def isPrizeClosure : Prop := False

theorem not_prizeClosure : ¬ isPrizeClosure := id

end

/-! ## Axiom audit

Every declaration below must report exactly `[propext, Classical.choice, Quot.sound]` — no
`sorry`, no custom axioms, no `native_decide`. -/

#print axioms detSubGaussianPair_iff_tail
#print axioms abs_le_of_detSubGaussianPair
#print axioms detSubGaussianPair_zero_dist
#print axioms fieldSpread_le_sqrtLog2_mul_metricDiam
#print axioms chaining_redundant_of_detSubG
#print axioms metricDiam_le_two_mul_netValue
#print axioms metricDiam_le_two_mul_gamma2Net
#print axioms no_subSpread_gamma2_certificate
#print axioms gamma2_certificate_is_conclusion
#print axioms cocycle_metric_dichotomy
#print axioms loneSpike_spread
#print axioms loneSpike_defeats_every_gauge
#print axioms valueFactored_null_on_equal_periods
#print axioms valueFactored_domination_descends
#print axioms not_prizeClosure

end ArkLib.CodingTheory.ProximityGap.Frontier.G94JacobiCocycleMetric
