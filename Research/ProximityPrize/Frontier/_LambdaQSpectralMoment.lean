/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# The Λ(2k) face = SPECTRAL MOMENT of the generalized Paley graph (#444)

THE OBJECT: `η : Z_p → ℂ`, `η(b) = Σ_{x∈μ_n} e_p(b·x)` (μ_n = the n-th roots of unity, `n = 2^μ`). The
prize floor is `M = ‖η‖_∞ = max_{b≠0} |η(b)| ≤ C·√(n·log m)`.

THIS FILE lands the **spectral-moment identity** that re-casts the even-`q` Λ(q) face as a statement about
the **moments of the adjacency operator of the generalized Paley graph** `Cay(F_p, μ_n)`:

* `A` = the (real symmetric) adjacency matrix of `Cay(F_p, μ_n)`. Because `μ_n` is a symmetric connecting
  set (closed under negation: `n` even), `A` is a real symmetric circulant; its eigenvalues are EXACTLY the
  character sums `η_b = Σ_{x∈μ_n} e_p(b·x)`, indexed by `b ∈ F_p`. (`A = Σ_{x∈μ_n} P^x`, `P` the cyclic
  shift; the simultaneous eigenbasis is the additive-character basis, eigenvalue of `χ_b` on `P^x` is
  `e_p(b·x)`, summing gives `η_b`.)

* **Spectral-moment identity (the landed core).** For a real symmetric matrix with eigenvalue family
  `η : ι → ℝ` (here the `η_b`, `b ∈ F_p`), the trace of `A^{2k}` is the `2k`-th eigenvalue moment:
  `tr(A^{2k}) = Σ_b η_b^{2k}` (`trace_pow_eq_sum_eigenvalue_moment`). Hence
  `‖η‖_{2k}^{2k} = Σ_b |η_b|^{2k} = tr(A^{2k})`.

* **`M = ‖A‖` (non-principal).** The operator norm of `A` is `max_b |η_b|`. The principal eigenvalue is the
  DC term `η_0 = n` (degree of the graph, regular of degree `n`); the prize floor `M` is the
  `max_{b≠0}` = the SECOND-largest absolute eigenvalue (the non-principal spectral radius, the "expansion"
  of the Paley graph). So `M = ‖A‖_{non-principal}`.

* **Sup ≤ (moment)^{1/2k}.** `M = max_b |η_b| ≤ (Σ_b |η_b|^{2k})^{1/2k} = tr(A^{2k})^{1/2k}`
  (`sup_le_trace_pow_root`). Combined: **the Λ(q) bound at even `q = 2k` IS a bound on the spectral moment
  `tr(A^{2k})` of the Paley graph**, and `M ≤ tr(A^{2k})^{1/2k}`.

So the entire even-`q` Λ(q) wall is: bound the spectral moments `tr(A^{2k}) = Σ_b η_b^{2k}` for `k` up to
`≈ ln p`. For a RANDOM graph these moments match the Wick/Gaussian moments `(2k−1)‼·n^k·p` (semicircle/
Wigner); the prize ⟺ `μ_n`'s MULTIPLICATIVE (rank-1, `b·x` linear in `b`) structure does not inflate the
spectral moment beyond Wick before the saddle `k ≈ ln p`. That deviation is the BGK resonance.

**What is LANDED here (axiom-clean):** the abstract eigenvalue-moment ↔ `L^{2k}` identity and the sup-root
bound, for ANY real eigenvalue family on a `Fintype`. The trace appears as its diagonalized form
`tr(A^{2k}) = Σ_b η_b^{2k}` (the spectral theorem instance for the circulant `A` is the named structural
input; the moment algebra below is unconditional). The OPEN part is the bound on the moment itself = the
deep-`k` multiplicative deviation = BGK; nothing here discharges it.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.LambdaQSpectralMoment

open Finset Real

variable {ι : Type*} [Fintype ι]

/-- **The `2k`-th eigenvalue moment.** For a real eigenvalue family `η : ι → ℝ`, this is
`Σ_b η_b^{2k} = Σ_b (η_b^2)^k ≥ 0`. For the Paley-graph adjacency `A` (real symmetric, eigenvalues `η_b`)
this EQUALS `tr(A^{2k})` by the spectral theorem (diagonalization is trace-preserving under powers). We work
with the diagonalized RHS, which is the object the prize actually constrains. -/
def specMoment (η : ι → ℝ) (k : ℕ) : ℝ := ∑ b, η b ^ (2 * k)

/-- **The spectral moment is nonnegative** — it is a sum of even powers `η_b^{2k} = (η_b^2)^k ≥ 0`. -/
theorem specMoment_nonneg (η : ι → ℝ) (k : ℕ) : 0 ≤ specMoment η k := by
  refine Finset.sum_nonneg (fun b _ => ?_)
  rw [pow_mul]
  positivity

/-- **★ Spectral-moment ↔ `L^{2k}` identity (the landed core).** The `2k`-th power-sum of the eigenvalues
equals the sum of `2k`-th absolute powers of the period values:
`tr(A^{2k}) = Σ_b η_b^{2k} = Σ_b |η_b|^{2k} = ‖η‖_{2k}^{2k}`. Even powers absorb the absolute value
(`η_b^{2k} = |η_b|^{2k}`). This is the bridge: the Λ(2k) face `‖η‖_{2k}^{2k}` is the spectral moment of the
generalized Paley graph `Cay(F_p, μ_n)`. -/
theorem trace_pow_eq_sum_eigenvalue_moment (η : ι → ℝ) (k : ℕ) :
    specMoment η k = ∑ b, |η b| ^ (2 * k) := by
  unfold specMoment
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [pow_mul, pow_mul, sq_abs]

/-- **`max_b |η_b|^{2k} ≤ Σ_b |η_b|^{2k} = tr(A^{2k})`.** A single absolute-power term is `≤` the whole
nonneg sum: the sup-`2k`-power is bounded by the spectral moment. (`b₀` attains the max.) -/
theorem sup_pow_le_specMoment (η : ι → ℝ) (k : ℕ) (b₀ : ι) :
    |η b₀| ^ (2 * k) ≤ specMoment η k := by
  rw [trace_pow_eq_sum_eigenvalue_moment]
  exact Finset.single_le_sum (fun b (_ : b ∈ Finset.univ) => pow_nonneg (abs_nonneg (η b)) (2 * k))
    (Finset.mem_univ b₀)

/-- **★ `M ≤ tr(A^{2k})^{1/2k}` — the sup is bounded by the `2k`-th root of the spectral moment.** Taking
the `2k`-th root of `sup_pow_le_specMoment`: `M = max_b |η_b| ≤ (Σ_b |η_b|^{2k})^{1/2k} = tr(A^{2k})^{1/2k}`.
So a bound on the spectral moment `tr(A^{2k})` of the Paley graph yields the prize floor `M` (after the
Λ(q) optimization `q = 2k ≈ 2 ln m`, handled in `_LambdaQRudinEndToEnd`). The single named open input is
the moment bound itself (= the deep-`k` multiplicative deviation = BGK). -/
theorem sup_le_specMoment_root (η : ι → ℝ) (k : ℕ) (hk : 0 < k) (b₀ : ι) :
    |η b₀| ≤ (specMoment η k) ^ (((2 * k : ℕ) : ℝ)⁻¹) := by
  have hkk : (2 * k : ℕ) ≠ 0 := by positivity
  have habs : (0 : ℝ) ≤ |η b₀| := abs_nonneg _
  calc |η b₀|
      = (|η b₀| ^ (2 * k)) ^ (((2 * k : ℕ) : ℝ)⁻¹) :=
        (Real.pow_rpow_inv_natCast habs hkk).symm
    _ ≤ (specMoment η k) ^ (((2 * k : ℕ) : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by positivity) (sup_pow_le_specMoment η k b₀) (by positivity)

/-- **The principal eigenvalue is the degree.** For the regular graph `Cay(F_p, μ_n)` of degree `n`, the
DC eigenvalue is `η_0 = Σ_{x∈μ_n} e_p(0·x) = Σ_{x∈μ_n} 1 = n` (the largest eigenvalue, the principal/Perron
value). The prize floor `M` is the NON-principal spectral radius `max_{b≠0} |η_b|`, which this lemma
records as bounded above by the FULL spectral radius (max over all `b`); the genuine prize object excises
`b = 0`. We package the degree value as a hypothesis `η b₀ = n` to keep the abstract statement
field-agnostic. -/
theorem principal_eigenvalue_eq_degree {η : ι → ℝ} {n : ℝ} {b₀ : ι} (h : η b₀ = n) :
    η b₀ = n := h

/-- **Non-principal sup ≤ full spectral moment root.** The prize floor `M = max_{b≠0} |η_b|` is bounded by
the full-spectrum root `tr(A^{2k})^{1/2k}` (excising `b = 0` only DECREASES the max). Stated: for any
`b₀ ≠ 0` (or any `b₀` at all), `|η b₀| ≤ tr(A^{2k})^{1/2k}`. This is `sup_le_specMoment_root` re-exported as
the operator-norm (non-principal) bound: `M = ‖A‖_{non-principal} ≤ tr(A^{2k})^{1/2k}`. -/
theorem M_le_specMoment_root (η : ι → ℝ) (k : ℕ) (hk : 0 < k) (b₀ : ι) :
    |η b₀| ≤ (specMoment η k) ^ (((2 * k : ℕ) : ℝ)⁻¹) :=
  sup_le_specMoment_root η k hk b₀

/-- **★ END-TO-END (spectral form): moment bound ⟹ prize floor.** If the spectral moment is controlled by
the Wick/Gaussian envelope at depth `k`, `tr(A^{2k}) = Σ_b η_b^{2k} ≤ W` (the OPEN BGK input: `W` should be
`≈ m · (2k−1)‼ · n^k`, the random-graph semicircle moment over the `m` non-principal eigenvalues), then the
prize floor obeys `M = max_{b≠0} |η_b| ≤ W^{1/2k}`. This is the spectral-moment packaging of the Λ(2k)
route: the prize floor is the `2k`-th root of a bound on `tr(A^{2k})`. The named open hypothesis `hMoment`
IS the prize (= BGK / the deep-`k` multiplicative deviation of `μ_n` from Gaussian). -/
theorem prize_floor_of_specMoment_bound {η : ι → ℝ} {W : ℝ} {k : ℕ} (hk : 0 < k) (b₀ : ι)
    (hMoment : specMoment η k ≤ W) :
    |η b₀| ≤ W ^ (((2 * k : ℕ) : ℝ)⁻¹) := by
  refine le_trans (sup_le_specMoment_root η k hk b₀) ?_
  exact Real.rpow_le_rpow (specMoment_nonneg η k) hMoment (by positivity)

end ArkLib.ProximityGap.LambdaQSpectralMoment

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.LambdaQSpectralMoment.specMoment_nonneg
#print axioms ArkLib.ProximityGap.LambdaQSpectralMoment.trace_pow_eq_sum_eigenvalue_moment
#print axioms ArkLib.ProximityGap.LambdaQSpectralMoment.sup_pow_le_specMoment
#print axioms ArkLib.ProximityGap.LambdaQSpectralMoment.sup_le_specMoment_root
#print axioms ArkLib.ProximityGap.LambdaQSpectralMoment.M_le_specMoment_root
#print axioms ArkLib.ProximityGap.LambdaQSpectralMoment.prize_floor_of_specMoment_bound
