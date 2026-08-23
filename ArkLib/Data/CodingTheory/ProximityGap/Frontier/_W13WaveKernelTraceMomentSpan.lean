/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic

/-!
# W13: wave-kernel / non-backtracking TRACE IDENTITIES lie in the moment span (#466)

**Thread `wall:probe-batch`.** Workbench §5(7) lists "non-backtracking Ihara–Bass
(arXiv 2606.27075)" among never-run probes. The RADIUS face of that paper's machinery was
killed 2026-07-01 (`466-r1-nonbacktracking-relabeling`, brick
`_NonBacktrackingRelabelingNoGo.lean`: the NB spectral radius is a strictly-monotone relabel
of the prize floor `M = max_{b≠0} |η_b|`). The paper's genuinely NEW machinery, however, is
not the radius: it is **discrete space-time wave kernels** (forward time-difference scheme,
closed forms via discrete modified Bessel functions and NB walk counts) and a **trace-type
formula** yielding closed-form additive-character-twisted trigonometric sums — i.e.
IDENTITIES, not radius bounds. Could such a trace identity be a new arithmetic *input* for
the wall `M(μ_n) ≤ C·√(n·log(p/n))`?

This brick is the machine-checked structural reason the answer is NO, complementing the
radius-face brick. All the paper's kernel/trace objects on a regular graph are built from the
single three-term recursion `F_{m+2} = X·F_{m+1} − q·F_m` (`q = degree − 1`) with polynomial
seeds:

* wave kernel (forward-difference scheme):     seeds `(1, X)`      — `K_t = w_t(A)`;
* Ihara–Bass per-eigenvalue NB power sums:      seeds `(2, X)`      — `s_m(λ) = μ₊^m + μ₋^m`;
* NB walk-count matrices `N_{m+1}`:             seeds `(X, X² − C(q+1))`.

We prove: every member of every such family is a polynomial of explicitly bounded degree with
coefficients depending ONLY on `(m, q)` — never on the instance — hence every trace functional
`∑_b F_m.eval (η b)` is a UNIVERSAL linear combination of the power sums `∑_b (η b)^j`,
`j ≤ deg` (`trace_eval_eq_moment_combo`), and two spectrum families with equal power sums up to
the depth have IDENTICAL wave-kernel / NB / Ihara–Bass traces at every time up to that depth
(`waveKernel_trace_blind`, `iharaBass_trace_blind`, `nbWalkCount_trace_blind`).

## Why this closes the identity face

The power sums of the `Cay(F_p, μ_n)` adjacency spectrum ARE the `E_r` moment ladder — the
wall's own vocabulary. So the paper's trace formula can only ever produce identities WITHIN
the ladder: zero new `p`-arithmetic, zero `L∞` content beyond what the moments at that depth
already pin, and the moments pin `M` only at depth `r ≈ log p` — the wall itself (tool-shape
principle). The companion probe `scripts/probes/probe_w13_wavekernel_trace.py` instantiates
everything numerically: (F1) Hashimoto moments `tr(B^m)`, NB walk counts `tr(N_m)` and wave
traces `tr(K_t)` on `Cay(F_p, μ_n)` reconstruct EXACTLY (≤ 2e-11 rel) from FFT power sums at
`n ∈ {8,16}`, `p ∈ {89, 233, 257, 337}`; (F2) the exact-rational coefficient triangles are
bitwise identical across primes at fixed `n`; (F3) at regime scale the pair `n = 16`,
`p = 65617` vs `65633` has moments `j ≤ 6` equal to `2.4e-4` relative while `M` differs
`4.5%` — a bounded-depth trace identity provably cannot separate them (this file), so it
cannot pin `M`. VERDICT for arXiv 2606.27075 as a wall lever: **DEAD (moment repackaging)**,
on both faces. Issue #466. Axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Polynomial Finset

namespace ArkLib.ProximityGap.Frontier.W13WaveKernelTraceMomentSpan

/-- The generic three-term (Chebyshev-like) recursion `F_{m+2} = X·F_{m+1} − q·F_m` with
arbitrary polynomial seeds — the single engine behind the wave kernels, the Ihara–Bass
per-eigenvalue NB power sums, and the NB walk-count matrices of arXiv 2606.27075 on a
`(q+1)`-regular graph. -/
noncomputable def chebLike (q : ℝ) (p₀ p₁ : Polynomial ℝ) : ℕ → Polynomial ℝ
  | 0 => p₀
  | 1 => p₁
  | (m + 2) => X * chebLike q p₀ p₁ (m + 1) - C q * chebLike q p₀ p₁ m

/-- The recursion holds at the evaluation level: evaluating the family at any spectrum point
`x` satisfies the same forward-difference scheme `f_{t+1}(x) = x·f_t(x) − q·f_{t-1}(x)` the
probe simulates directly on the graph. (Provenance tie between the Lean object and the
numerically verified wave propagation.) -/
theorem chebLike_eval_rec (q : ℝ) (p₀ p₁ : Polynomial ℝ) (m : ℕ) (x : ℝ) :
    (chebLike q p₀ p₁ (m + 2)).eval x
      = x * (chebLike q p₀ p₁ (m + 1)).eval x - q * (chebLike q p₀ p₁ m).eval x := by
  simp [chebLike]

/-- **Universal degree bound.** If the seeds satisfy `deg p₀ ≤ a` and `deg p₁ ≤ a + 1`, then
`deg (chebLike q p₀ p₁ m) ≤ a + m`. The coefficients of `chebLike q p₀ p₁ m` are (by
construction) polynomials in `q` alone — they carry no instance data. -/
theorem chebLike_natDegree_le (q : ℝ) (p₀ p₁ : Polynomial ℝ) (a : ℕ)
    (h₀ : p₀.natDegree ≤ a) (h₁ : p₁.natDegree ≤ a + 1) :
    ∀ m, (chebLike q p₀ p₁ m).natDegree ≤ a + m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 => simpa using h₀
    | 1 => exact h₁
    | (k + 2) =>
      have ih1 : (chebLike q p₀ p₁ (k + 1)).natDegree ≤ a + (k + 1) := ih (k + 1) (by omega)
      have ih0 : (chebLike q p₀ p₁ k).natDegree ≤ a + k := ih k (by omega)
      have hX : (X * chebLike q p₀ p₁ (k + 1)).natDegree ≤ a + (k + 2) := by
        refine le_trans (natDegree_mul_le) ?_
        have hx : (X : Polynomial ℝ).natDegree ≤ 1 := natDegree_X_le
        omega
      have hC : (C q * chebLike q p₀ p₁ k).natDegree ≤ a + (k + 2) := by
        refine le_trans (natDegree_mul_le) ?_
        have hc : (C q).natDegree = 0 := natDegree_C q
        omega
      show (X * chebLike q p₀ p₁ (k + 1) - C q * chebLike q p₀ p₁ k).natDegree ≤ a + (k + 2)
      exact le_trans (natDegree_sub_le _ _) (max_le hX hC)

/-- **Trace functionals lie in the moment span.** For ANY polynomial `P` of degree `< N` and
any finite spectrum family `η` over `s`, the trace functional `∑_b P.eval (η b)` is the
universal linear combination `∑_{j<N} P.coeff j · (∑_b (η b)^j)` of the power sums. On
`Cay(F_p, μ_n)` the power sums are exactly the `E_r` moment-ladder data — the wall's own
vocabulary. -/
theorem trace_eval_eq_moment_combo {ι : Type*} (s : Finset ι) (P : Polynomial ℝ) {N : ℕ}
    (hdeg : P.natDegree < N) (η : ι → ℝ) :
    ∑ b ∈ s, P.eval (η b) = ∑ j ∈ Finset.range N, P.coeff j * ∑ b ∈ s, η b ^ j := by
  calc ∑ b ∈ s, P.eval (η b)
      = ∑ b ∈ s, ∑ j ∈ Finset.range N, P.coeff j * η b ^ j :=
        Finset.sum_congr rfl fun b _ => eval_eq_sum_range' hdeg (η b)
    _ = ∑ j ∈ Finset.range N, ∑ b ∈ s, P.coeff j * η b ^ j := Finset.sum_comm
    _ = ∑ j ∈ Finset.range N, P.coeff j * ∑ b ∈ s, η b ^ j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]

/-- **Bounded-depth moment blindness (the decisive form).** Two spectrum families with equal
power sums for all `j < N` have EQUAL trace functionals for EVERY polynomial of degree `< N` —
in particular for every wave-kernel / NB-walk / Ihara–Bass trace identity at bounded depth.
No such identity can distinguish instances whose low moments agree, however different their
sup norms `M` are. -/
theorem trace_eval_eq_of_powerSums_eq {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (P : Polynomial ℝ) {N : ℕ} (hdeg : P.natDegree < N) (η : ι → ℝ) (η' : κ → ℝ)
    (hmom : ∀ j < N, ∑ b ∈ s, η b ^ j = ∑ b ∈ t, η' b ^ j) :
    ∑ b ∈ s, P.eval (η b) = ∑ b ∈ t, P.eval (η' b) := by
  rw [trace_eval_eq_moment_combo s P hdeg η, trace_eval_eq_moment_combo t P hdeg η']
  exact Finset.sum_congr rfl fun j hj => by rw [hmom j (Finset.mem_range.mp hj)]

/-- **The arXiv 2606.27075 no-go, wave-kernel face.** The forward-difference wave kernel at
time `m` is `chebLike q 1 X m` (seeds `(1, X)`), of degree `≤ m`; two spectra with equal power
sums to depth `m` have identical wave-kernel traces at every time `≤ m`. Combined with the
measured pair (`n = 16`, `p = 65617` vs `65633`: moments `j ≤ 6` equal to `2.4e-4`, `M`
differing `4.5%` — `probe_w13_wavekernel_trace.py` F3) this closes the identity face: a
bounded-depth wave-kernel trace formula cannot pin `M`. -/
theorem waveKernel_trace_blind {ι κ : Type*} (q : ℝ) (s : Finset ι) (t : Finset κ)
    (η : ι → ℝ) (η' : κ → ℝ) (m : ℕ)
    (hmom : ∀ j < m + 1, ∑ b ∈ s, η b ^ j = ∑ b ∈ t, η' b ^ j) :
    ∑ b ∈ s, (chebLike q 1 X m).eval (η b) = ∑ b ∈ t, (chebLike q 1 X m).eval (η' b) := by
  have hdeg : (chebLike q 1 X m).natDegree < m + 1 := by
    have := chebLike_natDegree_le q 1 X 0 (by simp) (by simpa using natDegree_X_le) m
    omega
  exact trace_eval_eq_of_powerSums_eq s t _ hdeg η η' hmom

/-- **The arXiv 2606.27075 no-go, Ihara–Bass power-sum face.** The per-eigenvalue NB power
sums `s_m(λ) = μ₊^m + μ₋^m` (`μ±` the roots of `x² − λx + q`) form the family
`chebLike q 2 X m` (seeds `(2, X)`), of degree `≤ m`: Hashimoto moments `tr(B^m)` are
moment-blind at bounded depth in exactly the same way. -/
theorem iharaBass_trace_blind {ι κ : Type*} (q : ℝ) (s : Finset ι) (t : Finset κ)
    (η : ι → ℝ) (η' : κ → ℝ) (m : ℕ)
    (hmom : ∀ j < m + 1, ∑ b ∈ s, η b ^ j = ∑ b ∈ t, η' b ^ j) :
    ∑ b ∈ s, (chebLike q 2 X m).eval (η b) = ∑ b ∈ t, (chebLike q 2 X m).eval (η' b) := by
  have h2 : ((2 : Polynomial ℝ)).natDegree ≤ 0 := by
    simpa using natDegree_C (2 : ℝ)
  have hdeg : (chebLike q 2 X m).natDegree < m + 1 := by
    have := chebLike_natDegree_le q 2 X 0 h2 (by simpa using natDegree_X_le) m
    omega
  exact trace_eval_eq_of_powerSums_eq s t _ hdeg η η' hmom

/-- **The arXiv 2606.27075 no-go, NB walk-count face.** The NB walk-count polynomials
(`N_1 = X`, `N_2 = X² − (q+1)`, `N_{m+1} = X·N_m − q·N_{m-1}`) are the family
`chebLike q X (X² − C (q+1))` reindexed (`N_{m+1} = chebLike … m`), of degree `≤ m + 1`:
NB walk-count traces are moment-blind at bounded depth. -/
theorem nbWalkCount_trace_blind {ι κ : Type*} (q : ℝ) (s : Finset ι) (t : Finset κ)
    (η : ι → ℝ) (η' : κ → ℝ) (m : ℕ)
    (hmom : ∀ j < m + 2, ∑ b ∈ s, η b ^ j = ∑ b ∈ t, η' b ^ j) :
    ∑ b ∈ s, (chebLike q X (X ^ 2 - C (q + 1)) m).eval (η b)
      = ∑ b ∈ t, (chebLike q X (X ^ 2 - C (q + 1)) m).eval (η' b) := by
  have h1 : (X : Polynomial ℝ).natDegree ≤ 1 := natDegree_X_le
  have h2 : ((X : Polynomial ℝ) ^ 2 - C (q + 1)).natDegree ≤ 2 := by
    refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
    · simpa using natDegree_pow_le (p := (X : Polynomial ℝ)) (n := 2)
    · simp [natDegree_C]
  have hdeg : (chebLike q X (X ^ 2 - C (q + 1)) m).natDegree < m + 2 := by
    have := chebLike_natDegree_le q X (X ^ 2 - C (q + 1)) 1 h1 h2 m
    omega
  exact trace_eval_eq_of_powerSums_eq s t _ hdeg η η' hmom

/-- **Non-vacuity guard.** The moment-equality hypothesis is instantiable by genuinely distinct
spectrum enumerations: the families `(1, −1)` and `(−1, 1)` over `Fin 2` have equal power sums
at every depth, so all three blindness theorems apply to them nontrivially. -/
example (N : ℕ) : ∀ j < N,
    ∑ b ∈ (univ : Finset (Fin 2)), (![(1 : ℝ), -1]) b ^ j
      = ∑ b ∈ (univ : Finset (Fin 2)), (![(-1 : ℝ), 1]) b ^ j := by
  intro j _
  simp [Fin.sum_univ_two]
  ring

-- Axiom audit (campaign law: only [propext, Classical.choice, Quot.sound], no sorryAx).
#print axioms chebLike_eval_rec
#print axioms chebLike_natDegree_le
#print axioms trace_eval_eq_moment_combo
#print axioms trace_eval_eq_of_powerSums_eq
#print axioms waveKernel_trace_blind
#print axioms iharaBass_trace_blind
#print axioms nbWalkCount_trace_blind

end ArkLib.ProximityGap.Frontier.W13WaveKernelTraceMomentSpan
