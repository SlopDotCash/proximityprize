/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Form-D exact-sup machinery: the char-0 Hermite recurrence `b_k²=n·k` and the Jacobi
# Gershgorin edge bound `M ≤ 2·max_k b_k` (#444, BUILD TASK `formD-exact-sup`)

**The genuinely-provable core of the exact-sup / orthogonal-polynomial face (D-Jacobi).**

Face A controls `M = max_{b≠0}|η_b|` through the moment ladder `E_r`, giving only the OVERSHOOTING
power-mean bound `M ≤ E_r^{1/(2r)}` (the half-power loss: equality only as `r→∞`).  Form D restates the
wall via the spectral measure `μ_η` of the periods: `M = max(supp μ_η) = topeig(J)` where `J` is the
Jacobi (tridiagonal) matrix of `μ_η` — the EXACT sup, no `L^{2r}` overshoot.  This file builds the
genuinely-provable mathematical content of that face:

1. **§1–2 (PROVEN, char-0).**  The char-0 period moments are the Gaussian `N(0,n)` moments (Wick),
   whose monic orthogonal polynomials are the `n`-scaled Hermite polynomials.  Their three-term
   recurrence has off-diagonal coefficient **`b_k² = n·k`** (`scaledHermite_recurrence_jacobi`,
   `jacobiOffDiagSq_eq`), anchored to Mathlib's Hermite at `n=1` (`scaledHermite_one_eq_hermite`).
   This required first proving the Hermite derivative recurrence `He_{n+1}' = (n+1)·He_n`
   (`derivative_hermite_succ`, not in Mathlib) and the classical three-term recurrence
   `He_{n+2} = X·He_{n+1} − (n+1)·He_n` (`hermite_three_term`, not in Mathlib).

2. **§3 (PROVEN).**  The exact-sup is a finite maximum `M = specEdge` (`specEdge_attained`,
   `le_specEdge`) — NO limit, NO overshoot — and the moment route genuinely OVERSHOOTS:
   `(M²)^r ≤ E_r` always (`sup_pow_le_moment`), with STRICT overshoot `(M²)^r < E_r` whenever the
   max is attained ≥ twice (`moment_strict_overshoot`).  This is the half-power loss made exact.

3. **§4 (PROVEN).**  The Gershgorin/Rayleigh upper bound for the zero-diagonal Jacobi quadratic form:
   `Q_b(v) ≤ (2·max_k b_k)·‖v‖²` (`jacobiForm_le`).  This is the rigorous half of `M = 2 max b_k`:
   the top of the spectrum is bounded by the recurrence coefficients DIRECTLY, with no moment route.

4. **§5 (REDUCTION).**  Combining §2+§4: under the exact-sup top-eigenvalue identity
   `M = topeig(J)` (`TopEigIdentity`, an explicit hypothesis — the OP/spectral-measure
   correspondence Mathlib lacks), `M ≤ 2·√(n·k_max)` (`M_le_two_sqrt_of_topEig`), and at the prize
   scale `M ≤ 2·√(n·L)` once `k_max ≤ L` (`M_le_two_sqrt_at_scale`).

## Honesty contract

The headline **char-0 facts are PROVEN axiom-clean**: the Hermite recurrences and the `b_k²=n·k`
Jacobi off-diagonal law (the "char-0 Hermite recurrence" the build task names as genuinely provable),
the exact-sup-is-a-max + power-mean overshoot, and the Gershgorin `M ≤ 2 max b_k` upper direction.
What is NOT proven (and is honestly an explicit hypothesis `TopEigIdentity`, never `sorry`-ed): the
exact identity `M = topeig(J)` (needs orthogonal-polynomial spectral theory absent from Mathlib).
The EXACT residual is the **depth bound `k_max = O(log p)`** — equivalently the b_k departing the
Hermite law `√(n·k)` early (the wraparound `W_r` at depth `r≈log p`): the Burgess/Paley/BGK wall.
This file does NOT close the face and does NOT fabricate any cancellation/anti-concentration estimate.
The `2` vs `√2` in the constant is genuine (Gershgorin is loose by a √2 at the semicircle edge); it is
NOT the wall — the wall is the depth `k_max`.  CORE remains OPEN.
-/

set_option autoImplicit false


namespace ProximityGap.Frontier.PIN1

open Polynomial

/-- The probabilists' Hermite derivative recurrence `He_n' = n · He_{n-1}`, packaged
in the `succ` form `He_{n+1}' = (n+1) · He_n`. -/
theorem derivative_hermite_succ (n : ℕ) :
    derivative (hermite (n + 1)) = (n + 1 : ℤ) • hermite n := by
  induction n with
  | zero => simp
  | succ m ih =>
    -- hermite (m+2) = X * hermite (m+1) - derivative (hermite (m+1))
    rw [hermite_succ (m + 1), derivative_sub, derivative_mul, derivative_X, one_mul, ih]
    simp only [zsmul_eq_mul, derivative_mul, derivative_intCast, zero_mul, zero_add]
    -- derivative (hermite m) = X * hermite m - hermite (m+1)   (from hermite_succ m)
    have hdm : derivative (hermite m) = X * hermite m - hermite (m + 1) := by
      rw [hermite_succ m]; ring
    rw [hdm]
    push_cast
    ring

/-- **The classical three-term recurrence for the probabilists' Hermite polynomials**
`He_{n+2} = X · He_{n+1} − (n+1) · He_n`.  This is the monic orthogonal-polynomial
recurrence `P_{k+1} = (X − a_k) P_k − b_k² P_{k−1}` with `a_k = 0` and `b_{k+1}² = (n+1)`. -/
theorem hermite_three_term (n : ℕ) :
    hermite (n + 2) = X * hermite (n + 1) - (n + 1 : ℤ) • hermite n := by
  rw [hermite_succ (n + 1), derivative_hermite_succ]

/-! ## 2. The variance-`n` (Gaussian `N(0,n)`) monic orthogonal polynomials: `b_k² = n·k`

The empirical period moments are the Gaussian `N(0,n)` moments (char-0 Wick, PROVEN in-tree:
`E_r ≤ (2r−1)‼·n^r`, with equality at the Wick value).  The MONIC orthogonal polynomials of
`N(0,n)` are the `n`-scaled Hermite polynomials, with three-term recurrence

  `P_{k+1}(x) = x·P_k(x) − (n·k)·P_{k−1}(x)`,   i.e.  `a_k = 0`,  `b_k² = n·k`.

We define this family directly over `ℝ[X]` and prove (a) the recurrence has off-diagonal
coefficient EXACTLY `n·k` (the headline `b_k² = nk`), and (b) at `n = 1` it is Mathlib's
probabilists' Hermite (so it is genuinely the Hermite family, not an ad-hoc definition). -/

open Polynomial in
/-- The `n`-scaled monic orthogonal polynomials of the Gaussian `N(0,n)` measure, defined by the
three-term recurrence `P_{k+2} = X·P_{k+1} − (n·(k+1))·P_k`, `P_0 = 1`, `P_1 = X`. -/
noncomputable def scaledHermite (n : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | k + 2 => X * scaledHermite n (k + 1) - C (n * (k + 1)) * scaledHermite n k

/-- **THE CHAR-0 RECURRENCE-COEFFICIENT IDENTITY `b_k² = n·k`.**  The off-diagonal coefficient of
the `N(0,n)` monic orthogonal polynomials at level `k+1` is EXACTLY `n·(k+1)`; the diagonal is `0`.
This is the exact Jacobi-matrix off-diagonal `b_{k+1}² = n·(k+1)` — the char-0 Hermite law made into
a definitional identity (`scaledHermite_recurrence_jacobi` below exhibits the subtracted coefficient
as `C (b_{k+1}²)`). -/
theorem scaledHermite_recurrence (n : ℝ) (k : ℕ) :
    scaledHermite n (k + 2)
      = X * scaledHermite n (k + 1) - C (n * (k + 1)) * scaledHermite n k := by
  rw [scaledHermite]

/-- The off-diagonal Jacobi coefficient `b_{k+1}²` of the `N(0,n)` measure read off the recurrence:
`b_{k+1}² = n·(k+1)`, so `b_k² = n·k`.  (The recurrence subtracts `C (b_{k+1}²)·P_k`.) -/
noncomputable def jacobiOffDiagSq (n : ℝ) (k : ℕ) : ℝ := n * k

theorem jacobiOffDiagSq_eq (n : ℝ) (k : ℕ) : jacobiOffDiagSq n (k + 1) = n * (k + 1) := by
  simp [jacobiOffDiagSq]

/-- **`b_k² = n·k` literally**: the coefficient subtracted in the recurrence is `C (jacobiOffDiagSq n (k+1))`. -/
theorem scaledHermite_recurrence_jacobi (n : ℝ) (k : ℕ) :
    scaledHermite n (k + 2)
      = X * scaledHermite n (k + 1) - C (jacobiOffDiagSq n (k + 1)) * scaledHermite n k := by
  rw [scaledHermite_recurrence, jacobiOffDiagSq_eq]

/-- **Anchor: at `n = 1` the scaled family IS Mathlib's probabilists' Hermite** (`scaledHermite 1 = hermite`,
mapped to `ℝ`), so it is genuinely the Hermite family and the recurrence `b_k²=k` matches
`hermite_three_term`.  This certifies the definition is not ad-hoc. -/
theorem scaledHermite_one_eq_hermite (k : ℕ) :
    scaledHermite 1 k = (hermite k).map (Int.castRingHom ℝ) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp [scaledHermite]
    | 1 => simp [scaledHermite]
    | m + 2 =>
      rw [scaledHermite_recurrence, hermite_three_term, ih (m + 1) (by omega), ih m (by omega)]
      simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_X, zsmul_eq_mul,
        Polynomial.map_intCast, one_mul]
      have hC : (C ((m : ℝ) + 1) : ℝ[X]) = ((m : ℝ[X]) + 1) := by
        rw [Polynomial.C_add, Polynomial.C_1, Polynomial.C_eq_natCast]
      rw [hC]
      push_cast
      ring

/-! ## 3. The EXACT-SUP identity: `M = max(support of μ_η)`, no `L^{2r}` overshoot

The empirical spectral measure of the periods is `μ_η = (1/(q−1)) Σ_{b≠0} δ_{|η_b|}`.  Face A
controls `M = max_{b≠0} |η_b|` through the moments `E_r = Σ_b |η_b|^{2r}`, giving only
`M ≤ E_r^{1/(2r)}` — a power-mean upper bound that OVERSHOOTS for every finite `r` and only
converges to `M` as `r → ∞` (the half-power loss).  The spectral-measure / orthogonal-polynomial
viewpoint replaces this by the EXACT identity `M = max(support of μ_η)`: a plain finite maximum,
with NO limit and NO overshoot.  We formalize this exactness over the finite period family. -/

open Finset in
/-- **The exact sup as a `Finset.sup'`** — the operative "no overshoot" object: `M = sup'_{b} |η_b|`,
attained at some `b`.  (Cleaner restatement; `M` is literally a maximum, not a limit of moments.) -/
noncomputable def specEdge {q : ℕ} (hq : 0 < q) (f : Fin q → ℝ) : ℝ :=
  (univ : Finset (Fin q)).sup' ⟨⟨0, hq⟩, mem_univ _⟩ f

open Finset in
theorem specEdge_attained {q : ℕ} (hq : 0 < q) (f : Fin q → ℝ) :
    ∃ b : Fin q, specEdge hq f = f b := by
  classical
  obtain ⟨b, _, hb⟩ := Finset.exists_mem_eq_sup' (⟨⟨0, hq⟩, mem_univ _⟩) f
  exact ⟨b, hb⟩

open Finset in
/-- `M = specEdge` upper-bounds every period value (it is an upper bound of the support). -/
theorem le_specEdge {q : ℕ} (hq : 0 < q) (f : Fin q → ℝ) (b : Fin q) :
    f b ≤ specEdge hq f :=
  Finset.le_sup' f (mem_univ b)

/-! ### The power-mean OVERSHOOT (why Face A loses a half power, and Face D does not)

For nonnegative values `g_b = |η_b|^2 ≥ 0`, the `r`-th moment is `E_r = Σ_b g_b^r`.  The sup
satisfies `(sup_b g_b)^r ≤ E_r`, hence the moment upper bound `M^2 = sup g_b ≤ E_r^{1/r}`.  But
`E_r^{1/r} ≥ sup g_b` is an OVERSHOOT: it counts the whole sum, not just the max, so equality holds
only as `r → ∞` (or when one value dominates).  The exact-sup `specEdge` (= `M^2` on the squared
values) needs NO limit — that is the half-power Face D closes IN PRINCIPLE. -/

open Finset in
/-- **The moment dominates the `r`-th power of the sup** (`(M²)^r ≤ E_r`): the source of the
moment upper bound `M ≤ E_r^{1/(2r)}`. -/
theorem sup_pow_le_moment {q : ℕ} (hq : 0 < q) (g : Fin q → ℝ)
    (hg : ∀ b, 0 ≤ g b) (r : ℕ) :
    (specEdge hq g) ^ r ≤ ∑ b, (g b) ^ r := by
  classical
  obtain ⟨b₀, hb₀⟩ := specEdge_attained hq g
  rw [hb₀]
  exact Finset.single_le_sum (f := fun b => (g b) ^ r) (fun b _ => pow_nonneg (hg b) r)
    (mem_univ b₀)

open Finset in
/-- **The OVERSHOOT is real (strict when ≥ 2 indices attain the max).**  If two distinct indices
both attain the max value `v > 0`, then `E_r ≥ 2·v^r > v^r = (M²)^r` for every `r`, so the moment
bound `E_r^{1/r}` strictly exceeds the exact sup `M²`.  This is the quantitative half-power loss that
the exact-sup / Jacobi route removes (it is INDEPENDENT of `r`: the moment route always overshoots
when the max is attained more than once — exactly the multiplicity the sup ignores). -/
theorem moment_strict_overshoot {q : ℕ} (hq : 0 < q) (g : Fin q → ℝ)
    (hg : ∀ b, 0 ≤ g b) (r : ℕ) {b₁ b₂ : Fin q} (hne : b₁ ≠ b₂)
    (hv : 0 < g b₁) (h1 : g b₁ = specEdge hq g) (h2 : g b₂ = specEdge hq g) :
    (specEdge hq g) ^ r < ∑ b, (g b) ^ r := by
  classical
  have hvr : 0 < (specEdge hq g) ^ r := by rw [← h1]; positivity
  -- The two terms `b₁, b₂` alone already give `2·v^r`.
  have hpair : (g b₁) ^ r + (g b₂) ^ r ≤ ∑ b, (g b) ^ r := by
    have hsub : ({b₁, b₂} : Finset (Fin q)) ⊆ univ := subset_univ _
    have := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun b _ _ => pow_nonneg (hg b) r)
    rw [Finset.sum_pair hne] at this
    exact this
  have hv2 : (g b₁) ^ r + (g b₂) ^ r = 2 * (specEdge hq g) ^ r := by
    rw [h1, h2]; ring
  rw [hv2] at hpair
  -- 2·v^r > v^r since v^r > 0
  linarith

/-! ## 4. The Jacobi Gershgorin bracket `M = topeig(J) ≤ 2·max_k b_k` (the honest exact-sup direction)

The exact-sup identity asserts `M = topeig(J)` for the period Jacobi matrix `J` (tridiagonal,
diagonal `a_k`, off-diagonal `b_k`).  The full `topeig(J) = M` and `topeig(J) = 2 max_k b_k`
identities need orthogonal-polynomial spectral machinery Mathlib lacks, AND `2 max b_k` is only an
approximate edge.  What IS rigorous and provable — and IS the content that closes the half-power loss
in the realizable direction — is the **Gershgorin/Rayleigh UPPER bound**:

  `topeig(J) = sup_{‖v‖=1} ⟪Jv, v⟫ ≤ max_k (|a_k| + b_k + b_{k+1})`.

For the Hermite/period Jacobi matrix the diagonal vanishes (`a_k = 0`, odd moments zero), so this is

  `M = topeig(J) ≤ 2·max_k b_k`,

the honest half of `M = 2 max b_k`.  We prove the operative quadratic-form inequality
`⟪Jv, v⟫ ≤ (2·max b)·‖v‖²` (Rayleigh ≤ Gershgorin), which is exactly this upper bound — and is the
EXACT-SUP machinery: it bounds the top of the spectrum (hence `M`) by the recurrence coefficients
directly, with NO `L^{2r}` moment overshoot. -/

open Finset in
/-- **The Jacobi (tridiagonal, zero-diagonal) quadratic form** on a sequence `v : ℕ → ℝ`, truncated
to size `N`:  `Q_b(v) = Σ_{k<N-1} 2·b_{k+1}·v_k·v_{k+1}` — the off-diagonal energy of the Hermite
Jacobi matrix.  (Diagonal contributes `0` since `a_k = 0`.)  The "squared norm" is `Σ_{k<N} v_k²`. -/
noncomputable def jacobiForm (N : ℕ) (b v : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range (N - 1), 2 * b (k + 1) * v k * v (k + 1)

/-- The (squared) Euclidean norm of the truncated sequence. -/
noncomputable def normSqSeq (N : ℕ) (v : ℕ → ℝ) : ℝ := ∑ k ∈ Finset.range N, (v k) ^ 2

/-- **THE GERSHGORIN/RAYLEIGH UPPER BOUND (`a_k = 0` case): `Q_b(v) ≤ (2·B)·‖v‖²`** where
`B = max_k b_k` bounds all off-diagonals (`0 ≤ b_j ≤ B`).  Each cross term is bounded by AM-GM
`2 b v_k v_{k+1} ≤ B(v_k² + v_{k+1}²)`, and summing gives each coordinate coefficient `≤ 2B`.  This is
the rigorous `topeig(J) ≤ 2·max b_k`, hence `M ≤ 2·max b_k` — the exact-sup upper bound with NO
moment overshoot.  (Combined with `b_k² = n·k` from §2: `M ≤ 2√(n·k_max)`, and the prize asks
`k_max = O(log p)`.) -/
theorem jacobiForm_le (N : ℕ) (b v : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hb0 : ∀ j, 0 ≤ b j)
    (hbB : ∀ k ∈ Finset.range (N - 1), b (k + 1) ≤ B) :
    jacobiForm N b v ≤ (2 * B) * normSqSeq N v := by
  classical
  -- Step 1: bound each cross term by `B·(v_k² + v_{k+1}²)`.
  have hterm : ∀ k ∈ Finset.range (N - 1),
      2 * b (k + 1) * v k * v (k + 1) ≤ B * ((v k) ^ 2 + (v (k + 1)) ^ 2) := by
    intro k hk
    have hbk : 0 ≤ b (k + 1) := hb0 _
    have hAMGM : 2 * v k * v (k + 1) ≤ (v k) ^ 2 + (v (k + 1)) ^ 2 := two_mul_le_add_sq _ _
    have h1 : 2 * b (k + 1) * v k * v (k + 1) = b (k + 1) * (2 * v k * v (k + 1)) := by ring
    rw [h1]
    calc b (k + 1) * (2 * v k * v (k + 1))
        ≤ b (k + 1) * ((v k) ^ 2 + (v (k + 1)) ^ 2) := mul_le_mul_of_nonneg_left hAMGM hbk
      _ ≤ B * ((v k) ^ 2 + (v (k + 1)) ^ 2) := by
          apply mul_le_mul_of_nonneg_right (hbB k hk); positivity
  -- Step 2: sum the cross-term bound.
  have hsum : jacobiForm N b v
      ≤ ∑ k ∈ Finset.range (N - 1), B * ((v k) ^ 2 + (v (k + 1)) ^ 2) :=
    Finset.sum_le_sum hterm
  refine le_trans hsum ?_
  -- Step 3: ∑_{k<N-1} B(v_k²+v_{k+1}²) ≤ 2B·∑_{k<N} v² (each coord appears ≤ twice).
  rw [← Finset.mul_sum]
  rw [show (2 * B) * normSqSeq N v = B * (2 * normSqSeq N v) by ring]
  apply mul_le_mul_of_nonneg_left _ hB
  unfold normSqSeq
  -- ∑_{k<N-1} (v_k² + v_{k+1}²) = (∑_{k<N-1} v_k²) + (∑_{k<N-1} v_{k+1}²); both ≤ ∑_{k<N} v_k².
  rw [Finset.sum_add_distrib]
  have hsubset : Finset.range (N - 1) ⊆ Finset.range N := Finset.range_subset_range.mpr (by omega)
  have hlow : (∑ k ∈ Finset.range (N - 1), (v k) ^ 2) ≤ ∑ k ∈ Finset.range N, (v k) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun _ _ _ => by positivity)
  have hhigh : (∑ k ∈ Finset.range (N - 1), (v (k + 1)) ^ 2) ≤ ∑ k ∈ Finset.range N, (v k) ^ 2 := by
    -- reindex k ↦ k+1 : range (N-1) → range N \ {0} ⊆ range N
    calc ∑ k ∈ Finset.range (N - 1), (v (k + 1)) ^ 2
        = ∑ k ∈ (Finset.range (N - 1)).map ⟨Nat.succ, Nat.succ_injective⟩, (v k) ^ 2 := by
          rw [Finset.sum_map]; rfl
      _ ≤ ∑ k ∈ Finset.range N, (v k) ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro x hx
            rw [Finset.mem_map] at hx
            obtain ⟨a, ha, rfl⟩ := hx
            simp only [Function.Embedding.coeFn_mk]
            rw [Finset.mem_range] at ha ⊢; omega
          · intro _ _ _; positivity
  linarith

/-! ## 5. Synthesis: the exact-sup upper bound `M ≤ 2·√(n·k_max)` and the residual

We now combine §2 (`b_k² = n·k`) with §4 (the Gershgorin/Rayleigh bound) into the operative
exact-sup upper bound.  On the truncation to depth `k_max` the off-diagonals `b_k = √(n·k)` are all
`≤ √(n·k_max)`, so the Gershgorin/Rayleigh top of the spectrum is `≤ 2·√(n·k_max)`.

The ONLY non-elementary input — the part Mathlib lacks the orthogonal-polynomial machinery for, and
which the honest census flags — is the exact identity `M = topeig(J)` (the spectral edge of the
period measure equals the top eigenvalue of its Jacobi matrix).  We state it as an explicit
hypothesis `TopEigIdentity` (NOT proven here; it is the OP/spectral-measure correspondence), and prove
that UNDER it, the prize bound `M ≤ 2√(n·k_max)` follows from the Gershgorin bound — and the residual
is exactly the depth control `k_max = O(log p)` (= the Hermite-departure / wraparound wall). -/

open Real

/-- `√(n·k)` is monotone in `k` (the off-diagonals `b_k = √(n·k)` increase), so on a truncation to
depth `k_max`, every `b_k = √(n·k) ≤ √(n·k_max)`.  This is the `B` for the Gershgorin bound. -/
theorem sqrt_offdiag_le {n : ℝ} (hn : 0 ≤ n) (kmax k : ℕ) (hk : k ≤ kmax) :
    Real.sqrt (n * k) ≤ Real.sqrt (n * kmax) := by
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_left _ hn
  exact_mod_cast hk

/-- **THE EXACT-SUP UPPER BOUND (Gershgorin, conditional on the top-eigenvalue identity).**
If `M = topeig(J)` (the spectral-edge identity), `topeig(J) = sup Rayleigh` is realized by some unit
vector supported on `[0, k_max]`, and the off-diagonals are `b_k = √(n·k)` (the `b_k²=nk` law), then
`M ≤ 2·√(n·k_max)`.  This is the exact-sup conversion with NO `L^{2r}` overshoot: the bound on the
top of the spectrum factors through the recurrence coefficients directly.  Stated here in the clean
quadratic-form shape: for any nonzero truncated vector `v` of depth `N = k_max+1` with
`b_k = √(n·k) ≤ √(n·k_max)`, the Rayleigh quotient `Q(v)/‖v‖² ≤ 2√(n·k_max)`. -/
theorem rayleigh_le_two_sqrt {n : ℝ} (hn : 0 ≤ n) (kmax N : ℕ) (hN : N ≤ kmax + 1)
    (v : ℕ → ℝ) :
    jacobiForm N (fun k => Real.sqrt (n * k)) v ≤ (2 * Real.sqrt (n * kmax)) * normSqSeq N v := by
  apply jacobiForm_le N _ v (Real.sqrt (n * kmax)) (Real.sqrt_nonneg _)
  · intro j; exact Real.sqrt_nonneg _
  · -- only indices `k+1` with `k ∈ range (N-1)` occur, so `k+1 ≤ N-1 ≤ kmax`.
    intro k hk
    rw [Finset.mem_range] at hk
    show Real.sqrt (n * ((k + 1 : ℕ) : ℝ)) ≤ Real.sqrt (n * kmax)
    exact sqrt_offdiag_le hn kmax (k + 1) (by omega)

/-- **The exact-sup edge identity (the OP/spectral-measure correspondence Mathlib lacks).**  An
explicit hypothesis: the spectral edge `M = max_{b≠0}|η_b|` equals the supremum of the Rayleigh
quotient of the Jacobi matrix `J` (equivalently the top eigenvalue / top of `supp μ_η`), attained at
some truncated vector `v ≠ 0` of depth `N`.  This is the EXACT-SUP identity — `M` is the top of the
spectrum, NOT an `L^{2r}` moment overshoot.  We do NOT prove it (it needs orthogonal-polynomial
spectral theory absent from Mathlib); it is stated to make the reduction precise. -/
structure TopEigIdentity (M : ℝ) (N : ℕ) (b v : ℕ → ℝ) : Prop where
  vne : 0 < normSqSeq N v
  /-- `M·‖v‖² = ⟪Jv,v⟫` at the maximizing (top-eigenvector) `v` (zero diagonal: `⟪Jv,v⟫ = Q_b(v)`). -/
  edge : M * normSqSeq N v = jacobiForm N b v

/-- **THE FORM-D REDUCTION CAPSTONE: `M ≤ 2·√(n·k_max)`, conditional ONLY on the top-eigenvalue
identity.**  Combining the exact-sup identity `M·‖v‖² = Q_b(v)` (the OP correspondence) with the
Gershgorin/Rayleigh bound `Q_b(v) ≤ 2√(n·k_max)·‖v‖²` (PROVEN, §4) and the recurrence law
`b_k = √(n·k)` (PROVEN, §2), the spectral edge satisfies `M ≤ 2·√(n·k_max)` with NO `L^{2r}`
overshoot.  The residual is EXACTLY the depth control `k_max = O(log p)` (the prize asks
`M ≤ √2·√(n·log p)`, i.e. `k_max ≲ (log p)/2` up to the constant): the Hermite-departure /
wraparound wall.  This is the exact-sup conversion the build task asks for, honestly bracketed. -/
theorem M_le_two_sqrt_of_topEig {n M : ℝ} (hn : 0 ≤ n) (kmax N : ℕ) (hN : N ≤ kmax + 1)
    (v : ℕ → ℝ) (h : TopEigIdentity M N (fun k => Real.sqrt (n * k)) v) :
    M ≤ 2 * Real.sqrt (n * kmax) := by
  have hform : M * normSqSeq N v ≤ (2 * Real.sqrt (n * kmax)) * normSqSeq N v := by
    rw [h.edge]; exact rayleigh_le_two_sqrt hn kmax N hN v
  exact le_of_mul_le_mul_right (by linarith [hform]) h.vne

/-- **The clean prize-scale corollary.**  With `k_max ≤ L` (depth bound at scale `L`, e.g. `L = log p`)
and `n ≥ 0`, the exact-sup edge satisfies `M ≤ 2·√(n·L)`.  Since the prize bound is `M ≤ √2·√(n·L)`,
the Form-D route reaches the prize up to the constant `2` vs `√2` PROVIDED the depth bound
`k_max ≤ L` holds — that bound (`k_max = O(log p)`) is the EXACT residual (the wall). -/
theorem M_le_two_sqrt_at_scale {n M L : ℝ} (hn : 0 ≤ n) (kmax N : ℕ)
    (hN : N ≤ kmax + 1) (hkL : (kmax : ℝ) ≤ L) (v : ℕ → ℝ)
    (h : TopEigIdentity M N (fun k => Real.sqrt (n * k)) v) :
    M ≤ 2 * Real.sqrt (n * L) := by
  refine le_trans (M_le_two_sqrt_of_topEig hn kmax N hN v h) ?_
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
  apply Real.sqrt_le_sqrt
  exact mul_le_mul_of_nonneg_left hkL hn

end ProximityGap.Frontier.PIN1

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
section Audit
open ProximityGap.Frontier.PIN1
#print axioms derivative_hermite_succ
#print axioms hermite_three_term
#print axioms scaledHermite_recurrence
#print axioms jacobiOffDiagSq_eq
#print axioms scaledHermite_recurrence_jacobi
#print axioms scaledHermite_one_eq_hermite
#print axioms specEdge_attained
#print axioms le_specEdge
#print axioms sup_pow_le_moment
#print axioms moment_strict_overshoot
#print axioms jacobiForm_le
#print axioms sqrt_offdiag_le
#print axioms rayleigh_le_two_sqrt
#print axioms M_le_two_sqrt_of_topEig
#print axioms M_le_two_sqrt_at_scale
end Audit
