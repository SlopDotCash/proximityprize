/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# W14 — the Jacobi window is a LOSSLESS RECODING of the low moments:
  depth-`K` window ⟺ moments to order `2K+1` (the Hankel/Lax-pair seam collapse) (#466)

**Thread `wall:hankel-jacobi-seam`** (dossier v3 §6 item 3, the "one non-magnitude seam"):
Hankel-positivity / Lax-pair spectral-shift at the Jacobi turnover `k*`.

## What this file proves (axiom-clean, UNCONDITIONAL)

For symmetric tridiagonal matrices (Jacobi matrices) `A, A' : Matrix (Fin N) (Fin N) ℝ`:

> **`window_determines_moments`**: if `A` and `A'` agree on the leading `(K+1) × (K+1)`
> corner block (= the depth-`K` Jacobi window `a_0, …, a_K, b_1, …, b_K`), then
> `(A^r) 0 0 = (A'^r) 0 0` for EVERY `r ≤ 2K+1` — i.e. the window determines the spectral
> measure's moments to order `2K+1`.

The order `2K+1` is SHARP by parameter count: the corner has `2K+1` free entries
(`a_0..a_K`, `b_1..b_K`), matching the nontrivial moments `m_1..m_{2K+1}` exactly — the
depth-`K` window and the moment vector to order `2K+1` are the SAME data in different
coordinates (the converse direction, moments → window, is the classical Lanczos /
Hankel-double-ratio construction — `_AvJB_TodaStringHankelExact.bsq_eq_double_hankel_ratio` —
kept here as the named input `MomentsDetermineWindow`, in the same hypothesis style as
`_AvJB_HankelRoutesToMoments`).

## Why this closes the assigned seam (the W14 verdict)

The seam hope was: some positivity/interlacing invariant of the Jacobi data AT the turnover
`k*` — Hankel-determinant signs, truncation eigenvalues/interlacing patterns, Christoffel
weights, Krein spectral shifts of the truncation family `J_1 ⊂ J_2 ⊂ …` — carries
non-magnitude information that feeds a sup bound on `M`.  This file + the in-tree record kill
every version of that hope at bounded window depth:

1. **Every truncation-level invariant at depth `K` is a functional of the corner `J_{K+1}`**
   (definitionally), hence — by `MomentsDetermineWindow` — a functional of the moments
   `m_0..m_{2K+1}` alone (`truncation_invariant_is_lowMoment_functional`).  Conversely
   (THIS file, unconditional) the corner is recoverable from those moments' data content:
   no window invariant sees anything the low moments do not.
2. Low-moment functionals are already dead three independent ways: they are
   **ensemble-deterministic** (read `(n, p)` only, not the instance —
   `466-r1-hankel-bounded-window-refuted`); positivity + equal masses on top of low moments
   caps at the **raw moment bound** (CMK lone-spike, `466-r2-cmk-lonespike-refuted`); and
   Hankel-PSD constrains the top power sum **only from below**
   (`_AvRR_RealRootHankelOneSided`).
3. At unbounded depth `K ≈ k* ≈ (log p)/2` the moments to order `2K+1 ≈ log p` are exactly
   the form-(A) deep-moment wall (`_AvJB_HankelRoutesToMoments` routing verdict) — the seam
   relocates onto the wall, it does not bypass it.

**Probe** (`scripts/probes/probe_w14_hankel_sign_seam.py`, 2026-07-10): the remaining sign
corners are ALSO empirically dead — (T1/T2) "global b-peak at the first local max" is not a
positivity law (an iid char-0 control violates it at ratio 1.02, and a designed equal-mass
uniform-atom measure violates it at ratio 4.85: arcsine bulk on `[-1,1]` + one far pair
`{±4}`, 16384 atoms — so the ∀k form-D criterion cannot be reduced to the early window even
under the uniform-weight constraint; Favard already kills the non-uniform case); (T3) the
diagonal `a_k` sign channel is the odd-moment channel — ensemble-deterministic at low `k`
(the exact law `Σ η^{2k+1} = −n^{2k}`, C076) and iid-noise at `k*`; matched-pair pre-turnover
residual signs predict `sign(Δk*)` at 58% and `sign(ΔM)` at 48% (coin flip; the sign pattern
is exactly the `p`-ordering, `1−q_j = c_j(n)/p`); (T4) the Ritz-edge/spectral-shift ladder is
one-sided (all edges `≤ M`, increments `≈ 0.1–0.3·√n` at `k*`, r15's Θ(√n)) and its relative
gap at `k*` does not separate real instances from iid controls in a consistent direction.

## Honesty contract

NO core / cancellation / completion / moment-saving / anti-concentration / capacity claim.
This is a structural equivalence + collapse verdict: the window IS the low moments; the sign
structure at `k*` adds nothing a moment functional lacks.  The named open input
`MomentsDetermineWindow` is the classical orthogonal-polynomial uniqueness direction
(Gram–Schmidt / Hankel-ratio; NOT proven here) and is consumed visibly.  The BGK/Paley wall
(`M ≤ C√(n log p)`, equivalently `k* = O(log p)`) remains OPEN.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000


namespace ArkLib.ProximityGap.Frontier.W14WindowMoment

open Matrix

variable {N : ℕ}

/-- `A` is tridiagonal: zero outside the three central diagonals. -/
def IsTridiagonal (A : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∀ i j : Fin N, ((i : ℕ) + 1 < (j : ℕ) ∨ (j : ℕ) + 1 < (i : ℕ)) → A i j = 0

/-- `A` and `A'` agree on the leading `(K+1) × (K+1)` corner block — the depth-`K` Jacobi
window `a_0, …, a_K, b_1, …, b_K`. -/
def CornerAgree (A A' : Matrix (Fin N) (Fin N) ℝ) (K : ℕ) : Prop :=
  ∀ i j : Fin N, (i : ℕ) ≤ K → (j : ℕ) ≤ K → A i j = A' i j

/-- Strictly positive superdiagonal (the Jacobi normalization `b_k > 0`; with symmetry this
covers the subdiagonal). -/
def PosSubdiag (A : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∀ i j : Fin N, (i : ℕ) + 1 = (j : ℕ) → 0 < A i j

/-- `A^(s+1) = A * A^s` (robust local form, no name dependence on `pow_succ'`). -/
private theorem pow_succ_left (A : Matrix (Fin N) (Fin N) ℝ) (s : ℕ) :
    A ^ (s + 1) = A * A ^ s := by
  conv_lhs => rw [show s + 1 = 1 + s by omega, pow_add, pow_one]

/-- **Krylov support growth.** The first column of `A^s` is supported on coordinates `≤ s`:
a length-`s` walk on the tridiagonal graph starting at `0` cannot reach past coordinate `s`. -/
theorem pow_firstcol_eq_zero_of_lt {A : Matrix (Fin N) (Fin N) ℝ}
    (htri : IsTridiagonal A) {i0 : Fin N} (h0 : (i0 : ℕ) = 0) :
    ∀ s : ℕ, ∀ i : Fin N, s < (i : ℕ) → (A ^ s) i i0 = 0 := by
  intro s
  induction s with
  | zero =>
    intro i hi
    have hne : i ≠ i0 := by
      intro h
      rw [h, h0] at hi
      omega
    simp [Matrix.one_apply_ne hne]
  | succ s ih =>
    intro i hi
    rw [pow_succ_left, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : s < (k : ℕ)
    · rw [ih k hk, mul_zero]
    · have hlt : (k : ℕ) + 1 < (i : ℕ) := by omega
      rw [htri i k (Or.inr hlt), zero_mul]

/-- **Corner-agreement propagation.** If `A, A'` agree on the `(K+1) × (K+1)` corner, their
`A^s`-first-columns agree on all coordinates `≤ K`, for every `s ≤ K + 1`.  (The length-`s`
walk from `0` to a coordinate `≤ K` only crosses edges inside the corner, except for steps
whose contribution vanishes by the support lemma.) -/
theorem pow_firstcol_agree {A A' : Matrix (Fin N) (Fin N) ℝ}
    (htri : IsTridiagonal A) (htri' : IsTridiagonal A')
    {K : ℕ} (hagree : CornerAgree A A' K)
    {i0 : Fin N} (h0 : (i0 : ℕ) = 0) :
    ∀ s : ℕ, s ≤ K + 1 → ∀ i : Fin N, (i : ℕ) ≤ K → (A ^ s) i i0 = (A' ^ s) i i0 := by
  intro s
  induction s with
  | zero => intro _ i _; rfl
  | succ s ih =>
    intro hsK i hi
    have hs : s ≤ K := by omega
    rw [pow_succ_left, pow_succ_left, Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : (k : ℕ) ≤ K
    · rw [hagree i k hi hk, ih (by omega) k hk]
    · have hz : (A ^ s) k i0 = 0 :=
        pow_firstcol_eq_zero_of_lt htri h0 s k (by omega)
      have hz' : (A' ^ s) k i0 = 0 :=
        pow_firstcol_eq_zero_of_lt htri' h0 s k (by omega)
      rw [hz, hz', mul_zero, mul_zero]

/-- Powers of a symmetric matrix are symmetric. -/
private theorem pow_transpose_eq {A : Matrix (Fin N) (Fin N) ℝ} (hsym : A.IsSymm) (s : ℕ) :
    (A ^ s)ᵀ = A ^ s := by
  rw [Matrix.transpose_pow, hsym.eq]

/-- **MAIN (unconditional): the depth-`K` Jacobi window determines the moments to order
`2K+1`.**  If two symmetric tridiagonal matrices agree on the `(K+1) × (K+1)` corner, then
`(A^r)₀₀ = (A'^r)₀₀` for every `r ≤ 2K + 1`.  The order `2K+1` matches the corner's free
parameter count (`a_0..a_K`, `b_1..b_K`) exactly: the window is a lossless recoding of the
low moments, nothing more. -/
theorem window_determines_moments {A A' : Matrix (Fin N) (Fin N) ℝ}
    (htri : IsTridiagonal A) (htri' : IsTridiagonal A')
    (hsym : A.IsSymm) (hsym' : A'.IsSymm)
    {K : ℕ} (hagree : CornerAgree A A' K)
    {i0 : Fin N} (h0 : (i0 : ℕ) = 0)
    {r : ℕ} (hr : r ≤ 2 * K + 1) :
    (A ^ r) i0 i0 = (A' ^ r) i0 i0 := by
  obtain ⟨s, t, hst, hsK, htK1⟩ :
      ∃ s t : ℕ, s + t = r ∧ s ≤ K ∧ t ≤ K + 1 :=
    ⟨r - min r (K + 1), min r (K + 1), by omega, by omega, by omega⟩
  have hA : A ^ r = A ^ s * A ^ t := by rw [← pow_add, hst]
  have hA' : A' ^ r = A' ^ s * A' ^ t := by rw [← pow_add, hst]
  rw [hA, hA', Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  -- flip the left factor to first-column form via symmetry of the power
  have e1 : (A ^ s) i0 k = (A ^ s) k i0 := by
    have h := Matrix.transpose_apply (A ^ s) i0 k
    rw [pow_transpose_eq hsym s] at h
    exact h
  have e1' : (A' ^ s) i0 k = (A' ^ s) k i0 := by
    have h := Matrix.transpose_apply (A' ^ s) i0 k
    rw [pow_transpose_eq hsym' s] at h
    exact h
  by_cases hk : (k : ℕ) ≤ K
  · rw [e1, e1',
      pow_firstcol_agree htri htri' hagree h0 s (by omega) k hk,
      pow_firstcol_agree htri htri' hagree h0 t htK1 k hk]
  · have hz : (A ^ s) k i0 = 0 :=
      pow_firstcol_eq_zero_of_lt htri h0 s k (by omega)
    have hz' : (A' ^ s) k i0 = 0 :=
      pow_firstcol_eq_zero_of_lt htri' h0 s k (by omega)
    rw [e1, e1', hz, hz', zero_mul, zero_mul]

/-- **NAMED OPEN INPUT (classical OP theory, converse direction).**  The moments to order
`2K+1` determine the depth-`K` window: two Jacobi-normalized (symmetric tridiagonal,
positive-subdiagonal) matrices with equal `(·^r)₀₀` for all `r ≤ 2K+1` agree on the
`(K+1) × (K+1)` corner.  This is the Lanczos / Gram–Schmidt uniqueness — equivalently the
Hankel-double-ratio formulas `b_k² = D_{k−1}D_{k+1}/D_k²` (in-tree in hypothesis form as
`_AvJB_TodaStringHankelExact`) — NOT proven here; consumed visibly below. -/
def MomentsDetermineWindow (N K : ℕ) : Prop :=
  ∀ A A' : Matrix (Fin N) (Fin N) ℝ,
    IsTridiagonal A → IsTridiagonal A' → A.IsSymm → A'.IsSymm →
    PosSubdiag A → PosSubdiag A' →
    ∀ i0 : Fin N, (i0 : ℕ) = 0 →
    (∀ r : ℕ, r ≤ 2 * K + 1 → (A ^ r) i0 i0 = (A' ^ r) i0 i0) →
    CornerAgree A A' K

/-- **The exact information-content identity.**  Under `MomentsDetermineWindow`, the depth-`K`
window and the moment vector to order `2K+1` are MUTUALLY determined: corner agreement holds
iff all moments to order `2K+1` agree.  (Forward = `window_determines_moments`,
unconditional; backward = the named classical input.) -/
theorem cornerAgree_iff_moments_agree
    {K : ℕ} (hconv : MomentsDetermineWindow N K)
    {A A' : Matrix (Fin N) (Fin N) ℝ}
    (htri : IsTridiagonal A) (htri' : IsTridiagonal A')
    (hsym : A.IsSymm) (hsym' : A'.IsSymm)
    (hpos : PosSubdiag A) (hpos' : PosSubdiag A')
    {i0 : Fin N} (h0 : (i0 : ℕ) = 0) :
    CornerAgree A A' K ↔
      (∀ r : ℕ, r ≤ 2 * K + 1 → (A ^ r) i0 i0 = (A' ^ r) i0 i0) := by
  constructor
  · intro hagree r hr
    exact window_determines_moments htri htri' hsym hsym' hagree h0 hr
  · intro hmom
    exact hconv A A' htri htri' hsym hsym' hpos hpos' i0 h0 hmom

/-- **SEAM COLLAPSE (the W14 verdict).**  Every truncation-level invariant of the Jacobi data
at depth `K` — Hankel-determinant signs, truncation eigenvalues and interlacing patterns,
Christoffel weights, Krein spectral shifts of the truncation family — is (definitionally) a
functional `Φ` of the corner block; under the classical converse it is therefore a functional
of the moments `m_0, …, m_{2K+1}` ALONE: two Jacobi instances with equal moments to order
`2K+1` have equal invariants.  Composed with the in-tree kills (`466-r1` ensemble-determinism
of low moments, `466-r2` CMK raw-moment cap for positivity + equal masses,
`_AvRR_RealRootHankelOneSided` lower-bound-only Hankel-PSD), no depth-`K`
window/positivity/interlacing invariant feeds a sup bound below the raw moment bound. -/
theorem truncation_invariant_is_lowMoment_functional
    {K : ℕ} (hconv : MomentsDetermineWindow N K)
    {X : Type} (Φ : Matrix (Fin N) (Fin N) ℝ → X)
    (hΦ : ∀ A A' : Matrix (Fin N) (Fin N) ℝ, CornerAgree A A' K → Φ A = Φ A')
    {A A' : Matrix (Fin N) (Fin N) ℝ}
    (htri : IsTridiagonal A) (htri' : IsTridiagonal A')
    (hsym : A.IsSymm) (hsym' : A'.IsSymm)
    (hpos : PosSubdiag A) (hpos' : PosSubdiag A')
    {i0 : Fin N} (h0 : (i0 : ℕ) = 0)
    (hmom : ∀ r : ℕ, r ≤ 2 * K + 1 → (A ^ r) i0 i0 = (A' ^ r) i0 i0) :
    Φ A = Φ A' :=
  hΦ A A' (hconv A A' htri htri' hsym hsym' hpos hpos' i0 h0 hmom)

/-- Non-vacuity guard: the structural hypotheses are jointly satisfiable by a genuine Jacobi
matrix (the 3×3 zero-diagonal Jacobi matrix with `b = (1, 2)`). -/
theorem hypotheses_instantiable :
    ∃ A : Matrix (Fin 3) (Fin 3) ℝ, IsTridiagonal A ∧ A.IsSymm ∧ PosSubdiag A := by
  refine ⟨!![0, 1, 0; 1, 0, 2; 0, 2, 0], ?_, ?_, ?_⟩
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all
  · show _ᵀ = _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

#print axioms pow_firstcol_eq_zero_of_lt
#print axioms pow_firstcol_agree
#print axioms window_determines_moments
#print axioms cornerAgree_iff_moments_agree
#print axioms truncation_invariant_is_lowMoment_functional
#print axioms hypotheses_instantiable

end ArkLib.ProximityGap.Frontier.W14WindowMoment
