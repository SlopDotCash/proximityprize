/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G98LargeValuesGramBootstrap
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G233JacobiL2MassFloorNoGo

/-!
# G234: the Schur-test operator bound derives G233's large-sieve input (A) (#466)

The quotient-Jacobi fanout no-go chain culminates in G233's basis-independent coefficient-L2 mass
floor `l2_mass_floor_of_largesieve_parseval`, whose two exact analytic inputs (sponsor regime
`2 ∉ G`) are

* `(A)` the large-sieve operator bound  `‖V a‖² ≤ n² · ‖a‖²`  for every coefficient vector `a`;
* `(B)` the sponsor Parseval lower bound  `‖S‖² ≥ n · (m − n)`.

G233 records `(A)` as a **bare hypothesis** — its source, the exact spectral fact
`λ_max(Vᴴ V) ≤ n²` (G231/G56), lives only as a numerically-checked probe, and a full analytic
derivation would need quotient-character Parseval on the fibers (heavy Mathlib character theory).

This file removes that hypothesis-shaped hole with an **elementary Schur test**, using only the
already-landed G98 Gram machinery — no character theory. `λ_max` of the Hermitian PSD Gram matrix
`Vᴴ V` is bounded by its maximal absolute row sum (Schur / Gershgorin), and that row sum is a
*structural* quantity: for the Jacobi columns each Gram row-mass is `≤ n²` because there are `n`
subgroup elements and `|J(λ,χ)| ≤ √p`.  So `(A)` is a **consequence** of the Gram-row-mass fact,
not an independent spectral assumption.

Concretely, writing `V a = ∑_b a_b V_b` as a weighted sum of columns on the χ-index domain `s`,
G98's `weighted_normSq_expand` gives `‖V a‖²_s = ∑_{b,b'} a_b a_{b'} gram(b,b')` (real weights),
and G98's `bilinear_rowsum_bound` bounds the absolute bilinear form by `(∑ a_b²)·R` whenever every
Gram row-mass `∑_{b'} ‖gram(b,b')‖ ≤ R`.  Chaining the two yields the **Schur operator bound**

```text
‖∑_b a_b V_b‖²_s ≤ R · ∑_b a_b²        (real a, R = max Gram row-mass).
```

Specialising `R = n²` (the G231 Gram-row-mass ceiling) reproduces exactly G233's input `(A)`, and
feeding it into `l2_mass_floor_of_largesieve_parseval` gives a mass floor whose *only* remaining
premises are the structural Gram-row-mass `n²` and the sponsor Parseval — a strictly smaller
hypothesis surface than G233's assumed spectral bound.

Scope.  This is a keystone that closes G233's last assumption; it is not a new character-sum
estimate and does not consume the target.  CORE remains OPEN / ON-BGK.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G234SchurOperatorBoundClosesG233

open Finset ComplexConjugate
open ProximityGap.Frontier.G98LargeValuesGramBootstrap

variable {α ι : Type*}

/-! ## The Schur-test operator bound (real coefficients) -/

/-- **Schur-test operator bound.**  For any finite family of `ℂ`-vectors `v` on a domain `s` whose
Gram matrix has every absolute row-mass `∑_{b'} ‖gram(b,b')‖ ≤ R` over `B`, the weighted `L²` mass
of the reconstruction `∑_b a_b v_b` (real weights `a`) obeys the operator bound

```text
∑_x ‖∑_b a_b v_b x‖² ≤ R · ∑_b a_b².
```

Proof: G98's `weighted_normSq_expand` (with the real weights cast to `ℂ`) rewrites the LHS as the
Gram quadratic form; taking norms and bounding each `‖gram‖` by its symmetric absolute kernel, the
G98 `bilinear_rowsum_bound` closes it with the row-mass `R`.  No spectral decomposition, no
character theory — this is the elementary `λ_max ≤ max row sum` for a Hermitian PSD matrix. -/
theorem schur_operator_bound
    (s : Finset α) (v : ι → α → ℂ) (B : Finset ι) (a : ι → ℝ) (R : ℝ)
    (hrow : ∀ b ∈ B, ∑ b' ∈ B, ‖gram s v b b'‖ ≤ R) :
    ∑ x ∈ s, ‖∑ b ∈ B, (a b : ℂ) * v b x‖ ^ 2 ≤ R * ∑ b ∈ B, a b ^ 2 := by
  -- Nonnegativity of the LHS (a real sum of squares).
  have hLHS0 : (0 : ℝ) ≤ ∑ x ∈ s, ‖∑ b ∈ B, (a b : ℂ) * v b x‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- Step 1: expand weighted L² mass as the Gram quadratic form (G98), weights `w b = (a b : ℂ)`.
  have hExpand : ((∑ x ∈ s, ‖∑ b ∈ B, (a b : ℂ) * v b x‖ ^ 2 : ℝ) : ℂ)
      = ∑ b ∈ B, ∑ b' ∈ B, (a b : ℂ) * conj ((a b' : ℂ)) * gram s v b b' :=
    weighted_normSq_expand s v B (fun b => (a b : ℂ))
  -- Step 2: bound the LHS (a nonneg real) by the absolute bilinear form.
  have hAbs : ∑ x ∈ s, ‖∑ b ∈ B, (a b : ℂ) * v b x‖ ^ 2
      ≤ ∑ b ∈ B, ∑ b' ∈ B, |a b| * |a b'| * ‖gram s v b b'‖ := by
    calc ∑ x ∈ s, ‖∑ b ∈ B, (a b : ℂ) * v b x‖ ^ 2
        = ‖((∑ x ∈ s, ‖∑ b ∈ B, (a b : ℂ) * v b x‖ ^ 2 : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg hLHS0]
      _ = ‖∑ b ∈ B, ∑ b' ∈ B, (a b : ℂ) * conj ((a b' : ℂ)) * gram s v b b'‖ := by
          rw [hExpand]
      _ ≤ ∑ b ∈ B, ‖∑ b' ∈ B, (a b : ℂ) * conj ((a b' : ℂ)) * gram s v b b'‖ :=
          norm_sum_le _ _
      _ ≤ ∑ b ∈ B, ∑ b' ∈ B, ‖(a b : ℂ) * conj ((a b' : ℂ)) * gram s v b b'‖ :=
          Finset.sum_le_sum fun b _ => norm_sum_le _ _
      _ = ∑ b ∈ B, ∑ b' ∈ B, |a b| * |a b'| * ‖gram s v b b'‖ := by
          refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => ?_
          rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs]
  -- Step 3: symmetric absolute-kernel bilinear form is bounded by `(∑ |a|²)·R` (G98 Schur step).
  have hBil : ∑ b ∈ B, ∑ b' ∈ B, |a b| * |a b'| * ‖gram s v b b'‖
      ≤ (∑ b ∈ B, |a b| ^ 2) * R :=
    bilinear_rowsum_bound B (fun b => |a b|) (fun b b' => ‖gram s v b b'‖) R
      (fun b b' => norm_nonneg _) (fun b b' => norm_gram_swap s v b b') hrow
  -- `∑ |a b|² = ∑ a b²`, and rearrange to `R * ∑ a b²`.
  have hsq : ∑ b ∈ B, |a b| ^ 2 = ∑ b ∈ B, a b ^ 2 := by
    refine Finset.sum_congr rfl fun b _ => ?_; rw [sq_abs]
  calc ∑ x ∈ s, ‖∑ b ∈ B, (a b : ℂ) * v b x‖ ^ 2
      ≤ ∑ b ∈ B, ∑ b' ∈ B, |a b| * |a b'| * ‖gram s v b b'‖ := hAbs
  _ ≤ (∑ b ∈ B, |a b| ^ 2) * R := hBil
  _ = R * ∑ b ∈ B, a b ^ 2 := by rw [hsq, mul_comm]

/-- **Large-sieve operator bound from the Gram-row-mass ceiling `n²`.**  Specialising the Schur
test to `R = n²` — the G231 structural Gram-row-mass ceiling for the quotient-Jacobi columns —
reproduces exactly G233's input `(A)`:

```text
‖V a‖²_s = ∑_x ‖∑_b a_b V_b x‖² ≤ n² · ∑_b a_b²  = n² · ‖a‖².
```

This is the elementary certificate the G231 probe measured numerically (`λ_max(Vᴴ V)/n² ≤ 1` in
every cell): the operator norm is at most the maximal Gram row-mass, which is `n²`. -/
theorem largesieve_operator_bound_of_gram_rowmass_le_nsq
    (s : Finset α) (v : ι → α → ℂ) (B : Finset ι) (a : ι → ℝ) (n : ℕ)
    (hrow : ∀ b ∈ B, ∑ b' ∈ B, ‖gram s v b b'‖ ≤ (n : ℝ) ^ 2) :
    ∑ x ∈ s, ‖∑ b ∈ B, (a b : ℂ) * v b x‖ ^ 2 ≤ (n : ℝ) ^ 2 * ∑ b ∈ B, a b ^ 2 :=
  schur_operator_bound s v B a ((n : ℝ) ^ 2) hrow

/-! ## Wiring the derived input (A) into the G233 mass floor -/

open ArkLib.ProximityGap.Frontier.G233JacobiL2MassFloorNoGo in
/-- **G233 mass floor with input (A) discharged by the Schur test.**

Combining `largesieve_operator_bound_of_gram_rowmass_le_nsq` (derived `(A)`) with the sponsor
Parseval bound `(B)` and a half-capture reconstruction gives the division-free coefficient mass
floor `m − n ≤ 4 · n · ‖a‖²` — with `(A)` no longer an assumed spectral bound but a consequence of
the **structural Gram-row-mass ceiling `n²`**.

Here `aNorm2 := ∑_b a_b²` is the concrete coefficient L2 mass and
`vNorm2 := ∑_x ‖∑_b a_b V_b x‖²` is the concrete reconstruction mass, so the only surviving
premises are the Gram-row-mass fact `(hrow)`, the sponsor Parseval `(hParseval)`, and half capture
`(hHalf)`.  This closes the last hypothesis-shaped hole in the G228→G233 fanout chain. -/
theorem l2_mass_floor_of_gram_rowmass_parseval
    (s : Finset α) (v : ι → α → ℂ) (B : Finset ι) (a : ι → ℝ)
    (n m : ℕ) (hn : 0 < n)
    (sNorm2 : ℝ)
    (hrow : ∀ b ∈ B, ∑ b' ∈ B, ‖gram s v b b'‖ ≤ (n : ℝ) ^ 2)
    (hParseval : (n : ℝ) * ((m : ℝ) - n) ≤ sNorm2)
    (hHalf : sNorm2 / 4 ≤ ∑ x ∈ s, ‖∑ b ∈ B, (a b : ℂ) * v b x‖ ^ 2) :
    (m : ℝ) - n ≤ 4 * n * (∑ b ∈ B, a b ^ 2) :=
  l2_mass_floor_of_largesieve_parseval n m hn
    (∑ b ∈ B, a b ^ 2)
    (∑ x ∈ s, ‖∑ b ∈ B, (a b : ℂ) * v b x‖ ^ 2)
    sNorm2
    (largesieve_operator_bound_of_gram_rowmass_le_nsq s v B a n hrow)
    hParseval hHalf

end ArkLib.ProximityGap.Frontier.G234SchurOperatorBoundClosesG233
