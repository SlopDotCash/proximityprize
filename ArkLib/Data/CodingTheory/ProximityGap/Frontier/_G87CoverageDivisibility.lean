/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.RingTheory.Int.Basic
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G86HadamardSupportSix

/-!
# G87: coverage ⟹ determinant divisibility — the second G83 instantiation piece

G83 (`_G83DeterminantCoverageFence.lean`) assumed `coverage_dvd : p ^ s ∣ determinant` as a
certificate field, naming "proving that common prime-ideal coverage yields the divisibility"
as an open instantiation piece. This file discharges it in the concrete form the census
actually has.

**The concrete meaning of coverage.** A degree-one prime `𝔭 ⊂ ℤ[ζ_n]` of index `p` is the
kernel of evaluation `ζ_n ↦ t` at a root `t` of `Φ_n` mod `p`; a census relation
`w = (w_0, …, w_{d-1})` (coefficient vector of `Σ w_j ζ_n^j`) *lies in* `𝔭` iff
`Σ_j w_j t^j ≡ 0 (mod p)`. Common coverage of the whole census at `s` distinct degree-one
primes says: every row of the census matrix vanishes mod `p` at `s` roots, pairwise distinct
mod `p`.

**The elementary mechanism (no Smith normal form).** Extend the covered roots to `d` nodes
pairwise distinct mod `p` (always possible for `d ≤ p`; in the application `p ≈ n⁴ ≫ d`) and
let `A = (vandermonde t)ᵀ`, so column `k` of `A` is `(t_k^j)_j`. Column `k` of `M * A` is
`(Σ_j M i j · t_k^j)_i` — divisible by `p` for each covered node. Multilinearity of the
determinant in columns gives `p^{#covered} ∣ det M · det A`, and
`det A = ∏_{i<j} (t_j − t_i)` is a unit mod `p`, so primality cancels it.

* `pow_card_dvd_det_of_cols_dvd` — multilinearity brick: if every column of a square integer
  matrix indexed by `S` is divisible by `p`, then `p^{|S|} ∣ det`. (Generic; upstreaming
  candidate.)
* `pow_dvd_det_of_annihilator` — cancellation: `p` prime, columns of `M * A` in `S` divisible
  by `p`, `p ∤ det A` ⟹ `p^{|S|} ∣ det M`.
* `pow_dvd_det_of_vanishing_at_roots` — **HEADLINE**: `p` prime, nodes `t : Fin d → ℤ`
  pairwise distinct mod `p`, every row of `M` vanishing mod `p` at the nodes in `S` ⟹
  `p^{|S|} ∣ det M`. The hypothesis is exactly common coverage of the census at `|S|`
  distinct degree-one primes.
* `censusFence_of_vanishing_rows` — **the end-to-end fence** (composing with G86 + G83): a
  support-six integer census matrix with nonzero determinant whose rows all vanish mod `p` at
  `s` pairwise-distinct roots satisfies `s·log p ≤ (d/2)·log 6`. Contrapositive: above the
  half-height threshold, no full-rank support-six census matrix with that much common
  coverage exists — the G82 fence with ALL arithmetic now theorem-level, consuming raw census
  data.

**Honest scope.** With G86 this closes the second of G83's three open instantiation pieces
(Hadamard bound; coverage divisibility). The remaining open content of the fence lane is now
exactly the *census-side* question: does the support-six census span contain a full-rank
`d × d` matrix whose common coverage exceeds the threshold (fires the G82 contradiction), or
is common coverage provably `o(n/log n)` (fences the CRT route)? The G82 addendum probe
measured coverage ≡ 1 at all accessible cells, supporting the fence. No bound on `M(μ_n)` is
claimed; CORE remains OPEN / ON-BGK. Issue #466/#505.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G87CoverageDivisibility

open Finset

variable {d : ℕ}

/-- Multilinearity brick: if every column of `N` indexed by `S` is divisible by `p`, then
`p^{|S|} ∣ det N`. Induction on `S`, factoring `p` out of one column at a time. -/
theorem pow_card_dvd_det_of_cols_dvd (p : ℤ) (N : Matrix (Fin d) (Fin d) ℤ)
    (S : Finset (Fin d)) (h : ∀ i : Fin d, ∀ k ∈ S, p ∣ N i k) :
    p ^ S.card ∣ N.det := by
  classical
  induction S using Finset.induction generalizing N with
  | empty => simp
  | insert k S hk ih =>
    -- factor `p` out of column `k`
    have hcol : ∀ i, p ∣ N i k := fun i => h i k (Finset.mem_insert_self k S)
    set v : Fin d → ℤ := fun i => (hcol i).choose with hv
    have hvspec : ∀ i, N i k = p * v i := fun i => (hcol i).choose_spec
    set N' : Matrix (Fin d) (Fin d) ℤ := N.updateCol k v with hN'
    have hupd : N'.updateCol k v = N' := by
      ext i j
      by_cases hj : j = k <;> simp [N', hj]
    have hNeq : N = N'.updateCol k (p • v) := by
      ext i j
      by_cases hj : j = k
      · subst hj
        simp [N', hvspec i]
      · simp [N', hj]
    have hdet : N.det = p * N'.det := by
      calc N.det = (N'.updateCol k (p • v)).det := by rw [← hNeq]
        _ = p * (N'.updateCol k v).det := Matrix.det_updateCol_smul N' k p v
        _ = p * N'.det := by rw [hupd]
    have hrest : ∀ i : Fin d, ∀ j ∈ S, p ∣ N' i j := by
      intro i j hj
      have hjk : j ≠ k := by rintro rfl; exact hk hj
      have hval : N' i j = N i j := by simp [N', hjk]
      rw [hval]
      exact h i j (Finset.mem_insert_of_mem hj)
    rw [Finset.card_insert_of_notMem hk, hdet, pow_succ, mul_comm (p ^ S.card) p]
    exact mul_dvd_mul_left p (ih N' hrest)

/-- Cancellation: if `p` is prime, the columns of `M * A` indexed by `S` are divisible by
`p`, and `p ∤ det A`, then `p^{|S|} ∣ det M`. -/
theorem pow_dvd_det_of_annihilator {p : ℕ} (hp : p.Prime)
    (M A : Matrix (Fin d) (Fin d) ℤ) (S : Finset (Fin d))
    (h : ∀ i : Fin d, ∀ k ∈ S, (p : ℤ) ∣ (M * A) i k)
    (hA : ¬ (p : ℤ) ∣ A.det) :
    (p : ℤ) ^ S.card ∣ M.det := by
  have hMA : (p : ℤ) ^ S.card ∣ M.det * A.det := by
    rw [← Matrix.det_mul]
    exact pow_card_dvd_det_of_cols_dvd (p : ℤ) (M * A) S h
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  exact hprime.pow_dvd_of_dvd_mul_right S.card hA hMA

/-- **Coverage ⟹ divisibility, Vandermonde form.** `p` prime, `t : Fin d → ℤ` pairwise
distinct mod `p`, and every row of `M` vanishing mod `p` at each node indexed by `S` — i.e.
`p ∣ Σ_j M i j * t k ^ j` for `k ∈ S` — imply `p^{|S|} ∣ det M`. Taking the `t k` to be roots
of `Φ_n` mod `p` (degree-one primes of `ℤ[ζ_n]` above `p`), the hypothesis is exactly common
coverage of the census at `|S|` distinct degree-one primes. -/
theorem pow_dvd_det_of_vanishing_at_roots {p : ℕ} (hp : p.Prime)
    (M : Matrix (Fin d) (Fin d) ℤ) (t : Fin d → ℤ) (S : Finset (Fin d))
    (hdist : ∀ k l : Fin d, k ≠ l → ¬ (p : ℤ) ∣ (t k - t l))
    (hvan : ∀ i : Fin d, ∀ k ∈ S, (p : ℤ) ∣ ∑ j : Fin d, M i j * t k ^ (j : ℕ)) :
    (p : ℤ) ^ S.card ∣ M.det := by
  classical
  haveI := Fact.mk hp
  haveI : Fact (1 < p) := ⟨hp.one_lt⟩
  set A : Matrix (Fin d) (Fin d) ℤ := (Matrix.vandermonde t).transpose with hA
  have hcols : ∀ i : Fin d, ∀ k ∈ S, (p : ℤ) ∣ (M * A) i k := by
    intro i k hk
    have hentry : (M * A) i k = ∑ j : Fin d, M i j * t k ^ (j : ℕ) := by
      simp [A, Matrix.mul_apply, Matrix.transpose_apply, Matrix.vandermonde]
    rw [hentry]
    exact hvan i k hk
  have hdetA : ¬ (p : ℤ) ∣ A.det := by
    have hvdm : A.det = ∏ i : Fin d, ∏ j ∈ Finset.Ioi i, (t j - t i) := by
      rw [hA, Matrix.det_transpose, Matrix.det_vandermonde]
    rw [hvdm, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hcast : ((∏ i : Fin d, ∏ j ∈ Finset.Ioi i, (t j - t i) : ℤ) : ZMod p)
        = ∏ i : Fin d, ∏ j ∈ Finset.Ioi i, ((t j : ZMod p) - (t i : ZMod p)) := by
      push_cast
      rfl
    rw [hcast]
    refine Finset.prod_ne_zero_iff.mpr (fun i _ => ?_)
    refine Finset.prod_ne_zero_iff.mpr (fun j hj => ?_)
    have hne : j ≠ i := (Finset.mem_Ioi.mp hj).ne'
    have hd := hdist j i hne
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hd
    intro hzero
    apply hd
    push_cast
    exact hzero
  exact pow_dvd_det_of_annihilator hp M A S hcols hdetA

/-- **The end-to-end fence** (G87 + G86 + G83): a support-six integer census matrix with
nonzero determinant whose rows all vanish mod `p` at `s` pairwise-distinct roots satisfies
the half-height fence `s·log p ≤ (d/2)·log 6`. Contrapositive: common coverage strictly above
`(d/2)·log 6 / log p` distinct degree-one primes forces every such census matrix to be
singular. -/
theorem censusFence_of_vanishing_rows {p : ℕ} (hp : p.Prime)
    (M : Matrix (Fin d) (Fin d) ℤ) (t : Fin d → ℤ) (S : Finset (Fin d))
    (hdist : ∀ k l : Fin d, k ≠ l → ¬ (p : ℤ) ∣ (t k - t l))
    (hvan : ∀ i : Fin d, ∀ k ∈ S, (p : ℤ) ∣ ∑ j : Fin d, M i j * t k ^ (j : ℕ))
    (hne : M.det ≠ 0)
    (hrows : ∀ i, (∑ j, M i j ^ 2) ≤ (6 : ℤ)) :
    (S.card : ℝ) * Real.log p ≤ (d : ℝ) / 2 * Real.log 6 :=
  G83DeterminantCoverageFence.coverage_log_le_half_height hp.two_le
    (G86HadamardSupportSix.supportSixDeterminantCertificate_of_rows p S.card M hne
      (pow_dvd_det_of_vanishing_at_roots hp M t S hdist hvan) hrows)

end ArkLib.ProximityGap.Frontier.G87CoverageDivisibility

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.G87CoverageDivisibility.pow_card_dvd_det_of_cols_dvd
#print axioms ArkLib.ProximityGap.Frontier.G87CoverageDivisibility.pow_dvd_det_of_annihilator
#print axioms
  ArkLib.ProximityGap.Frontier.G87CoverageDivisibility.pow_dvd_det_of_vanishing_at_roots
#print axioms ArkLib.ProximityGap.Frontier.G87CoverageDivisibility.censusFence_of_vanishing_rows
