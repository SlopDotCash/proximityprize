/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonancePhaseSumConvolutionRecursion

/-!
# Diagonal extraction of the L² convolution recursion of the resonance moment (#407 / #444)

Builds on the EXACT one-step convolution recursion
`phaseSum u (r+1) c = ∑_{a≠0} u(a)·phaseSum u r (c−a)`
(`_ResonancePhaseSumConvolutionRecursion`). The aggregate L² recursion file
`_ResonanceMomentConvolutionRecursion` proves the UPPER bound
`T (r+1) ≤ (m−1)² · T r` (one Cauchy–Schwarz on the `(m−1)`-term convolution).

What was MISSING (grep-confirmed: no diagonal split of the *convolution* recursion anywhere — the
`_ResonanceDiagonalExtraction` file splits the *Wick agreement* `∑X=∑Y` double sum, a DIFFERENT
object) is the EXACT one-step convolution diagonal extraction:

> **`(T (r+1) : ℂ) = (m−1)·(T r : ℂ) + Off r`** for unit-modulus phases,

where the diagonal `(m−1)·T r` is the `a = b` part of the expansion of
`T(r+1) = ∑_c ‖∑_{a≠0} u(a)·P_r(c−a)‖²` (each `|u a|² = 1`, and `c ↦ c−a` is a bijection of
`ZMod m` so each diagonal term contributes `T r`), and the **convolution off-diagonal**
`Off r = ∑_c ∑_{a≠0} ∑_{b≠0, b≠a} u(a)·conj(u b)·P_r(c−a)·conj(P_r(c−b))`
is the `a ≠ b` cross-correlation remainder.

## Why this is the matching LOWER-bound content (the two-sided pin)

The upper bound `T(r+1) ≤ (m−1)²·T r` and this exact extraction together bracket the recursion:
the diagonal term is EXACTLY `(m−1)·T r` (a clean factor `m−1`, not `(m−1)²`), so the gap factor
between the trivial upper bound and the diagonal floor is precisely one extra `(m−1)`. ALL of that
gap lives in the named convolution off-diagonal `Off r` — the `a≠b` phase cross-correlation. A
probe (`scripts/probes/probe_resonance_convdiag.py`, adversarial unit phases m=3..13, r=1..3,
30k trials) finds `Re(Off r) ≥ 0` robustly (worst observed `+0.125`), i.e. the diagonal `(m−1)·T r`
is an empirical LOWER bound matching the spectral Chebyshev-sum mechanism
`Off = (1/m)∑_b |K̂(b)|^{2r}·(|K̂(b)|²−(m−1)) ≥ 0`. We do NOT formalize `Off ≥ 0` (that routes
through the open Gauss-period spectral profile `K̂(b)`); we lock the EXACT identity, which is the
certain part, and NAME `Off` as the door-(iv) cancellation budget.

## Honest scope

A CERTAIN exact algebraic identity (a real-space double-sum reindexing), not a bound. The diagonal
factor is `m−1` (vs the `(m−1)²` trivial upper bound); the missing `(m−1)` cancellation budget is
the convolution off-diagonal `Off`, NAMED not bounded — it is the open Gauss-period/BGK content.
CORE `M(μ_n) ≤ C·√(n log m)` UNCHANGED / OPEN. No CORE / cancellation / completion / moment /
anti-concentration / capacity claim.

Axiom-clean (`propext, Classical.choice, Quot.sound`). Issues #407, #444.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open scoped BigOperators Classical
open Finset

variable {m : ℕ} [NeZero m]

/-- The nonzero-residue filter has cardinality `m − 1`. -/
private theorem card_nz_filter_cd :
    (Finset.univ.filter (fun a : ZMod m => a ≠ 0)).card = m - 1 := by
  classical
  rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ 0),
    Finset.card_univ, ZMod.card]

/-- **The convolution off-diagonal remainder `convOffDiag u r`.** The `a ≠ b` cross-correlation part
of the expansion of `‖phaseSum u (r+1) c‖²` via the convolution recursion, summed over all
frequencies `c`. This is the named door-(iv) cancellation budget: the entire gap between the
diagonal floor `(m−1)·T r` and the trivial ceiling `(m−1)²·T r` lives here, and it is the open
Gauss-period phase cross-correlation (NOT bounded). -/
noncomputable def convOffDiag (u : ZMod m → ℂ) (r : ℕ) : ℂ :=
  ∑ c : ZMod m,
    ∑ a ∈ Finset.univ.filter (fun a : ZMod m => a ≠ 0),
      ∑ b ∈ (Finset.univ.filter (fun b : ZMod m => b ≠ 0)).erase a,
        u a * (starRingEnd ℂ) (u b)
          * (phaseSum u r (c - a) * (starRingEnd ℂ) (phaseSum u r (c - b)))

/-- **Per-frequency expansion of `‖phaseSum u (r+1) c‖²` into a convolution double sum.**
`((‖P_{r+1} c‖² : ℝ) : ℂ) = ∑_{a≠0} ∑_{b≠0} u(a)·conj(u b)·P_r(c−a)·conj(P_r(c−b))`. The squared
norm of the convolution sum expands to the conjugated double sum over the `(m−1)`-term support. -/
theorem normSq_phaseSum_succ_eq_double (u : ZMod m → ℂ) (r : ℕ) (c : ZMod m) :
    ((‖phaseSum u (r + 1) c‖ ^ 2 : ℝ) : ℂ)
      = ∑ a ∈ Finset.univ.filter (fun a : ZMod m => a ≠ 0),
          ∑ b ∈ Finset.univ.filter (fun b : ZMod m => b ≠ 0),
            u a * (starRingEnd ℂ) (u b)
              * (phaseSum u r (c - a) * (starRingEnd ℂ) (phaseSum u r (c - b))) := by
  classical
  rw [phaseSum_succ]
  -- ((‖∑_{a∈s} u a P_r(c-a)‖² : ℝ) : ℂ) = conj(∑) * (∑) = (∑_b conj(u b P_r)) (∑_a u a P_r)
  rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self, map_sum]
  rw [Finset.sum_mul_sum]
  -- now: ∑_b ∑_a conj(u b P_r(c-b)) * (u a P_r(c-a)); reorder to ∑_a ∑_b and regroup
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [map_mul]
  ring

/-- **Diagonal (`a = b`) value of the convolution expansion is `(m−1)·(T r : ℂ)`** (unit phases).
Restricting the double sum to `a = b`, each summand is `|u a|²·|P_r(c−a)|² = |P_r(c−a)|²`; summing
over `c` (with the bijection `c ↦ c−a`) gives `T r`, and there are `m−1` choices of `a`. -/
theorem convDiag_eq (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1) (r : ℕ) :
    (∑ c : ZMod m,
        ∑ a ∈ Finset.univ.filter (fun a : ZMod m => a ≠ 0),
          u a * (starRingEnd ℂ) (u a)
            * (phaseSum u r (c - a) * (starRingEnd ℂ) (phaseSum u r (c - a))))
      = (((m : ℕ) - 1 : ℕ) : ℂ) * (resonanceMoment u r : ℂ) := by
  classical
  set s := Finset.univ.filter (fun a : ZMod m => a ≠ 0) with hs
  -- each summand: u a * conj(u a) * (P_r(c-a) * conj(P_r(c-a))) = (‖P_r(c-a)‖² : ℝ) : ℂ
  have hterm : ∀ (c : ZMod m), ∀ a ∈ s,
      u a * (starRingEnd ℂ) (u a)
        * (phaseSum u r (c - a) * (starRingEnd ℂ) (phaseSum u r (c - a)))
        = ((‖phaseSum u r (c - a)‖ ^ 2 : ℝ) : ℂ) := by
    intro c a _
    have hua : u a * (starRingEnd ℂ) (u a) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]; norm_num
    have hP : phaseSum u r (c - a) * (starRingEnd ℂ) (phaseSum u r (c - a))
        = ((‖phaseSum u r (c - a)‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hua, one_mul, hP]
  -- rewrite all summands, then swap c/a and use the shift bijection
  have hstep : (∑ c : ZMod m,
        ∑ a ∈ s, u a * (starRingEnd ℂ) (u a)
            * (phaseSum u r (c - a) * (starRingEnd ℂ) (phaseSum u r (c - a))))
      = ∑ c : ZMod m, ∑ a ∈ s, ((‖phaseSum u r (c - a)‖ ^ 2 : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    exact Finset.sum_congr rfl (hterm c)
  rw [hstep, Finset.sum_comm]
  -- ∑_a ∑_c (‖P_r(c-a)‖²) = ∑_a (T r) (shift bijection) = (m-1)·T r
  have hshift : ∀ a ∈ s, (∑ c : ZMod m, ((‖phaseSum u r (c - a)‖ ^ 2 : ℝ) : ℂ))
      = (resonanceMoment u r : ℂ) := by
    intro a _
    rw [resonanceMoment, Complex.ofReal_sum]
    exact Fintype.sum_equiv (Equiv.subRight a) _ _ (fun c => rfl)
  rw [Finset.sum_congr rfl hshift, Finset.sum_const, hs, card_nz_filter_cd, nsmul_eq_mul]

/-- **Diagonal extraction of the L² convolution recursion (the matching-lower-bound capstone).**
`(T (r+1) : ℂ) = (m−1)·(T r : ℂ) + convOffDiag u r` for unit-modulus phases. The depth-`(r+1)`
resonance moment splits EXACTLY into the convolution diagonal `(m−1)·T r` (the `a = b` part, a
clean factor `m−1`) plus the named off-diagonal `convOffDiag` (the `a ≠ b` phase cross-correlation,
the open door-(iv) cancellation budget). With the trivial ceiling `T(r+1) ≤ (m−1)²·T r` this pins
the recursion two-sidedly: `(m−1)·T r ≤ T(r+1)` would follow iff `Re(convOffDiag) ≥ 0` (probe-true,
spectral Chebyshev-sum mechanism, NOT formalized — open Gauss-period content). -/
theorem resonanceMoment_succ_eq_diag_add_offdiag
    (u : ZMod m → ℂ) (hu : ∀ l : ZMod m, ‖u l‖ = 1) (r : ℕ) :
    (resonanceMoment u (r + 1) : ℂ)
      = (((m : ℕ) - 1 : ℕ) : ℂ) * (resonanceMoment u r : ℂ) + convOffDiag u r := by
  classical
  set s := Finset.univ.filter (fun a : ZMod m => a ≠ 0) with hs
  -- T(r+1) as the cast sum of per-frequency squared norms, each expanded to the double sum
  have hTexp : (resonanceMoment u (r + 1) : ℂ)
      = ∑ c : ZMod m, ∑ a ∈ s, ∑ b ∈ s,
          u a * (starRingEnd ℂ) (u b)
            * (phaseSum u r (c - a) * (starRingEnd ℂ) (phaseSum u r (c - b))) := by
    rw [resonanceMoment, Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun c _ => normSq_phaseSum_succ_eq_double u r c)
  rw [hTexp]
  -- split each inner b-sum over s into the b = a diagonal + the b ∈ s.erase a off-diagonal
  have hsplit : ∀ (c : ZMod m), ∀ a ∈ s,
      (∑ b ∈ s, u a * (starRingEnd ℂ) (u b)
          * (phaseSum u r (c - a) * (starRingEnd ℂ) (phaseSum u r (c - b))))
        = (u a * (starRingEnd ℂ) (u a)
            * (phaseSum u r (c - a) * (starRingEnd ℂ) (phaseSum u r (c - a))))
          + ∑ b ∈ s.erase a, u a * (starRingEnd ℂ) (u b)
              * (phaseSum u r (c - a) * (starRingEnd ℂ) (phaseSum u r (c - b))) := by
    intro c a ha
    rw [← Finset.add_sum_erase s _ ha]
  rw [Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (hsplit c))]
  -- distribute the (diagonal + offdiag) sum: ∑_c ∑_a (D + O) = (∑_c ∑_a D) + (∑_c ∑_a O)
  simp_rw [Finset.sum_add_distrib]
  congr 1
  exact convDiag_eq u hu r

end ArkLib.ProximityGap.GaussPhaseResonance

-- Axiom audit: must be `{propext, Classical.choice, Quot.sound}` only.
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.normSq_phaseSum_succ_eq_double
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.convDiag_eq
#print axioms ArkLib.ProximityGap.GaussPhaseResonance.resonanceMoment_succ_eq_diag_add_offdiag
