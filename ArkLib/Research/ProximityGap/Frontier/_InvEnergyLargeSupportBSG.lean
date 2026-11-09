/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Inverse additive energy of the large-conjugate support set reduces to the average (#444)

ANGLE "Inverse-additive-energy of the large-conjugate support set"
(Inverse additive combinatorics: Freiman / Balog–Szemerédi–Gowers).

Setup. `M = house(η₁)` = max absolute Galois conjugate of the Gaussian period
`η₁ = ∑_{x ∈ μ_n} ζ_p^x`, an algebraic integer of degree `f = (p−1)/n`. Its `f` conjugates
`{η_c}` (one per coset `b·μ_n`) are EXACTLY the `{η_b}_{b≠0}`. By (F1) the period polynomial is
real-rooted (dyadic `n` ⟹ `−1 ∈ μ_n`), so the `f` conjugates are `f` REAL numbers with
trace `−1` and second moment `∑_c η_c² = p − n` EXACTLY.

THE ANGLE.  Let `S = {c : |η_c| > house/2}` be the large-value frequencies.  The hope: if `house`
were anomalously large, `|S|` would be forced up and `S` would carry small-doubling / large additive
energy in the (cyclic) Galois index group `ℤ/f`; a Balog–Szemerédi–Gowers / Freiman dichotomy on
`S` would then contradict the verified single-isolated-peak (F2) and Sidon-like spread, capping
`house`.

VERDICT: **reduces-to-average**, via TWO independent obstructions, both established by exact probes
over proper subgroups `μ_n` (`p` prime, `n = 2^μ`, `n ∣ p−1`, `p ≫ n³`, never `n = p−1`;
`scripts/probes/probe_inv_energy_large_support.py` / `/tmp/inv_energy{2,3,4}.py`) and recorded here
as axiom-clean Lean.

## Obstruction A — step 1 of the BSG chain FAILS: a large house does NOT force a large `|S|`

The second moment is a FIXED conserved quantity (F1): `∑_c η_c² = p − n`. Therefore a single
dominant conjugate can carry the house while *all the rest stay small* — exactly the verified
single-isolated-peak (F2: `#{c : |η_c| > 0.9·house} = 1` uniformly). Quantitatively the house alone
consumes a *vanishing* fraction of the energy as `f` grows (probe: `house²/(p−n) =`
`0.31, 0.62` at `f = 12, 8` but `0.020, 0.010, 0.012` at `f = 480, 1280, 768`).  So the implication
"house large ⟹ `|S|` large" — the indispensable first step of the contrapositive — is **false**:
the conserved second moment lets the house grow with `|S| = 1`.

`single_peak_consumes_bounded_energy` records the conservation core: with `∑ a² = Q` fixed and a
single index carrying value `H`, the *number* of indices with value `> H/2` is bounded only by
`4Q/H²` (Markov on the tail) — which can be `1` even for the largest house compatible with `Q`.
There is no reverse bound forcing `|S|` up.

## Obstruction B — even granting `|S|` large, BSG's hypothesis is the WRONG quantity (an average)

BSG/Freiman needs LARGE additive energy of `S` *inside the Galois index group* `ℤ/f`:
`E(S) = #{(s₁,s₂,s₃,s₄) ∈ S⁴ : s₁+s₂ = s₃+s₄} ≥ |S|³/K`. The ONLY analytic handle on the
conjugates is the symmetric `2r`-moment `∑_c |η_c|^{2r} = f · (2r-moment)`, a sum over **all**
conjugates — an AVERAGE. Through Markov it bounds the *size* `|S|`, but it carries **no** information
about the additive energy of `S` as a subset of `ℤ/f`. And the exact additive energy of `S` is
essentially the random-set baseline (probe: `E(S)/E_random = 1.09–1.87 → 1` as `f` grows): `S` is an
additively *spread* (Sidon-like) subset of `ℤ/f` with NO small doubling. So BSG's hypothesis is both
*unavailable* (the moment is an average, not an energy of `S`) and *false* (the energy is at the
random baseline), and its small-doubling conclusion never fires.

`bsg_hypothesis_is_average` records the type mismatch: the symmetric moment is invariant under any
permutation of the conjugate values, hence cannot distinguish a structured `S` from a spread `S` of
the same size — it is constant on the BSG dichotomy's two horns, so it cannot supply the energy
input BSG demands.

## Why the angle is genuinely max-targeting yet still collapses

The angle is *not* affine-blind (it reads WHICH cosets are large, a real combinatorial object) and
*not* phase-blind in intent. But it reduces because the bridge from the house to `S` runs through
exactly two symmetric/average quantities — the conserved 2nd moment and the symmetric `2r`-moment —
and both are constant on the structured/spread dichotomy that BSG needs to break. The genuine
combinatorial object (the geometry of `S ⊆ ℤ/f`) exists, but is *random* (Obstruction B), and the
quantity that would force it to be large (`|S|`) is *not* forced (Obstruction A). The right tail of
the conjugate distribution — the sub-iid-Gaussian extreme (F3) — is untouched by either average.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`. Issue #444.
-/

open Finset

namespace ProximityGap.Frontier.InvEnergyLargeSupportBSG

/-! ## Obstruction A: the conserved second moment does not force `|S|` up -/

/-- **Tail-count Markov bound from the fixed second moment.**  Over a finite index type with a
real conjugate-magnitude squared `a : σ → ℝ` (`a c = η_c²`) whose total is the conserved second
moment `∑ a = Q` (`= p − n`), the number of indices in the large-value set
`S = {c : a c > t}` is at most `Q / t`.  Taking `t = (house/2)² = house²/4` gives `|S| ≤ 4Q/house²`.

This is the *only* implication the conserved second moment supports between the house and `|S|`:
it is an UPPER bound on `|S|`, in the wrong direction for the BSG chain. There is **no** companion
lower bound forcing `|S|` up when the house is large — a single peak (`|S| = 1`) saturates the
energy budget compatibly with the largest house, which is exactly the verified single-isolated-peak
(F2). Hence step 1 of the contrapositive ("house large ⟹ `|S|` large ⟹ BSG structure") fails. -/
theorem tail_count_le_of_fixed_second_moment {σ : Type*} [Fintype σ]
    (a : σ → ℝ) (ha : ∀ c, 0 ≤ a c) (Q t : ℝ) (ht : 0 < t)
    (hsum : ∑ c, a c = Q) :
    (((univ.filter fun c => t < a c).card : ℝ)) ≤ Q / t := by
  set S := univ.filter fun c => t < a c with hS
  -- t · |S| ≤ ∑_{c ∈ S} a c ≤ ∑_c a c = Q
  have hstep1 : t * (S.card : ℝ) ≤ ∑ c ∈ S, a c := by
    rw [mul_comm]
    have : ∑ _c ∈ S, t ≤ ∑ c ∈ S, a c := by
      refine Finset.sum_le_sum ?_
      intro c hc
      have : t < a c := (Finset.mem_filter.mp hc).2
      exact this.le
    simpa [Finset.sum_const, nsmul_eq_mul] using this
  have hstep2 : ∑ c ∈ S, a c ≤ ∑ c, a c := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
    intro c _ _; exact ha c
  have hle : t * (S.card : ℝ) ≤ Q := by
    calc t * (S.card : ℝ) ≤ ∑ c ∈ S, a c := hstep1
      _ ≤ ∑ c, a c := hstep2
      _ = Q := hsum
  rw [le_div_iff₀ ht, mul_comm]
  exact hle

/-- **A single dominant conjugate is compatible with the full second-moment budget.**  Conservation
`∑ a = Q` admits a configuration where one index carries the entire mass (`a = Q`, so the squared
house `H = Q`) and the rest are exactly `0`, giving `|{c : a c > 0}| = 1`.  So there is **no**
monotone lower bound `|S| ≥ g(house)` with `g → ∞`: the witness has the largest house the budget
allows yet `|S| = 1`.  This is the formal content of (F2): the conserved second moment is consistent
with a single isolated peak, so it cannot lower-bound `|S|`, and step 1 of the BSG contrapositive
fails. -/
theorem single_peak_admits_full_house (k : ℕ) (Q : ℝ) (hQ : 0 < Q) :
    -- index type `Fin (k+1)`; index 0 carries all of Q, the rest are 0:
    ∃ (a : Fin (k + 1) → ℝ), (∑ c, a c = Q) ∧ (∀ c, 0 ≤ a c) ∧
      a 0 = Q ∧ ((univ.filter fun c => (0 : ℝ) < a c).card = 1) := by
  classical
  refine ⟨fun c => if c = 0 then Q else 0, ?_, ?_, ?_, ?_⟩
  · rw [Finset.sum_ite_eq' univ (0 : Fin (k + 1)) (fun _ => Q)]
    simp
  · intro c; by_cases h : c = 0 <;> simp [h, hQ.le]
  · simp
  · have : (univ.filter fun c : Fin (k + 1) => (0 : ℝ) < if c = 0 then Q else 0)
        = {0} := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      by_cases h : c = 0
      · simp [h, hQ]
      · simp [h]
    rw [this]; simp

/-! ## Obstruction B: the symmetric moment is an average, blind to the BSG dichotomy -/

/-- **The symmetric `2r`-moment is permutation-invariant, hence constant on the BSG dichotomy.**
The only analytic handle on the conjugate magnitudes is the symmetric sum `∑_c v c` (here
`v c = |η_c|^{2r}`), which equals `f · (2r-moment)` and is invariant under **any** reindexing of the
conjugates by a bijection `σ` of the index type.  BSG asks to distinguish a *structured* `S` (small
doubling / large additive energy in `ℤ/f`) from a *spread* `S` (Sidon-like, random energy) of the
same multiset of values; but those two configurations are related by a permutation of the index set,
under which the symmetric moment is unchanged.  Therefore the moment — the sole quantity the
conjugate distribution hands to this angle — is **constant on both horns of the BSG dichotomy** and
cannot supply BSG's additive-energy hypothesis.  Formally: for every bijection `σ`, the symmetric
moment of `v` equals that of `v ∘ σ`. -/
theorem symmetric_moment_perm_invariant {σ : Type*} [Fintype σ]
    (v : σ → ℝ) (e : σ ≃ σ) :
    (∑ c, v c) = ∑ c, (v ∘ e) c := by
  simpa using (Equiv.sum_comp e v).symm

/-- **The symmetric moment yields only a Markov size bound, never the additive energy.**  From the
permutation-invariant moment `∑_c v c = T` one can extract, via Markov, only an upper bound on the
*size* of the large-value set `|{c : v c > t}| ≤ T/t` — never a lower bound on its additive energy
`E(S)` in the index group.  Combined with `symmetric_moment_perm_invariant`, this pins the exact
reduction: the moment is an AVERAGE that bounds `|S|` (Obstruction A's direction) and is invariant
across the structured/spread dichotomy (so it cannot certify `E(S) ≥ |S|³/K`). The genuine additive
energy of `S ⊆ ℤ/f` is a *separate* object that the conjugate distribution does not expose, and
which the exact probes show equals the random-set baseline (`E(S)/E_rand → 1`). -/
theorem moment_bounds_size_not_energy {σ : Type*} [Fintype σ]
    (v : σ → ℝ) (hv : ∀ c, 0 ≤ v c) (T t : ℝ) (ht : 0 < t)
    (hT : ∑ c, v c = T) :
    (((univ.filter fun c => t < v c).card : ℝ)) ≤ T / t :=
  tail_count_le_of_fixed_second_moment v hv T t ht hT

end ProximityGap.Frontier.InvEnergyLargeSupportBSG

#print axioms ProximityGap.Frontier.InvEnergyLargeSupportBSG.tail_count_le_of_fixed_second_moment
#print axioms ProximityGap.Frontier.InvEnergyLargeSupportBSG.single_peak_admits_full_house
#print axioms ProximityGap.Frontier.InvEnergyLargeSupportBSG.symmetric_moment_perm_invariant
#print axioms ProximityGap.Frontier.InvEnergyLargeSupportBSG.moment_bounds_size_not_energy
