/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Algebra.Order.Chebyshev
import ArkLib.ToMathlib.Combinatorics.Additive.HigherEnergy

/-!
# The Balog–Szemerédi–Gowers theorem

The **Balog–Szemerédi–Gowers (BSG)** theorem is the cornerstone structural input for the
Bourgain–Glibichuk–Konyagin (BGK) exponential-sum estimates: it converts a *statistical* hypothesis
(large additive energy) into a *structural* conclusion (a large subset with small doubling).

## Statement

Let `A` be a finite subset of an abelian group with **additive energy** `E[A] ≥ #A ^ 3 / K`. Then
there is a subset `A' ⊆ A` with

* `#A' ≥ #A / (C₁ * K)` (a constant fraction up to `K`), and
* `#(A' - A') ≤ C₂ * K ^ c * #A'` (small difference set).

The standard quantitative form (Gowers / Schoen) takes `C₁, C₂` absolute and `c = 4`. This file
records:

1. **The elementary reductions, fully proven, axiom-clean.** Working with the *sum-representation
   count* `r(c) = #{(a,b) ∈ A×A : a + b = c}`:
   * `addEnergy_eq_sum_rAdd_sq` — `E[A] = ∑_c r(c) ^ 2` (anchored on Mathlib's
     `addEnergy_eq_sum_sq'`).
   * `sum_rAdd_eq_card_sq` — `∑_c r(c) = #A ^ 2` (every ordered pair has one sum).
   * `popularSum_carries_half_energy` — the **popular-pair averaging lemma**: thresholding sums at
     `θ` with `2 * #A ^ 2 * θ ≤ E[A]`, the *unpopular* part carries at most half the energy, so the
     *popular* sums carry at least half: `E[A] ≤ 2 * ∑_{c popular} r(c) ^ 2`. Threshold pigeonhole.
   * `exists_popularSum_ge` — under `K * E[A] ≥ #A ^ 3`, some popular sum has `2 * K * r(c) ≥ #A`,
     witnessing the dense bipartite graph that the deep argument refines.

2. **The deep core as a named open hypothesis** `BSGCore` (a `def ... : Prop`, NOT a hidden
   `sorry`): the dependent-random-choice / bipartite path-counting argument extracting the refined
   subset.

3. **The conditional theorem** `balog_szemeredi_gowers (h : BSGCore ..)`.

## Status

`PARTIAL-PROVEN-PLUS-NAMED-CORE`.

## References

* A. Balog, E. Szemerédi, *A statistical theorem of set addition* (1994).
* W. T. Gowers, *A new proof of Szemerédi's theorem for AP4* (1998), §6.
* T. Tao, V. Vu, *Additive Combinatorics*, Cambridge (2006), Theorem 2.29.
-/

open Finset
open scoped BigOperators Pointwise Combinatorics.Additive

namespace Finset

variable {α : Type*} [AddCommGroup α] [DecidableEq α]

/-- The **sum-representation count** of `c` in `A`: the number of ordered pairs `(a, b) ∈ A × A` with
`a + b = c`. This is the degree count of the popular-pair bipartite graph underlying BSG. -/
noncomputable def rAdd (A : Finset α) (c : α) : ℕ :=
  #{p ∈ A ×ˢ A | p.1 + p.2 = c}

lemma rAdd_def (A : Finset α) (c : α) :
    rAdd A c = #{p ∈ A ×ˢ A | p.1 + p.2 = c} := rfl

/-- Representation counts vanish off the sumset `A + A`. -/
lemma rAdd_eq_zero_of_not_mem {A : Finset α} {c : α} (hc : c ∉ A + A) : rAdd A c = 0 := by
  classical
  rw [rAdd, card_eq_zero, filter_eq_empty_iff]
  rintro ⟨a, b⟩ hp h
  rw [mem_product] at hp
  exact hc (h ▸ add_mem_add hp.1 hp.2)

/-- The total representation count over the sumset is `#A ^ 2`: every ordered pair has one sum. -/
lemma sum_rAdd_eq_card_sq (A : Finset α) :
    ∑ c ∈ A + A, rAdd A c = #A ^ 2 := by
  classical
  simp_rw [rAdd]
  rw [sq, ← card_product A A]
  refine (Finset.card_eq_sum_card_fiberwise (f := fun p : α × α => p.1 + p.2)
    (s := A ×ˢ A) (t := A + A) ?_).symm
  rintro ⟨a, b⟩ hp
  have hp' := Finset.mem_product.1 hp
  exact add_mem_add hp'.1 hp'.2

/-- **Energy as the sum of squared representation counts.** `E[A] = ∑_{c ∈ A+A} r(c) ^ 2`. This is
exactly Mathlib's `addEnergy_eq_sum_sq'` specialised to `s = t = A`, unfolded through `rAdd`. -/
lemma addEnergy_eq_sum_rAdd_sq (A : Finset α) :
    E[A] = ∑ c ∈ A + A, rAdd A c ^ 2 :=
  addEnergy_eq_sum_sq' A A

/-- **Popular-pair averaging lemma (threshold pigeonhole).** Split the sumset at threshold `θ`:
let `P = {c ∈ A+A | θ ≤ r(c)}` be the *popular* sums. If `2 * #A ^ 2 * θ ≤ E[A]`, then the popular
sums carry at least half the energy: `E[A] ≤ 2 * ∑_{c ∈ P} r(c) ^ 2`.

Proof: on the *unpopular* part `r(c) < θ`, so `r(c) ^ 2 ≤ θ * r(c)`, whence the unpopular energy is
at most `θ * ∑ r(c) = θ * #A ^ 2 ≤ E[A] / 2`; the popular part carries the remainder. -/
lemma popularSum_carries_half_energy (A : Finset α) (θ : ℕ)
    (hθ : 2 * #A ^ 2 * θ ≤ E[A]) :
    E[A] ≤ 2 * ∑ c ∈ {c ∈ A + A | θ ≤ rAdd A c}, rAdd A c ^ 2 := by
  classical
  set P : Finset α := {c ∈ A + A | θ ≤ rAdd A c} with hP
  set Q : Finset α := {c ∈ A + A | ¬ θ ≤ rAdd A c} with hQ
  have hsplit : ∑ c ∈ A + A, rAdd A c ^ 2
      = (∑ c ∈ P, rAdd A c ^ 2) + ∑ c ∈ Q, rAdd A c ^ 2 := by
    rw [hP, hQ, ← Finset.sum_filter_add_sum_filter_not (A + A) (fun c => θ ≤ rAdd A c)]
  -- Bound the unpopular energy by `θ * #A ^ 2`.
  have hQ_bound : (∑ c ∈ Q, rAdd A c ^ 2) ≤ θ * #A ^ 2 := by
    have hsub : Q ⊆ A + A := by rw [hQ]; exact Finset.filter_subset _ _
    calc ∑ c ∈ Q, rAdd A c ^ 2
        ≤ ∑ c ∈ Q, θ * rAdd A c := by
          refine Finset.sum_le_sum (fun c hc => ?_)
          rw [hQ, mem_filter, not_le] at hc
          rw [sq]
          exact Nat.mul_le_mul_right _ (le_of_lt hc.2)
      _ = θ * ∑ c ∈ Q, rAdd A c := by rw [Finset.mul_sum]
      _ ≤ θ * ∑ c ∈ A + A, rAdd A c := by
          apply Nat.mul_le_mul_left
          exact Finset.sum_le_sum_of_subset hsub
      _ = θ * #A ^ 2 := by rw [sum_rAdd_eq_card_sq]
  -- Combine.
  have hE : E[A] = (∑ c ∈ P, rAdd A c ^ 2) + ∑ c ∈ Q, rAdd A c ^ 2 := by
    rw [addEnergy_eq_sum_rAdd_sq, hsplit]
  have : E[A] ≤ (∑ c ∈ P, rAdd A c ^ 2) + θ * #A ^ 2 := by
    rw [hE]; exact Nat.add_le_add_left hQ_bound _
  -- `θ * #A ^ 2 ≤ E[A] / 2`, so `E[A] ≤ ∑_P + E[A]/2`, giving `E[A]/2 ≤ ∑_P`.
  have hhalf : 2 * (θ * #A ^ 2) ≤ E[A] := by
    have : 2 * #A ^ 2 * θ = 2 * (θ * #A ^ 2) := by ring
    omega
  omega

/-- **A popular sum of large degree exists.** If `K * E[A] ≥ #A ^ 3` and `A` is nonempty, then there
is a sum `c ∈ A + A` whose representation count satisfies `2 * K * rAdd A c ≥ #A`. This `c` (more
precisely the bipartite graph of representations of the popular sums) is the object the deep BSG
core refines into the small-doubling subset. -/
lemma exists_popularSum_ge (A : Finset α) (K : ℕ) (hK : 0 < K) (hA : A.Nonempty)
    (hE : #A ^ 3 ≤ K * E[A]) :
    ∃ c ∈ A + A, #A ≤ 2 * K * rAdd A c := by
  classical
  -- Take the threshold `θ` with `2 * K * θ = #A` (rounding); use the averaging lemma with this θ.
  -- We argue by contradiction: if every popular degree were `< #A / (2K)`, the energy would be too
  -- small. Concretely, set `θ := ⌈#A / (2K)⌉` is awkward over ℕ; instead use the direct max bound.
  by_contra hcon
  push_neg at hcon
  -- Then for every `c ∈ A+A`, `2 * K * rAdd A c < #A`, i.e. `rAdd A c < #A` and small.
  -- Energy `= ∑ r(c)^2 ≤ (max r) * ∑ r(c) = (max r) * #A^2`. With `2K * (max r) < #A`:
  -- `2K * E[A] = 2K * ∑ r(c)^2 ≤ ∑ r(c) * (2K * r(c)) < ∑ r(c) * #A = #A^3`. Contradiction.
  have hbound : 2 * K * E[A] < #A ^ 3 := by
    have hstep : 2 * K * ∑ c ∈ A + A, rAdd A c ^ 2
        ≤ ∑ c ∈ A + A, rAdd A c * (2 * K * rAdd A c) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum (fun c _ => ?_)
      rw [sq]; exact le_of_eq (by ring)
    have hstrict : ∑ c ∈ A + A, rAdd A c * (2 * K * rAdd A c)
        < #A ^ 3 := by
      have hAA : (A + A).Nonempty := hA.add hA
      have hkey : ∀ c ∈ A + A, rAdd A c * (2 * K * rAdd A c) ≤ rAdd A c * (#A - 1) := by
        intro c hc
        rcases Nat.eq_zero_or_pos (rAdd A c) with h0 | hpos
        · simp [h0]
        · exact Nat.mul_le_mul_left _ (by have := hcon c hc; omega)
      calc ∑ c ∈ A + A, rAdd A c * (2 * K * rAdd A c)
          ≤ ∑ c ∈ A + A, rAdd A c * (#A - 1) :=
            Finset.sum_le_sum hkey
        _ = (∑ c ∈ A + A, rAdd A c) * (#A - 1) := by rw [← Finset.sum_mul]
        _ = #A ^ 2 * (#A - 1) := by rw [sum_rAdd_eq_card_sq]
        _ < #A ^ 3 := by
            have hcard : 0 < #A := hA.card_pos
            have hsq : 0 < #A ^ 2 := by positivity
            have hlt : #A ^ 2 * (#A - 1) < #A ^ 2 * #A :=
              (Nat.mul_lt_mul_left hsq).mpr (by omega)
            calc #A ^ 2 * (#A - 1) < #A ^ 2 * #A := hlt
              _ = #A ^ 3 := by ring
    calc 2 * K * E[A] = 2 * K * ∑ c ∈ A + A, rAdd A c ^ 2 := by
          rw [addEnergy_eq_sum_rAdd_sq]
      _ ≤ ∑ c ∈ A + A, rAdd A c * (2 * K * rAdd A c) := hstep
      _ < #A ^ 3 := hstrict
  -- But `#A ^ 3 ≤ K * E[A] ≤ 2 * K * E[A]`, contradiction.
  have hmono : K * E[A] ≤ 2 * K * E[A] := by
    have h2 : 2 * K * E[A] = 2 * (K * E[A]) := by ring
    rw [h2]
    exact Nat.le_mul_of_pos_left _ (by norm_num)
  have hge : #A ^ 3 ≤ 2 * K * E[A] := le_trans hE hmono
  omega

/-! ## The deep core and the conditional theorem -/

/-- **The deep Balog–Szemerédi–Gowers core**, carried as a named open hypothesis (NOT a hidden
`sorry`). It packages the constant-tracking dependent-random-choice / bipartite path-counting
argument: from a finite set `A` with energy `E[A] ≥ #A ^ 3 / K` (here `#A ^ 3 ≤ K * E[A]`), one can
extract a subset `A' ⊆ A` that is a constant fraction of `A` (up to `K`) and has a controlled
difference set.

The constants `C₁, C₂` and the exponent `c` are bundled as explicit parameters so a downstream
discharge (or a future Mathlib `Graph`-based proof) may fix them; the canonical Gowers form uses
`c = 4`. -/
def BSGCore (C₁ C₂ c : ℕ) : Prop :=
  ∀ {α : Type} [inst : AddCommGroup α] [inst2 : DecidableEq α],
    ∀ (A : Finset α) (K : ℕ), 0 < K → A.Nonempty → #A ^ 3 ≤ K * E[A] →
      ∃ A' : Finset α, A' ⊆ A ∧ A'.Nonempty ∧
        C₁ * K * #A' ≥ #A ∧ #(A' - A') ≤ C₂ * K ^ c * #A'

/-- **Balog–Szemerédi–Gowers (conditional on the named core).** Given the deep core `BSGCore` and a
finite set `A` with additive energy `E[A] ≥ #A ^ 3 / K` (in the cleared form `#A ^ 3 ≤ K * E[A]`),
there is a subset `A' ⊆ A` of size at least `#A / (C₁ K)` whose difference set has size at most
`C₂ K ^ c #A'`. -/
theorem balog_szemeredi_gowers {C₁ C₂ c : ℕ} (hcore : BSGCore C₁ C₂ c)
    {α : Type} [AddCommGroup α] [DecidableEq α]
    (A : Finset α) (K : ℕ) (hK : 0 < K) (hA : A.Nonempty) (hE : #A ^ 3 ≤ K * E[A]) :
    ∃ A' : Finset α, A' ⊆ A ∧ A'.Nonempty ∧
      C₁ * K * #A' ≥ #A ∧ #(A' - A') ≤ C₂ * K ^ c * #A' :=
  hcore A K hK hA hE

end Finset

-- Axiom audit (expected: propext, Classical.choice, Quot.sound)
#print axioms Finset.sum_rAdd_eq_card_sq
#print axioms Finset.addEnergy_eq_sum_rAdd_sq
#print axioms Finset.popularSum_carries_half_energy
#print axioms Finset.exists_popularSum_ge
#print axioms Finset.balog_szemeredi_gowers
