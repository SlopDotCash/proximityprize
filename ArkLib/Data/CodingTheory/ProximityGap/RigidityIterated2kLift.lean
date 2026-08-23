/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.PowerBasis
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic
import ArkLib.Data.CodingTheory.ProximityGap.RigidityGeneralT1
import ArkLib.Data.CodingTheory.ProximityGap.RigidityWindowHalving

/-!
# Round 29 (Issue #232) — THE ITERATED `2^k`-LIFT THEOREM, UNCONDITIONAL:
# full-window rigidity for disjoint families, with the independence hypothesis DISCHARGED

This file closes the two items the Round-26/27 ledger left open for the disjoint case of
Step 2 (O46/O50/O51): the **level-iteration statement** and the **discharge of the half-basis
independence hypothesis** (the queued "Lam–Leung at `p = 2`" cyclotomic brick of O47/O48).
Same-hour convergence note: `RigidityFullWindow.lean` (Round-28) proves the level iteration
with the per-level closure as an *oracle hypothesis* (its ledger entry names "hclosure
de-oracling" as the remaining assembly); this file's encoding bridge + cyclotomic discharge
supply exactly that closure unconditionally, so the iteration here carries **no oracles**.
`LamLeungTwoPow.lean` (O50) independently machine-checks the single-set `t = 1` theorem; the
single-set forms here (§7) recover it as the `B = ∅` instance of the disjoint-pair engine.

## The audit finding (machine-checked below)

The Round-23/24/25 rigidity bricks (`RigidityBaseCasePairs`, `RigidityTriplesSunflower`,
`RigidityGeneralT1`) all take the hypothesis

  `hindep : ∀ g : Fin N → F, (∑ j, g j * ζ ^ (j : ℕ)) = 0 → ∀ j, g j = 0`

with **`F`-valued** coefficients. For `N ≥ 2` this hypothesis is *unsatisfiable* — take
`g = (ζ, −1, 0, …)`: the sum telescopes to `ζ − ζ = 0` while `g 1 = −1 ≠ 0`
(`fValued_hindep_unsatisfiable`). So those theorems, as stated, are vacuously true and can
never be applied. Their *proofs* are sound: every application of `hindep` instantiates `g`
with integer-cast coefficients. This file states the satisfiable **`ℤ`-valued** form
(`HalfBasisIndepZ`), re-derives the Round-25 general `t = 1` theorem from it
(`disjoint_equal_sum_antipodal_int` — same proof skeleton, now non-vacuous), and then
**discharges** the `ℤ`-form for every primitive `2^m`-th root of unity in a characteristic-0
field (`halfBasisIndepZ_of_primitiveRoot`), via `Φ_{2^m} = minpoly ℚ ζ` of degree
`φ(2^m) = 2^{m−1}` and `linearIndependent_pow`. This is exactly the Lam–Leung-at-`p = 2`
content recorded in O47.

## The iteration (the remaining Step-2 assembly, disjoint case)

With the discharged base in hand, the Round-26 window-halving engine iterates:

* `antipodallyClosed_of_disjoint_equal_sum` — the encoding bridge from field-element finsets
  to the Round-25 signed-point world: disjoint `A, B ⊆ ±ζ^{<N}` with equal sums are
  antipodally closed (both of them), unconditionally.
* `isSignedPow_sq` / `IsPrimitiveRoot.pow` — the scale descent `μ_{2^m} → μ_{2^{m-1}}`:
  squares of signed half-basis points are signed half-basis points one level down, and `ζ^2`
  is primitive one level down.
* `closure_step` — the assembly step (the general `mul_i_closure`): if `A` is antipodally
  closed and `A²` is closed under multiplication by `ω²`, then `A` is closed under
  multiplication by `ω` (a shared square forces `y = ±ωx`; the antipode upgrades the sign).
* **`iterated_2k_lift`** — THE THEOREM (induction on `k`): if `A, B ⊆ μ_{2^m}` are disjoint
  with equal power sums `p_1, …, p_t` and `2^{k-1} ≤ t` (`1 ≤ k ≤ m`), then both `A` and `B`
  are closed under multiplication by **every** `2^k`-th root of unity — the `2^k`-lift
  (Round-22) structure. Floor = ceiling on the full window, disjoint case, **no undischarged
  hypotheses**: characteristic 0 and primitivity suffice.
* `coset_closure_of_equal_window` — display corollary: closure under the canonical generator
  `ζ^{2^{m-k}}` of `μ_{2^k}`, i.e. `A` and `B` are unions of `μ_{2^k}`-cosets.

Together with Round-27 (`RigiditySunflowerCore`, the reduction of non-disjoint families to
disjoint residuals) this completes the verified Step-2 chain of O46 end-to-end for the
disjoint case: core division (R27) → antipodal closure (this file, unconditional) → window
halving (R26) → iterated `2^k`-lift structure (this file). The remaining open composition is
the Conj-41/δ* wiring (O50 item (iii)), not the rigidity itself.
-/

open Finset Round25General Round26Recursion

namespace Round29IteratedLift

variable {F : Type*} [Field F]

/-! ## §0 The audit: the `F`-valued independence hypothesis is unsatisfiable -/

/-- **AUDIT (machine-checked).** The `F`-valued half-basis independence hypothesis consumed by
the Round-23/24/25 rigidity bricks is **unsatisfiable** for every `ζ` once `N ≥ 2`:
`g = (ζ, −1, 0, …)` gives `∑ g j · ζ^j = ζ·1 − 1·ζ = 0` with `g ≠ 0`. Hence those theorems
are vacuously true as stated; the satisfiable (and intended) form is `HalfBasisIndepZ`
below, under which the same proofs go through. -/
theorem fValued_hindep_unsatisfiable {N : ℕ} (hN : 2 ≤ N) (ζ : F) :
    ¬ (∀ g : Fin N → F, (∑ j : Fin N, g j * ζ ^ (j : ℕ)) = 0 → ∀ j, g j = 0) := by
  classical
  intro h
  have h0N : (0 : ℕ) < N := by omega
  have h1N : (1 : ℕ) < N := by omega
  have hne : (⟨0, h0N⟩ : Fin N) ≠ ⟨1, h1N⟩ := by simp [Fin.ext_iff]
  set g : Fin N → F :=
    fun j => if j = ⟨0, h0N⟩ then ζ else if j = ⟨1, h1N⟩ then -1 else 0 with hg
  have hzero : ∀ j ∈ Finset.univ,
      j ∉ ({⟨0, h0N⟩, ⟨1, h1N⟩} : Finset (Fin N)) → g j * ζ ^ (j : ℕ) = 0 := by
    intro j _ hj
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    simp [hg, hj.1, hj.2]
  have hsum : (∑ j : Fin N, g j * ζ ^ (j : ℕ)) = 0 := by
    rw [← Finset.sum_subset (Finset.subset_univ _) hzero, Finset.sum_pair hne]
    have hg0 : g ⟨0, h0N⟩ = ζ := by simp [hg]
    have hg1 : g ⟨1, h1N⟩ = -1 := by simp [hg, Ne.symm hne]
    rw [hg0, hg1]
    show ζ * ζ ^ (0 : ℕ) + -1 * ζ ^ (1 : ℕ) = 0
    ring
  have hcontra := h g hsum ⟨1, h1N⟩
  simp [hg, Ne.symm hne] at hcontra

/-! ## §1 The satisfiable `ℤ`-valued form and its cyclotomic discharge -/

/-- `ℤ`-valued half-basis independence: no nonzero **integer** relation among
`1, ζ, …, ζ^{N-1}`. This is the satisfiable replacement for the `F`-valued hypothesis —
every use of the latter in the rigidity chain instantiates integer coefficients only. -/
def HalfBasisIndepZ (ζ : F) (N : ℕ) : Prop :=
  ∀ g : Fin N → ℤ, (∑ j : Fin N, (g j : F) * ζ ^ (j : ℕ)) = 0 → ∀ j, g j = 0

/-- **THE DISCHARGE (Lam–Leung at `p = 2`; the queued O47/O48 cyclotomic keystone).**
In a characteristic-0 field, the half basis `1, ζ, …, ζ^{2^{m-1}-1}` of a primitive
`2^m`-th root of unity admits no nonzero integer relation: `minpoly ℚ ζ = Φ_{2^m}` has
degree `φ(2^m) = 2^{m-1}`, so the lower powers are `ℚ`-linearly independent. -/
theorem halfBasisIndepZ_of_primitiveRoot [CharZero F] {m : ℕ} (hm : 1 ≤ m) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ m)) :
    HalfBasisIndepZ ζ (2 ^ (m - 1)) := by
  intro g hg
  have hpos : 0 < 2 ^ m := pow_pos (by norm_num) m
  have hdeg : (minpoly ℚ ζ).natDegree = 2 ^ (m - 1) := by
    rw [← Polynomial.cyclotomic_eq_minpoly_rat hζ hpos, Polynomial.natDegree_cyclotomic,
      Nat.totient_prime_pow Nat.prime_two hm]
    simp
  have hli : LinearIndependent ℚ (fun i : Fin (2 ^ (m - 1)) => ζ ^ (i : ℕ)) := by
    have h := linearIndependent_pow (K := ℚ) ζ
    rwa [hdeg] at h
  have hsmul : (∑ j : Fin (2 ^ (m - 1)), (g j : ℚ) • ζ ^ (j : ℕ)) = 0 := by
    have hcast : ∀ j : Fin (2 ^ (m - 1)),
        (g j : ℚ) • ζ ^ (j : ℕ) = (g j : F) * ζ ^ (j : ℕ) := by
      intro j
      rw [Algebra.smul_def, map_intCast]
    rw [Finset.sum_congr rfl fun j _ => hcast j]
    exact hg
  intro j
  exact_mod_cast Fintype.linearIndependent_iff.mp hli (fun j => (g j : ℚ)) hsmul j

/-- No power of `ζ` in the independent range is zero (in particular `ζ ≠ 0`). -/
theorem pow_ne_zero_of_indep {N : ℕ} {ζ : F} (hindep : HalfBasisIndepZ ζ N) (j : Fin N) :
    ζ ^ (j : ℕ) ≠ 0 := by
  classical
  intro h0
  have hsingle := Finset.sum_eq_single (s := Finset.univ)
    (f := fun j' : Fin N => ((if j' = j then (1 : ℤ) else 0 : ℤ) : F) * ζ ^ (j' : ℕ)) j
    (fun j' _ hne => by
      show ((if j' = j then (1 : ℤ) else 0 : ℤ) : F) * ζ ^ (j' : ℕ) = 0
      rw [if_neg hne]
      simp)
    (fun hj => absurd (Finset.mem_univ _) hj)
  have hF : (∑ j' : Fin N,
      ((if j' = j then (1 : ℤ) else 0 : ℤ) : F) * ζ ^ (j' : ℕ)) = 0 := by
    rw [hsingle]
    show ((if j = j then (1 : ℤ) else 0 : ℤ) : F) * ζ ^ (j : ℕ) = 0
    rw [if_pos rfl, h0, mul_zero]
  have := hindep (fun j' => if j' = j then 1 else 0) hF j
  simp at this

/-! ## §2 The Round-25 bridge and general `t = 1` theorem, restated non-vacuously -/

/-- **The integer bridge, `ℤ`-form** (the non-vacuous restatement of
`Round25General.bridgeF`): equal signed-point sums force equal integer contributions at
every index. Identical proof skeleton; the independence hypothesis is now satisfiable. -/
theorem bridgeZ {N : ℕ} {ζ : F} (hindep : HalfBasisIndepZ ζ N)
    {A B : Finset (Fin N × Bool)}
    (hsum : (∑ p ∈ A, sval ζ p) = ∑ p ∈ B, sval ζ p) :
    ∀ j, contribZ A j = contribZ B j := by
  intro j
  have hF : (∑ j : Fin N, (((contribZ A j - contribZ B j : ℤ) : F) * ζ ^ (j : ℕ))) = 0 := by
    have expand : ∀ (S : Finset (Fin N × Bool)),
        (∑ p ∈ S, sval ζ p) = ∑ j : Fin N, ((contribZ S j : ℤ) : F) * ζ ^ (j : ℕ) := by
      intro S
      rw [Finset.sum_congr rfl (fun p _ => sval_eq_sum (ζ := ζ) p), Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [← sum_coefAt S j]
      push_cast
      rw [Finset.sum_mul]
    calc (∑ j : Fin N, (((contribZ A j - contribZ B j : ℤ) : F) * ζ ^ (j : ℕ)))
        = (∑ p ∈ A, sval ζ p) - (∑ p ∈ B, sval ζ p) := by
          rw [expand A, expand B, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro j _
          push_cast
          ring
      _ = 0 := by rw [hsum]; ring
  have := hindep (fun j => contribZ A j - contribZ B j) hF j
  omega

/-- **General `t = 1` rigidity, `ℤ`-form** (the non-vacuous restatement of
`Round25General.disjoint_equal_sum_antipodal`): disjoint signed-point sets with equal sums
are closed under the antipode. -/
theorem disjoint_equal_sum_antipodal_int {N : ℕ} {ζ : F} (hindep : HalfBasisIndepZ ζ N)
    {A B : Finset (Fin N × Bool)}
    (hsum : (∑ p ∈ A, sval ζ p) = ∑ p ∈ B, sval ζ p)
    (hdisj : Disjoint A B) :
    ∀ p ∈ A, antipode p ∈ A := by
  intro p hp
  by_contra hnot
  have hfib : fiber A p.1 = {p} := by
    apply Finset.Subset.antisymm
    · intro q hq
      obtain ⟨hqA, hqj⟩ := Finset.mem_filter.mp hq
      rw [Finset.mem_singleton]
      by_cases hs : q.2 = p.2
      · exact Prod.ext hqj hs
      · exfalso
        apply hnot
        have hqap : q = antipode p := by
          unfold antipode
          refine Prod.ext hqj ?_
          rcases hp2 : p.2 <;> rcases hq2 : q.2 <;> simp_all
        rw [← hqap]
        exact hqA
    · intro q hq
      rw [Finset.mem_singleton] at hq
      rw [hq]
      exact mem_fiber_self.mpr hp
  have hcA : contribZ A p.1 = isgn p := contrib_of_singleton hfib
  have hbridge := bridgeZ hindep hsum p.1
  have hcB : contribZ B p.1 = isgn p := by omega
  rcases fiber_trichotomy B p.1 with h0 | ⟨q, hq⟩ | ⟨_, hzero⟩
  · rw [show contribZ B p.1 = 0 by unfold contribZ; rw [h0]; rfl] at hcB
    unfold isgn at hcB
    rcases p with ⟨_, (_|_)⟩ <;> simp_all
  · have hcq : contribZ B p.1 = isgn q := contrib_of_singleton hq
    have hsgn : isgn q = isgn p := by omega
    have hqj : q.1 = p.1 := by
      have : q ∈ fiber B p.1 := by rw [hq]; exact Finset.mem_singleton_self q
      exact (Finset.mem_filter.mp this).2
    have hqB : q ∈ B := by
      have : q ∈ fiber B p.1 := by rw [hq]; exact Finset.mem_singleton_self q
      exact (Finset.mem_filter.mp this).1
    have hqp : q = p := by
      unfold isgn at hsgn
      rcases p with ⟨pj, (_|_)⟩ <;> rcases q with ⟨qj, (_|_)⟩ <;> simp_all
    rw [hqp] at hqB
    exact (Finset.disjoint_left.mp hdisj hp) hqB
  · rw [hzero] at hcB
    unfold isgn at hcB
    rcases p with ⟨_, (_|_)⟩ <;> simp_all <;> omega

/-! ## §3 The encoding bridge: field-element finsets to signed points and back -/

/-- `x` is a *signed half-basis point*: `x = ±ζ^j` for some `j < N`. For `ζ` a primitive
`2N`-th root of unity (with `N` the half-order) this says exactly `x ∈ μ_{2N}`. -/
def IsSignedPow (ζ : F) (N : ℕ) (x : F) : Prop :=
  ∃ j : Fin N, x = ζ ^ (j : ℕ) ∨ x = -ζ ^ (j : ℕ)

/-- `sval` is injective under `ℤ`-independence (the non-vacuous form of Round-23's
`sval_injective`): distinct signed points give a `{−2,…,2}`-coefficient relation. -/
theorem sval_injective_int {N : ℕ} {ζ : F} (hindep : HalfBasisIndepZ ζ N) :
    Function.Injective (sval ζ : Fin N × Bool → F) := by
  intro p q hpq
  have hF : (∑ j : Fin N, (((coefAt p j - coefAt q j : ℤ) : F) * ζ ^ (j : ℕ))) = 0 := by
    have hexp : (∑ j : Fin N, (((coefAt p j - coefAt q j : ℤ) : F) * ζ ^ (j : ℕ)))
        = (∑ j : Fin N, ((coefAt p j : ℤ) : F) * ζ ^ (j : ℕ))
          - ∑ j : Fin N, ((coefAt q j : ℤ) : F) * ζ ^ (j : ℕ) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      ring
    rw [hexp, ← sval_eq_sum, ← sval_eq_sum, hpq, sub_self]
  have hz := hindep (fun j => coefAt p j - coefAt q j) hF
  have h1 : coefAt p p.1 - coefAt q p.1 = 0 := hz p.1
  unfold coefAt at h1
  rw [if_pos rfl] at h1
  by_cases hj : q.1 = p.1
  · rw [if_pos hj] at h1
    have hsgn : isgn p = isgn q := by omega
    have hb : p.2 = q.2 := by
      unfold isgn at hsgn
      rcases hp2 : p.2 <;> rcases hq2 : q.2 <;> simp_all
    exact Prod.ext hj.symm hb
  · rw [if_neg hj] at h1
    exfalso
    unfold isgn at h1
    rcases hp2 : p.2 <;> simp [hp2] at h1

/-- Signed-point sets exclude `0`. -/
theorem zero_not_mem_of_signed {N : ℕ} {ζ : F} (hindep : HalfBasisIndepZ ζ N)
    {A : Finset F} (hA : ∀ x ∈ A, IsSignedPow ζ N x) : (0 : F) ∉ A := by
  intro h0
  obtain ⟨j, hj | hj⟩ := hA 0 h0
  · exact pow_ne_zero_of_indep hindep j hj.symm
  · exact pow_ne_zero_of_indep hindep j (neg_eq_zero.mp hj.symm)

/-- The antipode flips the sign of `sval`. -/
theorem sval_antipode {N : ℕ} (ζ : F) (p : Fin N × Bool) :
    sval ζ (antipode p) = -sval ζ p := by
  unfold sval antipode
  rcases p with ⟨j, (_|_)⟩ <;> simp

/-- **The field-level `t = 1` closure (the encoding bridge, unconditional given
`ℤ`-independence):** disjoint finsets of signed half-basis points with equal sums are both
antipodally closed in the Round-26 sense. -/
theorem antipodallyClosed_of_disjoint_equal_sum [DecidableEq F] {N : ℕ} {ζ : F}
    (hindep : HalfBasisIndepZ ζ N) {A B : Finset F}
    (hA : ∀ x ∈ A, IsSignedPow ζ N x) (hB : ∀ x ∈ B, IsSignedPow ζ N x)
    (hdisj : Disjoint A B) (hsum : (∑ x ∈ A, x) = ∑ x ∈ B, x) :
    AntipodallyClosed A ∧ AntipodallyClosed B := by
  classical
  -- the encodings
  have hencode : ∀ (S : Finset F), (∀ x ∈ S, IsSignedPow ζ N x) →
      ((Finset.univ.filter (fun p : Fin N × Bool => sval ζ p ∈ S)).image (sval ζ) = S) := by
    intro S hS
    ext x
    constructor
    · intro hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hp).2
    · intro hx
      obtain ⟨j, hj | hj⟩ := hS x hx
      · refine Finset.mem_image.mpr ⟨(j, true), ?_, ?_⟩
        · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          have hs : sval ζ (j, true) = x := by simp [sval, hj]
          rw [hs]; exact hx
        · simp [sval, hj]
      · refine Finset.mem_image.mpr ⟨(j, false), ?_, ?_⟩
        · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          have hs : sval ζ (j, false) = x := by simp [sval, hj]
          rw [hs]; exact hx
        · simp [sval, hj]
  set Ah : Finset (Fin N × Bool) := Finset.univ.filter (fun p => sval ζ p ∈ A) with hAh
  set Bh : Finset (Fin N × Bool) := Finset.univ.filter (fun p => sval ζ p ∈ B) with hBh
  have himgA : Ah.image (sval ζ) = A := hencode A hA
  have himgB : Bh.image (sval ζ) = B := hencode B hB
  have hinj := sval_injective_int hindep
  have hsumA : (∑ p ∈ Ah, sval ζ p) = ∑ x ∈ A, x := by
    rw [← himgA, Finset.sum_image (fun p _ q _ h => hinj h)]
  have hsumB : (∑ p ∈ Bh, sval ζ p) = ∑ x ∈ B, x := by
    rw [← himgB, Finset.sum_image (fun p _ q _ h => hinj h)]
  have hsumh : (∑ p ∈ Ah, sval ζ p) = ∑ p ∈ Bh, sval ζ p := by
    rw [hsumA, hsumB]; exact hsum
  have hdisjh : Disjoint Ah Bh := by
    rw [Finset.disjoint_left]
    intro p hpA hpB
    have h1 := (Finset.mem_filter.mp hpA).2
    have h2 := (Finset.mem_filter.mp hpB).2
    exact (Finset.disjoint_left.mp hdisj h1) h2
  have hantA := disjoint_equal_sum_antipodal_int hindep hsumh hdisjh
  have hantB := disjoint_equal_sum_antipodal_int hindep hsumh.symm hdisjh.symm
  -- transfer back
  have htransfer : ∀ (S : Finset F) (Sh : Finset (Fin N × Bool)),
      Sh = Finset.univ.filter (fun p => sval ζ p ∈ S) →
      (∀ x ∈ S, IsSignedPow ζ N x) → Sh.image (sval ζ) = S →
      (∀ p ∈ Sh, antipode p ∈ Sh) → AntipodallyClosed S := by
    intro S Sh hShdef hS himg hant
    refine ⟨zero_not_mem_of_signed hindep hS, ?_⟩
    intro x hx
    rw [← himg] at hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    have hap := hant p hp
    rw [hShdef] at hap
    have := (Finset.mem_filter.mp hap).2
    rwa [sval_antipode] at this
  exact ⟨htransfer A Ah hAh hA himgA hantA, htransfer B Bh hBh hB himgB hantB⟩

/-! ## §4 The scale descent `μ_{2^m} → μ_{2^{m-1}}` -/

/-- For `ζ` primitive `2^m`-th (`m ≥ 1`), the half-order power is `−1`. -/
theorem pow_half_eq_neg_one {m : ℕ} (hm : 1 ≤ m) {ζ : F}
    (hζ : IsPrimitiveRoot ζ (2 ^ m)) :
    ζ ^ (2 ^ (m - 1)) = -1 := by
  have hadd : 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ m := by
    have h1 : m - 1 + 1 = m := by omega
    calc 2 ^ (m - 1) + 2 ^ (m - 1) = 2 ^ (m - 1) * 2 := by ring
      _ = 2 ^ (m - 1 + 1) := (pow_succ 2 (m - 1)).symm
      _ = 2 ^ m := by rw [h1]
  have hsq : ζ ^ (2 ^ (m - 1)) * ζ ^ (2 ^ (m - 1)) = 1 := by
    rw [← pow_add, hadd, hζ.pow_eq_one]
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · exact absurd h (hζ.pow_ne_one_of_pos_of_lt
      (Nat.pos_iff_ne_zero.mp (pow_pos (by norm_num) _))
      (Nat.pow_lt_pow_right (by norm_num) (by omega)))
  · exact h

/-- **Squaring descends signed half-basis points one level:** if `x = ±ζ^j` (`j < 2^{m-1}`)
then `x² = ±(ζ²)^{j'}` (`j' < 2^{m-2}`), using `ζ^{2^{m-1}} = −1` to fold the upper range. -/
theorem isSignedPow_sq {m : ℕ} (hm : 2 ≤ m) {ζ : F}
    (hhalf : ζ ^ (2 ^ (m - 1)) = -1) {x : F}
    (hx : IsSignedPow ζ (2 ^ (m - 1)) x) :
    IsSignedPow (ζ ^ 2) (2 ^ (m - 2)) (x ^ 2) := by
  obtain ⟨j, hj⟩ := hx
  have hx2 : x ^ 2 = (ζ ^ 2) ^ (j : ℕ) := by
    rcases hj with h | h <;> rw [h] <;> ring
  by_cases hsmall : (j : ℕ) < 2 ^ (m - 2)
  · exact ⟨⟨(j : ℕ), hsmall⟩, Or.inl hx2⟩
  · have hsplit : 2 ^ (m - 1) = 2 ^ (m - 2) + 2 ^ (m - 2) := by
      have h1 : m - 2 + 1 = m - 1 := by omega
      calc 2 ^ (m - 1) = 2 ^ (m - 2 + 1) := by rw [h1]
        _ = 2 ^ (m - 2) * 2 := pow_succ 2 (m - 2)
        _ = 2 ^ (m - 2) + 2 ^ (m - 2) := by ring
    have hjlt : (j : ℕ) - 2 ^ (m - 2) < 2 ^ (m - 2) := by
      have hj2 := j.isLt
      omega
    refine ⟨⟨(j : ℕ) - 2 ^ (m - 2), hjlt⟩, Or.inr ?_⟩
    show x ^ 2 = -(ζ ^ 2) ^ ((j : ℕ) - 2 ^ (m - 2))
    have htop : (ζ ^ 2) ^ (2 ^ (m - 2)) = -1 := by
      rw [← pow_mul]
      have h2 : 2 * 2 ^ (m - 2) = 2 ^ (m - 1) := by rw [hsplit]; ring
      rw [h2, hhalf]
    have hpow : (ζ ^ 2) ^ (j : ℕ)
        = (ζ ^ 2) ^ ((j : ℕ) - 2 ^ (m - 2)) * (ζ ^ 2) ^ (2 ^ (m - 2)) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hx2, hpow, htop]
    ring

/-! ## §5 The closure-assembly step and THE ITERATED THEOREM -/

/-- **The assembly step** (the general form of O48's `mul_i_closure`): if `A` is antipodally
closed and `A²` is closed under multiplication by `ω²`, then `A` is closed under
multiplication by `ω`: a shared square forces `y = ±ωx`, and the antipode upgrades the
sign. Characteristic-free. -/
theorem closure_step [DecidableEq F] {A : Finset F} (hA : AntipodallyClosed A) {ω : F}
    (hsq : ∀ y ∈ squares A, ω ^ 2 * y ∈ squares A) :
    ∀ x ∈ A, ω * x ∈ A := by
  intro x hx
  have hx2 : x ^ 2 ∈ squares A := Finset.mem_image_of_mem (fun z => z ^ 2) hx
  obtain ⟨y, hyA, hy⟩ := Finset.mem_image.mp (hsq _ hx2)
  have hfact : (y - ω * x) * (y + ω * x) = 0 := by linear_combination hy
  rcases mul_eq_zero.mp hfact with h | h
  · have hyx : y = ω * x := by linear_combination h
    rwa [← hyx]
  · have hyx : y = -(ω * x) := by linear_combination h
    have h2 := hA.2 y hyA
    rwa [hyx, neg_neg] at h2

/-- **THE ITERATED `2^k`-LIFT THEOREM (full-window rigidity, disjoint case,
UNCONDITIONAL).** Let `F` have characteristic 0, `ζ` a primitive `2^m`-th root of unity,
and `A, B` disjoint finsets of signed half-basis points (`= μ_{2^m}` elements) with equal
power sums `p_1, …, p_t`. If `1 ≤ k ≤ m` and `2^{k-1} ≤ t`, then `A` and `B` are closed
under multiplication by **every** `2^k`-th root of unity in `F` — the `2^k`-lift
(Round-22) structure. Proof: induction on `k`; the base is the discharged `t = 1`
antipodal closure; the step squares the sets (Round-26 engine), applies the inductive
hypothesis one level down (`ζ²`, `t/2`), and reassembles via `closure_step`. -/
theorem iterated_2k_lift [CharZero F] [DecidableEq F] :
    ∀ k : ℕ, 1 ≤ k → ∀ m : ℕ, k ≤ m → ∀ ζ : F, IsPrimitiveRoot ζ (2 ^ m) →
    ∀ A B : Finset F,
      (∀ x ∈ A, IsSignedPow ζ (2 ^ (m - 1)) x) →
      (∀ x ∈ B, IsSignedPow ζ (2 ^ (m - 1)) x) →
      Disjoint A B →
      ∀ t : ℕ, 2 ^ (k - 1) ≤ t →
      (∀ r, 1 ≤ r → r ≤ t → (∑ x ∈ A, x ^ r) = ∑ x ∈ B, x ^ r) →
      ∀ ω : F, ω ^ (2 ^ k) = 1 →
      (∀ x ∈ A, ω * x ∈ A) ∧ (∀ x ∈ B, ω * x ∈ B) := by
  intro k
  induction k with
  | zero => omega
  | succ k ih =>
    intro _ m hkm ζ hζ A B hA hB hdisj t ht hwin ω hω
    simp only [Nat.add_sub_cancel] at ht
    have hm1 : 1 ≤ m := by omega
    have hindep := halfBasisIndepZ_of_primitiveRoot hm1 hζ
    have ht1 : 1 ≤ t := le_trans Nat.one_le_two_pow ht
    have hsum1 : (∑ x ∈ A, x) = ∑ x ∈ B, x := by
      have := hwin 1 le_rfl ht1
      simpa using this
    have hclosed := antipodallyClosed_of_disjoint_equal_sum hindep hA hB hdisj hsum1
    by_cases hk : k = 0
    · -- base: ω² = 1, so ω = ±1
      subst hk
      have hω2 : ω * ω = 1 := by
        have : ω ^ (2 : ℕ) = 1 := by simpa using hω
        rwa [pow_two] at this
      rcases mul_self_eq_one_iff.mp hω2 with h | h
      · subst h
        exact ⟨fun x hx => by rwa [one_mul], fun x hx => by rwa [one_mul]⟩
      · subst h
        exact ⟨fun x hx => by rw [neg_one_mul]; exact hclosed.1.2 x hx,
               fun x hx => by rw [neg_one_mul]; exact hclosed.2.2 x hx⟩
    · -- step: halve the window, descend the scale, reassemble
      have hk1 : 1 ≤ k := by omega
      have hm2 : 2 ≤ m := by omega
      obtain ⟨hdisj2, hwin2⟩ := window_halving_step hclosed.1 hclosed.2 hdisj hwin
      have hhalf := pow_half_eq_neg_one hm1 hζ
      have hζ2 : IsPrimitiveRoot (ζ ^ 2) (2 ^ (m - 1)) := by
        refine hζ.pow (pow_pos (by norm_num) m) ?_
        have h1 : m - 1 + 1 = m := by omega
        calc 2 ^ m = 2 ^ (m - 1 + 1) := by rw [h1]
          _ = 2 * 2 ^ (m - 1) := pow_succ' 2 (m - 1)
      have hidx : m - 1 - 1 = m - 2 := by omega
      have hA2 : ∀ y ∈ squares A, IsSignedPow (ζ ^ 2) (2 ^ (m - 1 - 1)) y := by
        intro y hy
        obtain ⟨x, hxA, rfl⟩ := Finset.mem_image.mp hy
        rw [hidx]
        exact isSignedPow_sq hm2 hhalf (hA x hxA)
      have hB2 : ∀ y ∈ squares B, IsSignedPow (ζ ^ 2) (2 ^ (m - 1 - 1)) y := by
        intro y hy
        obtain ⟨x, hxB, rfl⟩ := Finset.mem_image.mp hy
        rw [hidx]
        exact isSignedPow_sq hm2 hhalf (hB x hxB)
      have hdiv : 2 ^ (k - 1) ≤ t / 2 := by
        have h2 : 2 ^ k = 2 ^ (k - 1) * 2 := by
          have h1 : k - 1 + 1 = k := by omega
          calc 2 ^ k = 2 ^ (k - 1 + 1) := by rw [h1]
            _ = 2 ^ (k - 1) * 2 := pow_succ 2 (k - 1)
        omega
      have hwin' : ∀ r, 1 ≤ r → r ≤ t / 2 →
          (∑ y ∈ squares A, y ^ r) = ∑ y ∈ squares B, y ^ r := by
        intro r h1 hr
        exact hwin2 r h1 (by omega)
      have hω2 : (ω ^ 2) ^ (2 ^ k) = 1 := by
        rw [← pow_mul]
        have h2 : 2 * 2 ^ k = 2 ^ (k + 1) := (pow_succ' 2 k).symm
        rw [h2]
        exact hω
      obtain ⟨ihA, ihB⟩ := ih hk1 (m - 1) (by omega) (ζ ^ 2) hζ2
        (squares A) (squares B) hA2 hB2 hdisj2 (t / 2) hdiv hwin' (ω ^ 2) hω2
      exact ⟨closure_step hclosed.1 ihA, closure_step hclosed.2 ihB⟩

/-! ## §6 Display corollaries -/

/-- **Coset-union structure (the O48-shaped consequence):** under the hypotheses of
`iterated_2k_lift`, `A` is closed under the canonical generator `ζ^{2^{m-k}}` of
`μ_{2^k}` — i.e. `A` (and `B`) are unions of `μ_{2^k}`-cosets, `2^k` the window-adapted
2-power. Completely hypothesis-discharged: characteristic 0 + primitivity suffice. -/
theorem coset_closure_of_equal_window [CharZero F] [DecidableEq F] {k m : ℕ}
    (hk : 1 ≤ k) (hkm : k ≤ m) {ζ : F} (hζ : IsPrimitiveRoot ζ (2 ^ m))
    {A B : Finset F}
    (hA : ∀ x ∈ A, IsSignedPow ζ (2 ^ (m - 1)) x)
    (hB : ∀ x ∈ B, IsSignedPow ζ (2 ^ (m - 1)) x)
    (hdisj : Disjoint A B) {t : ℕ} (ht : 2 ^ (k - 1) ≤ t)
    (hwin : ∀ r, 1 ≤ r → r ≤ t → (∑ x ∈ A, x ^ r) = ∑ x ∈ B, x ^ r) :
    ∀ x ∈ A, ζ ^ (2 ^ (m - k)) * x ∈ A := by
  have hgen : (ζ ^ (2 ^ (m - k))) ^ (2 ^ k) = 1 := by
    rw [← pow_mul, ← pow_add]
    have h1 : m - k + k = m := by omega
    rw [h1]
    exact hζ.pow_eq_one
  exact (iterated_2k_lift k hk m hkm ζ hζ A B hA hB hdisj t ht hwin
    (ζ ^ (2 ^ (m - k))) hgen).1

/-- **`t = 1` antipodal closure, end-to-end unconditional** (the non-vacuity witness for the
whole chain): in characteristic 0, disjoint subsets of `μ_{2^m}` with equal sums are unions
of antipodal pairs. No independence hypothesis — it is discharged cyclotomically. -/
theorem antipodal_closure_unconditional [CharZero F] [DecidableEq F] {m : ℕ}
    (hm : 1 ≤ m) {ζ : F} (hζ : IsPrimitiveRoot ζ (2 ^ m))
    {A B : Finset F}
    (hA : ∀ x ∈ A, IsSignedPow ζ (2 ^ (m - 1)) x)
    (hB : ∀ x ∈ B, IsSignedPow ζ (2 ^ (m - 1)) x)
    (hdisj : Disjoint A B) (hsum : (∑ x ∈ A, x) = ∑ x ∈ B, x) :
    ∀ x ∈ A, -x ∈ A := by
  have hindep := halfBasisIndepZ_of_primitiveRoot hm hζ
  exact (antipodallyClosed_of_disjoint_equal_sum hindep hA hB hdisj hsum).1.2

/-! ## §7 Single-set corollaries (`B = ∅`): Lam–Leung at `p = 2` and the O48 tower theorem -/

/-- **Lam–Leung at `p = 2`, single-set form (the queued O47 brick, now a theorem):** in
characteristic 0, a finset of `μ_{2^m}` elements with vanishing sum is a union of antipodal
pairs. This is the `B = ∅` instance of the disjoint-pair machinery. -/
theorem vanishing_sum_antipodal [CharZero F] [DecidableEq F] {m : ℕ}
    (hm : 1 ≤ m) {ζ : F} (hζ : IsPrimitiveRoot ζ (2 ^ m))
    {A : Finset F} (hA : ∀ x ∈ A, IsSignedPow ζ (2 ^ (m - 1)) x)
    (hsum : (∑ x ∈ A, x) = 0) :
    ∀ x ∈ A, -x ∈ A := by
  have hindep := halfBasisIndepZ_of_primitiveRoot hm hζ
  have h := antipodallyClosed_of_disjoint_equal_sum (B := (∅ : Finset F)) hindep hA
    (fun x hx => absurd hx (Finset.notMem_empty x)) (Finset.disjoint_empty_right A)
    (by rw [Finset.sum_empty]; exact hsum)
  exact h.1.2

/-- **THE TOWER THEOREM, power-sum form (O48's forward inclusion), machine-checked at all
`t`:** in characteristic 0, a finset of `μ_{2^m}` elements whose power sums `p_1, …, p_t`
all vanish (`2^{k-1} ≤ t`, `1 ≤ k ≤ m`) is closed under multiplication by every `2^k`-th
root of unity — a union of `μ_{2^k}`-cosets. With O46's `coset_union_esymm_zero` as the
converse inclusion, this is the O48 squaring-tower descent as a theorem rather than a
recorded induction (modulo the Newton `e ↔ p` window formulation bridge). -/
theorem vanishing_window_coset_closure [CharZero F] [DecidableEq F] {k m : ℕ}
    (hk : 1 ≤ k) (hkm : k ≤ m) {ζ : F} (hζ : IsPrimitiveRoot ζ (2 ^ m))
    {A : Finset F} (hA : ∀ x ∈ A, IsSignedPow ζ (2 ^ (m - 1)) x)
    {t : ℕ} (ht : 2 ^ (k - 1) ≤ t)
    (hwin : ∀ r, 1 ≤ r → r ≤ t → (∑ x ∈ A, x ^ r) = 0) :
    ∀ ω : F, ω ^ (2 ^ k) = 1 → ∀ x ∈ A, ω * x ∈ A := by
  intro ω hω
  exact (iterated_2k_lift k hk m hkm ζ hζ A ∅ hA
    (fun x hx => absurd hx (Finset.notMem_empty x)) (Finset.disjoint_empty_right A)
    t ht
    (fun r h1 hr => by rw [Finset.sum_empty]; exact hwin r h1 hr)
    ω hω).1

end Round29IteratedLift

#print axioms Round29IteratedLift.fValued_hindep_unsatisfiable
#print axioms Round29IteratedLift.halfBasisIndepZ_of_primitiveRoot
#print axioms Round29IteratedLift.disjoint_equal_sum_antipodal_int
#print axioms Round29IteratedLift.antipodallyClosed_of_disjoint_equal_sum
#print axioms Round29IteratedLift.iterated_2k_lift
#print axioms Round29IteratedLift.coset_closure_of_equal_window
#print axioms Round29IteratedLift.antipodal_closure_unconditional
#print axioms Round29IteratedLift.vanishing_sum_antipodal
#print axioms Round29IteratedLift.vanishing_window_coset_closure
