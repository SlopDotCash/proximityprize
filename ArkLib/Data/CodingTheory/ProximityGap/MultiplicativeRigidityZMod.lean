/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Algebra.Group.Subgroup.Ker

/-! # Coset rigidity for the power map on a finite cyclic group

This file formalizes the *monomial agreement* (a.k.a. "coset rigidity") lemma used in the
multiplicative-blowup analysis of the proximity gap: in a finite cyclic group `G` of order `n`,
the solution set of `x ^ d = c` is a coset of the kernel of the `d`-th power map, hence is either
empty or has cardinality *exactly* `Nat.gcd d n`.

* `MultiplicativeRigidity.pow_map_card_eq_zero_or_gcd` — coset rigidity through an injective
  evaluation `ι : G →* M` (the workhorse).
* `MultiplicativeRigidity.pow_eq_card_eq_zero_or_gcd` — the core count for a finite cyclic
  group `G` (stated with `Fintype.card G`).
* `MultiplicativeRigidity.pow_eq_card_le_gcd` — the consumable `≤ gcd d n` form.
* `MultiplicativeRigidity.binomial_agree_card` — the *monomial agreement bound* for a finite
  cyclic subgroup `H ≤ Fˣ`: the count of `x ∈ H` with `c₁ * x ^ a = c₂ * x ^ b` (`b < a`) is
  `0` or `Nat.gcd (a - b) n`, obtained by dividing through by the unit `x ^ b`.
* `MultiplicativeRigidity.binomial_agree_card_le` — its `≤ a - b` consumable form.
* `MultiplicativeRigidity.binomial_separation` — the rigidity packaged as `agreement < k`
  whenever `b < a < k` (exponents drawn from degree-`< k` data).

The proof route is purely group-theoretic: the `d`-th power map is `powMonoidHom d`, its fibers are
cosets of its kernel (`MonoidHom.fiberEquivKer`), so every non-empty fiber has the same size as the
kernel, whose cardinality for a finite cyclic group is `Nat.gcd (Nat.card G) d`
(`IsCyclic.card_powMonoidHom_ker`). -/

namespace MultiplicativeRigidity

open Finset

section Hom

variable {G : Type*} [CommGroup G] [Fintype G] [IsCyclic G] [DecidableEq G]
variable {M : Type*} [CommGroup M] [DecidableEq M]

omit [CommGroup G] [IsCyclic G] [DecidableEq G] [CommGroup M] [DecidableEq M] in
/-- Bridge: for any evaluation function `e : G → M`, the `Finset.filter` count of `e x = γ`
equals `Nat.card` of the fiber `e ⁻¹' {γ}`. Stated for a bare function (not a `MonoidHom`
application) so the `DecidablePred` instance is supplied by `Classical` and never needs to match. -/
private theorem card_filter_eq_card_fiber (e : G → M) (γ : M)
    [DecidablePred fun x => e x = γ] :
    (univ.filter fun x : G => e x = γ).card = Nat.card (e ⁻¹' {γ}) := by
  classical
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card' (e ⁻¹' {γ})]
  congr 1
  ext x
  simp only [Set.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, mem_filter, mem_univ,
    true_and]

omit [DecidableEq G] in
/-- **Coset rigidity through an injective evaluation.**

Generalization of `pow_eq_card_eq_zero_or_gcd` where the `d`-th power is post-composed with an
injective monoid hom `ι : G →* M` (e.g. the inclusion of a finite cyclic subgroup `H ≤ Fˣ` into
`Fˣ`). The fiber of `x ↦ ι (x ^ d)` over a target `γ : M` is again a coset of the kernel of the
`d`-th power map (injectivity of `ι` makes the kernels coincide), so it is empty or has size
exactly `Nat.gcd d (Fintype.card G)`. -/
theorem pow_map_card_eq_zero_or_gcd (ι : G →* M) (hι : Function.Injective ι)
    (d : ℕ) (γ : M) :
    (univ.filter fun x : G => ι (x ^ d) = γ).card = 0 ∨
      (univ.filter fun x : G => ι (x ^ d) = γ).card = Nat.gcd d (Fintype.card G) := by
  classical
  -- The composite hom `f = ι ∘ powMonoidHom d`; note `f x = ι (x ^ d)` definitionally.
  set f : G →* M := ι.comp (powMonoidHom d) with hf
  have hfe : (fun x : G => ι (x ^ d)) = (f : G → M) := rfl
  rw [card_filter_eq_card_fiber (fun x : G => ι (x ^ d)) γ, hfe]
  -- The kernel of `f` equals the kernel of `powMonoidHom d` (injective `ι`).
  have hker : f.ker = (powMonoidHom d : G →* G).ker := by
    ext x
    simp only [hf, MonoidHom.mem_ker, MonoidHom.comp_apply, ← map_one ι]
    exact ⟨fun h => hι h, fun h => congrArg ι h⟩
  by_cases hγ : ((f : G → M) ⁻¹' {γ}).Nonempty
  · right
    obtain ⟨a, ha⟩ := hγ
    have hpre : (f : G → M) ⁻¹' {γ} = (f : G → M) ⁻¹' {f a} := by rw [(ha : f a = γ)]
    have hequiv : ((f : G → M) ⁻¹' {f a}) ≃ f.ker := MonoidHom.fiberEquivKer f a
    have hcard : Nat.card ((f : G → M) ⁻¹' {γ}) = Nat.card f.ker := by
      rw [hpre]; exact Nat.card_congr hequiv
    rw [hcard, hker, IsCyclic.card_powMonoidHom_ker G d, Nat.card_eq_fintype_card, Nat.gcd_comm]
  · left
    rw [Set.not_nonempty_iff_eq_empty] at hγ
    rw [hγ]; simp

/-- **Coset rigidity / monomial agreement (core).**

In a finite cyclic group `G` of order `n = Fintype.card G`, for any exponent `d` and target `c`,
the number of `x : G` with `x ^ d = c` is either `0` (no solution) or *exactly* `Nat.gcd d n`
(a coset of the kernel of the `d`-th power map).

Note the `d = 0` edge case is honest: `gcd 0 n = n`, and indeed `x ^ 0 = c` holds for all `x`
when `c = 1` (count `n`) and for no `x` otherwise (count `0`). -/
theorem pow_eq_card_eq_zero_or_gcd (d : ℕ) (c : G) :
    (univ.filter fun x : G => x ^ d = c).card = 0 ∨
      (univ.filter fun x : G => x ^ d = c).card = Nat.gcd d (Fintype.card G) := by
  classical
  have h := pow_map_card_eq_zero_or_gcd (MonoidHom.id G) Function.injective_id d c
  simpa using h

/-- The consumable upper bound: the agreement count for `x ^ d = c` is at most `Nat.gcd d n`. -/
theorem pow_eq_card_le_gcd (d : ℕ) (c : G) :
    (univ.filter fun x : G => x ^ d = c).card ≤ Nat.gcd d (Fintype.card G) := by
  rcases pow_eq_card_eq_zero_or_gcd d c with h | h
  · rw [h]; exact Nat.zero_le _
  · rw [h]

end Hom

section Subgroup

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Monomial agreement bound on a finite cyclic subgroup of `Fˣ`.**

Let `H` be a finite cyclic subgroup of `Fˣ` of order `n = Fintype.card H`, let `c₁ c₂ : Fˣ` be
nonzero constants, and let `b < a` be exponents. Then the number of `x ∈ H` solving the binomial
equation `c₁ * x ^ a = c₂ * x ^ b` is either `0` or *exactly* `Nat.gcd (a - b) n`.

Proof: divide through by the unit `x ^ b` (every `x ∈ H ⊆ Fˣ` is invertible), turning the equation
into `(x : Fˣ) ^ (a - b) = c₂ * c₁⁻¹`, then apply the coset-rigidity count for the inclusion
`H ↪ Fˣ`. -/
theorem binomial_agree_card
    {H : Subgroup Fˣ} [Fintype H] [IsCyclic H] [DecidableEq H]
    (c₁ c₂ : Fˣ) {a b : ℕ} (hba : b < a) :
    (univ.filter fun x : H => c₁ * (x : Fˣ) ^ a = c₂ * (x : Fˣ) ^ b).card = 0 ∨
      (univ.filter fun x : H => c₁ * (x : Fˣ) ^ a = c₂ * (x : Fˣ) ^ b).card
        = Nat.gcd (a - b) (Fintype.card H) := by
  classical
  -- For a unit `x`, `c₁ * x^a = c₂ * x^b ↔ x^(a-b) = c₂ * c₁⁻¹` (divide by the unit `x^b`).
  have key : ∀ x : H,
      (c₁ * (x : Fˣ) ^ a = c₂ * (x : Fˣ) ^ b) ↔ (H.subtype (x ^ (a - b)) = c₂ * c₁⁻¹) := by
    intro x
    rw [map_pow, Subgroup.coe_subtype]
    have hsplit : (x : Fˣ) ^ a = (x : Fˣ) ^ (a - b) * (x : Fˣ) ^ b := by
      rw [← pow_add, Nat.sub_add_cancel hba.le]
    -- Cancel the unit `x ^ b`, leaving `c₁ * x^(a-b) = c₂`, then isolate `x^(a-b)`.
    rw [hsplit, ← mul_assoc, mul_left_inj, mul_comm c₁ ((x : Fˣ) ^ (a - b)),
      eq_mul_inv_iff_mul_eq]
  -- Rewrite the filter predicate and invoke `pow_map_card_eq_zero_or_gcd` for `ι = H.subtype`.
  have hfilter : (univ.filter fun x : H => c₁ * (x : Fˣ) ^ a = c₂ * (x : Fˣ) ^ b)
      = (univ.filter fun x : H => (H.subtype) (x ^ (a - b)) = c₂ * c₁⁻¹) :=
    Finset.filter_congr (fun x _ => key x)
  rw [hfilter]
  exact pow_map_card_eq_zero_or_gcd (H.subtype) (Subgroup.subtype_injective H) (a - b) (c₂ * c₁⁻¹)

/-- The consumable upper bound form: the binomial agreement count is at most `a - b`.

Uses `Nat.gcd (a - b) n ≤ a - b`, valid since `a - b ≠ 0` (because `b < a`). -/
theorem binomial_agree_card_le
    {H : Subgroup Fˣ} [Fintype H] [IsCyclic H] [DecidableEq H]
    (c₁ c₂ : Fˣ) {a b : ℕ} (hba : b < a) :
    (univ.filter fun x : H => c₁ * (x : Fˣ) ^ a = c₂ * (x : Fˣ) ^ b).card ≤ a - b := by
  have hab : a - b ≠ 0 := by omega
  have hgcd : Nat.gcd (a - b) (Fintype.card H) ≤ a - b := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)
  rcases binomial_agree_card (H := H) c₁ c₂ hba with h | h
  · rw [h]; exact Nat.zero_le _
  · rw [h]; exact hgcd

/-- **Binomial separation.**

Packaging of coset rigidity in the form the dossier consumes: if `b < a < k` (both exponents come
from degree-`< k` data, so `a ≤ k - 1`), then the binomial `c₁ * x ^ a = c₂ * x ^ b` is satisfied
by *strictly fewer than `k`* points of the finite cyclic subgroup `H ≤ Fˣ`. -/
theorem binomial_separation
    {H : Subgroup Fˣ} [Fintype H] [IsCyclic H] [DecidableEq H]
    (c₁ c₂ : Fˣ) {a b k : ℕ} (hba : b < a) (hak : a < k) :
    (univ.filter fun x : H => c₁ * (x : Fˣ) ^ a = c₂ * (x : Fˣ) ^ b).card < k := by
  have h := binomial_agree_card_le (H := H) c₁ c₂ hba
  omega

end Subgroup

end MultiplicativeRigidity

