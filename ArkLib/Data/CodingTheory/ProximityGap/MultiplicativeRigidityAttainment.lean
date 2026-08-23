/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MultiplicativeRigidityZMod

/-! # The ATTAINMENT criterion for the power-map coset-rigidity dichotomy (#444, #389)

`MultiplicativeRigidity.pow_eq_card_eq_zero_or_gcd` proves the SHARP DICHOTOMY for the count of
`x ^ d = c` in a finite cyclic group `G` of order `n`:

> the count is **either `0` or exactly `Nat.gcd d n`**.

It does NOT say *which* branch occurs. This file pins it: the `gcd` branch is the one realised
whenever the fiber is nonempty, and — crucially — the fiber over `c = 1` is **always** nonempty
(`x = 1` is a solution), so the **worst-case** count over all targets `c` is *exactly* `gcd d n`,
attained at `c = 1`. This converts the `0`-or-`gcd` dichotomy into a usable exact worst-case
identity, the structural input the binomial / monomial agreement strata consume (the probe
`probe_binomial_attainment_criterion.py` confirms the count is `gcd(d,n)` iff the target is a
`d`-th power, i.e. `c ^ (n / gcd d n) = 1`, and the worst case is attained at `c = 1`, over the
thin prize-regime `μ_n` with `p ≡ 1 mod n`, `(p−1)/n ≥ 2`, never `n = q − 1`).

## Theorems
* `pow_map_card_eq_gcd_of_nonempty` — if the fiber `{x : ι (x ^ d) = γ}` is nonempty then its
  card is *exactly* `Nat.gcd d (Fintype.card G)` (the non-zero branch isolated).
* `pow_one_eq_card_eq_gcd` — `#{x : x ^ d = 1} = Nat.gcd d (Fintype.card G)` (the fiber over `1`
  is always nonempty, so the `gcd` branch fires).
* `pow_eq_card_le_pow_one` — every fiber count is `≤` the count over `1`, so `c = 1` is the
  worst case: `#{x : x ^ d = c} ≤ #{x : x ^ d = 1}`.
* `binomial_agree_card_eq_gcd_of_nonempty` — the arbitrary-target binomial fiber is *exactly*
  `Nat.gcd (a − b) n` whenever it has one witness, isolating the nonzero branch of the dichotomy.
* `binomial_self_agree_card_eq_gcd` — the WORST-CASE binomial incidence on a cyclic
  `H ≤ Fˣ` is *exactly* `Nat.gcd (a − b) (Fintype.card H)`, realised when `c₁ = c₂` (target
  `γ = 1`): `#{x ∈ H : c * x ^ a = c * x ^ b} = Nat.gcd (a − b) n`.

NON-MOMENT (pure cyclic-group / power-map coset combinatorics). EXTEND-proven (sits directly on
`pow_map_card_eq_zero_or_gcd` and `binomial_agree_card`). Axiom-clean
(`propext, Classical.choice, Quot.sound`). NOT a CORE / Conj-7.1 closure — the strata-to-soundness
bridge remains open; this only pins the per-direction worst-case incidence to the gcd value.
-/

set_option linter.unusedDecidableInType false

namespace MultiplicativeRigidity

open Finset

section Hom

variable {G : Type*} [CommGroup G] [Fintype G] [IsCyclic G] [DecidableEq G]
variable {M : Type*} [CommGroup M] [DecidableEq M]

omit [DecidableEq G] in
/-- **The `gcd` branch isolated.** If the fiber of `x ↦ ι (x ^ d)` over `γ` is nonempty (there is
some `x₀` with `ι (x₀ ^ d) = γ`), then its cardinality is *exactly* `Nat.gcd d (Fintype.card G)`.
The vacuous `0` branch of `pow_map_card_eq_zero_or_gcd` is ruled out by the witness. -/
theorem pow_map_card_eq_gcd_of_nonempty (ι : G →* M) (hι : Function.Injective ι)
    (d : ℕ) (γ : M) {x₀ : G} (hx₀ : ι (x₀ ^ d) = γ) :
    (univ.filter fun x : G => ι (x ^ d) = γ).card = Nat.gcd d (Fintype.card G) := by
  classical
  rcases pow_map_card_eq_zero_or_gcd ι hι d γ with h | h
  · -- The filter is empty, contradicting the witness `x₀`.
    exfalso
    have hmem : x₀ ∈ univ.filter fun x : G => ι (x ^ d) = γ := by
      simp only [mem_filter, mem_univ, true_and, hx₀]
    rw [Finset.card_eq_zero] at h
    rw [h] at hmem
    exact absurd hmem (Finset.notMem_empty x₀)
  · exact h

/-- **The fiber over `1` realises the `gcd` branch.** Since `x = 1` solves `x ^ d = 1`, the fiber
over the identity is nonempty, so its card is *exactly* `Nat.gcd d (Fintype.card G)`. This is the
worst-case attainment witness: the dichotomy's nontrivial branch is always realised at `c = 1`. -/
theorem pow_one_eq_card_eq_gcd (d : ℕ) :
    (univ.filter fun x : G => x ^ d = (1 : G)).card = Nat.gcd d (Fintype.card G) := by
  classical
  have h := pow_map_card_eq_gcd_of_nonempty (MonoidHom.id G) Function.injective_id d (1 : G)
    (x₀ := 1) (by simp)
  simpa using h

/-- **`c = 1` is the worst case.** For every target `c`, the count of `x ^ d = c` is at most the
count over the identity. (Both are bounded by `gcd d n`, and the latter *attains* it.) -/
theorem pow_eq_card_le_pow_one (d : ℕ) (c : G) :
    (univ.filter fun x : G => x ^ d = c).card ≤
      (univ.filter fun x : G => x ^ d = (1 : G)).card := by
  classical
  rw [pow_one_eq_card_eq_gcd]
  exact pow_eq_card_le_gcd d c

end Hom

section Subgroup

variable {F : Type*} [Field F] [DecidableEq F]

/-- **Any nonempty binomial fiber has the full gcd size.** For a finite cyclic subgroup
`H ≤ Fˣ`, the binomial equation `c₁ * x ^ a = c₂ * x ^ b` (`b < a`) has the usual `0`-or-`gcd`
coset-rigidity dichotomy. This theorem isolates the nonzero branch in the exact form consumed by
C71 strata arguments: once a single witness `x₀` exists, the whole fiber has cardinality exactly
`Nat.gcd (a − b) (Fintype.card H)`. -/
theorem binomial_agree_card_eq_gcd_of_nonempty
    {H : Subgroup Fˣ} [Fintype H] [IsCyclic H] [DecidableEq H]
    (c₁ c₂ : Fˣ) {a b : ℕ} (hba : b < a) {x₀ : H}
    (hx₀ : c₁ * (x₀ : Fˣ) ^ a = c₂ * (x₀ : Fˣ) ^ b) :
    (univ.filter fun x : H => c₁ * (x : Fˣ) ^ a = c₂ * (x : Fˣ) ^ b).card
      = Nat.gcd (a - b) (Fintype.card H) := by
  classical
  rcases binomial_agree_card (H := H) c₁ c₂ hba with hzero | hgcd
  · exfalso
    have hxmem : x₀ ∈ (univ.filter fun x : H => c₁ * (x : Fˣ) ^ a = c₂ * (x : Fˣ) ^ b) := by
      simp [hx₀]
    rw [Finset.card_eq_zero] at hzero
    rw [hzero] at hxmem
    exact Finset.notMem_empty x₀ hxmem
  · exact hgcd

/-- **The worst-case binomial incidence is *exactly* `gcd (a − b) n`.** Taking `c₁ = c₂ = c`
(target `γ = c · c⁻¹ = 1`, the worst case isolated by `pow_one_eq_card_eq_gcd`), the binomial
`c * x ^ a = c * x ^ b` on a finite cyclic subgroup `H ≤ Fˣ` of order `n` is solved by *exactly*
`Nat.gcd (a − b) n` points. So the `0`-or-`gcd` dichotomy of `binomial_agree_card` attains the
nontrivial `gcd` branch, pinning the worst-case strata incidence to the gcd value. -/
theorem binomial_self_agree_card_eq_gcd
    {H : Subgroup Fˣ} [Fintype H] [IsCyclic H] [DecidableEq H]
    (c : Fˣ) {a b : ℕ} (hba : b < a) :
    (univ.filter fun x : H => c * (x : Fˣ) ^ a = c * (x : Fˣ) ^ b).card
      = Nat.gcd (a - b) (Fintype.card H) := by
  exact binomial_agree_card_eq_gcd_of_nonempty (H := H) c c hba (x₀ := 1) (by simp)

end Subgroup

end MultiplicativeRigidity

-- Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}):
-- #print axioms MultiplicativeRigidity.pow_map_card_eq_gcd_of_nonempty
-- #print axioms MultiplicativeRigidity.pow_one_eq_card_eq_gcd
#print axioms MultiplicativeRigidity.binomial_agree_card_eq_gcd_of_nonempty
#print axioms MultiplicativeRigidity.binomial_self_agree_card_eq_gcd
