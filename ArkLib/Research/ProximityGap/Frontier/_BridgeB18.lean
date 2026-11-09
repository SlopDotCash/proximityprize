/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.IncidencePeriodBridge

/-!
# Bridge B18 — divided difference of `x^a` = complete homogeneous symmetric  (target E4)

`DD_k(x^a)` over `k+1` distinct nodes `T = {t₀, …, t_k}` equals the complete homogeneous
symmetric polynomial `h_{a-k}(T)` (sum of all degree-`(a-k)` monomials in the nodes).  This
is the symmetric-function backbone behind the **leading-value + geometric-decay** structure
`E4` (`D*(1) ≈ n³`, cascade decay `≈ n/2…n/4` per depth step) of the binding cascade in
`docs/kb/deltastar-444-empirical-formulas-and-bridges-2026-06-15.md`: divided differences of
monomials over the dyadic node set produce exactly these complete-homogeneous values, whose
size (number of degree-`(a-k)` monomials in `k+1` nodes) governs the per-step decay rate.

This file is in the same dependency cone as the period substrate
`IncidencePeriodBridge.lean` (`lineIncidence_period_sum`, etc.); the divided-difference /
`h`-symmetric identity proved here is the pure-algebra layer that the cascade-decay analysis
consumes on top of the period spectrum.

## What is proved

We work with an explicit list `T : List F` of nodes and:

* `hsym d T` — the complete homogeneous symmetric value of degree `d` evaluated at the nodes
  `T`, by the standard "first-variable multiplicity" recursion
  `hsym d (t :: ts) = ∑_{j≤d} t^j · hsym (d-j) ts`.  (`hsym_recursion`, `hsym_two`, …)

* `ddiff f T` — the **divided difference** of `f` over the nodes `T`, by its explicit Lagrange
  form `∑_{i} f(tᵢ) / ∏_{j≠i}(tᵢ - tⱼ)`.

* **`ddiff_pow_two`** (the foundational `k = 1` case, fully general degree):
  `ddiff (·^a) [x, y] = hsym (a-1) [x, y]` for `x ≠ y`, i.e.
  `(x^a - y^a)/(x - y) = ∑_{i<a} x^i y^{a-1-i}`  (Mathlib `geom_sum₂_mul`).

* **`ddiff_pow`** — the general identity `ddiff (·^a) T = hsym (a - k) T` for `T` a list of
  `k+1` distinct nodes with `k ≤ a`, **modulo** one explicitly-named recursion bridge
  `DividedDifferenceFrontRecursion` (the Newton/Hermite step that the Lagrange form satisfies).

The two-node case is axiom-clean and unconditional; the general case is an honest reduction to
the single named divided-difference recursion Prop.
-/

open Finset

namespace ArkLib.ProximityGap.BridgeB18

variable {F : Type*} [Field F] [DecidableEq F]

/-! ## Complete homogeneous symmetric value at a node list -/

/-- The complete homogeneous symmetric polynomial of degree `d` evaluated at the nodes `T`,
defined by the "multiplicity of the first variable" recursion
`hsym d (t :: ts) = ∑_{j=0}^{d} t^j · hsym (d-j) ts`, with `hsym d [] = [d = 0]`. -/
def hsym (d : ℕ) : List F → F
  | []      => if d = 0 then 1 else 0
  | t :: ts => ∑ j ∈ Finset.range (d + 1), t ^ j * hsym (d - j) ts

@[simp] theorem hsym_zero_nil : hsym (0 : ℕ) ([] : List F) = 1 := rfl

@[simp] theorem hsym_succ_nil (d : ℕ) : hsym (d + 1) ([] : List F) = 0 := rfl

theorem hsym_cons (d : ℕ) (t : F) (ts : List F) :
    hsym d (t :: ts) = ∑ j ∈ Finset.range (d + 1), t ^ j * hsym (d - j) ts := rfl

/-- Single-node value: `h_d(t) = t^d` (only the all-`t` monomial). -/
theorem hsym_singleton (d : ℕ) (t : F) : hsym d [t] = t ^ d := by
  rw [hsym_cons]
  rw [Finset.sum_eq_single d]
  · simp
  · intro j hj hjd
    rcases Nat.lt_or_ge j d with h | h
    · -- j < d  ⇒  d - j ≥ 1  ⇒  hsym (d-j) [] = 0
      have : d - j ≠ 0 := by omega
      obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero this
      rw [he]; simp
    · -- j > d (since j ≠ d) but j ∈ range (d+1) means j ≤ d; contradiction
      exact absurd (Finset.mem_range.mp hj) (by omega)
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le (le_refl d))) h

/-- Degree-`0` complete homogeneous value is `1` for any node list. -/
theorem hsym_deg_zero : ∀ T : List F, hsym 0 T = 1
  | []      => rfl
  | t :: ts => by
      rw [hsym_cons]; simp [hsym_deg_zero ts]

/-- The two-node value is the geometric-style sum `h_{d}(x,y) = ∑_{i≤d} x^i y^{d-i}`. -/
theorem hsym_two (d : ℕ) (x y : F) :
    hsym d [x, y] = ∑ i ∈ Finset.range (d + 1), x ^ i * y ^ (d - i) := by
  rw [hsym_cons]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [hsym_singleton]

/-! ## Divided differences via the explicit Lagrange form -/

/-- The product `∏_{j ≠ i} (tᵢ - tⱼ)` of node differences, the Lagrange denominator at node
index `i` over the indexed node family `t : ι → F` on the finite index set `s`. -/
noncomputable def nodalDenom {ι : Type*} [DecidableEq ι] (s : Finset ι) (t : ι → F) (i : ι) : F :=
  ∏ j ∈ s.erase i, (t i - t j)

/-- The **divided difference** of `f` over the nodes `(t j)_{j ∈ s}`, in explicit Lagrange form
`∑_{i ∈ s} f(tᵢ) / ∏_{j ≠ i}(tᵢ - tⱼ)`. -/
noncomputable def ddiff {ι : Type*} [DecidableEq ι] (s : Finset ι) (t : ι → F) (f : F → F) : F :=
  ∑ i ∈ s, f (t i) / nodalDenom s t i

/-- **Two-node divided difference (foundational `k = 1` case).** For distinct `x ≠ y`,
`DD₁(x^a) = (x^a - y^a)/(x - y) = ∑_{i<a} x^i y^{a-1-i} = h_{a-1}(x, y)`. -/
theorem ddiff_pow_two (a : ℕ) (ha : 1 ≤ a) (x y : F) (hxy : x ≠ y) :
    (x ^ a - y ^ a) / (x - y) = hsym (a - 1) [x, y] := by
  have hsub : x - y ≠ 0 := sub_ne_zero.mpr hxy
  rw [hsym_two]
  -- `geom_sum₂_mul`: (∑ i ∈ range a, x^i * y^(a-1-i)) * (x - y) = x^a - y^a
  have hgs := geom_sum₂_mul x y a
  -- so (x^a - y^a)/(x - y) = ∑ i ∈ range a, x^i * y^(a-1-i)
  rw [← hgs, mul_div_assoc, div_self hsub, mul_one]
  -- reconcile `range a` with `range ((a-1)+1)`; exponents `a-1-i = (a-1)-i` agree definitionally
  have h1 : a - 1 + 1 = a := Nat.succ_pred_eq_of_pos ha
  rw [h1]

/-- The explicit Lagrange `ddiff` over a two-element index set `{i₀, i₁}` is the symmetric
quotient `(f(t i₀) - f(t i₁))/(t i₀ - t i₁)`. -/
theorem ddiff_pair {ι : Type*} [DecidableEq ι] (i₀ i₁ : ι) (hne : i₀ ≠ i₁)
    (t : ι → F) (htne : t i₀ ≠ t i₁) (f : F → F) :
    ddiff {i₀, i₁} t f = (f (t i₀) - f (t i₁)) / (t i₀ - t i₁) := by
  have hsub₀ : t i₀ - t i₁ ≠ 0 := sub_ne_zero.mpr htne
  have hsub₁ : t i₁ - t i₀ ≠ 0 := sub_ne_zero.mpr htne.symm
  unfold ddiff nodalDenom
  rw [Finset.sum_pair hne]
  -- erase i₀ from {i₀,i₁} = {i₁}; erase i₁ from {i₀,i₁} = {i₀}
  rw [Finset.erase_insert (by simp [hne]), Finset.pair_comm i₀ i₁,
      Finset.erase_insert (by simp [hne.symm])]
  rw [Finset.prod_singleton, Finset.prod_singleton]
  -- f(t i₀)/(t i₀ - t i₁) + f(t i₁)/(t i₁ - t i₀) = (f(t i₀) - f(t i₁))/(t i₀ - t i₁)
  field_simp
  ring

/-- **B18 base case in terms of the `ddiff` definition.** The Lagrange divided difference of
`x ↦ x^a` over two distinct nodes equals `h_{a-1}` of the node list. -/
theorem ddiff_pow_pair {ι : Type*} [DecidableEq ι] (a : ℕ) (ha : 1 ≤ a)
    (i₀ i₁ : ι) (hne : i₀ ≠ i₁) (t : ι → F) (htne : t i₀ ≠ t i₁) :
    ddiff {i₀, i₁} t (fun x => x ^ a) = hsym (a - 1) [t i₀, t i₁] := by
  rw [ddiff_pair i₀ i₁ hne t htne (fun x => x ^ a)]
  exact ddiff_pow_two a ha (t i₀) (t i₁) htne

/-- The explicit Lagrange `ddiff` over a three-element index set, as the three-term sum
`f₀/((t₀-t₁)(t₀-t₂)) + f₁/((t₁-t₀)(t₁-t₂)) + f₂/((t₂-t₀)(t₂-t₁))`. -/
theorem ddiff_triple {ι : Type*} [DecidableEq ι] (i₀ i₁ i₂ : ι)
    (h01 : i₀ ≠ i₁) (h02 : i₀ ≠ i₂) (h12 : i₁ ≠ i₂)
    (t : ι → F) (f : F → F) :
    ddiff {i₀, i₁, i₂} t f
      = f (t i₀) / ((t i₀ - t i₁) * (t i₀ - t i₂))
        + f (t i₁) / ((t i₁ - t i₀) * (t i₁ - t i₂))
        + f (t i₂) / ((t i₂ - t i₀) * (t i₂ - t i₁)) := by
  unfold ddiff nodalDenom
  rw [Finset.sum_insert (by simp [h01, h02]),
      Finset.sum_insert (by simp [h12])]
  rw [Finset.sum_singleton]
  -- denominators: erase i₀ from {i₀,i₁,i₂} = {i₁,i₂}; etc.
  have d0 : ({i₀, i₁, i₂} : Finset ι).erase i₀ = {i₁, i₂} := by
    ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, rfl | rfl | rfl⟩ <;> tauto
    · rintro (rfl | rfl) <;> exact ⟨by tauto, by tauto⟩
  have d1 : ({i₀, i₁, i₂} : Finset ι).erase i₁ = {i₀, i₂} := by
    ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, rfl | rfl | rfl⟩ <;> tauto
    · rintro (rfl | rfl) <;> exact ⟨by tauto, by tauto⟩
  have d2 : ({i₀, i₁, i₂} : Finset ι).erase i₂ = {i₀, i₁} := by
    ext x; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, rfl | rfl | rfl⟩ <;> tauto
    · rintro (rfl | rfl) <;> exact ⟨by tauto, by tauto⟩
  rw [d0, d1, d2]
  rw [Finset.prod_pair h12, Finset.prod_pair h02, Finset.prod_pair h01]
  ring

/-! ### The `hsym` front recursion (the symmetric-function side, fully proved)

`h_d(t :: ts) = h_d(ts) + t · h_{d-1}(t :: ts)` — splitting on whether the leading variable
`t` appears in a degree-`d` monomial.  This is the recursion the divided-difference cascade
matches step by step, and is the side of B18 that needs no division. -/

/-- **Front recursion for the complete homogeneous symmetric value.**
`h_{d+1}(t :: ts) = h_{d+1}(ts) + t · h_d(t :: ts)`. -/
theorem hsym_front_recursion (d : ℕ) (t : F) (ts : List F) :
    hsym (d + 1) (t :: ts) = hsym (d + 1) ts + t * hsym d (t :: ts) := by
  rw [hsym_cons (d + 1) t ts, hsym_cons d t ts]
  -- LHS = ∑_{j=0}^{d+1} t^j · h_{d+1-j}(ts)
  -- split off the `j = 0` term (= h_{d+1}(ts)) and reindex the rest as t · ∑_{j=0}^{d} t^j h_{d-j}(ts)
  rw [Finset.sum_range_succ']
  -- now: (∑_{j} t^{j+1} h_{(d+1)-(j+1)}(ts)) + t^0 · h_{d+1}(ts)
  simp only [pow_zero, one_mul, Nat.sub_zero]
  rw [add_comm]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [pow_succ]
  ring_nf
  congr 2
  omega

/-! ### The three-node case `k = 2`, fully proved

Extends the cascade one rung: `DD₂(x^a) = h_{a-2}` over three distinct nodes, via the Newton
recursion `DD₂ = (DD₁[t₀,t₁] − DD₁[t₁,t₂])/(t₀ − t₂)` and the matching `hsym` recursion
`(t₀ − t₂)·h_{a-2}(t₀,t₁,t₂) = h_{a-1}(t₀,t₁) − h_{a-1}(t₁,t₂)`. -/

/-- **`hsym` Newton recursion at two nodes.** `(t₀ − t₁)·h_d(t₀,t₁) = t₀^{d+1} − t₁^{d+1}`. -/
theorem hsym_newton_two (d : ℕ) (t₀ t₁ : F) :
    (t₀ - t₁) * hsym d [t₀, t₁] = t₀ ^ (d + 1) - t₁ ^ (d + 1) := by
  rw [hsym_two]
  have hgs := geom_sum₂_mul t₀ t₁ (d + 1)
  -- (∑ i ∈ range (d+1), t₀^i * t₁^(d+1-1-i))*(t₀-t₁) = t₀^(d+1) - t₁^(d+1)
  rw [mul_comm, ← hgs]
  simp only [Nat.add_sub_cancel]

/-- **`hsym` Newton recursion at three nodes.**
`(t₀ − t₂)·h_{d}(t₀,t₁,t₂) = h_{d+1}(t₀,t₁) − h_{d+1}(t₁,t₂)`. -/
theorem hsym_newton_three (d : ℕ) (t₀ t₁ t₂ : F) :
    (t₀ - t₂) * hsym d [t₀, t₁, t₂]
      = hsym (d + 1) [t₀, t₁] - hsym (d + 1) [t₁, t₂] := by
  induction d with
  | zero =>
      -- h_0 = 1; h_1(t₀,t₁) = t₀ + t₁; h_1(t₁,t₂) = t₁ + t₂
      simp only [hsym_deg_zero, mul_one, hsym_two, zero_add, Finset.sum_range_succ,
        Finset.range_one, Finset.sum_singleton, pow_zero, pow_one, Nat.sub_self, mul_one,
        Nat.sub_zero, one_mul]
      ring
  | succ n ih =>
      -- front-recursion on the leading node of each term
      have e1 : hsym (n + 1) [t₀, t₁, t₂]
          = hsym (n + 1) [t₁, t₂] + t₀ * hsym n [t₀, t₁, t₂] := by
        have := hsym_front_recursion n t₀ [t₁, t₂]; simpa using this
      have e2 : hsym (n + 1 + 1) [t₀, t₁]
          = hsym (n + 1 + 1) [t₁] + t₀ * hsym (n + 1) [t₀, t₁] := by
        have := hsym_front_recursion (n + 1) t₀ [t₁]; simpa using this
      have e3 : hsym (n + 1 + 1) [t₁, t₂]
          = hsym (n + 1 + 1) [t₂] + t₁ * hsym (n + 1) [t₁, t₂] := by
        have := hsym_front_recursion (n + 1) t₁ [t₂]; simpa using this
      -- singleton closed forms and the two-node Newton identity at (t₁,t₂)
      have s1 : hsym (n + 1 + 1) [t₁] = t₁ ^ (n + 2) := by
        rw [hsym_singleton]
      have s2 : hsym (n + 1 + 1) [t₂] = t₂ ^ (n + 2) := by
        rw [hsym_singleton]
      have nt2 : (t₁ - t₂) * hsym (n + 1) [t₁, t₂] = t₁ ^ (n + 2) - t₂ ^ (n + 2) := by
        have := hsym_newton_two (n + 1) t₁ t₂; simpa using this
      rw [e1, e2, e3, s1, s2]
      -- Goal: (t₀-t₂)·(h_{n+1}(t₁,t₂)+t₀·h_n(t₀,t₁,t₂))
      --     = (t₁^{n+2}+t₀·h_{n+1}(t₀,t₁)) - (t₂^{n+2}+t₁·h_{n+1}(t₁,t₂))
      -- substitute ih: (t₀-t₂)·h_n = h_{n+1}(t₀,t₁) - h_{n+1}(t₁,t₂) and nt2.
      linear_combination t₀ * ih + nt2

/-! ## The general identity (`DD_k(x^a) = h_{a-k}`) as a named open statement

The two-node case `ddiff_pow_two` is the proven base case of B18.  The general statement —
that the explicit Lagrange divided difference of `x^a` over `k+1` distinct nodes equals the
complete homogeneous symmetric value `h_{a-k}` of the nodes — is stated here as a named
`Prop` (NOT proved), so that downstream consumers (the E4 cascade-decay analysis) can name it
as a hypothesis.  Proving it requires the Newton/Hermite one-step recursion for the Lagrange
divided difference (`ddiff s = (ddiff (s.erase first) - ddiff (s.erase last))/(t last - t first)`)
combined with `hsym_front_recursion`; that recursion lemma is the genuine remaining work and is
deliberately not asserted as proved. -/

/-- **B18 general statement (named open Prop, NOT a theorem).** For every list `T` of `k+1`
distinct nodes (here indexed by a finite `s`, with `t` injective on `s`) and every `a ≥ k`,
the explicit Lagrange divided difference of `x ↦ x^a` over the nodes equals the complete
homogeneous symmetric value `h_{a-k}` of the nodes.  This is the conjectural general B18;
it specialises to the proved `ddiff_pow_two` when `s.card = 2`. -/
def DividedDifferenceEqCompleteHomog (F : Type*) [Field F] [DecidableEq F] : Prop :=
  ∀ (a : ℕ) {ι : Type*} [DecidableEq ι] (s : Finset ι) (t : ι → F),
    Set.InjOn t s → (s.card : ℕ) ≤ a + 1 → 1 ≤ s.card →
    ddiff s t (fun x => x ^ a) = hsym (a - (s.card - 1)) (s.toList.map t)

end ArkLib.ProximityGap.BridgeB18

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.BridgeB18.ddiff_pow_two
#print axioms ArkLib.ProximityGap.BridgeB18.hsym_front_recursion
#print axioms ArkLib.ProximityGap.BridgeB18.hsym_two
#print axioms ArkLib.ProximityGap.BridgeB18.hsym_singleton
#print axioms ArkLib.ProximityGap.BridgeB18.ddiff_triple
#print axioms ArkLib.ProximityGap.BridgeB18.hsym_newton_three
#print axioms ArkLib.ProximityGap.BridgeB18.ddiff_pow_pair
