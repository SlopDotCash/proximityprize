/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic

/-!
# The full depth-ℓ graded 2-adic tower on cyclotomic wraparound norms (#444)

This file generalizes the depth-1 parity gate (`_TwoAdicParityGate.lean`, `v_λ ≥ 1 ⟺ σ₀ even`) and the
depth-2 graded gate (`_TwoAdicGradedDepth2.lean`, `v_λ ≥ 2 ⟺ σ₀, σ₁ even`) to **arbitrary depth ℓ**.

**The tower.** Write `t := ζ − 1`, so `I = (λ) = (t)` and `ζ = 1 + t`. The exact binomial expansion
`ζ^a = (1 + t)^a = Σ_{j} C(a,j) t^j` truncates modulo `I^ℓ` to its first `ℓ` terms, because every tail term
`C(a,j) t^j` with `j ≥ ℓ` lies in `I^ℓ` (`t^j = t^ℓ·t^{j−ℓ}` and `t^ℓ ∈ I^ℓ`). Hence
```
        ζ^a ≡ Σ_{j<ℓ} C(a,j) t^j   (mod I^ℓ),
```
and summing signed, a wraparound `D = Σ_i ε_i·ζ^{a_i}` reduces to its **graded weight vector**
```
        D ≡ Σ_{j<ℓ} σ_j·t^j   (mod I^ℓ),     σ_j(D) := Σ_i ε_i·C(a_i, j).
```
So `D ∈ I^ℓ ⟺ Σ_{j<ℓ} σ_j·t^j ∈ I^ℓ`: the depth-ℓ gate is governed by the first ℓ integer moments
`σ₀, …, σ_{ℓ−1}` (each `σ_j ∈ ℤ`). This is the full 2-adic tower whose rungs `ℓ = 1, 2` were the previous
two files; `σ_0 = Σε_i` (signed weight), `σ_1 = Σε_i a_i` (signed first exponent-moment), `σ_2 = Σε_i C(a_i,2)`,…

**Exact-verified (probe `probe_twoadic_graded_depthL.py`).** Over all signed relations of support `2..4` at
`n = 8, 16` (35 600 enumerated, `D ≠ 0` over `ℂ`), the integer-criterion reading
`v_λ(D) ≥ ℓ ⟺ σ₀, …, σ_{ℓ−1} all even` holds for `ℓ = 1, 2, 3` with `0` violations and is **tight at every
rung**: partitioned by `(σ₀, σ₁, σ₂) mod 2`,
* `(0,0,0)`: `v_λ ≥ 3` (min 3, up to 12);
* `(0,0,1)`: `v_λ = 2` **exactly** (`σ₂·t²` is the depth-3 obstruction);
* `(0,1,·)`: `v_λ = 1` **exactly**;  `(1,·,·)`: `v_λ = 0`.
Each successive moment parity `σ_{ℓ−1}` is the precise obstruction to climbing from `I^{ℓ−1}` into `I^ℓ`.

**Honest scope.** This is **not** a proof of BGK / the prize, and not the full `v_λ ≥ ℓ` *integer* criterion
(turning `Σ σ_j t^j ∈ I^ℓ` into `σ_j ≡ 0 mod 2 ∀ j<ℓ` uses the specific local arithmetic of `ℤ[ζ_{2^μ}]`, here
only probe-verified at `ℓ ≤ 3`). What is proved axiom-clean is the **ring-theoretic graded tower congruence**
`D − Σ_{j<ℓ} σ_j·t^j ∈ I^ℓ` in any commutative ring, for every `ℓ`: the load-bearing algebra confining the
depth-ℓ obstruction to the first ℓ integer moments. The odd prize prime still reaches prize scale at `r ≈ 3`
(BGK wall); the tower sharpens the low-`r` vanishing exactly (`W_r = 0` for `r ≤ ℓ` ⟺ the depth-ℓ gate forces
`v_λ` high) but does not cross the wall.

**What this file proves (axiom-clean).**
* `pow_one_add_eq_binom_sum` — the closed form `(1+t)^a = Σ_{j≤a} C(a,j) t^j`.
* `tail_mem_idealPow` — `Σ_{j∈s, j≥ℓ} r_j·t^j ∈ I^ℓ` whenever `t ∈ I` (every high term is in `I^ℓ`).
* `pow_one_add_sub_truncation_mem` — `(1+t)^a − Σ_{j<ℓ} C(a,j) t^j ∈ I^ℓ` (the depth-ℓ truncation).
* `signedSum_sub_gradedTower_mem` — `D − Σ_{j<ℓ} σ_j·t^j ∈ I^ℓ` (the graded tower congruence; `D = Σ_i ε_i (1+t)^{a_i}`).
* `signedSum_mem_idealPow_iff_gradedTower` — the depth-ℓ gate biconditional. Issue #444.
-/

namespace ProximityGap.Frontier.TwoAdicGradedTower

open Finset

variable {ι R : Type*} [CommRing R]

/-- **Binomial closed form.** `(1 + t)^a = Σ_{j ∈ range (a+1)} C(a,j)·t^j`. (The exact expansion of `ζ^a`
with `t = ζ − 1`; obtained from `add_pow` by reflecting the index.) -/
theorem pow_one_add_eq_binom_sum (t : R) (a : ℕ) :
    (1 + t) ^ a = ∑ j ∈ range (a + 1), (a.choose j : R) * t ^ j := by
  rw [add_pow, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [mem_range] at hj
  have e1 : a + 1 - 1 - j = a - j := by omega
  have e3 : a - (a - j) = j := by omega
  rw [e1, one_pow, one_mul, Nat.choose_symm (by omega : j ≤ a), e3, mul_comm]

/-- **High terms lie in `I^ℓ`.** If `t ∈ I`, then any single term `r·t^j` with `ℓ ≤ j` is in `I^ℓ`
(`t^j = t^ℓ·t^{j−ℓ}`, `t^ℓ ∈ I^ℓ`). -/
theorem term_mem_idealPow (I : Ideal R) (t : R) (ht : t ∈ I) (ℓ j : ℕ) (hj : ℓ ≤ j) (r : R) :
    r * t ^ j ∈ I ^ ℓ := by
  have htl : t ^ ℓ ∈ I ^ ℓ := Ideal.pow_mem_pow ht ℓ
  have : t ^ j = t ^ ℓ * t ^ (j - ℓ) := by
    rw [← pow_add]; congr 1; omega
  rw [this, ← mul_assoc, mul_comm r, mul_assoc]
  exact Ideal.mul_mem_right _ _ htl

/-- **The tail is in `I^ℓ`.** A finite sum `Σ_{j ∈ s, ℓ ≤ j} r j · t^j` (the truncation tail) lies in `I^ℓ`. -/
theorem tail_mem_idealPow (I : Ideal R) (t : R) (ht : t ∈ I) (ℓ : ℕ) (s : Finset ℕ) (r : ℕ → R) :
    (∑ j ∈ s.filter (fun j => ℓ ≤ j), r j * t ^ j) ∈ I ^ ℓ := by
  refine Ideal.sum_mem _ (fun j hj => ?_)
  rw [mem_filter] at hj
  exact term_mem_idealPow I t ht ℓ j hj.2 (r j)

/-- **Depth-ℓ truncation.** For `t ∈ I`, `(1 + t)^a` agrees with its degree-`<ℓ` Taylor truncation modulo `I^ℓ`:
`(1 + t)^a − Σ_{j<ℓ} C(a,j)·t^j ∈ I^ℓ`. (The omitted terms `Σ_{ℓ ≤ j ≤ a} C(a,j) t^j` are the `I^ℓ` tail.) -/
theorem pow_one_add_sub_truncation_mem (I : Ideal R) (t : R) (ht : t ∈ I) (ℓ a : ℕ) :
    (1 + t) ^ a - ∑ j ∈ range ℓ, (a.choose j : R) * t ^ j ∈ I ^ ℓ := by
  rw [pow_one_add_eq_binom_sum t a]
  -- Σ_{range(a+1)} − Σ_{range ℓ} = (low overlap cancels) + tail. We split range(a+1) by the predicate ℓ ≤ j.
  set f : ℕ → R := fun j => (a.choose j : R) * t ^ j with hf
  have hsplit : (∑ j ∈ range (a + 1), f j)
      = (∑ j ∈ (range (a + 1)).filter (fun j => j < ℓ), f j)
        + (∑ j ∈ (range (a + 1)).filter (fun j => ℓ ≤ j), f j) := by
    rw [← Finset.sum_filter_add_sum_filter_not (range (a + 1)) (fun j => j < ℓ)]
    congr 1
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    apply Finset.filter_congr
    intro x _; simp [not_lt]
  rw [hsplit]
  -- The low part equals Σ_{range ℓ} f, because for a < j (< ℓ) we have C(a,j) = 0 ⟹ f j = 0.
  have hlow : (∑ j ∈ (range (a + 1)).filter (fun j => j < ℓ), f j)
      = ∑ j ∈ range ℓ, f j := by
    -- (range (a+1)).filter (·<ℓ) ⊆ range ℓ, and the missing terms (a < x < ℓ) have f = 0.
    -- sum_subset (s ⊆ t) (∀ x ∈ t, x ∉ s → f x = 0) : ∑ s = ∑ t.  s = filtered, t = range ℓ.
    refine Finset.sum_subset ?_ ?_
    · intro x hx
      rw [mem_filter, mem_range] at hx
      rw [mem_range]; exact hx.2
    · intro x hx hxnot
      rw [mem_range] at hx
      rw [mem_filter, mem_range] at hxnot
      -- x < ℓ (from hx) but x ∉ filtered ⟹ ¬(x < a+1) ⟹ a < x ⟹ C(a,x) = 0.
      have hax : a < x := by
        by_contra h
        exact hxnot ⟨by omega, hx⟩
      simp [hf, Nat.choose_eq_zero_of_lt hax]
  rw [hlow]
  -- Now goal: (Σ_{range ℓ} f) + tail − Σ_{range ℓ} f ∈ I^ℓ, i.e. tail ∈ I^ℓ.
  have hcancel : ((∑ j ∈ range ℓ, f j)
        + (∑ j ∈ (range (a + 1)).filter (fun j => ℓ ≤ j), f j))
      - ∑ j ∈ range ℓ, f j
      = ∑ j ∈ (range (a + 1)).filter (fun j => ℓ ≤ j), f j := by ring
  rw [hcancel]
  exact tail_mem_idealPow I t ht ℓ (range (a + 1)) (fun j => (a.choose j : R))

/-- **The graded tower congruence.** With `t ∈ I` and `D = Σ_{i∈s} ε_i·(1+t)^{a_i}`, the wraparound reduces to
its graded weight vector modulo `I^ℓ`:
```
    D − Σ_{j<ℓ} σ_j·t^j ∈ I^ℓ,      σ_j := Σ_{i∈s} ε_i·C(a_i, j).
```
Proof: sum the per-term truncations `(1+t)^{a_i} − Σ_{j<ℓ} C(a_i,j) t^j ∈ I^ℓ`, then commute the finite double
sum (`Σ_i ε_i Σ_{j<ℓ} C(a_i,j) t^j = Σ_{j<ℓ} (Σ_i ε_i C(a_i,j)) t^j = Σ_{j<ℓ} σ_j t^j`). -/
theorem signedSum_sub_gradedTower_mem (I : Ideal R) (t : R) (ht : t ∈ I) (ℓ : ℕ)
    (s : Finset ι) (c : ι → R) (a : ι → ℕ) :
    (∑ i ∈ s, c i * (1 + t) ^ (a i))
      - ∑ j ∈ range ℓ, (∑ i ∈ s, c i * ((a i).choose j : R)) * t ^ j ∈ I ^ ℓ := by
  -- Rewrite the graded-weight sum as a double sum over i then j.
  have hgrad : (∑ j ∈ range ℓ, (∑ i ∈ s, c i * ((a i).choose j : R)) * t ^ j)
      = ∑ i ∈ s, c i * (∑ j ∈ range ℓ, ((a i).choose j : R) * t ^ j) := by
    -- push t^j inside the i-sum, swap the two sums, then collect c i.
    have step1 : (∑ j ∈ range ℓ, (∑ i ∈ s, c i * ((a i).choose j : R)) * t ^ j)
        = ∑ j ∈ range ℓ, ∑ i ∈ s, c i * (((a i).choose j : R) * t ^ j) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [step1, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
  rw [hgrad, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ (fun i _ => ?_)
  have hmul : c i * (1 + t) ^ (a i) - c i * (∑ j ∈ range ℓ, ((a i).choose j : R) * t ^ j)
      = c i * ((1 + t) ^ (a i) - ∑ j ∈ range ℓ, ((a i).choose j : R) * t ^ j) := by ring
  rw [hmul]
  exact Ideal.mul_mem_left _ _ (pow_one_add_sub_truncation_mem I t ht ℓ (a i))

/-- **The depth-ℓ gate biconditional.** With `t ∈ I` and `D = Σ ε_i·(1+t)^{a_i}`, membership in `I^ℓ` is
governed by the graded weight vector: `D ∈ I^ℓ ⟺ Σ_{j<ℓ} σ_j·t^j ∈ I^ℓ`, where `σ_j = Σ_i ε_i·C(a_i,j)`. For
`I = (λ)` this is the full 2-adic tower `λ^ℓ ∣ D ⟺ λ^ℓ ∣ Σ_{j<ℓ} σ_j·(ζ−1)^j`; the rungs `ℓ = 1, 2` recover the
parity gate and the depth-2 graded gate. (Probe-verified integer reading `v_λ(D) ≥ ℓ ⟺ σ_0,…,σ_{ℓ−1} even`,
tight, for `ℓ ≤ 3`.) -/
theorem signedSum_mem_idealPow_iff_gradedTower (I : Ideal R) (t : R) (ht : t ∈ I) (ℓ : ℕ)
    (s : Finset ι) (c : ι → R) (a : ι → ℕ) :
    (∑ i ∈ s, c i * (1 + t) ^ (a i)) ∈ I ^ ℓ
      ↔ (∑ j ∈ range ℓ, (∑ i ∈ s, c i * ((a i).choose j : R)) * t ^ j) ∈ I ^ ℓ := by
  have h := signedSum_sub_gradedTower_mem I t ht ℓ s c a
  set D := ∑ i ∈ s, c i * (1 + t) ^ (a i) with hD
  set G := ∑ j ∈ range ℓ, (∑ i ∈ s, c i * ((a i).choose j : R)) * t ^ j with hG
  constructor
  · intro hDmem
    have : G = D - (D - G) := by ring
    rw [this]; exact (I ^ ℓ).sub_mem hDmem h
  · intro hGmem
    have : D = G + (D - G) := by ring
    rw [this]; exact (I ^ ℓ).add_mem hGmem h

end ProximityGap.Frontier.TwoAdicGradedTower

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.TwoAdicGradedTower.pow_one_add_eq_binom_sum
#print axioms ProximityGap.Frontier.TwoAdicGradedTower.term_mem_idealPow
#print axioms ProximityGap.Frontier.TwoAdicGradedTower.tail_mem_idealPow
#print axioms ProximityGap.Frontier.TwoAdicGradedTower.pow_one_add_sub_truncation_mem
#print axioms ProximityGap.Frontier.TwoAdicGradedTower.signedSum_sub_gradedTower_mem
#print axioms ProximityGap.Frontier.TwoAdicGradedTower.signedSum_mem_idealPow_iff_gradedTower
