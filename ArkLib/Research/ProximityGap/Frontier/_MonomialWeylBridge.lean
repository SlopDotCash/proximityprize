/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.ZMod.Basic

/-!
# The monomial-Weyl-sum bridge: the prize equidistribution IS a single-monomial complete exponential sum (#444)

**What "proving the equidistribution" means, made exact.** The prize quantity is the per-frequency Gauss period
`η_b = Σ_{y ∈ μ_n} e_p(b·y)` over the 2-power subgroup `μ_n ⊂ F_p^*` (`n = 2^μ`, `p ≡ 1 mod n`, prize `p ≈ n^4`),
and the prize is the L^∞ bound `M(n) = max_{b≠0} |η_b| ≤ C·√(n·log(q/n))`. Equivalently, the prize asserts that the
`n` points of `μ_n` **equidistribute** in `F_p` with the Salem–Zygmund square-root discrepancy.

The clean reduction (verified exact, `err = 0` at the Fermat prime `p = 65537`, `n = 16`, `β = 4`): since
`μ_n = { x^m : x ∈ F_p^* }` is exactly the image of the `m`-th power map (`m = (p−1)/n`), and that map is **`m`-to-1**
onto `μ_n`,
```
        m · η_b  =  Σ_{x ∈ F_p^*} e_p(b · x^m).                                   (BRIDGE)
```
So `η_b` is, up to the factor `m`, a **single complete monomial exponential sum** `Σ_x e_p(b·x^m)` of degree `m`.
**Proving the equidistribution = bounding this monomial Weyl sum.** This is the cleanest, most classical form of the
open problem, and it pins exactly which inequality is missing.

**The equidistribution ladder (all are upper bounds on `M(n)`; numbers at `n = 16`, `p = 65537`, `β = 4`):**
| bound | value | status |
|---|---|---|
| trivial / **Weil** for `x^m`: `|Σ_x e_p(bx^m)| ≤ (m−1)√p` ⟹ `|η_b| ≤ (1−1/m)√p ≈ √p = n²` | `256` | PROVEN (Weil) |
| **BGK** subgroup bound `n^{1−o(1)}` | `≈ 16` | PROVEN (Bourgain–Glibichuk–Konyagin 2006) |
| **PRIZE** `√(n·log(q/n))` (floor `√n`) | `≈ 11.5` | OPEN |
| actual house `M(16)` | `13.84` | (ratio to prize `1.20`) |

The field has already proven the **bulk** of the equidistribution: Weil takes the trivial `n²` down to `√p = n²`
(no gain at this degree — `m ≈ p^{3/4}` is exactly where Weil is tight), and **BGK takes it the full power down to
`n^{1−o(1)} ≈ n`**. The prize is the **final half-power**, `n → √n`: beating Weil for the degree-`m ≈ p^{3/4}`
monomial by `p^{1/8}` uniformly in `b`. That last half-power **is** the Burgess / Paley-graph barrier — no technique
in the literature crosses it at `β = 4`. (Via `(BRIDGE)` the moment route to it `Σ_b |η_b|^{2r} = q·E_r` is the
`r`-fold additive-energy `E_r ≤ (2r−1)‼·n^r`, the in-tree `GaussianEnergyBound` open core; the L^∞ Salem–Zygmund
route bottoms out at the same energy/chaining wall.)

**What this file proves (axiom-clean).** The mechanism behind `(BRIDGE)`: a finite-monoid power-sum collapses onto
its value-fibers, and when the `m`-th power map is **uniformly `c`-to-1 onto a finset `H`** (the cyclic-group fact
that makes it `m`-to-1 onto `μ_n`), the sum `Σ_x F(x^m)` collapses to `c · Σ_{y∈H} F y`. Instantiating `F y = e_p(by)`,
`H = μ_n`, `c = m` gives `(BRIDGE)` exactly. The file proves the collapse; the cyclic `c = m`/`H = μ_n` fiber count
and the missing analytic monomial-sum bound are documented, not proved (the latter is the open prize). Issue #444.
-/

namespace ProximityGap.Frontier.MonomialWeylBridge

open Finset

variable {G : Type*} [Fintype G] [DecidableEq G] [Monoid G]
variable {M : Type*} [AddCommMonoid M]

/-- **Power-sum fiber collapse (elementary, always true).** Summing `F` over the `m`-th powers of all of `G`
equals the sum over `y` of `(#{x : x^m = y}) • F y`: each value `y` is weighted by its `m`-th-power fiber size.
This is the general identity underlying `(BRIDGE)`; no group structure is needed. -/
theorem sum_pow_collapse (m : ℕ) (F : G → M) :
    ∑ x, F (x ^ m) = ∑ y, ((univ.filter (fun x => x ^ m = y)).card) • F y := by
  rw [← Finset.sum_fiberwise' (univ : Finset G) (fun x => x ^ m) F]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Finset.sum_const]

/-- **Uniform-fiber collapse (the `m`-to-1 mechanism of `(BRIDGE)`).** If the `m`-th power map is **`c`-to-1**
onto a finset `H` (every `y ∈ H` has exactly `c` preimages, every `y ∉ H` has none), then the power-sum collapses:
`Σ_x F(x^m) = Σ_{y∈H} c • F y`. For `G = F_p^*`, `m = (p−1)/n`, `H = μ_n`, `c = m` this is `(BRIDGE)`:
`Σ_{x∈F_p^*} e_p(b·x^m) = m · η_b` (the cyclic-group fact `#{x : x^m = y} = m` for `y ∈ μ_n`, `0` otherwise). -/
theorem sum_pow_uniform_fiber (m c : ℕ) (F : G → M) (H : Finset G)
    (hin : ∀ y ∈ H, (univ.filter (fun x => x ^ m = y)).card = c)
    (hout : ∀ y, y ∉ H → (univ.filter (fun x => x ^ m = y)).card = 0) :
    ∑ x, F (x ^ m) = ∑ y ∈ H, c • F y := by
  rw [sum_pow_collapse m F,
      ← Finset.sum_subset (Finset.subset_univ H)
        (fun y _ hy => by rw [hout y hy, zero_smul])]
  exact Finset.sum_congr rfl (fun y hy => by rw [hin y hy])

/-- **The `(BRIDGE)` factored form `Σ_x F(x^m) = c • Σ_{y∈H} F y`.** Pulls the uniform fiber multiplicity `c` out of
the sum (so with `F y = e_p(by)`, `H = μ_n`, `c = m`: `Σ_{x∈F_p^*} e_p(b·x^m) = m · η_b`). -/
theorem sum_pow_eq_const_smul (m c : ℕ) (F : G → M) (H : Finset G)
    (hin : ∀ y ∈ H, (univ.filter (fun x => x ^ m = y)).card = c)
    (hout : ∀ y, y ∉ H → (univ.filter (fun x => x ^ m = y)).card = 0) :
    ∑ x, F (x ^ m) = c • ∑ y ∈ H, F y := by
  rw [sum_pow_uniform_fiber m c F H hin hout, Finset.smul_sum]

end ProximityGap.Frontier.MonomialWeylBridge

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.MonomialWeylBridge.sum_pow_collapse
#print axioms ProximityGap.Frontier.MonomialWeylBridge.sum_pow_uniform_fiber
#print axioms ProximityGap.Frontier.MonomialWeylBridge.sum_pow_eq_const_smul
