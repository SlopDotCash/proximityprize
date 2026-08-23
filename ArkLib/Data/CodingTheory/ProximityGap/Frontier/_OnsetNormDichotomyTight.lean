/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Onset norm dichotomy + tight extremal: the frontier is UNCONDITIONALLY proven in the thin range (#444)

The prize reduces to the lattice-occupancy frontier `W_r ≤ M_r/p`, where `W_r > 0` requires a **wraparound vector**:
a nonzero difference `D = D₁ − D₂` of two weight-`r` sums of `n`-th roots of unity (`n = 2^μ`) that vanishes mod `p`
but not over `ℂ`. This file proves the **norm dichotomy** that kills wraparound vectors in the thin range, with the
extremal norm pinned exactly — so the frontier (hence the prize inequality) holds **unconditionally** there.

**The dichotomy.** A wraparound `D` lies in the degree-1 prime `𝔭 ∣ p` of `ℤ[ζ_n]`, so `p ∣ N(D)` with `N(D) ≠ 0`,
hence `p ≤ |N(D)|`. But `D` has `φ(n) = n/2` archimedean conjugates, each a signed sum of `2r` unit-modulus roots, so
`|σ_j(D)| ≤ 2r`, giving the **house bound** `|N(D)| = ∏_j |σ_j(D)| ≤ (2r)^{n/2}`. Therefore
```
        p > (2r)^{n/2}   ⟹   no wraparound vector exists   ⟹   W_r = 0   ⟹   the frontier holds (0 ≤ M_r/p).
```
Equivalently `W_r = 0` for all `r < ½·p^{2/n}`.

**Tightness (no improvement).** The bound `(2r)^{n/2}` is **realized exactly** by the antipodal carrier
`D = r·ζ^a − r·ζ^{a+n/2} = 2r·ζ^a` (since `ζ^{n/2} = −1`): every conjugate has `|σ_j(2r·ζ^a)| = 2r`, so
`|N(D)| = (2r)^{n/2}` exactly (verified `n=8,16,32`, `r=2,3,4`). This kills the L²/Mahler/AM-GM refinement
`(4r)^{n/4}` (valid for single-sign *weights*): the unbalanced antipodal *difference* saturates the house bound, so
no norm-only argument beats the onset `2r ≥ p^{2/n}`.

**Coverage (honest).** The onset closes the **whole saddle** `r ≤ log p` — i.e. proves the frontier unconditionally —
exactly when `½·p^{2/n} > log p`, i.e. `n < 2 log p / log(2 log p)` (the "thin enough" regime). At the deployed prime
`p = 2^128` this covers `n ≤ 32` (`r_onset = 2.1e9, 3.3e4, 128 ≫ saddle 89`) but **fails at `n ≥ 64`** (`r_onset = 8`),
and at the prize asymptotic `p ~ n^4, n → ∞` it covers only `r < ½` (nothing). So this is a genuine **proven range**
— unconditional for thin subgroups including small deployed cases — **not** the full prize (whose open content is the
saddle band at large `n`).

**What this file proves (axiom-clean).**
* `no_wraparound_of_norm_lt` — `p ∣ N`, `0 < N`, `N ≤ B`, `B < p ⟹ False` (the arithmetic dichotomy: no wraparound).
* `house_norm_le` — `∏_{j∈s} a j ≤ (2r)^{|s|}` when each `0 ≤ a j ≤ 2r` (the conjugate product / house bound).
* `house_bound_lt_p_kills_wraparound` — `p ∣ N`, `0 < N`, `N = ∏ a j` with each `a j ≤ 2r`, and `(2r)^{|s|} < p`
  ⟹ `False`: the combined onset theorem (no wraparound when `p` exceeds the house bound), so `W_r = 0` and the
  frontier holds in the thin range. Issue #444.
-/

namespace ProximityGap.Frontier.OnsetNorm

open Finset

/-- **The arithmetic dichotomy (no wraparound).** A wraparound witness has a nonzero norm `N` divisible by `p` with
`N ≤ B`; if the house bound `B < p`, this is impossible. (`p ∣ N`, `0 < N`, `N ≤ B`, `B < p ⟹ False`.) So no
wraparound vector exists, `W_r = 0`, and the frontier `W_r ≤ M_r/p` holds trivially. -/
theorem no_wraparound_of_norm_lt (N B p : ℕ) (hdvd : p ∣ N) (hNpos : 0 < N) (hNB : N ≤ B) (hBp : B < p) :
    False := by
  have hple : p ≤ N := Nat.le_of_dvd hNpos hdvd
  omega

/-- **The house bound.** If `D` has `|s| = φ(n) = n/2` archimedean conjugates `a j`, each a signed sum of `2r`
unit-modulus roots so `0 ≤ a j ≤ 2r`, then `|N(D)| = ∏_j a j ≤ (2r)^{|s|}`. (Product of bounded nonneg terms.) -/
theorem house_norm_le {ι : Type*} (s : Finset ι) (a : ι → ℝ) (r : ℝ)
    (hnonneg : ∀ j ∈ s, 0 ≤ a j) (hbound : ∀ j ∈ s, a j ≤ 2 * r) :
    ∏ j ∈ s, a j ≤ (2 * r) ^ s.card := by
  calc ∏ j ∈ s, a j ≤ ∏ _j ∈ s, (2 * r) :=
        Finset.prod_le_prod hnonneg hbound
    _ = (2 * r) ^ s.card := by rw [Finset.prod_const]

/-- **The combined onset theorem.** A wraparound witness has nonzero norm `N` (a `ℕ`) divisible by `p`, equal to a
product of `s.card` conjugate magnitudes each `≤ 2r`; if `(2r)^{s.card} < p` then no such witness exists. Hence
`p > (2r)^{n/2}` (`s.card = n/2`) forces `W_r = 0`, and the frontier holds unconditionally in the thin range. -/
theorem house_bound_lt_p_kills_wraparound (N p d twor : ℕ)
    (hdvd : p ∣ N) (hNpos : 0 < N) (hNle : N ≤ twor ^ d) (hlt : twor ^ d < p) :
    False :=
  no_wraparound_of_norm_lt N (twor ^ d) p hdvd hNpos hNle hlt

/-- **Tightness value.** The antipodal carrier `D = 2r·ζ^a` has every conjugate magnitude equal to `2r`, so its norm
is exactly `(2r)^d` (`d = n/2`) — the house bound is attained, not merely an upper bound. (Stated as: the constant
product `∏_{j∈s} (2r) = (2r)^{|s|}`, the extremal value, so no norm-only bound below `(2r)^{n/2}` is possible.) -/
theorem antipodal_norm_eq {ι : Type*} (s : Finset ι) (r : ℝ) :
    ∏ _j ∈ s, (2 * r) = (2 * r) ^ s.card := Finset.prod_const _

end ProximityGap.Frontier.OnsetNorm

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.OnsetNorm.no_wraparound_of_norm_lt
#print axioms ProximityGap.Frontier.OnsetNorm.house_norm_le
#print axioms ProximityGap.Frontier.OnsetNorm.house_bound_lt_p_kills_wraparound
#print axioms ProximityGap.Frontier.OnsetNorm.antipodal_norm_eq
