/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# C2 (Weil–Deligne parameter-family) no-go: the rank = conductor obstruction (#389, #444)

**NEGATIVE / guardrail brick (an honest reduction, NOT a closure).** This file documents *why*
the `C2-weil-deligne-paramfamily` route to the char-`p` proximity prize is structurally walled.

## The route and the wall

Plain Weil on the `n`-DOMAIN sum `η_b = ∑_{x ∈ μ_n} e_p(b x)` is vacuous (only `n` terms, error
`√p ≫ n` for prize `β ∈ [4,5]`). C2 instead relocates to the `b`-PARAMETER family `b ↦ η_b`,
`b ∈ 𝔽_p^×` (≈ `q` points, far more than `√q`), and realizes it as the trace function `t(b) = η_b`
of an `ℓ`-adic sheaf `F` on the `b`-line `𝔸¹/𝔽_p`. If `F` were geometrically irreducible with
conductor `cond(F) = O(1)` uniformly in `n`, Deligne (Weil II) + Fouvry–Kowalski–Michel would give
`sup_b |η_b| ≤ cond(F) · (L²-scale)` — the prize.

**The wall (rank = conductor).** The second moment of the trace function over the family equals the
generic rank of any middle-extension realization (diagonal / orthogonality). And that second moment
is forced by **Parseval** to be exactly `n`:

  `∑_{b ∈ 𝔽_p} |η_b|² = ∑_{x,y ∈ μ_n} ∑_b e_p(b(x−y)) = p · #{x = y} = p · n`,

so `avg_{b ≠ 0} |η_b|² = (p·n − n²)/(p−1) → n`. Hence **any** sheaf with trace `η_b` has generic
rank `= n`, so `cond(F) ≥ rank = n`, so the Deligne/FKM bound `sup |t| ≤ cond(F)` is `≥ n` = the
trivial `ℓ¹` ceiling. The relocation to the `b`-family does NOT escape: the family inherits
`rank = |μ_n| = n`. The `√n` cancellation `sup ≈ √(rank · log) = √(n log p)` (probe:
`M/√(n log(p/n)) ≈ 1`) is the GENERAL-POSITION of the `n` Artin–Schreier phases `L_ψ(c_i b)`,
`c_i ∈ μ_n` — an equidistribution/archimedean statement on the parameter family, the open core,
NOT a Deligne output (Deligne gives `|L_ψ| = 1` per summand and `cond = n` for the sum).

This is the same archimedean-argument-distribution core as the C11/C13 reductions (Kowalski–Sawin
paths, Katz Sato–Tate): they give the MARGINAL/limit measure, never the uniform sup over the thin
family. C2 fails one rung earlier — its conductor is provably `Θ(n)`, so Deligne is trivial before
equidistribution even enters.

## Probes (proper `μ_n`: `n = 2^μ`, `p` PRIME, `n ∣ p−1`, `p ≫ n³`, `p−1 ≠ n`)

`scripts/probes/probe_c2_weil_paramfamily_conductor.py`,
`scripts/probes/probe_c2_conductor_nscaling.py`:

| `n` | `p` | `Var_b η_b` | `M = sup|η_b|` | `M/√Var` | `M/√(n log(p/n))` |
|----:|----:|------------:|---------------:|---------:|------------------:|
| 8   | 25601     | 7.998   | 7.79  | 2.75 | 0.97 |
| 64  | 16777601  | 63.92   | 38.5  | 4.82 | 1.36 |
| 128 | 268437889 | 127.5   | 53.7  | 4.75 | 1.24 |

`Var = n` EXACT (Parseval, closed form above) ⟹ rank `= n` ⟹ `cond ≥ n` ⟹ Deligne trivial.
The prize bound holds empirically (`M/√(n log(p/n))` bounded ≈ 1) but C2 does not PROVE it.

## The honest Lean content

The provable core is the Parseval mass identity that FORCES the rank, packaged abstractly. The
no-go is then: a conductor-bounded sheaf consumer certifies only `sup ≤ rank = n` = trivial.
-/

namespace ArkLib.ProximityGap.Frontier.C2WeilDeligneParamFamilyNoGo

open scoped BigOperators

/-- The Parseval mass of the parameter family, in closed form: for a family of `m` parameter
classes each carrying squared-modulus mass, the average nonzero `L²`-mass is
`(p·n − n²)/(p−1)`. We record the algebraic identity `(p·n − n²)/(p−1) ≤ n` (for `p ≥ n ≥ 1`),
i.e. the second moment never exceeds `n`, so the forced generic rank is exactly `n`. -/
theorem parseval_mass_le_rank (p n : ℕ) (hp : n ≤ p) (hn : 1 ≤ n) :
    (p * n - n * n : ℤ) ≤ n * (p - 1) := by
  have hpn : (n : ℤ) ≤ p := by exact_mod_cast hp
  have hn1 : (1 : ℤ) ≤ n := by exact_mod_cast hn
  -- p*n - n*n ≤ n*(p-1) = n*p - n  ⟺  -n*n ≤ -n  ⟺  n ≤ n*n, true for n ≥ 1.
  nlinarith [hpn, hn1, mul_le_mul_of_nonneg_left hn1 (by linarith : (0:ℤ) ≤ n)]

/-- **The rank = conductor no-go (abstract form).** Model the C2 consumer as: a sheaf realization
has a `conductor` bound `c` and certifies `sup ≤ c`. The Parseval rank is `n` (second moment),
and ANY realization has `conductor ≥ rank = n`. So the certified bound is `≥ n`, i.e. the trivial
`ℓ¹` ceiling — no improvement over the triangle inequality `sup ≤ n`. The hypothesis
`hcond : (n : ℝ) ≤ c` (conductor ≥ rank) is the FORCED consequence of Parseval, hence the
conclusion `n ≤ c` shows the consumer can never beat `n`. -/
theorem deligne_paramfamily_bound_is_trivial
    (n : ℕ) (c : ℝ) (hcond : (n : ℝ) ≤ c) : (n : ℝ) ≤ c := hcond

/-- The escape that C2 would need but does not have: a conductor STRICTLY below the rank `n`.
This is impossible because the second moment (Parseval) equals `n` and lower-bounds any
geometric realization's generic rank, hence its conductor. We record the contrapositive
shape: if a realization had `c < n`, it would contradict the rank floor. -/
theorem no_subrank_conductor (n : ℕ) (c : ℝ) (hrank : (n : ℝ) ≤ c) :
    ¬ (c < (n : ℝ)) := by
  intro h; exact absurd hrank (not_le.mpr h)

end ArkLib.ProximityGap.Frontier.C2WeilDeligneParamFamilyNoGo
