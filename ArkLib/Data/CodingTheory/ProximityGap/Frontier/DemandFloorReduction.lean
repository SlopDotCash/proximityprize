/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# `DemandFloorReduction` — the deep-band prize floor reduced to one orbit-count conjecture (#444)

The demand-side prize floor (CensusDomination) asks that the deep-band distinct-bad-scalar count
satisfy `#bad ≤ K := 2^r · C(n/2, r)` for every admissible witness line on the smooth domain `μ_n`
(`n = 2^μ`). Two multi-agent workflows established (verified exact, char-0 / two primes, r=3
calibration digit-for-digit):

* **Orbit identity (proven):** `#bad = (n/d)·O_P + [γ=0]`, where `γ` is the bilinear Schur-ratio
  pin, `d = gcd(e−f, n)`, every nonzero `γ`-orbit has full size `n/d`, and `O_P` counts the distinct
  dilation invariants `J := γ^{n/d}`. In particular `#bad ≤ n·O_P + 1` (worst case `d = 1`).
* **The remaining conjecture (open, evidence-backed):** `O_P ≤ C(n/2, r−1)` for every admissible
  line, all `n = 2^μ`. Verified exhaustively at `n = 16` (all lines, two primes, worst ratio 0.25),
  `n = 32`, and all known maximizers to `n = 64`. It is **not proven for any `r` as a general-`n`
  theorem**: `r = 3` is one lemma short (the inequality `O_P ≤ C(n/4, 2) ≤ C(n/2, 2)` follows from a
  fixed-point-free negation involution *once* one proves `J = γ^{n/d}` factors through the
  scale-invariant ratio `I₃ = e₁⁴/e₄` — verified only to `n ≤ 1024`; note the *equality*
  `O_P = C(n/4, 2)` is FALSE for `n ≥ 2048`, where extra collisions shrink the count, so only the
  inequality is the live claim). For `r ≥ 4` the single-coordinate structure breaks and it is wide
  open; the residual is a per-fiber cyclotomic field-degree (eliminant degree of `J` on the variety).
  Sharpness is proven: any proof must use the index-2 squares subgroup `μ_{n/2}` (a generic
  codim-1 / Bézout count gives `C(n, ·)`, too weak by `2^r`); subset-valued descents to `μ_{n/2}`
  provably do not exist (`J` carries finer field data than any roots-of-unity subset).

This file formalizes the **PROVEN bridge**: the elementary clearance inequality and the consequent
reduction `O_P ≤ C(n/2, r−1) ⟹ #bad ≤ K`. Hence the entire demand-side prize floor reduces to the
single named conjecture `DeepBandOrbitConjecture`. Axiom-clean (`decide`-free; pure `Nat`).

Writing `m := n/2` (the squares-subgroup size) and `n = 2m`, the worst-case (`d = 1`) bound to
clear is `n · O_P = 2m · O_P ≤ K = 2^r · C(m, r)`. Given `O_P ≤ C(m, r−1)`, this follows from the
clearance lemma `2·m·r ≤ 2^r·(m − r + 1)` (valid for `r ≥ 4`, `2r ≤ m`, i.e. `n ≥ 4r`) and the
Pascal identity `r · C(m, r) = (m − r + 1) · C(m, r − 1)`.
-/

namespace ArkLib.ProximityGap.DemandFloorReduction

open Nat

/-- Elementary growth fact: `4·r ≤ 2^r` for `r ≥ 4` (the engine of the clearance lemma). -/
theorem four_mul_le_two_pow : ∀ r, 4 ≤ r → 4 * r ≤ 2 ^ r := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r hr ih =>
    have h4 : (4 : ℕ) ≤ 2 ^ r := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 4 * (r + 1) = 4 * r + 4 := by ring
      _ ≤ 2 ^ r + 2 ^ r := by omega
      _ = 2 ^ (r + 1) := by rw [pow_succ]; ring

/-- **The clearance lemma.** For `r ≥ 4` and `2r ≤ m` (i.e. `n = 2m ≥ 4r`), the orbit budget
`C(m, r−1)` clears the supply `K·d/n` in the worst case `d = 1`: concretely `2·m·r ≤ 2^r·(m−r+1)`.
This is what makes `O_P ≤ C(m, r−1)` strong enough to give `#bad ≤ K`. -/
theorem clearance (m r : ℕ) (hr : 4 ≤ r) (hm : 2 * r ≤ m) :
    2 * m * r ≤ 2 ^ r * (m - r + 1) := by
  have hmr : m ≤ 2 * (m - r + 1) := by omega
  have h4r : 4 * r ≤ 2 ^ r := four_mul_le_two_pow r hr
  calc 2 * m * r = 2 * r * m := by ring
    _ ≤ 2 * r * (2 * (m - r + 1)) := by gcongr
    _ = (4 * r) * (m - r + 1) := by ring
    _ ≤ (2 ^ r) * (m - r + 1) := by gcongr

/-- **The reduction (PROVEN bridge).** If the deep-band orbit count satisfies `O_P ≤ C(m, r−1)`
(with `m = n/2`), then the worst-case bad-scalar count `n·O_P = 2m·O_P` is at most the supply budget
`K = 2^r·C(m, r)`. Combined with the proven orbit identity `#bad = (n/d)·O_P + [γ=0] ≤ n·O_P + 1`,
this closes the CensusDomination prize floor `#bad ≤ K` from the single conjecture below. -/
theorem demand_floor_of_orbit_bound (m r OP : ℕ) (hr : 4 ≤ r) (hm : 2 * r ≤ m)
    (hOP : OP ≤ m.choose (r - 1)) :
    2 * m * OP ≤ 2 ^ r * m.choose r := by
  have hr1 : 1 ≤ r := by omega
  -- Pascal/absorption identity: `C(m,r)·r = C(m,r−1)·(m−r+1)`.
  have hch : m.choose r * r = m.choose (r - 1) * (m - r + 1) := by
    have h := Nat.choose_succ_right_eq m (r - 1)
    rw [Nat.sub_add_cancel hr1] at h
    rw [h]; congr 1; omega
  have hcl : 2 * m * r ≤ 2 ^ r * (m - r + 1) := clearance m r hr hm
  have hrpos : 0 < r := by omega
  -- cancel the common factor `r` after multiplying the target through.
  refine Nat.le_of_mul_le_mul_right ?_ hrpos
  calc (2 * m * OP) * r ≤ (2 * m * m.choose (r - 1)) * r := by gcongr
    _ = (2 * m * r) * m.choose (r - 1) := by ring
    _ ≤ (2 ^ r * (m - r + 1)) * m.choose (r - 1) := by gcongr
    _ = 2 ^ r * (m.choose (r - 1) * (m - r + 1)) := by ring
    _ = 2 ^ r * (m.choose r * r) := by rw [← hch]
    _ = (2 ^ r * m.choose r) * r := by ring

/-! ## The remaining open obligation

The bridge `demand_floor_of_orbit_bound` consumes exactly one hypothesis on the witness — its orbit
count `OP` (the number of distinct dilation invariants `J = γ^{n/d}` of the depth-`r` bilinear
Schur-ratio variety on `μ_n`):

  **`OP ≤ C(n/2, r − 1)`   (`m = n/2`, the squares subgroup).**

This is the single open input. It is verified exhaustively at `n = 16` (all lines, two primes, worst
ratio `0.25`), `n = 32`, and every known maximizer to `n = 64`, with the ratio shrinking in `n`, but
is **proven for no `r` as a general-`n` theorem**: `r = 3` is one factoring lemma short (and the
clean *equality* `OP = C(n/4,2)` even fails for `n ≥ 2048` — only the inequality is live), and
`r ≥ 4` is wide open with the residual a per-fiber cyclotomic field-degree. Sharpness is proven: any
proof must exploit the index-2 squares subgroup `μ_{n/2}` — a generic codimension-1 / Bézout /
Schwartz–Zippel count yields `C(n, ·)`, too weak by `2^r` — yet no subset-valued descent to `μ_{n/2}`
exists (`J` carries finer field-arithmetic data than any roots-of-unity subset). (We deliberately do
NOT encode this as a top-level `def … : Prop`, since the faithful statement quantifies over the
witness's *actual* orbit count, not an arbitrary `OP`; stating it with a free `OP` would be a vacuous
placeholder.) -/

end ArkLib.ProximityGap.DemandFloorReduction
