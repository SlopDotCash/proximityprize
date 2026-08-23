/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Tactic

/-!
# The below-saddle depth threshold: onset ceiling is unconditional but vacuous at prize scale (#444)

Target (B) of the round: can the unconditional good region `W_r = 0` (the onset ceiling) be *provably*
extended above onset toward the saddle `r ≈ log p`?  This brick records the honest verdict, axiom-clean.

**The onset ceiling (the unconditional good direction).**  A depth-`r` relation `α = Σζ^{a_i} − Σζ^{b_j}`
has field norm `1 ≤ |N(α)| ≤ (2r)^{φ(n)}` if `α ≠ 0`, and lies in the split prime `𝔭 | p` only if `p | N(α)`,
forcing `|N(α)| ≥ p`.  So if the norm ceiling `(2r)^{φ(n)} < p`, *no* nonzero relation reduces into `𝔭` and the
wraparound `W_r(p) = 0` — unconditionally.  `no_wraparound_below_ceiling` captures this: a nonzero relation with
norm `≤ maxNorm < p` cannot be `𝔭`-divisible.

**The reduction (why it does not reach the saddle).**  The ceiling applies only for `r < r_onset = ½·p^{1/φ(n)}`.
At **prize scale** `φ(n) = 2^{29}`, `p ≈ 2^{158}`, so `(2·1)^{φ(n)} = 2^{2^{29}} ≫ 2^{158} ≥ p` already at `r = 1`:
the ceiling `(2r)^{φ(n)} < p` is **false at every integer depth `r ≥ 1`**.  `onset_ceiling_vacuous_at_prize`
proves exactly this — the unconditional good region is *empty* of useful depths.  The probe
`probe_depth_threshold` confirms `W_r ≤ slack` holds throughout the computable range with no finite failure, that
the actual onset is even later than `r_onset` (the cyclotomic lattice is round, no super-short relations), and
that the crude Minkowski lattice-point count `(2r)^{φ(n)}/p` *overshoots* `slack` immediately — a vacuous upper
bound.  The crude count cannot certify `W_r ≤ slack`; only the signed cancellation (growing-order equidistribution)
can.  This is the moment-necessity obstruction in geometric/lattice dress: a count overshoots, the gap
`[r_onset, log p]` is the whole range, and bridging it is the open wall.

`#print axioms` ⊆ {propext, Classical.choice, Quot.sound}.
-/

namespace ProximityGap.DepthThresholdReduction

/-- **The onset ceiling (unconditional good direction).**  A *nonzero* relation has field norm `N ≥ 1`; being
`𝔭`-divisible forces `p ∣ N`, hence `N ≥ p`.  So if every relation norm is `≤ maxNorm < p`, no nonzero relation
is `𝔭`-divisible — the wraparound vanishes.  (Stated as the impossibility of a `𝔭`-divisible relation below the
ceiling.) -/
theorem no_wraparound_below_ceiling {p maxNorm N : ℕ}
    (hmax : maxNorm < p) (hN1 : 1 ≤ N) (hNmax : N ≤ maxNorm) (hdvd : p ∣ N) : False := by
  have hpN : p ≤ N := Nat.le_of_dvd hN1 hdvd
  omega

/-- **The onset radius is the largest `r` with `(2r)^d < p`.**  Below it the ceiling certifies `W_r = 0`; this
restates the ceiling in the depth/`r` variable: if `(2r)^d < p` and a nonzero relation of norm `≤ (2r)^d` were
`𝔭`-divisible, contradiction. -/
theorem no_wraparound_below_onset {p r d N : ℕ}
    (honset : (2 * r) ^ d < p) (hN1 : 1 ≤ N) (hNmax : N ≤ (2 * r) ^ d) (hdvd : p ∣ N) : False :=
  no_wraparound_below_ceiling honset hN1 hNmax hdvd

/-- **The onset ceiling is vacuous at prize scale.**  With `φ(n) = d ≥ 158` and `p ≤ 2^{158}`, for *every*
depth `r ≥ 1` the norm ceiling satisfies `(2r)^d ≥ p` — so `(2r)^d < p` is false and the unconditional
`W_r = 0` certificate is unavailable at *any* integer depth.  Hence the below-onset good region reaches no
useful depth; the gap to the saddle `r ≈ log p` is the entire range and requires the growing-order
equidistribution (the wall), not the depth ceiling. -/
theorem onset_ceiling_vacuous_at_prize {p r d : ℕ}
    (hd : 158 ≤ d) (hp : p ≤ 2 ^ 158) (hr : 1 ≤ r) :
    p ≤ (2 * r) ^ d := by
  calc p ≤ 2 ^ 158 := hp
    _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
    _ ≤ (2 * r) ^ d := Nat.pow_le_pow_left (by omega) d

/-- **Corollary — no unconditional depth certificate at prize scale.**  Combining the two: at prize parameters,
the onset ceiling cannot certify `W_r = 0` at any depth `r ≥ 1`, because its hypothesis `(2r)^d < p` is
contradicted by `onset_ceiling_vacuous_at_prize`.  The unconditional good region is empty; what remains is the
open `[1, log p]` equidistribution gap. -/
theorem no_unconditional_certificate_at_prize {p r d : ℕ}
    (hd : 158 ≤ d) (hp : p ≤ 2 ^ 158) (hr : 1 ≤ r) :
    ¬ ((2 * r) ^ d < p) := by
  have h := onset_ceiling_vacuous_at_prize hd hp hr
  omega

end ProximityGap.DepthThresholdReduction
