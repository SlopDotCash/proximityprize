/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandR3Bound
import ArkLib.Data.CodingTheory.ProximityGap.DeepBandR4Bound

/-!
# The 2-adic self-similar descent on the deep-band ORBIT COUNT (#444)

`lalalune`'s 2026-06-15 22:13 "decay-rate attack" reformulated the prize's open core as an
orbit count `D*(m) = (orbit size ≤ n)·#orbits(m)`.  Two halves of that reformulation are now
in-tree and axiom-clean:

* the **orbit SIZE** is `= n` EXACTLY on the prize-regime (odd-card) carriers
  (`Frontier.CliqueOrbitFreeness`, push `2dd402fb6`: the rotation `E ↦ E + j` is a FREE action),
  so each `#bad = n·#orbits + [0 ∈ bad]` with the single fixed `γ = 0` slice as the `+1`;
* the **bad-scalar counts** at the shallow rungs are pinned closed forms
  (`DeepBandR3.deepBandBadCount g = 2g²(g−1)+1` and
  `DeepBandR4.deepBandBadCount4 g = g⁴−2g³+4g+1`, with `g = n/4`).

Combining the two gives the deep-band **orbit counts** as exact closed forms, and (the content of
this file) a clean **2-adic self-similar descent law** relating the depth-`r=4` orbit count at
scale `n` to the depth-`r=3` bad count at the half-scale `n/2`.  This is the orbit-count form of
the parity / Lam–Leung antipodal descent that `DeepBandR4Bound` documents at the bad-count level
(`deepBandBadCount4 (2h) = 4·(2h)·R3(h) + 1`); expressing it at the orbit-count level removes the
`n·(…)` orbit-size factor uniformly and exposes the self-similarity directly.

## The descent law (all `g` even, `g = n/4`, `h = g/2 = n/8`)

  **Orbit-size factorization (`deepBandBadCount4_eq_orbit_factorization`).**
  `deepBandBadCount4 g = 4·g · DeepBandR3.deepBandBadCount (g/2) + 1`  (for even `g`).
  Reading `4·g = n` and `+1 = [γ = 0]`, this is exactly `#bad₄ = n·#orbits₄ + 1`, so

  **Orbit count at depth 4 (`orbitCount4`).**
  `orbitCount4 g := DeepBandR3.deepBandBadCount (g/2)`, the number of `⟨ζ⟩`-orbits of bad
  scalars at the `r=4` rung, scale `n = 4g`.

  **The self-similar descent (`orbitCount4_descent`).**
  `orbitCount4 g = (n/2)·(orbit count at depth 3, half scale) + 1`, i.e. in `g`:
  `orbitCount4 g = 2·g · (g/2).choose 2 + 1`.  The depth-4 orbit count at scale `n` is
  `(n/2)` copies of the depth-3 orbit count `C(n/8, 2)` at half-scale, plus the `+1` homogeneous
  `γ = 0` slice, i.e. one peeled 2-adic parity layer, depth `4 → 3`, scale `n → n/2`, weight `n/2`.

  Equivalently `orbitCount4 g = DeepBandR3.deepBandBadCount (g/2)` itself equals the *bad* count
  `#bad₃(n/2)` at the half-scale (`orbitCount4_eq_badCount3_halfScale`): the depth-4 ORBIT count is
  the depth-3 BAD count one octave down.

## Honest scope

This is a **pure-ℕ structural identity** over the two proven shallow closed forms plus the proven
orbit-size `= n`.  It is the orbit-count restatement of the *already-documented* `r=4` parity
descent (no new field computation; the `r=4` bad count itself is `[COMPUTED]`-calibrated in
`DeepBandR4Bound`, not re-asserted here).  It is **NOT** a bound on the deep rung `r ≈ log n`, which
is exactly `|Σ_r(μ_s)|` = BCHKS 1.12 = the BGK wall, untouched.  The `DeepBandR4Bound` docstring
records that the order-2 parity split (which this descent encodes) is the worst case only up to
`r = 4`: at `r = 5` the maximizing line flips to a full-order line invisible to the order-2
character, so this descent **does not continue past `r = 4`**.  Character-sum-free, char-agnostic,
NOT thinness-essential; does **not** close CORE `M(μ_n) ≤ C·√(n·log(p/n))`.

Probe: `scripts/probes/probe_orbit_count_descent.py` (the orbit-count descent over the proven
closed forms; `orbitCount4 = (bad4−1)/n = R3(n/8) = bad3(n/2) = 2g·C(g/2,2)+1`, exact `n = 16..512`,
NEVER `n = q−1`).
-/

namespace ArkLib.ProximityGap.DeepBandOrbitCountDescent

open ArkLib.ProximityGap

/-- **Orbit-size factorization of the `r=4` bad count.**  For even `g` (`g = n/4`, `n = 2^a`,
`a ≥ 3`), the depth-`4` bad-scalar count factors as `n·(orbit count) + 1`:
`deepBandBadCount4 g = 4·g · DeepBandR3.deepBandBadCount (g/2) + 1`.

Mechanism: `4·g = n` is the proven orbit size (`Frontier.CliqueOrbitFreeness`, free action), and the
`+1` is the single fixed `γ = 0` (homogeneous) slice.  Pure ℕ algebra over the two proven closed
forms (`g = 2h`: both sides expand to `16h⁴ − 16h³ + 8h + 1`). -/
theorem deepBandBadCount4_eq_orbit_factorization (h : ℕ) (hh : 1 ≤ h) :
    DeepBandR4.deepBandBadCount4 (2 * h)
      = 4 * (2 * h) * DeepBandR3.deepBandBadCount h + 1 := by
  obtain ⟨e, rfl⟩ : ∃ e, h = e + 1 := ⟨h - 1, by omega⟩
  -- Avoid ℕ truncated subtraction in `deepBandBadCount4` via the proven additive form.
  have hadd : DeepBandR4.deepBandBadCount4 (2 * (e + 1)) + 2 * (2 * (e + 1)) ^ 3
      = (2 * (e + 1)) ^ 4 + 4 * (2 * (e + 1)) + 1 :=
    DeepBandR4.deepBandBadCount4_add (2 * (e + 1)) (by omega)
  -- the r=3 count with `(e+1)-1 = e` resolved (no truncated subtraction left).
  have hr3 : DeepBandR3.deepBandBadCount (e + 1) = 2 * (e + 1) ^ 2 * e + 1 := by
    rw [DeepBandR3.deepBandBadCount, Nat.add_sub_cancel]
  rw [hr3]
  -- `4*(2(e+1))*(2(e+1)^2 e + 1) + 1 + 2*(2(e+1))^3 = (2(e+1))^4 + 4*(2(e+1)) + 1`, then cancel.
  have hexpand : 4 * (2 * (e + 1)) * (2 * (e + 1) ^ 2 * e + 1) + 1 + 2 * (2 * (e + 1)) ^ 3
      = (2 * (e + 1)) ^ 4 + 4 * (2 * (e + 1)) + 1 := by ring
  omega

/-- The number of `⟨ζ⟩`-orbits of bad scalars at the `r=4` rung, scale `n = 4g` (`g = n/4`):
`orbitCount4 g = #bad₄ / n = DeepBandR3.deepBandBadCount (g/2)` (the `g/2 = n/8` half-scale `r=3`
count).  Well-defined because the rotation action has orbit size exactly `n` off the fixed
`γ = 0` point (`Frontier.CliqueOrbitFreeness`). -/
def orbitCount4 (g : ℕ) : ℕ := DeepBandR3.deepBandBadCount (g / 2)

/-- **The orbit-size identity in `orbitCount4` form** (even `g`):
`deepBandBadCount4 g = 4·g · orbitCount4 g + 1`, i.e. `#bad₄ = n·#orbits₄ + 1`. -/
theorem deepBandBadCount4_eq_n_mul_orbitCount4 (h : ℕ) (hh : 1 ≤ h) :
    DeepBandR4.deepBandBadCount4 (2 * h) = 4 * (2 * h) * orbitCount4 (2 * h) + 1 := by
  rw [orbitCount4]
  have : (2 * h) / 2 = h := by omega
  rw [this]
  exact deepBandBadCount4_eq_orbit_factorization h hh

/-- **The depth-3 orbit count** at scale `n = 4g`: `#bad₃ = n·#orbits₃ + 1` with
`#orbits₃ = C(n/4, 2) = (g).choose 2`.  Recorded here as the half-scale anchor of the descent
(its `g/2` instance is the right-hand side of `orbitCount4_descent`). -/
def orbitCount3 (g : ℕ) : ℕ := g.choose 2

/-- `DeepBandR3.deepBandBadCount g = 4·g · orbitCount3 g + 1` (the `r=3` orbit-size factorization,
`#bad₃ = n·#orbits₃ + 1`, `#orbits₃ = C(g,2)`, `g = n/4`). -/
theorem deepBandBadCount_eq_n_mul_orbitCount3 (g : ℕ) :
    DeepBandR3.deepBandBadCount g = 4 * g * orbitCount3 g + 1 := by
  rw [orbitCount3, DeepBandR3.deepBandBadCount_eq_choose]

/-- **The 2-adic self-similar descent law** (even `g`, `g = n/4`, `h = g/2 = n/8`):
`orbitCount4 g = 2·g · orbitCount3 (g/2) + 1`.

Reading `2·g = n/2` and `orbitCount3 (g/2) = C(n/8, 2) = #orbits₃` at the half-scale `n/2`, this is
`#orbits₄(n) = (n/2)·#orbits₃(n/2) + 1`: the depth-4 orbit count at scale `n` is `(n/2)` copies of
the depth-3 orbit count one octave down, plus the `+1` homogeneous `γ = 0` slice.  One peeled 2-adic
parity layer (`r: 4 → 3`, scale `n → n/2`). -/
theorem orbitCount4_descent (h : ℕ) :
    orbitCount4 (2 * h) = 2 * (2 * h) * orbitCount3 h + 1 := by
  rw [orbitCount4, orbitCount3]
  have hh : (2 * h) / 2 = h := by omega
  rw [hh, DeepBandR3.deepBandBadCount_eq_choose]
  ring

/-- **The depth-4 ORBIT count is the depth-3 BAD count one octave down.**
`orbitCount4 g = DeepBandR3.deepBandBadCount (g/2) = #bad₃(n/2)`. -/
theorem orbitCount4_eq_badCount3_halfScale (g : ℕ) :
    orbitCount4 g = DeepBandR3.deepBandBadCount (g / 2) := rfl

/-! ## Numerical rungs (must reproduce the data; `n = 4g`). -/

/-- `n = 16`  (`g = 4`): `#bad₄ = 145 = 16·9 + 1`, `#orbits₄ = 9`. -/
theorem rung_n16 : DeepBandR4.deepBandBadCount4 4 = 145 ∧ orbitCount4 4 = 9 :=
  ⟨by decide, by decide⟩

/-- `n = 32`  (`g = 8`): `#bad₄ = 3105 = 32·97 + 1`, `#orbits₄ = 97`. -/
theorem rung_n32 : DeepBandR4.deepBandBadCount4 8 = 3105 ∧ orbitCount4 8 = 97 :=
  ⟨by decide, by decide⟩

/-- `n = 64`  (`g = 16`): `#bad₄ = 57409 = 64·897 + 1`, `#orbits₄ = 897`. -/
theorem rung_n64 : DeepBandR4.deepBandBadCount4 16 = 57409 ∧ orbitCount4 16 = 897 :=
  ⟨by decide, by decide⟩

/-- `n = 128` (`g = 32`): `#bad₄ = 983169 = 128·7681 + 1`, `#orbits₄ = 7681`. -/
theorem rung_n128 : DeepBandR4.deepBandBadCount4 32 = 983169 ∧ orbitCount4 32 = 7681 :=
  ⟨by decide, by decide⟩

/-- Cross-check: the descent reproduces the same orbit-count rungs. -/
theorem rung_descent_n16 : orbitCount4 4 = 2 * 4 * orbitCount3 2 + 1 := by decide
theorem rung_descent_n32 : orbitCount4 8 = 2 * 8 * orbitCount3 4 + 1 := by decide
theorem rung_descent_n64 : orbitCount4 16 = 2 * 16 * orbitCount3 8 + 1 := by decide

end ArkLib.ProximityGap.DeepBandOrbitCountDescent
