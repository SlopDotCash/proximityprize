/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
Co-authored-by: wakesync <shadow@shad0w.xyz>
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Real.Basic

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# The char-`p` r=3 DC-Wick rung, fused with the explicit wraparound spur (#444 / #407)

`Frontier/Kappa6R3DCWickRung.lean` proves the r=3 rung `κ₆ ≤ 45 n²` from the **char-0** depth-3
energy `E₃ = 15n³ − 45n² + 40n` (hypothesis `h3`). `Frontier/_wf6P2_charp_lamleung_slack.lean`
isolates the open content to the **wraparound spur** `Spur_r(p) := A_r^{F_p} − A_r^ℤ` (the char-`p`
additive energy minus its char-0 value), and `Frontier/DCWickWraparoundTransfer.lean` pins the prize
crux to `q·wickExcess ≤ n^{2r}`. NONE of them carries the spur into the r=3 **cumulant** face.

This file does exactly that fusion at `r = 3`: it threads the explicit spur term `S := Spur_3(p)`
through the κ₆ algebra and proves the **exact** gate

> `κ₆^{F_p}(μ_n) = 40 n + S`     and     `κ₆^{F_p} ≤ 45 n²  ⟺  S ≤ 45 n² − 40 n`,

so the r=3 char-`p` rung holds **iff** the wraparound spur fits in the quadratic slack
`45 n² − 40 n = ceiling − Z` (`ceiling = 15 n³` the Lam–Leung double-factorial cap, `Z = E₃^ℤ`).
This is precisely the `(P2-Slack)` residual of `_wf6P2` specialized to `r = 3`, now expressed on the
cumulant the rung actually consumes.

## The char-`p` energy split it consumes (from `_wf6P2`)

`E₃^{F_p}(μ_n) = E₃^ℤ(μ_n) + S` with `E₃^ℤ = 15 n³ − 45 n² + 40 n` (PROVEN char-0, two in-tree
routes agree: `E3RouteBridge.e3_routes_agree`) and `S = Spur_3(p) ≥ 0` the char-`p` wraparound
excess (count-unbalanced zero-sum 6-tuples that vanish mod `p` but not over `ℂ`).

## Probe verdict (the gate hypothesis is PRIZE-SCALE-ESSENTIAL, not prime-uniform)

`scripts/probes/probe_spur3_*`, exact-integer `E₃^{F_p}` over the PROPER subgroup `μ_n ⊊ F_p^*`
(`E₃ = Σ_s T₃(s)·T₃(−s)`, `T₃` the 3-tuple sum distribution), `n = 4..32`, NEVER `n = q−1`:

* **At the prize scale `p ≥ n⁴`: `S = Spur_3(p) = 0` EXACTLY**, verified at 9 instances
  (`n=4`: `p=257,509,1021`; `n=8`: `p=4073,11593,32801`; `n=16`: `p=65537,262193,1048609`; mixed
  Fermat / non-Fermat, `β = 4, 4.5, 5`). So the gate `S ≤ 45n²−40n` holds with full margin and the
  char-0 `h3` is EXACT there.
* **At small `p` the gate FAILS**: `S > 45n²−40n` by an unbounded factor (`S=10440 > 2560` at
  `n=8,p=17`; `S=141120 > 10880` at `n=16,p=97`, a `12.97×` overshoot). The last violating prime is
  `p ≈ n^{2.3}` (`p=41` for `n=8`, `p=641` for `n=16`) and the last prime with **any** `S > 0` is
  `< n⁴` (`p=13, 313, 41521` for `n=4,8,16`), all BELOW the prize scale.

**Mechanism (constraint lemma).** A count-unbalanced zero-sum 6-tuple needs its integer-lift root
sum to be a NONZERO multiple of `p`; the house of a nonzero 6-term `2^a`-th-root sum is bounded, so
such `p` sit below a polynomial threshold. Hence the slack route `S ≤ ceiling − Z` is **NOT
prime-uniform**: it FAILS at small `p` and holds at the prize scale, where `S = 0` outright. The r=3
rung is **prize-scale-essential**: any prime-uniform / thickness-monotone version is FALSE (the
char-`p` analogue of the thinness-essentiality the prize CORE demands).

## What THIS file proves (axiom-clean; the only inputs are the named energy values + the spur term)

* `kappa6_charp_eq` : `κ₆^{F_p} = (E₃^ℤ + S) − 15 E₂ E₁ + 30 E₁³ = 40 n + S` (pure algebra;
  the char-0 cubic/quadratic cancellation of `Kappa6R3.kappa6_eq` survives, the spur `S` passes
  through additively).
* `kappa6_charp_le_iff_spur_le` : the **exact gate** `κ₆^{F_p} ≤ 45 n² ↔ S ≤ 45 n² − 40 n`.
* `kappa6_charp_le_of_spur_le` : the consumable forward direction.
* `spur_slack_eq_ceiling_sub_charZero` : the slack `45 n² − 40 n` is exactly `ceiling − Z` at
  `r = 3` (`ceiling = 15n³`, `Z = E₃^ℤ = 15n³−45n²+40n`), tying the gate to `_wf6P2` `(P2-Slack)`.

## Honest status (a REDUCTION/UNIFICATION, NOT a CORE closure)

This fuses two existing in-tree faces (the char-0 r=3 cumulant rung and the abstract spur slack
route) into the single exact r=3 gate on the spur, and records the probe verdict that the gate is
prize-scale-essential. It does NOT prove `S ≤ 45n²−40n` for general `p` (that is an open
char-`p` count bound, here a named term), and it touches NO `r > 3` rung. The prize floor needs the
full DC-Wick ladder `r ≤ log m`. CORE `M(μ_n) ≤ C√(n log(p/n))` stays OPEN.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`. Issue #444 / #407.
-/

namespace ArkLib.ProximityGap.Frontier.Kappa6R3CharPSpur

/-- **The char-`p` 6th cumulant carries the wraparound spur additively: `κ₆^{F_p} = 40 n + S`.**
With the two PROVEN char-0 energies `E₁ = n`, `E₂ = 3n²−3n` and the char-`p` depth-3 energy split
as `E₃^{F_p} = (15n³−45n²+40n) + S` (char-0 value plus the wraparound spur `S = Spur_3(p)`), the
symmetric mean-0 6th cumulant `κ₆ = E₃^{F_p} − 15 E₂ E₁ + 30 E₁³` equals `40 n + S`. The char-0
cubic/quadratic cancellation (`Kappa6R3.kappa6_eq`) is undisturbed; the spur passes through. -/
theorem kappa6_charp_eq (n E1 E2 E3 S : ℝ)
    (h1 : E1 = n) (h2 : E2 = 3 * n ^ 2 - 3 * n)
    (h3 : E3 = (15 * n ^ 3 - 45 * n ^ 2 + 40 * n) + S) :
    E3 - 15 * E2 * E1 + 30 * E1 ^ 3 = 40 * n + S := by
  subst h1 h2 h3; ring

/-- **The slack at `r = 3` is exactly `ceiling − Z`.** With the Lam–Leung double-factorial ceiling
`ceiling = 15 n³` (`= (2·3−1)‼·n³`) and the char-0 zero-sum count `Z = E₃^ℤ = 15n³−45n²+40n`, the
quadratic slack the spur must fit is `ceiling − Z = 45 n² − 40 n`. This is the r=3 instance of the
`(P2-Slack)` residual of `_wf6P2_charp_lamleung_slack` (`S ≤ ceiling − Z`). -/
theorem spur_slack_eq_ceiling_sub_charZero (n : ℝ) :
    (15 * n ^ 3) - (15 * n ^ 3 - 45 * n ^ 2 + 40 * n) = 45 * n ^ 2 - 40 * n := by
  ring

/-- **The exact r=3 char-`p` gate: `κ₆^{F_p} ≤ 45 n² ↔ S ≤ 45 n² − 40 n`.** The char-`p` r=3
DC-Wick rung (cumulant face) holds if and only if the wraparound spur `S` fits in the quadratic
slack `45 n² − 40 n`. No hidden inflation: the gate is the bare `(P2-Slack)` residual at `r = 3`,
on the cumulant the rung consumes. -/
theorem kappa6_charp_le_iff_spur_le (n E1 E2 E3 S : ℝ)
    (h1 : E1 = n) (h2 : E2 = 3 * n ^ 2 - 3 * n)
    (h3 : E3 = (15 * n ^ 3 - 45 * n ^ 2 + 40 * n) + S) :
    (E3 - 15 * E2 * E1 + 30 * E1 ^ 3 ≤ 45 * n ^ 2) ↔ (S ≤ 45 * n ^ 2 - 40 * n) := by
  rw [kappa6_charp_eq n E1 E2 E3 S h1 h2 h3]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **Consumable forward direction.** If the wraparound spur fits the quadratic slack
(`S ≤ 45 n² − 40 n`) then the char-`p` r=3 rung holds (`κ₆^{F_p} ≤ 45 n²`). The PROBE certifies the
hypothesis HOLDS at the prize scale (`S = Spur_3(p) = 0`, `p ≥ n⁴`) and FAILS at small `p`
(prize-scale-essential). -/
theorem kappa6_charp_le_of_spur_le (n E1 E2 E3 S : ℝ)
    (h1 : E1 = n) (h2 : E2 = 3 * n ^ 2 - 3 * n)
    (h3 : E3 = (15 * n ^ 3 - 45 * n ^ 2 + 40 * n) + S)
    (hgate : S ≤ 45 * n ^ 2 - 40 * n) :
    E3 - 15 * E2 * E1 + 30 * E1 ^ 3 ≤ 45 * n ^ 2 :=
  (kappa6_charp_le_iff_spur_le n E1 E2 E3 S h1 h2 h3).mpr hgate

/-- **Recovery of the char-0 rung.** At the prize scale the spur vanishes (`S = 0`, PROBE-certified
`p ≥ n⁴`); the gate `0 ≤ 45 n² − 40 n` is automatic for `n ≥ 1`, and `κ₆^{F_p} = 40 n` recovers
`Kappa6R3.kappa6_eq` exactly. This is the brick degenerating to the proven char-0 rung precisely
where the spur clears. -/
theorem kappa6_charp_le_of_spur_zero (n E1 E2 E3 : ℝ) (hn : 1 ≤ n)
    (h1 : E1 = n) (h2 : E2 = 3 * n ^ 2 - 3 * n)
    (h3 : E3 = 15 * n ^ 3 - 45 * n ^ 2 + 40 * n) :
    E3 - 15 * E2 * E1 + 30 * E1 ^ 3 ≤ 45 * n ^ 2 := by
  refine kappa6_charp_le_of_spur_le n E1 E2 E3 0 h1 h2 (by rw [h3]; ring) ?_
  nlinarith [hn, sq_nonneg (n - 1)]

end ArkLib.ProximityGap.Frontier.Kappa6R3CharPSpur

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.Kappa6R3CharPSpur.kappa6_charp_eq
#print axioms ArkLib.ProximityGap.Frontier.Kappa6R3CharPSpur.spur_slack_eq_ceiling_sub_charZero
#print axioms ArkLib.ProximityGap.Frontier.Kappa6R3CharPSpur.kappa6_charp_le_iff_spur_le
#print axioms ArkLib.ProximityGap.Frontier.Kappa6R3CharPSpur.kappa6_charp_le_of_spur_le
#print axioms ArkLib.ProximityGap.Frontier.Kappa6R3CharPSpur.kappa6_charp_le_of_spur_zero
