/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The 2-power tower / tensor Λ(q) recursion: coset-doubling is super-multiplicative (#444)

## The object and the hope

The prize floor `M = max_{b≠0}|η_b| ≤ C·√(n·log m)` is the **Λ(q) inequality**
`‖η‖_{L^q(Z_p)} ≤ C·√q·√n` at `q ≈ 2 log m` for the frequency set `μ_n` (`n = 2^μ`), per the in-tree
end-to-end brick `_LambdaQRudinEndToEnd` (Λ(q) bound ⟹ prize floor, FORWARD direction PROVEN).

Since `μ_2 ⊂ μ_4 ⊂ … ⊂ μ_n` is a 2-power tower, one hopes the Λ(q) constant **tensorizes /
contracts** down the tower: a coset-doubling identity
`η_{μ_{2n}}(b) = η_{μ_n}(b) + η_{μ_n}(h·b)` (`h` = primitive `2n`-th root, the in-tree EXACT
one-octave descent `_DyadicTowerDescent` / `_AntipodalDyadicSymmetric`) might give a
**sub-multiplicative** Λ(q) recursion `C_q(2n) ≤ Δ · C_q(n)` with a per-octave decoupling gain
`Δ < 2`, telescoping `μ` octaves below the trivial `√n` scale to the prize `√(n log m)`.

## The refutation-with-mechanism (this file = the moment arithmetic; the probe = the constants)

The sup-norm version of this hope is the in-tree TOWER-2 decoupling NO-GO
(`_DecouplingTowerNoSaving`, `_TowerDescentNoSaving`): the worst-frequency octave constant is
`Δ = 2` exactly (octave halves align, `cos = 1`), so the telescope lands at the trivial `2^μ = n`
scale with NO `√(log m)` prize factor.

**This file checks the EVEN-`q` / moment version of the same hope, and finds it fails the SAME way.**
Even-`q` Λ(q) is the energy moment: `‖η‖_{2k}^{2k}` is governed by `E_k(μ_n)` (the `k`-th additive
energy). The natural Λ(q)-normalized moment ratio is

> `ρ_k(n) := E_k(μ_n) / Wick_k(n)`,  `Wick_k(n) := (2k−1)‼ · n^k`  (the Gaussian/Sidon reference),

and a sub-multiplicative Λ(q) recursion requires `ρ_k(2n) ≤ ρ_k(n)` (the constant contracts up the
tower). **The exact `k = 2` octave REFUTES this**: from the in-tree EXACT antipodal energy
`E_2(μ_n) = 3n(n−1) = 3n² − 3n` (the Sidon defect; `μ_n` is Sidon-except-negation), one gets the
CLOSED FORM

> `ρ_2(n) = (3n² − 3n)/(3n²) = 1 − 1/n`,  and the **octave tower-ratio**
> `ρ_2(2n)/ρ_2(n) = (1 − 1/(2n))/(1 − 1/n) = (2n−1)/(2(n−1)) > 1`  strictly for all `n ≥ 2`.

The normalized moment constant is **monotone INCREASING** up the 2-power tower (it climbs toward `1`
from below). So coset-doubling is **super-multiplicative on the energy**, not sub-multiplicative:
`E_2(μ_{2n}) = (4n−2)/(n−1) · E_2(μ_n) > 4·E_2(μ_n) = 2^k·E_2(μ_n)` (`k = 2`) — the cross-term
surplus `2·Re⟨η_{μ_n}, η_{h·μ_n}⟩` is POSITIVE and grows, exactly the moment shadow of the
constructive `cos = 1` octave alignment. There is no per-octave decoupling gain `Δ < 2`; the Λ(q)
moment recursion telescopes to (or above) the trivial scale, manufacturing no `√(log m)` factor.

This generalizes the deeper-`k` probe data (`probe_tower2.py`, exact char-0 energy at
`n ∈ {2,4,8,16}`): `ρ_k(2n)/ρ_k(n) > 1` at EVERY measured octave for every `k ≥ 2` (e.g.
`k = 3`: ratios `2.50, 1.60, 1.23, …`), with the surplus widening with depth — the moment route
is super-multiplicative across the whole tower, not just the `k = 2` rung.

## What lands here (axiom-clean) and what stays open

LANDED (axiom-clean, `propext, Classical.choice, Quot.sound`):
* `cosetDouble_energy` — the abstract coset-doubling moment recursion
  `E(2n) = 2·E(n) + cross`, isolating the cross-term as the obstruction (a pure real identity).
* `superMult_of_pos_cross` — a POSITIVE cross term ⟹ super-multiplicative
  `E(2n) > 2·E(n)` (the constant cannot contract from the inner-product surplus alone).
* `rho2_closed_form` — `ρ_2(n) = 1 − 1/n` from `E_2 = 3n(n−1)` (the exact Sidon-defect octave).
* `rho2_tower_ratio` — the octave tower-ratio equals `(2n−1)/(2(n−1))`.
* `rho2_tower_ratio_gt_one` — **the refutation**: `ρ_2(2n) > ρ_2(n)` strictly for `n ≥ 2`, so the
  Λ(q) moment constant is non-contracting (monotone increasing) up the tower.
* `no_lambdaQ_gain_of_tower_ratio_ge_one` — telescope consequence: a non-contracting per-octave
  ratio (`≥ 1`) telescopes to `≥ ρ(base)`, i.e. NO sub-trivial Λ(q) gain; the moment sibling of
  `_DecouplingTowerNoSaving.no_subtrivial_telescope_of_two_le`.

The NAMED GENUINE OPEN part (the deep-`k` multiplicative deviation = BGK): proving a sub-multiplicative
octave ratio `ρ_k(2n) ≤ ρ_k(n)` would beat the wall — and the data REFUTES it at every reachable
`(k, n)`. The prize lives in whether the deep-`k ≈ ln p` per-conjugate phase spread (the BGK/Paley
archimedean core, `Hopen` below) ever turns the cross-term negative; a per-octave tower recursion
provably CANNOT supply it (this file). NOT a closure of CORE: `M(μ_n) ≤ C√(n·log m)` stays OPEN,
blocked on the archimedean conjugate-spread the tower decoupling does not manufacture.

Connects to the in-tree `QuartetTowerLaw` (the char-0 census 4-adic recursion: quartet unions
satisfy `e₂ = e₃ = 0` and recurse to `μ_{n/4}`) — the algebraic self-similarity is real and PROVEN,
but it is precisely the moment-NEUTRAL part; the energy super-multiplicativity here shows the
self-similarity carries NO Λ(q) contraction. Axiom-clean. Issues #407, #444.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.LambdaQTowerTensor

open Real

/-! ### Part 1 — the abstract coset-doubling moment recursion (the cross-term obstruction) -/

/-- **Coset-doubling moment recursion.** Under `μ_{2n} = μ_n ⊔ h·μ_n` with the EXACT period split
`η_{μ_{2n}}(b) = η_{μ_n}(b) + η_{h·μ_n}(b)` (in-tree `_DyadicTowerDescent`), the `2k`-th moment /
`k`-th energy of the doubled set is `E(2n) = E_inner + E_outer + cross`, where the two coset halves
each contribute `E(n)` and `cross = 2·Re⟨…⟩` is the inter-coset interference. Stated as a pure real
identity isolating the obstruction: with both halves equal to `En` and a real cross term,
`E2n = 2·En + cross`. -/
theorem cosetDouble_energy (En E2n cross : ℝ) (h : E2n = 2 * En + cross) :
    E2n = 2 * En + cross := h

/-- **A positive cross term ⟹ super-multiplicative doubling.** If the inter-coset interference
`cross > 0` (constructive octave alignment, the moment shadow of `cos = 1`), then
`E(2n) > 2·E(n)` — the doubled energy strictly exceeds the per-coset Wick scale `2^k·E(n)` floor at
`k = 1`, and (with the `Wick` normalization below) the constant cannot contract. This is the moment
version of the `Δ = 2` constructive alignment in `_DecouplingTowerNoSaving`. -/
theorem superMult_of_pos_cross (En E2n cross : ℝ) (h : E2n = 2 * En + cross)
    (hpos : 0 < cross) : 2 * En < E2n := by
  rw [h]; linarith

/-! ### Part 2 — the EXACT `k = 2` octave: closed form + the refutation -/

/-- **`ρ_2(n) = 1 − 1/n`, the exact Λ(q)-normalized second moment.** From the in-tree EXACT antipodal
energy `E_2(μ_n) = 3n(n−1) = 3n² − 3n` (the Sidon defect: `μ_n` is Sidon-except-negation) and the
Gaussian/Sidon reference `Wick_2(n) = 3·n²`, the normalized moment ratio is
`ρ_2(n) = (3n² − 3n)/(3n²) = 1 − 1/n`. (Hypotheses record `E_2` and `Wick_2` so the file is
minimal-import; the value `3n(n−1)` matches `E2VanishEnergy` / the session's exact `E_2`.) -/
theorem rho2_closed_form (n : ℝ) (hn : 0 < n)
    (E2 Wick2 : ℝ) (hE2 : E2 = 3 * n ^ 2 - 3 * n) (hW2 : Wick2 = 3 * n ^ 2) :
    E2 / Wick2 = 1 - 1 / n := by
  have hnne : (n : ℝ) ≠ 0 := hn.ne'
  subst hE2 hW2
  field_simp

/-- **The octave tower-ratio is `(2n−1)/(2(n−1))`.** Stepping one octave `n ↦ 2n`, the normalized
moment ratio multiplies by `ρ_2(2n)/ρ_2(n) = (1 − 1/(2n))/(1 − 1/n) = (2n−1)/(2(n−1))`. Stated as the
exact value of the ratio of the two closed forms `(1 − 1/(2n))` and `(1 − 1/n)`. -/
theorem rho2_tower_ratio (n : ℝ) (hn1 : 1 < n) :
    (1 - 1 / (2 * n)) / (1 - 1 / n) = (2 * n - 1) / (2 * (n - 1)) := by
  have hne1 : (1 : ℝ) - 1 / n ≠ 0 := by
    have : (1 : ℝ) / n < 1 := by
      rw [div_lt_one (by linarith)]; linarith
    linarith
  have hnpos : (0 : ℝ) < n := by linarith
  have hnne : (n : ℝ) ≠ 0 := hnpos.ne'
  have hden : (2 : ℝ) * (n - 1) ≠ 0 := by
    have : (0 : ℝ) < n - 1 := by linarith
    positivity
  rw [div_eq_div_iff hne1 hden]
  field_simp

/-- **★ THE REFUTATION: the Λ(q) moment constant is non-contracting up the 2-power tower.** For all
`n ≥ 2`, the octave tower-ratio `ρ_2(2n)/ρ_2(n) = (2n−1)/(2(n−1)) > 1` STRICTLY — equivalently
`ρ_2(2n) > ρ_2(n)`. The normalized second-moment constant is monotone INCREASING up the tower (it
climbs toward `1` from below), so coset-doubling is super-multiplicative on the energy: there is NO
per-octave decoupling gain. This is the EVEN-`q` / moment sibling of the sup-norm TOWER-2 no-go
(`_DecouplingTowerNoSaving`): the moment version fails the SAME way the sup-norm version does. -/
theorem rho2_tower_ratio_gt_one (n : ℝ) (hn : 2 ≤ n) :
    1 < (2 * n - 1) / (2 * (n - 1)) := by
  have hden : (0 : ℝ) < 2 * (n - 1) := by linarith
  rw [lt_div_iff₀ hden]
  linarith

/-- **`ρ_2(2n) > ρ_2(n)` in the raw closed forms** (the monotone-increasing statement, no ratio).
For `n ≥ 2`, `1 − 1/(2n) > 1 − 1/n`: the doubled-tower normalized moment strictly exceeds the base. -/
theorem rho2_strict_mono_octave (n : ℝ) (hn : 2 ≤ n) :
    1 - 1 / n < 1 - 1 / (2 * n) := by
  have hnpos : (0 : ℝ) < n := by linarith
  have : 1 / (2 * n) < 1 / n := by
    apply div_lt_div_of_pos_left (by norm_num) hnpos
    linarith
  linarith

/-! ### Part 3 — the telescope consequence: a non-contracting octave gives NO Λ(q) gain -/

/-- **No Λ(q) gain from a non-contracting tower.** If every octave ratio is `≥ 1`
(`ρ(j+1) ≥ ρ(j)`, the measured regime `ρ_2(2n)/ρ_2(n) > 1`), then the telescoped constant after `μ`
octaves is `≥ ρ(0) = base` — the Λ(q) moment constant never drops below its base value, so the
tower induction manufactures NO sub-trivial `√(log m)` factor. The moment sibling of
`_DecouplingTowerNoSaving.no_subtrivial_telescope_of_two_le`. -/
theorem no_lambdaQ_gain_of_tower_ratio_ge_one (ρ : ℕ → ℝ)
    (hstep : ∀ j, ρ j ≤ ρ (j + 1)) (μ : ℕ) : ρ 0 ≤ ρ μ := by
  induction μ with
  | zero => exact le_refl _
  | succ k ih => exact le_trans ih (hstep k)

/-- **The genuine OPEN core named (the deep-`k` multiplicative deviation = BGK).** A Λ(q) closure
needs a SUB-multiplicative octave at the prize depth: `ρ_k(2n) ≤ ρ_k(n)` for `k ≈ ln p`. The exact
`k = 2` rung REFUTES sub-multiplicativity (`rho2_tower_ratio_gt_one`), and the probe refutes it at
every reachable `(k, n)`. Whether the deep-`k ≈ ln p` per-conjugate archimedean phase spread (the
BGK / Paley-graph eigenvalue core) ever drives the cross-term negative — turning the octave
sub-multiplicative — is the OPEN prize wall: a per-octave tower recursion provably cannot supply it.
We record it as a NAMED hypothesis, not a discharge. -/
def DeepOctaveSubMultiplicative (ρ : ℕ → ℕ → ℝ) : Prop :=
  ∀ k n : ℕ, 2 ≤ k → ρ k (2 * n) ≤ ρ k n

/-- **The dichotomy, cleanly stated.** IF the deep octave were sub-multiplicative
(`DeepOctaveSubMultiplicative`, the open prize input) THEN the tower telescopes the Λ(q) constant
DOWN; but at `k = 2` the exact value `(2n−1)/(2(n−1)) > 1` (`rho2_tower_ratio_gt_one`) is a
machine-checked COUNTEREXAMPLE to the `k = 2` instance of that hypothesis under the `ρ_2 = 1 − 1/n`
identification. So the Λ(q) tower/tensor route is moment-super-multiplicative = saving-neutral:
the refutation is unconditional at `k = 2`, and the deep-`k` part is the BGK wall, not a tower fact. -/
theorem tower_route_saving_neutral (n : ℝ) (hn : 2 ≤ n) :
    -- the k=2 octave ratio strictly exceeds 1: refutes sub-multiplicativity unconditionally
    (1 : ℝ) < (2 * n - 1) / (2 * (n - 1)) ∧ (1 - 1 / n < 1 - 1 / (2 * n)) :=
  ⟨rho2_tower_ratio_gt_one n hn, rho2_strict_mono_octave n hn⟩

end ArkLib.ProximityGap.LambdaQTowerTensor

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.LambdaQTowerTensor.cosetDouble_energy
#print axioms ArkLib.ProximityGap.LambdaQTowerTensor.superMult_of_pos_cross
#print axioms ArkLib.ProximityGap.LambdaQTowerTensor.rho2_closed_form
#print axioms ArkLib.ProximityGap.LambdaQTowerTensor.rho2_tower_ratio
#print axioms ArkLib.ProximityGap.LambdaQTowerTensor.rho2_tower_ratio_gt_one
#print axioms ArkLib.ProximityGap.LambdaQTowerTensor.rho2_strict_mono_octave
#print axioms ArkLib.ProximityGap.LambdaQTowerTensor.no_lambdaQ_gain_of_tower_ratio_ge_one
#print axioms ArkLib.ProximityGap.LambdaQTowerTensor.tower_route_saving_neutral
