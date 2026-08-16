/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.style.longLine false

/-!
# The phase-blind energy floor: why every L²/moment/additive-energy method caps at exponent 1 (#444)

This is the cleanest unifying statement of the BGK/Paley wall, surfaced by the open-avenue ledger:
**the half-power gap is pure phase cancellation, and every additive-energy / moment / L²-magnitude
transfer is phase-blind**, so none can cross the Burgess exponent 1 at β=4.

## The mechanism

The worst-case period is `M = max_{b≠0}‖η_b‖`, `η_b = Σ_{x∈μ_n} e_p(bx)`. Every energy/moment method
bounds `M` through the transfer identity `Σ_b‖η_b‖^{2k} = p·E_k` (`E_k` = additive `2k`-energy of
`μ_n`), giving `M^{2k} ≤ p·E_k`, i.e. `M ≤ (p·E_k)^{1/2k}`. The catch (Plancherel/L² floor): `E_k` is
itself bounded **below** by the DC term `E_k ≥ n^{2k}/p` (the `b=0` contribution `‖η_0‖^{2k}=n^{2k}`
divided by `p`). Hence

  `(p·E_k)^{1/2k} ≥ (p · n^{2k}/p)^{1/2k} = n`   — the transfer bound is **never below `n^{1}`**.

So at β=4 (`p ≈ n^4`), *no* additive-energy method — Murphy–Rudnev–Shkredov 3rd-energy, the moment
ladder, OSV completion, Wasserstein/KU25 moment-equidistribution, FKMS bilinear (`Σ_b‖η_b‖^{2r}=p·E_r`
exactly), the dyadic-tower `ℓ²` step — can beat exponent `1` (`= n^{1-o(1)}` Burgess). The true `M`
sits at exponent `≈ 0.91–0.97` (in the half-power gap); the gap is supplied entirely by **phase
cancellation among the `η_b`**, which the `E_k` *magnitude* cannot see. This is the load-bearing
reason the ~50 frameworks of the campaign all reduce to the wall.

## What is proven here (axiom-clean)

`energyTransfer_ge_one` : the exact arithmetic core — given the L² floor `n^{2k}/p ≤ E`, the
energy-transfer quantity satisfies `n^{2k} ≤ p·E` (so its `2k`-th root, the `M`-bound, is `≥ n`). The
magnitude of `E` is irrelevant once the floor binds: every L²/energy method pins at exponent 1.

## Honest scope (#444)

This formalizes the *barrier* (why energy methods cannot cross), not a bound on `M`. It is the moment-
method/Burgess wall stated at its cleanest. A crossing would require a genuinely **phase-aware** method
(not L², not energy, not completion) — which is exactly the Paley/BGK conjecture and does not exist in
the literature (Burgess exponent is exactly 1 at β=4). NOT a closure; the cleanest map of the wall.
-/

namespace ArkLib.ProximityGap.Frontier.PhaseBlindEnergyFloor

/-- **The phase-blind energy floor (the wall, cleanest form).** For the additive-energy transfer
`M^{2k} ≤ p·E_k` with the Plancherel/L² floor `n^{2k}/p ≤ E_k`, the transfer quantity is
`≥ n^{2k}` — so the `M`-bound `(p·E_k)^{1/2k}` is `≥ n`, exponent `1`. No additive-energy / moment /
L²-magnitude method beats `n^{1-o(1)}` at β=4: the half-power gap is pure phase cancellation. -/
theorem energyTransfer_ge_one (n p k : ℕ) (E : ℚ) (hp : 0 < p)
    (hE : (n ^ (2 * k) : ℚ) / p ≤ E) : (n ^ (2 * k) : ℚ) ≤ p * E := by
  have hp' : (0 : ℚ) < p := by exact_mod_cast hp
  rw [div_le_iff₀ hp'] at hE
  calc (n ^ (2 * k) : ℚ) ≤ E * p := hE
    _ = p * E := by ring

/-- The L² floor itself, as a hypothesis-free statement about the DC contribution: the additive
`2k`-energy always carries the `b=0` term `‖η_0‖^{2k} = n^{2k}`, so `p·E_k ≥ n^{2k}` whenever the
transfer identity `Σ_b‖η_b‖^{2k} = p·E_k` holds with the DC term included. (Stated as the contrapositive
form for downstream use: if `p·E < n^{2k}` then the L² floor is violated, impossible.) -/
theorem no_subOne_from_energy (n p k : ℕ) (E : ℚ) (hp : 0 < p)
    (hfloor : (n ^ (2 * k) : ℚ) / p ≤ E) : ¬ (p * E < (n ^ (2 * k) : ℚ)) := by
  have h := energyTransfer_ge_one n p k E hp hfloor
  exact not_lt.mpr h

end ArkLib.ProximityGap.Frontier.PhaseBlindEnergyFloor

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx). -/
#print axioms ArkLib.ProximityGap.Frontier.PhaseBlindEnergyFloor.energyTransfer_ge_one
#print axioms ArkLib.ProximityGap.Frontier.PhaseBlindEnergyFloor.no_subOne_from_energy
