/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.StepanovWeilSqrtCorollary

/-!
# The explicit `√q` Weil count: instantiating the Stepanov–Weil engine at `M = ⌊√q⌋` (#444)

`StepanovWeilSqrtCorollary.weil_stepanov_card_le_one` discharged the auxiliary multiplicity
`ℓ = 1` and divided the proven Stepanov–Weil engine through by the Hasse multiplicity `M`,
landing in the standard normal form

> `|V| ≤ (((q−1)/2)·d + (q−1)) / M`   under   `|V|·M < 2(A+1)`,  `2A + d < q`,  `0 < M`,

but its doc-comment named the remaining elementary continuation explicitly: *"The `√q` value
still requires plugging the explicit `M`."*  This file removes that named continuation by taking
the **Stepanov-optimal multiplicity** `M := ⌊√q⌋` (`Nat.sqrt q`) and discharging the divided
bound to an explicit closed form in `q, d`:

> **`weil_stepanov_card_le_sqrt`** — for `g` squarefree, `deg g = d > 0`, `q = |F|` odd,
> `2A + d < q`, and the `M = ⌊√q⌋` construction-dimension condition `|V|·⌊√q⌋ < 2(A+1)`,
> the root/Hasse set satisfies  `|V| ≤ (d + 2)·⌊√q⌋`.

This is the classical `O_d(√q)` Weil count made fully explicit on the proven engine: the
leading term `(d+2)·⌊√q⌋ ≤ (d+2)·√q` is exactly the `O_d(√q)` Stepanov–Weil bound (the
`(d/2)·√q` asymptotic, here in a clean integer envelope valid at *every* finite `q`).

The arithmetic core is `divided_le_sqrt` (below): `(((q−1)/2)·d + (q−1)) / ⌊√q⌋ ≤ (d+2)·⌊√q⌋`,
which holds because `⌊√q⌋² ≤ q < (⌊√q⌋+1)²` forces `q − 1 ≤ ⌊√q⌋² + 2⌊√q⌋`, and then
`((q−1)/2)·d + (q−1) ≤ (d+2)·⌊√q⌋²` (probe-confirmed tight at `q = 3`, `d = 1`, where both
sides equal `3`).

## Honest scope (rules 1, 3, 6)

A specialization of the proven `weil_stepanov_card_le_one` at `M := Nat.sqrt q`, NOT a CORE
closure.  The classical `√q` Weil bound it now states explicitly is the **trivial completion
ceiling** for the thin subgroup `μ_n` (`M(μ_n) ≤ √q`), the upper end of the proven bracket
`[√n, √q]`; the prize `√(n·log(q/n))` lives strictly below it and is **NOT** reached by
Weil/Stepanov on the full character (thinness-blind).  This is plumbing on the proven
analytic-NT engine — it removes the file's own named open continuation and gives the engine an
explicit `O_d(√q)` head — and is **thinness-blind by construction**, therefore explicitly NOT a
thinness-essential CORE lever.  No moment/census/orbit/geometric-minor re-derivation, no
capacity/beyond-Johnson/growth-law claim, cliff-at-`n/2` untouched.
CORE `M(μ_n) ≤ C·√(n·log(p/n))` stays OPEN.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Polynomial

namespace ArkLib.ProximityGap.StepanovWeilEngine

variable {F : Type*} [Field F] [Fintype F]

/-- **The arithmetic core.** With `M := Nat.sqrt q` the divided Stepanov threshold
`D₀ = ((q−1)/2)·d + (q−1)` satisfies `D₀ / M ≤ (d + 2)·M`.  Proof: `M² ≤ q < (M+1)²` gives
`q ≤ M² + 2M`, hence `q − 1 ≤ M² + 2M − 1` and `((q−1)/2)·d + (q−1) ≤ (d+2)·M²`; dividing by
`M` (`Nat.le_div_iff_mul_le` is unnecessary — `Nat.div_le_iff_le_mul_add_pred`/`omega` on the
multiplied form) closes it. -/
theorem divided_le_sqrt (q d : ℕ) (hq : 0 < q) :
    (((q - 1) / 2) * d + (q - 1)) / Nat.sqrt q ≤ (d + 2) * Nat.sqrt q := by
  set M := Nat.sqrt q with hM
  have hMpos : 0 < M := Nat.sqrt_pos.mpr hq
  -- M² ≤ q  and  q < (M+1)²
  have hlo : M * M ≤ q := Nat.sqrt_le q
  have hhi : q < (M + 1) * (M + 1) := by
    have := Nat.lt_succ_sqrt q
    simpa [hM, Nat.succ_eq_add_one] using this
  -- q ≤ M² + 2M  (from q < M² + 2M + 1)
  have hq_le : q ≤ M * M + 2 * M := by nlinarith [hhi]
  -- core nat inequality: D₀ ≤ (d+2)·M².  Double everything to clear the halving, then a clean
  -- chain  2·D₀ = (2h)·d + 2(q-1) ≤ (q-1)(d+2) ≤ (M²+2M)(d+2) ≤ 2M²(d+2)  [last step: 2M ≤ M²+1].
  have hcore : ((q - 1) / 2) * d + (q - 1) ≤ (d + 2) * (M * M) := by
    set h := (q - 1) / 2 with hh
    have h2 : h * 2 ≤ q - 1 := Nat.div_mul_le_self _ _
    -- 2·D₀ ≤ (q-1)·(d+2)
    have step1 : 2 * (h * d + (q - 1)) ≤ (q - 1) * (d + 2) := by
      have hpd : (h * 2) * d ≤ (q - 1) * d := Nat.mul_le_mul_right d h2
      nlinarith [hpd]
    -- q-1 ≤ 2M²  :  from q ≤ M²+2M (hq_le) and 2M ≤ M²+1 ⇐ (M-1)² ≥ 0 (tight at M=1, q=3)
    have h2M : 2 * M ≤ M * M + 1 := by nlinarith [hMpos]
    have hq2M2 : q - 1 ≤ 2 * (M * M) := by omega
    -- (q-1)·(d+2) ≤ 2M²·(d+2)
    have step2 : (q - 1) * (d + 2) ≤ (2 * (M * M)) * (d + 2) :=
      Nat.mul_le_mul_right _ hq2M2
    -- chain and halve
    have hfin : 2 * (h * d + (q - 1)) ≤ 2 * ((d + 2) * (M * M)) := by
      calc 2 * (h * d + (q - 1)) ≤ (q - 1) * (d + 2) := step1
        _ ≤ (2 * (M * M)) * (d + 2) := step2
        _ = 2 * ((d + 2) * (M * M)) := by ring
    omega
  -- divide by M:  D₀ / M ≤ (d+2)·M   since D₀ ≤ (d+2)·M·M
  have hdvd : ((q - 1) / 2) * d + (q - 1) ≤ ((d + 2) * M) * M := by
    calc ((q - 1) / 2) * d + (q - 1) ≤ (d + 2) * (M * M) := hcore
      _ = ((d + 2) * M) * M := by ring
  exact Nat.div_le_of_le_mul (by simpa [Nat.mul_comm] using hdvd)

/-- **The explicit `√q` Stepanov–Weil count.** Instantiating `weil_stepanov_card_le_one` at the
Stepanov-optimal multiplicity `M := Nat.sqrt q` and discharging the divided threshold via
`divided_le_sqrt` gives the classical `O_d(√q)` Weil bound in fully explicit closed form:
`|V| ≤ (deg g + 2)·⌊√q⌋`. -/
theorem weil_stepanov_card_le_sqrt
    (g : F[X]) (hg : Squarefree g) (hdeg : 0 < g.natDegree)
    (hq_odd : Odd (Fintype.card F)) (A : ℕ)
    (hAq : 2 * A + g.natDegree < Fintype.card F)
    (V : Finset F)
    (hdim : V.card * Nat.sqrt (Fintype.card F) < 2 * (A + 1)) :
    V.card ≤ (g.natDegree + 2) * Nat.sqrt (Fintype.card F) := by
  classical
  set q := Fintype.card F with hq
  have hqpos : 0 < q := Fintype.card_pos
  have hMpos : 0 < Nat.sqrt q := Nat.sqrt_pos.mpr hqpos
  have hbase :=
    weil_stepanov_card_le_one g hg hdeg hq_odd A hAq V (Nat.sqrt q) hMpos hdim
  exact hbase.trans (divided_le_sqrt q g.natDegree hqpos)

end ArkLib.ProximityGap.StepanovWeilEngine

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.StepanovWeilEngine.weil_stepanov_card_le_sqrt
