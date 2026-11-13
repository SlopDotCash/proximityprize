/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26ThornerZaman
-- (the consumer `kkh26_mcaDeltaStar_le_of_TZ` lives in KKH26PolyFieldCeiling; import it only
--  when wiring the final ceiling — keeping it out keeps this lane's iteration fast.)

/-!
# B3 — s=128 prize rows via Thorner–Zaman (#334)

**Target.** Discharge the single analytic hypothesis `TZPrimeSupply n β supply`
(`KKH26ThornerZaman.lean`):

  `le_card : supply ≤ (tzWindow n β).card`

i.e. the window `[n^β, 2·n^β]` contains at least `supply` primes `p ≡ 1 (mod n)`. This is a
**prime-counting lower bound in an arithmetic progression** for the smooth modulus
`n = 2^μ·m` at polynomial field size `p = Θ(n^β)`. Proving it for the s=128 prize parameters
removes the only unproven input of `kkh26_mcaDeltaStar_le_of_TZ`, opening the s=128 rows
(s=64 is already unconditional via the A3 Parseval threshold — see `KKH26ParsevalThreshold`).

**Reference.** [KKH26] ePrint 2026/782, Lemma 2 (the analytic step); [TZ24] Thorner–Zaman
"refined PNT in APs" (log-free Linnik-type lower bound). The unconditional *counting* half
(`card_bigPrimeFactors_le`) is already proven in `KKH26ThornerZaman.lean`.

**Substrate to consume.**
- `KKH26ThornerZaman.TZPrimeSupply` (the structure to construct), `tzWindow`,
  `card_bigPrimeFactors_le` (unconditional prime-factor count).
- `kkh26_mcaDeltaStar_le_of_TZ` (the consumer: feeds your `TZPrimeSupply` → the δ* ceiling).

**Plan.** Either (i) formalize the TZ effective lower bound `π(2x; n, 1) − π(x; n, 1) ≳
x/(φ(n) log x)` for `x = n^β` directly (hard analytic NT, may need a Bombieri–Vinogradov or
Linnik-type input not yet in mathlib — if so, name THAT as a sub-hypothesis), or (ii) for the
specific prize moduli, exhibit `supply` explicit primes (a finite Decidable check — but mind
`native_decide` is banned; use `decide` only if it terminates, else an explicit list with
`Nat.Prime` witnesses). Keep the obligation an explicit `Prop` until a real proof lands.

**Honesty.** `TZPrimeSupply` is the honest named hypothesis. Do NOT assert it as an `axiom`.
-/

-- Replace with `theorem tzPrimeSupply_prize_holds : TZPrimeSupply n β supply := …`
-- for the concrete prize (n, β, supply), or a parametrized sufficient condition.
example : True := trivial
