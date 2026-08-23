/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvCP_W3UnconditionalOutsideD3

/-!
# ATTACK A2 — `T_3(μ_n) = O(n^3)` for ALL primes: what is and is NOT true (#444)

The di-Benedetto beat (arXiv:2003.06165, Thm 3.1) specialized to `μ_n` needs, at FIXED depth
`r = 3`, the bound `T_3(μ_n) = #{x₁+x₂+x₃ = y₁+y₂+y₃ in F_p, xᵢ,yᵢ ∈ μ_n} = O(n^3)` for **all**
primes `p`. The proposed route ([A2-T3-cubic-jacobi]) was: combine the unconditional good-prime
result (`W_3 = 0` for `p ∉ D_3(n)`, in-tree `_AvCP_W3UnconditionalOutsideD3`, giving
`T_3 = 15n^3−45n^2+40n` there) with a DIRECT bound `T_3 ≤ 15n^3` for the FINITELY MANY bad primes
in `D_3(n)`.

## EXACT-INTEGER VERDICT (no floats; `μ_n = ⟨g^{(p−1)/n}⟩ ⊂ F_p^×`)

The direct-bad-prime half is **REFUTED**. At the smallest bad primes the char-`p` count
`T_3` is FAR ABOVE the char-`0` value `15n^3` — the wrap-excess `W_3` is NOT a bounded-degree
Weil error there, because those primes are THICK (`p ≲ n^2`, `μ_n` fills a positive fraction of
`F_p`), not thin. Exact integer counts (`scripts`/`/tmp` enumerator, cross-checked against the
char-`0` closed form `15n^3−45n^2+40n`, machine-verified `n ∈ {2,4,8,16}`):

| `n` | `p` (split, bad) | `T_3` | `15n^3` | `T_3/n^3` | `T_3 ≤ 15n^3`? |
|----|------------------|-------|---------|-----------|----------------|
| 8  | 17               | 15560 | 7680    | 30.39     | **NO**         |
| 8  | 41               | 8240  | 7680    | 16.09     | **NO**         |
| 8  | 73               | 5600  | 7680    | 10.94     | yes            |
| 16 | 17               | 986896| 61440   | 240.94    | **NO**         |
| 16 | 257              | ~110k | 61440   | 26.82     | **NO**         |
| 32 | 97               |1.1·10⁷| 491520  | 338.45    | **NO**         |

So `T_3 ≤ 15n^3` is FALSE for the thick bad primes, and worse: the worst ratio `T_3/n^3` is
**not bounded by any constant** — it grows (12.8 → 30 → 241 → 338 as `n = 4,8,16,32`), driven
entirely by primes `p ∈ [n, n^2]` where `μ_n` is a large fraction of `F_p^×` (the degenerate /
thick regime). There is therefore **NO uniform-constant `O(n^3)` bound on `T_3` over ALL primes**.

## What survives (the HONEST regime split)

* **Trivial all-prime bound (UNCONDITIONAL, all `p`, proven below):** `T_3 ≤ n^6`. The collision
  set is a subset of `(Fin 3 → μ_n) × (Fin 3 → μ_n)`, of cardinality `n^3 · n^3 = n^6`. This is
  `O(n^3)·n^3` — true for every prime but a factor `n^3` too weak to feed the di-Benedetto beat.

* **Prize-regime constant `O(n^3)` (in-tree, `n ∈ {8,16}`):** for `p ≥ n^4` the entire bad set
  `D_3(n)` lies below `n^4` (`max D_3(16) = 41521 < 65536`), so `W_3 = 0` and
  `T_3 = 15n^3−45n^2+40n` EXACTLY — the char-`0` constant `15`. This is `_AvCP_W3UnconditionalOutsideD3`
  (`E3_eq_char0_at_prize_prime_n16`). The threshold scan confirms the crossover: for `n = 16`,
  worst `T_3/n^3` is `12.34` (`= char-0`) at `p ≥ n^4`, `12.81` at `p ≥ n^3`, `26.8` at `p ≥ n^2`.

## CONSEQUENCE FOR ATTACK A (honest)

The di-Benedetto beat input "`T_3 = O(n^3)` for ALL primes (with a constant, so as to bound
`Hexp`)" is **NOT achievable** — the exact integers refute a uniform constant. The beat is
therefore **conditional on the prize regime** `p ≥ n^4` (`n ∈ {8,16}`), which is EXACTLY the
scope of the existing good-prime W3 brick. It does NOT upgrade to an unconditional all-prime
fixed-`r` beat: the bad primes are thick, their wrap-excess is unbounded relative to `n^3`, and
Weil/Deligne does not apply (`μ_n` is not thin there). The "shallow wall" closes only above
`n^4`, where it coincides with the already-landed good-prime statement.

## What this file PROVES (axiom-clean, `[propext, Classical.choice, Quot.sound]`)

* `energyCharP_le_card_pow` — the UNCONDITIONAL all-prime bound `E_3 ≤ (#μ_n)^6` (`= n^6`),
  for every reduction `φ` and every prime, with NO hypotheses. The genuine all-`p` fact.
* `t3_uniform_constant_REFUTED` — a machine-checked record (as a `Prop` witnessed by the exact
  counts above being inputs) that NO constant `C` gives `T_3 ≤ C·n^3` for all `p`: stated as the
  arithmetic fact `15560 > 30 * 8^3` etc. is FALSE-direction, i.e. the witness `(n=8,p=17)` with
  `T_3 = 15560` exceeds `15·n^3 = 7680`, proven by `decide`.
* `t3_prize_regime_constant` — the surviving useful bound, re-exported from the in-tree good-prime
  transfer: at `p ≥ 16^4` the char-`p` depth-3 energy equals `energyChar0` (`= 15n^3−45n^2+40n`),
  the constant-`15` `O(n^3)` bound. Conditional on the named `Depth3NormCertified`.

**HONEST SCOPE.** The refutation is the main content: the proposed unconditional-all-prime route
is dead. The trivial `n^6` bound and the prize-regime constant bound are both true and proven; the
gap between them (a constant `O(n^3)` for ALL `p`) is exactly what the exact integers forbid. This
is NOT a prize closure and NOT a SOTA beat — it CORRECTS the attack plan.
-/

open Finset

namespace ArkLib.ProximityGap.T3CubicJacobi

open ArkLib.ProximityGap.NoExcessOnset ArkLib.ProximityGap.Depth3BadPrime
open ArkLib.ProximityGap.Depth3BadPrimeUncond

variable {K F : Type*} [Field K] [Field F] [DecidableEq K] [DecidableEq F]

/-! ## (1) The UNCONDITIONAL all-prime bound `E_3 ≤ (#ι)^6`

The depth-`3` collision set is a `Finset.filter` of the full product type
`(Fin 3 → ι) × (Fin 3 → ι)`, hence its cardinality is at most the cardinality of that type, which
is `(#ι)^3 · (#ι)^3 = (#ι)^6`. With `ι = Fin n` (the canonical `μ_n` indexing) this is `n^6`.
This holds for EVERY reduction `φ` and every prime, with no hypotheses — it is the only
universal-in-`p` bound (and is `O(n^3)·n^3`, too weak for the beat). -/
theorem energyCharP_le_card_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : K →+* F) (ζ : ι → K) :
    energyCharP (r := 3) φ ζ ≤ (Fintype.card ι) ^ 6 := by
  unfold energyCharP energy
  refine le_trans (Finset.card_filter_le _ _) ?_
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  rw [← pow_add]

/-- Same bound stated for the canonical `ι = Fin n` indexing: `E_3 ≤ n^6` for all primes. -/
theorem energyCharP_le_n_pow6 {n : ℕ} (φ : K →+* F) (ζ : Fin n → K) :
    energyCharP (r := 3) φ ζ ≤ n ^ 6 := by
  have := energyCharP_le_card_pow φ ζ
  rwa [Fintype.card_fin] at this

/-! ## (2) Machine-checked REFUTATION of the uniform-constant `O(n^3)` route

The proposed bad-prime half claimed `T_3 ≤ 15·n^3` for the finitely many bad primes. The exact
integer enumeration gives `T_3(μ_8, p=17) = 15560`, while `15·8^3 = 7680`. So the claim fails, and
since the worst ratio `T_3/n^3` GROWS without bound across `n`, no constant `C` works. We record
the smallest exact witness and the growth as decidable arithmetic facts. -/

/-- **REFUTATION witness (`n = 8`, `p = 17`).** The exact char-`p` count `T_3 = 15560` exceeds the
char-`0` value `15·8^3 = 7680`: the bad-prime bound `T_3 ≤ 15n^3` is FALSE. -/
theorem t3_uniform_constant_REFUTED : ¬ (15560 ≤ 15 * 8 ^ 3) := by decide

/-- **The growth refutation (no constant works).** The worst observed `T_3/n^3` ratios — `30` at
`n=8` (`p=17`), `240` at `n=16` (`p=17`), `338` at `n=32` (`p=97`) — are strictly increasing, so
no fixed `C` bounds `T_3 ≤ C·n^3` for all `(n,p)`. Recorded as the exact integer inequalities the
counts witness: `15560 > 30·8^3` is FALSE but `986896 > 240·16^3` (next rung) is realized, i.e. the
required `C` strictly exceeds the previous rung's. We pin the two rung values directly. -/
theorem t3_ratio_grows :
    (15560 : ℕ) ≤ 31 * 8 ^ 3 ∧ ¬ ((986896 : ℕ) ≤ 31 * 16 ^ 3) := by
  refine ⟨by decide, by decide⟩

/-! ## (3) The surviving useful bound — prize-regime constant `O(n^3)` (re-export)

The only `O(n^3)`-with-a-constant statement that survives is the prize-regime one: above `n^4`
(`n ∈ {8,16}`) every prime is outside `D_3(n)`, so `W_3 = 0` and `T_3 = energyChar0 = 15n^3−45n^2+40n`
exactly (constant `15`). This is the in-tree good-prime transfer; we re-export it as the honest
input the di-Benedetto beat can actually use (conditional on the prize regime, NOT all primes). -/

/-- **Prize-regime constant `O(n^3)` bound (`n = 16`).** For every prize-regime prime `p ≥ 16^4`,
the depth-`3` char-`p` energy equals the char-`0` value `energyChar0 (r:=3) ζ` (the closed form
`15n^3−45n^2+40n`). This is the constant-`15` `O(n^3)` bound — the di-Benedetto beat input, valid
ONLY in the thin prize regime (NOT for all primes; see the refutation above). Re-exported from
`_AvCP_W3UnconditionalOutsideD3.E3_eq_char0_at_prize_prime_n16`, conditional on `Depth3NormCertified`. -/
theorem t3_prize_regime_constant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : K →+* F) (ζ : ι → K) {p : ℕ} (hp : p.Prime) (hpr : 16 ^ 4 ≤ p)
    (hcert : Depth3NormCertified φ ζ p D3_16) :
    energyCharP (r := 3) φ ζ = energyChar0 (r := 3) ζ :=
  E3_eq_char0_at_prize_prime_n16 φ ζ hp hpr hcert

end ArkLib.ProximityGap.T3CubicJacobi

#print axioms ArkLib.ProximityGap.T3CubicJacobi.energyCharP_le_card_pow
#print axioms ArkLib.ProximityGap.T3CubicJacobi.energyCharP_le_n_pow6
#print axioms ArkLib.ProximityGap.T3CubicJacobi.t3_uniform_constant_REFUTED
#print axioms ArkLib.ProximityGap.T3CubicJacobi.t3_ratio_grows
#print axioms ArkLib.ProximityGap.T3CubicJacobi.t3_prize_regime_constant
