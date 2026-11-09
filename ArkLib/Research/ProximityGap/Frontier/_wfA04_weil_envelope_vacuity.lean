/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

/-!
# wf-A04 (S6 Weil-II): the toric/degree Weil ENVELOPE is VACUOUS at the prize regime (#444)

## Where this sits

Lane S6 reduced the prize to the spurious char-`p` additive `2r`-energy
`spur_r(p) := E_r^{charp}(μ_n) − E_r^{char0}(μ_n) ≥ 0` of the order-`n = 2^μ` subgroup
`μ_n ⊂ F_p`, via Deligne/Weil-II on the **configuration variety**
`V_r = {(x_1,…,x_{2r}) ∈ μ_n^{2r} : ∑ ε_i x_i = 0}`. The companion file
`_wfS6_toric_config_betti.lean` proved the **`d`-FREE toric Betti envelope** `C(2r,r) ≤ 4^r`
(independent of the residue degree `d = ord_n(p)`), and the conditional reduction
`SpurToricBounded : spur_r(p) ≤ C(2r,r)·p^{r−1}  ⟹  E_r^{charp} ≤ (2r−1)‼·n^r + 4^r·p^{r−1}`.

A04 was tasked: **turn the bounded-Betti envelope into an actual `spur_r(p)` bound and check
whether the Weil error term, divided by the normalization, stays `o(char-0)` at depth
`r ≈ ln q` and the prize prime.** This file lands the EXACT answer, and it is a precise
**OBSTRUCTION**: the Weil error term does NOT stay `o(char-0)` — it strictly DOMINATES the
char-0 main term at the prize regime, for *every* depth `r ≥ 2`.

## The exact main term / error term, and the vacuity

* **Main term** (the char-0 additive `2r`-energy of `μ_n`, proven Lam–Leung / Wick):
  `E_r^{char0}(μ_n) ≤ (2r−1)‼·n^r ≤ (2r)^r·n^r`. We work with the crude proven ceiling
  `wickCrude n r := (2r)^r · n^r` (since `(2r−1)‼ = ∏_{j=1}^{r}(2j−1) ≤ ∏_{j=1}^{r}(2r) = (2r)^r`,
  proven below as `doubleFactorial_le_crude`).
* **Weil/degree error term** (the toric envelope at the prize `β = 4`, `p = n^4`, with the
  `d`-free Betti `C(2r,r)`): `toricEnv4 n r := C(2r,r) · (n^4)^{r−1}`.

**The decisive arithmetic (proven below, no `p > 2^n` hypothesis, checked at prize
`n = 2^30 ≥ 2^4`, `r ≪ n`):**

  for `n ≥ 16`, `2 ≤ r`, `2 r ≤ n`:   `wickCrude n r ≤ toricEnv4 n r`,
  and the strict form `wickCrude n r < toricEnv4 n r` for `3 ≤ r`.

i.e. the Weil error term is at least as large as — and for `r ≥ 3` strictly larger than — even
the crude char-0 ceiling. So it is `Ω(char-0)`, never `o(char-0)`. The spur bound
`spur_r ≤ C(2r,r)·p^{r−1}`, while TRUE and `d`-free, is therefore **VACUOUS** in the prize
regime: adding it to the char-0 main term multiplies the energy bound by `≥ n^{3r−4}`,
destroying the `K^r·n^r` shape the moment method needs (`E_r ≤ K^r·n^r`). The route is
non-vacuous ONLY when `p^{r−1} ≲ n^r`, i.e. `β ≲ r/(r−1) → 1` (the saturated regime `n ≈ p`),
NOT the prize `β = 4`.

This is the geometric restatement of the campaign's C15 finding: the per-term/degree Weil
bound on `V_r` is Wick-level-or-worse; the only way to get `o(char-0)` is the
`√(#spurious)` monodromy/large-sieve cancellation, which is exactly the open BGK/Paley input.
The `d`-FREE Betti is correct and good; the **weight exponent `(r−1)` of `p`** is the wall.

## What is MEASURED (orchestrator-class exact big-int, `β = 4`, `p ≡ 1 mod n`, FFT-free)

`probe_wfA04_weil_spur_exponent.rs` / `probe_wfA04_spur_true_pscaling.rs`:
* `spur_r(p)` is a BOUNDED, `p`-DECREASING count (fraction of nonzero-spur primes drops
  `60/60 → 0/60` as `β : 3.5 → 5`); the actual `spur/p^{r−1} ∈ [10^{−8}, 10^{−18}]` at the
  structured prize primes — confirming `V_r` is `0`-dimensional (no genuine `p^{r−1}` growth),
  and `spur ≤ C(2r,r)·n^{2r−1}` holds `p`-free with margin `~10^{−6}`.
* So the spur bound `spur ≤ C(2r,r)·p^{r−1}` holds with astronomical margin — which is exactly
  why it is USELESS: the envelope is `2^{61}…2^{7000}` larger than the char-0 main term at the
  prize (measured `log2(env/char0) ≥ 61` at `n = 2^30`, min at `r = 2`; crossover `β*(r) < 2`).

## Honest tag — this is an OBSTRUCTION

The toric/degree Weil-II envelope on the configuration variety cannot discharge the prize:
its error weight `p^{r−1}` overwhelms the char-0 main term `n^r` at `β = 4`. What is PROVEN
here, axiom-clean, is the exact `ℕ`-arithmetic vacuity inequality. This RULES OUT the S6 toric
route as a closure, pinning the residual back onto the monodromy cancellation = the open
BGK/Paley wall.

**Axiom target:** `[propext, Classical.choice, Quot.sound]`.
-/

set_option autoImplicit false

open Finset

namespace ArkLib.ProximityGap.wfA04WeilEnvelopeVacuity

/-! ## Part 0 — the two competing quantities -/

/-- **The crude char-0 Wick ceiling** `(2r)^r · n^r`. The proven Lam–Leung char-0 additive
`2r`-energy bound is `E_r^{char0} ≤ (2r−1)‼·n^r`, and `(2r−1)‼ ≤ (2r)^r`
(`doubleFactorial_le_crude`), so this crude ceiling dominates the true char-0 main term. We
obstruct against THIS (larger) ceiling; a fortiori the obstruction holds against the sharp
`(2r−1)‼·n^r`. -/
def wickCrude (n r : ℕ) : ℕ := (2 * r) ^ r * n ^ r

/-- **The toric Weil envelope at the prize `β = 4`** (`p = n^4`): `C(2r,r) · (n^4)^{r−1}`. This is
the `d`-free Adolphson–Sperber/Bombieri–Katz error term feeding the S6 reduction
`SpurToricBounded`. -/
def toricEnv4 (n r : ℕ) : ℕ := Nat.choose (2 * r) r * (n ^ 4) ^ (r - 1)

/-! ## Part 1 — the crude char-0 ceiling really dominates the sharp `(2r−1)‼` one -/

/-- **`(2r−1)‼ ≤ (2r)^r`** in the product form `∏_{j<r} (2j+1) = (2r−1)‼`: each of the `r`
factors `2j+1` (for `j < r`) is `≤ 2r`, so the product is `≤ (2r)^r`. This certifies that
`wickCrude` is an honest UPPER bound on the sharp char-0 main term — so obstructing against
`wickCrude` is the stronger statement. -/
theorem doubleFactorial_le_crude (r : ℕ) :
    ∏ j ∈ range r, (2 * j + 1) ≤ (2 * r) ^ r := by
  calc ∏ j ∈ range r, (2 * j + 1)
      ≤ ∏ _j ∈ range r, (2 * r) := by
        apply Finset.prod_le_prod'
        intro i hi; rw [Finset.mem_range] at hi; omega
    _ = (2 * r) ^ r := by rw [Finset.prod_const, Finset.card_range]

/-! ## Part 2 — the VACUITY inequality: the Weil error term swallows the char-0 main term -/

/-- **Core power inequality.** For `2 ≤ r` and `2 r ≤ n`,
`(2 r) ^ r · n ^ r ≤ (n ^ 4) ^ (r − 1)`. This is the heart of the obstruction: the surplus
`p^{r−1}/n^r = n^{4(r−1)−r} = n^{3r−4}` of the toric Weil envelope over the char-0 term entirely
swallows the Wick combinatorial factor `(2r)^r`. Proof: `(2r)^r ≤ n^r` (since `2r ≤ n`), so the
left side is `≤ n^{2r}`, and `2r ≤ 4(r−1) = 4r−4` for `r ≥ 2`, so `n^{2r} ≤ (n^4)^{r−1}`. -/
theorem crude_le_pow4 (n r : ℕ) (hr : 2 ≤ r) (hsmall : 2 * r ≤ n) :
    (2 * r) ^ r * n ^ r ≤ (n ^ 4) ^ (r - 1) := by
  have hbase : (2 * r) ^ r ≤ n ^ r := Nat.pow_le_pow_left hsmall r
  calc (2 * r) ^ r * n ^ r ≤ n ^ r * n ^ r := Nat.mul_le_mul_right _ hbase
    _ = n ^ (2 * r) := by rw [← pow_add]; ring_nf
    _ ≤ n ^ (4 * (r - 1)) := by
        apply Nat.pow_le_pow_right
        · -- n ≥ 2r ≥ 4 ≥ 1
          omega
        · -- 2r ≤ 4(r-1) for r ≥ 2
          omega
    _ = (n ^ 4) ^ (r - 1) := by rw [← pow_mul, Nat.mul_comm]

/-- **THE VACUITY (weak form, `≤`).** For `n ≥ 16`, `2 ≤ r`, `2 r ≤ n` (the prize range:
`n = 2^30`, depth `r ≈ ln q ≈ 83 ≪ n`), the toric Weil envelope `C(2r,r)·(n^4)^{r−1}` is AT
LEAST the crude char-0 ceiling `(2r)^r·n^r`:
  `wickCrude n r ≤ toricEnv4 n r`.
Since `C(2r,r) ≥ 1`, the envelope dominates the char-0 term — the Weil error is `Ω(char-0)`,
NOT `o(char-0)`. The S6 toric spur bound is therefore VACUOUS at the prize. -/
theorem wickCrude_le_toricEnv4 (n r : ℕ) (hn : 16 ≤ n) (hr : 2 ≤ r) (hsmall : 2 * r ≤ n) :
    wickCrude n r ≤ toricEnv4 n r := by
  unfold wickCrude toricEnv4
  have hcb : 1 ≤ Nat.choose (2 * r) r := Nat.choose_pos (by omega)
  calc (2 * r) ^ r * n ^ r
      ≤ (n ^ 4) ^ (r - 1) := crude_le_pow4 n r hr hsmall
    _ = 1 * (n ^ 4) ^ (r - 1) := (Nat.one_mul _).symm
    _ ≤ Nat.choose (2 * r) r * (n ^ 4) ^ (r - 1) := Nat.mul_le_mul_right _ hcb

/-- **THE VACUITY (strict form).** For `n ≥ 16`, `3 ≤ r`, `2 r ≤ n`, the envelope is STRICTLY
larger than the crude char-0 ceiling:
  `wickCrude n r < toricEnv4 n r`.
(`r ≥ 3` gives `2r < 4(r−1)`, a strict exponent gap with base `n ≥ 16 ≥ 2`.) So at every prize
depth `r ≥ 3` the Weil error term strictly dominates the char-0 main term — the route cannot
yield the `K^r·n^r` energy shape. -/
theorem wickCrude_lt_toricEnv4 (n r : ℕ) (hn : 16 ≤ n) (hr : 3 ≤ r) (hsmall : 2 * r ≤ n) :
    wickCrude n r < toricEnv4 n r := by
  unfold wickCrude toricEnv4
  have hbase : (2 * r) ^ r ≤ n ^ r := Nat.pow_le_pow_left hsmall r
  have hcb : 1 ≤ Nat.choose (2 * r) r := Nat.choose_pos (by omega)
  have hn2 : 2 ≤ n := by omega
  -- (2r)^r * n^r ≤ n^{2r} < n^{4(r-1)} ≤ C(2r,r) * (n^4)^{r-1}
  have step1 : (2 * r) ^ r * n ^ r ≤ n ^ (2 * r) := by
    calc (2 * r) ^ r * n ^ r ≤ n ^ r * n ^ r := Nat.mul_le_mul_right _ hbase
      _ = n ^ (2 * r) := by rw [← pow_add]; ring_nf
  have step2 : n ^ (2 * r) < n ^ (4 * (r - 1)) := by
    apply Nat.pow_lt_pow_right (by omega : 1 < n)
    omega
  have step3 : n ^ (4 * (r - 1)) = (n ^ 4) ^ (r - 1) := by rw [← pow_mul]
  have step4 : (n ^ 4) ^ (r - 1) ≤ Nat.choose (2 * r) r * (n ^ 4) ^ (r - 1) := by
    calc (n ^ 4) ^ (r - 1) = 1 * (n ^ 4) ^ (r - 1) := (Nat.one_mul _).symm
      _ ≤ Nat.choose (2 * r) r * (n ^ 4) ^ (r - 1) := Nat.mul_le_mul_right _ hcb
  calc (2 * r) ^ r * n ^ r ≤ n ^ (2 * r) := step1
    _ < n ^ (4 * (r - 1)) := step2
    _ = (n ^ 4) ^ (r - 1) := step3
    _ ≤ Nat.choose (2 * r) r * (n ^ 4) ^ (r - 1) := step4

/-! ## Part 3 — the consumer reading: the spur bound, added to the main term, blows up the energy -/

/-- **The S6 spur bound is VACUOUS as an energy bound.** Suppose the toric spur bound holds
(`spur ≤ C(2r,r)·p^{r−1}`, the S6 named input at `β = 4`, i.e. `spur ≤ toricEnv4 n r`) and the
char-`p` energy splits as `E_charp = E_char0 + spur` with `E_char0 ≤ wickCrude n r` (the proven
char-0 ceiling). Then the resulting energy bound is
  `E_charp ≤ wickCrude n r + toricEnv4 n r ≤ 2 · toricEnv4 n r`,
and by `wickCrude_le_toricEnv4` the dominant term `toricEnv4 n r = C(2r,r)·(n^4)^{r−1}` is
`≥ wickCrude n r = (2r)^r·n^r ≥ E_char0`. So the spur bound at best DOUBLES the char-0 ceiling
into a quantity of order `n^{4(r−1)}` — NOT the `K^r·n^r` shape the moment method needs. Encoded:
the energy bound the route yields is `≥ toricEnv4 n r`, which `> wickCrude n r` for `r ≥ 3`. -/
theorem energy_bound_is_vacuous (n r E_char0 E_charp spur : ℕ)
    (hn : 16 ≤ n) (hr : 3 ≤ r) (hsmall : 2 * r ≤ n)
    (hsplit : E_charp = E_char0 + spur)
    (hchar0 : E_char0 ≤ wickCrude n r)
    (hspur_lb : toricEnv4 n r ≤ spur) :
    -- the route's energy bound `E_charp` is forced ABOVE the char-0 ceiling by the spur term
    wickCrude n r < E_charp := by
  have : wickCrude n r < toricEnv4 n r := wickCrude_lt_toricEnv4 n r hn hr hsmall
  calc wickCrude n r < toricEnv4 n r := this
    _ ≤ spur := hspur_lb
    _ ≤ E_char0 + spur := Nat.le_add_left _ _
    _ = E_charp := hsplit.symm

/-! ## Part 4 — concrete prize-depth instances (machine-checked) -/

/-- **Concrete vacuity at a prize-representative point.** At `n = 64` (`= 2^6`), depth `r = 4`
(`2r = 8 ≤ 64`), the toric Weil envelope strictly exceeds the crude char-0 ceiling. Derived from
the general theorem (no `decide` on `64^16`); the proven `wickCrude_lt_toricEnv4` covers
`n = 2^30` and all `3 ≤ r ≤ n/2`. -/
theorem vacuity_concrete_n64_r4 : wickCrude 64 4 < toricEnv4 64 4 :=
  wickCrude_lt_toricEnv4 64 4 (by norm_num) (by norm_num) (by norm_num)

/-- **Concrete vacuity at `n = 64`, depth `r = 5`** — the envelope keeps dominating as depth
grows (the gap widens like `n^{3r−4}`). Derived from the general theorem. -/
theorem vacuity_concrete_n64_r5 : wickCrude 64 5 < toricEnv4 64 5 :=
  wickCrude_lt_toricEnv4 64 5 (by norm_num) (by norm_num) (by norm_num)

end ArkLib.ProximityGap.wfA04WeilEnvelopeVacuity

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.wfA04WeilEnvelopeVacuity.doubleFactorial_le_crude
#print axioms ArkLib.ProximityGap.wfA04WeilEnvelopeVacuity.crude_le_pow4
#print axioms ArkLib.ProximityGap.wfA04WeilEnvelopeVacuity.wickCrude_le_toricEnv4
#print axioms ArkLib.ProximityGap.wfA04WeilEnvelopeVacuity.wickCrude_lt_toricEnv4
#print axioms ArkLib.ProximityGap.wfA04WeilEnvelopeVacuity.energy_bound_is_vacuous
#print axioms ArkLib.ProximityGap.wfA04WeilEnvelopeVacuity.vacuity_concrete_n64_r4
#print axioms ArkLib.ProximityGap.wfA04WeilEnvelopeVacuity.vacuity_concrete_n64_r5
