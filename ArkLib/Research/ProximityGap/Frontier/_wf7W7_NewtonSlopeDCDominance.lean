/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-W7)
-/
import Mathlib

/-!
# Conditional arithmetic reduction: `Spur_r ≤ n^{2r}/p` (assumed) plus the char-`0` floor gives
  `A_r ≤ Wick` with `K = 1` (#444, lane wf-W7)

**Scope.** Every theorem in this file is a one-step `ring`/`linarith` rearrangement of real
numbers.  The headline `A_r ≤ Wick` is **conditional** on the assumed dominance
`Spur_r ≤ n^{2r}/p` (`NPSlopeZeroDominance`), which is open; nothing here proves it.  The
Newton-polygon language below is motivational only: no Newton polygon, valuation, or
configuration count is formalised, and the quantities `DC_r`, `GEN_r` are real numbers, not
segment masses or config counts.

## Setting

`p` prime, `n = 2^μ ∣ p − 1`, `μ_n` the order-`n` subgroup of `𝔽_p^×`, `η_b = Σ_{x∈μ_n} e_p(bx)`.
The **DC-subtracted** `2r`-moment is

  `A_r(μ_n) = (1/p) Σ_{b≠0} η_b^{2r} = E_r − n^{2r}/p`,
  `E_r = #{(x,y)∈μ_n^{2r} : Σx = Σy mod p}`,

and the char-`0` floor `E_r^{(0)} := #{antipodal-matched configs} ≤ (2r−1)‼·n^r =: Wick` is **PROVEN
in tree** (`DyadicEnergyK1`, Lam–Leung). The TARGET (Wick bound) is `A_r ≤ K^r · Wick` at `r ~ ln q`.

## The bookkeeping (definitions, not a decomposition theorem)

Set
  • `Spur_r := E_r − E_r^{(0)}` (a nonnegative integer count: the char-`p` configs that are not
     char-`0` antipodal matchings);
  • `DC_r := n^{2r}/p` (the trivial-character term subtracted in `A_r`; in general **not** an
     integer, so not a configuration count or segment mass);
  • `GEN_r := A_r − E_r^{(0)} = Spur_r − DC_r` (a **difference** of a count and a real number; it
     can be — and in the probes is — negative, so it is not a "mass").

Then `A_r = E_r^{(0)} + GEN_r` by definition, and

  `A_r ≤ Wick   ⟺   GEN_r ≤ Wick − E_r^{(0)}`,   and in particular   `GEN_r ≤ 0 ⟹ A_r ≤ E_r^{(0)} ≤ Wick`.

(Heuristic motivation, not formalised: each config gives `σ = Σ ±ζ_n^{i} ∈ ℤ[ζ_n]`, and sorting
by `p`-adic valuation of `N(σ)` suggests a Newton-polygon picture; this file does not use it.)

## What the band-depth pre-screen ESTABLISHES (the new W7 finding)

`scripts/probes/rust/wf7W7_dc_vs_genuine_spur.rs`, `wf7W7_n64_check.rs` (EXACT, prize scale `p ≍ n^β`,
`β ∈ {3,4,5}`, `n ∈ {16,32,64}`, depth `r` THROUGH the optimal `r* ≈ ln q / 2`):

  `GEN_r = A_r − E_r^{(0)} < 0` at **every** measured row, INCLUDING at and beyond `r*`,
  with `|GEN_r|/Wick` GROWING with `r` (more slack at deeper bands): e.g.
    n=16,β=4: GEN/Wick `−8.9e-3 → −1.7e-2 → −1.8e-2` (r=4,6(=r*),7);
    n=32,β=3: `−0.150 → −0.243(r*) → −0.309` (r=4,5,6);
    n=64,β=3: A_r/Wick `0.98 → 0.92 → 0.81 → 0.65` (r=2..5), GEN<0 throughout.

So, numerically, the DC term `n^{2r}/p` exceeds `Spur_r` — i.e. `Spur_r ≤ n^{2r}/p` with strict
margin at the measured rows — and the DC-subtracted moment falls strictly BELOW the char-`0` Wick
floor. If this persisted uniformly it would give `K = 1`; that is the open crux, not a result. (Contrast lane W6: `Spur_r/Wick` itself GROWS
unboundedly — but that is dominated by exactly the DC term that `A_r` subtracts.)

## What is PROVEN here (axiom-clean ℝ arithmetic)

* `Ar_eq_charzero_add_gen` — the ring identity `A_r = E_r^{(0)} + GEN_r` (definitional
  rearrangement of `A_r = E_r − DC_r` and `GEN_r = (E_r − DC_r) − E_r^{(0)}`).
* `gen_le_zero_iff_spur_le_dc` — `GEN_r ≤ 0 ⟺ Spur_r ≤ DC_r` (one `linarith` step).
* **`wick_bound_K1_of_dc_dominance`** — CONDITIONAL: *assuming* `Spur_r ≤ DC_r` (`= GEN_r ≤ 0`)
  and the in-tree char-`0` Wick floor `E_r^{(0)} ≤ Wick`, conclude `A_r ≤ Wick` (one `linarith`
  step).  The dominance hypothesis is the open crux.
* `moment_sup_K1` — the moment→sup consequence at `K = 1`: `A_r ≤ Wick ⟹ max_b‖η_b‖ ≤ (p·Wick)^{1/2r}`
  (the prize square-root shape with the absolute constant `K = 1`).
* `dc_dominance_uniform_of_pointwise` — uniformity packaging: a pointwise `Spur_r(p) ≤ DC_r(p)` over
  prize primes transports to the uniform Wick-`K1` bound (worst-prime reduction).

## The PRECISE remaining open step (the W7 crux)

  `(W7-crux: NP slope-0 DC-dominance)`   `Spur_r(p) ≤ n^{2r}/p`   uniformly over prize primes
  `p ≍ n^β`, at band depth `r ~ ln q`,

i.e. the count `Spur_r = E_r − E_r^{(0)}` is at most the real number `n^{2r}/p`. The pre-screen verifies this exactly with growing margin for `n ≤ 64`, `β ≤ 5`, `r ≤ r*`; the open
content is the uniform `n = 2^30` transfer. This is a SHARPER, `K=1` target than the lane-W4/W6
relative-count `(S-W4)`/`(S-W6)`: it asserts not that `Spur_r` is small relative to `Wick`, but that
`Spur_r` is dominated by the *explicitly subtracted* DC term — exactly the quantity that `A_r`
removes. (The Newton-polygon "slope-`≥1` vs slope-`0` segment" phrasing is heuristic only.)

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. #444.
- Stevenhagen–Lenstra, *Chebotarëv and his density theorem* (the `(1−ζ)`-adic valuation / Newton
  polygon mechanism; cf. in-tree `_ChebotarevValuationModP.lean`).
- Lam–Leung, *On vanishing sums of roots of unity* (the char-`0` antipodal floor `E_r^{(0)} ≤ Wick`).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


namespace ArkLib.ProximityGap.Frontier.WF7W7

open scoped BigOperators

/-! ### §1  The bookkeeping identity `A_r = E_r^{(0)} + GEN_r` (a ring identity). -/

/-- The DC-subtracted moment `A_r = E_r − DC_r`, the difference `GEN_r := A_r − E0` (a real number,
possibly negative), and `Spur_r := E_r − E0` satisfy `A_r = E0 + GEN_r` and `GEN_r = Spur_r − DC_r`.
(A ring identity in arbitrary reals `Er, E0, DC`; `DC = n^{2r}/p` is generally not an integer.) -/
theorem Ar_eq_charzero_add_gen (Er E0 DC : ℝ) :
    (Er - DC) = E0 + ((Er - DC) - E0) := by ring

/-- **Dominance reformulation (one `linarith` step).** With `Spur_r = E_r − E0` and
`DC_r = n^{2r}/p`, the difference `GEN_r = (E_r − DC_r) − E0` is `≤ 0` **iff** `Spur_r ≤ DC_r`. -/
theorem gen_le_zero_iff_spur_le_dc (Er E0 DC : ℝ) :
    ((Er - DC) - E0) ≤ 0 ↔ (Er - E0) ≤ DC := by
  constructor <;> intro h <;> linarith

/-! ### §2  Conditional: assumed DC-dominance ⟹ the Wick bound with `K = 1`. -/

/-- **`wick_bound_K1_of_dc_dominance`** — conditional arithmetic step.

ASSUMING `Spur_r ≤ DC_r` (equivalently `GEN_r ≤ 0`; observed numerically in the pre-screen, open in
general) and the in-tree char-`0` Wick floor `E0 ≤ Wick`, the DC-subtracted moment satisfies
`A_r = E_r − DC_r ≤ Wick`.  The proof is `linarith`; all content is in the hypotheses. -/
theorem wick_bound_K1_of_dc_dominance (Er E0 DC Wick : ℝ)
    (hdc : (Er - E0) ≤ DC)        -- NP slope-dominance:  Spur_r ≤ DC_r  (= GEN_r ≤ 0)
    (hwick : E0 ≤ Wick) :         -- char-0 Lam–Leung floor (in tree, DyadicEnergyK1)
    (Er - DC) ≤ Wick := by
  -- A_r = E_r − DC ≤ E0 ≤ Wick.
  have : (Er - DC) ≤ E0 := by linarith
  linarith

/-- **Moment→sup at `K = 1`.** If `A_r ≤ Wick` and the raw-moment identity `p·A_r = Σ_{b≠0} η_b^{2r}`
holds with `M^{2r} ≤ p·A_r` (`M = max_{b≠0}‖η_b‖`, the standard sup-by-`2r`-moment step), then
`M ≤ (p·Wick)^{1/2r}` — the prize square-root envelope with the **absolute** constant `K = 1`.
Stated as the clean monotone inequality on the `2r`-th powers (the `rpow` step is wf-M4's). -/
theorem moment_sup_K1 (M2r p Ar Wick : ℝ)
    (hM : M2r ≤ p * Ar) (hp : 0 ≤ p) (hAr : Ar ≤ Wick) :
    M2r ≤ p * Wick := by
  have : p * Ar ≤ p * Wick := by
    apply mul_le_mul_of_nonneg_left hAr hp
  linarith

/-! ### §3  Uniformity over prize primes (worst-prime reduction). -/

/-- **`dc_dominance_uniform_of_pointwise`.** The NP DC-dominance is a *pointwise* hypothesis on each
prize prime; if it holds for the prime `p` (with that prime's exact counts `Er p`, `DC p`) and the
char-`0` floor is `p`-independent (`E0 ≤ Wick`, the Lam–Leung bound carries no `p`), the Wick-`K1`
bound `A_r(p) ≤ Wick` holds for that `p`. Quantifying over all prize primes gives the uniform bound
`∀ p ∈ Prize, A_r(p) ≤ Wick`. -/
theorem dc_dominance_uniform_of_pointwise {ι : Type*} (Prize : Set ι)
    (Er DC : ι → ℝ) (E0 Wick : ℝ)
    (hdc : ∀ p ∈ Prize, (Er p - E0) ≤ DC p)
    (hwick : E0 ≤ Wick) :
    ∀ p ∈ Prize, (Er p - DC p) ≤ Wick := by
  intro p hp
  exact wick_bound_K1_of_dc_dominance (Er p) E0 (DC p) Wick (hdc p hp) hwick

/-! ### §4  The named open crux as a `Prop` (the modularity convention). -/

/-- **`NPSlopeZeroDominance`** (the named W7 open crux). For a prize prime `p ≍ n^β` and band depth
`r ~ ln q`, the count `Spur_r(p) = E_r(p) − E_r^{(0)}` is at most the real number `n^{2r}/p`
(the name's "Newton-polygon slope-0" reading is heuristic):  `E_r(p) − E0 ≤ n^{2r}/p`. Pre-screened EXACT with growing
margin for `n ≤ 64`, `β ≤ 5`, `r ≤ r*` (`wf7W7_*` probes); the open content is the uniform `n = 2^30`
transfer. Consuming this with the in-tree char-`0` floor `E0 ≤ Wick` discharges `A_r ≤ Wick` (K=1)
via `wick_bound_K1_of_dc_dominance` — the prize moment bound. Named, never `sorry`-ed. -/
def NPSlopeZeroDominance (Er E0 : ℝ) (n p : ℝ) (r : ℕ) : Prop :=
  Er - E0 ≤ n ^ (2 * r) / p

/-- The named crux is *exactly* the hypothesis of the headline bound: granting it (and the in-tree
char-`0` floor) yields `A_r ≤ Wick` with `K = 1`.  This is a conditional reduction; the crux is
assumed, not proved. -/
theorem prize_wick_K1_of_crux (Er E0 Wick n p : ℝ) (r : ℕ)
    (hCrux : NPSlopeZeroDominance Er E0 n p r)
    (hwick : E0 ≤ Wick) :
    (Er - n ^ (2 * r) / p) ≤ Wick :=
  wick_bound_K1_of_dc_dominance Er E0 (n ^ (2 * r) / p) Wick hCrux hwick

end ArkLib.ProximityGap.Frontier.WF7W7

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.WF7W7.Ar_eq_charzero_add_gen
#print axioms ArkLib.ProximityGap.Frontier.WF7W7.gen_le_zero_iff_spur_le_dc
#print axioms ArkLib.ProximityGap.Frontier.WF7W7.wick_bound_K1_of_dc_dominance
#print axioms ArkLib.ProximityGap.Frontier.WF7W7.moment_sup_K1
#print axioms ArkLib.ProximityGap.Frontier.WF7W7.dc_dominance_uniform_of_pointwise
#print axioms ArkLib.ProximityGap.Frontier.WF7W7.prize_wick_K1_of_crux
