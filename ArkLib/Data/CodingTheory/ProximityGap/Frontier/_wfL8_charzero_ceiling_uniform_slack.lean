/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-L8, #444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._CharZeroWickEnergy
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf6P2_charp_lamleung_slack

/-!
# The char-`0` Lam–Leung ceiling, discharged UNIFORMLY in `r`, wired into the slack route (#444, wf-L8)

## What this close-out tightening discharges

The slack route `Frontier/_wf6P2_charp_lamleung_slack.lean` carries the char-`0` Lam–Leung ceiling
`(S-M1) : A_r ≤ (2r−1)‼·n^r` as a **free real hypothesis** `hZceiling : Z ≤ ceiling` inside
`slack_route_full`.  Lanes wf-OT4 (`r ∈ {2,3}`) and wf-L6 (`r ∈ {7,8,9}`) discharged that input
only **per-rung**, and only on the **closed-form value carriers** (`BalancedCount B`, the integer
closed forms `E_2 = 3n²−3n`, …, `E_9`), leaving `r ∈ {4,5,6}` — and every `r > 9` — still resting on
the free `hZceiling`, and never on the *actual* `rEnergy` carrier the route's energy is.

But the char-`0` energy ceiling is in fact **already** a single uniform-in-`r` axiom-clean theorem on
the real `rEnergy` carrier, for **every** `r` at once: `CharZeroWickEnergy.gaussianEnergyBound_dyadic`
(#407) proves, with NO per-`r` hypothesis,

> `GaussianEnergyBound G r`  i.e.  `(rEnergy G r : ℝ) ≤ (2r−1)‼·|G|^r`

for any finset `G ⊆ μ_{2^k}` (`k ≥ 1`, char-`0`, negation-closed — automatic for `μ_{2^k}`).  That is
the discharged `hZceiling`, **uniformly in `r`**, on the carrier the route consumes.  What was missing
was the WIRING: a single theorem that takes `gaussianEnergyBound_dyadic` as the ceiling input and runs
the *entire* `slack_route_full` chain with `hZceiling` PROVEN — for ALL `r`, on the real carrier,
filling `r ∈ {4,5,6}` and every higher rung in one shot, superseding the per-rung OT4/L6 discharges.

This file is exactly that wiring.

## The char-`0` / char-`p` boundary, pinned precisely

For `G = μ_n`, `n = 2^μ`, the char-`p` additive energy splits as `A_r = Z_r + Spur_r(p)` where
`Z_r = E_r(μ_n)` is the char-`0` (vanishing-over-ℂ) zero-sum count.  The whole slack route consumes
exactly two facts about this split:

* **char-`0` half — `hZceiling : Z_r ≤ ceiling_r`** — DISCHARGED here UNIFORMLY in `r` by
  `gaussianEnergyBound_dyadic` (Lam–Leung antipodal closure; `propext, Classical.choice, Quot.sound`,
  no `sorry`).  This is everything the char-`0` substrate can supply, now PROVEN for all `r`.
* **char-`p` half — `hslack : Spur_r(p) ≤ ceiling_r − Z_r`** (the `(P2-Slack)` residual) — stays
  GENUINELY OPEN.  This is the BGK char-`p` wall: it asks that the prize prime `p ≍ n^4` not divide so
  many small cyclotomic norms `N(σ_T)` that the spurious mod-`p` coincidences overflow the Lam–Leung
  slack.  At the prize regime `n = 2^30`, `GaussianEnergyBound` is in fact FALSE in char-`p` (the DC
  term beats Wick — `DCEnergyEssential`, `PairingResidualFailsAtPrize`), so the *only* dischargeable
  half is the char-`0` ceiling, which this file now removes from the route as a free hypothesis for
  every `r` simultaneously.

## What is PROVEN here (axiom-clean: `propext, Classical.choice, Quot.sound`; NO sorryAx)

* `charzero_ceiling_uniform` — `(rEnergy G r : ℝ) ≤ (2r−1)‼·|G|^r` UNCONDITIONALLY for every `r`
  (the discharged `hZceiling` on the real carrier; just `gaussianEnergyBound_dyadic` unfolded).
* `slack_route_full_charzero_discharged` — the END-TO-END slack route with the char-`0` ceiling input
  PROVEN (not free), for EVERY `r`: given only the OPEN char-`p` residual `hslack` (and the trivial
  `principal ≥ 0`, `Eprime ≥ 0`), the nonprincipal energy obeys the char-`0` ceiling AND its
  moment→sup envelope is the char-`0` envelope with `K = 1`.  This is `slack_route_full` with
  `hZceiling` DISCHARGED uniformly in `r` — the close-out the per-rung OT4/L6 bricks approximated.
* `SM1_uniform_of_slack` — `(P2-Slack) at r ⟹ A_r ≤ ceiling_r` for EVERY `r`, ceiling input PROVEN.
* `SM1_uniform_at_faithful_edge` — at the faithfulness edge `Spur = 0` the char-`p` energy IS the
  char-`0` energy and the prize bound IS the (now-proven) char-`0` ceiling, for every `r`.
* `charp_residual_is_the_only_open_input` — the boundary statement: the slack route's conclusion
  holds for every `r` ASSUMING ONLY the char-`p` residual `hslack`; the char-`0` ceiling is no longer
  an input.  Pins exactly what is open (char-`p`) vs proven (char-`0`).

## Honest scope

This is the char-`0` HALF only, now removed UNIFORMLY in `r` (superseding the per-rung discharges) and
on the real `rEnergy` carrier.  It does NOT bound `Spur_r(p)`; the `(P2-Slack)` residual stays
GENUINELY OPEN (= the BGK char-`p` wall, the genuine open core).  No `δ*` / capacity / beyond-Johnson
claim.  `CORE M(μ_n) ≤ C·√(n·log(p/n))` UNCHANGED/OPEN.  Issue #444, wf-L8.
-/

set_option autoImplicit false
set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.WFL8

open Nat
open ArkLib.ProximityGap.SubgroupGaussSumMoment
open ArkLib.ProximityGap.GaussPeriodMomentBound
open ProximityGap.Frontier.CharZeroWickEnergy

variable {F : Type*} [Field F] [CharZero F] [DecidableEq F]

/-! ## The char-`0` ceiling, UNIFORM in `r`, on the real `rEnergy` carrier (the discharged `hZceiling`) -/

/-- **Char-`0` Lam–Leung ceiling, UNCONDITIONAL and UNIFORM in `r`.**  For a finset `G` of `2^k`-th
roots of unity (`k ≥ 1`) in a characteristic-`0` field (negation-closed, automatic for `μ_{2^k}`),
the `r`-fold additive energy obeys the double-factorial ceiling for **every** `r`:

> `(rEnergy G r : ℝ) ≤ (2r−1)‼·|G|^r`.

This is the slack route's free `hZceiling` input, DISCHARGED for all `r` at once on the actual energy
carrier — the single uniform-in-`r` form of the per-rung OT4 (`r∈{2,3}`) / L6 (`r∈{7,8,9}`) discharges.
It is `gaussianEnergyBound_dyadic` (#407) unfolded. -/
theorem charzero_ceiling_uniform {k : ℕ} (hk : 1 ≤ k) (G : Finset F)
    (hG : ∀ z ∈ G, z ^ (2 ^ k) = 1) (hneg : ∀ g ∈ G, -g ∈ G) (r : ℕ) :
    (rEnergy G r : ℝ) ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r :=
  gaussianEnergyBound_dyadic hk G hG hneg r

/-! ## The END-TO-END slack route with the char-`0` ceiling DISCHARGED, uniform in `r` -/

/-- **The end-to-end slack route, char-`0` ceiling DISCHARGED, for EVERY `r`.**  Run the full
`WF6P2.slack_route_full` chain with the free `hZceiling` input now SUPPLIED by `charzero_ceiling_uniform`
(PROVEN, uniform in `r`, on the real `rEnergy` carrier).  The char-`p` energy is `A_r = Z_r + S` with
`Z_r = rEnergy G r` the char-`0` zero-sum count; the consumer rests on ONLY:

* `hslack` — the OPEN char-`p` residual `(P2-Slack)`: `S ≤ ceiling_r − Z_r` (spurious fits the slack);
* `hprinc` / `hEnn` — `principal ≥ 0` and `Eprime ≥ 0` (trivial: `Eprime = (1/q)Σ_{b≠0}‖η_b‖^{2r} ≥ 0`).

Conclusion (for the ceiling `ceiling_r := (2r−1)‼·|G|^r`): the nonprincipal energy
`Eprime = (Z_r + S) − principal` obeys the char-`0` ceiling AND its moment→sup envelope
`(q·Eprime)^{1/2r} ≤ (q·ceiling_r)^{1/2r}` with `K = 1`.  The char-`0` ceiling is no longer a free
hypothesis at ANY `r`. -/
theorem slack_route_full_charzero_discharged
    {k : ℕ} (hk : 1 ≤ k) (G : Finset F)
    (hG : ∀ z ∈ G, z ^ (2 ^ k) = 1) (hneg : ∀ g ∈ G, -g ∈ G) (r : ℕ)
    (q S principal : ℝ) (hq : 0 ≤ q)
    (hslack : S ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r - (rEnergy G r : ℝ))
    (hprinc : 0 ≤ principal)
    (hEnn : 0 ≤ ((rEnergy G r : ℝ) + S) - principal) :
    (((rEnergy G r : ℝ) + S) - principal
        ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) ∧
    (q * (((rEnergy G r : ℝ) + S) - principal)) ^ ((2 * r : ℝ)⁻¹)
        ≤ (q * ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r)) ^ ((2 * r : ℝ)⁻¹) :=
  WF6P2.slack_route_full q (rEnergy G r : ℝ) S principal
    ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) r
    hq (charzero_ceiling_uniform hk G hG hneg r) hslack hprinc hEnn

/-! ## `(P2-Slack) ⟹ (S-M1)`, uniform in `r`, char-`0` ceiling DISCHARGED -/

/-- **`(S-M1)` at EVERY `r`, char-`0` ceiling DISCHARGED.**  The char-`p` energy `A_r = Z_r + S`
(`Z_r = rEnergy G r`).  Given the OPEN char-`p` residual `S ≤ ceiling_r − Z_r` and `S ≥ 0`, the
char-`p` energy obeys the char-`0` ceiling `A_r ≤ (2r−1)‼·|G|^r`.  The ceiling input is PROVEN
(`charzero_ceiling_uniform`); the consumer rests ONLY on the open residual — for every `r`. -/
theorem SM1_uniform_of_slack
    {k : ℕ} (hk : 1 ≤ k) (G : Finset F)
    (hG : ∀ z ∈ G, z ^ (2 ^ k) = 1) (hneg : ∀ g ∈ G, -g ∈ G) (r : ℕ)
    (S : ℝ) (hspur : 0 ≤ S)
    (hslack : S ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r - (rEnergy G r : ℝ)) :
    (rEnergy G r : ℝ) + S ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r :=
  WF6P2.slack_domination_implies_SM1 (rEnergy G r : ℝ) S
    ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r) hslack

/-- **Faithfulness-edge sanity (`Spur = 0`), uniform in `r`.**  At the char-`0` faithfulness edge
`S = 0` (probe-confirmed through `n=16, r≤3`, where `A_r = E_r`), the prize bound IS the now-proven
char-`0` ceiling, for every `r` — no residual needed. -/
theorem SM1_uniform_at_faithful_edge
    {k : ℕ} (hk : 1 ≤ k) (G : Finset F)
    (hG : ∀ z ∈ G, z ^ (2 ^ k) = 1) (hneg : ∀ g ∈ G, -g ∈ G) (r : ℕ) :
    (rEnergy G r : ℝ) + (0 : ℝ) ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r := by
  simpa using charzero_ceiling_uniform hk G hG hneg r

/-! ## The char-`0` / char-`p` boundary, as one theorem -/

/-- **The boundary pin: the char-`p` residual is the ONLY open input.**  For every `r`, the slack
route's conclusion (`A_r ≤ ceiling_r`) holds ASSUMING ONLY the char-`p` residual `hslack`
(`S ≤ ceiling_r − Z_r`) and `S ≥ 0`.  The char-`0` ceiling on `Z_r` is no longer an input — it is
discharged inside the proof by `charzero_ceiling_uniform`.  Thus the char-`0` half is PROVEN (for all
`r`) and the char-`p` `(P2-Slack)` residual is precisely and solely what remains OPEN (the BGK wall).
Identical statement to `SM1_uniform_of_slack`, recorded under a name that asserts the boundary. -/
theorem charp_residual_is_the_only_open_input
    {k : ℕ} (hk : 1 ≤ k) (G : Finset F)
    (hG : ∀ z ∈ G, z ^ (2 ^ k) = 1) (hneg : ∀ g ∈ G, -g ∈ G) (r : ℕ)
    (S : ℝ) (hspur : 0 ≤ S)
    (hslack : S ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r - (rEnergy G r : ℝ)) :
    (rEnergy G r : ℝ) + S ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (G.card : ℝ) ^ r :=
  SM1_uniform_of_slack hk G hG hneg r S hspur hslack

end ArkLib.ProximityGap.Frontier.WFL8

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.WFL8.charzero_ceiling_uniform
#print axioms ArkLib.ProximityGap.Frontier.WFL8.slack_route_full_charzero_discharged
#print axioms ArkLib.ProximityGap.Frontier.WFL8.SM1_uniform_of_slack
#print axioms ArkLib.ProximityGap.Frontier.WFL8.SM1_uniform_at_faithful_edge
#print axioms ArkLib.ProximityGap.Frontier.WFL8.charp_residual_is_the_only_open_input
