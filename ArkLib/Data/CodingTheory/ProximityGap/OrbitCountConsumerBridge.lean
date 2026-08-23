/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OrbitCountCrossingLaw
import ArkLib.Data.CodingTheory.ProximityGap.BridgeLoop44

/-!
# Orbit-count consumer bridge (#407) — discharging the hypothesized MCA inequality

The `BridgeLoop43`/`BridgeLoop44` MCA prize reductions each take a **hypothesized** real-number
inequality `Vcard ≤ N·S` (the bad-challenge count is at most `#orbits · orbit-size`).  This was a
placeholder for the Action–Orbit factorization.  Meanwhile `OrbitCountCrossingLaw` proves the
**exact** orbit-count identity `|B| = (#orbits)·S` (`card_eq_orbitCount_mul_size`) from the
constant-orbit-size partition that `ActionOrbitFRI.badSet_orbit_closed` supplies.

This file wires the two together: it casts the exact ℕ identity to the real inequality and feeds it
into the consumers, **removing the hypothesized inequality**.  After this bridge, the only remaining
hypothesis in the MCA reductions is the genuinely-open orbit-count *bound* (`N ≤ K` constant, or
`N ≤ (2^m)^d` polynomial) — the inequality `Vcard ≤ N·S` itself is now a theorem, not an assumption.

It also records the prize's extremal **coprime direction** strengthening: when `gcd(b−a,n)=1` the
orbit size is the full domain `S = n`, and the crossing law degenerates to `I_pencil ≤ n ⟺ N ≤ 1`
— δ* for the primitive pencil is exactly where the bad-α set collapses to a *single*
`⟨ω^{b−a}⟩`-orbit.

## What is formalized here (axiom-clean, no `sorry`)

* `orbitCount_card_le_real` — cast bridge: exact ℕ identity `|B| = N·S` ⟹ `(|B|:ℝ) ≤ N·S` (the
  consumer hypothesis, discharged with no slack since it is really an equality).
* `mca_prize_of_orbit_partition` — `BridgeLoop43.mca_prize_of_bounded_orbit_count` with `hcard`
  discharged: from the orbit partition + the open *constant* bound `N ≤ K`, `|B|/q² ≤ K/q`.
* `mca_prize_of_orbit_partition_poly` — `BridgeLoop44.mca_prize_of_poly_orbit_count` with `hcard`
  discharged: from the orbit partition + the open *polynomial* bound `N ≤ (2^m)^d`,
  `|B|/q² ≤ (1/q)·(2^m)^{d+1}`.
* `coprime_crossing_law` / `coprime_pencil_crossing_law` — the `gcd(b−a,n)=1` specialization:
  `|B| ≤ n ⟺ N ≤ 1`.
* `coprime_single_orbit_at_budget` — the threshold boundary case (`N = 1`, `|B| = n`).

## Honest scope

This is a **REFORMULATION / plumbing** step, identical in spirit to `OrbitCountCrossingLaw`.  It
turns the *hypothesized* MCA inequality `Vcard ≤ N·S` into a *proven* consequence of the
Action–Orbit partition.  It does **NOT** establish the open content — that the orbit count `N`
stays `≤ poly(n)` (let alone `O(1)`) at constant rate in the small-gap window.  That bound (the
crux `Q2`/poly-orbit-count residual) remains the live research question; here we only ensure that
*if* such a bound is supplied, the MCA prize shape follows with no remaining placeholder inequality.
-/

open Finset

namespace ArkLib.ProximityGap.OrbitCountConsumerBridge

open ArkLib.ProximityGap.OrbitCountCrossingLaw
open ArkLib.ProximityGap.BridgeLoop43
open ArkLib.ProximityGap.BridgeLoop44

variable {ι : Type*} [DecidableEq ι]

/-! ### Step 1 — the cast bridge: exact ℕ orbit-count identity ⟹ real inequality -/

/-- The exact orbit-count identity `|B| = N·S` (ℕ), cast to the real-number inequality
`(|B| : ℝ) ≤ N·S` that the `BridgeLoop43/44` MCA consumers take as a *hypothesis*.  Because the
identity is an *equality*, the cast inequality holds with no slack — the consumer hypothesis is
*discharged*, not merely bounded. -/
theorem orbitCount_card_le_real
    (B : Finset ι) (rep : ι → ι) (S : ℕ)
    (hmap : ∀ a ∈ B, rep a ∈ B)
    (hfib : ∀ u ∈ B.image rep, (B.filter (fun a => rep a = u)).card = S) :
    (B.card : ℝ) ≤ ((B.image rep).card : ℝ) * (S : ℝ) := by
  have hidNat : B.card = (B.image rep).card * S :=
    card_eq_orbitCount_mul_size B rep S hmap hfib
  have hidR : (B.card : ℝ) = ((B.image rep).card : ℝ) * (S : ℝ) := by
    rw [hidNat]; push_cast; ring
  exact le_of_eq hidR

/-! ### Step 2 — discharge the `BridgeLoop43` constant-orbit-count MCA consumer -/

/-- **`mca_prize_of_bounded_orbit_count` with its hypothesized inequality DISCHARGED.**
`BridgeLoop43.mca_prize_of_bounded_orbit_count` takes the *hypothesized* real inequality
`Vcard ≤ N·S`.  Here we supply it from the proven exact orbit-count identity
`card_eq_orbitCount_mul_size` (the Action–Orbit factorization), so the only remaining hypothesis is
the genuinely-open orbit-count *bound* `N ≤ K`.  Conclusion: the MCA term `|B|/q²` is at most the
Conjecture-1.1 prize shape `K/q`. -/
theorem mca_prize_of_orbit_partition
    (B : Finset ι) (rep : ι → ι) (S : ℕ)
    (hmap : ∀ a ∈ B, rep a ∈ B)
    (hfib : ∀ u ∈ B.image rep, (B.filter (fun a => rep a = u)).card = S)
    {q K : ℝ} {m : ℕ}
    (hq : 0 < q) (hKnn : 0 ≤ K)
    (hN : ((B.image rep).card : ℝ) ≤ K) (hS : (S : ℝ) ≤ (2 : ℝ) ^ m)
    (hqbig : (2 : ℝ) ^ m ≤ q) :
    (B.card : ℝ) / q ^ 2 ≤ K / q := by
  have hSnn : (0 : ℝ) ≤ (S : ℝ) := by positivity
  exact mca_prize_of_bounded_orbit_count hq hKnn hSnn
    (orbitCount_card_le_real B rep S hmap hfib) hN hS hqbig

/-! ### Step 3 — discharge the `BridgeLoop44` POLYNOMIAL-orbit-count MCA consumer -/

/-- **`mca_prize_of_poly_orbit_count` with its hypothesized inequality DISCHARGED.**
`BridgeLoop44.mca_prize_of_poly_orbit_count` takes the *hypothesized* real inequality
`Vcard ≤ N·S`; we supply it from the exact orbit-count identity.  The only remaining hypothesis is
the genuinely-open *polynomial* orbit-count bound `N ≤ (2^m)^d`.  Conclusion: `|B|/q²` lands on the
weaker prize RHS `(1/q)·(2^m)^{d+1}`. -/
theorem mca_prize_of_orbit_partition_poly
    (B : Finset ι) (rep : ι → ι) (S : ℕ)
    (hmap : ∀ a ∈ B, rep a ∈ B)
    (hfib : ∀ u ∈ B.image rep, (B.filter (fun a => rep a = u)).card = S)
    {q : ℝ} {m d : ℕ}
    (hq : 1 ≤ q)
    (hN : ((B.image rep).card : ℝ) ≤ ((2 : ℝ) ^ m) ^ d) (hS : (S : ℝ) ≤ (2 : ℝ) ^ m) :
    (B.card : ℝ) / q ^ 2 ≤ (1 / q) * ((2 : ℝ) ^ m) ^ (d + 1) := by
  have hSnn : (0 : ℝ) ≤ (S : ℝ) := by positivity
  have hNnn : (0 : ℝ) ≤ ((B.image rep).card : ℝ) := by positivity
  exact mca_prize_of_poly_orbit_count hq hSnn hNnn
    (orbitCount_card_le_real B rep S hmap hfib) hN hS

/-! ### Step 4 — the coprime-direction STRENGTHENING of the crossing law

The prize's extremal monomial direction has `gcd(b−a, n) = 1` (a primitive pencil): then the orbit
size is the *full* domain `S = n` and the supply identity is `S·1 = n`.  The crossing law then
degenerates to: the budget test `I_pencil ≤ n` holds *iff there is a single orbit* `N ≤ 1`.  So δ*
for that pencil is **exactly where the bad-α orbit count drops to one orbit**. -/

/-- **Coprime crossing law (`d = 1`).**  When `gcd(b−a,n) = 1`, the orbit size is `S = n` and
`|B| = N·n`.  The budget test `|B| ≤ n` is then equivalent to `N ≤ 1`: a single bad-α orbit. -/
theorem coprime_crossing_law
    {Bcard N n : ℕ} (hn : 0 < n) (hid : Bcard = N * n) :
    Bcard ≤ n ↔ N ≤ 1 := by
  have := crossing_law (S := n) (d := 1) (n := n) hn (by simp) hid
  simpa using this

/-- **Assembled coprime pencil crossing law.**  From the orbit partition with the *full-domain*
orbit size `S = n` (the `gcd(b−a,n)=1` extremal direction), the per-pencil budget test on the
bad-α count `I_pencil = |B|` is equivalent to *the orbit count being a single orbit* `N ≤ 1`.
This pins δ* for the primitive pencil to the radius where the bad set collapses to one
`⟨ω^{b−a}⟩`-orbit. -/
theorem coprime_pencil_crossing_law
    (B : Finset ι) (rep : ι → ι) (n : ℕ) (hn : 0 < n)
    (hmap : ∀ a ∈ B, rep a ∈ B)
    (hfib : ∀ u ∈ B.image rep, (B.filter (fun a => rep a = u)).card = n) :
    B.card ≤ n ↔ (B.image rep).card ≤ 1 :=
  coprime_crossing_law hn (card_eq_orbitCount_mul_size B rep n hmap hfib)

/-- **Single-orbit ⟹ within budget (coprime direction).**  In the extremal `gcd(b−a,n)=1`
direction, a single bad-α orbit (`N = 1`, `|B| = n`) is *exactly* at the per-pencil budget `n`:
the boundary case of the crossing law. -/
theorem coprime_single_orbit_at_budget
    {Bcard n : ℕ} (hn : 0 < n) (hid : Bcard = 1 * n) :
    Bcard ≤ n :=
  (coprime_crossing_law hn hid).mpr le_rfl

/-! ### Non-vacuity / sanity -/

/-- A genuine concrete coprime instance: `B = {0,1,2,3}` is one full-domain orbit of size `n = 4`
(rep ≡ 0, `N = 1`).  The coprime crossing law equivalence holds: `|B| = 4 ≤ 4 = n` iff the orbit
count `N = 1 ≤ 1`, both true at the threshold. -/
example :
    (({0, 1, 2, 3} : Finset ℕ).card ≤ 4)
      ↔ ((({0, 1, 2, 3} : Finset ℕ).image (fun _ => 0)).card ≤ 1) := by
  apply coprime_pencil_crossing_law ({0,1,2,3} : Finset ℕ) (fun _ => 0) 4 (by decide)
  · intro a ha; fin_cases ha <;> decide
  · intro u hu; fin_cases hu; decide

end ArkLib.ProximityGap.OrbitCountConsumerBridge

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.OrbitCountConsumerBridge.orbitCount_card_le_real
#print axioms ArkLib.ProximityGap.OrbitCountConsumerBridge.mca_prize_of_orbit_partition
#print axioms ArkLib.ProximityGap.OrbitCountConsumerBridge.mca_prize_of_orbit_partition_poly
#print axioms ArkLib.ProximityGap.OrbitCountConsumerBridge.coprime_crossing_law
#print axioms ArkLib.ProximityGap.OrbitCountConsumerBridge.coprime_pencil_crossing_law
#print axioms ArkLib.ProximityGap.OrbitCountConsumerBridge.coprime_single_orbit_at_budget
