/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-S4 frontier — Galois ORBIT-partition law for spurious configs)
-/
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# wf-S4 — the Galois ORBIT-partition law: per-prime count is UNIFORM = (#orbits) (#444)

This sharpens `_wfS4_galois_perprime_spread.lean`. That file proves the Fubini identity
`Σ_a perPrime a = Σ_T spread T` and, in the measured `spread ≡ 1` regime, that the total incidence
equals the number of landing configs. **This file proves the exact `(n/2)×` SPREAD LAW behind the
prize CONCENTRATION mechanism** by adding the *orbit-transitivity* structure that the probes
measured, abstracted to its combinatorial core.

## The exact measured law (probe `probe_wfS4_perprime_law.py`, EXACT, prize-shaped `p ≍ n^β`)

`p ≡ 1 mod n` splits completely in `ℤ[ζ_n]` into the `φ(n) = n/2` primes `𝔭_a` (`a ∈ G := (ℤ/n)^×`),
on which `G` acts **simply transitively**. A spurious config `T` (antipodal-free signed subset of
`μ_n` with `p ∣ N(σ_T)`) lands in the set `Land(T) ⊆ G`. The probe found, at the *worst* structured
prime in each band, EXACTLY:

| n | worst p | β | total spur (any prime) | per-prime `c(𝔭₁)` | ratio | orbit sizes |
|---|---|---|---|---|---|---|
| 8  | 73  | 2.06 | 0 | 0 | — | — |
| 16 | 401 | 2.16 | 64 | 8 | **8 = n/2** | all **8** (full) |

i.e. (i) **`spread t(T) = 1`** — each config lands in exactly ONE prime; (ii) the landing configs
fall into **full Galois orbits of size `|G| = n/2`** — one config per prime; hence (iii)
**`perPrime a = #orbits` for EVERY prime `a`** (uniform), and `total = (n/2) · #orbits`.
Two further EXACT facts (probes `probe_wfS4_orbit_growth`, `_galois_perprime_spread`):
- **Stickelberger multiplicity pin: `v_{𝔭_a}(σ_T) = 1` always** (max valuation 1 over all measured
  n ∈ {8,16,32}, all weights ≤ 6) — vanishing is always SIMPLE; no config concentrates depth in one
  prime.
- **β-sweep collapse: at prize β (≥ 3) the bounded-weight spurious mass is `0`** (n=16: p=4129 (β=3),
  p=65537=Fermat (β=4) both have `0` weight-≤4 spurious configs; the structured bad primes for SHORT
  relations sit at SMALL β). So the energy inflation at structured primes (the S2 Fermat 2.58× at r=2)
  comes from HIGH-weight (`≈ 2r`, collision-heavy) configs, NOT bounded-weight ones — exactly the
  "spread over many frequencies, not concentrated" signature.

## What this file proves (axiom-clean), the ORBIT-partition / uniform-per-prime law

Abstracted: `G` a finite group (the Galois group), acting on a config set `C`; the *landing prime*
of a config is a function `home : C → G` (well-defined because `spread ≡ 1`), and the action is
modeled by a `G`-action `act : G → C → C` that is **`home`-equivariant**: `home (act g T) = g • home T`
in the regular `G`-torsor sense `home (act g T) = g * home T`. Then:

> **`perPrime_eq_of_torsor`** — if `home` is `G`-equivariant onto the regular `G`-action on itself
> and `act` is a free transitive action on each fibre's orbit, then `perPrime a` is **independent of
> `a`** (every prime sees the same number of configs) and equals `(#landing configs) / |G|`. This is
> the exact `1/(n/2)` per-prime concentration, now a THEOREM (given the measured `home`-equivariance),
> not just an average.

We give the load-bearing piece as a clean bijection: the fibre `home⁻¹(a)` is in bijection with the
fibre `home⁻¹(b)` for any two primes `a b`, via translation by `b a⁻¹` through the equivariant action.
Hence all fibres (`= perPrime a`) have equal cardinality.

## Honest scope (rules 1, 3, 6)

NOT a CORE closure. This is the EXACT Galois-orbit bookkeeping making the prompt's CONCENTRATION
mechanism precise: at a structured prime the TOTAL config count inflates, but it is spread UNIFORMLY
over the `n/2` split primes (per-prime `= total/(n/2)`), and per-prime each vanishing is simple
(`v_𝔭 = 1`). The equivariance input `home (act g T) = g * home T` is the MEASURED `spread ≡ 1` +
simple-transitivity fact (probe), not proven here. CORE (`M(μ_n) ≤ C·√(n·log(p/n))`) stays **OPEN**;
this constrains HOW the spurious mass can be distributed, supporting (does not prove) the bounded-`M`
spread picture.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. #444.
- Washington, *Introduction to Cyclotomic Fields* (Stickelberger ideal, splitting of `p ≡ 1 mod n`).
- in-tree: `_wfS4_galois_perprime_spread.lean` (the Fubini incidence identity this sharpens),
  `_wf5M2_stickelberger_depth.lean` (the depth-R norm wall).
-/

set_option linter.style.longLine false
set_option autoImplicit false


namespace ProximityGap.Frontier.GaloisOrbitPartition

open Finset

variable {C G : Type*} [Fintype C] [Fintype G] [DecidableEq C] [DecidableEq G] [Group G]

-- `home` = the landing prime of a config (well-defined in the measured `spread ≡ 1` regime).
-- `act`  = the Galois action on configs (`act g T : ζ^i ↦ ζ^{g i}`).
variable (home : C → G) (act : G → C → C)

/-- Per-prime count: number of configs whose (unique) landing prime is `a`. -/
def perPrime (a : G) : ℕ := (univ.filter fun T : C => home T = a).card

/-- **The home-equivariance hypothesis (MEASURED: simple transitivity of `G` on the `n/2` primes).**
The Galois action moves the landing prime by left translation: `home (act g T) = g * home T`. -/
def HomeEquivariant : Prop := ∀ (g : G) (T : C), home (act g T) = g * home T

/-- **`act` is a genuine (left) group action** — identity acts trivially and the action composes.
This is exactly the Galois action on configs (`σ_g · (σ_h · T) = σ_{gh} · T`, `σ_1 = id`). It makes
each `act g` a bijection with inverse `act g⁻¹`. -/
structure ActIsAction : Prop where
  one : ∀ T : C, act 1 T = T
  mul : ∀ (x y : G) (T : C), act (x * y) T = act x (act y T)

/-- **ORBIT-PARTITION LEMMA — the fibres over distinct primes are equinumerous.**
Under `home`-equivariance and bijectivity of the action, translation by `b * a⁻¹` is a bijection from
the fibre `home⁻¹(a)` onto the fibre `home⁻¹(b)`. Hence `perPrime a = perPrime b` for ALL primes:
the spurious configs are spread **UNIFORMLY** across the `|G| = n/2` split primes. -/
theorem perPrime_eq_of_equivariant
    (hequiv : HomeEquivariant home act) (hact : ActIsAction act) (a b : G) :
    perPrime home a = perPrime home b := by
  classical
  -- Translation by g = b * a⁻¹ sends fibre(a) to fibre(b); by g⁻¹ back. Use card_nbij'.
  let g : G := b * a⁻¹
  -- act g and act g⁻¹ are mutually inverse (group action).
  have hgg : ∀ U : C, act g (act g⁻¹ U) = U := by
    intro U; rw [← hact.mul, mul_inv_cancel, hact.one]
  have hg'g : ∀ T : C, act g⁻¹ (act g T) = T := by
    intro T; rw [← hact.mul, inv_mul_cancel, hact.one]
  refine Finset.card_bij' (fun (T : C) _ => act g T) (fun (U : C) _ => act g⁻¹ U) ?_ ?_ ?_ ?_
  · -- maps fibre(a) into fibre(b)
    intro T hT
    simp only [mem_filter, mem_univ, true_and] at hT ⊢
    have h1 : home (act g T) = g * home T := hequiv g T
    rw [h1, hT]
    -- g * a = (b * a⁻¹) * a = b
    simp only [g, mul_assoc, inv_mul_cancel, mul_one]
  · -- maps fibre(b) into fibre(a)
    intro U hU
    simp only [mem_filter, mem_univ, true_and] at hU ⊢
    have h2 : home (act g⁻¹ U) = g⁻¹ * home U := hequiv g⁻¹ U
    rw [h2, hU]
    -- g⁻¹ * b = (b a⁻¹)⁻¹ * b = a b⁻¹ * b = a
    simp only [g, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
  · -- left inverse on fibre(a)
    intro T _; exact hg'g T
  · -- right inverse on fibre(b)
    intro U _; exact hgg U

/-- **UNIFORM-CONCENTRATION COROLLARY — `|G| · perPrime a = total landing count`, for every prime.**
Summing the uniform per-prime count over the `|G| = n/2` primes recovers the total number of landing
configs. Equivalently each single split prime `𝔭_a` carries the fraction `1/|G| = 1/(n/2)` of the
spurious configs — the exact `(n/2)×` SPREAD the probe measured (`total = 64 = 8 · 8 = (n/2) · c`). -/
theorem card_mul_perPrime_eq_total
    (hequiv : HomeEquivariant home act) (hact : ActIsAction act) [Nonempty G] (a : G) :
    (Fintype.card G) * perPrime home a = Fintype.card C := by
  classical
  -- Σ_b perPrime b = #C (every config has exactly one home), and perPrime is uniform.
  have huniform : ∀ b : G, perPrime home b = perPrime home a := fun b =>
    perPrime_eq_of_equivariant home act hequiv hact b a
  have hsum_total : ∑ b : G, perPrime home b = Fintype.card C := by
    simp only [perPrime, card_filter]
    rw [Finset.sum_comm]
    -- Σ_T Σ_b 1_{home T = b} = Σ_T 1 = #C
    have hone : ∀ T : C, ∑ b : G, (if home T = b then 1 else 0) = 1 := by
      intro T
      rw [Finset.sum_ite_eq univ (home T) (fun _ => 1)]
      simp
    rw [Finset.sum_congr rfl (fun T _ => hone T)]
    simp [Finset.card_univ]
  have hconst : ∑ _b : G, perPrime home a = (Fintype.card G) * perPrime home a := by
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc (Fintype.card G) * perPrime home a
      = ∑ _b : G, perPrime home a := hconst.symm
    _ = ∑ b : G, perPrime home b :=
        (Finset.sum_congr rfl (fun b _ => (huniform b))).symm
    _ = Fintype.card C := hsum_total

/-- **The per-prime count is `0` exactly when there are no spurious configs at all.**
(So a structured prime with inflated total `#C > 0` still spreads `#C / (n/2)` to EACH prime — never
concentrates all the mass on one.) -/
theorem perPrime_pos_iff_total_pos
    (hequiv : HomeEquivariant home act) (hact : ActIsAction act) [Nonempty G] (a : G) :
    0 < perPrime home a ↔ 0 < Fintype.card C := by
  classical
  have hG : 0 < Fintype.card G := Fintype.card_pos
  have hmul := card_mul_perPrime_eq_total home act hequiv hact a
  constructor
  · intro h
    rw [← hmul]; exact Nat.mul_pos hG h
  · intro h
    rw [← hmul] at h
    exact (Nat.pos_of_mul_pos_left (by rwa [Nat.mul_comm] at h))

end ProximityGap.Frontier.GaloisOrbitPartition

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.GaloisOrbitPartition.perPrime_eq_of_equivariant
#print axioms ProximityGap.Frontier.GaloisOrbitPartition.card_mul_perPrime_eq_total
#print axioms ProximityGap.Frontier.GaloisOrbitPartition.perPrime_pos_iff_total_pos
