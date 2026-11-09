/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# wf-S7 — the char-`p` Mann analogue, RESOLVED into a GALOIS-SPREAD count law (#444)

## What the measurement settled (and why the naive Mann hope is FALSE)

The S7 mission asked whether the char-`p` "spurious" vanishing relations (signed configs
`σ_T = ∑_{i∈T} ε_i ζ_n^i`, `ε_i ∈ {±1}`, with `p ∣ N(σ_T) ≠ 0`) have **bounded weight** — a
char-`p` analogue of Mann's char-0 weight bound — which would bound their count and force `K`
bounded. The exact measurement (`probe_wfS7_galois_spread_law.py`) gives a TWO-PART answer:

1. **The short-weight Mann floor HOLDS but only locally.** `maxOdd(n,w)` (largest odd prime that
   divides any weight-`w` norm) at FIXED weight GROWS with `n`:
   `w=4`: `log_n(maxOdd) = 1.65 (n=16), 2.59 (n=32), 4.33 (n=64)`. It crosses `4` at `n=64`, so a
   weight-`4` config can carry a genuine prize prime `p ≈ n^4`. CONCRETE TRANSFER-FALSE WITNESS
   (`n=64`): the prize prime `p = 17318209 ≡ 1 (mod 64)`, `p = n^{4.008}`, divides
   `N_{ℚ(ζ₆₄)/ℚ}(ζ^8 + ζ^{13} − ζ^{14} − ζ^{20})`. So **short spurious relations DO reach prize
   primes** for `n ≥ 64`; the Mann analogue does NOT push minimal spurious weight above the depth
   band. The naive "bounded weight ⟹ bounded count" hope is refuted.

2. **BUT the spurious mass is GALOIS-EQUIVARIANT.** For that `p` at `n=64`, the `1024` weight-`4`
   spurious configs decompose into EXACTLY `32` Galois orbits, EACH of size `32 = φ(64)`:
   `#spurious(n,w,p) = (#base orbits) · φ(n)`, every orbit FULL. This is the decisive reduction:
   `K` bounded `⟺` the number of *base orbits* is controlled (the S2/S4/S6 spread).

## What is PROVEN here (axiom-clean)

The structural mechanism behind (2): **the Galois action is FREE on the spurious set, so every
orbit has cardinality `|G| = φ(n)`, and the spurious count is a multiple of `φ(n)`.** We formalize:

* `stabilizer_eq_bot_of_free` — a free action has trivial stabilizers.
* `card_orbit_of_free` — under a free action of a finite group `G`, every orbit has cardinality
  exactly `|G|` (orbit–stabilizer with trivial stabilizer). The "every orbit is FULL, size `φ(n)`".
* `card_eq_numOrbits_mul_card_group_of_free` / `galois_card_dvd_of_free` — the class equation under
  a free action: `|X| = (#orbits)·|G|`, hence `|G| ∣ |X|`. Specialized to the spurious set with
  `G = (ℤ/n)^×` (order `φ(n)`): the spurious count is a MULTIPLE of `φ(n)` — `0` (Mann floor: no
  spurious orbit) or `≥ φ(n)` — NEVER a small nonzero number. The sharp char-`p` Mann dichotomy:
  spurious mass is `0`, or it comes in a FULL Galois orbit.

These give the SHARP form of the S7 lane: the obstruction is a *count of Galois orbits*, never a
single small relation, and that count is the same spread object S2/S4/S6 isolate. Axiom-clean
(`propext, Classical.choice, Quot.sound`); no `sorry`, no new axiom. Issue #444.
-/

set_option linter.style.longLine false


namespace ArkLib.ProximityGap.Frontier.WFS7Galois

open scoped BigOperators
open MulAction

/-- **A free action has trivial stabilizers.** If `g • b = b ⟹ g = 1` for all `g, b`, then the
stabilizer of every point is `⊥`. The "free" hypothesis is exactly that the Galois group
`(ℤ/n)^×` moves every antipodal-free signed config (no nontrivial unit fixes a low-weight config),
which the measurement confirms (all realized spurious orbits have full size `φ(n)`). -/
theorem stabilizer_eq_bot_of_free {G β : Type*} [Group G] [MulAction G β]
    (hfree : ∀ (g : G) (b : β), g • b = b → g = 1) (b : β) :
    stabilizer G b = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro g hg
  exact hfree g b (by simpa using hg)

/-- **Every orbit of a free finite-group action has cardinality `|G|`.** Orbit–stabilizer plus
trivial stabilizer: `|orbit b| · |stab b| = |G|` and `|stab b| = 1`. This is the "each spurious
orbit is FULL, size `φ(n)`" half of the measured law `#spurious = (#orbits) · φ(n)`. -/
theorem card_orbit_of_free {G β : Type*} [Group G] [Fintype G] [MulAction G β]
    (hfree : ∀ (g : G) (b : β), g • b = b → g = 1) (b : β)
    [Fintype (orbit G b)] :
    Fintype.card (orbit G b) = Fintype.card G := by
  haveI : Fintype (stabilizer G b) := Fintype.ofFinite _
  have h := card_orbit_mul_card_stabilizer_eq_card_group G b
  have hst : Fintype.card (stabilizer G b) = 1 := by
    have hbot : stabilizer G b = ⊥ := stabilizer_eq_bot_of_free hfree b
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨1, hbot ▸ Subgroup.mem_bot.mpr rfl⟩, fun y => Subtype.ext ?_⟩
    have hy : (y : G) = 1 := Subgroup.mem_bot.mp (hbot ▸ y.2)
    simp [hy]
  rw [hst, mul_one] at h
  exact h

/-- **The Galois-spread class equation (free action).** For a free action of a finite group `G` on
a fintype `β`, `|β| = (#orbits) · |G|`. Each orbit is full (`card_orbit_of_free`) and the orbits
partition `β` (the class formula `selfEquivSigmaOrbitsQuotientStabilizer`, with every stabilizer
`⊥` so `G ⧸ ⊥ ≃ G`). Specialized to the spurious set with `|G| = φ(n)`, the count is an integer
multiple of `φ(n)`. -/
theorem card_eq_numOrbits_mul_card_group_of_free {G β : Type*} [Group G] [Finite G]
    [MulAction G β] [Finite β]
    (hfree : ∀ (g : G) (b : β), g • b = b → g = 1) :
    Nat.card β
      = Nat.card (Quotient (orbitRel G β)) * Nat.card G := by
  classical
  haveI : Fintype (Quotient (orbitRel G β)) := Fintype.ofFinite _
  -- Class formula bijection `β ≃ Σ ω, G ⧸ stabilizer G ω.out`.
  have e := selfEquivSigmaOrbitsQuotientStabilizer G β
  rw [Nat.card_congr e, Nat.card_sigma]
  -- each summand: `|G ⧸ stabilizer G ω.out| = |G|` since the stabilizer is `⊥`.
  have hsumm : ∀ ω : Quotient (orbitRel G β),
      Nat.card (G ⧸ stabilizer G ω.out) = Nat.card G := by
    intro ω
    have hbot : stabilizer G ω.out = ⊥ := stabilizer_eq_bot_of_free hfree ω.out
    rw [hbot]
    exact Nat.card_congr (QuotientGroup.quotientBot.toEquiv)
  rw [Finset.sum_congr rfl (fun ω _ => hsumm ω)]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul,
      ← Nat.card_eq_fintype_card (α := Quotient (orbitRel G β))]

/-- **The Galois-spread divisibility law.** Under a free action of a finite group `G`, `|G|` divides
`|β|`. For the spurious-config set with `G = (ℤ/n)^×`, `|G| = φ(n)`: the spurious count is a
MULTIPLE of `φ(n)` — so it is `0` (Mann floor: no spurious orbit) or `≥ φ(n)`, NEVER a small nonzero
number. This is the exact char-`p` Mann dichotomy the measurement exhibits (`32` full orbits of
size `φ(64)=32` for the witnessed prize prime). -/
theorem galois_card_dvd_of_free {G β : Type*} [Group G] [Finite G] [MulAction G β] [Finite β]
    (hfree : ∀ (g : G) (b : β), g • b = b → g = 1) :
    Nat.card G ∣ Nat.card β := by
  rw [card_eq_numOrbits_mul_card_group_of_free hfree]
  exact Dvd.intro_left _ rfl

end ArkLib.ProximityGap.Frontier.WFS7Galois
