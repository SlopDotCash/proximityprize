/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.IncidencePeriodBridge

/-!
# Bridge B34 — the monomial far direction maximizes the line incidence (the V=F shadow)

**Spec B34 [target X].** *At the binding crossing `s*` the monomial far direction achieves
the max incidence (binding is monomial-controlled).*

**Honest scope.** The substrate `IncidencePeriodBridge.lean` lives in the **one-dimensional**
syndrome geometry `V = F` (the field itself, the geometry on which the prize's far-coset
attack lives). There a "direction" is a single field element `s₁`, and the period-sum identity
`lineIncidence_period_sum` (anchor **P2**) forces the incidence of *every* non-degenerate
("far") direction `s₁ ≠ 0` to be exactly `|G|` — the `s₁`-annihilator filter collapses to the
trivial frequency `b = 0`, contributing `conj(η₀)·ψ(0) = |G|`. Consequently:

* a monomial direction `s₁ = x^a` (any *nonzero* field element, in particular a generator
  power) achieves the incidence `|G|`;
* `|G|` is the maximum over **all** non-degenerate directions — they all *tie* at `|G|`;
* hence the monomial far direction is a maximizer of the far-line incidence (it is the binding
  value, with no non-monomial direction strictly exceeding it).

This is the faithful, axiom-clean V=F shadow of the spec's claim. What it does **not** prove —
and where the genuine open content of B34 lives — is the *strict separation* of the spec
("non-monomial decays below by the crossing"): in `V = F` every far direction ties exactly at
`|G|`, so there is no strict gap to exhibit. The strict `dirworst`/decay phenomenon is a
property of the **multi-dimensional** syndrome space `F^{n-k}` (the over-determined cascade
`D*(m)`), which is *not* provided by this substrate. See the REDUCED note in the campaign log:
the multi-dimensional strict-binding statement is the named gap.

Axiom-clean; pure consequence of P2 (`lineIncidence_period_sum`). Issue #444.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.IncidencePeriodBridge

namespace ArkLib.ProximityGap.BridgeB34

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The far-direction incidence is exactly `|G|`.** For any non-degenerate (far) direction
`s₁ ≠ 0` over the field geometry `V = F`, the line–ball incidence equals the ball size `|G|`.
This is read straight off the period-sum identity (P2): when `s₁ ≠ 0`, the `s₁`-annihilator
`{b : b·s₁ = 0}` is `{0}`, so the incidence collapses to the single term
`conj(η₀)·ψ(0) = |G|`. -/
theorem farLineIncidence_eq_card {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (s₀ s₁ : F) (hs₁ : s₁ ≠ 0) :
    lineIncidence G s₀ s₁ = G.card := by
  classical
  -- Read the integer incidence off the complex period-sum identity P2.
  have hPS := lineIncidence_period_sum hψ G s₀ s₁
  -- The annihilator filter is `{0}` because `s₁ ≠ 0`.
  have hfilt : (Finset.univ.filter (fun b : F => b * s₁ = 0)) = {0} := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h; exact (mul_eq_zero.mp h).resolve_right hs₁
    · intro h; subst h; simp
  rw [hfilt, Finset.sum_singleton] at hPS
  -- The single surviving term is `conj(η₀)·ψ(0) = |G|·1 = |G|`.
  have heta0 : eta ψ G 0 = (G.card : ℂ) := by
    rw [eta]
    simp only [zero_mul, AddChar.map_zero_eq_one, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [heta0] at hPS
  simp only [zero_mul, AddChar.map_zero_eq_one, mul_one, map_natCast] at hPS
  -- Now `(lineIncidence G s₀ s₁ : ℂ) = (G.card : ℂ)`; cast back to ℕ.
  exact_mod_cast hPS

/-- **The monomial far direction attains the maximal far-line incidence.** Fix a generator-style
monomial direction `s₁ = m` with `m ≠ 0`. For *any* other non-degenerate direction `t ≠ 0` the
line incidence at `t` is `≤` the incidence at the monomial direction `m` (in fact they are equal,
both `= |G|`). So the monomial far direction is a maximizer of the far-line incidence over all
non-degenerate directions — the binding is monomial-controlled (no non-monomial direction
strictly exceeds it). -/
theorem monomial_dir_maximizes {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (s₀ t₀ : F) (m t : F) (hm : m ≠ 0) (ht : t ≠ 0) :
    lineIncidence G t₀ t ≤ lineIncidence G s₀ m := by
  rw [farLineIncidence_eq_card hψ G t₀ t ht, farLineIncidence_eq_card hψ G s₀ m hm]

/-- **The monomial far direction is the binding value, exactly.** Every non-degenerate direction
ties with the monomial direction at incidence `|G|`. Stated as the explicit two-sided pin: the
monomial incidence equals every other far incidence. This is the V=F binding identity —
"binding is monomial-controlled" in the sharpest possible form (degenerate ties, not strict
domination, in the one-dimensional geometry). -/
theorem farLineIncidence_const_eq_monomial {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (s₀ t₀ : F) (m t : F) (hm : m ≠ 0) (ht : t ≠ 0) :
    lineIncidence G t₀ t = lineIncidence G s₀ m := by
  rw [farLineIncidence_eq_card hψ G t₀ t ht, farLineIncidence_eq_card hψ G s₀ m hm]

/-- **Sanity: the degenerate direction `s₁ = 0` is not in the far family.** For `s₀ ∈ G` the
constant-direction incidence is `q ≥ |G|` (it can *exceed* the far value), confirming that the
maximization in `monomial_dir_maximizes` is genuinely over the *far* (`s₁ ≠ 0`) family — the
degenerate point is excluded by hypothesis, not by accident. -/
theorem degenerate_dir_incidence_ge_card (G : Finset F) (s₀ : F) (hmem : s₀ ∈ G) :
    G.card ≤ lineIncidence G s₀ 0 := by
  rw [lineIncidence_zero_dir, if_pos hmem]
  exact Finset.card_le_univ G

end ArkLib.ProximityGap.BridgeB34

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.ProximityGap.BridgeB34.farLineIncidence_eq_card
#print axioms ArkLib.ProximityGap.BridgeB34.monomial_dir_maximizes
#print axioms ArkLib.ProximityGap.BridgeB34.farLineIncidence_const_eq_monomial
#print axioms ArkLib.ProximityGap.BridgeB34.degenerate_dir_incidence_ge_card
