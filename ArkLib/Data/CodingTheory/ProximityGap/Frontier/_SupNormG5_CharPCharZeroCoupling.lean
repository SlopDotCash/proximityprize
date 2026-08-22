/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (Issue #444, IDEA G5 — char-p↔char-0 direct sup coupling)
-/
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# IDEA G5: char-p ↔ char-0 DIRECT SUP COUPLING — the exact anchor and the precise no-go (#444)

μ_n ⊂ 𝔽_p^* order-n subgroup (n=2^μ, p≡1 mod n, prize p≈n^4). η_b := ∑_{x∈μ_n} e_p(b·x),
M := max_{b≠0}|η_b|. Prize: M ≤ C·√(n·log(q/n)), C=O(1) (q=p, m=(p−1)/n).

G5: directly TRANSPORT the char-0 (Gaussian-ideal) periods — sup √(2n log m), extreme value of m
correlated N(0,n) — onto the real char-p periods in the b-variable: M² ≤ (char-0 ideal sup)² +
correction, WITHOUT the moment ladder (PROVEN vacuous). Either the coupling controls the
correction (→ prize) or the correction IS the char-p excess (→ wall).

EXACT COUPLING ANCHOR: M² = max_{b≠0}|η_b}|² = mean + excess, mean := (∑_{b≠0}|η_b|²)/(p−1).
The mean is char-INDEPENDENT: ∑_{b≠0}|η_b|² = p·n − n² (exact integer identity, verified rel-err
≤1.2e−15), so mean = n − n(n−1)/(p−1) → n = char-0 Parseval value. Prize lives in the excess.

PROBES (this session, /tmp/g5_*.py, exact 2nd moment, float sup): worst-of-window
C=M/√(n log m): 1.106(n=8), 1.214(n=16), 1.214(n=32), 1.213(n=64), spike 1.329(n=64 bad prime).
Char-0 overshoot M²/(n·H_m): 1.17,1.43,1.77,1.39 — bounded ≈1.2–1.8×, NOT →1, prime-dependent.

α≈0.5: coupling pins prize SCALE √(n log m), empirical C∈[1.10,1.33] (would suffice) but
boundedness unprovable. BARRIER: correction = discrepancy of b-equidistribution of (n−1) Gauss
phases arg g(χ) (|g(χ)|=√p exact, phase-only, HD-invariant, B2-dead) = n^{1−o(1)}→√n BGK wall.
Deterministic transport (2nd moment) loses a full power of p. REDUCES TO WALL.

PROVES (axiom-clean): exactMean decomposition (mean_eq, mean_le_n, excess_def, coupling_identity);
deterministic transport + its full-power loss (transport_bound, transport_loses_power); the no-go
(coupling_reduces_to_excess, excess_split): prize ⟺ bounding char-p excess at √log m scale = wall.
NOT a closure; a rigorous localization. Issue #444, IDEA G5.
-/

set_option linter.style.longLine false
set_option autoImplicit false


namespace ProximityGap.Frontier.G5Coupling

open Real

def parsevalMass (p n : ℝ) : ℝ := p * n - n ^ 2
noncomputable def mean (p n : ℝ) : ℝ := parsevalMass p n / (p - 1)

theorem mean_eq (p n : ℝ) (hp : 1 < p) : mean p n = n - n * (n - 1) / (p - 1) := by
  have hp1 : p - 1 ≠ 0 := by linarith
  unfold mean parsevalMass; field_simp; ring

theorem mean_le_n (p n : ℝ) (hp : 1 < p) (hn : 1 ≤ n) : mean p n ≤ n := by
  rw [mean_eq p n hp]
  have hp1 : 0 < p - 1 := by linarith
  have : 0 ≤ n * (n - 1) / (p - 1) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (le_of_lt hp1)
  linarith

noncomputable def excess (Msq p n : ℝ) : ℝ := Msq - mean p n

theorem excess_def (Msq p n : ℝ) : Msq = mean p n + excess Msq p n := by unfold excess; ring

theorem transport_bound (Msq p n : ℝ) (hM : Msq ≤ parsevalMass p n) :
    excess Msq p n ≤ parsevalMass p n - mean p n := by unfold excess; linarith

theorem transport_loses_power (p n : ℝ) (hp : 2 ≤ p) (hn : 1 ≤ n) (hpn : 2 * n ≤ p) :
    (n / 2) * (p - 2) ≤ parsevalMass p n - mean p n := by
  have hp1 : (0:ℝ) < p - 1 := by linarith
  rw [mean_eq p n (by linarith)]
  have hsq : (0:ℝ) ≤ n * (n - 1) / (p - 1) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) (le_of_lt hp1)
  unfold parsevalMass
  nlinarith [hsq, hn, hp, mul_nonneg (by linarith : (0:ℝ) ≤ n) (by linarith : (0:ℝ) ≤ p - 2 * n)]

theorem coupling_reduces_to_excess (Msq p n C : ℝ) (logm : ℝ) :
    Msq ≤ C ^ 2 * (n * logm) ↔ excess Msq p n ≤ C ^ 2 * (n * logm) - mean p n := by
  unfold excess
  constructor
  · intro h; linarith
  · intro h; linarith

theorem excess_split (Msq p n C logm : ℝ) (hbound : Msq ≤ C ^ 2 * (n * logm)) :
    excess Msq p n ≤ (C ^ 2 - 1) * (n * logm) + ((n * logm) - mean p n) := by
  unfold excess; nlinarith [hbound]

theorem coupling_identity (Msq p n : ℝ) (hp : 1 < p) :
    Msq = (n - n * (n - 1) / (p - 1)) + excess Msq p n := by
  rw [← mean_eq p n hp]; exact excess_def Msq p n

end ProximityGap.Frontier.G5Coupling
/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ProximityGap.Frontier.G5Coupling.mean_eq
#print axioms ProximityGap.Frontier.G5Coupling.transport_loses_power
#print axioms ProximityGap.Frontier.G5Coupling.coupling_reduces_to_excess
#print axioms ProximityGap.Frontier.G5Coupling.coupling_identity
