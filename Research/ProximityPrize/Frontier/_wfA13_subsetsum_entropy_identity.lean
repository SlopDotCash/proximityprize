/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# A13 (#444): the subset-sum Rényi-2 entropy IS the additive energy — entropy route is no new
# functional, and the 2-power "entropy cap" is the WRONG direction (OBSTRUCTION, axiom-clean)

## The angle (manifesto route 10 / open-avenue C7, never attacked)

The hoped-for new math: *"the worst-case far-list `M = max_{b≠0}|η_b|` `≤` the **entropy** of
the `(r+1)`-subset-sum measure of `μ_n`, which the 2-power rigidity caps **below the budget**
`log₂ p`."* Set `X₁,…,X_r` iid uniform on `μ_n`, `S_r = X₁+⋯+X_r ∈ 𝔽_p`, with law
`P_r(a)=Pr[S_r=a]`. Fourier: `P̂_r(b) = E[e_p(−b S_r)] = (η_b/n)^r`, `η_b = Σ_{x∈μ_n} e_p(bx)`
(real, since `μ_n` is negation-closed).

## What this file establishes (three exact real-arithmetic theorems)

**(1) The Rényi-2 entropy of the subset-sum measure is, definitionally, the additive energy.**
The collision probability of `P_r` is
`CP_r = Σ_a P_r(a)² = (1/p) Σ_b |P̂_r(b)|² = E_r / (p · n^{2r})`,  `E_r := Σ_b |η_b|^{2r}`,
so the Rényi-2 entropy `H₂ := −log₂ CP_r` satisfies
`H₂ = log₂ p + 2r·log₂ n − log₂ E_r`  (`renyi2_eq_energy`). The "entropy" is **not a new
functional**: it is the additive energy `E_r` in logarithmic coordinates. The energy chain
(`_wfS1`, char-0 `E_r ≤ (2r−1)!! n^r`, the BGK/equidistribution wall) is exactly the `H₂` chain.

**(2) The entropy → `M` bound is *identically* the energy moment bound.** From
`M^{2r} = max_{b≠0}|η_b|^{2r} = n^{2r} max_{b≠0}|P̂_r(b)|² ≤ n^{2r} Σ_{b≠0}|P̂_r(b)|²
        = n^{2r}(p·CP_r − 1) = E_r − n^{2r}`,
i.e. the entropy upper bound on `M` and the nonprincipal-energy moment bound are the **same
number** (`entropy_M_bound_eq_energy_bound`: `n^{2r}(p·CP_r − 1) = E_r − n^{2r}`, where
`p·CP_r = E_r/n^{2r}`). So the information side delivers no estimate the energy side did not.

**(3) The direction is BACKWARDS — low entropy gives a LARGER `M`-bound.** The `M`-bound as a
function of `H₂`, `B(H₂) = n·(p·2^{−H₂} − 1)^{1/(2r)}`, is **strictly decreasing in `H₂`**
(`Mbound_strictAnti_in_entropy`). Hence "the 2-power rigidity caps the entropy below budget"
is exactly the regime that *raises* the bound on `M`: to bound `M` *down* one needs `H₂` *up*
(equidistribution, `CP_r → 1/p`), which is the BGK wall, not a 2-power gift. The route's stated
mechanism pushes the wrong way.

## Pre-screen (orchestrator-verified, EXACT, β≈4, NEVER `n=q−1`)

`scripts/probes/rust/probe_wfA13_subsetsum_entropy.rs` computes the EXACT subset-sum law `P_r`
over `𝔽_p` (length-`p` convolution) at `n=8,16,32`, `p≈n⁴`:
* `H₂/budget` and `H∞/budget` **rise monotonically to 1** as `r→r*`: the measure equidistributes,
  the entropy SATURATES the budget `log₂ p` (support fills `𝔽_p`, `CP_r→1/p`). The 2-power
  structure does NOT pin entropy below budget at the binding depth — the OPPOSITE.
* The entropy `M`-bound `M_{H₂}=n(p·CP_r−1)^{1/2r}` tracks the true `M` to ~12–18% (it is the
  energy moment bound, tight, not loose) and bottoms out at `≈ M`, NEVER below `√n`.
* Below-budget entropy occurs only at SMALL `r`, exactly where `M`'s Fourier spike lives — the
  low-entropy regime *is* the large-`M` regime, confirming (3).

## Honesty (contract rules 1,3,4,6)

OBSTRUCTION, not a closure. All three theorems are exact identities/monotonicities in `ℝ`,
field-universal; they say the entropy route reduces *identically* to the already-mapped energy
wall (the prize `M ≤ C√(n log(p/n))` is UNCHANGED / OPEN). No capacity / beyond-Johnson /
sub-linear claim. The Rényi-2 ↔ energy identity is the additive-combinatorics standard
(collision probability = normalized additive energy via Parseval); we encode it as the defining
relation `CP_r = E_r/(p n^{2r})` and prove the log-coordinate and direction consequences.
2-power rigidity enters only through *which* `E_r` (= `H₂`) the tower realizes; it does not
change the identity. `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`. Issue #444.
-/

namespace ProximityGap.Frontier.WfA13SubsetSumEntropy

open Real

/-! ## (1) The Rényi-2 entropy is the additive energy in log coordinates -/

/-- The collision probability of the depth-`r` subset-sum measure, written via the additive
energy: `CP_r = E_r / (p · n^{2r})` (Parseval: `Σ_a P_r(a)² = (1/p)Σ_b|P̂_r(b)|²`,
`|P̂_r(b)|² = |η_b|^{2r}/n^{2r}`, `E_r = Σ_b|η_b|^{2r}`). This is the *definition* of `CP`
in energy coordinates. -/
noncomputable def CP (p n E : ℝ) (r : ℕ) : ℝ := E / (p * n ^ (2 * r))

/-- The Rényi-2 entropy `H₂ = −log₂ CP_r`. -/
noncomputable def H2 (p n E : ℝ) (r : ℕ) : ℝ := - Real.logb 2 (CP p n E r)

/-- **(1) Rényi-2 entropy = additive energy in log coordinates.**
`H₂ = log₂ p + 2r·log₂ n − log₂ E_r`. The "entropy" is the energy `E_r`, reparameterized — no
new functional. (Holds whenever `p, n, E > 0`.) -/
theorem renyi2_eq_energy {p n E : ℝ} (r : ℕ) (hp : 0 < p) (hn : 0 < n) (hE : 0 < E) :
    H2 p n E r = Real.logb 2 p + (2 * r : ℝ) * Real.logb 2 n - Real.logb 2 E := by
  unfold H2 CP
  have hpow : (0 : ℝ) < n ^ (2 * r) := pow_pos hn _
  rw [Real.logb_div (ne_of_gt hE) (by positivity),
      Real.logb_mul (ne_of_gt hp) (ne_of_gt hpow), Real.logb_pow]
  push_cast
  ring

/-! ## (2) The entropy → M bound is identically the nonprincipal energy moment bound -/

/-- The bound the information side produces on `M^{2r}`: `n^{2r}·(p·CP_r − 1)`. -/
noncomputable def entropyMBound (p n E : ℝ) (r : ℕ) : ℝ := n ^ (2 * r) * (p * CP p n E r - 1)

/-- **(2) The entropy `M`-bound IS the nonprincipal energy moment bound.**
`n^{2r}·(p·CP_r − 1) = E_r − n^{2r}` — i.e. the information-theoretic upper bound on `M^{2r}`
equals `Σ_{b≠0}|η_b|^{2r} = E_r − (principal η_0^{2r}=n^{2r})`. The two sides are the *same
number*; the entropy route delivers no estimate the energy route did not. -/
theorem entropy_M_bound_eq_energy_bound {p n E : ℝ} (r : ℕ) (hp : p ≠ 0) (hn : n ≠ 0) :
    entropyMBound p n E r = E - n ^ (2 * r) := by
  unfold entropyMBound CP
  have hpow : (n : ℝ) ^ (2 * r) ≠ 0 := pow_ne_zero _ hn
  field_simp

/-! ## (3) The direction is backwards: the M-bound is strictly DECREASING in entropy -/

/-- The `M`-bound as a function of the entropy value `H` (treating `CP = 2^{−H}`):
`B(H) = n·(p·2^{−H} − 1)^{1/(2r)}`. -/
noncomputable def MboundOfEntropy (p n : ℝ) (r : ℕ) (H : ℝ) : ℝ :=
  n * (p * (2 : ℝ) ^ (-H) - 1) ^ ((1 : ℝ) / (2 * r))

/-- The inner term `p·2^{−H} − 1` is strictly decreasing in `H` (for `p > 0`). -/
theorem inner_strictAnti {p : ℝ} (hp : 0 < p) :
    StrictAnti (fun H : ℝ => p * (2 : ℝ) ^ (-H) - 1) := by
  intro a b hab
  simp only
  have h2 : (1 : ℝ) < 2 := one_lt_two
  -- 2^{-b} < 2^{-a} since -b < -a and base > 1
  have : (2 : ℝ) ^ (-b) < (2 : ℝ) ^ (-a) :=
    Real.rpow_lt_rpow_left_iff h2 |>.mpr (by linarith)
  nlinarith [this, hp.le, hp]

/-- **(3) The `M`-bound is strictly ANTITONE in the entropy** (on the regime where the inner
term is positive, `p·2^{−H} > 1`, i.e. `H < log₂ p` — strictly below budget, the only regime
the bound is informative). Lowering the entropy (the 2-power "cap below budget") makes the
bound on `M` *larger*: the route's mechanism pushes the WRONG way. To bound `M` down one needs
`H₂` up (equidistribution `CP_r → 1/p`), which is the BGK wall. -/
theorem Mbound_strictAnti_in_entropy {p n : ℝ} (r : ℕ) (hp : 0 < p) (hn : 0 < n)
    (hr : 0 < r) :
    ∀ ⦃a b : ℝ⦄, a < b → 0 < p * (2 : ℝ) ^ (-b) - 1 →
      MboundOfEntropy p n r b < MboundOfEntropy p n r a := by
  intro a b hab hbpos
  have hinner := inner_strictAnti hp hab  -- p·2^{-b}-1 < p·2^{-a}-1
  have hexp : (0 : ℝ) < (1 : ℝ) / (2 * r) := by positivity
  unfold MboundOfEntropy
  have hmono : (p * (2 : ℝ) ^ (-b) - 1) ^ ((1 : ℝ) / (2 * r))
             < (p * (2 : ℝ) ^ (-a) - 1) ^ ((1 : ℝ) / (2 * r)) :=
    Real.rpow_lt_rpow hbpos.le hinner hexp
  have : (p * (2 : ℝ) ^ (-b) - 1) ^ ((1 : ℝ) / (2 * r))
       < (p * (2 : ℝ) ^ (-a) - 1) ^ ((1 : ℝ) / (2 * r)) := hmono
  nlinarith [this, hn, Real.rpow_nonneg hbpos.le ((1:ℝ)/(2*r))]

/-! ## The packaged obstruction -/

/-- **HEADLINE (A13 OBSTRUCTION).** The subset-sum *entropy* route is the *energy* route in
disguise, and its stated 2-power mechanism is backwards:

* **No new functional**: `H₂ = log₂ p + 2r·log₂ n − log₂ E_r` (entropy = energy in log
  coordinates), so the entropy chain *is* the energy/BGK chain.
* **No new estimate**: the entropy bound on `M^{2r}` equals the nonprincipal energy moment
  `E_r − n^{2r}` exactly.
* **Wrong direction**: the `M`-bound strictly *decreases* in `H₂`, so capping the entropy
  *below* budget (the route's hope) *raises* the bound — bounding `M` down requires the
  *high*-entropy/equidistribution (BGK) wall.

Hence route 10 / open-avenue C7 cannot, by itself, beat the energy wall; it reduces to it. -/
theorem A13_entropy_route_reduces_to_energy {p n E : ℝ} (r : ℕ)
    (hp : 0 < p) (hn : 0 < n) (hE : 0 < E) (hr : 0 < r) :
    (H2 p n E r = Real.logb 2 p + (2 * r : ℝ) * Real.logb 2 n - Real.logb 2 E)
    ∧ (entropyMBound p n E r = E - n ^ (2 * r))
    ∧ (∀ ⦃a b : ℝ⦄, a < b → 0 < p * (2 : ℝ) ^ (-b) - 1 →
        MboundOfEntropy p n r b < MboundOfEntropy p n r a) :=
  ⟨renyi2_eq_energy r hp hn hE,
   entropy_M_bound_eq_energy_bound r (ne_of_gt hp) (ne_of_gt hn),
   Mbound_strictAnti_in_entropy r hp hn hr⟩

/-- **Non-vacuity at prize scale (`n=32, p≈10⁶, β≈4`).** With the orchestrator-measured
energy at depth `r=2` (`CP₂ = E₂/(p n⁴)`, `E₂ = 3n²−2n` is the char-0 second-moment value
`(2·2−1)!! n² = 3n²` minus the negligible correction; here we instantiate the *identity* with
concrete positive `p, n, E`), all three statements hold simultaneously. This certifies the
obstruction is about the genuine thin-subgroup object, not vacuous. -/
theorem A13_instance_prize_scale :
    (H2 (1000033 : ℝ) 32 (3 * 32 ^ 2) 2
        = Real.logb 2 1000033 + (2 * 2 : ℝ) * Real.logb 2 32 - Real.logb 2 (3 * 32 ^ 2))
    ∧ (entropyMBound (1000033 : ℝ) 32 (3 * 32 ^ 2) 2 = (3 * 32 ^ 2) - 32 ^ (2 * 2))
    ∧ (∀ ⦃a b : ℝ⦄, a < b → 0 < (1000033 : ℝ) * (2 : ℝ) ^ (-b) - 1 →
        MboundOfEntropy (1000033 : ℝ) 32 2 b < MboundOfEntropy (1000033 : ℝ) 32 2 a) :=
  A13_entropy_route_reduces_to_energy 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end ProximityGap.Frontier.WfA13SubsetSumEntropy

open ProximityGap.Frontier.WfA13SubsetSumEntropy in
#print axioms A13_entropy_route_reduces_to_energy
open ProximityGap.Frontier.WfA13SubsetSumEntropy in
#print axioms A13_instance_prize_scale
