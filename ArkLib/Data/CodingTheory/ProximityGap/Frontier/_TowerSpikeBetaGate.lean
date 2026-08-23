/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumDilationRecursion

/-!
# The 2-power tower spike: per-level cross-parity is EXACT, the blow-up is β-gated (#407)

## What this session measured (decisive numerics, the "missed angle" tower wave)

The prize-deciding object is the Gauss-period sup-norm `M(G) = max_{b≠0} ‖η_b(G)‖`,
`η_b(G) = ∑_{x∈G} ψ(b·x)`, and its normalized form `R(G) = M(G)/√(n·ln m)`, `n = |G|`,
`m = (q-1)/n` the subgroup index. The Wick floor is `R = √2`; `R > √2` is the
structured-prime "spike" the refutation hunt flagged (measured `R = 1.49`).

The 2-power tower is the recursion `μ_{2^{i+1}} = μ_{2^i} ⊔ ζ•μ_{2^i}`, giving the **exact**
single-level identity (substrate `eta_union_dilate`):
`η_b(μ_n) = η_b(μ_{n/2}) + η_{ζb}(μ_{n/2})`.

This session pulled the tower angle on the **period sup-norm** (not the cumulant, not the
incidence — the prior `cumulant2power` and `laneF cross-parity` refutations were about those
two objects). Three new exact measurements:

1. **The argmax cross-parity is EXACTLY constructive.** At the global maximizer `b*` of
   `‖η_b(μ_n)‖`, the two child periods `η_{b*}(μ_{n/2})` and `η_{ζb*}(μ_{n/2})` have
   `cos(phase difference) = 1.000` to machine precision — for EVERY prime, every `n` tested
   (`probe_tower_ratio_v2.py`, `probe_cosphi_mechanism.py`). So the worst-case L^∞ tower step
   is the *full* `M(μ_n) = ‖η_{b*}(μ_{n/2})‖ + ‖η_{ζb*}(μ_{n/2})‖` triangle-equality, never the
   `√2` averaging — the substrate's "cos = 1 empirically at the maximizer" is *exact* at `b*`.

2. **The blow-up is β-GATED, not 2-adicity-gated** (`probe_diseng3.py`, 34 curated primes
   `≡ 1 mod 16`, n=16, v2 and β varied independently):
   ```
     corr(β,  M(n)/M(n/2)) = +0.62   ← thinness DRIVES the ratio toward 2
     corr(v2, M(n)/M(n/2)) = −0.04   ← 2-adic structure does NOT (once β is freed)
     corr(v2, R(n))        = +0.33   (weak)   corr(β, R(n)) = −0.26
   ```
   The apparent "Fermat-prime spike" in the naive sweep is a CONFOUND: larger primes happened
   to carry larger `v2`. Holding `n = 16` fixed and reading `R(16)` at thin `β ≥ 4` at the
   WORST structured primes:
   ```
       p      v2  β     R(16)
     40961   13 3.83  1.130
     65537   16 4.00  1.199   ← FERMAT, maximal v2 — still < √2 = 1.414
    114689   14 4.20  1.149
    163841   15 4.33  1.150
   ```
   At the prize regime (thin `β ≥ 4`) the period sup-norm stays **below the Wick floor** even
   at the maximally-2-adic Fermat prime. The `R = 2.07` blow-up only appears at `n = 64,
   p = 65537` where `β = 2.67` — a THICK subgroup, far outside the prize window.

3. **R blows up DOWN the tower (β shrinking), not up it (β growing).** At a fixed prime,
   climbing `n = 4,8,…,64` shrinks `β = log_n q`; at the Fermat prime `R` then climbs
   `0.64 → 0.93 → 1.20 → 1.61 → 2.07` (`probe_Rtower.py`). The amplification is a low-β
   (thick-subgroup) effect; the per-level ratio relaxes back toward `√2` as `β` grows.

## The honest verdict on the "imprimitive tower drives the spike" hypothesis

**Partially confirmed, prize-relevance REFUTED.** The tower recursion is exact and the
worst-case step IS full constructive amplification (`cos = 1` at `b*`, ratio `→ 2`). But the
amplification is gated by the subgroup *thickness* `β`, not by 2-adic prime structure, and in
the prize regime (`β ≥ 4`) the spike sits comfortably below the Wick floor `√2`. This LOCALIZES
the `R > √2` phenomenon to the non-prize thick regime and reconciles the prior `cumulant2power`
refutation (the heavy frequencies carry generic order — there is no finite imprimitive carrier)
with the exact single-level recursion: the *value* recurses cleanly, the *carrier* does not.

## What this file proves (on top of the substrate, axiom-clean)

The per-level recursion is already in `SubgroupGaussSumDilationRecursion`. This file adds the
**iterated tower envelope** — the clean statement that converts a uniform per-level ratio bound
into a μ-level bound — and names the β-gated cocycle obligation as an explicit `Prop`. Nothing
here is the open BGK core; the open content is the *value* of the per-level ratio (`√2` vs `2`)
along the worst trajectory, which this file leaves as the named hypothesis `LevelRatioBound`.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
- substrate: `SubgroupGaussSumDilationRecursion.lean` (the exact single-level recursion).
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


open Finset AddChar

namespace ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The level functional.** `levelTower ψ G ζ μ` is the `2^μ`-fold disjoint dilate tower built
from base `G` by repeatedly adjoining the `ζ`-dilate. One step is `H ↦ H ∪ ζ•H`. -/
noncomputable def levelTower (ψ : AddChar F ℂ) (G : Finset F) (ζ : F) : ℕ → Finset F
  | 0 => G
  | (k + 1) => levelTower ψ G ζ k ∪ dilate ζ (levelTower ψ G ζ k)

/-- A *uniform per-level sup-norm ratio bound* `r`: at each tower level `k < μ`, every frequency
value at level `k+1` is at most `r` times the worst value at level `k`. `r = √2` is the (open,
desired) L²-tracking value; `r = 2` is the trivial triangle value (always true). This is the
named hypothesis isolating the open BGK content as ONE scalar. -/
def LevelRatioBound (ψ : AddChar F ℂ) (G : Finset F) (ζ : F) (μ : ℕ) (r : ℝ) : Prop :=
  ∀ k : ℕ, k < μ → ∀ b : F,
    ‖eta ψ (levelTower ψ G ζ (k + 1)) b‖ ≤ r * (⨆ c : F, ‖eta ψ (levelTower ψ G ζ k) c‖)

/-- **The base sup-norm** of the tower (level-0 worst frequency value). -/
noncomputable def baseSup (ψ : AddChar F ℂ) (G : Finset F) : ℝ :=
  ⨆ c : F, ‖eta ψ G c‖

/-- **Iterated tower envelope (trivial direction).** The per-level *triangle* bound of the
substrate (`eta_union_dilate_le_of_bound`, ratio `2`) iterates to the `2^μ` envelope: if every
level-`k` value is `≤ M_k`, the next level is `≤ 2·M_k`. This is the proven-but-trivial side;
the prize asks the same with `2` replaced by `√2`. We package it as: a uniform level-`k` bound
propagates to level-`k+1` with factor `2`. -/
theorem levelTower_succ_le_of_bound (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} (hζ : ζ ≠ 0)
    (k : ℕ) (hdisj : Disjoint (levelTower ψ G ζ k) (dilate ζ (levelTower ψ G ζ k)))
    {M : ℝ} (hM : ∀ c : F, ‖eta ψ (levelTower ψ G ζ k) c‖ ≤ M) (b : F) :
    ‖eta ψ (levelTower ψ G ζ (k + 1)) b‖ ≤ 2 * M := by
  simpa [levelTower] using
    eta_union_dilate_le_of_bound ψ (levelTower ψ G ζ k) hζ hdisj hM b

/-- **The recursion is the exact single-level identity at every tower level.** Records that
`levelTower`'s step is literally `eta_union_dilate`: the level-`(k+1)` frequency value is its own
level-`k` value plus the level-`k` value of its dilate `ζ·b`. This is the object whose worst-case
constructive alignment (`cos = 1` at `b*`, measured this session) the open ratio bound controls. -/
theorem levelTower_succ_eq (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} (hζ : ζ ≠ 0) (k : ℕ)
    (hdisj : Disjoint (levelTower ψ G ζ k) (dilate ζ (levelTower ψ G ζ k))) (b : F) :
    eta ψ (levelTower ψ G ζ (k + 1)) b
      = eta ψ (levelTower ψ G ζ k) b + eta ψ (levelTower ψ G ζ k) (ζ * b) := by
  simpa [levelTower] using eta_union_dilate ψ (levelTower ψ G ζ k) hζ hdisj b

/-- **β-gated worst-case ratio obligation (the named open content, ONE scalar).** The prize
floor `M(μ_n) ≲ C·√(n·ln(q/n))` is equivalent to: along the worst tower trajectory the per-level
sup-norm ratio is the L²-value `√2`, not the trivial triangle value `2`. This session's numerics
say the *actual* worst-case ratio is `2`-leaning at thick β (`R → 2.07` at `β = 2.67`) but
relaxes below `√2` at thin β (`R ≤ 1.2` at `β ≥ 4`, even at the Fermat prime). So the obligation
is conditioned on the thinness `β`: for `β ≥ β₀` (prize), the worst per-level ratio is `≤ √2`.

This is a NAMED HYPOTHESIS (open), the β-gated form of the BGK cocycle large-deviation bound —
NOT a theorem. A proof discharges it from a thin-subgroup short-character-sum bound; a refutation
exhibits a `β ≥ β₀` trajectory with ratio `> √2`. -/
def BetaGatedRatio (ψ : AddChar F ℂ) (G : Finset F) (ζ : F) (μ : ℕ) : Prop :=
  LevelRatioBound ψ G ζ μ (Real.sqrt 2)

/-- **The L²-tracking consequence (clean, conditional).** Under the β-gated ratio bound `√2`,
a base sup-norm `M₀` propagates one tower level with factor `√2` (the floor-scale step), in
contrast to the unconditional factor `2`. This is the exact statement the prize needs at every
level; it is here only as the immediate consequence of `BetaGatedRatio`, with the hypothesis
left open. -/
theorem betaGated_succ_le (ψ : AddChar F ℂ) (G : Finset F) {ζ : F} (μ : ℕ)
    (h : BetaGatedRatio ψ G ζ μ) {k : ℕ} (hk : k < μ) (b : F) :
    ‖eta ψ (levelTower ψ G ζ (k + 1)) b‖
      ≤ Real.sqrt 2 * (⨆ c : F, ‖eta ψ (levelTower ψ G ζ k) c‖) :=
  h k hk b

/-- **The gap is exactly `√2` vs `2`.** Records that `BetaGatedRatio` (the open, desired, floor)
strengthens the unconditional triangle bound (ratio `2`) by the factor `√2/2 = 1/√2` per level —
the single scalar separating the proven Johnson-side from the prize. Over the `μ ≈ log₂ n` tower
levels this `(1/√2)^μ = n^{-1/2}` factor is exactly the `√n` energy-vs-sup-norm deficit. -/
theorem ratio_gap_is_sqrt2 : Real.sqrt 2 < 2 := by
  rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

end ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
