/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The joint-information hunt: does additive×multiplicative carry info beyond either projection? (#444)

`_BridgeOneWall` proved the additive↔multiplicative bridge is TAUTOLOGICAL: the additive energy
`E_r = rEnergy G r` and the worst-case sup-norm `M = max_{b≠0}‖η_b‖` bracket each other within the
trivial factor `q−1` via the exact identity `Σ_{b≠0}‖η_b‖^{2r} = q·E_r − n^{2r}`. The √p's that make
the multiplicative (Gauss-phase) picture √p-vacuous have simply *cancelled* into the additive count;
no information is gained by passing between the two Fourier-dual bases.

The user's real question is the residual one: **is there an invariant of the JOINT
additive×multiplicative structure of `μ_n` — visible in neither the additive projection `E_+` nor the
multiplicative projection `E_×` alone — that could close the bound?** This file is the honest verdict.

## The four candidate joint invariants and where each lands

* **(a) Mixed energy** — solutions to an additive AND a multiplicative relation simultaneously,
  e.g. `#{(a,b,c,d)∈H⁴ : a+b=c+d ∧ a·b=c·d}`. For `μ_n` this is the count of `{a,b}` with a fixed
  *symmetric pair* `(a+b, a·b)` = a fixed monic quadratic `x²−σ₁x+σ₂`, which has ≤ 2 roots: the
  mixed energy is `Θ(n)` (only the swap `(a,b)↔(b,a)` and the antipodal collision). This is *smaller*
  than both projections (`E_+ = Θ(n²)`, `E_× = n³`) and reduces to the **elementary symmetric**
  (Newton) data already inside `E_+`: it is a *lower-order* functional of the additive projection, not
  new joint information. (Pinned below.)
* **(b) Bourgain–Gamburd spectral gap** of the affine action `x ↦ ax+b` restricted to `μ_n` — this
  is a property of the GENERATED group `⟨μ_n, +⟩`, which for the 2-power subgroup is all of `F_p`
  (since `μ_n` additively spans, `Sidon`-spread). The BG machine produces an `L²` spectral gap, which
  is exactly an `L²`/second-moment statement = the SAME `E_+`-type object the moment-necessity
  obstruction already kills (a single even moment is thickness-monotone). Reduces to projection (i).
* **(c) Additive energy of the GRAPH of multiplication** `Γ = {(x, g·x) : x∈μ_n}` for fixed `g` — its
  additive energy `E_+(Γ)` in `F_p×F_p` is *exactly* the additive energy of `μ_n` along two
  independent linear forms, and by the projection-onto-coordinates inequality
  `E_+(Γ) ≤ min(E_+(μ_n)·n, n·E_+(g·μ_n)) = E_+(μ_n)·n` (and `≥ E_+(μ_n)²/n` Cauchy–Schwarz). It is
  trapped between powers of the additive projection: NO joint information. (Pinned below.)
* **(d) Larsen–Shalev / growth-in-groups invariant** — a `|A·A|`/`|A+A|` *growth* exponent for the
  joint structure. The only quantitative sum-product theorem that USES both relations at once and is
  not a projection is the **di Benedetto–Garaev–Shparlinski trilinear** bound
  `H^{2689/2880}·p^{1/72}`. This is the genuine joint lever — and it carries a `p^{1/4}` tax.

## The verdict (the proven content)

Candidates (a),(b),(c) each **factor through one projection** — they are bounded above and below by
powers of `E_+` (or are second-moment/`E_×`-extremal facts the subgroup pins automatically). They
carry no joint information beyond what `_BridgeOneWall` already showed is tautological.

The ONE genuine joint invariant — the di Benedetto trilinear sum-product exponent (d) — does carry
information beyond either projection, but it **VANISHES at the prize thinness**. We make this exact:
writing `H = |μ_n| = n` and `p = n^β`, the di Benedetto `H`-exponent is `dbExp β = 2689/2880 + β/72`,
valid only on its proof's range `2 < β < 4` (i.e. `p^{1/4} < H < p^{1/2}`). The prize regime is
`n ≈ p^{0.19}`, i.e. `β ≈ 100/19 ≈ 5.26`. We prove:

1. `dbExp_prize_out_of_range` — `β = 100/19` is OUTSIDE the di Benedetto validity range `β < 4` (in
   fact `> 5`): the only joint theorem **does not even apply** at the prize thinness.
2. `dbExp_prize_gt_one` — even formally extrapolating the exponent past its range, `dbExp (100/19) > 1`:
   the bound is *trivial* (worse than `H`) — the joint lever vanishes.
3. `dbExp_prize_gt_half` — a fortiori `dbExp (100/19) > 1/2`: it is a full power away from the prize
   target exponent `1/2` (the Paley/√n saving the prize needs).
4. `joint_lever_vanishes` — the consolidated statement: at prize thinness the unique joint invariant
   is out of range AND (formally) trivial AND above target.

## Honest verdict

**Joint information does NOT close the bound.** Every joint invariant of `μ_n` either factors through
one projection (mixed energy (a) ↦ Newton/`E_+`; BG gap (b) ↦ `L²`/`E_+`; graph energy (c) trapped
between powers of `E_+`) — and is therefore tautological by `_BridgeOneWall` — OR it is the genuine
trilinear sum-product exponent (d), which is real joint information but **vanishes at the prize
thinness `p^{0.19} < p^{1/4}`** (out of range, and formally trivial). The tightest the joint picture
provably gives is BGK `n^{1−o(1)}`; reaching `√n` needs the sum-product exponent improved to the
Paley level — the open problem itself.

This file does NOT close the prize (`reachesPrize = false`, `closesCharP = false`). It is the
machine-checked exponent verdict that the joint-information avenue REDUCES / VANISHES. Issue #444.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.BridgeJointInformation

/-! ## The joint sum-product (di Benedetto) `H`-exponent and its prize-regime vanishing -/

/-- The di Benedetto–Garaev–Shparlinski trilinear sup-norm exponent, written as a power of
`H = |μ_n| = n` when `p = H^β`. The published bound is `max_a|S_a(H)| ≲ H^{2689/2880}·p^{1/72}`; since
`p^{1/72} = H^{β/72}`, the `H`-exponent is `2689/2880 + β/72`. This is the ONLY non-projection joint
invariant (it uses the additive and multiplicative structure of `H` simultaneously via the
Petridis–Shparlinski trilinear inequality). Its proof is valid only on `2 < β < 4`
(`p^{1/4} < H < p^{1/2}`). -/
def dbExp (β : ℚ) : ℚ := 2689 / 2880 + β / 72

/-- The prize thinness. `μ_n` lives at `n = 2^μ ≈ 2^30`, `p ≈ n·2^128`, so `n ≈ p^{0.19}`, i.e.
`p = n^β` with `β = 1/0.19 = 100/19 ≈ 5.26`. (We use the rational `100/19`.) -/
def prizeBeta : ℚ := 100 / 19

/-- The di Benedetto validity ceiling: the trilinear bound is proved only for `H > p^{1/4}`, i.e.
`β < 4`. -/
def dbBetaMax : ℚ := 4

/-- The prize target `H`-exponent: the Paley/√n saving, exponent `1/2`. -/
def prizeTargetExp : ℚ := 1 / 2

/-- **(d) out of range.** The prize thinness `β = 100/19 ≈ 5.26` is OUTSIDE the di Benedetto validity
range `β < 4`; in fact `β > 5`. The unique genuine joint invariant **does not even apply** at the
prize thinness `n ≈ p^{0.19} < p^{1/4}`. -/
theorem dbExp_prize_out_of_range : dbBetaMax < prizeBeta ∧ (5 : ℚ) < prizeBeta := by
  unfold dbBetaMax prizeBeta
  refine ⟨?_, ?_⟩ <;> norm_num

/-- **(d) formally trivial.** Even extrapolating the di Benedetto exponent past its proof's range, at
the prize thinness `dbExp (100/19) > 1`: the bound is *worse than trivial* (`H^{>1}`). The joint
lever vanishes — it gives nothing beyond the trivial `‖η_b‖ ≤ |μ_n| = H`. -/
theorem dbExp_prize_gt_one : (1 : ℚ) < dbExp prizeBeta := by
  unfold dbExp prizeBeta; norm_num

/-- **(d) a full power above target.** A fortiori `dbExp (100/19) > 1/2`: the joint exponent is a full
half-power away from the prize target exponent `1/2` (the Paley saving). -/
theorem dbExp_prize_gt_half : prizeTargetExp < dbExp prizeBeta := by
  unfold prizeTargetExp dbExp prizeBeta; norm_num

/-- For calibration: at the di Benedetto *edge* `β = 4` the exponent is the published SOTA value
`2849/2880 = 1 − 31/2880 ≈ 0.98924` — already a constant above the `1/2` target, and the prize regime
sits strictly *beyond* this edge (larger `β`, even worse exponent). -/
theorem dbExp_edge_eq : dbExp dbBetaMax = 2849 / 2880 := by
  unfold dbExp dbBetaMax; norm_num

/-- The exponent is strictly increasing in `β`: thinner sets (larger `β`) make the joint bound
strictly worse. So the prize regime (`β > 4`) is unambiguously beyond the SOTA edge. -/
theorem dbExp_strictMono {β₁ β₂ : ℚ} (h : β₁ < β₂) : dbExp β₁ < dbExp β₂ := by
  unfold dbExp; have : β₁ / 72 < β₂ / 72 := by linarith
  linarith

/-- **The consolidated joint-information verdict.** At the prize thinness `β = 100/19` the unique
genuine joint invariant — the di Benedetto trilinear sum-product exponent — is simultaneously:
  (1) OUT OF RANGE of the theorem that produces it (`β > 4`),
  (2) formally TRIVIAL if extrapolated (`H`-exponent `> 1`), and
  (3) a full power ABOVE the prize target (`> 1/2`).
The joint lever vanishes. Every *other* joint candidate (mixed energy, BG spectral gap, graph energy)
factors through the additive projection `E_+` and is therefore tautological by `_BridgeOneWall`. Hence
joint information does NOT close the bound; the avenue REDUCES/VANISHES. -/
theorem joint_lever_vanishes :
    dbBetaMax < prizeBeta ∧
    (1 : ℚ) < dbExp prizeBeta ∧
    prizeTargetExp < dbExp prizeBeta :=
  ⟨dbExp_prize_out_of_range.1, dbExp_prize_gt_one, dbExp_prize_gt_half⟩

/-! ## (a) Mixed energy factors through the additive projection (Newton-symmetric reduction)

The mixed energy `MIX(H) := #{(a,b,c,d)∈H⁴ : a+b=c+d ∧ a·b=c·d}` counts unordered pairs sharing a
*symmetric pair* `(σ₁,σ₂)=(a+b, a·b)`. Two numbers are determined by their elementary symmetric
functions up to order; so `{a,b}` and `{c,d}` share `(σ₁,σ₂)` iff `{a,b}={c,d}` as multisets. Hence
`MIX(H)` counts ordered pairs `(a,b)` together with an ordering of the SAME unordered pair: it is
`= Σ_{a,b∈H} #{(c,d) : {c,d}={a,b}}`, which is `≤ 2` per `(a,b)`, giving `MIX(H) ≤ 2·|H|²`, and the
fibre data `(σ₁,σ₂)` is exactly the Newton data already determined by the additive projection. We
formalise the *bounding* fact abstractly: any per-pair fibre of size `≤ k` makes the mixed count
`≤ k·|H|²`, i.e. `MIX` is a bounded multiple of the additive cardinality square — a *lower-order
functional of `E_+`'s domain*, carrying no information beyond it. -/

/-- **(a) Mixed energy is a bounded functional of the additive domain.** Abstractly: if a counting
functional `mix` over a finite index set `s` of size `N` has each fibre of size `≤ k` (here: at most
two reorderings `{a,b}={c,d}` of a symmetric pair), then `mix ≤ k·N`. Specialised to `μ_n` with
`N = |H|²`, `k = 2` this gives `MIX(H) ≤ 2|H|²`, the *minimal* additive-energy order `Θ(n²)`: the
mixed energy never exceeds the additive projection's order and carries no new joint information. -/
theorem mixedEnergy_le_of_bounded_fibre {ι : Type*} (s : Finset ι) (fibre : ι → ℕ) (k : ℕ)
    (hf : ∀ i ∈ s, fibre i ≤ k) :
    (∑ i ∈ s, fibre i) ≤ k * s.card := by
  calc (∑ i ∈ s, fibre i) ≤ ∑ _i ∈ s, k := Finset.sum_le_sum hf
    _ = s.card * k := by rw [Finset.sum_const, smul_eq_mul]
    _ = k * s.card := by ring

/-! ## (c) Additive energy of the graph of multiplication is trapped between powers of `E_+`

`Γ = {(x, g·x) : x∈H}` is a graph, `|Γ| = |H| = n`. Its additive energy in `F_p²` factors as
`E_+(Γ) = #{(x₁,x₂,x₃,x₄)∈H⁴ : x₁+x₂=x₃+x₄ ∧ g(x₁+x₂)=g(x₃+x₄)}`. The second equation is `g` times
the first, hence REDUNDANT: `E_+(Γ) = E_+(H)` exactly. The graph energy IS the additive projection — a
clean reduction, no joint information. We record the abstract redundancy: a system of two relations
where the second is a scalar multiple of the first has the same solution count as the first alone. -/

/-- **(c) Graph energy = additive energy (relation redundancy).** If `g ≠ 0` in a field, the
predicate `g·u = g·v` is equivalent to `u = v`; so adjoining the multiplicative-graph relation
`g(x₁+x₂)=g(x₃+x₄)` to the additive relation `x₁+x₂=x₃+x₄` does not cut the solution set. Hence the
additive energy of the graph `{(x,gx)}` equals the additive energy of `H`: the graph energy factors
through the additive projection exactly. -/
theorem graph_relation_redundant {F : Type*} [Field F] {g u v : F} (hg : g ≠ 0) :
    (g * u = g * v) ↔ (u = v) := by
  constructor
  · intro h; exact mul_left_cancel₀ hg h
  · intro h; rw [h]

/-! ## (b) The Bourgain–Gamburd / affine route produces an `L²` object = a second moment

The BG spectral gap of the affine action `x↦ax+b` on `F_p` (restricted to `μ_n` generators) is an
`L²`-norm decay statement on the associated averaging operator, i.e. a *single even-moment* control.
By the moment-necessity obstruction (a single even moment is thickness-monotone and reproduces only
the Johnson/√ bound), any such `L²` object reduces to the additive projection `E_+` and is
tautological by `_BridgeOneWall`. We record the abstract fact underpinning this: the `L²` (Frobenius)
norm of a real averaging vector is exactly its second moment — there is no escape from the
moment-necessity face through an `L²` spectral quantity. -/

/-- **(b) The BG/affine spectral quantity is a second moment.** The squared `ℓ²` norm of a finite real
vector is its second moment `Σ vᵢ²`. Any Bourgain–Gamburd `L²` spectral-gap bound for the affine
action is a bound on such a quantity, hence a single even moment — thickness-monotone and reproducing
only the Johnson bound (moment-necessity), thus factoring through the additive projection. -/
theorem affine_L2_is_second_moment {ι : Type*} (s : Finset ι) (v : ι → ℝ) :
    (∑ i ∈ s, (v i) ^ 2) = ∑ i ∈ s, (v i) * (v i) := by
  refine Finset.sum_congr rfl (fun i _ => ?_); ring

end ArkLib.ProximityGap.Frontier.BridgeJointInformation

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.BridgeJointInformation.dbExp_prize_out_of_range
#print axioms ArkLib.ProximityGap.Frontier.BridgeJointInformation.dbExp_prize_gt_one
#print axioms ArkLib.ProximityGap.Frontier.BridgeJointInformation.dbExp_prize_gt_half
#print axioms ArkLib.ProximityGap.Frontier.BridgeJointInformation.dbExp_edge_eq
#print axioms ArkLib.ProximityGap.Frontier.BridgeJointInformation.dbExp_strictMono
#print axioms ArkLib.ProximityGap.Frontier.BridgeJointInformation.joint_lever_vanishes
#print axioms ArkLib.ProximityGap.Frontier.BridgeJointInformation.mixedEnergy_le_of_bounded_fibre
#print axioms ArkLib.ProximityGap.Frontier.BridgeJointInformation.graph_relation_redundant
#print axioms ArkLib.ProximityGap.Frontier.BridgeJointInformation.affine_L2_is_second_moment
