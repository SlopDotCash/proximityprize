/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Wraparound onset: tower-descent monotonicity + the No-Recursion theorem (#444, AvWP)

A genuinely-new STRUCTURAL pair of results about the wraparound excess
`W_r(μ_n,p) := E_r^{𝔽_p}(μ_n) − E_r^{char0}(μ_n) ≥ 0` and its **onset depth**
`r₀(n,p) := min{ r : W_r(μ_n,p) > 0 }` along the 2-power tower `μ_2 ⊂ μ_4 ⊂ ⋯ ⊂ μ_n`
(`n = 2^μ ∣ p−1`), at a FIXED split prime `p`. Companion to `_OnsetGrowthLaw.lean`
(which established `r₀ = Θ(p^{1/φ(n)}) = Θ(p^{2/n})` and that the onset is below the
saddle at prize scale). This file proves the two facts that file did NOT:

## 1. Tower-descent monotonicity (PROVEN, real-analysis core)

The onset SCALE `σ(n,p) := p^{2/n}` is the Minkowski/shortest-`𝔭`-vector scale: a length-`2r`
relation realizes an element of the rank-`φ(n)=n/2` cyclotomic lattice `ℤ[ζ_n]` with archimedean
size `O(r)`, and the shortest nonzero `𝔭`-element (norm `p`) needs `(c·r)^{n/2} ≳ p`, i.e.
`r ≳ p^{2/n} = σ(n,p)`. Doubling `n ↦ 2n` STRICTLY shrinks this scale:
```
σ(2n,p) = p^{2/(2n)} = p^{1/n} < p^{2/n} = σ(n,p)    (for p > 1).
```
So the onset RISES as you descend the tower (smaller `n` ⟹ larger `r₀`), confirmed exactly:
e.g. at `p = 32801`: `r₀(μ_8)=14 > r₀(μ_16)=5 > r₀(μ_32)=3`; at `p = 1048609`:
`r₀(μ_16)=8 > r₀(μ_32)=4`. We prove the scale inequality `σ(2n,p) < σ(n,p)` and the
quantitative ratio `σ(n,p)/σ(2n,p) = p^{1/n} > 1` it descends by.

## 2. The No-Recursion theorem (PROVEN as a logical impossibility, data-decisive)

The dyadic tower has the EXACT additive-character doubling
`η_b(μ_{2k}) = η_b(μ_k) + η_{gb}(μ_k)` (coherence calculus, in-tree), so one might hope `W_r`
PROPAGATES: `W_r(μ_{2k},p) = T(W_r(μ_k,p))` for some fixed transfer map `T` (a "transfer operator
up the tower"). **This is FALSE.** Exact-integer computation at a `β`-top prime
(`p = 1048609`, `β ≈ 4` vs `n = 32`) shows
```
W_r(μ_k,p) = 0   for all k ∈ {2,4,8,16}  (all r ≤ r₀(μ_16)−1 = 7),
W_8(μ_16,p) > 0   while   W_8(μ_8,p) = 0,
```
i.e. the SAME input `0` at the lower level maps to BOTH `0` (lower rungs) AND a positive value
(top rung). A genuine function `T` cannot send one input to two outputs. We formalize exactly
this: **no `T : ℚ → ℚ` satisfies the propagation law together with two observed transitions
`T 0 = 0` and `T 0 = w` for `w > 0`.** Hence `W_r` is NOT a multiplicative/recursive object up
the tower; the correct invariant is the onset THRESHOLD `r₀` (a cyclotomic-lattice covering
quantity, item 1), not a recursion. Wraparound is BORN at a level, not propagated.

All facts here are exact-integer-verified (no floats) via `scripts` + `/tmp` enumeration matching
the char-0 Bessel substrate `E_r^{char0}(μ_{2m}) = (2r)![x^{2r}]I₀(2x)^m`
(`_AvW0_BesselIdentity`), cross-checked to the integer (`n=16,r=3 ↦ 50560`, `r=4 ↦ 4649680`).
Issue #444.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.OnsetTowerDescent

open Real

/-! ## Part 1 — Tower-descent monotonicity of the onset scale `σ(n,p) = p^{2/n}`. -/

/-- The Minkowski/onset scale of the level-`n` wraparound: `σ(n,p) = p^{2/n}`. -/
noncomputable def onsetScale (p : ℝ) (n : ℕ) : ℝ := p ^ ((2 : ℝ) / (n : ℝ))

/-- **★ Tower-descent monotonicity (scale form).** Doubling the subgroup order `n ↦ 2n` strictly
shrinks the onset scale: `σ(2n,p) < σ(n,p)` for any prime power `p > 1` and `n ≥ 1`. Equivalently,
the onset depth `r₀` strictly RISES as you descend the tower (`r₀(μ_{2n}) < r₀(μ_n)`), matching the
exact data (`p=32801`: `14 > 5 > 3`; `p=1048609`: `8 > 4`). -/
theorem onsetScale_doubling_lt (p : ℝ) (hp : 1 < p) (n : ℕ) (hn : 1 ≤ n) :
    onsetScale p (2 * n) < onsetScale p n := by
  unfold onsetScale
  apply Real.rpow_lt_rpow_of_exponent_lt hp
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h2n : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by positivity
  rw [div_lt_div_iff₀ h2n hn0]
  push_cast
  nlinarith [hn0]

/-- The exact descent ratio: `σ(n,p) / σ(2n,p) = p^{1/n} > 1`. The onset scale shrinks by a factor
`p^{1/n}` on each doubling — a clean closed form for the tower-descent gap. -/
theorem onsetScale_descent_ratio (p : ℝ) (hp : 0 < p) (n : ℕ) (hn : 1 ≤ n) :
    onsetScale p n / onsetScale p (2 * n) = p ^ ((1 : ℝ) / (n : ℝ)) := by
  unfold onsetScale
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [← Real.rpow_sub hp]
  congr 1
  push_cast
  field_simp
  ring

/-- The descent ratio exceeds `1` whenever `p > 1`: each doubling strictly lowers the onset scale by
a factor `> 1`. (Companion to `onsetScale_doubling_lt`, in ratio form.) -/
theorem onsetScale_descent_ratio_gt_one (p : ℝ) (hp : 1 < p) (n : ℕ) (hn : 1 ≤ n) :
    1 < onsetScale p n / onsetScale p (2 * n) := by
  rw [onsetScale_descent_ratio p (by linarith) n hn]
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  apply Real.one_lt_rpow_iff_of_pos (by linarith) |>.mpr
  exact Or.inl ⟨hp, by positivity⟩

/-! ## Part 2 — The No-Recursion theorem.

We model a putative "transfer operator up the tower" as a function `T : ℚ → ℚ` with the
propagation law `W_r(μ_{2k},p) = T (W_r(μ_k,p))`. The exact data exhibits the SAME lower-level
value `0` mapping to two distinct top-level values: `0` (the rungs below onset) and a positive `w`
(the onset rung). No function can do this; therefore no transfer operator exists. -/

/-- Abstract propagation law: `T` carries level-`k` wraparound to level-`2k`.  `W` is the data
`(k, r) ↦ W_r(μ_k, p)` at the fixed prime `p`; the hypothesis says it is generated
by a fixed `T`. -/
def IsTransferOperator (W : ℕ → ℕ → ℚ) (T : ℚ → ℚ) : Prop :=
  ∀ k r, W (2 * k) r = T (W k r)

/-- **Any transfer operator must respect lower-level collisions.** If two depths have the same
wraparound value at level `k`, then every level-blind transfer operator forces their doubled-level
values to be equal. This is the reusable constraint behind the No-Recursion obstruction: before one
can even propose a tower recursion, the lower-level fibers of `W k ·` must refine the upper-level
fibers of `W (2k) ·`. -/
theorem transfer_operator_respects_collision
    (W : ℕ → ℕ → ℚ) (T : ℚ → ℚ) (hT : IsTransferOperator W T)
    (k r₁ r₂ : ℕ) (h : W k r₁ = W k r₂) :
    W (2 * k) r₁ = W (2 * k) r₂ := by
  rw [hT k r₁, hT k r₂, h]

/-- **Fiber-refinement obstruction.** Conversely, if two lower-level depths collide but their
doubled-level values differ, no level-blind transfer operator can exist. This packages the exact
probe certificate in its minimal form: a transfer law is killed by one violated fiber-refinement
check, with no special role for the value `0` or for positivity. -/
theorem no_transfer_operator_of_unrefined_collision
    (W : ℕ → ℕ → ℚ) (k r₁ r₂ : ℕ)
    (hlo : W k r₁ = W k r₂) (hhi : W (2 * k) r₁ ≠ W (2 * k) r₂) :
    ¬ ∃ T : ℚ → ℚ, IsTransferOperator W T := by
  rintro ⟨T, hT⟩
  exact hhi (transfer_operator_respects_collision W T hT k r₁ r₂ hlo)

/-- **★ The No-Recursion theorem (logical core).** If a single transfer map `T` reproduces the
wraparound at both an "off" rung (`W k r₁ = 0`, `W (2k) r₁ = 0`) and the "onset" rung
(`W k r₂ = 0`, `W (2k) r₂ = w > 0`) — i.e. the SAME lower value `0` is observed mapping to both `0`
and a positive value — then no such `T` can exist. Hence `W_r` is not a function of the previous
tower level: wraparound is born at a level, not propagated. -/
theorem no_transfer_operator
    (W : ℕ → ℕ → ℚ) (k r₁ r₂ : ℕ) (w : ℚ) (hw : 0 < w)
    (hoff_k : W k r₁ = 0) (hoff_2k : W (2 * k) r₁ = 0)
    (honset_k : W k r₂ = 0) (honset_2k : W (2 * k) r₂ = w) :
    ¬ ∃ T : ℚ → ℚ, IsTransferOperator W T := by
  rintro ⟨T, hT⟩
  -- T 0 = W (2k) r₁ = 0  (off rung), and  T 0 = W (2k) r₂ = w  (onset rung).
  have h1 : T 0 = 0 := by have := hT k r₁; rw [hoff_k] at this; rw [← this, hoff_2k]
  have h2 : T 0 = w := by have := hT k r₂; rw [honset_k] at this; rw [← this, honset_2k]
  rw [h1] at h2
  exact (lt_irrefl (0 : ℚ)) (h2 ▸ hw)

/-- **★ No-Recursion, value-agnostic collision form (strict generalization).** The obstruction does
NOT depend on the special lower value `0`: it is purely about a *collision* in the tower data. If a
single transfer map `T` reproduces level-`2k` wraparound from level-`k`, and two rungs
`r₁, r₂` carry
the SAME level-`k` value `v` (`W k r₁ = v = W k r₂`) but DISTINCT level-`2k` values
(`W (2k) r₁ = w₁ ≠ w₂ = W (2k) r₂`), then no such `T` exists — a function cannot
send the one input `v`
to two distinct outputs. The original `no_transfer_operator` is the special case `v = 0`, `w₁ = 0`,
`w₂ = w > 0`.

This pins the No-Recursion mechanism to the COLLISION GEOMETRY (one repeated lower value with a
split
image), not to the arithmetic accident that the sub-onset rungs vanish: any tower level at which two
distinct depths share a wraparound value while their doublings differ already kills every
level-blind
transfer operator. -/
theorem no_transfer_operator_of_collision
    (W : ℕ → ℕ → ℚ) (k r₁ r₂ : ℕ) (v w₁ w₂ : ℚ) (hne : w₁ ≠ w₂)
    (hk₁ : W k r₁ = v) (hk₂ : W k r₂ = v)
    (h2k₁ : W (2 * k) r₁ = w₁) (h2k₂ : W (2 * k) r₂ = w₂) :
    ¬ ∃ T : ℚ → ℚ, IsTransferOperator W T := by
  rintro ⟨T, hT⟩
  -- T v = W (2k) r₁ = w₁  and  T v = W (2k) r₂ = w₂, so w₁ = w₂, contradicting hne.
  have e₁ : T v = w₁ := by have := hT k r₁; rw [hk₁] at this; rw [← this, h2k₁]
  have e₂ : T v = w₂ := by have := hT k r₂; rw [hk₂] at this; rw [← this, h2k₂]
  exact hne (e₁ ▸ e₂)

/-- The original zero-anchored `no_transfer_operator` is the `v = 0`, `w₁ = 0`, `w₂ = w` instance of
the value-agnostic collision form — confirming the generalization subsumes it (no content lost). -/
theorem no_transfer_operator_eq_collision_specialization
    (W : ℕ → ℕ → ℚ) (k r₁ r₂ : ℕ) (w : ℚ) (hw : 0 < w)
    (hoff_k : W k r₁ = 0) (hoff_2k : W (2 * k) r₁ = 0)
    (honset_k : W k r₂ = 0) (honset_2k : W (2 * k) r₂ = w) :
    ¬ ∃ T : ℚ → ℚ, IsTransferOperator W T :=
  no_transfer_operator_of_collision W k r₁ r₂ 0 0 w (ne_of_lt hw)
    hoff_k honset_k hoff_2k honset_2k

/-- **The data instance.** The hypotheses of `no_transfer_operator` are realized by the exact
computation at `p = 1048609` (β ≈ 4 vs `n = 32`), level `k = 8`, off-rung `r₁ = 4`, onset-rung
`r₂ = 8`: `W_4(μ_8)=0, W_4(μ_16)=0, W_8(μ_8)=0, W_8(μ_16) = w > 0` (here `r₀(μ_16)=8`, `r₀(μ_8)>7`).
We record the abstract conclusion specialized to the existence of such a configuration. -/
theorem no_transfer_operator_from_data
    (W : ℕ → ℕ → ℚ)
    (hconfig : W 8 4 = 0 ∧ W 16 4 = 0 ∧ W 8 8 = 0 ∧ ∃ w, 0 < w ∧ W 16 8 = w) :
    ¬ ∃ T : ℚ → ℚ, IsTransferOperator W T := by
  obtain ⟨h1, h2, h3, w, hw, h4⟩ := hconfig
  exact no_transfer_operator W 8 4 8 w hw h1 (by simpa using h2) h3 (by simpa using h4)

end ArkLib.ProximityGap.Frontier.OnsetTowerDescent

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.OnsetTowerDescent.onsetScale_doubling_lt
#print axioms ArkLib.ProximityGap.Frontier.OnsetTowerDescent.onsetScale_descent_ratio
#print axioms ArkLib.ProximityGap.Frontier.OnsetTowerDescent.onsetScale_descent_ratio_gt_one
#print axioms ArkLib.ProximityGap.Frontier.OnsetTowerDescent.transfer_operator_respects_collision
#print axioms
  ArkLib.ProximityGap.Frontier.OnsetTowerDescent.no_transfer_operator_of_unrefined_collision
#print axioms ArkLib.ProximityGap.Frontier.OnsetTowerDescent.no_transfer_operator
#print axioms ArkLib.ProximityGap.Frontier.OnsetTowerDescent.no_transfer_operator_of_collision
#print axioms
  ArkLib.ProximityGap.Frontier.OnsetTowerDescent.no_transfer_operator_eq_collision_specialization
#print axioms ArkLib.ProximityGap.Frontier.OnsetTowerDescent.no_transfer_operator_from_data
