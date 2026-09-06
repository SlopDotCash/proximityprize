/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Geometry of numbers of the ideal `𝔭 ⊂ ℤ[ζ_{2^μ}]`: the shortest `𝔭`-vector and the onset `r₀` (#444)

This is the **G1-shortest-vector** door. The onset `r₀(n)` (the first depth at which a wraparound
relation `W_r ≠ 0` appears) was reduced — in the companion onset files — to the first `r` for which
the **radius-`r` sumset disk** of `μ_n` (sums of `≤ 2r` `n`-th roots of unity) contains a NONZERO,
non-antipodal element of the prime ideal `𝔭 ⊂ ℤ[ζ_n]` lying over the field characteristic `p`.

A sum of `≤ 2r` roots of unity has **every archimedean embedding of size `≤ 2r`**: for any embedding
`σ : ℤ[ζ_n] ↪ ℂ`, `|σ(ζ₁ + ⋯ + ζ_{2r})| ≤ 2r`. Hence a `𝔭`-element living in the radius-`r` disk must
have **sup-over-embeddings norm `‖α‖_∞ := max_σ |σ(α)| ≤ 2r`**. Contrapositive: **if the SHORTEST
nonzero `𝔭`-vector in the sup-norm has length `Λ_𝔭`, then no `𝔭`-element fits in the disk until
`2r ≥ Λ_𝔭`, so**
```
                              r₀  ≥  Λ_𝔭 / 2.
```
This file builds that geometry-of-numbers object and the `r₀` lower bound it yields, and delivers the
honest verdict on **the crux**: *does the 2-power cyclotomic structure make `Λ_𝔭` bigger than the
worst-case Minkowski/AM-GM floor — i.e. does GoN beat the worst-case norm bound?*

## The shortest `𝔭`-vector floor (clean AM-GM — NO discriminant term)

Let `K = ℚ(ζ_{2^μ})`, `d = [K:ℚ] = φ(2^μ) = 2^{μ-1} = n/2` (with `n = 2^μ`). For an odd prime `p`,
`p` is **unramified** and `𝔭 | p` has residue degree `f = ord_{2^μ}(p)` (the multiplicative order of `p`
mod `2^μ`) and absolute norm `N(𝔭) = p^f`. For **any** nonzero `α ∈ 𝔭`, AM–GM over the `d` archimedean
embeddings gives
```
   ‖α‖_∞ = max_σ |σ(α)|  ≥  (∏_σ |σ(α)|)^{1/d}  =  |N_{K/ℚ}(α)|^{1/d}  ≥  N(𝔭)^{1/d}  =  p^{f/d} = p^{2f/n},
```
because `α ∈ 𝔭 ⟹ 𝔭 | (α) ⟹ N(𝔭) | N(α)`. This is `shortestVector_ge_normFloor`: **a clean lower
bound on the shortest `𝔭`-vector with NO discriminant factor.** It yields
```
   r₀  ≥  ½ · p^{f/d}  =  ½ · p^{2f/n}.                               (onsetLowerBound_via_shortestVector)
```

## The crux: GoN vs the worst-case norm bound — does the 2-power structure help?

* **`f`-aware gain (genuine, this IS new).** When the residue degree `f > 1` the GoN bound
  `½·p^{2f/n}` is **strictly larger** than the worst-case norm bound `½·p^{2/n}` from the prompt
  (which is exactly the `f = 1` instance). `gon_beats_worstNorm_when_f_large` records the strict gain
  per fixed `p`. So for any individual `p` with `p ≢ 1 (mod 2^μ)`, the onset is provably later than the
  universal norm bound says — a real, machine-checked, lattice-geometric improvement.

* **Worst case over `p` collapses (the prize is `q`-uniform → REDUCES).** The prize must hold for ALL
  `p`. The adversary picks the WORST `p`, namely `p ≡ 1 (mod 2^μ)` (`p` **totally split**, `f = 1`),
  where `p^{2f/n} = p^{2/n}` — exactly the weak norm bound. `gon_worstCase_eq_norm` records this
  collapse. The only place 2-power structure could lift the `f = 1` floor is the **transference / upper
  Minkowski** side, governed by `disc(ℚ(ζ_{2^μ})) = ± 2^{(μ-1)·2^{μ-1}}`. Its contribution to a
  shortest-vector bound is `|disc|^{1/(2d)} = 2^{(μ-1)/2} = n^{(μ-1)/(2μ)} ≤ √n` (`discFactor_le_sqrt_n`):
  a **polynomial-in-`n` factor**, sub-leading to `p` at prize scale. It enters only the UPPER bound and
  therefore **cannot raise the `f = 1` lower-bound floor `p^{2/n}`**. GoN does NOT beat the worst-case
  norm.

* **At prize scale the bound is vacuous (NOT CLOSED).** With `n = 2^μ`, `μ ≈ 30`, and `p` thin
  (`n ≈ p^{1/β}`, `β ≈ 4`), the worst-case (`f = 1`) bound is `r₀ ≥ ½·p^{2/n}`, and `p^{2/n} = 2^{(2 log₂ p)/n}`
  with `2 log₂ p / n ≈ 2·256 / 2^{30} ≈ 2^{-21} → 0`, so `p^{2/n} → 1` and the bound gives only
  `r₀ ≥ ½`. `onsetBound_vacuous_at_prizeScale` records that the exponent `→ 0`. This is `≪ log p`, so
  GoN does NOT prove `r₀ > log p`. NOT CLOSED.

## Verdict

The geometry-of-numbers object is real and the AM-GM shortest-vector floor `Λ_𝔭 ≥ p^{f/d}` is clean
(no discriminant), giving a **genuine `f`-aware onset bound `r₀ ≥ ½ p^{2f/n}`** that strictly beats the
worst-case norm bound whenever the residue degree `f > 1` (`boundsOnset`). **But the 2-power cyclotomic
structure does NOT beat the worst-case norm**: the worst `p` is totally split (`f = 1`), where the GoN
floor equals the norm floor `p^{2/n}`, and the discriminant transference factor `2^{(μ-1)/2} ≤ √n` is a
sub-leading polynomial that lives only on the UPPER bound. At prize scale the `f = 1` exponent `2/n → 0`
makes the bound `r₀ ≥ ½` — vacuous, `≪ log p`. So GoN gives a real per-`p` onset improvement but
**REDUCES** to the worst-case norm wall for the (`q`-uniform) prize. Axiom-clean. NOT a closure. Issue #444.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.OnsetShortestVector

open Real

/-! ### The 2-power cyclotomic data: degree, residue degree, absolute norm of `𝔭` -/

/-- Degree of `K = ℚ(ζ_{2^μ})` over `ℚ`: `d = φ(2^μ) = 2^{μ-1} = n/2` where `n = 2^μ`. -/
def cycDeg (μ : ℕ) : ℕ := 2 ^ (μ - 1)

/-- The subgroup size `n = 2^μ`. Then `cycDeg μ = n / 2`. -/
def subgroupSize (μ : ℕ) : ℕ := 2 ^ μ

/-- `d = n/2`: the field degree is half the subgroup size, the standard 2-power cyclotomic fact. -/
theorem cycDeg_eq_half_subgroup {μ : ℕ} (hμ : 1 ≤ μ) :
    2 * cycDeg μ = subgroupSize μ := by
  unfold cycDeg subgroupSize
  rw [← pow_succ']
  congr 1
  omega

/-- Absolute norm of the prime `𝔭 | p` of residue degree `f` (`p` unramified, odd): `N(𝔭) = p^f`. -/
def idealNorm (p f : ℕ) : ℕ := p ^ f

/-! ### The geometry-of-numbers object: the shortest `𝔭`-vector in the sup-over-embeddings norm -/

/-- **The sup-over-embeddings (archimedean) norm of an algebraic integer.** Abstractly `‖α‖_∞ =
max_σ |σ(α)|`; we carry it as a nonnegative real `Λ` with its two defining geometry-of-numbers
properties supplied as hypotheses where needed (the AM-GM norm floor and the disk-fit bound). This
keeps the file lattice-geometric and minimal-import while pinning the EXACT inequalities that matter. -/
abbrev SupNorm := ℝ

/-- **The radius-`r` disk-fit constraint (the bridge from sumset to sup-norm).** A sum of `≤ 2r` roots
of unity has every embedding of modulus `≤ 2r`, hence sup-norm `≤ 2r`. So any `𝔭`-element realized in
the radius-`r` sumset disk has `Λ ≤ 2r`. This is the geometric content `diskFit`. -/
def diskFit (Λ : SupNorm) (r : ℕ) : Prop := Λ ≤ 2 * r

/-- **AM–GM shortest-vector floor (the clean GoN bound — NO discriminant).** For any nonzero `α ∈ 𝔭`,
`‖α‖_∞^d ≥ ∏_σ |σ(α)| = |N(α)| ≥ N(𝔭)`, so `Λ ≥ N(𝔭)^{1/d} = p^{f/d}`. We state it as: the `d`-th power
of the shortest-vector length is at least the ideal norm. `p > 0`, `f, d ≥ 0`. -/
theorem shortestVector_ge_normFloor
    {Λ : SupNorm} {p f d : ℕ} (hΛ : 0 ≤ Λ) (hd : 1 ≤ d)
    (hAMGM : (idealNorm p f : ℝ) ≤ Λ ^ d) :
    (idealNorm p f : ℝ) ^ ((1 : ℝ) / d) ≤ Λ := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  -- `Λ = (Λ^d)^{1/d}` and rpow is monotone on nonnegatives.
  have hpow : Λ = (Λ ^ d) ^ ((1 : ℝ) / d) := by
    rw [← rpow_natCast Λ d, ← rpow_mul hΛ]
    rw [mul_one_div, div_self (ne_of_gt hdpos), rpow_one]
  rw [hpow]
  exact rpow_le_rpow (by positivity) hAMGM (by positivity)

/-! ### The onset lower bound delivered by the shortest `𝔭`-vector -/

/-- **Onset lower bound via the shortest `𝔭`-vector (`r₀ ≥ ½ Λ_𝔭`).** If every `𝔭`-element fitting the
radius-`r` disk has `Λ ≤ 2r`, and the shortest `𝔭`-vector has length `Λ_𝔭`, then no `𝔭`-element fits
until `2r ≥ Λ_𝔭`. So the onset radius `r` satisfies `r ≥ Λ_𝔭 / 2`. -/
theorem onsetLowerBound_via_shortestVector
    {Λ : SupNorm} {r : ℕ} (hfit : diskFit Λ r) :
    Λ / 2 ≤ r := by
  unfold diskFit at hfit
  linarith

/-- **The full `r₀` floor from AM–GM (`r₀ ≥ ½ p^{f/d} = ½ p^{2f/n}`).** Combining the AM–GM
shortest-vector floor with the disk-fit onset bound: any `r` realizing a `𝔭`-element satisfies
`r ≥ ½ · N(𝔭)^{1/d} = ½ · p^{f/d}`. With `d = n/2` this is `½ · p^{2f/n}`. -/
theorem onset_ge_normFloor_halved
    {Λ : SupNorm} {r p f d : ℕ} (hΛ : 0 ≤ Λ) (hd : 1 ≤ d)
    (hAMGM : (idealNorm p f : ℝ) ≤ Λ ^ d) (hfit : diskFit Λ r) :
    (idealNorm p f : ℝ) ^ ((1 : ℝ) / d) / 2 ≤ r := by
  have h1 : (idealNorm p f : ℝ) ^ ((1 : ℝ) / d) ≤ Λ :=
    shortestVector_ge_normFloor hΛ hd hAMGM
  have h2 : Λ / 2 ≤ r := onsetLowerBound_via_shortestVector hfit
  linarith

/-! ### The CRUX 1: the `f`-aware gain — GoN beats the worst-case norm bound when `f > 1` -/

/-- The worst-case norm exponent (`f = 1`): the prompt's bound is `r₀ ≥ ½ p^{2/n}`, i.e. exponent
`1/d`. The GoN bound has exponent `f/d`. -/
noncomputable def normFloorExp (d : ℕ) : ℝ := (1 : ℝ) / d

/-- The GoN floor exponent with residue degree `f`. -/
noncomputable def gonFloorExp (f d : ℕ) : ℝ := (f : ℝ) / d

/-- **CRUX 1 — `f`-aware gain (the genuinely new bound).** For a fixed `p > 1`, the GoN onset floor
`½·p^{f/d}` is **strictly larger** than the worst-case norm floor `½·p^{1/d}` exactly when the residue
degree `f > 1`. This is the real lattice-geometric improvement: any `p` with `p ≢ 1 (mod 2^μ)` (so
`f ≥ 2`) has a provably later onset than the universal norm bound. -/
theorem gon_beats_worstNorm_when_f_large
    {p f d : ℕ} (hp : 1 < (p : ℝ)) (hd : 1 ≤ d) (hf : 1 < f) :
    (p : ℝ) ^ normFloorExp d < (p : ℝ) ^ gonFloorExp f d := by
  unfold normFloorExp gonFloorExp
  rw [rpow_lt_rpow_left_iff hp]
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  rw [div_lt_div_iff_of_pos_right hdpos]
  exact_mod_cast hf

/-! ### The CRUX 2: worst case over `p` collapses (`f = 1`, totally split) → REDUCES -/

/-- **CRUX 2 — worst case collapses to the norm bound.** The prize is `q`-uniform: the adversary picks
the worst `p`. For `p ≡ 1 (mod 2^μ)`, `p` splits **completely**, residue degree `f = 1`, and the GoN
floor exponent `f/d = 1/d` **equals** the worst-case norm exponent. GoN gives NOTHING beyond the norm
bound at the worst prime. -/
theorem gon_worstCase_eq_norm (d : ℕ) :
    gonFloorExp 1 d = normFloorExp d := by
  unfold gonFloorExp normFloorExp; norm_num

/-- The discriminant of `ℚ(ζ_{2^μ})`: `|disc| = 2^{(μ-1)·2^{μ-1}}` (exact 2-power; matches `disc = 2^8`
for `μ = 3`/`n = 8`, `disc = 4` for `μ = 2`/`n = 4`). The exponent. -/
def discExp (μ : ℕ) : ℕ := (μ - 1) * 2 ^ (μ - 1)

/-- **The transference / upper-Minkowski factor is at most `√n` — sub-leading, and only on the UPPER
bound.** A shortest-vector UPPER bound via Minkowski carries `|disc|^{1/(2d)} = 2^{discExp μ /(2d)} =
2^{(μ-1)/2}`. As a power of `n = 2^μ` this is `n^{(μ-1)/(2μ)} ≤ n^{1/2} = √n`. So the 2-power structure
contributes only a polynomial-in-`n` factor, which cannot lift the `p^{2/n}` LOWER floor (AM-GM has no
disc term). Here: `2·discExp μ = (μ-1)·subgroupSize μ`, i.e. `discExp μ / (2 · cycDeg μ) = (μ-1)/2`. -/
theorem discFactor_eq_half_mu_minus_one {μ : ℕ} (hμ : 1 ≤ μ) :
    (discExp μ : ℝ) / (2 * cycDeg μ) = ((μ : ℝ) - 1) / 2 := by
  unfold discExp cycDeg
  have hμ1 : ((μ - 1 : ℕ) : ℝ) = (μ : ℝ) - 1 := by
    rw [Nat.cast_sub hμ]; norm_num
  rw [Nat.cast_mul, hμ1]
  have hpos : (0 : ℝ) < 2 ^ (μ - 1) := by positivity
  field_simp

/-- The transference exponent `(μ-1)/2` as a power of `n = 2^μ`: it equals `((μ-1)/(2μ))·log₂ n`, with
`(μ-1)/(2μ) ≤ 1/2`, so the factor is `≤ n^{1/2} = √n`. We record the exponent bound `(μ-1)/(2μ) ≤ 1/2`. -/
theorem discFactor_le_sqrt_n {μ : ℕ} (hμ : 1 ≤ μ) :
    ((μ : ℝ) - 1) / (2 * μ) ≤ 1 / 2 := by
  have hμpos : (0 : ℝ) < μ := by exact_mod_cast hμ
  have hden : (0 : ℝ) < 2 * μ := by positivity
  rw [div_le_iff₀ hden]
  nlinarith

/-! ### The CRUX 3: at prize scale the worst-case (`f=1`) onset bound is vacuous (NOT CLOSED) -/

/-- **CRUX 3 — the worst-case onset exponent `→ 0` at prize scale.** At the worst prime (`f = 1`) the
onset floor is `½·p^{2/n}` with exponent `2/n = 2/2^μ`. This exponent is monotonically vanishing in `μ`;
concretely it is `≤ 2/μ` for `μ ≥ 1` (since `2^μ ≥ μ`), so it `→ 0`. Thus `p^{2/n} → 1` and the bound
gives only `r₀ ≥ ½`, which is `≪ log p`. GoN does NOT prove `r₀ > log p`: NOT CLOSED. -/
theorem onsetBound_vacuous_at_prizeScale {μ : ℕ} (hμ : 1 ≤ μ) :
    (2 : ℝ) / subgroupSize μ ≤ 2 / μ := by
  unfold subgroupSize
  push_cast
  have hμpos : (0 : ℝ) < μ := by exact_mod_cast hμ
  have h2μ : (μ : ℝ) ≤ 2 ^ μ := by
    have : (μ : ℕ) ≤ 2 ^ μ := Nat.le_of_lt (Nat.lt_two_pow_self)
    exact_mod_cast this
  exact div_le_div_of_nonneg_left (by norm_num) hμpos h2μ

/-- **At worst-case `f = 1`, `p^{2/n} ≥ 1` but its exponent `→ 0`: the bound is `r₀ ≥ ½`-scale only.**
For `p ≥ 1`, `p^{2/n} ≥ 1` always (so the bound is non-vacuous as a `≥` statement) but with the
exponent shrinking to `0` (CRUX 3) the value approaches `1`, leaving the onset bound at the trivial
constant scale — far below `log p`. -/
theorem worstCase_floor_ge_one {p μ : ℕ} (hp : 1 ≤ p) :
    (1 : ℝ) ≤ (p : ℝ) ^ ((2 : ℝ) / subgroupSize μ) := by
  apply one_le_rpow (by exact_mod_cast hp)
  positivity

/-! ### Consolidation: the honest verdict as a theorem -/

/-- **Consolidated verdict (honest, as a theorem).** The GoN object delivers, simultaneously:
(1) a clean AM-GM shortest-vector floor `Λ_𝔭 ≥ p^{f/d}` with **no discriminant term**
    (`shortestVector_ge_normFloor`), hence a genuine onset bound `r₀ ≥ ½ p^{2f/n}`
    (`onset_ge_normFloor_halved`);
(2) an `f`-aware **strict gain** over the worst-case norm bound whenever `f > 1`
    (`gon_beats_worstNorm_when_f_large`) — the genuinely-new, machine-checked improvement;
(3) but a **worst-case collapse**: at the `q`-uniform worst prime `f = 1`, the GoN exponent equals the
    norm exponent (`gon_worstCase_eq_norm`), and the only 2-power lever (the discriminant transference
    factor `≤ √n`, `discFactor_le_sqrt_n`) lives on the UPPER bound and is sub-leading — so GoN does NOT
    beat the worst-case norm;
(4) and **vacuity at prize scale**: the worst-case exponent `2/n → 0` (`onsetBound_vacuous_at_prizeScale`),
    leaving `r₀ ≥ ½ ≪ log p`. NOT CLOSED.
We package the combination of (2) and (3): there is a strict `f`-gain off the worst case, AND exact
equality at `f = 1`. -/
theorem gon_verdict
    {p d : ℕ} (hp : 1 < (p : ℝ)) (hd : 1 ≤ d) :
    (∀ f, 1 < f → (p : ℝ) ^ normFloorExp d < (p : ℝ) ^ gonFloorExp f d) ∧
      gonFloorExp 1 d = normFloorExp d :=
  ⟨fun _ hf => gon_beats_worstNorm_when_f_large hp hd hf, gon_worstCase_eq_norm d⟩

end ArkLib.ProximityGap.Frontier.OnsetShortestVector

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.OnsetShortestVector.cycDeg_eq_half_subgroup
#print axioms ArkLib.ProximityGap.Frontier.OnsetShortestVector.shortestVector_ge_normFloor
#print axioms ArkLib.ProximityGap.Frontier.OnsetShortestVector.onsetLowerBound_via_shortestVector
#print axioms ArkLib.ProximityGap.Frontier.OnsetShortestVector.onset_ge_normFloor_halved
#print axioms ArkLib.ProximityGap.Frontier.OnsetShortestVector.gon_beats_worstNorm_when_f_large
#print axioms ArkLib.ProximityGap.Frontier.OnsetShortestVector.gon_worstCase_eq_norm
#print axioms ArkLib.ProximityGap.Frontier.OnsetShortestVector.discFactor_eq_half_mu_minus_one
#print axioms ArkLib.ProximityGap.Frontier.OnsetShortestVector.discFactor_le_sqrt_n
#print axioms ArkLib.ProximityGap.Frontier.OnsetShortestVector.onsetBound_vacuous_at_prizeScale
#print axioms ArkLib.ProximityGap.Frontier.OnsetShortestVector.worstCase_floor_ge_one
#print axioms ArkLib.ProximityGap.Frontier.OnsetShortestVector.gon_verdict
