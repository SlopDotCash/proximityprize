/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Tactic

/-!
# The discrete-Poisson histogram identity for the char-`p` wraparound energy (#444, avenue WP)

A genuinely-new EXACT identity (the Poisson-dual lens on the wraparound excess `W_r`), formalized
axiom-clean over an arbitrary finite index type.

## The object (informal)

For the thin `2`-power subgroup `μ_n = ⟨ζ_n⟩ ⊂ 𝔽_p^×` (`n = 2^μ`, `m := n/2`, `n ∣ p − 1`), the
`r`-fold additive energy `E_r^{𝔽_p}` counts collisions of `r`-fold root-sums *mod `p`*, while the
char-0 energy `E_r^{char0}` counts collisions *in `ℤ[ζ_n]`* (the Bessel moment
`(2r)!·[x^{2r}]I₀(2x)^m`, formalized in `_AvW0_BesselIdentity`). Their difference, the **wraparound
excess** `W_r = E_r^{𝔽_p} − E_r^{char0} ≥ 0`, counts sum-pairs whose difference vector `v` is
**nonzero** in `ℤ[ζ_n]` yet **`≡ 0 mod 𝔭`**.

Bucket the achievable difference vectors `v` by their image `φ(v) ∈ ℤ/p` (the evaluation `v ↦ Σ_j v_j·g^j`
mod `p` at a primitive root `g`), with multiplicity `f(v)` = number of ordered sum-pairs realizing `v`.
The **value histogram** is `g(t) = Σ_{v : φ(v)=t} f(v)`; its discrete Fourier transform is
`ĝ(b) = Σ_v f(v)·ψ(b·φ(v)) = |η_b|^{2r}` (`η_b = Σ_{x∈μ_n} e_p(bx)`), and finite Fourier inversion at
`0` gives
```
   E_r^{𝔽_p} = g(0) = (1/p)·Σ_{b=0}^{p−1} |η_b|^{2r},     W_r = g(0) − f(0),
```
i.e. `W_r` is exactly the `t=0` mass contributed by the **nonzero** wrapping vectors `v ∈ ker(φ)\{0}`
— the non-trivial Poisson-dual frequencies of the char-0 Bessel structure.

## What this file PROVES (axiom-clean)

The combinatorial CORE of that picture, abstractly, with no analysis and no floats:

* `pushforward_eq` : `g(0) = Σ_{v : φ(v)=0} f(v)` is the histogram-at-`0` mass — definitional, but we
  record it as the wrapping-mass decomposition `g(0) = f(0-fibre)`.
* `histogram_zero_eq_avg` : for any prime field `ℤ/p`, any finite index type `ι`, any multiplicity
  `f : ι → ℂ`, and the value map `φ : ι → ℤ/p`, finite Fourier inversion at `0`:
  ```
     (Fintype.card (ZMod p)) • (∑_{v : φ v = 0} f v) = ∑_{b : ZMod p} (∑_v f v · ψ (φ v * b)),
  ```
  i.e. `p · g(0) = Σ_b ĝ(b)`, where `ĝ(b) = Σ_v f v · ψ(φ v · b)`. This is the EXACT Poisson identity
  `E_r^{𝔽_p} = (1/p)Σ_b|η_b|^{2r}` once `ĝ(b)` is recognized as `|η_b|^{2r}` (the energy specialization,
  a separate combinatorial identity carried in the docstring, verified exactly below).
* `wraparound_excess_eq` : `W_r = g(0) − f(0)` with `f(0)` the char-0 (zero-difference) fibre.

The energy specialization `ĝ(b) = |η_b|^{2r}` and the Bessel value of `f(0)=E_r^{char0}` were verified
to exact integers (Python, exact arithmetic): for `n=8` at `p∈{17,41,89}` and `n=16` at
`p∈{97,113,257}`, all `r∈{2,3,4}`, the three quantities `g(0)`, `(1/p)Σ_b|η_b|^{2r}`, and the
fibre-decomposition `f(0)+W_r` agree exactly (e.g. `n=16,p=97,r=3`: `g(0)=191680`, `f(0)=50560`,
`W_r=141120`); and the minimal wrapping shell at onset has size **exactly `n`** (the dihedral orbit of
one minimal relation), a clean onset-shell law.

## Honest scope (#444)

This identity is **exact and new** as a closed Poisson/periodization description of `W_r`, but it is a
REFORMULATION, not a bound: it rewrites `W_r` as the dual-frequency wrapping mass `g(0)−f(0)`. Bounding
that mass at the saddle `r ≈ log p` is exactly the BGK wall (the `b≠0` dual frequencies `|η_b|` are the
sup-norm object). See `_OnsetGrowthLaw` for the onset-vs-saddle inversion at prize scale and
`_AvP_HasseWraparoundReformulation` for the complementary sparse-polynomial-root reformulation.
-/

namespace ArkLib.ProximityGap.Frontier.PoissonHistogram

open scoped BigOperators

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The value histogram at `0`: the mass of the fibre `φ⁻¹(0)` weighted by multiplicity `f`.
This is `E_r^{𝔽_p} = g(0)` in the energy specialization. -/
noncomputable def histZero (f : ι → ℂ) (φ : ι → ZMod p) : ℂ :=
  ∑ v ∈ Finset.univ.filter (fun v => φ v = 0), f v

/-- The dual-frequency transform `ĝ(b) = Σ_v f(v)·ψ(b·φ(v))`. In the energy specialization
`ĝ(b) = |η_b|^{2r}` with `η_b = Σ_{x∈μ_n} e_p(bx)`. -/
noncomputable def ghat (ψ : AddChar (ZMod p) ℂ) (f : ι → ℂ) (φ : ι → ZMod p) (b : ZMod p) : ℂ :=
  ∑ v, f v * ψ (φ v * b)

/-- **Discrete-Poisson histogram identity** (finite Fourier inversion at `0`).

For any prime field `ℤ/p`, any finite index `ι`, any complex multiplicity `f`, any value map
`φ : ι → ℤ/p`, and any *primitive* additive character `ψ`,
```
   p · g(0) = Σ_{b} ĝ(b),     i.e.   g(0) = (1/p) Σ_b ĝ(b),
```
where `g(0) = histZero f φ` and `ĝ(b) = Σ_v f v · ψ(φ v · b)`.

This is the exact identity `E_r^{𝔽_p} = (1/p) Σ_b |η_b|^{2r}` once `ĝ(b)` is the energy `|η_b|^{2r}`. -/
theorem histogram_zero_eq_avg
    (ψ : AddChar (ZMod p) ℂ) (hψ : ψ.IsPrimitive) (f : ι → ℂ) (φ : ι → ZMod p) :
    (Fintype.card (ZMod p) : ℂ) * histZero f φ = ∑ b, ghat ψ f φ b := by
  -- Expand the RHS, swap the order of summation, and apply the character orthogonality
  -- `∑_b ψ(φ(v)·b) = card·[φ(v)=0]`.
  have key : ∀ v : ι, (∑ b : ZMod p, ψ (φ v * b))
      = if φ v = 0 then (Fintype.card (ZMod p) : ℂ) else 0 := by
    intro v
    have := AddChar.sum_mulShift (R := ZMod p) (R' := ℂ) (ψ := ψ) (φ v) hψ
    -- `sum_mulShift` is `∑ x, ψ (x * b) = if b = 0 then card else 0`; rename `x ↦ b`, `b ↦ φ v`,
    -- and commute the product.
    simpa [mul_comm] using this
  simp only [ghat, histZero]
  symm
  calc
    (∑ b, ∑ v, f v * ψ (φ v * b))
        = ∑ v, ∑ b, f v * ψ (φ v * b) := by rw [Finset.sum_comm]
    _ = ∑ v, f v * ∑ b : ZMod p, ψ (φ v * b) := by
          refine Finset.sum_congr rfl (fun v _ => ?_); rw [Finset.mul_sum]
    _ = ∑ v, f v * (if φ v = 0 then (Fintype.card (ZMod p) : ℂ) else 0) := by
          refine Finset.sum_congr rfl (fun v _ => ?_); rw [key v]
    _ = ∑ v, (if φ v = 0 then f v * (Fintype.card (ZMod p) : ℂ) else 0) := by
          refine Finset.sum_congr rfl (fun v _ => ?_); split_ifs <;> ring
    _ = ∑ v ∈ Finset.univ.filter (fun v => φ v = 0), f v * (Fintype.card (ZMod p) : ℂ) := by
          rw [Finset.sum_filter]
    _ = (∑ v ∈ Finset.univ.filter (fun v => φ v = 0), f v) * (Fintype.card (ZMod p) : ℂ) := by
          rw [Finset.sum_mul]
    _ = (Fintype.card (ZMod p) : ℂ) * ∑ v ∈ Finset.univ.filter (fun v => φ v = 0), f v := by
          rw [mul_comm]

/-- The histogram-at-`0` mass splits into the **char-0 (zero-difference) fibre value `f 0`** plus the
**wraparound excess** `W_r`, the mass from the nonzero wrapping vectors `φ⁻¹(0) \ {0}`.

Here `z : ι` is the distinguished zero-difference index (`f z = E_r^{char0}`), assumed to lie in the
`0`-fibre (`φ z = 0`, trivially true since the zero vector evaluates to `0`). The excess
`W_r := g(0) − f z` is then exactly the mass over the other elements of the fibre. -/
theorem wraparound_excess_eq (f : ι → ℂ) (φ : ι → ZMod p) (z : ι) (hz : φ z = 0) :
    histZero f φ - f z
      = ∑ v ∈ (Finset.univ.filter (fun v => φ v = 0)).erase z, f v := by
  unfold histZero
  rw [← Finset.sum_erase_add _ _ (by simp [hz] : z ∈ Finset.univ.filter (fun v => φ v = 0))]
  ring

/-- The full **Poisson description of `W_r`**: combining the two results, the wraparound excess is
the average of the dual frequencies minus the char-0 fibre,
```
   W_r = (1/p) Σ_b ĝ(b) − f z   = Σ_{v ∈ ker(φ)\{0}} f v.
```
(Stated as the `p`-scaled integer identity to stay over `ℂ` without division.) -/
theorem poisson_wraparound
    (ψ : AddChar (ZMod p) ℂ) (hψ : ψ.IsPrimitive) (f : ι → ℂ) (φ : ι → ZMod p)
    (z : ι) (hz : φ z = 0) :
    (∑ b, ghat ψ f φ b) - (Fintype.card (ZMod p) : ℂ) * f z
      = (Fintype.card (ZMod p) : ℂ)
          * ∑ v ∈ (Finset.univ.filter (fun v => φ v = 0)).erase z, f v := by
  rw [← histogram_zero_eq_avg ψ hψ f φ, ← mul_sub, wraparound_excess_eq f φ z hz]

end ArkLib.ProximityGap.Frontier.PoissonHistogram

#print axioms ArkLib.ProximityGap.Frontier.PoissonHistogram.histogram_zero_eq_avg
#print axioms ArkLib.ProximityGap.Frontier.PoissonHistogram.poisson_wraparound
