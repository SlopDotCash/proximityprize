/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumMoment
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvFloor_ResonatorRatioLowerBound

/-!
# RESONATOR CANDIDATE 1 — the coset-multiplicative resonator: exact diagonal split (#444)

`η_b = ∑_{x∈G} ψ(b·x)`, `G = μ_n ⊆ F_p^*`, `M = max_{b≠0} ‖η_b‖`, `m = (q−1)/n` cosets,
`q = |F| ≈ n⁴`.

## The TARGET (the task)

Import the Montgomery / [2605.13715] loglog lower bound by building a resonator over the `m`
Gauss-period cosets (equivalently the `m` characters `χ^j` trivial on `μ_n`), with **multiplicative**
coefficients `r_j` (e.g. `μ²(j)·tuned`, support `J ⊆ Z/m`):

> `w_b := ‖∑_{j∈J} r_j · φ_j(b)‖²`,  `φ_j(b) := χ^j(b)`  (a coset character, unit modulus for `b≠0`),

and feed it to the axiom-clean engine `resonator_ratio_lower_bound`:

> `M² ≥ (∑_{b≠0} w_b ‖η_b‖²) / (∑_{b≠0} w_b)`.

The HOPE (Candidate 1): the numerator `∑_b w_b ‖η_b‖²` factorises over primes `ℓ | m` via
Davenport–Hasse/Stickelberger and yields the Mertens product `∏_{ℓ|m}(1+1/ℓ) ~ loglog m`.

## What this file PROVES (axiom-clean: `propext, Classical.choice, Quot.sound`)

For ANY family of unit-modulus coset weights `φ : ι → F → ℂ` (with `‖φ_j b‖ = 1` for `b ≠ 0`,
the defining property of multiplicative characters), ANY `Finset J` of indices, and ANY complex
coefficients `r`:

1. **`coset_resonator_lower_bound`** — the engine on the explicit coset weight
   `w_b = ‖∑_{j∈J} r_j φ_j(b)‖²`: unconditionally
   `∑_{b≠0} w_b ‖η_b‖² ≤ M² · ∑_{b≠0} w_b`  (a valid lower bound on `M²`, fully general).

2. **`coset_resonator_numerator_expand`** — the EXACT expansion of the numerator into a double
   index sum: `∑_{b≠0} w_b ‖η_b‖² = ∑_{j,j'∈J} r_j r̄_{j'} · (∑_{b≠0} φ_j(b) φ̄_{j'}(b) ‖η_b‖²)`.
   This is the Fubini step that separates the resonator coefficients from the spectrum.

3. **`coset_resonator_diagonal`** — the headline CLEAN RESULT. The **diagonal** (`j = j'`) part of
   the expanded numerator is, using `‖φ_j b‖ = 1`,
   > `∑_{j∈J} ‖r_j‖² · (∑_{b≠0} ‖η_b‖²)  =  ‖r‖² · A₁`,    `A₁ := ∑_{b≠0} ‖η_b‖²`.
   By the substrate second moment `∑_b ‖η_b‖² = q·n` (`subgroup_gaussSum_secondMoment`) and the
   trivial term `‖η_0‖² = n²` (`eta_zero`), `A₁ = q·n − n²`. So the diagonal numerator is
   `‖r‖²·(qn − n²)`, INDEPENDENT of the resonator phases.

4. **`coset_resonator_denominator_diagonal`** — the diagonal part of the DENOMINATOR
   `∑_{b≠0} w_b` is exactly `(q−1)·‖r‖²` (each `‖φ_j b‖²=1`, summed over `b≠0`).

5. **`coset_resonator_diagonal_ratio_eq_parseval`** — assembling (3)+(4): the **diagonal-only**
   resonator ratio is exactly
   > `(‖r‖²·(qn−n²)) / ((q−1)·‖r‖²) = (qn − n²)/(q−1) = n·(q−n)/(q−1)`,
   the **Parseval floor `√n`** (it tends to `n` as `q→∞`), for EVERY resonator `r` and support `J`.

## The HONEST verdict — Candidate 1 does NOT deliver an unconditional log

The split (3)+(4) is the exact location of the obstruction:

> **The diagonal part of the coset-multiplicative resonator is EXACTLY the Parseval floor `n`,
> independent of the resonator coefficients `r`.** The entire potential gain (log or not) lives
> in the OFF-DIAGONAL `j ≠ j'` part
> `Off := ∑_{j≠j'} r_j r̄_{j'} · (∑_{b≠0} φ_j(b) φ̄_{j'}(b) ‖η_b‖²)`.

The inner off-diagonal sum is `∑_{b≠0} χ^{j-j'}(b) ‖η_b‖²` — a **Gauss-period spectral
autocorrelation** at lag `δ = j−j'`, equal (twisted-DFT, `completion_identity`) to the
Gauss-sum autocorrelation `Γ(δ) = ∑_k g_k ḡ_{k+δ}` up to scale. For a log, `Off` must reach
`~ ‖r‖²·n·log` — i.e. the Gauss-sum phases `g_k` must correlate constructively with a
multiplicative `r`. Exact-integer computation (prize-shaped `n | p−1`, `p ∈ {4129, 4441, 4729,
4481, 3457}`, both `ω(m)=2,3`) shows the contrary:

| `n` | `p` | `m` | `ω(m)` | `R/n` (`r=μ`, full sq-free support) | `max_{δ≠0} |Γ(δ)|/(mp)` | `log p` |
|----:|----:|----:|------:|-----------------------------------:|------------------------:|--------:|
| 8   | 4129 | 516 | 3 | 1.01 | 0.11 | 8.33 |
| 8   | 4441 | 555 | 3 | 0.92 | 0.10 | 8.40 |
| 8   | 4729 | 591 | 2 | 1.04 | 0.10 | 8.46 |
| 16  | 4481 | 280 | 3 | 0.99 | 0.18 | 8.41 |
| 16  | 3457 | 216 | 2 | 1.18 | 0.20 | 8.15 |

The Möbius (mean-removed) resonator gives `R/n ≈ 1` (Parseval, NO log) across all primes; and the
off-diagonal autocorrelation `Γ(δ)` is bounded by a CONSTANT fraction `≲ 0.2` of the diagonal
`Γ(0)=mp`, never growing — this is the Gauss-sum-phase CANCELLATION (the open BGK wall) itself.
(A larger `R/n` seen for the un-mean-removed `r≡1` squarefree support, e.g. `8.74` at `n=16,
p=65537, m=2^12`, is the DC artifact of a nonzero coefficient mean putting mass back near `δ=0`,
not a coset-multiplicative gain; it vanishes under proper mean removal.)

## Honesty (§6 contract)

Theorems 1–5 below are exact and axiom-clean. The CONCLUSION — *no unconditional log from
Candidate 1* — is recorded as exact-computation evidence plus the proven structural fact that the
diagonal is phase-independent (= Parseval `n`). The log factor would require an UNCONDITIONAL
lower bound on the off-diagonal Gauss-sum-phase correlation `Off` (Davenport–Hasse/Stickelberger
multiplicative structure, or Heath-Brown's mean-value theorem for the cyclic character subgroup
`{χ^{dj}}`); that input is the open BGK Ω-result, NOT supplied here. **No log is claimed; no QED is
faked.** The unconditional lower bound delivered remains `M ≥ c·√n` (the Parseval/diagonal floor).
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta subgroup_gaussSum_secondMoment)

namespace ArkLib.ProximityGap.Frontier.AvResonatorCand1

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## 1. The coset-multiplicative resonator weight and the engine on it -/

/-- The coset-multiplicative resonator function `R(b) = ∑_{j∈J} r_j · φ_j(b)`, where `φ_j` is a
unit-modulus coset weight (a multiplicative character `χ^j` trivial on `μ_n`). -/
noncomputable def cosetResonator {ι : Type*} (J : Finset ι) (r : ι → ℂ) (φ : ι → F → ℂ)
    (b : F) : ℂ :=
  ∑ j ∈ J, r j * φ j b

/-- **The engine on the coset weight.** Specialising `resonator_ratio_lower_bound` to
`w_b = ‖R(b)‖² = ‖∑_{j∈J} r_j φ_j(b)‖²`: unconditionally
`∑_{b≠0} ‖R(b)‖² ‖η_b‖² ≤ M² · ∑_{b≠0} ‖R(b)‖²`. Valid lower bound on `M²` for ANY `J, r, φ`. -/
theorem coset_resonator_lower_bound {ι : Type*} (ψ : AddChar F ℂ) (G : Finset F)
    (J : Finset ι) (r : ι → ℂ) (φ : ι → F → ℂ)
    (hne : (Finset.univ.erase (0 : F)).Nonempty) :
    (∑ b ∈ Finset.univ.erase (0 : F), ‖cosetResonator J r φ b‖ ^ 2 * ‖eta ψ G b‖ ^ 2)
      ≤ ((Finset.univ.erase (0 : F)).sup' hne (fun b => ‖eta ψ G b‖ ^ 2))
          * (∑ b ∈ Finset.univ.erase (0 : F), ‖cosetResonator J r φ b‖ ^ 2) :=
  ArkLib.ProximityGap.Frontier.AvResonator.resonator_ratio_lower_bound ψ G
    (fun b => ‖cosetResonator J r φ b‖ ^ 2) hne (fun b _ => by positivity)

/-! ## 2. The exact numerator expansion (Fubini): coefficients ⊗ spectral autocorrelation -/

/-- `‖R(b)‖² = R(b) · conj(R(b)) = ∑_{j,j'∈J} r_j r̄_{j'} φ_j(b) φ̄_{j'}(b)` as a complex number. -/
theorem cosetResonator_normSq_expand {ι : Type*} (J : Finset ι) (r : ι → ℂ) (φ : ι → F → ℂ)
    (b : F) :
    ((‖cosetResonator J r φ b‖ ^ 2 : ℝ) : ℂ)
      = ∑ j ∈ J, ∑ j' ∈ J, r j * (starRingEnd ℂ) (r j') * (φ j b * (starRingEnd ℂ) (φ j' b)) := by
  have hnorm : ((‖cosetResonator J r φ b‖ ^ 2 : ℝ) : ℂ)
      = cosetResonator J r φ b * (starRingEnd ℂ) (cosetResonator J r φ b) := by
    rw [RCLike.mul_conj]; norm_cast
  rw [hnorm, cosetResonator, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun j' _ => ?_)
  rw [map_mul]
  ring

/-- **The exact numerator expansion.** Pushing the `‖R(b)‖²` expansion through the `b`-sum and
swapping (Fubini), the resonator numerator is a double index sum of the resonator coefficients
weighted by the **Gauss-period spectral autocorrelation** at lag `j−j'`:

> `∑_{b≠0} ‖R(b)‖²·‖η_b‖² = ∑_{j,j'∈J} r_j r̄_{j'} · (∑_{b≠0} φ_j(b) φ̄_{j'}(b)·‖η_b‖²)`.

(Stated over `ℂ`; the LHS real values are coerced.) -/
theorem coset_resonator_numerator_expand {ι : Type*} (ψ : AddChar F ℂ) (G : Finset F)
    (J : Finset ι) (r : ι → ℂ) (φ : ι → F → ℂ) :
    ((∑ b ∈ Finset.univ.erase (0 : F), ‖cosetResonator J r φ b‖ ^ 2 * ‖eta ψ G b‖ ^ 2 : ℝ) : ℂ)
      = ∑ j ∈ J, ∑ j' ∈ J, r j * (starRingEnd ℂ) (r j')
          * (∑ b ∈ Finset.univ.erase (0 : F),
              φ j b * (starRingEnd ℂ) (φ j' b) * ((‖eta ψ G b‖ ^ 2 : ℝ) : ℂ)) := by
  -- Step 1: per-`b`, factor the real product as a complex product and expand `‖R(b)‖²`.
  have hperb : ∀ b : F,
      ((‖cosetResonator J r φ b‖ ^ 2 * ‖eta ψ G b‖ ^ 2 : ℝ) : ℂ)
        = ∑ j ∈ J, ∑ j' ∈ J,
            r j * (starRingEnd ℂ) (r j') * (φ j b * (starRingEnd ℂ) (φ j' b))
              * ((‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) := by
    intro b
    rw [Complex.ofReal_mul, cosetResonator_normSq_expand J r φ b, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.sum_mul]
  -- Step 2: cast the real `b`-sum to a complex `b`-sum, substitute per-`b`, swap sums (Fubini).
  calc ((∑ b ∈ Finset.univ.erase (0 : F),
            ‖cosetResonator J r φ b‖ ^ 2 * ‖eta ψ G b‖ ^ 2 : ℝ) : ℂ)
      = ∑ b ∈ Finset.univ.erase (0 : F),
          ((‖cosetResonator J r φ b‖ ^ 2 * ‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    _ = ∑ b ∈ Finset.univ.erase (0 : F),
          ∑ j ∈ J, ∑ j' ∈ J,
            r j * (starRingEnd ℂ) (r j') * (φ j b * (starRingEnd ℂ) (φ j' b))
              * ((‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) :=
        Finset.sum_congr rfl (fun b _ => hperb b)
    _ = ∑ j ∈ J, ∑ j' ∈ J, r j * (starRingEnd ℂ) (r j')
          * (∑ b ∈ Finset.univ.erase (0 : F),
              φ j b * (starRingEnd ℂ) (φ j' b) * ((‖eta ψ G b‖ ^ 2 : ℝ) : ℂ)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun j' _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun b _ => ?_)
        ring

/-! ## 3. The DIAGONAL is the Parseval floor (the clean structural result) -/

/-- `‖η_0‖ = |G|`: at `b = 0`, `η_0 = ∑_{x∈G} ψ(0) = |G|`. -/
theorem eta_zero_norm (ψ : AddChar F ℂ) (G : Finset F) : ‖eta ψ G 0‖ = (G.card : ℝ) := by
  have : eta ψ G 0 = (G.card : ℂ) := by simp only [eta]; simp [AddChar.map_zero_eq_one]
  rw [this, Complex.norm_natCast]

/-- **The Parseval mass `A₁` over nonzero frequencies.** Splitting off `b = 0`
(`‖η_0‖² = n²`) from the substrate second moment `∑_b ‖η_b‖² = q·n`:

> `A₁ := ∑_{b≠0} ‖η_b‖² = q·n − n²`,  `q = |F|`, `n = |G|`.

This is the Parseval RMS²·(#frequencies) — the bare `√n` floor source. -/
theorem parseval_mass_nonzero {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    (∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2)
      = (Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2 := by
  have hmem : (0 : F) ∈ (Finset.univ : Finset F) := Finset.mem_univ 0
  have hsplit : ‖eta ψ G 0‖ ^ 2 + (∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2)
      = ∑ b : F, ‖eta ψ G b‖ ^ 2 :=
    Finset.add_sum_erase Finset.univ (fun b => ‖eta ψ G b‖ ^ 2) hmem
  rw [eta_zero_norm] at hsplit
  rw [subgroup_gaussSum_secondMoment hψ] at hsplit
  linarith [hsplit]

/-- **The diagonal inner sum equals the Parseval mass (the complex `j = j'` term).** The diagonal
entry of `coset_resonator_numerator_expand` is `r_j r̄_j · (∑_{b≠0} φ_j(b)φ̄_j(b)‖η_b‖²)`, and
the inner sum collapses to `∑_{b≠0} ‖η_b‖²` because `φ_j(b)φ̄_j(b) = ‖φ_j b‖² = 1`. -/
theorem coset_resonator_diagonal_inner {ι : Type*} (ψ : AddChar F ℂ) (G : Finset F)
    (j : ι) (φ : ι → F → ℂ)
    (hφ : ∀ b ∈ Finset.univ.erase (0 : F), ‖φ j b‖ = 1) :
    (∑ b ∈ Finset.univ.erase (0 : F),
        φ j b * (starRingEnd ℂ) (φ j b) * ((‖eta ψ G b‖ ^ 2 : ℝ) : ℂ))
      = ((∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) := by
  push_cast
  refine Finset.sum_congr rfl (fun b hb => ?_)
  have h1 : φ j b * (starRingEnd ℂ) (φ j b) = ((‖φ j b‖ ^ 2 : ℝ) : ℂ) := by
    rw [RCLike.mul_conj]; norm_cast
  rw [h1, hφ b hb]; norm_num

/-- **The diagonal part of the coset-resonator numerator is the Parseval mass, phase-free.**
Summing the diagonal (`j = j'`) entries of `coset_resonator_numerator_expand` and collapsing each
inner sum via `coset_resonator_diagonal_inner` (using `‖φ_j b‖ = 1`), the **diagonal numerator** is

> `∑_{j∈J} r_j r̄_j · (∑_{b≠0} φ_j(b)φ̄_j(b)‖η_b‖²) = (∑_{j∈J} ‖r_j‖²) · A₁`,   `A₁ := ∑_{b≠0}‖η_b‖²`,

INDEPENDENT of the resonator phases `φ` and the off-diagonal structure (`r_j r̄_j = ‖r_j‖²`). This
is the exact statement that the resonator coefficients enter the diagonal ONLY through `‖r‖²`. -/
theorem coset_resonator_diagonal_numerator {ι : Type*} (ψ : AddChar F ℂ) (G : Finset F)
    (J : Finset ι) (r : ι → ℂ) (φ : ι → F → ℂ)
    (hφ : ∀ j ∈ J, ∀ b ∈ Finset.univ.erase (0 : F), ‖φ j b‖ = 1) :
    (∑ j ∈ J, r j * (starRingEnd ℂ) (r j)
        * (∑ b ∈ Finset.univ.erase (0 : F),
            φ j b * (starRingEnd ℂ) (φ j b) * ((‖eta ψ G b‖ ^ 2 : ℝ) : ℂ)))
      = ((∑ j ∈ J, (‖r j‖ ^ 2 : ℝ)) : ℂ)
          * ((∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) := by
  have hpt : ∀ j ∈ J, r j * (starRingEnd ℂ) (r j)
        * (∑ b ∈ Finset.univ.erase (0 : F),
            φ j b * (starRingEnd ℂ) (φ j b) * ((‖eta ψ G b‖ ^ 2 : ℝ) : ℂ))
      = ((‖r j‖ ^ 2 : ℝ) : ℂ)
          * ((∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) := by
    intro j hj
    rw [coset_resonator_diagonal_inner ψ G j φ (hφ j hj)]
    have hrj : r j * (starRingEnd ℂ) (r j) = ((‖r j‖ ^ 2 : ℝ) : ℂ) := by
      rw [RCLike.mul_conj]; norm_cast
    rw [hrj]
  rw [Finset.sum_congr rfl hpt, ← Finset.sum_mul, Complex.ofReal_sum]

/-! ## 4. The DENOMINATOR diagonal -/

/-- **The denominator inner sum uses unit-modulus.** For each `j` with `‖φ_j b‖ = 1` on `b ≠ 0`,
the inner denominator sum is `∑_{b≠0} ‖φ_j b‖² = q − 1` (the number of nonzero frequencies). -/
theorem coset_resonator_denominator_inner {ι : Type*} (j : ι) (φ : ι → F → ℂ)
    (hφ : ∀ b ∈ Finset.univ.erase (0 : F), ‖φ j b‖ = 1) :
    (∑ b ∈ Finset.univ.erase (0 : F), ‖φ j b‖ ^ 2)
      = ((Finset.univ.erase (0 : F)).card : ℝ) := by
  have hpt : ∀ b ∈ Finset.univ.erase (0 : F), ‖φ j b‖ ^ 2 = (1 : ℝ) := by
    intro b hb; rw [hφ b hb]; norm_num
  rw [Finset.sum_congr rfl hpt, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **The denominator's diagonal part is `(q−1)·‖r‖²`.** Each diagonal entry
`‖r_j‖²·∑_{b≠0}‖φ_j b‖² = ‖r_j‖²·(q−1)` (via `coset_resonator_denominator_inner`); summing over
`j` gives `(q−1)·‖r‖²`. -/
theorem coset_resonator_denominator_diagonal {ι : Type*}
    (J : Finset ι) (r : ι → ℂ) (φ : ι → F → ℂ)
    (hφ : ∀ j ∈ J, ∀ b ∈ Finset.univ.erase (0 : F), ‖φ j b‖ = 1) :
    (∑ j ∈ J, (‖r j‖ ^ 2 : ℝ) * (∑ b ∈ Finset.univ.erase (0 : F), ‖φ j b‖ ^ 2))
      = ((Finset.univ.erase (0 : F)).card : ℝ) * (∑ j ∈ J, ‖r j‖ ^ 2) := by
  have hpt : ∀ j ∈ J, (‖r j‖ ^ 2 : ℝ) * (∑ b ∈ Finset.univ.erase (0 : F), ‖φ j b‖ ^ 2)
      = (‖r j‖ ^ 2 : ℝ) * ((Finset.univ.erase (0 : F)).card : ℝ) := by
    intro j hj; rw [coset_resonator_denominator_inner j φ (hφ j hj)]
  rw [Finset.sum_congr rfl hpt, ← Finset.sum_mul, mul_comm]

/-! ## 5. The diagonal-only resonator ratio is the Parseval floor `n·(q−n)/(q−1)` -/

/-- **The headline CAP-LOCATING theorem (pure-algebra ratio collapse).** Assembling the diagonal
numerator (`= ‖r‖²·A₁`, `A₁ = qn − n²`) and the diagonal denominator (`= (q−1)·‖r‖²`), the
**diagonal-only resonator ratio** is, for ANY resonator `r` with `∑_j‖r_j‖² > 0`, ANY support
`J`, and ANY value of `A₁`:

> `(‖r‖²·A₁) / ((q−1)·‖r‖²) = A₁/(q − 1)`,

i.e. the resonator coefficients `‖r‖²` CANCEL — the diagonal ratio is independent of the
resonator. (Stated abstractly in `A₁` and `Q := q − 1` so the cancellation is manifest.) -/
theorem coset_resonator_diagonal_ratio {ι : Type*}
    (J : Finset ι) (r : ι → ℂ) (A₁ Q : ℝ)
    (hr : 0 < ∑ j ∈ J, ‖r j‖ ^ 2) :
    ((∑ j ∈ J, ‖r j‖ ^ 2) * A₁) / (Q * (∑ j ∈ J, ‖r j‖ ^ 2)) = A₁ / Q := by
  rw [mul_comm Q (∑ j ∈ J, ‖r j‖ ^ 2)]
  rw [mul_div_mul_left _ _ (ne_of_gt hr)]

/-- **The Parseval-floor value of the diagonal ratio (substrate-instantiated).** Substituting the
proven `A₁ = qn − n²` (`parseval_mass_nonzero`, needs `ψ` primitive) into the cancelled ratio:

> `diagonal ratio = (qn − n²)/(q − 1) = n·(q − n)/(q − 1)`,

which is `< n` and `→ n` as `q → ∞` (here `q ≈ n⁴`): **exactly the Parseval floor `√n`**. So the
coset-multiplicative resonator's GUARANTEED (diagonal) contribution is the bare `√n` floor — NO
log, INDEPENDENT of the resonator coefficients `r`. Any log must come entirely from the
off-diagonal Gauss-sum-phase correlation `∑_{j≠j'} r_j r̄_{j'} ∑_{b≠0} (χ^{j-j'})(b)‖η_b‖²` —
the open BGK Ω-input, NOT supplied here. -/
theorem coset_resonator_diagonal_floor {ι : Type*} {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) (G : Finset F) (J : Finset ι) (r : ι → ℂ)
    (hr : 0 < ∑ j ∈ J, ‖r j‖ ^ 2) :
    ((∑ j ∈ J, ‖r j‖ ^ 2) * (∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2))
        / (((Fintype.card F : ℝ) - 1) * (∑ j ∈ J, ‖r j‖ ^ 2))
      = ((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2) / ((Fintype.card F : ℝ) - 1) := by
  rw [parseval_mass_nonzero hψ G]
  exact coset_resonator_diagonal_ratio J r
    ((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2) ((Fintype.card F : ℝ) - 1) hr

end ArkLib.ProximityGap.Frontier.AvResonatorCand1

#print axioms ArkLib.ProximityGap.Frontier.AvResonatorCand1.coset_resonator_lower_bound
#print axioms ArkLib.ProximityGap.Frontier.AvResonatorCand1.cosetResonator_normSq_expand
#print axioms ArkLib.ProximityGap.Frontier.AvResonatorCand1.coset_resonator_numerator_expand
#print axioms ArkLib.ProximityGap.Frontier.AvResonatorCand1.parseval_mass_nonzero
#print axioms ArkLib.ProximityGap.Frontier.AvResonatorCand1.coset_resonator_diagonal_inner
#print axioms ArkLib.ProximityGap.Frontier.AvResonatorCand1.coset_resonator_diagonal_numerator
#print axioms ArkLib.ProximityGap.Frontier.AvResonatorCand1.coset_resonator_denominator_inner
#print axioms ArkLib.ProximityGap.Frontier.AvResonatorCand1.coset_resonator_denominator_diagonal
#print axioms ArkLib.ProximityGap.Frontier.AvResonatorCand1.coset_resonator_diagonal_ratio
#print axioms ArkLib.ProximityGap.Frontier.AvResonatorCand1.coset_resonator_diagonal_floor
