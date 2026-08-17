/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonanceLogLocalizedOffDiagonal

/-!
# Door-(iv) Lane 2/3 — the coset resonator numerator splits EXACTLY into
# (Parseval diagonal) + (named off-diagonal autocorrelation) (#444)

This file LOCKS, as a single citable kernel-checked identity, the structural claim that is currently
only recorded as PROSE + two separate pieces in `_ResonanceLogLocalizedOffDiagonal`:

> The coset-multiplicative resonator numerator
> `Num = ∑_{b≠0} ‖R(b)‖² ‖η_b‖²` (with `R(b) = ∑_{j∈J} r_j φ_j(b)`)
> decomposes EXACTLY as
> `Num = (Parseval diagonal)  +  (off-diagonal Gauss-period autocorrelation)`,
> where
>  * the DIAGONAL is `‖r‖² · A₁`, `A₁ = ∑_{b≠0} ‖η_b‖²` — the phase-FREE Parseval floor
>    (already proven `= qn − n²` and `√n`-bound source), and
>  * the OFF-DIAGONAL is the `j ≠ j'` part
>    `Off := ∑_{j∈J} ∑_{j'∈J, j'≠j} r_j r̄_{j'} · Γ(j,j')`,
>    `Γ(j,j') := ∑_{b≠0} φ_j(b) φ̄_{j'}(b) ‖η_b‖²` — the Gauss-period spectral autocorrelation
>    at lag `j−j'`, which is NAMED, NOT BOUNDED here.

## Why this is a real, non-redundant contribution (honesty contract §4–§6)

The existing file proves the full numerator EXPANSION (`coset_resonator_numerator_expand`) and,
SEPARATELY, that the DIAGONAL `j=j'` part collapses to `‖r‖²·A₁` (`coset_resonator_diagonal_numerator`).
It does NOT, anywhere, package the EXACT equation `full = diagonal + off-diagonal`. That equation is
the precise, kernel-checkable form of the campaign's standing prose claim:

> *"the diagonal of the coset resonator is exactly the Parseval floor `n`, independent of `r`; the
>  ENTIRE potential gain (log or not) lives in the off-diagonal."*

Locking it makes the localization of the open content to the off-diagonal a THEOREM, not an assertion:
any resonator-route improvement over the bare `√n` floor must come ENTIRELY from `Off`, with `Off`
named exactly as the Gauss-period autocorrelation lag-sum. This is the Lane-2/3 capstone form of the
no-fifth-door obstruction for the coset-multiplicative (Montgomery loglog) resonator route.

This is a PURE algebraic Finset identity (split a double index sum into its diagonal and the
`j'≠j` complement, per inner sum); it is true over any field of the right type by construction and
needs no empirical probing. It makes NO claim about the SIZE of `Off` (that is the open BGK
Ω-input). **No CORE, cancellation, completion, moment, anti-concentration, or capacity claim is made;
`Off` is NAMED, not bounded; CORE `M(μ_n) ≤ C·√(n·log(p/n))` is OPEN throughout.**

All theorems are axiom-clean: `{propext, Classical.choice, Quot.sound}`.
-/

set_option autoImplicit false
set_option linter.style.longLine false


open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta subgroup_gaussSum_secondMoment)

namespace ArkLib.ProximityGap.Frontier.AvResonatorCand1

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The Gauss-period spectral autocorrelation kernel at index pair `(j, j')`:
`Γ(j,j') := ∑_{b≠0} φ_j(b) · φ̄_{j'}(b) · ‖η_b‖²`. This is the inner sum appearing in
`coset_resonator_numerator_expand`; at `j = j'` (unit modulus) it collapses to the Parseval mass
`A₁`, and at `j ≠ j'` it is the lag-`(j−j')` Gauss-period autocorrelation (the open object). -/
noncomputable def autocorrKernel {ι : Type*} (ψ : AddChar F ℂ) (G : Finset F)
    (φ : ι → F → ℂ) (j j' : ι) : ℂ :=
  ∑ b ∈ Finset.univ.erase (0 : F), φ j b * (starRingEnd ℂ) (φ j' b) * ((‖eta ψ G b‖ ^ 2 : ℝ) : ℂ)

/-- **Per-`j` diagonal-extraction of the inner index sum.** For each fixed `j ∈ J`, the inner sum
over `j' ∈ J` splits exactly into its `j' = j` diagonal entry plus the `j' ≠ j` complement:
`∑_{j'∈J} r_j r̄_{j'} Γ(j,j') = r_j r̄_j Γ(j,j) + ∑_{j'∈J, j'≠j} r_j r̄_{j'} Γ(j,j')`. -/
theorem inner_sum_diag_add_offdiag {ι : Type*} [DecidableEq ι] (ψ : AddChar F ℂ) (G : Finset F)
    (J : Finset ι) (r : ι → ℂ) (φ : ι → F → ℂ) {j : ι} (hj : j ∈ J) :
    (∑ j' ∈ J, r j * (starRingEnd ℂ) (r j') * autocorrKernel ψ G φ j j')
      = r j * (starRingEnd ℂ) (r j) * autocorrKernel ψ G φ j j
        + ∑ j' ∈ J.erase j, r j * (starRingEnd ℂ) (r j') * autocorrKernel ψ G φ j j' := by
  rw [← Finset.add_sum_erase J (fun j' => r j * (starRingEnd ℂ) (r j') * autocorrKernel ψ G φ j j') hj]

/-- **The EXACT diagonal/off-diagonal split of the resonator numerator (HEADLINE).**
The full coset-resonator numerator
`Num = ∑_{b≠0} ‖R(b)‖² ‖η_b‖²` equals the Parseval DIAGONAL `‖r‖² · A₁` plus the named OFF-DIAGONAL
Gauss-period autocorrelation sum:

> `(Num : ℂ) = (∑_{j∈J} ‖r_j‖²) · A₁  +  ∑_{j∈J} ∑_{j'∈J.erase j} r_j r̄_{j'} · Γ(j,j')`,

with `A₁ = ∑_{b≠0} ‖η_b‖²` (the phase-free Parseval mass) and `Γ(j,j') = autocorrKernel`.
The off-diagonal term is NAMED here, NOT bounded — it is exactly the open Gauss-period correlation
that the BGK Ω-input would have to control. Requires only the unit-modulus property `‖φ_j b‖ = 1`
(the defining property of the multiplicative coset characters). -/
theorem coset_resonator_numerator_diag_add_offdiag {ι : Type*} [DecidableEq ι] (ψ : AddChar F ℂ)
    (G : Finset F) (J : Finset ι) (r : ι → ℂ) (φ : ι → F → ℂ)
    (hφ : ∀ j ∈ J, ∀ b ∈ Finset.univ.erase (0 : F), ‖φ j b‖ = 1) :
    ((∑ b ∈ Finset.univ.erase (0 : F), ‖cosetResonator J r φ b‖ ^ 2 * ‖eta ψ G b‖ ^ 2 : ℝ) : ℂ)
      = ((∑ j ∈ J, (‖r j‖ ^ 2 : ℝ)) : ℂ)
          * ((∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2 : ℝ) : ℂ)
        + ∑ j ∈ J, ∑ j' ∈ J.erase j,
            r j * (starRingEnd ℂ) (r j') * autocorrKernel ψ G φ j j' := by
  -- Start from the proven full expansion, rewritten with the `autocorrKernel` abbreviation.
  rw [coset_resonator_numerator_expand ψ G J r φ]
  -- Per-`j`, split the inner `j'`-sum into its `j'=j` diagonal and the `j'≠j` complement.
  have hsplit : ∀ j ∈ J,
      (∑ j' ∈ J, r j * (starRingEnd ℂ) (r j')
          * (∑ b ∈ Finset.univ.erase (0 : F),
              φ j b * (starRingEnd ℂ) (φ j' b) * ((‖eta ψ G b‖ ^ 2 : ℝ) : ℂ)))
        = r j * (starRingEnd ℂ) (r j) * autocorrKernel ψ G φ j j
          + ∑ j' ∈ J.erase j, r j * (starRingEnd ℂ) (r j') * autocorrKernel ψ G φ j j' := by
    intro j hj
    exact inner_sum_diag_add_offdiag ψ G J r φ hj
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  -- The diagonal sum collapses (unit modulus) to `‖r‖² · A₁`; the off-diagonal is left named.
  congr 1
  -- Diagonal: `∑_j r_j r̄_j Γ(j,j) = ‖r‖² · A₁` via the proven `coset_resonator_diagonal_numerator`.
  have hdiag := coset_resonator_diagonal_numerator ψ G J r φ hφ
  -- Unfold `autocorrKernel` on the diagonal to match `coset_resonator_diagonal_numerator`'s shape.
  simpa only [autocorrKernel] using hdiag

/-- **Corollary — substrate-instantiated split: `Num = ‖r‖²·(qn − n²) + Off`.** Substituting the
proven Parseval mass `A₁ = q·n − n²` (`parseval_mass_nonzero`, needs `ψ` primitive) into the diagonal
of the headline split, the resonator numerator is

> `(Num : ℂ) = (∑_{j∈J} ‖r_j‖²) · (q·n − n²)  +  Off`,

making manifest that the guaranteed (`r`-independent) part of the numerator is the Parseval mass
`qn − n²` (the `√n` floor) and that ALL `r`-dependence beyond `‖r‖²` lives in the off-diagonal `Off`.
No size claim on `Off`. -/
theorem coset_resonator_numerator_eq_parseval_add_offdiag {ι : Type*} [DecidableEq ι]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (J : Finset ι) (r : ι → ℂ) (φ : ι → F → ℂ)
    (hφ : ∀ j ∈ J, ∀ b ∈ Finset.univ.erase (0 : F), ‖φ j b‖ = 1) :
    ((∑ b ∈ Finset.univ.erase (0 : F), ‖cosetResonator J r φ b‖ ^ 2 * ‖eta ψ G b‖ ^ 2 : ℝ) : ℂ)
      = ((∑ j ∈ J, (‖r j‖ ^ 2 : ℝ)) : ℂ)
          * (((Fintype.card F : ℝ) * G.card - (G.card : ℝ) ^ 2 : ℝ) : ℂ)
        + ∑ j ∈ J, ∑ j' ∈ J.erase j,
            r j * (starRingEnd ℂ) (r j') * autocorrKernel ψ G φ j j' := by
  rw [coset_resonator_numerator_diag_add_offdiag ψ G J r φ hφ]
  rw [parseval_mass_nonzero hψ G]

/-! ## Two structural consequences of the split (Lane-3 constraint form) -/

/-- **Hermitian symmetry of the autocorrelation kernel.** `Γ(j',j) = conj(Γ(j,j'))`: swapping the
index pair conjugates the kernel (the `‖η_b‖²` weight is real, and `φ_j φ̄_{j'} ↦ φ_{j'} φ̄_j` is
conjugation). This is the structural fact that makes the off-diagonal a Hermitian form in `r`, so the
full numerator (manifestly real) stays real: the off-diagonal contribution is automatically real. -/
theorem autocorrKernel_conj_symm {ι : Type*} (ψ : AddChar F ℂ) (G : Finset F) (φ : ι → F → ℂ)
    (j j' : ι) :
    autocorrKernel ψ G φ j' j = (starRingEnd ℂ) (autocorrKernel ψ G φ j j') := by
  unfold autocorrKernel
  rw [map_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  -- conj(φ_j b · conj(φ_{j'} b) · ‖η_b‖²) = φ_{j'} b · conj(φ_j b) · ‖η_b‖²
  rw [map_mul, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  ring

/-- **Single-coset resonator gives NO log (the off-diagonal is empty).** When the resonator support
`J = {j₀}` is a single coset, `J.erase j₀ = ∅`, so the off-diagonal sum in the headline split
VANISHES and the numerator is EXACTLY the Parseval diagonal `‖r‖²·A₁`. Hence a single-coset
resonator can NEVER beat the bare `√n` floor — any log must use ≥ 2 cosets that genuinely correlate
through the off-diagonal Gauss-period autocorrelation. (Constraint lemma; no size claim.) -/
theorem coset_resonator_numerator_single_eq_parseval {ι : Type*} [DecidableEq ι] (ψ : AddChar F ℂ)
    (G : Finset F) (j₀ : ι) (r : ι → ℂ) (φ : ι → F → ℂ)
    (hφ : ∀ b ∈ Finset.univ.erase (0 : F), ‖φ j₀ b‖ = 1) :
    ((∑ b ∈ Finset.univ.erase (0 : F),
        ‖cosetResonator {j₀} r φ b‖ ^ 2 * ‖eta ψ G b‖ ^ 2 : ℝ) : ℂ)
      = ((‖r j₀‖ ^ 2 : ℝ) : ℂ)
          * ((∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ G b‖ ^ 2 : ℝ) : ℂ) := by
  have hφ' : ∀ j ∈ ({j₀} : Finset ι), ∀ b ∈ Finset.univ.erase (0 : F), ‖φ j b‖ = 1 := by
    intro j hj b hb
    rw [Finset.mem_singleton] at hj; subst hj; exact hφ b hb
  rw [coset_resonator_numerator_diag_add_offdiag ψ G {j₀} r φ hφ']
  -- the off-diagonal double sum over `j ∈ {j₀}` reduces to `j = j₀` with `({j₀}).erase j₀ = ∅`, = 0;
  -- the diagonal singleton sum reduces to `‖r j₀‖²`.
  simp [Finset.sum_singleton, Finset.erase_singleton, Finset.sum_empty]

/-! ## The DENOMINATOR side: exact closed form under coset-character orthogonality -/

/-- The denominator kernel `D(j,j') := ∑_{b≠0} φ_j(b) φ̄_{j'}(b)` (the resonator denominator is
`∑_{b≠0} ‖∑_j r_j φ_j(b)‖² = ∑_{j,j'} r_j r̄_{j'} D(j,j')`). At `j=j'` (unit modulus) `D = q−1`;
at `j≠j'` it is the coset-character orthogonality sum (`= 0` for genuine multiplicative characters). -/
noncomputable def denomKernel {ι : Type*} (φ : ι → F → ℂ) (j j' : ι) : ℂ :=
  ∑ b ∈ Finset.univ.erase (0 : F), φ j b * (starRingEnd ℂ) (φ j' b)

/-- **The resonator denominator expands as a double index sum of `denomKernel`.**
`(∑_{b≠0} ‖R(b)‖² : ℂ) = ∑_{j,j'∈J} r_j r̄_{j'} D(j,j')` (Fubini on the `‖R(b)‖²` expansion). -/
theorem coset_resonator_denominator_expand {ι : Type*} (J : Finset ι) (r : ι → ℂ) (φ : ι → F → ℂ) :
    ((∑ b ∈ Finset.univ.erase (0 : F), ‖cosetResonator J r φ b‖ ^ 2 : ℝ) : ℂ)
      = ∑ j ∈ J, ∑ j' ∈ J, r j * (starRingEnd ℂ) (r j') * denomKernel φ j j' := by
  have hperb : ∀ b : F,
      ((‖cosetResonator J r φ b‖ ^ 2 : ℝ) : ℂ)
        = ∑ j ∈ J, ∑ j' ∈ J, r j * (starRingEnd ℂ) (r j') * (φ j b * (starRingEnd ℂ) (φ j' b)) := by
    intro b; exact cosetResonator_normSq_expand J r φ b
  calc ((∑ b ∈ Finset.univ.erase (0 : F), ‖cosetResonator J r φ b‖ ^ 2 : ℝ) : ℂ)
      = ∑ b ∈ Finset.univ.erase (0 : F), ((‖cosetResonator J r φ b‖ ^ 2 : ℝ) : ℂ) := by
        push_cast; ring
    _ = ∑ b ∈ Finset.univ.erase (0 : F),
          ∑ j ∈ J, ∑ j' ∈ J, r j * (starRingEnd ℂ) (r j') * (φ j b * (starRingEnd ℂ) (φ j' b)) :=
        Finset.sum_congr rfl (fun b _ => hperb b)
    _ = ∑ j ∈ J, ∑ j' ∈ J, r j * (starRingEnd ℂ) (r j') * denomKernel φ j j' := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun j' _ => ?_)
        unfold denomKernel
        rw [Finset.mul_sum]

/-- **Under coset-character orthogonality, the denominator is EXACTLY `‖r‖²·(q−1)`.** If the
weights `φ` are unit-modulus on `b≠0` (so `D(j,j) = q−1`) and ORTHOGONAL off-diagonal
(`D(j,j') = 0` for `j≠j'`, the defining property of distinct multiplicative coset characters), then
the full resonator denominator collapses to its diagonal `‖r‖²·(q−1)` with NO off-diagonal
contribution. Combined with the numerator split, the resonator ratio is exactly
`(‖r‖²·A₁ + Off) / (‖r‖²·(q−1))` — the denominator carries no open content; ALL of it is in the
numerator off-diagonal `Off`. -/
theorem coset_resonator_denominator_eq_diagonal_of_orthogonal {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (r : ι → ℂ) (φ : ι → F → ℂ)
    (hdiag : ∀ j ∈ J, denomKernel φ j j = ((Finset.univ.erase (0 : F)).card : ℂ))
    (horth : ∀ j ∈ J, ∀ j' ∈ J, j ≠ j' → denomKernel φ j j' = 0) :
    ((∑ b ∈ Finset.univ.erase (0 : F), ‖cosetResonator J r φ b‖ ^ 2 : ℝ) : ℂ)
      = ((Finset.univ.erase (0 : F)).card : ℂ) * ∑ j ∈ J, r j * (starRingEnd ℂ) (r j) := by
  rw [coset_resonator_denominator_expand J r φ]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  -- inner sum over j': only j'=j survives (orthogonality), giving r_j r̄_j (q−1)
  rw [← Finset.add_sum_erase J (fun j' => r j * (starRingEnd ℂ) (r j') * denomKernel φ j j') hj]
  have hoff : (∑ j' ∈ J.erase j, r j * (starRingEnd ℂ) (r j') * denomKernel φ j j') = 0 := by
    refine Finset.sum_eq_zero (fun j' hj' => ?_)
    have hj'J : j' ∈ J := Finset.mem_of_mem_erase hj'
    have hne : j ≠ j' := (Finset.ne_of_mem_erase hj').symm
    rw [horth j hj j' hj'J hne, mul_zero]
  rw [hoff, add_zero, hdiag j hj]
  ring

end ArkLib.ProximityGap.Frontier.AvResonatorCand1

#print axioms ArkLib.ProximityGap.Frontier.AvResonatorCand1.inner_sum_diag_add_offdiag
#print axioms ArkLib.ProximityGap.Frontier.AvResonatorCand1.coset_resonator_numerator_diag_add_offdiag
#print axioms ArkLib.ProximityGap.Frontier.AvResonatorCand1.coset_resonator_numerator_eq_parseval_add_offdiag
#print axioms ArkLib.ProximityGap.Frontier.AvResonatorCand1.autocorrKernel_conj_symm
#print axioms ArkLib.ProximityGap.Frontier.AvResonatorCand1.coset_resonator_numerator_single_eq_parseval
#print axioms ArkLib.ProximityGap.Frontier.AvResonatorCand1.coset_resonator_denominator_expand
#print axioms ArkLib.ProximityGap.Frontier.AvResonatorCand1.coset_resonator_denominator_eq_diagonal_of_orthogonal
