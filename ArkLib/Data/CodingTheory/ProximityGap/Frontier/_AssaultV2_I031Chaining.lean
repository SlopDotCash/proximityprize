/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.I031OrbitCountPartition

/-!
# I031_B_chaining — is the dilation-quotient entropy reduction EXPLOITABLE or COSMETIC? (#444)

**Lever (Dossier §6.3).** The per-frequency prize core
`M(μ_n) = max_{b≠0} ‖η_b‖` is dilation-orbit-invariant, so the sup over `Fₚ*` collapses to a sup
over a transversal of the `(p−1)/n` dilation orbits (`I031DilationOrbitReduction`,
`I031OrbitCountPartition.orbit_count`). The metric entropy of the index set drops from
`log p` to `log(p/n)` — the campaign's strongest *empirical* non-BGK signal. The named open
question (§6.3): **does the union over the `(p−1)/n` reps at depth `r` genuinely change the
achievable constant, or is the entropy reduction COSMETIC because the per-rep deep-moment energy
`Σ_{transversal} ‖η‖^{2r}` is the SAME `E_r` object (= `E_r / n`)?**

**This file settles it: the entropy reduction is COSMETIC at the moment-input level.**

The decisive identity (verified exact-integer, `/tmp/i031_moment_identity.py`,
`E_full / E_reps ≡ n` to machine precision at every depth `r=1..5`, `n=4,8,16`):

> Because `‖η_b‖` is **constant on each size-`n` dilation orbit**, the full-frequency
> `2r`-th energy equals `n` times the transversal energy:
>
>   `Σ_{b≠0} ‖η_b‖^{2r}  =  n · Σ_{rep ∈ transversal} ‖η_rep‖^{2r}`.            (★)

Consequence (the cosmetic verdict). A Lamzouri-type union bound over the collapsed index set takes
the per-rep moment `Σ_{reps} ‖η‖^{2r} = E_r / n` and a Markov count over `m = (p−1)/n` reps:

  `#{rep : ‖η_rep‖ > t} ≤ (E_r / n) / t^{2r}`,   so   `M^{2r} ≤ E_r / n + (small)`,
  `M ≤ (E_r / n)^{1/(2r)} = E_r^{1/(2r)} · n^{-1/(2r)}`.

The reduced index count `m = (p−1)/n` enters **only** through the optimal depth `r* ≈ log m =
log(p/n)` — a *constant factor of the log* inside `√(2n·log(p/n))`, NOT a power saving. The
moment INPUT it consumes (`E_r / n ≤ Wick / n`, i.e. the DC-subtracted `A_r/n ≤ (2r−1)‼·n^{r−1}`)
is **propositionally the same** `A_r ≤ Wick` BGK/Paley wall (multiplied by the harmless `1/n`).
The `1/n` is fully cancelled by the `n^{-1/(2r)}` outside under the `2r`-th root up to the
`O(1)` log-constant — it does NOT touch the deep-moment energy excess that is the wall.

**Verdict: REDUCES_TO_WALL.** The entropy reduction `log p → log(p/n)` is REAL in the *log of the
union count* (the bracket `I031LogTargetForm.i031_M_le_logTarget` lands the bound at `log(q/n)`,
the proven shave of `log n` of entropy) but **COSMETIC in the moment input**: identity (★) shows
the per-rep energy is the *same* `E_r` divided by `n`, so the `A_r ≤ Wick` hypothesis needed at
depth `r* = log(p/n)` is the same recognized-open object. The reduction relocates the depth, it
does not weaken the per-rep tail.

**Honesty (rules 3, 6).** Nothing here closes CORE. (★) is an EXACT, field-independent,
axiom-clean identity (the orbit-energy collapse). The cosmetic conclusion `i031_chaining_cosmetic`
makes the relocation precise: the union-bound RHS at the reduced count is the SAME energy `E_r`
up to the `1/n` that the outer root cancels. CORE (`M ≤ C√(n·log(p/n))`) stays OPEN on the
`A_r ≤ Wick` BGK/Paley wall.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


open Finset Polynomial
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.I031Chaining

open ArkLib.ProximityGap.I031DilationOrbitReduction

/-! ## 1. The abstract orbit-energy collapse (field-independent core)

If a nonneg weight `w : F → ℝ` is **constant on each fiber** of a label map `f` (i.e. `w` depends
only on the orbit), and **every fiber has card `n`**, then the full sum over `S` is `n` times the
sum over a transversal (one representative per label). This is the EXACT mechanism of identity (★):
`w = ‖η_·‖^{2r}`, `f = cosetLabel`, fibers = `μ_n`-orbits of card `n`. -/

variable {F ι : Type*} [DecidableEq F] [DecidableEq ι]

/-- **Sum regroups over fibers** (pure regrouping; always true). For any `w : F → M` (commutative
monoid), `∑_{x∈S} w x = ∑_{i ∈ S.image f} ∑_{x ∈ fiber i} w x`. -/
theorem sum_eq_sum_fibers {M : Type*} [AddCommMonoid M]
    (S : Finset F) (f : F → ι) (w : F → M) :
    ∑ x ∈ S, w x = ∑ i ∈ S.image f, ∑ x ∈ S.filter (fun x => f x = i), w x :=
  (Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem f hx) w).symm

/-- **Constant-on-fiber + equal fiber card `n` ⟹ each fiber sum is `n · (value on rep)`.**
If `w` is constant on the fiber of `i` (value `c i`) and the fiber has card `n`, then
`∑_{x ∈ fiber i} w x = n • c i`. -/
theorem fiber_sum_const {M : Type*} [AddCommMonoid M]
    (S : Finset F) (f : F → ι) (w : F → M) {n : ℕ} {i : ι} {c : M}
    (hcard : (S.filter (fun x => f x = i)).card = n)
    (hconst : ∀ x ∈ S.filter (fun x => f x = i), w x = c) :
    ∑ x ∈ S.filter (fun x => f x = i), w x = n • c := by
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, hcard]

/-! ## 2. Identity (★) for the dilation orbits of `Fₚ*`

Instantiate the abstract collapse at the prize object: `S = Fₚ*` (nonzero frequencies),
`f = cosetLabel n` (dilation orbit), `w b = ‖η_b‖^{2r}`. Constant-on-orbit is
`eta_norm_const_on_coset`; fiber card `= n` is `coset_fiber_card`. -/

variable [Field F] [Fintype F]

/-- **The sharp scalar identity (★): full energy `=` `n` × transversal energy.**
Choosing one representative `b_i ∈ Fₚ*` per orbit label `i` (a section of the orbit map), the
period modulus is constant on each orbit (`eta_norm_const_on_coset`), so the fiber sum collapses to
`n` copies of the representative's `2r`-th power. Summing over the `(q−1)/n` labels:

> `Σ_{b≠0} ‖η_b‖^{2r}  =  n · Σ_{i ∈ labels} ‖η_{b_i}‖^{2r}`.

Hence the transversal energy `Σ_{reps} ‖η‖^{2r}` is **exactly** `E_r / n` (the orbit reduction
divides the energy by `n`, the orbit size). This is the COSMETIC mechanism: the Markov/union bound
over the `(q−1)/n` reps consumes `E_r/n`, the SAME `E_r` object up to the constant `1/n`. -/
theorem energy_eq_n_mul_transversal {ψ : AddChar F ℂ} {n : ℕ} {ζ : F}
    (hζprim : IsPrimitiveRoot ζ n) (hn : 0 < n) (r : ℕ)
    (rep : Finset F → F)
    (hrep_mem : ∀ i ∈ (nonzeroFreqs F).image (cosetLabel n), rep i ∈ nonzeroFreqs F)
    (hrep_label : ∀ i ∈ (nonzeroFreqs F).image (cosetLabel n), cosetLabel n (rep i) = i) :
    ∑ b ∈ nonzeroFreqs F, ‖eta ψ (nthRootsFinset n (1 : F)) b‖ ^ (2 * r)
      = (n : ℝ) * ∑ i ∈ (nonzeroFreqs F).image (cosetLabel n),
                    ‖eta ψ (nthRootsFinset n (1 : F)) (rep i)‖ ^ (2 * r) := by
  rw [sum_eq_sum_fibers (nonzeroFreqs F) (cosetLabel n)
        (fun b => ‖eta ψ (nthRootsFinset n (1 : F)) b‖ ^ (2 * r)),
      Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hbi : rep i ≠ 0 := by
    have := hrep_mem i hi; rwa [mem_nonzeroFreqs] at this
  -- the fiber of `i` has card `n`, and on it `‖η_x‖^{2r} = ‖η_{rep i}‖^{2r}`.
  have hcard : ((nonzeroFreqs F).filter (fun x => cosetLabel n x = i)).card = n := by
    have h := coset_fiber_card hζprim hn hbi
    rwa [hrep_label i hi] at h
  -- constancy on the fiber: every `x` with `cosetLabel x = i = cosetLabel (rep i)` has the same norm
  have hconst : ∀ x ∈ (nonzeroFreqs F).filter (fun x => cosetLabel n x = i),
      ‖eta ψ (nthRootsFinset n (1 : F)) x‖ ^ (2 * r)
        = ‖eta ψ (nthRootsFinset n (1 : F)) (rep i)‖ ^ (2 * r) := by
    intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨hxmem, hxlabel⟩ := hx
    have hx0 : x ≠ 0 := by rw [mem_nonzeroFreqs] at hxmem; exact hxmem
    -- `cosetLabel x = i = cosetLabel (rep i)` ⇒ `x (rep i)⁻¹ ∈ μ_n` ⇒ `x = ζ' * rep i`
    have hlabel_eq : cosetLabel n x = cosetLabel n (rep i) := by
      rw [hxlabel, hrep_label i hi]
    have hratio : x * (rep i)⁻¹ ∈ nthRootsFinset n (1 : F) :=
      ratio_mem_of_cosetLabel_eq hn hbi hx0 hlabel_eq.symm
    -- `x = (x (rep i)⁻¹) * rep i`, and `‖η_{ζ' * rep i}‖ = ‖η_{rep i}‖`
    have hxeq : x = (x * (rep i)⁻¹) * rep i := by
      field_simp
    rw [hxeq, eta_norm_const_on_coset hratio (rep i)]
  rw [fiber_sum_const (nonzeroFreqs F) (cosetLabel n)
        (fun b => ‖eta ψ (nthRootsFinset n (1 : F)) b‖ ^ (2 * r)) hcard hconst,
      nsmul_eq_mul]

/-! ## 3. The cosmetic verdict, stated as a theorem

The transversal energy is `(1/n)·E_full`. So any Markov/union bound at the reduced count `(q−1)/n`
consumes the SAME `E_r`-object divided by `n`. We record this as the explicit cosmetic relocation:
the per-rep energy threshold is `E_r/n`, and `(E_r/n)^{1/(2r)} = E_r^{1/(2r)} · n^{-1/(2r)}` — the
`1/n` enters only as a `2r`-th-root constant, never weakening the deep-moment `A_r ≤ Wick` wall. -/

/-- **COSMETIC verdict (the headline).** The transversal (per-rep) `2r`-th energy is **exactly**
`E_full / n`. Concretely, with `E_full := Σ_{b≠0}‖η_b‖^{2r}` and
`E_reps := Σ_{labels}‖η_{rep}‖^{2r}`, identity (★) gives `E_reps = E_full / n`. Therefore a
Lamzouri/Markov union bound over the `m = (q−1)/n` reps consumes `E_full / n` — the SAME `E_r`
object the full-frequency moment method consumes, divided by the orbit size `n`. The entropy
reduction `log p → log(p/n)` is real in the *log of the count* but the per-rep moment INPUT is the
same open `A_r ≤ Wick` BGK/Paley object; the `1/n` cancels under the outer `2r`-th root up to the
`O(1)` log-constant. **The reduction relocates the optimal depth `r* = log(p/n)`; it does not
weaken the tail.** -/
theorem i031_chaining_cosmetic {ψ : AddChar F ℂ} {n : ℕ} {ζ : F}
    (hζprim : IsPrimitiveRoot ζ n) (hn : 0 < n) (r : ℕ)
    (rep : Finset F → F)
    (hrep_mem : ∀ i ∈ (nonzeroFreqs F).image (cosetLabel n), rep i ∈ nonzeroFreqs F)
    (hrep_label : ∀ i ∈ (nonzeroFreqs F).image (cosetLabel n), cosetLabel n (rep i) = i) :
    (∑ i ∈ (nonzeroFreqs F).image (cosetLabel n),
        ‖eta ψ (nthRootsFinset n (1 : F)) (rep i)‖ ^ (2 * r))
      = (∑ b ∈ nonzeroFreqs F, ‖eta ψ (nthRootsFinset n (1 : F)) b‖ ^ (2 * r)) / (n : ℝ) := by
  have hkey := energy_eq_n_mul_transversal (ψ := ψ) hζprim hn r rep hrep_mem hrep_label
  have hncast : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact this.ne'
  rw [hkey]
  field_simp

end ArkLib.ProximityGap.I031Chaining

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.I031Chaining.sum_eq_sum_fibers
#print axioms ArkLib.ProximityGap.I031Chaining.fiber_sum_const
#print axioms ArkLib.ProximityGap.I031Chaining.energy_eq_n_mul_transversal
#print axioms ArkLib.ProximityGap.I031Chaining.i031_chaining_cosmetic
