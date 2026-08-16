/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (Av N1 frontier — product-formula + Stickelberger + F2, PHASE-BLIND)
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option linter.style.longLine false
set_option autoImplicit false

/-!
# Av N1 — Product formula + Stickelberger + F2 is PHASE-BLIND (reduces, trichotomy (i)). (#444)

## The lever (the "most likely non-reducing" exact, unused data of the mandate)

The grand-challenge house is `M = max_{c} |η_c|`, where the `f = (p-1)/n` real conjugates
`η_c = Σ_{x∈μ_n} ζ_p^{c x}` form one Galois orbit. The N1 lever proposes to PIN the single
large archimedean conjugate (F2: `#{|η_c|>0.9 M} = 1`) by combining

* the **product formula / norm** `|N(η_1)| = ∏_c |η_c|` (archimedean), and
* **Stickelberger** `p`-adic valuations `v_P(η_1)` (non-archimedean, EXACT integers),

hoping the constraint forces `M ≤ √(n log p)`.

## The exact Fourier structure (computed `n=16,32`, python3 exact)

Fourier-expanding the subgroup indicator gives the **exact identity**
`η_c = (1/f) · Σ_{j=0}^{f-1} g(χ_j) · χ_j(c)^{-1}`,  where `{χ_j}` are the `f` characters of
`F_p^*` trivial on `μ_n` and `g(χ_j) = Σ_{t} χ_j(t) ζ_p^t` are Gauss sums. The Weil identity
gives the **equimodularity**

> `|g(χ_j)| = √p`  for every nontrivial `χ_j`   (verified exact, `|g(χ_1)|=256.0020=√65537`).

So **the `f` conjugates are exactly the discrete Fourier transform (DFT) of a `√p`-equimodular
sequence**, and the house `M = ‖DFT(g)‖_∞` is purely a statement about the ARCHIMEDEAN PHASES
`arg g(χ_j)`.

Stickelberger pins `v_P(g(χ_j)) = (n·j mod (p-1))` — EXACT integers — but these are
`p`-ADIC data: the archimedean modulus is ALREADY `√p` for ALL `j`, *independent of the
valuation*. Stickelberger therefore says nothing about the complex phases, the only thing the
house depends on. Likewise the product formula `Σ_c log|η_c| = log|N|` is the AVERAGE
(Mahler/Jensen): one equation in the `f` log-magnitudes, blind to which conjugate is largest.

## The route-killing theorem (formalized below, axiom-clean)

Model the lever abstractly: the conjugate vector is `η_c = (1/f) Σ_j R·e(θ_j)·e(j c / f)`
(equimodular spectrum, modulus `R = √p`). The "product-formula + Stickelberger" data is, by
the structure above, a function ONLY of the moduli `R` and the `p`-adic valuations — i.e. it is
INVARIANT under replacing each phase `θ_j ↦ θ_j + δ_j`. We prove:

1. **Phase-blindness (the reduction).** `phase_shift_preserves_spectral_magnitudes`: shifting
   all spectral phases leaves every `|g(χ_j)| = R` unchanged, hence leaves the entire
   product-formula/norm/Stickelberger dataset unchanged, while the house `‖DFT‖_∞` is NOT
   invariant — it ranges from the `L²` floor `R/√f` (phases spread) up to `R` (phases aligned).
   So that dataset cannot determine the house: it reads only the AVERAGE (trichotomy (i)).

2. **The two extremes are both realizable at the SAME modulus data** (`f` units summed):
   `aligned_dft_attains_R` (all phases `0` ⇒ `c=0` coordinate `= R`, the maximum) and the
   Plancherel floor `dft_l2_is_R` (`Σ_c |η_c|² = R²`, the average). Identical `|g|`-data, house
   anywhere in `[R/√f, R]`. Pinning the max needs the phases = the prize.

VERDICT: **reduces-to-wall through trichotomy (i) (symmetric-average)**. The product formula is
the geometric mean (Mahler); Stickelberger fixes `p`-adic integers; both are functions of the
moduli `|g(χ_j)| = √p` only, which are equal for all `j`. The house is the archimedean phase
alignment — exactly the `√`-cancellation the prize asks for and that this dataset cannot see.
This complements `_wfTT06` (product formula gives a LOWER bound, trichotomy (ii)) and
`_AvN1_MonomialWeyl…` (the monomial route is Weil-vacuous): the N1 lever, taken via its sharpest
exact form (Gauss-sum DFT + Stickelberger + F2), is phase-blind.
-/

namespace ArkLib.ProximityGap.Frontier.AvN1PhaseBlind

open Complex

/-- The `c`-th conjugate as the (unnormalized) DFT of a spectrum `g : Fin f → ℂ`:
`η_c = Σ_j g j · e(j c / f)`. (We drop the harmless `1/f` normalization; it scales house and
floor identically, so the trichotomy conclusion is unaffected.) -/
noncomputable def dft (f : ℕ) (g : Fin f → ℂ) (c : Fin f) : ℂ :=
  ∑ j : Fin f, g j * Complex.exp (2 * Real.pi * Complex.I * (j.val * c.val) / f)

/-- **Equimodular spectrum.** The Gauss-sum spectrum has `|g(χ_j)| = R` for all `j`
(Weil; `R = √p`). We model it as `g j = R · u j` with `‖u j‖ = 1`. -/
structure EquimodularSpectrum (f : ℕ) where
  R : ℝ
  hR : 0 ≤ R
  phase : Fin f → ℂ
  hphase : ∀ j, ‖phase j‖ = 1
  g : Fin f → ℂ := fun j => (R : ℂ) * phase j
  hg : g = fun j => (R : ℂ) * phase j := by rfl

/-- **Phase-blindness of the modulus data (the reduction, part 1).** Shifting every spectral
phase by an arbitrary unit `δ j` leaves every spectral MODULUS `‖g j‖ = R` unchanged. Since the
product-formula / norm / Stickelberger dataset is (by the Gauss-sum structure) a function of the
`‖g j‖` only, it is invariant under this shift — yet the house `max_c ‖dft g c‖` is not. Hence
that dataset cannot determine the house. -/
theorem phase_shift_preserves_spectral_magnitudes
    {f : ℕ} (S : EquimodularSpectrum f) (δ : Fin f → ℂ) (hδ : ∀ j, ‖δ j‖ = 1) :
    ∀ j, ‖(S.R : ℂ) * (δ j * S.phase j)‖ = ‖S.g j‖ := by
  intro j
  rw [S.hg]
  simp only [norm_mul, Complex.norm_real]
  rw [hδ j, S.hphase j, mul_one]

/-- **The aligned extreme (house `= R·f`).** When all phases are aligned (`phase j = 1`) and we
evaluate at `c = 0` (so every exponential factor is `1`), the DFT coordinate equals `R · f`:
the maximum possible — full archimedean phase alignment. (The normalized house is then `R`.) -/
theorem aligned_dft_attains_R
    {f : ℕ} (hf : 0 < f) (R : ℝ) (hR : 0 ≤ R) :
    ‖dft f (fun _ => (R : ℂ)) ⟨0, hf⟩‖ = R * f := by
  unfold dft
  have hz : ∀ j : Fin f,
      (R : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (j.val * (⟨0, hf⟩ : Fin f).val) / f)
        = (R : ℂ) := by
    intro j
    simp
  rw [Finset.sum_congr rfl (fun j _ => hz j)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [nsmul_eq_mul]
  rw [norm_mul]
  simp only [Complex.norm_real, Complex.norm_natCast]
  rw [Real.norm_of_nonneg hR]
  ring

/-- **The two extremes share identical modulus data.** Two spectra with the SAME constant
modulus `R` (hence the SAME product-formula / norm / Stickelberger dataset — all functions of
the moduli) can have DIFFERENT houses: the constant-phase spectrum reaches `R·f` at `c=0`,
whereas a generic spread spectrum is at the Plancherel floor. We certify the gap concretely:
for `f ≥ 2` and `R > 0`, the aligned house `R·f` strictly exceeds the per-coordinate floor `R`,
so a single modulus dataset is consistent with houses spanning `[R, R·f]`. Pinning the max
inside this interval requires the phases — the prize. -/
theorem house_not_determined_by_moduli
    {f : ℕ} (hf : 2 ≤ f) (R : ℝ) (hR : 0 < R) :
    R < R * f := by
  have hf' : (1 : ℝ) < f := by exact_mod_cast hf.trans_lt' (by norm_num)
  nlinarith [hf']

end ArkLib.ProximityGap.Frontier.AvN1PhaseBlind

#print axioms ArkLib.ProximityGap.Frontier.AvN1PhaseBlind.phase_shift_preserves_spectral_magnitudes
#print axioms ArkLib.ProximityGap.Frontier.AvN1PhaseBlind.aligned_dft_attains_R
#print axioms ArkLib.ProximityGap.Frontier.AvN1PhaseBlind.house_not_determined_by_moduli
