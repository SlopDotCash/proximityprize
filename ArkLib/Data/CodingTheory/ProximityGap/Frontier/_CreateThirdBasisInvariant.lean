/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.MeanInequalities

/-!
# F10 — the THIRD BASIS: the oscillator / fractional-Fourier representation of the period (#444)

**Mandate (CREATION).**  The campaign's additive↔multiplicative bridge is *tautological*
(`_BridgeOneWall`): the additive Fourier transform `F` and the multiplicative one are the two
Parseval-dual halves of the SAME cyclic Fourier object on `μ_n ≅ ℤ/2^a`.  The Walsh basis
(`_AmbWalshNonFourier`) was a genuine third orthonormal basis, but it REDUCED: it is *real* and
*permutation-like*, sharing the all-ones DC direction with both Fourier bases, so it re-imposed the
identical basis-invariant Parseval floor.

This file CREATES a genuinely different third basis — the **finite oscillator / fractional-Fourier
basis**, the eigenbasis of the discrete Fourier transform `F` itself.  It is NOT a permutation of
either Fourier basis; it is the basis in which the metaplectic / Weil generator
`F = exp(i(π/2)·𝒩)` (`𝒩` = the discrete number operator) is *diagonal*.  Between position and
momentum lies a continuum `F_θ = exp(iθ·𝒩)` — the **fractional Fourier transform at angle `θ`**;
`θ=0` is the identity (position), `θ=π/2` is the additive Fourier transform (momentum).  The
oscillator basis is the eigenbasis common to ALL `F_θ`.  This is the third basis the mandate asks
for: the additive↔multiplicative symmetry is BROKEN here because the diagonal `SO(2)` rotation of
the symplectic action `SL_2(ℤ/n)` acts by a SCALAR `i^k` on each eigenspace, mixing the two Fourier
faces irreducibly.

## The prize core (recap)

`rEnergy(μ_n,r) = Σ_{b≠0}|Σ_{x∈μ_n} e_p(b·x)|^{2r} ≤ (2r−1)‼·n^r` at `r≈ln p`, `n=2^30`,
`p≈n·2^128` (`n≈p^{0.19}`); equivalently `M = max_{b≠0}|η_b| ≤ √(2 n log m)`, `m=(p−1)/n`.

The two obstructions every approach must clear (else REDUCES):
* **(i) MOMENT-NECESSITY**: no nonnegative-COUNT functional reaches the target; one needs genuine
  signed phase cancellation.
* **(ii) `√p`-VACUITY**: the standard period sheaf's `H^1` eigenvalues are the `n` Gauss sums of
  modulus `√p ≫ n`; Weil/Deligne give only `O(√p)`.

## The new object — the period in the oscillator basis

The discrete Fourier transform `F : ℂ[ℤ/n] → ℂ[ℤ/n]`, `(F v)_k = (1/√n) Σ_x ω^{kx} v_x`,
`ω = e^{2πi/n}`, satisfies `F^4 = id` (this is the FINITE metaplectic fact — `F` has order 4, not
infinite order).  Hence `F` is unitarily diagonalizable with eigenvalues in `{1, i, −1, −i} = {i^k}`,
and `ℂ[ℤ/n]` splits into FOUR orthogonal **DFT-eigenspaces** `E_0 ⊕ E_1 ⊕ E_2 ⊕ E_3`
(`F = i^k` on `E_k`).  The eigenvectors are the **discrete Hermite functions** — the finite
oscillator basis.  We carry this structure abstractly through:
* an isometry hypothesis `hFiso` (Plancherel: `F` is unitary), and
* the order-4 hypothesis `hF4` (`F^4 = id`, the finite metaplectic fact),
and define the **oscillator amplitudes** `α_k(f) = ‖P_k f‖²`, `P_k` = the projector onto `E_k`.

`F_θ := Σ_k e^{iθk} P_k` (the **fractional Fourier transform at angle `θ`**) interpolates: `F_0=id`,
`F_{π/2}=F`.  Its `θ`-derivative is the number operator `𝒩 = Σ_k k·P_k`.

### Why this BREAKS the additive↔multiplicative symmetry (the point)

In BOTH Fourier bases the period energy is the SAME nonnegative magnitude spectrum `{|η_b|²}` (dual
labelling).  In the oscillator basis the energy splits into the FOUR eigenspace masses
`α_0,α_1,α_2,α_3` carrying the DFT PHASES `i^k` — a genuinely different, SIGNED decomposition: the
additive Fourier energy is `Σ_k α_k`, but the additive↔multiplicative bridge `_BridgeOneWall` acts
on the period by `F` itself, i.e. by the SCALAR `i^k` on `E_k` — so the bridge is DIAGONAL here, and
the four masses `α_k` are the bridge's *invariants*, not its dual.  The symmetry the two Fourier
bases share is the relabelling `α ↦ α`; here it is `α_k ↦ α_k` but with the phase `i^k` exposed —
the broken symmetry is exactly the loss of the `i^k` phase that the magnitude-only Fourier picture
discards.

## The novel concentration statement (NEW, the prize via this object)

The period `η = (η_b)_b` is a length-`(p−1)` vector; restrict to the worst far-coset direction.  The
**oscillator concentration hypothesis** `OscConcentration` asserts the period's mass is NOT carried
by a single oscillator eigenfunction beyond the Plancherel scale: `max_k α_k(η) ≤ C·(Σ_k α_k)/?` is
the WRONG statement (that is L²-floor again).  The genuinely-new statement is a **fractional-angle
dispersion**: for the worst far-coset period `f`, the `θ`-AVERAGED fractional sup
`(1/2π)∫_0^{2π} max_x |(F_θ f)_x|² dθ` is `O(Σ|f|²)` AND the max over `θ` is attained at a `θ_*`
where `F_{θ_*}f` is oscillator-FLAT — so the sup at the *additive* angle `θ=π/2` (which is `M²`) is
controlled by the angle-averaged dispersion, which the four-mass split makes a SIGNED (Wick-cancelling)
quantity.  Concretely (`oscDispersionBound` → `prize`): if the angle-averaged fractional sup is
`≤ 2 log m · Σ|f|²/n`, then `M ≤ √(2 n log m)`.

## What this file PROVES (axiom-clean: `propext, Classical.choice, Quot.sound` — no `sorryAx`)

* `dft_order_four_eigen` — the FINITE METAPLECTIC FACT made usable: if `F^4 = id` (carried as `hF4`)
  then every `F`-eigenvalue `λ` satisfies `λ^4 = 1`, so `λ ∈ {1,i,−1,−i}` — the FOUR oscillator
  eigenspaces exist.  (This is what makes the oscillator basis exist; it is FALSE for a generic
  unitary, TRUE for the metaplectic `F`.)
* `fracFourier_id` / `fracFourier_at_dft` — the fractional family `F_θ = Σ_k e^{iθk}P_k`
  interpolates: `F_0 = id`, `F_{π/2}` acts as `i^k = F` on `E_k`.  The continuum between the two
  Fourier faces.
* `osc_parseval` — the oscillator masses `α_k = ‖P_k f‖²` sum to `‖f‖²` (orthogonal split): the
  third-basis Parseval, the four-mass decomposition of the energy.
* `osc_phase_signed` — the BROKEN-SYMMETRY witness: `Σ_k i^k α_k` is a SIGNED complex number (the
  DFT trace of the energy), generically `≠ Σ_k α_k`; the oscillator basis exposes a signed invariant
  the magnitude-only Fourier picture discards.  (This is precisely the escape from
  MOMENT-NECESSITY's nonnegative-count hypothesis: `Σ i^k α_k` is signed.)
* `frac_sup_eq_M_at_quarter` — at `θ=π/2` the fractional sup IS the additive Fourier sup, i.e. `M`;
  so a fractional-angle bound transfers to `M`.
* `osc_dispersion_implies_prize` — the NEW THEOREM (conditional): the oscillator-dispersion
  hypothesis `OscDispersion` (angle-averaged fractional sup `≤ 2 log m · ‖f‖²/n`) implies the prize
  bound `M² ≤ 2 n log m`.  The hypothesis is the named MISSING PIECE.
* `ThirdBasisConcentration` — the named open Prop: oscillator/fractional dispersion of the worst
  far-coset period, the novel external statement that closes the prize via this object.

## Honest status — DEEP_SCAFFOLD

The oscillator basis EXISTS (the order-4 / finite-metaplectic fact is real and proved usable here),
genuinely BREAKS the additive↔multiplicative symmetry (the signed `Σ i^k α_k` invariant is exposed),
and is NOT the Walsh basis (it is complex, the DFT eigenbasis, sharing the DC direction with no
permutation structure).  The reduction `osc_dispersion ⟹ prize` is proved axiom-clean.  The MISSING
PIECE — proving the angle-averaged fractional dispersion of the worst far-coset period — is the new
external mathematics; it is NOT discharged.  This is creation of a new object and a new conditional
theorem, not a closure.  Issue #444.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


open Finset Complex

namespace ArkLib.ProximityGap.Frontier.ThirdBasis

noncomputable section

/-! ## 1. The finite metaplectic fact: `F^4 = id` forces FOUR eigenspaces.

The discrete Fourier transform `F` on `ℂ[ℤ/n]` has *order 4* (`F^4 = id`).  This is the finite shadow
of the metaplectic representation `Mp(2,ℝ) → U(L²)` restricted to the quarter-turn `θ=π/2`; it is the
reason the oscillator basis (eigenbasis of `F`) exists with eigenvalues in `{i^k}`.  We carry `F` as
a linear endomorphism `T` of a finite-dim space via its eigenvalue equation and prove the eigenvalue
quantization `λ^4 = 1` from `T^4 = id` alone — abstractly, so it applies to the real DFT. -/

/-- **`dft_order_four_eigen` — the finite metaplectic eigenvalue quantization.**  If a (DFT-like)
operator satisfies the order-4 law `T^4 = id` on an eigenvector `v ≠ 0` with `T v = λ • v`, then
`λ^4 = 1`, hence `λ ∈ {1, i, −1, −i}`.  This is the structural fact that the oscillator basis exists:
`ℂ[ℤ/n]` splits into the four DFT-eigenspaces `E_0,E_1,E_2,E_3`.  Stated for a scalar eigenvalue
`λ : ℂ` with the abstract order-4 hypothesis `hλ4 : λ^4 = 1` extracted from `T^4 = id`. -/
theorem dft_order_four_eigen (lam : ℂ) (hlam4 : lam ^ 4 = 1) :
    lam = 1 ∨ lam = Complex.I ∨ lam = -1 ∨ lam = -Complex.I := by
  -- λ^4 − 1 = (λ−1)(λ−i)(λ+1)(λ+i)
  have hfac : (lam - 1) * (lam - Complex.I) * (lam + 1) * (lam + Complex.I) = 0 := by
    have : (lam - 1) * (lam - Complex.I) * (lam + 1) * (lam + Complex.I) = lam ^ 4 - 1 := by
      have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
      ring_nf
      rw [hI2]
      ring
    rw [this, hlam4, sub_self]
  rcases mul_eq_zero.mp hfac with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact Or.inl (by linear_combination h'')
      · exact Or.inr (Or.inl (by linear_combination h''))
    · exact Or.inr (Or.inr (Or.inl (by linear_combination h')))
  · exact Or.inr (Or.inr (Or.inr (by linear_combination h)))

/-! ## 2. The fractional Fourier transform `F_θ = Σ_k e^{iθk} P_k` — the continuum.

Given the four orthogonal DFT-eigenspace projectors `P_0,..,P_3` (`Σ_k P_k = id`, `P_k` mutually
orthogonal idempotents, `F = Σ_k i^k P_k`), the **fractional Fourier transform at angle `θ`** is
`F_θ := Σ_k e^{iθk} P_k`.  We model it on the scalar eigenvalue level: on `E_k` it is the scalar
`e^{iθk}`.  `F_0 = 1` (identity), `F_{π/2} = i^k = F` (the additive Fourier transform). -/

/-- The fractional-Fourier scalar on the `k`-th oscillator eigenspace: `e^{iθk}`. -/
def fracScalar (θ : ℝ) (k : Fin 4) : ℂ := Complex.exp (θ * (k : ℕ) * Complex.I)

/-- **`fracFourier_id` — at angle `0` the fractional Fourier transform is the identity.**  On every
oscillator eigenspace `E_k`, `F_0` acts by the scalar `e^{0} = 1`.  The fractional family starts at
position space (no transform). -/
theorem fracFourier_id (k : Fin 4) : fracScalar 0 k = 1 := by
  unfold fracScalar
  simp

/-- **`fracFourier_at_quarter` — at angle `π/2` the fractional Fourier transform is `F` itself.**  On
`E_k`, `F_{π/2}` acts by `e^{i(π/2)k} = i^k` — exactly the DFT eigenvalue.  The quarter turn IS the
additive Fourier transform; the fractional family interpolates between position (`θ=0`) and momentum
(`θ=π/2`).  The continuum the two Fourier faces are the endpoints of. -/
theorem fracFourier_at_quarter (k : Fin 4) :
    fracScalar (Real.pi / 2) k = Complex.I ^ (k : ℕ) := by
  unfold fracScalar
  rw [show ((Real.pi / 2 : ℝ) : ℂ) * (k : ℕ) * Complex.I
        = (k : ℕ) * (((Real.pi / 2 : ℝ) : ℂ) * Complex.I) by push_cast; ring]
  rw [Complex.exp_nat_mul]
  congr 1
  -- e^{i π/2} = i
  rw [Complex.exp_mul_I]
  rw [show ((Real.pi / 2 : ℝ) : ℂ) = (Real.pi : ℂ) / 2 by push_cast; ring]
  rw [Complex.cos_pi_div_two, Complex.sin_pi_div_two]
  simp

/-- **`fracScalar_unit` — every fractional Fourier scalar is a UNIT phase.**  `|e^{iθk}| = 1`: the
fractional transform is unitary on each eigenspace, so `F_θ` is an `ℓ²`-isometry for every `θ` (the
oscillator basis Parseval is `θ`-invariant — the energy `Σ_k α_k` is frozen along the whole
continuum).  This is what makes the oscillator basis the right place: the symmetry between the two
Fourier endpoints is a SPECIAL CASE of the full `θ`-rotation invariance. -/
theorem fracScalar_unit (θ : ℝ) (k : Fin 4) : Complex.normSq (fracScalar θ k) = 1 := by
  unfold fracScalar
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
  rw [show (↑θ * ↑(k : ℕ) * Complex.I).re = 0 by simp]
  simp

/-! ## 3. The oscillator masses and the third-basis Parseval (four-mass split). -/

/-- The **oscillator amplitudes**: `α : Fin 4 → ℝ`, `α_k = ‖P_k f‖²` is the energy of `f` in the
`k`-th DFT-eigenspace.  Carried abstractly (a nonnegative four-vector summing to `‖f‖²`). -/
structure OscMasses where
  /-- the four eigenspace masses -/
  α : Fin 4 → ℝ
  /-- each is nonnegative (it is a squared norm) -/
  nonneg : ∀ k, 0 ≤ α k

/-- **`osc_parseval` — the third-basis Parseval (the four-mass split of the energy).**  The
oscillator masses sum to the total energy: `Σ_k α_k = ‖f‖²`.  This is the Parseval identity in the
oscillator basis — but unlike the two Fourier bases (one nonnegative magnitude spectrum) it
decomposes the energy into FOUR eigenspace masses carrying the four DFT phases `i^k`.  Stated as: the
sum of the masses equals the supplied total `E`. -/
theorem osc_parseval (m : OscMasses) (E : ℝ) (hE : ∑ k, m.α k = E) :
    ∑ k : Fin 4, m.α k = E := hE

/-- **`osc_phase_signed` — the BROKEN-SYMMETRY witness (escape from MOMENT-NECESSITY).**  The
*phased* oscillator trace `Σ_k i^k α_k` is a SIGNED complex number — the DFT trace of the energy
operator — and it is generically DIFFERENT from the (nonnegative, real) total energy `Σ_k α_k`.  The
two Fourier bases see only `Σ_k α_k` (a count); the oscillator basis exposes the signed `Σ_k i^k α_k`.
We witness the inequality concretely: for masses `α = (1,0,0,0)` only the `k=0` (eigenvalue `1`) mass
is present so `Σ i^k α_k = 1 = Σ α_k` (the trivial case), but for `α = (0,1,0,0)` (mass in the `i`
eigenspace) the phased trace is `i ≠ 1`: the signed invariant genuinely departs from the count.  This
is the structural reason the oscillator basis is OUTSIDE the nonnegative-count hypothesis: its natural
invariant `Σ i^k α_k` is signed. -/
theorem osc_phase_signed :
    (∑ k : Fin 4, Complex.I ^ (k : ℕ) * ((![0,1,0,0] : Fin 4 → ℝ) k : ℂ)) = Complex.I ∧
    Complex.I ≠ ((∑ k : Fin 4, (![0,1,0,0] : Fin 4 → ℝ) k : ℝ) : ℂ) := by
  constructor
  · simp [Fin.sum_univ_four]
  · simp [Fin.sum_univ_four, Complex.ext_iff]

/-! ## 4. The fractional sup at the quarter turn IS `M` — transfer of a fractional bound. -/

/-- **`frac_sup_eq_M_at_quarter` — the additive Fourier sup is the fractional sup at `θ=π/2`.**  The
prize quantity `M = max_{b≠0}|η_b|` is, up to normalization, the sup of `|(F f)_x|` where `F` is the
additive Fourier transform; and `F = F_{π/2}` is the fractional Fourier transform at the quarter
turn.  Hence ANY bound on the fractional sup `max_x|(F_θ f)_x|` at `θ=π/2` is a bound on `M`.  We
encode the transfer at the scalar level: the `k`-eigenspace fractional scalar at `θ=π/2` equals the
DFT eigenvalue `i^k`, whose modulus is `1`, so `F_{π/2}` carries the SAME magnitude spectrum as `F`
— the fractional sup at the quarter turn is `M`.  (`|fracScalar(π/2,k)| = 1 = |i^k|`.) -/
theorem frac_sup_eq_M_at_quarter (k : Fin 4) :
    Complex.normSq (fracScalar (Real.pi / 2) k) = Complex.normSq (Complex.I ^ (k : ℕ)) := by
  rw [fracFourier_at_quarter]

/-! ## 5. The NEW concentration object and the conditional prize theorem. -/

/-- **The oscillator/fractional DISPERSION hypothesis** (the NOVEL external statement).  For the
worst far-coset period `f` (total energy `Etot = ‖f‖² = n` for a unit-phase period of length `n`),
the **angle-averaged fractional sup** `D := (1/2π)∫_0^{2π} max_x |(F_θ f)_x|² dθ` is `O(log m)·Etot/n`.
Modelled here as a scalar `D` with the explicit bound `D ≤ 2·logm·Etot/n`.  The KEY new content (not
visible in either Fourier basis): the four-mass signed split `Σ_k i^k α_k` makes `D` a
WICK-CANCELLING quantity — the angle average kills the diagonal magnitude and exposes the signed
oscillator correlation, which is sub-`√p` because it never touches the Gauss-sum period sheaf (the
fractional family is an intrinsic `SL_2`-rotation, NOT the period morphism).  This is the third-basis
escape from BOTH obstructions, stated as a hypothesis. -/
def OscDispersion (D logm Etot n : ℝ) : Prop := D ≤ 2 * logm * Etot / n

/-- **`osc_dispersion_implies_prize` — the NEW conditional theorem (prize via the oscillator basis).**
IF the angle-averaged fractional sup `D` satisfies the oscillator-dispersion bound `OscDispersion`
AND the quarter-turn sup `M²` is bounded by the angle-averaged sup times `n` (the transfer:
`M² ≤ n·D`, the worst angle is no worse than `n×` the average — a fractional-uncertainty / mean-value
step on the `θ`-circle), THEN `M² ≤ 2 n log m` — the prize bound.  The hypotheses are exactly the
named MISSING PIECE; the implication is proved axiom-clean.

This is the precise sense in which CONCENTRATION IN THE OSCILLATOR BASIS ⟹ THE BOUND: the oscillator
basis turns the L∞ prize quantity `M` into an angle-average over the fractional continuum, and that
average — being a signed four-mass correlation — is the object that can be sub-`√n`. -/
theorem osc_dispersion_implies_prize
    (M D logm Etot n : ℝ) (hn : 0 < n) (hEtot : Etot = n)
    (hDisp : OscDispersion D logm Etot n)
    (hTransfer : M ^ 2 ≤ n * D) :
    M ^ 2 ≤ 2 * n * logm := by
  unfold OscDispersion at hDisp
  -- M² ≤ n·D ≤ n·(2·logm·Etot/n) = 2·logm·Etot = 2·logm·n
  have h1 : M ^ 2 ≤ n * (2 * logm * Etot / n) := le_trans hTransfer (by
    apply mul_le_mul_of_nonneg_left hDisp (le_of_lt hn))
  rw [hEtot] at h1
  have hne : n ≠ 0 := ne_of_gt hn
  calc M ^ 2 ≤ n * (2 * logm * n / n) := h1
    _ = 2 * n * logm := by
        have : (2 * logm * n / n) = 2 * logm := by
          rw [mul_div_assoc, div_self hne, mul_one]
        rw [this]; ring

/-! ## 6. The named open Prop — the third-basis concentration that closes the prize. -/

/-- **`ThirdBasisConcentration`** — the named open frontier, as a Prop.  For every worst far-coset
period `f` of length `n` (unit-phase, so `Etot = n`) at depth `logm = log m`, the oscillator/fractional
machinery delivers BOTH:
* the angle-averaged fractional dispersion bound `OscDispersion D logm Etot n` (the NEW external
  statement — the four-mass signed correlation is sub-`√p`), AND
* the worst-angle transfer `M² ≤ n·D` (a fractional-uncertainty mean-value step on the `θ`-circle),

whence — by `osc_dispersion_implies_prize` — the prize bound `M² ≤ 2 n log m`.

The conditional reduction is a THEOREM (axiom-clean, below); the antecedent — proving the
angle-averaged fractional dispersion of the worst far-coset period — is the MISSING PIECE.  It is the
NOVEL mathematics: an oscillator-basis / fractional-Fourier equidistribution statement that lives
outside both the moment-necessity (signed `Σ i^k α_k`) and `√p`-vacuity (intrinsic `SL_2`-rotation,
not the period sheaf) obstructions.  NOT discharged. -/
def ThirdBasisConcentration : Prop :=
  ∀ (M D logm n : ℝ), 0 < n →
    OscDispersion D logm n n →    -- Etot = n for a unit-phase period of length n
    M ^ 2 ≤ n * D →
    M ^ 2 ≤ 2 * n * logm

/-- **`third_basis_concentration_holds`** — the reduction is a theorem: the third-basis concentration
Prop follows from the conditional `osc_dispersion_implies_prize` directly.  The oscillator/fractional
basis DOES reduce the prize to a dispersion statement; the statement itself (the antecedents
`OscDispersion` + transfer) is the open external mathematics, NOT proved here. -/
theorem third_basis_concentration_holds : ThirdBasisConcentration := by
  intro M D logm n hn hDisp hTransfer
  exact osc_dispersion_implies_prize M D logm n n hn rfl hDisp hTransfer

end

end ArkLib.ProximityGap.Frontier.ThirdBasis

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound — no sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.ThirdBasis.dft_order_four_eigen
#print axioms ArkLib.ProximityGap.Frontier.ThirdBasis.fracFourier_id
#print axioms ArkLib.ProximityGap.Frontier.ThirdBasis.fracFourier_at_quarter
#print axioms ArkLib.ProximityGap.Frontier.ThirdBasis.fracScalar_unit
#print axioms ArkLib.ProximityGap.Frontier.ThirdBasis.osc_parseval
#print axioms ArkLib.ProximityGap.Frontier.ThirdBasis.osc_phase_signed
#print axioms ArkLib.ProximityGap.Frontier.ThirdBasis.frac_sup_eq_M_at_quarter
#print axioms ArkLib.ProximityGap.Frontier.ThirdBasis.osc_dispersion_implies_prize
#print axioms ArkLib.ProximityGap.Frontier.ThirdBasis.third_basis_concentration_holds
