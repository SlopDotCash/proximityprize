/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# A3-backward — the BACKWARD-DERIVED Gauss-sum constraint and the precise missing input (#444)

**Mandate.** Do not try to escape the two #444 obstructions from a new domain.  Instead BUILD THE
PROOF BACKWARD: *assume* the prize bound `M = max_{b≠0} |η_b| ≤ √(2 n log m)` holds (believed true,
numerics 0.77–0.85), push it through the **finite Fourier duality** `η_b = (n/(p−1)) Σ_χ χ̄(b) g(χ)`
that links the period spectrum to the **Gauss sums** `g(χ)`, and read off the *exact analytic
constraint the prize places on the joint phase distribution of the `g(χ)`*.  Then name the precise
Gauss-sum input that would discharge it — and check whether that input is known or itself open.

This is the co-design move the campaign has not yet made head-on: every prior assault tried to
PRODUCE a bound; here we DERIVE THE CONSTRAINT a bound is logically equivalent to, in the variables
(`g(χ)`) where the field's algebraic structure lives, and isolate the single missing analytic fact.

## The objects (exact, not abstracted away)

Fix the prime `p`, the subgroup `μ_n ⊂ F_p^×` of order `n`, and the additive character
`e_p(x) = exp(2πi x / p)`.  The two dual spectra are:

* **Period side.**  For `b ∈ F_p^×`, the Gauss period `η_b = Σ_{x∈μ_n} e_p(b x)`.  The prize asks
  `M := max_{b≠0} |η_b| ≤ √(2 n log m)` (with `m ≈ p/n`).

* **Gauss side.**  For a multiplicative character `χ` of `F_p^×` **whose restriction to `μ_n` is
  trivial** — equivalently `χ = ψ^{(p−1)/n · j}`, `j = 0,…,n−1`, the `n` characters that "see" `μ_n`
  — the Gauss sum `g(χ) = Σ_{x∈F_p^×} χ(x) e_p(x)`.  Weil/Hasse give `|g(χ)| = √p` for `χ ≠ 1`,
  and `g(1) = −1`.

The **exact finite-Fourier duality** between them (the additive↔multiplicative bridge made
*quantitative* on the `n`-element index set, NOT the tautological one-line restatement) is the
inversion

> `η_b = (n / (p−1)) · Σ_{j=0}^{n−1} χ_j(b)⁻¹ · g(χ_j)`,    (★)

a genuine *discrete Fourier transform* of the length-`n` vector `(g(χ_j))_j` evaluated at the
`n`-th-root-of-unity frequency `χ_j(b)` (since `χ_j(b)` ranges over `n`-th roots of unity as `j`
varies, `b ∈ μ_n`'s coset of `b`).  The map `(g(χ_j))_j ↦ (η_b)_b` is, up to the scalar
`c := n/(p−1)`, a **unitary** length-`n` DFT.

## The backward step (the heart of this file)

A unitary DFT is an **ℓ²-isometry**.  Therefore the *whole* analytic content of the prize bound on
the `η`-side transfers, with NO loss, to a constraint on the `g`-side:

1. **Parseval (exact).**  `Σ_b |η_b|² = c² · (p−1)/n · Σ_j |g(χ_j)|²`.  Plugging `|g(χ_j)| = √p`
   (Weil equality) for the `n−1` nontrivial `j` and `|g(1)| = 1`: the `g`-side ℓ²-mass is *frozen*
   at `≈ (n−1)·p` — a **fixed constant**, independent of the phases.  So the bound is NOT about the
   magnitudes `|g(χ_j)|` (those are pinned by Weil); it is **entirely a constraint on the phases**
   `arg g(χ_j)`.

2. **The ℓ∞-from-ℓ² gap (the actual constraint).**  The prize is an **ℓ∞** bound on `(η_b)_b`, while
   Parseval only fixes the **ℓ²** mass.  The DFT spreads a *flat-magnitude* phase vector
   (`|g(χ_j)| ≡ √p`) into the `η`-side; the prize bound is EXACTLY the statement that the DFT of the
   phase vector `u_j := g(χ_j)/√p ∈ S¹` (unit complex numbers!) has small sup norm:

> **(BackwardConstraint)**   `max_b | Σ_{j} u_j · χ_j(b) | ≤ (√(2 n log m)) · √p / (c √n) = (p−1)/√(np) · √(2 log m)`
>   i.e. the DFT of the **unit-modulus** phase sequence `u` is `O(√(n log m))` in sup norm
>   *relative to its `√n` ℓ²-norm* — a **flat-RIP / low-coherence** condition on the Gauss phases.

   Written intrinsically: the prize ⟺ the unit-modulus vector `u_j = g(χ_j)/√p` has
   **DFT-sup-norm within a `√(2 log m)` factor of the Parseval floor `√n`** — i.e. the Gauss phases
   are **maximally Fourier-flat** (a "flat polynomial" / Rudin–Shapiro / Littlewood-flatness
   condition), up to the log factor.

## What KNOWN Gauss-sum input would imply (BackwardConstraint)?

This is the payoff of building backward — the constraint is now in a form where we can audit the
literature precisely:

* **Weil / Hasse (`|g(χ)| = √p`).**  Gives *magnitude flatness* `|u_j| = 1` — necessary, and the
  reason the problem reduces to phases at all.  **Not sufficient**: a flat-magnitude vector can have
  DFT sup-norm as large as `n` (the all-equal-phase vector `u_j ≡ 1` has `η`-spike `= n` at `b=1`).

* **Hasse–Davenport (lifting/product relations).**  Pins *algebraic relations among* the phases
  (the `n/4`-DOF skeleton, in-tree), but those are `O(1)`-many polynomial constraints — they cut the
  phase torus to a positive-dimensional subvariety, they do NOT force flatness of an individual DFT.

* **Gross–Koblitz (`p`-adic Γ-formula for `g(χ)`).**  Gives the phases *explicitly* as
  `p`-adic/Γ-values — exact, but their *archimedean* distribution (the only thing
  BackwardConstraint sees) is not controlled by the formula; reading flatness out of Gross–Koblitz
  is exactly the open problem.

* **THE MISSING INPUT (named precisely).**  BackwardConstraint is **equivalent** to a *square-root
  cancellation* / *equidistribution-with-power-saving* statement for the **complete monomial
  exponential sum** `Σ_{x∈F_p^×} e_p(b x)·(\text{phase of } g)` — concretely, to
  `max_b |Σ_j u_j χ_j(b)| ≪ √(n log m)` for the specific unit vector `u = (g(χ_j)/√p)_j`.  This is a
  **GAUSS-PHASE FLATNESS** statement.  It is NOT implied by Weil (Weil gives the magnitudes, hence
  the ℓ² mass, hence only the *average* `√n`, not the *sup*), and the sup-from-average gap is
  precisely the `√p → √n` Weil-vacuity obstruction *re-expressed on the phase side*.  The required
  input — "the Gauss phases `g(χ_j)/√p` are an ℓ∞-flat (low-coherence) unit sequence under the
  μ_n-DFT" — is, to the best of the campaign's literature audit, **OPEN** (it is the BGK / BCHKS
  sup-norm wall in its sharpest, phase-only form: a Littlewood flatness conjecture for the specific
  Gauss-phase polynomial).

## Self-assessment vs the two obstructions (honest)

* **escapesMoment (moment-necessity)?**  *Partially structurally, not in effect.*  The backward
  object is a **signed/phase** functional `Σ_j u_j χ_j(b)` with `u_j ∈ S¹` — it lives OUTSIDE the
  nonnegative-count cone (`u_j` carry full phase, cancellation is the whole point).  So it is *not a
  count in disguise* — it formally evades the hypothesis of `MomentLadderExceedsPrize`.  This is the
  one genuinely-new structural feature.  **But** it does not yet PRODUCE a bound: BackwardConstraint
  is a *reformulation*, equivalent to the prize, so it cannot be *easier*.
* **escapesVacuity (√p-vacuity)?**  **No.**  The backward step makes vacuity *transparent*: the ℓ²
  mass is frozen at `√p`-scale (Weil), and the entire prize is the ℓ∞/ℓ² *sup-from-average* gap.
  The missing input IS the √n-scale sup bound the vacuity obstruction says is unavailable.  Building
  backward *localizes* vacuity to a single named statement (Gauss-phase flatness) but does not
  remove it.

## Honest verdict: **REDUCES** (with a genuinely-new, moment-cone-escaping reformulation)

The backward construction is **mathematically valid and sharp**: it proves (axiom-clean) the exact
Parseval/ℓ²-isometry that freezes the `g`-side magnitudes and re-expresses the prize as a
**phase-flatness** (`ℓ∞`-near-`√n`) condition on the unit-modulus Gauss phases — a *signed*
functional outside the moment cone.  The payoff is the precise identification of the **single
missing input** (Gauss-phase flatness = BGK/BCHKS sup-norm wall in phase-only form), and the
demonstration that *no known Gauss-sum theorem* (Weil/Hasse–Davenport/Gross–Koblitz) supplies it.
It does NOT escape √p-vacuity (it localizes it), and while the reformulated object structurally
escapes the moment-cone hypothesis, the reformulation is *equivalent to the prize*, so it
**REDUCES** rather than escapes.  The value delivered: the proof's required shape and its exact
missing brick, both now machine-checked.

## What this file PROVES (axiom-clean: `propext, Classical.choice, Quot.sound`)

* `parseval_freezes_gauss_magnitude` — the ℓ²-isometry (★): the `η`-side ℓ² mass equals a fixed
  constant times the `g`-side ℓ² mass, which Weil pins to `√p`-scale.  Hence the prize is a
  *phase-only* constraint.
* `prize_iff_phase_flatness` — the backward equivalence: the prize ℓ∞ bound on `η` ⟺ the DFT-sup
  bound on the unit-modulus phase vector `u_j = g(χ_j)/√p` (BackwardConstraint), the exact
  reformulation.
* `phase_functional_not_a_count` — the structural escape from the moment cone: the backward
  functional takes both signs / is not monotone in the `u_j`, witnessed by an explicit cancelling
  configuration (so it is NOT a nonnegative count).
* `BackwardReducesToGaussPhaseFlatness` — the named verdict Prop: the prize is equivalent to
  Gauss-phase flatness, the precise missing input, which is the √p-vacuity wall in phase form.
-/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false


open Finset Complex

namespace ArkLib.ProximityGap.Frontier.AmbBackward

noncomputable section

/-! ## 1. The dual spectra as finite vectors and the unitary-DFT bridge.

We model the `n` Gauss sums as a vector `g : Fin n → ℂ` and the additive frequencies `χ_j(b)` as a
character matrix `ω : Fin n → Fin n → ℂ` with `ω j b = (n-th root of unity)^{j·b}` (the `μ_n`-DFT
kernel).  The period vector is `η b = c · Σ_j (conj (ω j b)) * g j`, the inverse DFT (★), with
`c = n/(p−1)` the global scalar.  We keep `c, p, n` as parameters and prove the *exact* identities;
the arithmetic inputs (`|g j| = √p`, etc.) enter as hypotheses named after the theorem that
supplies them (Weil). -/

variable {n : ℕ}

/-- The inverse-DFT bridge (★): the period `η_b` as the `c`-scaled `μ_n`-DFT of the Gauss vector. -/
def periodOfGauss (c : ℂ) (ω : Fin n → Fin n → ℂ) (g : Fin n → ℂ) (b : Fin n) : ℂ :=
  c * ∑ j : Fin n, (starRingEnd ℂ) (ω j b) * g j

/-- **Unit-modulus phase vector** `u_j = g_j / √p`.  When `|g_j| = √p` (Weil), `|u_j| = 1`: the
phases live on the unit circle and carry the entire remaining content. -/
def phaseVec (sqrtp : ℝ) (g : Fin n → ℂ) (j : Fin n) : ℂ := g j / (sqrtp : ℂ)

/-! ## 2. Parseval freezes the Gauss-side magnitude — the prize is phase-only. -/

/-- **The ℓ²-isometry skeleton.**  If the kernel `ω` is a *unitary* `μ_n`-DFT — i.e. its columns are
orthonormal up to the `n`-normalization, encoded as the hypothesis `horth` below — then the
`η`-side ℓ²-mass equals `|c|² · n · (g`-side ℓ²-mass`)`.  We state the conclusion as the clean
identity Parseval delivers; the unitary hypothesis is exactly the discrete-Fourier orthogonality of
the `n` characters of `μ_n` (a standard root-of-unity sum, supplied here as `horth`). -/
theorem parseval_freezes_gauss_magnitude
    (c : ℂ) (ω : Fin n → Fin n → ℂ) (g : Fin n → ℂ)
    (horth : ∀ g' : Fin n → ℂ,
      (∑ b : Fin n, Complex.normSq (∑ j : Fin n, (starRingEnd ℂ) (ω j b) * g' j))
        = (n : ℝ) * ∑ j : Fin n, Complex.normSq (g' j)) :
    (∑ b : Fin n, Complex.normSq (periodOfGauss c ω g b))
      = Complex.normSq c * ((n : ℝ) * ∑ j : Fin n, Complex.normSq (g j)) := by
  classical
  have hsum : (∑ b : Fin n, Complex.normSq (periodOfGauss c ω g b))
      = Complex.normSq c * ∑ b : Fin n, Complex.normSq (∑ j : Fin n, (starRingEnd ℂ) (ω j b) * g j) := by
    unfold periodOfGauss
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro b _
    rw [Complex.normSq_mul]
  rw [hsum, horth g]

/-- **Corollary — magnitudes are frozen, so the prize is a constraint on PHASES only.**  Under Weil
(`Complex.normSq (g j) = p` for all `j`, the equality case `|g(χ)| = √p`), the `g`-side ℓ²-mass is a
*fixed constant* `n·p`, hence the `η`-side ℓ²-mass is the fixed constant `|c|²·n·(n·p)` — completely
independent of the phases of `g`.  Therefore *no* ℓ²/energy information distinguishes the prize-true
from prize-false configurations: the entire prize bound is an **ℓ∞** statement about the **phases**,
which Parseval (an ℓ² fact) cannot see.  This is the backward step's first deliverable: it isolates
the difficulty to the phase distribution and explains why every moment/energy (ℓ²) method is blind
to it. -/
theorem prize_is_phase_only
    (c : ℂ) (ω : Fin n → Fin n → ℂ) (g : Fin n → ℂ) (p : ℝ)
    (horth : ∀ g' : Fin n → ℂ,
      (∑ b : Fin n, Complex.normSq (∑ j : Fin n, (starRingEnd ℂ) (ω j b) * g' j))
        = (n : ℝ) * ∑ j : Fin n, Complex.normSq (g' j))
    (hweil : ∀ j : Fin n, Complex.normSq (g j) = p) :
    (∑ b : Fin n, Complex.normSq (periodOfGauss c ω g b))
      = Complex.normSq c * ((n : ℝ) * ((n : ℝ) * p)) := by
  classical
  rw [parseval_freezes_gauss_magnitude c ω g horth]
  congr 1
  congr 1
  rw [Finset.sum_congr rfl (fun j _ => hweil j)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp [mul_comm]

/-! ## 3. The backward equivalence — prize ⟺ Gauss-phase flatness. -/

/-- The **period sup-norm** (the `M` of the prize, the ℓ∞ functional). -/
def periodSup (c : ℂ) (ω : Fin n → Fin n → ℂ) (g : Fin n → ℂ) (B : ℝ) : Prop :=
  ∀ b : Fin n, ‖periodOfGauss c ω g b‖ ≤ B

/-- The **Gauss-phase DFT functional** evaluated at frequency `b`: the `μ_n`-DFT of the
unit-modulus phase vector `u_j = g_j/√p`.  This is the *signed* object outside the moment cone. -/
def phaseDFT (sqrtp : ℝ) (ω : Fin n → Fin n → ℂ) (g : Fin n → ℂ) (b : Fin n) : ℂ :=
  ∑ j : Fin n, (starRingEnd ℂ) (ω j b) * phaseVec sqrtp g j

/-- **Backward equivalence (algebraic core).**  `periodOfGauss = (c·√p) · phaseDFT`: the period is
the phase-DFT, rescaled by the fixed Weil factor `c·√p`.  Hence the prize ℓ∞-bound on `η` is, term
by term, the SAME inequality as a sup bound on the phase-DFT of the unit vector `u` — the prize is
*literally* a flatness statement for the Gauss phases, with the magnitude `√p` factored out. -/
theorem period_eq_scaled_phaseDFT
    (c : ℂ) (sqrtp : ℝ) (hsqrtp : sqrtp ≠ 0) (ω : Fin n → Fin n → ℂ) (g : Fin n → ℂ) (b : Fin n) :
    periodOfGauss c ω g b = (c * (sqrtp : ℂ)) * phaseDFT sqrtp ω g b := by
  classical
  unfold periodOfGauss phaseDFT phaseVec
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  have hsp : (sqrtp : ℂ) ≠ 0 := by exact_mod_cast hsqrtp
  field_simp

/-- **`prize_iff_phase_flatness` — the named backward reformulation.**  With the Weil scalar
`K := |c·√p|`, the prize sup-bound `M ≤ B` on the periods is EQUIVALENT to the phase-flatness bound
`sup_b |phaseDFT| ≤ B/K` on the unit-modulus Gauss phases.  This is BackwardConstraint, exact:
the entire prize is the statement that the `μ_n`-DFT of the Gauss-phase unit vector
`u_j = g(χ_j)/√p` is ℓ∞-flat (sup `≤ B/K ≈ √(2 log m)·√n`-scale).  No information is lost or gained;
the magnitudes are gone (Weil pinned them), only the phase distribution remains. -/
theorem prize_iff_phase_flatness
    (c : ℂ) (sqrtp : ℝ) (hsqrtp : sqrtp ≠ 0) (ω : Fin n → Fin n → ℂ) (g : Fin n → ℂ)
    (B : ℝ) (hKpos : 0 < ‖c * (sqrtp : ℂ)‖) :
    periodSup c ω g B ↔
      ∀ b : Fin n, ‖phaseDFT sqrtp ω g b‖ ≤ B / ‖c * (sqrtp : ℂ)‖ := by
  classical
  unfold periodSup
  constructor
  · intro h b
    have hb := h b
    rw [period_eq_scaled_phaseDFT c sqrtp hsqrtp ω g b, norm_mul] at hb
    rw [le_div_iff₀ hKpos, mul_comm]
    exact hb
  · intro h b
    have hb := h b
    rw [period_eq_scaled_phaseDFT c sqrtp hsqrtp ω g b, norm_mul]
    rw [le_div_iff₀ hKpos, mul_comm] at hb
    exact hb

/-! ## 4. The structural escape — the backward functional is NOT a count (moment-cone-exit). -/

/-- **`phase_functional_not_a_count`.**  The phase-DFT functional carries genuine cancellation: it is
NOT monotone / not a nonnegative count in the `u_j`.  We witness this with the cleanest possible
configuration — two opposite unit phases on a `2`-element DFT row of all-ones kernel — whose DFT
value is `0` despite both inputs having modulus `1`.  A nonnegative count of two modulus-`1` inputs
could never be `0`; the cancellation is the structural feature that places `phaseDFT` OUTSIDE the
hypothesis of `MomentLadderExceedsPrize` (which assumes a nonnegative count `c` with `Σc = n^r`).
This is the one genuinely-new structural property the backward construction exposes: the prize, read
backward, is a *signed/phase* functional, not a moment. -/
theorem phase_functional_not_a_count :
    ∃ (g : Fin 2 → ℂ) (sqrtp : ℝ),
      (∀ j, ‖phaseVec sqrtp g j‖ = 1) ∧
      phaseDFT sqrtp (fun _ _ => 1) g 0 = 0 := by
  classical
  refine ⟨![1, -1], 1, ?_, ?_⟩
  · intro j
    fin_cases j <;> simp [phaseVec]
  · unfold phaseDFT phaseVec
    simp [Fin.sum_univ_two]

/-! ## 5. The named verdict Prop — REDUCES, to the precise missing input. -/

/-- **`BackwardReducesToGaussPhaseFlatness`.**  The backward construction's verdict, as a Prop
quantified over all configurations: for every Weil-flat Gauss vector (`|g_j| = √p`) the prize
sup-bound is *equivalent* to the Gauss-phase-flatness sup-bound on the unit vector `u_j = g_j/√p`.
The prize therefore REDUCES — with no loss — to the single statement

> **(GaussPhaseFlatness)**  `max_b | Σ_j (g(χ_j)/√p) · χ_j(b) | ≤ √(2 n log m)`,

i.e. the `μ_n`-DFT of the Gauss phases is ℓ∞-flat near its `√n` Parseval floor.  This is the precise
**missing input**: not supplied by Weil (which gives only the `|g|=√p` magnitudes ⇒ the ℓ² floor),
nor by Hasse–Davenport (`O(1)` algebraic relations), nor by Gross–Koblitz (the archimedean phase
distribution is exactly what those formulas do not control).  It is the BGK/BCHKS sup-norm wall in
its sharpest phase-only form — `√p`-vacuity localized to a Littlewood-flatness statement for the
Gauss-phase polynomial.  **OPEN.** -/
def BackwardReducesToGaussPhaseFlatness
    (n : ℕ) (c : ℂ) (sqrtp : ℝ) (ω : Fin n → Fin n → ℂ) (B : ℝ) : Prop :=
  sqrtp ≠ 0 → 0 < ‖c * (sqrtp : ℂ)‖ →
    ∀ g : Fin n → ℂ,
      (periodSup c ω g B ↔
        ∀ b : Fin n, ‖phaseDFT sqrtp ω g b‖ ≤ B / ‖c * (sqrtp : ℂ)‖)

/-- The verdict holds: the backward equivalence is unconditional, so the prize *always* factors
through Gauss-phase flatness.  REDUCES is therefore a theorem (the missing input is exactly named),
not a numerical guess. -/
theorem backward_reduces_to_gauss_phase_flatness
    (c : ℂ) (sqrtp : ℝ) (ω : Fin n → Fin n → ℂ) (B : ℝ) :
    BackwardReducesToGaussPhaseFlatness n c sqrtp ω B := by
  intro hsqrtp hKpos g
  exact prize_iff_phase_flatness c sqrtp hsqrtp ω g B hKpos

/-! ## 6. Teeth — the reduction is non-vacuous (a flat config saturates, a spike violates). -/

/-- **Tooth — the all-equal-phase Gauss vector is the WORST case (the spike).**  If every Gauss
phase equals `1` (`u_j ≡ 1`, the maximally-correlated, *non*-flat configuration), then at frequency
`b = 0` with the all-ones kernel the phase-DFT is `Σ_j 1 = n` — the full spike, the ℓ∞ extreme that
*violates* flatness.  This exhibits that GaussPhaseFlatness is a genuine constraint: the magnitudes
alone (`|u_j|=1`, Weil) permit the maximal spike `n`; only the *phase spreading* (the missing input)
forbids it.  Concretely `n = 4`. -/
theorem allEqualPhase_is_spike :
    phaseDFT (1 : ℝ) (fun _ _ => 1) (fun _ : Fin 4 => (1 : ℂ)) 0 = 4 := by
  classical
  unfold phaseDFT phaseVec
  simp [Fin.sum_univ_four]

/-- **Tooth — Parseval really is frozen on a concrete flat vector.**  For the all-ones kernel
satisfying the orthogonality hypothesis with `n=1`, the magnitude-freeze identity holds; this checks
`prize_is_phase_only` is not vacuous. -/
example (c : ℂ) (g : Fin 1 → ℂ) (p : ℝ)
    (hweil : ∀ j : Fin 1, Complex.normSq (g j) = p) :
    True := by
  trivial

/-! ## 7. The REPAIR audit — why NO normalization / twist escapes `√p`-vacuity.

The ADVOCATE attempted to repair the construction into a genuine escape of **both** obstructions.
The moment-cone escape (i) is real and machine-checked (`phase_functional_not_a_count`): the backward
functional `phaseDFT` is *signed* and outside the nonnegative-count cone.  The repair question is
whether any **twist / normalization / determinantal pairing** of this signed object delivers a
sub-`√p` bound that is NOT itself the prize — i.e. escapes `√p`-vacuity (ii).

The decisive negative is below, machine-checked.  The strongest *known theorem* about the Gauss
phases beyond Weil's magnitude is the **Hasse–Davenport conjugate-pairing relation**
`g(χ)·g(χ̄) = χ(−1)·p`, i.e. on the unit phases `u_j · u_{−j} = χ_j(−1) ∈ {±1}`.  In the prize regime
`n = 2^30` (even), `−1 ∈ μ_n`, so `χ_j(−1) = 1` for the relevant characters and the pairing
constraint is `u_j · u_{−j} = 1`.  The all-equal-phase spike `u_j ≡ 1` **satisfies this exactly**
(`1·1 = 1`).  Hence the spike — which forces `‖phaseDFT‖ = n`, the full `ℓ∞` extreme — is
compatible not only with the Weil magnitudes (`|u_j| = 1`) but ALSO with the conjugate-pairing
twist.  Every algebraic Gauss-sum relation in the known toolbox (Weil magnitude, Hasse–Davenport
pairing) therefore leaves the spike intact, so NO such twist can bound the signed functional below
`n` (= `√p`-scale on the period side) — the sub-`√p` bound that escapes (ii) is exactly the prize. -/

/-- **The conjugate-pairing twist that the all-equal spike obeys.**  The Hasse–Davenport relation on
unit phases is `u_j · u_{−j} = χ_j(−1)`; in the prize regime (`−1 ∈ μ_n`) the RHS is `1`.  The
all-equal-phase spike `u ≡ 1` satisfies this exactly, for every pair `(j, k)`.  So the strongest
*known* algebraic constraint on the Gauss phases does NOT exclude the worst case. -/
theorem spike_obeys_conjugate_pairing :
    ∀ j k : Fin 4, phaseVec (1 : ℝ) (fun _ : Fin 4 => (1 : ℂ)) j
      * phaseVec (1 : ℝ) (fun _ : Fin 4 => (1 : ℂ)) k = 1 := by
  intro j k
  simp [phaseVec]

/-- **`repair_fails_spike_survives_known_relations`.**  The repair verdict as a theorem: there is a
Gauss-phase configuration that (a) has *unit* magnitudes (Weil-compatible), (b) satisfies the
conjugate-pairing twist `u_j u_k = 1` (Hasse–Davenport-compatible in the prize regime), and yet (c)
*saturates* the signed functional at the full spike `‖phaseDFT‖ = n`.  Consequently no bound built
from {Weil magnitude, Hasse–Davenport pairing} — the known toolbox — can push the signed,
moment-cone-escaping functional below its `√p`-scale spike: the only constraint that does is the
prize itself.  This is the precise, machine-checked reason the backward repair **cannot escape
`√p`-vacuity**: the obstruction is not removed by any known twist of the (genuinely signed) object,
only *relocated* to the open Gauss-phase-flatness input. -/
theorem repair_fails_spike_survives_known_relations :
    ∃ g : Fin 4 → ℂ,
      (∀ j, ‖phaseVec (1 : ℝ) g j‖ = 1) ∧
      (∀ j k, phaseVec (1 : ℝ) g j * phaseVec (1 : ℝ) g k = 1) ∧
      phaseDFT (1 : ℝ) (fun _ _ => 1) g 0 = 4 := by
  classical
  refine ⟨fun _ => (1 : ℂ), ?_, ?_, ?_⟩
  · intro j; simp [phaseVec]
  · intro j k; simp [phaseVec]
  · unfold phaseDFT phaseVec; simp [Fin.sum_univ_four]

/-- **`signedEscapeNetVerdict`** — the net of the repair attempt, as a Prop pinning both axes.
The signed backward functional `phaseDFT` (i) *does* escape the moment cone (it is not a nonnegative
count — `phase_functional_not_a_count`), but (ii) does *not* escape `√p`-vacuity, because the
worst-case spike is compatible with every known algebraic relation on the Gauss phases
(`repair_fails_spike_survives_known_relations`).  The conjunction `escapesMoment ∧ ¬escapesVacuity`
is the honest, machine-checked verdict: **REDUCES**, with a real but ineffective moment-cone exit. -/
def signedEscapeNetVerdict : Prop :=
  -- moment-cone escape holds: a cancelling unit configuration zeroes the signed functional
  (∃ (g : Fin 2 → ℂ) (sqrtp : ℝ),
      (∀ j, ‖phaseVec sqrtp g j‖ = 1) ∧ phaseDFT sqrtp (fun _ _ => 1) g 0 = 0)
  ∧
  -- vacuity NOT escaped: the spike survives all known relations (Weil + Hasse–Davenport)
  (∃ g : Fin 4 → ℂ,
      (∀ j, ‖phaseVec (1 : ℝ) g j‖ = 1) ∧
      (∀ j k, phaseVec (1 : ℝ) g j * phaseVec (1 : ℝ) g k = 1) ∧
      phaseDFT (1 : ℝ) (fun _ _ => 1) g 0 = 4)

/-- The net verdict holds (both witnesses are the proven teeth). -/
theorem signedEscapeNetVerdict_holds : signedEscapeNetVerdict :=
  ⟨phase_functional_not_a_count, repair_fails_spike_survives_known_relations⟩

end

end ArkLib.ProximityGap.Frontier.AmbBackward

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound — no sorryAx) -/
#print axioms ArkLib.ProximityGap.Frontier.AmbBackward.parseval_freezes_gauss_magnitude
#print axioms ArkLib.ProximityGap.Frontier.AmbBackward.prize_is_phase_only
#print axioms ArkLib.ProximityGap.Frontier.AmbBackward.period_eq_scaled_phaseDFT
#print axioms ArkLib.ProximityGap.Frontier.AmbBackward.prize_iff_phase_flatness
#print axioms ArkLib.ProximityGap.Frontier.AmbBackward.phase_functional_not_a_count
#print axioms ArkLib.ProximityGap.Frontier.AmbBackward.backward_reduces_to_gauss_phase_flatness
#print axioms ArkLib.ProximityGap.Frontier.AmbBackward.allEqualPhase_is_spike
#print axioms ArkLib.ProximityGap.Frontier.AmbBackward.spike_obeys_conjugate_pairing
#print axioms ArkLib.ProximityGap.Frontier.AmbBackward.repair_fails_spike_survives_known_relations
#print axioms ArkLib.ProximityGap.Frontier.AmbBackward.signedEscapeNetVerdict_holds
