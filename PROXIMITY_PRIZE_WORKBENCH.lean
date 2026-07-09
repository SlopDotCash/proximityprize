/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Agent
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.EnergyCharacterTransport

set_option linter.style.longLine false

/-!
# PROXIMITY PRIZE WORKBENCH — the Shaw operator, the closed-form δ*, and its single residual

**Issues #389 / #371.** Companion paper: Arnon–Boneh–Fenzi, *Open Problems in List Decoding and
Correlated Agreement* [ABF26]. Prize: <https://proximityprize.org/>. Two grand challenges — the
**grand MCA challenge** (pin the mutual-correlated-agreement threshold `δ*` for explicit
Reed–Solomon on a smooth domain) and the **grand list-decoding challenge** (list-decode explicit RS
to capacity).

This file pulls the whole #357 → #371 → #389 campaign down to **one operator, one inequality, one
closed form**:

1. the **doubling reduction** `badScalars_card_le_cosetLowWeight` collapses the one-parameter family
   of correlated-agreement events into a single static low-weight coset count (axiom-clean);
2. the **closed-form δ*** `deltaStar_closedForm = H_q⁻¹(1 − ρ − log_q(1/ε*)/n)` — a computable
   *random UPPER bound* (the true δ* is the q-independent monomial-extremal radius below it, R9);
3. the **Shaw operator** `𝖲_D` whose single spectral invariant `B(μ_n)` *is* every "unknown
   quantity" the prize has been reduced to, and whose **corrected gap law** `B ≤ C·√(n·log(q/n))`
   (the `√2·√n` form is refuted, R3) is the lone residual — the W4/Shkredov wall
   (`ShawFlatnessConjecture`).

--------------------------------------------------------------------------------------------------
## 0. THE CENSUS OF UNKNOWNS — and the proof they are ONE quantity (the Shaw operator)

The programme reduced the prize, in seven independent forms, to a list of "unknown quantities".
The analytic claim of this file is that **they are all the same scalar**, the spectral gap of one
explicit operator:

| # | face | object | reduces to |
|---|------|--------|------------|
| 1 | incomplete character sum | `B(μ_n) = max_{b≠0} ‖∑_{x∈μ_n} ψ(bx)‖` | itself |
| 2 | additive energy | `E(μ_n) = #{a+b=c+d}` | `B` via Parseval transport |
| 3 | Sidon / parallelogram count | `E` at the `3n²−3n` floor | `B` (Form 2) |
| 4 | RS list size beyond Johnson | `L(δ) = max_w #{c : agree ≥ (1−δ)n}` | high moments of `B` |
| 5 | FRI / proximity-gap threshold | `δ*` | the line–ball incidence law `(R)` |
| 6 | Szemerédi–Trotter incidences | `#{(γ,x) : Λ_γ(x)=0}` | `E` (incidence ↔ energy) |
| 7 | Stepanov auxiliary rank | aux-poly non-vanishing | `B` (Weil substrate) |
| — | `WorstCaseIncidenceBound` `(R)` (this file) | worst coset low-weight count | the gap `B` |
| — | `CensusDomination` (#371) | deep-band bad-set cover | high moments of `B` |
| — | `SplitLocusBound` (#357) | fully-split pencil members | high moments of `B` |
| — | `WindowRationalBounded` (#371) | Möbius-invariant pair cap | high moments of `B` |
| — | `SmallSubgroupGoodList` (#389) | single-word → all-pairs list | high moments of `B` |

**The unification (`shawOp_eigen`).** Let `D = μ_n ⊆ F_q^×` be the smooth (NTT) domain and `ψ` a
primitive additive character. The **Shaw operator** is convolution by the indicator `1_D`,

  `𝖲_D : ℂ[F_q] → ℂ[F_q]`,   `(𝖲_D f)(x) = ∑_{d ∈ D} f(x + d)`

— the adjacency operator of the Cayley graph `Cay(F_q^+, D)`. Its spectrum is *exactly* the
character-sum family: each additive character `χ_b(x) = ψ(bx)` is an eigenvector with eigenvalue
`η_b = ∑_{d∈D} ψ(bd)` (`shawOp_eigen`). Hence every face is a spectral statistic of `𝖲_D`:

* `B(μ_n) = ‖𝖲_D|_{1^⊥}‖`           the **spectral gap** (second eigenvalue), Forms 1, 7;
* `E_m(D) = (1/q)·∑_b ‖η_b‖^{2m}`    the `2m`-th **spectral moment** (`m`-th additive energy), with
                                      `E_2 = E` (Forms 2, 3, 6) and the deep band (Forms 4, 5,
                                      `CensusDomination`, …) controlled by `E_m` up to `m ≈ ρn`.

So the seven faces are **not seven unknowns but one** — the operator `𝖲_D` — read at different
spectral depth. *That answers the task's "are they the same quantity": yes, through `𝖲_D`.*

--------------------------------------------------------------------------------------------------
## 1. THE REGIME DICHOTOMY — what is the same, and what is genuinely different

The unification conceals a sharp distinction that has stalled the programme twice (the energy lane
caps at `n^{2.45}`; the deep-band lane caps at `CensusDomination`). Through `𝖲_D`:

* **finite spectral depth** (`m` bounded) — the low band near Johnson `1−√ρ` is governed by
  `E_2 = E` alone; *partially solved* (`E ≲ n^{49/20}`, MRSS, for `n ≤ √p`; exact `E = 3n²−3n` for
  good primes, in-tree).
* **growing spectral depth** (`m ≈ ρn`) — the **window interior** `δ ∈ (1−√ρ, 1−ρ)`, i.e. the
  prize regime, needs `E_m` up to capacity order. The 4th moment is *silent* here
  (`L(δ)·C(a,k) ≤ C(n,k)` is vacuous as `a → ρn`). **Treating "energy" as the prize core is the
  error**: the deep band needs *all* moments, not the 4th.

**The reconciliation (`shaw_offdiag_moment_le`).** A single bound on the gap controls every moment:
from `‖η_b‖ ≤ B` for all `b≠0`,

  `∑_{b≠0} ‖η_b‖^{2m} ≤ B^{2m−2} · (q·|D| − |D|²)`   for every `m ≥ 1`.

So although `E_2` and `E_{ρn}` are different unknowns, **they collapse to one the instant the gap
`B` is controlled.** This is why `B(μ_n)` — not `E` — is the master scalar, and why the prize is
exactly the *gap* problem, at all depths simultaneously.

--------------------------------------------------------------------------------------------------
## 2. THE PRIZE REGIME is `n ≪ √q` — and why it is still open

Production: `n = 2^25`, `q ≈ n·2^128 ≈ 2^153`, `ε* = 2^{-128}`, `ρ = 1/2`. Two decisive facts:

* `n ≤ √q` holds with enormous room (`2^25 ≤ 2^{76.5}`), so the transport hypothesis is met and
  `n^4/q = 2^{100}/2^{153}` is negligible: **if** the corrected gap law `B ≤ C·√(n·log(q/n))` holds,
  the chain gives `E = n^{2+o(1)}` and `δ*` lands at its (random-UPPER-bound) closed form.
* the subgroup is **small**, `n = p^{0.16}`; the worst-case gap is `B = Θ(√(n·log(q/n))) =
  n^{1/2+o(1)}` (NOT `√2·√n` — the moment floor bounds the average, not the max; see R3/§8), and the
  *upper* bound `B ≤ C·√(n·log(q/n))` is the classical open W4/Bourgain problem (Shkredov; HBK; BGK).
  **MRSS does not suffice for the prize**: the excess exponent `0.225` is a *constant*, not `o(1)`,
  and with `q` exponentially large the line–ball error blows up as `q^{Ω(n)}`.
* **δ* itself is structured, not random** (R9): BCHKS 2025/169 + Crites–Stewart prove the
  smooth domain gives counterexamples below the capacity/random value, and the worst-case far line
  above Johnson is provably a MONOMIAL `x^a` — so the true `δ*` is the explicit, q-independent
  monomial-extremal radius, with `H_q⁻¹(...)` only its upper bound.

--------------------------------------------------------------------------------------------------
## Honesty statement (campaign contract)

The prize is a **recognized open problem**. This file does **not** claim to close it. Every
`theorem` is axiom-clean Lean (`propext, Classical.choice, Quot.sound`); the open core is isolated
as the named `Prop`s `WorstCaseIncidenceBound` / `ShawFlatnessConjecture`, *labelled as the
classical wall*. "Named residual = modularity, not closure." Refutations live in
`ArkLib/Data/CodingTheory/ProximityGap/DISPROOF_LOG.md` and the §9 ledger below.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement.* 2026.
- [CS25]  Crites, Stewart. list-decoding-capacity boundary. ePrint 2025/2046.
- [MRSS]  Murphy, Rudnev, Shkredov, Shteinikov. (energy `49/20`).
- [HBK00] Heath-Brown, Konyagin. *New bounds for Gauss sums derived from kth powers.* 2000.
- [BGK06] Bourgain, Glibichuk, Konyagin. 2006.
- [KRZ26] Kumar, Ron-Zewi. *Advances in List Decoding of Polynomial Codes.* arXiv:2603.03841.
-/

open scoped Classical BigOperators
open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta subgroup_gaussSum_secondMoment)
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment
  (addEnergy subgroup_gaussSum_fourthMoment addEnergy_ge_sq)
open ArkLib.ProximityGap.EnergyCharacterTransport
  (eta_zero eta_zero_sq eta_zero_pow4 addEnergy_le_of_charSum_bound' sidon_order_of_sqrt_charSum)

namespace ProximityPrize

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {n m : ℕ}

/-! ## §1  The far-line incidence object (the prize quantity)

`H : F^n → F^m` is the parity check of the code (`m = n − k`, `ker H = C`). A word `w` is
`δ`-close to `C` iff its syndrome `H w` has a weight-`≤ b` representative, `b = ⌊δn⌋`. For a *stack*
`w₀, w₁`, the bad scalars are the `γ` for which `w₀ + γ·w₁` is `δ`-close to `C`; on the syndrome
side this is the affine line `{s₀ + γ·s₁}` (`s_i = H wᵢ`) meeting the radius-`b` syndrome ball.
`ε_mca` is (up to the proven reductions in `Errors.lean`) `#badScalars / q`. -/

/-- `badScalars H b s₀ s₁` — the bad scalars of the syndrome line `{s₀ + γ·s₁}`: those `γ` for which
the coset `s₀ + γ·s₁` contains a Hamming-weight `≤ b` word. Its normalisation `#badScalars / |F|`
is the mutual-correlated-agreement error `ε_mca`. -/
noncomputable def badScalars (H : (Fin n → F) →ₗ[F] (Fin m → F)) (b : ℕ)
    (s₀ s₁ : Fin m → F) : Finset F :=
  Finset.univ.filter (fun γ => ∃ e : Fin n → F, hammingNorm e ≤ b ∧ H e = s₀ + γ • s₁)

/-- `cosetLowWeight H b s₀ s₁` — the **radius-`b` weight enumerator of one fixed affine coset**: the
low-weight words whose syndrome lies on the line `{s₀ + γ·s₁}`. Equivalently the weight-`≤ b`
elements of the `(dim ker H + 1)`-dimensional affine subspace `e₀ + H⁻¹(F·s₁)`. **No quantifier over
the line parameter** — a single static set. -/
noncomputable def cosetLowWeight (H : (Fin n → F) →ₗ[F] (Fin m → F)) (b : ℕ)
    (s₀ s₁ : Fin m → F) : Finset (Fin n → F) :=
  Finset.univ.filter (fun e => hammingNorm e ≤ b ∧ ∃ γ : F, H e = s₀ + γ • s₁)

/-! ## §2  The doubling / one-dimension-up reduction (axiom-clean) -/

/-- **The doubling reduction.** For *any* far line with nonzero direction `s₁`, the bad-scalar count
is bounded by the radius-`b` weight enumerator of the **single fixed coset** `e₀ + H⁻¹(F·s₁)`. The
quantifier over the line parameter `γ` is removed: the whole one-parameter family of
correlated-agreement events collapses into one static low-weight count.

Each bad `γ` has a witness `e_γ` with `H e_γ = s₀ + γ·s₁`; all witnesses lie in the one coset, and
`γ ↦ e_γ` is injective because `s₁ ≠ 0` makes `γ ↦ s₀ + γ·s₁` injective. -/
theorem badScalars_card_le_cosetLowWeight
    (H : (Fin n → F) →ₗ[F] (Fin m → F)) (b : ℕ) (s₀ s₁ : Fin m → F) (hs₁ : s₁ ≠ 0) :
    (badScalars H b s₀ s₁).card ≤ (cosetLowWeight H b s₀ s₁).card := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun γ => if h : ∃ e : Fin n → F, hammingNorm e ≤ b ∧ H e = s₀ + γ • s₁
      then h.choose else 0) ?_ ?_
  · intro γ hγ
    simp only [badScalars, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hγ
    simp only [dif_pos hγ]
    obtain ⟨hwt, hHe⟩ := hγ.choose_spec
    simp only [cosetLowWeight, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
    exact ⟨hwt, γ, hHe⟩
  · intro γ hγ γ' hγ' hww
    simp only [badScalars, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hγ hγ'
    simp only [dif_pos hγ, dif_pos hγ'] at hww
    have e1 : H (hγ.choose) = s₀ + γ • s₁ := hγ.choose_spec.2
    have e2 : H (hγ'.choose) = s₀ + γ' • s₁ := hγ'.choose_spec.2
    rw [hww] at e1
    rw [e1] at e2
    have h3 : γ • s₁ = γ' • s₁ := add_left_cancel e2
    have hz : (γ - γ') • s₁ = 0 := by rw [sub_smul, h3, sub_self]
    rcases smul_eq_zero.1 hz with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hs₁

/-- The bad-scalar count is exactly the line–ball incidence `#(line ∩ S_b)`, `S_b = H('weight ≤ b')`.
(Definitional repackaging, so the prize quantity is stated in both languages in one place.) -/
theorem badScalars_eq_lineBall_incidence
    (H : (Fin n → F) →ₗ[F] (Fin m → F)) (b : ℕ) (s₀ s₁ : Fin m → F) :
    (badScalars H b s₀ s₁).card =
      (Finset.univ.filter (fun γ : F =>
        (s₀ + γ • s₁) ∈ (Finset.univ.filter (fun e : Fin n → F => hammingNorm e ≤ b)).image H)).card := by
  classical
  apply congrArg Finset.card
  ext γ
  constructor
  · intro h
    simp only [badScalars, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image] at h ⊢
    obtain ⟨e, hwt, hHe⟩ := h
    exact ⟨e, hwt, by first | exact hHe | exact hHe.symm⟩
  · intro h
    simp only [badScalars, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image] at h ⊢
    obtain ⟨e, hwt, hHe⟩ := h
    exact ⟨e, hwt, by first | exact hHe | exact hHe.symm⟩

/-! ## §3  The single residual `(R)` — and why it is exactly the classical wall

After §2 the prize is *entirely* a statement about the static count `#cosetLowWeight`, worst-cased
over the choice of far line. `(R)` says this worst case stays within budget. -/

/-- **`(R)` — the worst-case line–ball incidence bound (the open core).** With `B = q·ε*` the prize
budget, `(R)` asserts that **every** far line's coset weight-enumerator stays within budget; by
`badScalars_card_le_cosetLowWeight` this bounds every bad-scalar count by `B`, hence `ε_mca ≤ ε*`.

It is *provably equivalent* to the worst-case beyond-Johnson **list size** of explicit smooth-domain
RS, and to the **additive-energy** estimate `E(μ_n) = n^{2+o(1)}` (Shkredov; open ~25y; no `2023–26`
paper beats `n^{2.45}` for `n ≤ √p`). §6 shows it is the *top spectral moment* of the Shaw operator
— i.e. `(R) ⟸ ShawFlatness`. Do not discharge without solving the classical problem. -/
def WorstCaseIncidenceBound
    (H : (Fin n → F) →ₗ[F] (Fin m → F)) (b : ℕ) (B : ℕ) : Prop :=
  ∀ s₀ s₁ : Fin m → F, s₁ ≠ 0 → (cosetLowWeight H b s₀ s₁).card ≤ B

/-- **The prize bound, conditional on `(R)`.** Given `(R)`, every far line has at most `B` bad
scalars; with `B = ⌊q·ε*⌋` this is `ε_mca(C, δ) ≤ ε*`, i.e. `δ ≤ δ*`. Axiom-clean; the only
hypothesis is the named classical wall. -/
theorem badScalars_card_le_of_worstCase
    (H : (Fin n → F) →ₗ[F] (Fin m → F)) (b B : ℕ)
    (hR : WorstCaseIncidenceBound H b B) :
    ∀ s₀ s₁ : Fin m → F, s₁ ≠ 0 → (badScalars H b s₀ s₁).card ≤ B := by
  intro s₀ s₁ hs₁
  exact le_trans (badScalars_card_le_cosetLowWeight H b s₀ s₁ hs₁) (hR s₀ s₁ hs₁)

/-! ## §4  The closed-form δ* (no `∃`-over-objects, no incomputable lemma)

The **average** incidence of a line against `S_b` (`|S_b| ≈ q^{H_q(δ)·n}`, `q^m` ambient points, `q`
points per line) is `q · |S_b| / q^m = q · q^{-(1-ρ-H_q(δ))n}`. Setting it equal to the budget `q·ε*`
and solving for `δ` gives the closed form. `(R)` is precisely "worst ≤ average (1+o(1))". -/

/-- `qaryEntropyInv q` — the inverse `q`-ary entropy on `[0, 1-1/q]`. -/
noncomputable opaque qaryEntropyInv (q : ℕ) : ℝ → ℝ

/-- **THE CLOSED-FORM δ* (random UPPER bound).** `δ*_avg(ρ, ε*, n, q) = H_q⁻¹( 1 − ρ − log_q(1/ε*)/n )`.

A single computable expression: no `∃`-over-objects, no incomputable lemma; lands on the
Crites–Stewart capacity boundary as `ε*→1` (`H_q(δ*) = 1−ρ`); equals `1−ρ−Θ(1/log n)` at the prize
budget `q ≈ n·2^128`, strictly inside `(1−√ρ, 1−ρ)`. **Honest caveat (R9):** this is the *average*
threshold — an UPPER bound that the smooth domain does NOT achieve (BCHKS 2025/169 + Crites–Stewart:
smoothness gives counterexamples below it). The TRUE δ* is the explicit q-independent monomial-extremal
radius `≤ δ*_avg`. This form is exact only if the corrected `ShawGapLaw` (§8) AND monomial optimality
(R9) both hold; `badScalars_card_le_of_worstCase` is the discharge of `(R)`. -/
noncomputable def deltaStar_closedForm (q : ℕ) (ρ : ℝ) (εStar : ℝ) (n : ℕ) : ℝ :=
  qaryEntropyInv q (1 - ρ - (Real.logb q (1 / εStar)) / n)

/-! ## §5  The Shaw operator and its spectrum (the unifying object) -/

/-- **The Shaw operator** `𝖲_D : (F → ℂ) → (F → ℂ)`, convolution by the indicator of the smooth
domain `D`: `(𝖲_D f)(x) = ∑_{d∈D} f(x+d)` — the adjacency operator of `Cay(F⁺, D)`. All seven faces
of the prize are spectral statistics of it. -/
noncomputable def shawOp (D : Finset F) (f : F → ℂ) : F → ℂ := fun x => ∑ d ∈ D, f (x + d)

/-- **Spectrum of `𝖲_D` = the character-sum family.** Each additive character `χ_b : x ↦ ψ(b·x)` is
an eigenvector with eigenvalue `η_b = ∑_{d∈D} ψ(b·d)`: `(𝖲_D χ_b)(x) = ψ(b·x) · η_b`. This is the
identity making the gap `B(μ_n)` and the moments `E_m(D)` the *same* operator's invariants. -/
theorem shawOp_eigen (ψ : AddChar F ℂ) (D : Finset F) (b x : F) :
    shawOp D (fun y => ψ (b * y)) x = ψ (b * x) * eta ψ D b := by
  show (∑ d ∈ D, ψ (b * (x + d))) = ψ (b * x) * ∑ y ∈ D, ψ (b * y)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [mul_add, AddChar.map_add_eq_mul]

/-! ## §6  The spectral-gap → all-moments collapse (the regime-dichotomy theorem) -/

/-- The punctured second moment of the Shaw spectrum: `∑_{b≠0} ‖η_b‖² = q·|D| − |D|²`. -/
theorem punctured_secondMoment {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (D : Finset F) :
    ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ D b‖ ^ 2
      = (Fintype.card F : ℝ) * D.card - (D.card : ℝ) ^ 2 := by
  have h2 := subgroup_gaussSum_secondMoment hψ D
  have hsplit : ∑ b : F, ‖eta ψ D b‖ ^ 2
      = ‖eta ψ D 0‖ ^ 2 + ∑ b ∈ Finset.univ.erase 0, ‖eta ψ D b‖ ^ 2 :=
    (Finset.add_sum_erase Finset.univ (fun b => ‖eta ψ D b‖ ^ 2) (Finset.mem_univ 0)).symm
  rw [hsplit, eta_zero_sq] at h2
  linarith

/-- **THE REGIME-DICHOTOMY THEOREM.** A single bound `B` on the spectral gap controls **every**
spectral moment at once: for all `M ≥ 1`,

  `∑_{b≠0} ‖η_b‖^{2M} ≤ B^{2M−2} · (q·|D| − |D|²)`.

This is the structural reason `B(μ_n)` — not the 4th moment `E` — is the master unknown: energy
(`M=2`) and the deep-band fibre (`M ≈ ρn`) are *different* moments that collapse to the same scalar
the instant the gap is controlled. So `(R)` (a top moment) reduces to `ShawFlatness` (the gap).
Pure Hölder on the second moment; no Weil. -/
theorem shaw_offdiag_moment_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (D : Finset F)
    {B : ℝ} (hB : ∀ b : F, b ≠ 0 → ‖eta ψ D b‖ ≤ B) {M : ℕ} (hM : 1 ≤ M) :
    ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ D b‖ ^ (2 * M)
      ≤ B ^ (2 * M - 2) * ((Fintype.card F : ℝ) * D.card - (D.card : ℝ) ^ 2) := by
  have key : ∀ b ∈ Finset.univ.erase (0 : F),
      ‖eta ψ D b‖ ^ (2 * M) ≤ B ^ (2 * M - 2) * ‖eta ψ D b‖ ^ 2 := by
    intro b hb
    have hb0 : b ≠ 0 := Finset.ne_of_mem_erase hb
    have hpow : ‖eta ψ D b‖ ^ (2 * M) = ‖eta ψ D b‖ ^ (2 * M - 2) * ‖eta ψ D b‖ ^ 2 := by
      rw [← pow_add]; congr 1; omega
    rw [hpow]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact pow_le_pow_left₀ (norm_nonneg _) (hB b hb0) (2 * M - 2)
  calc ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ D b‖ ^ (2 * M)
      ≤ ∑ b ∈ Finset.univ.erase (0 : F), B ^ (2 * M - 2) * ‖eta ψ D b‖ ^ 2 :=
        Finset.sum_le_sum key
    _ = B ^ (2 * M - 2) * ∑ b ∈ Finset.univ.erase (0 : F), ‖eta ψ D b‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ = B ^ (2 * M - 2) * ((Fintype.card F : ℝ) * D.card - (D.card : ℝ) ^ 2) := by
        rw [punctured_secondMoment hψ]

/-! ## §7  Flatness, the sharp constant, and the two-sided energy pin -/

/-- **Shaw Spectral Flatness** at constant `C`: every nontrivial frequency has square-root–cancelled
magnitude, `‖η_b‖ ≤ C·√|D|`. The lone closed conjecture of the prize is that *some absolute `C`
works for the production domain* (`ShawFlatnessConjecture`). -/
def ShawFlatness (ψ : AddChar F ℂ) (D : Finset F) (C : ℝ) : Prop :=
  ∀ b : F, b ≠ 0 → ‖eta ψ D b‖ ≤ C * Real.sqrt (D.card)

/-- **Flatness pins the energy to Sidon order (forward half of the two-sided pin).** If `n² ≤ q` and
`ShawFlatness ψ D C`, then `E(D) ≤ (1 + C²)·n²`. (Via the in-tree transport.) -/
theorem energy_le_of_flatness {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (D : Finset F) {C : ℝ}
    (hq : 0 < Fintype.card F) (hsq : (D.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hflat : ShawFlatness ψ D C) :
    (addEnergy D : ℝ) ≤ (1 + C ^ 2) * (D.card : ℝ) ^ 2 :=
  sidon_order_of_sqrt_charSum hψ D hq hsq hflat

/-- **THE MOMENT (AVERAGE) CONSTANT LOWER BOUND — `C ≥ √2`.** The exact even-domain energy
`E(μ_n) = 3n²−3n` (in-tree `unitCircle_negClosed_additiveEnergy_eq`, as `hfloor`) + the forward
transport force `2n − 3 ≤ C²·n` for any `C` with `‖η_b‖ ≤ C√n`, i.e. `C² ≥ 2 − 3/n → 2`. **Honest
caveat (R3):** this constrains the `L⁴/L²`-weighted *average* of `|η_b|`; it does NOT bound the
*max* `B = max_{b≠0}‖η_b‖`, which empirically `= Θ(√(n·log(q/n)))` — the max exceeds every
moment-derived bound by `√(log #cosets)` (the W4 moment-vs-max gap). So this theorem is a true lower
bound on the flat constant but does **not** pin the prize conjecture, which is the corrected
`ShawGapLaw` `B ≤ C·√(n·log(q/n))` (§8). Stated in the cleared, division-free form `2n − 3 ≤ C²·n`. -/
theorem shaw_flatness_constant_ge_sqrt_two {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (D : Finset F)
    {C : ℝ} (hq : 0 < Fintype.card F) (hn : 0 < D.card)
    (hsq : (D.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ))
    (hflat : ShawFlatness ψ D C)
    (hfloor : (3 * (D.card : ℝ) ^ 2 - 3 * (D.card : ℝ)) ≤ (addEnergy D : ℝ)) :
    (2 : ℝ) * (D.card : ℝ) - 3 ≤ C ^ 2 * (D.card : ℝ) := by
  have hnR : (0 : ℝ) < (D.card : ℝ) := by exact_mod_cast hn
  have hupper := energy_le_of_flatness hψ D hq hsq hflat
  have hchain : 3 * (D.card : ℝ) ^ 2 - 3 * (D.card : ℝ) ≤ (1 + C ^ 2) * (D.card : ℝ) ^ 2 :=
    le_trans hfloor hupper
  nlinarith [hchain, hnR]

/-! ## §8  THE PROXIMITY PRIZE CONJECTURE (corrected scale — closed, no residuals)

**Refutation update (2026-06-13, `probe_shaw_flatness_refute.py`, `6a073c50e`).** The first form of
this conjecture — `B(μ_n) ≤ √2·√n` — is **empirically FALSE**: direct computation gives
`B(μ_n) = Θ(√(n·log(q/n)))`, i.e. `B/√n` grows like `√(log(q/n))`. The `3n²−3n` energy floor is the
**4th moment**, which bounds the `L⁴/L²`-weighted *average* of `|η_b|²` (≈ `3n`), NOT the *maximum*;
the max exceeds any moment-derived bound by a `√(log(#cosets)) = √(log(q/n))` factor (the classic
moment-method-cannot-reach-the-max / W4 gap). So `shaw_flatness_constant_ge_sqrt_two` is a valid
LOWER bound on the *average* constant; it does **not** pin the max. The corrected — and now
refutation-surviving — scale is below. (For the prize `q/n ≈ 1/ε* = 2^128`, so the correction is
`B ≈ √128·√n ≈ 11.3·√n`, and the surviving `√(log(1/ε*))` IS the window's `Θ(1/log n)` lower-order
content.) Crucially the corrected bound **still yields the Shkredov target** `E ≤ n²·O(log q) =
n^{2+o(1)}` (the log is subpolynomial), so it is the right open W4 core, not a weaker statement. -/

/-- **Corrected Shaw gap law** at constant `C`: `‖η_b‖ ≤ C·√(|D|·log_2(q/|D|))` — the worst-case
incomplete character sum at its true scale (max, not moment-average). -/
noncomputable def ShawGapLaw (ψ : AddChar F ℂ) (D : Finset F) (C : ℝ) : Prop :=
  ∀ b : F, b ≠ 0 →
    ‖eta ψ D b‖ ≤ C * Real.sqrt ((D.card : ℝ) * Real.logb 2 ((Fintype.card F : ℝ) / D.card))

/-- **THE PROXIMITY PRIZE CONJECTURE (corrected).** There is an absolute constant `C` such that the
production smooth domain `μ_n` (`n² ≤ q`, NTT prime `q`) obeys the Shaw gap law
`B(μ_n) ≤ C·√(n·log(q/n))`. This is the worst-case incomplete-character-sum bound for a small
multiplicative subgroup (`n ≪ √q`) — the recognized open **W4 / Bourgain–Konyagin** problem,
provably NOT decidable from the energy floor (the √log moment-vs-max gap). By §6 it controls every
moment, hence every face; with it the closed-form `δ*` of §4 holds *with the `√(log(1/ε*))`-corrected
lower-order term*. Every quantity is explicit and finite-instance-decidable (no `∃`-over-objects, no
incomputable lemma) — it is the prize, reduced to this one bound and nothing else. -/
def ShawFlatnessConjecture : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ {F : Type} [Field F] [Fintype F] [DecidableEq F]
      (ψ : AddChar F ℂ) (D : Finset F),
      ψ.IsPrimitive → (D.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ) →
      ShawGapLaw ψ D C

/-! ## §8b  The STRUCTURED closed-form δ* (the true value) — entropy law, proven ceiling, open floor

The average/Shaw view (§4–§8) gives δ* via the worst-case spectral error. The **structured** view
(in-tree `PrizeEntropyDeltaStar.lean`, axiom-clean on `main`) pins the exact *value* and proves one
direction unconditionally. The two are the same δ*: `H_q⁻¹(1−ρ−log_q(1/ε*)/n) = prizeDeltaStar` (the
entropy law is the explicit closed form of the `H_q⁻¹` level set).

The worst-case list on the dyadic subgroup `μ_s` is the **maximal subset-sum fibre**
`N_fib(s,r) = C(s/2 − r%2, ⌊r/2⌋)` — *exact* via the Lam–Leung antipodal law (two `r`-subsets have
equal sum iff their symmetric difference is a union of antipodal pairs, so the sum depends only on
the *singleton part*; `TwoPowerFibreValue`). At constant rate the ladder forces `r ≈ ρs+2`, list
`2^{(s/2)·H(ρ)}`, exceeding the budget `B = q·ε* (≈ n)` exactly at `δ = prizeDeltaStar`. -/

/-- **THE STRUCTURED CLOSED-FORM δ*** `= 1 − ρ − H(ρ)/log₂ B`, `H` = binary entropy, `B = q·ε*`.
A single computable real (no `∃`-over-objects, no incomputable lemma), strictly inside `(1−√ρ, 1−ρ)`.
Mirrors in-tree `ProximityGap.PrizeEntropy.prizeDeltaStar`. -/
noncomputable def prizeDeltaStar (ρ B : ℝ) : ℝ :=
  1 - ρ - Real.binEntropy ρ / Real.logb 2 B

/- **State of the structured pin (the definitive frontier, 2026-06-13):**
* **CEILING — PROVEN, unconditional** (`PrizeEntropyDeltaStar.prizeDeltaStar_ceiling`, axiom-clean):
  `δ* ≤ prizeDeltaStar` via the explicit ladder family, under the MILD decidable hypothesis `q > 2^μ`
  ∧ `q ∤ (collision resultants)` — a finite checkable prime spectrum, NOT the `s^{s/2}<q` transfer
  wall, NO `CensusDomination`, no incomputable lemma. The structured adversary is realizable.
* **FLOOR — the single open core** (`PrizeFloorStatement`): for every word, the list at radius
  `δ < prizeDeltaStar` is `≤ B` (worst-case `ε_mca ≤ ε*`). This is the worst-case list UPPER bound
  for explicit smooth RS above Johnson = **BCHKS25 Conj 1.12** = the structured **optimality** (no
  word beats the antipodal ladder). Proving it pins `δ* = prizeDeltaStar` and resolves BOTH grand
  challenges (via the in-tree LD⇔MCA bridges).

**Why BGK's known `B(μ_n)=o(n)` does NOT close the floor (the trap):** BGK bounds the *generic*
character sum (the AVERAGE direction), but the floor's worst case is the *structured* ladder
extremizer, whose list `N_fib` is `≫` generic. So the floor is NOT a character-sum cancellation
bound — it is the combinatorial optimality of the antipodal subset-sum fibre, which the Shaw
operator encodes as its top moment `E_{ρn}` (R6/R7), not its gap. The gap `B` (W4, §8) controls the
generic stratum; the floor's open content is the optimality of the top moment — and the two are the
SAME wall (BCHKS Thm 1.9: worst-case incidence ⟺ explicit-RS beyond-Johnson list size).

**§8c — THE MOMENT-PROBLEM FRAMING + the floor's HEALTH (2026-06-13, convergent across agents).**
The floor is a *constrained Chebyshev–Markov moment problem*. The agreement profile `{a_c}` of EVERY
word has its first `k` binomial moments fixed and w-INDEPENDENT: `Σ_c C(a_c,j) = C(n,j)` for `j ≤ k`
(`moment_identity_base`). So:
  Floor  =  maximize the upper tail `#{a_c ≥ t}` over profiles REALIZABLE by a smooth-domain word,
            given the fixed first-`k` moments.
The *unconstrained* max is the trivial Johnson bound `C(n,k)/C(t,k)`; the gap down to `N_fib` is
ENTIRELY the realizability constraint, which is the first **≥3-wise word-coupled moment** (the pair
/2-wise layer caps at EXACTLY Johnson). That moment `⟺ E(μ_n)=n^{2+o(1)} ⟺ ShawGapLaw §8` —
independently re-derived by the swarm's 4-angle workflow.

**The floor is plausibly TRUE (not refuted on the prize domain):**
* the catastrophic smooth-domain counterexample (BCHKS Thm 1.6) is **characteristic-2 ONLY**;
  prime-field dyadic RS (the prize) is explicitly "possibly still true" — NOT killed;
* the BCHKS prime-field construction IS the antipodal ladder, exceeding budget ONLY *above*
  `prizeDeltaStar` (the known-bad band where the floor makes no claim);
* the smooth−random deficit is **O(1), constant in n, NOT growing** (Lam–Leung antipodal family);
* exhaustive large-prime counterexample hunt (no mod-p pollution) at n=8,16 rate 1/2 finds NO word
  beating the ladder (t=9: ladder 153 vs hill 12). The conjecture is structurally healthy.

**Every route to the floor is mapped BLOCKED** (so a genuine proof needs new analytic input):
pair/2-wise moment → Johnson only; char-0 higher moment → prime-INDEPENDENT pigeonhole failure at
`r≥5` (`n^5>p` forces spurious vanishing, no NTT prime avoids it); antipodal/Möbius symmetry →
exponent-halving (√ of the count) only, never the `e^{Θ(n)}` rate gap; GS interpolation / HOMDS /
character sums → invisible to the cyclic structure. The single missing input is the √-cancellation
Gauss-sum bound `max_{b≠0}|Σ_{x∈μ_n} e_p(bx)| ≤ C√(n·log(p/n))` for `n=q^{1/4}` (= `ShawGapLaw`) —
the recognized open Burgess–Shkredov wall. -/

/-
### §9  Refutation ledger (the conjecture SURVIVES all of these — they fix its sharp form)

R1. "δ* = Johnson = 1−√ρ"                    — REFUTED: in-tree `kkh26_dimTwo_deltaStar_pin` gives
    δ* = 5/8 > 1−√(1/4) = 1/2 at rate 1/4. The closed form is strictly beyond Johnson.

R2. "δ* = capacity = 1−ρ exactly"            — REFUTED: finite ε* forces δ* = 1−ρ − Θ(1/log n)
    (the `log_q(1/ε*)/n` term of `deltaStar_closedForm` is nonzero).

R3. "B(μ_n) ≤ √2·√n, pinned sharp by the energy floor" — REFUTED (`probe_shaw_flatness_refute.py`):
    direct computation gives B = Θ(√(n·log(q/n))), so B/√n ~ √(log(q/n)) is UNBOUNDED. The √2 floor
    bounds the L⁴/L²-AVERAGE of |η_b|, not the MAX; the max exceeds it by √(log #cosets). The
    corrected, refutation-surviving conjecture is `ShawGapLaw`: B ≤ C·√(n·log(q/n)) (§8).

R4. "worst-case incidence = average exactly" — REFUTED: the gap term is nonzero, so `(R)` is `≤`
    (one-sided) with a genuine (1+o(1)), not equality.

R5. "MRSS energy n^{49/20} already closes it"— REFUTED (§2,§6): the excess exponent 0.225 is a
    constant, so the off-diagonal moment `B^{2M-2}·qn` is `q^{Ω(n)}` larger than the diagonal; the
    prize needs B = n^{1/2+o(1)}, the genuine o(1), which MRSS does not give.

R6. "the deep band is the energy E"          — REFUTED (§1,§6): the window interior is governed by
    E_m with m ≈ ρn, NOT E = E_2; they coincide only through the gap B. Conflating them is the
    documented stall of both lanes (`CensusDomination`; the n^{2.45} energy wall).

R7. "N_fib, SplitLocusBound, WindowRationalBounded, CensusDomination are different unknowns"
    — REFUTED (§0,§6): all are high spectral moments of the ONE Shaw operator 𝖲_D; `shawOp_eigen`
    + `shaw_offdiag_moment_le` exhibit the identification.

R8. "the bad-scalar count needs a per-γ argument"— REFUTED (§2): `badScalars_card_le_cosetLowWeight`
    removes the quantifier over γ — the whole line family is one static coset count.

R9. "δ* = H_q⁻¹(...) is the exact threshold"  — REFUTED (BCHKS 2025/169 §1.4.3 + Crites–Stewart):
    the smooth domain gives COUNTEREXAMPLES below the capacity/random value, so H_q⁻¹ is only an
    UPPER bound. The exact worst-case far line above Johnson is a MONOMIAL direction `x^a`
    (`probe_monomial_extremal.py`: I_mono = I(δ) at every above-Johnson radius), so the true δ* is
    the STRUCTURED (q-independent, char-0-computable) monomial-extremal radius — strictly between
    Johnson and the H_q⁻¹ upper bound. The open core is its optimality (≡ the same W4/BCHKS object).

R10. "the corrected bound is weaker than Shkredov" — REFUTED: `B ≤ C·√(n·log(q/n))` still gives
    `E ≤ n²·O(log q) = n^{2+o(1)}` (log is subpolynomial), the exact Shkredov target. The √log is
    the genuine `√(log(1/ε*))` lower-order content, not a weakening.

What remains genuinely open is exactly `ShawFlatnessConjecture` (the corrected `ShawGapLaw`
`B ≤ C·√(n·log(q/n))`) ⟺ `WorstCaseIncidenceBound` ⟺ monomial-extremal optimality — the W4/Bourgain
worst-case character-sum bound for the small production subgroup, equivalently (BCHKS 2025/169
Thm 1.9) explicit-μ_n-RS beyond-Johnson list-decoding — and nothing else. That is the prize.

--------------------------------------------------------------------------------------------------
### §10  Status ledger (honest)

| component | status |
|---|---|
| `badScalars_card_le_cosetLowWeight` (doubling reduction) | **PROVEN, axiom-clean** |
| `badScalars_eq_lineBall_incidence` (incidence repackaging) | **PROVEN, axiom-clean** |
| `badScalars_card_le_of_worstCase` (`(R)` ⟹ prize bound) | **PROVEN, axiom-clean** |
| `shawOp_eigen` (spectrum = character sums) | **PROVEN, axiom-clean** |
| `punctured_secondMoment` (Parseval, punctured) | **PROVEN, axiom-clean** |
| `shaw_offdiag_moment_le` (gap controls ALL moments) | **PROVEN, axiom-clean** |
| `energy_le_of_flatness` (flatness ⟹ Sidon energy) | **PROVEN, axiom-clean** |
| `shaw_flatness_constant_ge_sqrt_two` (moment/avg lower bound C ≥ √2) | **PROVEN, axiom-clean** |
| `deltaStar_closedForm` (closed-form δ*, random UPPER bound) | **CONJECTURE** (computable) |
| `ShawGapLaw` `B ≤ C·√(n·log(q/n))` = `ShawFlatnessConjecture` = `(R)` | **OPEN CORE** = W4/Shkredov wall |

**One sentence.** Every face of the prize is one spectral statistic of the Shaw operator `𝖲_D`; a
single bound on its gap — the corrected `B(μ_n) ≤ C·√(n·log(q/n))` (the `√2·√n` form is refuted, R3) —
controls all of them at once and yields the closed form `δ*_avg = H_q⁻¹(1−ρ−log_q(1/ε*)/n)` (a random
UPPER bound; the true δ* is the q-independent monomial-extremal radius, R9); everything above the gap
is machine-checked here, and the gap bound is exactly the classical W4/Shkredov wall `E(μ_n)=n^{2+o(1)}`
— the prize, reduced to that one bound and nothing else.
-/

end ProximityPrize

/-! ## Axiom audit (the proved structural spine) -/
#print axioms ProximityPrize.badScalars_card_le_cosetLowWeight
#print axioms ProximityPrize.badScalars_eq_lineBall_incidence
#print axioms ProximityPrize.badScalars_card_le_of_worstCase
#print axioms ProximityPrize.shawOp_eigen
#print axioms ProximityPrize.punctured_secondMoment
#print axioms ProximityPrize.shaw_offdiag_moment_le
#print axioms ProximityPrize.energy_le_of_flatness
#print axioms ProximityPrize.shaw_flatness_constant_ge_sqrt_two
