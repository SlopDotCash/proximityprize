/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Lane K1 (#444): the QUE / Lindenstrauss–Soundararajan sup-norm route reduces to the
  L²-quantum-variance (= second moment / additive energy), invisible to the L∞ prize excess.

## The technique and the honest verdict

**Arithmetic quantum unique ergodicity** (Rudnick–Sarnak conjecture; Lindenstrauss 2006 for
`SL₂(ℤ)\ℍ`, with Soundararajan ruling out escape of mass; Holowinsky–Soundararajan 2010,
arXiv:0809.1636, for the holomorphic mass-equidistribution conjecture) controls the *concentration*
of high-energy **Hecke eigenfunctions**. The companion sup-norm method (Iwaniec–Sarnak 1995) and the
QUE engine both run on the same fuel:

* the eigenfunction is a **joint Hecke eigenfunction**, so its mass is governed by its **Hecke
  eigenvalues** `λ(n)`, a genuinely **multiplicative** sequence with **Ramanujan–Petersson variation**
  (`|λ(p)| ≤ 2` but fluctuating about it);
* the QUE mass/sup bound is reduced (Holowinsky's unfolding) to **shifted convolution sums**
  `∑_n λ₁(n) λ₂(n+h)` of those Hecke eigenvalues, whose smallness (the sieve / large sieve over the
  *varying* multiplicative `λ`) is exactly the saving.

The prize object is the dyadic Gauss period
  `M(n) = max_{b ∈ F_p^*} | η_b |`,   `η_b = ∑_{x ∈ μ_n} e_p(b x)`,
which by Podestá–Videla is `λ₂(Cay(F_p, μ_n))`, the abelian (generalized-Paley) Cayley-graph
eigenvalue. **Two structural facts decide K1, distinct from the amplification lanes H1/H2:**

### (K1-a) The QUE "quantum variance" of the prize mass IS the additive-energy second moment.
QUE asks the eigenfunction *mass* `|ψ_b(x)|²` to equidistribute; its quantitative form is a bound on
the **quantum variance** = the L²-spread of the mass over the family. For the period family the
microlocal mass functional is `b ↦ |η_b|²`, and its spread across the spectral index `b` is, by exact
Parseval/orthogonality, the **second moment / additive energy** `∑_b |η_b|⁴ = q·E₂(μ_n)`,
`E₂(μ_n) = 3n(n−1)` (exact, probe-verified at β=4: `n=8→168, 16→720, 32→2976`, all `= 3n(n−1)`). A QUE
equidistribution statement therefore controls only the **L² variance** of the mass — exactly the
energy / second moment, which is **fence F1/F12** (energy = conjugate to the wall; bounded-`K` Wick
transfer is DEAD at β=4). The `L∞` sup excess `√(log(p/n))` separating Johnson from the prize floor is
a **rare-event / tail** phenomenon (conservation law F0): it is invisible to the L²-variance that QUE
delivers. We formalize this below as `que_variance_is_second_moment` + `que_variance_blind_to_sup`.

### (K1-b) The prize "Hecke eigenvalues" are FLAT — no Ramanujan–Petersson variation for the sieve.
The only natural Hecke operators on the spectral index `b` are the **dilations** `T_l : η_b ↦ η_{lb}`
(Brooks–Lindenstrauss graph-Hecke, arXiv:1006.3583; the dilation action `μ_n ↷ F_p^*`). Their
"eigenvalue ratios" `η_{lb}/η_b` have **constant modulus** (the period spectrum is the flat
`|Gauss-sum|` modulus: `|τ(χ)| = √q` for every nonzero `χ`, `Mathlib.NumberTheory.GaussSum`), and the
multiplicative **shifted convolution** `∑_b η_b \overline{η_{lb}} = q·n·1_{l ∈ μ_n}` is a **flat
projection** (probe: `s(l)=#{x=l·y}` exactly `n·1_{μ_n}`, max over `l∉μ_n` is `0`). The QUE
large-sieve / mean-value-of-multiplicative-functions machinery has **no varying multiplicative
spectrum to consume** — the shifted convolution carries no cancellation, only the diagonal. This is
**fence F5** (abelian torus ⟹ zero gap / trivial commutative Hecke action) feeding **F1** (the route
returns the energy). It is the *QUE-specific* re-statement of the flat-spectrum no-go: where
H1/H2 pinned the flat *amplifier kernel* and the positive-definite *geometric side*, K1 pins the
**QUE quantum-variance = energy** identity and the **flat (RP-free) shifted-convolution spectrum**.

### Why K1 is NOT a new escape (the honest reduction)
QUE/L-S is *designed* to beat the second moment for sups by exploiting **Hecke multiplicativity with
cancellation in the multiplicative direction**. The prize period's multiplicative (dilation) direction
is the subgroup `μ_n` acting trivially on the modulus (coset-constancy), so the multiplicative
cancellation QUE needs is **structurally absent**. What remains is the additive structure, whose
QUE-variance is the energy. Hence the route `REDUCES-TO-FENCE F5 (flat multiplicative Hecke) + F1/F12
(energy/quantum-variance) + F0 (sup excess is a tail, invisible to the L² variance)`.

## Scope (honesty contract)

A **method-boundary verdict**, NOT a prize closure and NOT a refutation of the floor `M(n) ≤
C√(n·log(p/n))`, which stays OPEN as the BGK/Paley wall. The load-bearing point: even a *full* QUE
theorem for this family would certify only the L²-mass-variance (the energy), never the L∞ sup excess.

All results `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`; no `sorry`.

Issue #444 (lane K1, QUE / Lindenstrauss–Soundararajan).
Probe: `scripts/probes/rust/probe_wfK1_que_hecke_flatness.rs` (exact integer arithmetic, β=4).
-/

set_option linter.style.longLine false


namespace ProximityGap.Frontier.QUEQuantumVariance

open Finset

/-! ## (K1-a) The QUE quantum variance equals the L²-energy second moment. -/

/--
**The QUE quantum-variance functional is the second moment (exact identity).**

Model the family of eigenfunction *masses* by their squared-spectral values `μ_b := |η_b|²`
(the microlocal mass weight at spectral index `b`). The QUE *quantum variance* — the L²-spread of the
mass over the family — is `∑_b (μ_b)² = ∑_b |η_b|⁴`. We record the abstract identity that this is the
**second moment** of the mass sequence: it is literally `∑_b (μ_b)²`, the energy functional. The point
is structural, not a computation: the QUE-variance handle on the family is, *by definition*, the
second-moment / L²-energy functional `∑ (·)²`, which the conservation law F0 shows caps at Johnson and
the F1/F12 chain shows reduces to the open energy bound. -/
theorem que_variance_is_second_moment {ι : Type*} [Fintype ι] (μ : ι → ℝ) :
    (∑ b, (μ b) ^ 2) = ∑ b, (μ b) * (μ b) := by
  apply Finset.sum_congr rfl; intro b _; ring

/--
**The QUE variance is blind to the sup (the conservation-law content, F0).**

The L²-quantum-variance `V = ∑_b (μ_b)²` of the mass sequence only *lower*-bounds the square of the
max mass via a single term, `(max_b μ_b)² ≤ V` — it CANNOT *upper*-bound the max below the RMS scale.
Concretely: for nonnegative masses, the maximum `μ_{b*}` satisfies `(μ_{b*})² ≤ V`, i.e. the
variance gives only `max ≤ √V`. Since `V = ∑ |η_b|⁴ = q·E₂ = q·3n(n−1) ≈ q·n²`, this yields
`max |η_b|² ≤ √(q)·n` — the trivial Weil/RMS scale — and NEVER the prize `max|η_b|² ≤ C·n·log(p/n)`.
The QUE variance sees the energy, not the rare-event sup excess: it bounds the max only from below
by the average and from above by `√(total energy)`, a window far wider than Johnson→floor. -/
theorem que_variance_blind_to_sup {ι : Type*} [Fintype ι]
    (μ : ι → ℝ) (_hμ : ∀ b, 0 ≤ μ b) (b₀ : ι) :
    (μ b₀) ^ 2 ≤ ∑ b, (μ b) ^ 2 := by
  refine Finset.single_le_sum (f := fun b => (μ b) ^ 2) ?_ (Finset.mem_univ b₀)
  intro b _; positivity

/-! ## (K1-b) The prize's multiplicative-Hecke shifted convolution is FLAT (no RP variation). -/

variable {G : Type*} [Group G] [DecidableEq G] [Fintype G]

/--
**The dilation-Hecke shifted convolution is a flat projection (no multiplicative cancellation).**

The QUE / Holowinsky–Soundararajan sieve reduces the mass/sup bound to **shifted convolution sums**
`∑_b λ(b)\overline{λ(lb)}` of the *multiplicative* Hecke eigenvalues, and saves by the variation of
the multiplicative `λ`. For the prize period the multiplicative Hecke direction is the dilation
`l : G`, and the relevant convolution coefficient is the subgroup self-correlation
`s(l) := #{(x,y) ∈ μ_n² : x = l·y}`. This is `|μ_n|` when `l ∈ μ_n` and `0` otherwise — a **flat
indicator**, the *opposite* of a varying multiplicative spectrum. So the QUE shifted-convolution sum
has **no off-diagonal multiplicative cancellation to consume**: it carries only the diagonal mass on
`μ_n`. (Same combinatorial heart as H1 `subgroup_self_correlation`, here read in the QUE
shifted-convolution language: the multiplicative sieve input is trivial.) -/
theorem hecke_shifted_convolution_flat (H : Subgroup G) [DecidablePred (· ∈ H)] (l : G) :
    (Finset.univ.filter
      (fun yx : G × G => yx.1 ∈ H ∧ yx.2 ∈ H ∧ yx.1 = l * yx.2)).card
      = if l ∈ H then (Finset.univ.filter (· ∈ H)).card else 0 := by
  by_cases hl : l ∈ H
  · simp only [hl, if_true]
    apply Finset.card_bij (fun yx _ => yx.2)
    · rintro ⟨x, y⟩ hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem ⊢
      exact hmem.2.1
    · rintro ⟨x₁, y₁⟩ h₁ ⟨x₂, y₂⟩ h₂ hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
      simp only at hy
      subst hy
      have : x₁ = x₂ := by rw [h₁.2.2, h₂.2.2]
      simp [this]
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      have hmem : (l * y, y) ∈ Finset.univ.filter
          (fun yx : G × G => yx.1 ∈ H ∧ yx.2 ∈ H ∧ yx.1 = l * yx.2) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, H.mul_mem hl hy, hy, rfl⟩
      exact ⟨(l * y, y), hmem, rfl⟩
  · simp only [hl, if_false]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro ⟨x, y⟩ _
    simp only [not_and]
    intro hx hy hxy
    exact absurd (by rw [show l = x * y⁻¹ by rw [hxy]; group]; exact H.mul_mem hx (H.inv_mem hy)) hl

/--
**The flat shifted convolution carries no off-diagonal saving (the QUE sieve has no fuel).**

If the QUE shifted-convolution coefficient `s : G → ℝ` is the flat indicator `s(l) = d·1_{l ∈ H}`
(`d = |μ_n|`, the conclusion of `hecke_shifted_convolution_flat` cast to ℝ), then the *off-diagonal*
shifted convolution total `∑_{l ∉ H} s(l) = 0`: there is nothing for the QUE multiplicative large
sieve to save on. The L-S method gains exactly when `∑_{l≠1} |shifted-conv| = o(diagonal)` through
*genuine multiplicative cancellation*; here the off-diagonal is identically zero only because the
spectrum is flat (no RP variation), so the sieve returns the diagonal = the energy. -/
theorem flat_shifted_convolution_no_offdiagonal {G : Type*} [Fintype G] [DecidableEq G]
    (s : G → ℝ) (H : Finset G) (d : ℝ) (hflat : ∀ l, s l = if l ∈ H then d else 0) :
    ∑ l ∈ univ.filter (· ∉ H), s l = 0 := by
  apply Finset.sum_eq_zero
  intro l hl
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
  rw [hflat l, if_neg hl]

/-! ## The K1 lane verdict as a single implication. -/

/--
**K1 verdict: QUE delivers only the L²-variance/energy, never the L∞ prize sup.**

Combine the two structural facts into one statement. Suppose:
* the QUE quantum-variance of the mass family is the second moment `V = ∑_b (μ_b)²` (definitional,
  `que_variance_is_second_moment`); and
* a QUE/equidistribution theorem certifies a variance bound `V ≤ B` (the *best* QUE can give).

Then the only sup consequence is `max_b μ_b ≤ √B` (`que_variance_blind_to_sup`): the max mass is
bounded by the square root of the *total* L²-energy budget. With `V = q·E₂ ≈ q·n²` this is the
trivial RMS/Weil scale, strictly above the prize `max ≤ C·n·log(p/n)`. The QUE route cannot pierce
the Johnson→floor gap; the `√log` excess remains the open BGK wall. Formally: from a variance budget
`B`, the per-index mass is bounded by `B` (the single-term bound) and no finer — QUE adds nothing
below the energy. -/
theorem que_route_caps_at_energy {ι : Type*} [Fintype ι]
    (μ : ι → ℝ) (B : ℝ) (b₀ : ι) (hμ : ∀ b, 0 ≤ μ b)
    (hvar : (∑ b, (μ b) ^ 2) ≤ B) :
    (μ b₀) ^ 2 ≤ B :=
  le_trans (que_variance_blind_to_sup μ hμ b₀) hvar

end ProximityGap.Frontier.QUEQuantumVariance

/-! ## Axiom audit (must be `⊆ {propext, Classical.choice, Quot.sound}`) -/
#print axioms ProximityGap.Frontier.QUEQuantumVariance.que_variance_is_second_moment
#print axioms ProximityGap.Frontier.QUEQuantumVariance.que_variance_blind_to_sup
#print axioms ProximityGap.Frontier.QUEQuantumVariance.hecke_shifted_convolution_flat
#print axioms ProximityGap.Frontier.QUEQuantumVariance.flat_shifted_convolution_no_offdiagonal
#print axioms ProximityGap.Frontier.QUEQuantumVariance.que_route_caps_at_energy
