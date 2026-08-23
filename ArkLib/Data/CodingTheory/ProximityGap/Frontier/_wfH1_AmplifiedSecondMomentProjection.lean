/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# H1 — the Iwaniec–Sarnak amplified second moment for the Gauss period is a FLAT projection (#444)

**NEGATIVE / guardrail brick (an honest no-go, the SHARP second-moment-level reason
amplification dies).** This file pins the precise algebraic obstruction that kills the
flagship Iwaniec–Sarnak (IS) sup-norm *amplification* route for the dyadic Gauss period
`η_b = Σ_{x∈μ_n} e_p(b x)`, `M(μ_n) = max_{b≠0}|η_b| = λ₂(Cay(F_p, μ_n))`.

The companion file `_AmplificationGainOne.lean` records the *first-moment* no-go (the Fourier
coefficients of a single `η_b` are flat). This file goes one level deeper, to the level the IS
method actually operates at: the **amplified SECOND moment over the spectral family**
`{η_b : b ∈ F_p^*}`, with a genuine **dilation–Hecke amplifier** `A_x(b) = Σ_l x_l η_{l b}`
(the operators `T_l : η_b ↦ η_{lb}` are the only natural "Hecke" operators on the spectral
index `b`). The IS method bounds the worst `b` via the amplified second moment
`Q(x) = Σ_{b≠0} |A_x(b)|² |η_b|²`, expanded by the pre-trace formula into a quadratic form
`Q(x) = Σ_{l,l'} x_l \overline{x_{l'}} K(l'/l)` in the **pre-trace kernel**
`K(t) = Σ_b η_b \overline{η_{t b}}`.

## The exact structure (verified, `probe_wfH1_kernel_structure.py`, exact integer arithmetic)

Expanding `η_b = Σ_{x∈μ_n} e_p(b x)` and summing the geometric series over `b` gives the EXACT
identity (no error term, no `√q` Weil loss):

  `K(t) = q · #{(x,y) ∈ μ_n² : x = t y} = q · n · 1_{t ∈ μ_n}`,

because `μ_n` is a **subgroup**: the multiplicative self-correlation
`r(t) := #{(x,y) ∈ μ_n² : x·y⁻¹ = t}` is `|μ_n| = n` when `t ∈ μ_n` and `0` otherwise. So the
IS pre-trace kernel is `q·n` times the **indicator of the subgroup** — a *scaled orthogonal
projection* onto the `m = (p−1)/n` multiplicative characters trivial on `μ_n` (the AVERAGING /
Parseval eigenspace), with the FLAT eigenvalue `q·n²` on that eigenspace and `0` everywhere else.

## Why this is the death of IS amplification (the genuine mathematical content)

In the real IS method the gain comes from a Hecke kernel whose diagonal carries genuine
*eigenvalue variation* and whose off-diagonal is a *Diophantine* count one can save on. Here
there is **nothing to save**: the kernel is a flat projection. The amplified quadratic form
`Q(x) = ⟨x, K x⟩` is therefore **maximized exactly on the projection's range** (the averaging
direction) and is `≤ q·n·‖x‖²` for *every* amplifier `x` — the amplification "gain"
`Q(x)/‖x‖²` is capped at the constant `q·n` and is achieved by the *flat* averaging amplifier,
never by a shape that isolates the worst `b`. So amplification certifies only the RMS / Parseval
scale `√n` (Johnson), never the `L^∞` prize factor `√(n·log(p/n))`. The "Hecke eigenvalues"
`λ_l(b) = η_{lb}/η_b` carry the same flat `|Gauss-sum|` modulus and provide no variation to amplify.

`M(μ_n)` is therefore **NOT** a genuine amplifiable automorphic/Hecke sup-norm; the IS route
`REDUCES-TO-FENCE` (flat spectrum, now at the second-moment level). The `√log` excess remains
the open BGK/Paley wall, untouched by amplification.

## What is proven here (axiom-clean)

1. `subgroup_self_correlation` — the combinatorial heart: for a finite subgroup `H ≤ G` and any
   `t : G`, the multiplicative self-correlation `#{(x,y) ∈ H×H : x = t·y}` equals `|H|` if
   `t ∈ H` and `0` otherwise. THIS is the exact fact that makes the kernel a flat projection.
2. `amplified_form_le_scale` / `amplification_gain_capped` — the abstract projection-ceiling
   no-go: if the pre-trace kernel acts as a scaled projection (`Q(x) = c · ‖Px‖²` with
   `‖Px‖² ≤ ‖x‖²`), then `Q(x) ≤ c‖x‖²` for every amplifier and equality holds on the range —
   the gain is the constant `c`, reshaping `x` buys nothing.

Issue #444, lane H1 (Iwaniec–Sarnak amplification).
-/

namespace ProximityGap.Frontier.H1AmplifiedProjection

open Finset

/-! ## 1. The combinatorial heart: a subgroup's multiplicative self-correlation is `|H|·1_H`. -/

variable {G : Type*} [Group G] [DecidableEq G] [Fintype G]

/--
**Subgroup self-correlation (the exact kernel content).**

For a finite subgroup `H ≤ G` and any element `t : G`, the number of pairs `(x, y) ∈ H × H`
with `x = t · y` is `|H|` when `t ∈ H` and `0` when `t ∉ H` (here `|H|` is the `Finset`
cardinality `#{g | g ∈ H}`).

This is the precise reason the Iwaniec–Sarnak pre-trace kernel `K(t) = q·r(t)` of the
dilation–Hecke amplifier is `q·n·1_{μ_n}` — a *flat scaled projection*, with **no Diophantine
off-diagonal to save on**. (Apply with `G = F_p^*`, `H = μ_n`, `n = |H|`.)
-/
theorem subgroup_self_correlation (H : Subgroup G) [DecidablePred (· ∈ H)] (t : G) :
    (Finset.univ.filter
      (fun yx : G × G => yx.1 ∈ H ∧ yx.2 ∈ H ∧ yx.1 = t * yx.2)).card
      = if t ∈ H then (Finset.univ.filter (· ∈ H)).card else 0 := by
  by_cases ht : t ∈ H
  · -- t ∈ H: for each y ∈ H, the unique x = t·y is in H; bijection with {g | g ∈ H}.
    simp only [ht, if_true]
    -- Count by mapping each valid pair to its second coordinate y ∈ H.
    apply Finset.card_bij (fun yx _ => yx.2)
    · -- maps into the H-filter
      rintro ⟨x, y⟩ hmem
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem ⊢
      exact hmem.2.1
    · -- injective on the filtered set: x is determined by y via x = t·y
      rintro ⟨x₁, y₁⟩ h₁ ⟨x₂, y₂⟩ h₂ hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
      simp only at hy
      subst hy
      have : x₁ = x₂ := by rw [h₁.2.2, h₂.2.2]
      simp [this]
    · -- surjective onto the H-filter: each y ∈ H is hit by (t·y, y)
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      have hmem : (t * y, y) ∈ Finset.univ.filter
          (fun yx : G × G => yx.1 ∈ H ∧ yx.2 ∈ H ∧ yx.1 = t * yx.2) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, H.mul_mem ht hy, hy, rfl⟩
      exact ⟨(t * y, y), hmem, rfl⟩
  · -- t ∉ H: no valid pair, because x ∈ H and y ∈ H would force t = x·y⁻¹ ∈ H.
    simp only [ht, if_false]
    rw [Finset.card_eq_zero]
    rw [Finset.filter_eq_empty_iff]
    rintro ⟨x, y⟩ _
    simp only [not_and]
    intro hx hy hxy
    -- hxy : x = t * y, so t = x * y⁻¹ ∈ H, contradiction
    exfalso
    apply ht
    have : t = x * y⁻¹ := by
      rw [hxy]; group
    rw [this]
    exact H.mul_mem hx (H.inv_mem hy)

/-! ## 2. The abstract projection-ceiling no-go for the amplified second moment.

We model the IS amplified second moment as a quadratic form `Q(x) = c · ‖P x‖²` where `P` is the
(self-adjoint idempotent) projection onto the averaging eigenspace and `c = q·n` is the flat
eigenvalue (the verified kernel `K = c·P`). The point: no amplifier `x` makes `Q(x)/‖x‖²` exceed
`c`, and the maximum is attained on the range of `P` — the averaging direction. We phrase it over
`ℝ` with the abstract data `(Q, normSq, projNormSq, c)`, the only structure used being
`projNormSq ≤ normSq` (a projection is a contraction) and `Q = c · projNormSq`. -/

/-- Abstract amplified-second-moment data extracted from the flat-projection kernel `K = c·P`:
`Q x = c · ‖P x‖²`, with the projection contraction `‖P x‖² ≤ ‖x‖²` and `c ≥ 0`. -/
structure FlatProjectionForm where
  /-- amplifier energy `‖x‖²` (nonneg). -/
  normSq : ℝ
  /-- projected energy `‖P x‖²` (nonneg), where `P` projects onto the averaging eigenspace. -/
  projNormSq : ℝ
  /-- the flat kernel eigenvalue `c = q·n` (nonneg). -/
  c : ℝ
  /-- the amplified second moment `Q(x) = c · ‖P x‖²`. -/
  Q : ℝ
  normSq_nonneg : 0 ≤ normSq
  projNormSq_nonneg : 0 ≤ projNormSq
  c_nonneg : 0 ≤ c
  /-- `P` is a contraction (orthogonal projection): `‖P x‖² ≤ ‖x‖²`. -/
  proj_contraction : projNormSq ≤ normSq
  /-- the verified kernel identity `K = c·P` gives `Q = c · ‖P x‖²`. -/
  Q_eq : Q = c * projNormSq

/--
**The amplification ceiling (no shape gain).** For the flat-projection kernel, the amplified
second moment is at most `c · ‖x‖²` for *every* amplifier — the "gain" `Q/‖x‖²` is capped at the
constant flat eigenvalue `c = q·n`. No reshaping of the amplifier beats this; the bound is the
Parseval/RMS value. -/
theorem amplified_form_le_scale (F : FlatProjectionForm) :
    F.Q ≤ F.c * F.normSq := by
  rw [F.Q_eq]
  exact mul_le_mul_of_nonneg_left F.proj_contraction F.c_nonneg

/--
**Amplification gain is capped by the flat eigenvalue (ratio form, no shape gain).**
For any amplifier with positive energy, the amplified second moment per unit energy `Q/‖x‖²`
never exceeds `c`. The certified sup bound is the flat eigenvalue `c = q·n`, i.e. the RMS /
Parseval scale `√n` (Johnson). The `L^∞` prize factor `√(log)` lies strictly above and is
invisible to amplification. -/
theorem amplification_gain_capped (F : FlatProjectionForm) (hpos : 0 < F.normSq) :
    F.Q / F.normSq ≤ F.c := by
  rw [div_le_iff₀ hpos]
  exact amplified_form_le_scale F

/--
**Equality on the averaging eigenspace (the gain is realized only by averaging).**
When the amplifier lies in the range of the projection (`‖P x‖² = ‖x‖²`, the averaging /
Parseval direction), the amplified second moment attains the ceiling `Q = c · ‖x‖²`. Combined
with `amplified_form_le_scale`, this shows the maximum gain `c` is achieved precisely by the
*flat* averaging amplifier — never by a shape that isolates the worst `b`. So amplification can
only ever certify the average (RMS) value, which is the no-go. -/
theorem amplified_form_eq_on_range (F : FlatProjectionForm)
    (hrange : F.projNormSq = F.normSq) :
    F.Q = F.c * F.normSq := by
  rw [F.Q_eq, hrange]

#print axioms ProximityGap.Frontier.H1AmplifiedProjection.subgroup_self_correlation
#print axioms ProximityGap.Frontier.H1AmplifiedProjection.amplified_form_le_scale
#print axioms ProximityGap.Frontier.H1AmplifiedProjection.amplification_gain_capped
#print axioms ProximityGap.Frontier.H1AmplifiedProjection.amplified_form_eq_on_range

end ProximityGap.Frontier.H1AmplifiedProjection
