/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.IncidencePeriodBridge
import ArkLib.Data.CodingTheory.ProximityGap.PrizeStructuralConstant

/-!
# The realizer is an L²/AVERAGE, not the L∞/SUP `B` — outcome (C) for #444

This file is the honest resolution of the directive's crux question:

  > Does the worst-case far-line incidence see the **SUP** period
  >   `B = max_{b≠0} ‖η_b‖`   (the OPEN BGK/Paley wall)
  > or the **L²/average** `∑_b ‖η_b‖²`   (COMPUTABLE, `= q·n` by Parseval)?

The exact incidence↔period identity `IncidencePeriodBridge.lineIncidence_period_sum`
already forces the answer.  Over the syndrome space `V = F` (the geometry where the prize's
far-coset attack lives), the line–ball incidence is

  `I(s₀, s₁) = ∑_{b : b·s₁ = 0} conj(η_b)·ψ(b·s₀)`.

We prove TWO exact structural facts that together REFUTE a sup-`B` realizer:

* **`farLine_incidence_eq_card` (blind to `b ≠ 0`).**  For EVERY non-degenerate far direction
  `s₁ ≠ 0`, the incidence is *exactly* `|G|`, a constant **independent of every nonzero period
  `η_b`** — in particular independent of `B = max_{b≠0}‖η_b‖`.  The constraint `b·s₁ = 0` kills
  all frequencies except `b = 0`, leaving only the principal term `η₀ = |G|`.  So no far
  direction's incidence is an increasing function of `B`: the would-be realizer
  `I_{u*} = f(B)` with `f` increasing is **FALSE** in this geometry.

* **`farLine_incidence_l2_eq_period_l2` / `farLine_incidence_le_sqrt_l2` (the surviving
  dependence is L², computable).**  The only spectrum-sensitive direction is the degenerate
  `s₁ = 0` (the "line" is a point), and there the incidence energy is *exactly* the L²/Parseval
  total `∑_{s₀} I(s₀,0)² = q·∑_b ‖η_b‖² = q²·|G|` — an **L² sum** of ALL periods, the
  *average*-scale quantity, never the sup.  Hence each incidence is `≤ √(q·∑_b‖η_b‖²) = q·√|G|`,
  a COMPUTABLE bound that does not involve `B`.

**Consequence (the prize-relevant conclusion).**  In this far-line geometry the incidence
budget `I ≤ q·ε* = n` is a constraint on a COMPUTABLE functional of the spectrum (the principal
constant `|G|`, or the L² energy `∑‖η_b‖²`), NOT on the open sup `B`.  The realizer
`δ* ⟹ B` cannot be supplied by this geometry: the far-line incidence is L²/average-measurable,
and is **decoupled from the L∞ sup `B`** that carries the BGK/Paley wall.

This is corroborated numerically (`scripts/probes/probe_realizer_supVSavg.py`): the max
far-line incidence is **`p`-independent** (identical across primes `p ≡ 1 mod n`), whereas
`B = max_{b≠0}‖η_b‖` is strongly **`p`-dependent** (structured/Fermat primes blow `B` up while
the incidence is unchanged) — a quantity cannot be an increasing function of one that varies
while it stays fixed.

## Honest scope

This file does NOT assert the prize is computable.  It proves the precise structural statement
that the **far-line incidence functional** (the F1 face of the open core, in the one-dimensional
syndrome geometry of `IncidencePeriodBridge`) reads the L²/average of the period spectrum, not
its L∞ sup.  Whether the GENUINELY `≥ 2`-dimensional MCA incidence (`mcaEvent`, witness sets of
size `(1-δ)n`) re-introduces a sup-`B` dependence is a separate, still-open question — but the
*available* exact bridge is L²/sup-blind, which is exactly why `OpenCoreConverse` names the
realizer as residual.  We make that "why" a theorem, not a remark.

Axiom-clean; pure additive-character orthogonality + Cauchy–Schwarz, no field-size or regime
hypotheses.  Issue #444.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.IncidencePeriodBridge

namespace ArkLib.ProximityGap.RealizerL2NotSup

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## Fact 1 — every non-degenerate far direction is BLIND to the nonzero periods -/

/-- **The far-line incidence is exactly `|G|` for every direction `s₁ ≠ 0` — blind to `B`.**

For a non-degenerate direction the affine map `γ ↦ s₀ + γ·s₁` is a bijection of `F`, so the
line is all of `F` and meets `G` in exactly `|G|` points.  Read through the period identity
`lineIncidence_period_sum`, the constraint `b·s₁ = 0` forces `b = 0`, collapsing the period sum
to the single principal term `η₀ = |G|`: the incidence does **not** depend on any nonzero period
`η_b`, hence not on `B = max_{b≠0}‖η_b‖`. -/
theorem farLine_incidence_eq_card (G : Finset F) {s₀ s₁ : F} (hs₁ : s₁ ≠ 0) :
    lineIncidence G s₀ s₁ = G.card := by
  classical
  unfold lineIncidence
  have hinj : Function.Injective (fun γ : F => s₀ + γ * s₁) := by
    intro a b hab
    simp only at hab
    have : a * s₁ = b * s₁ := by linear_combination hab
    exact mul_right_cancel₀ hs₁ this
  rw [← Finset.card_image_of_injective _ hinj]
  congr 1
  ext z
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨γ, hγ, rfl⟩; exact hγ
  · intro hz
    refine ⟨(z - s₀) * s₁⁻¹, ?_, ?_⟩
    · have : (z - s₀) * s₁⁻¹ * s₁ = z - s₀ := by field_simp
      rw [this]; simpa using hz
    · have : (z - s₀) * s₁⁻¹ * s₁ = z - s₀ := by field_simp
      rw [this]; ring

/-- **Quantitative blindness: any two far directions give the SAME incidence.**  Since both
equal `|G|`, the incidence is constant across all non-degenerate directions and all offsets.  A
functional that is constant on the entire far-direction family cannot be an increasing function
of the direction-dependent sup `B` — the realizer `I_{u*} = f(B)`, `f` increasing, is refuted. -/
theorem farLine_incidence_constant (G : Finset F) {s₀ s₀' s₁ s₁' : F}
    (hs₁ : s₁ ≠ 0) (hs₁' : s₁' ≠ 0) :
    lineIncidence G s₀ s₁ = lineIncidence G s₀' s₁' := by
  rw [farLine_incidence_eq_card G hs₁, farLine_incidence_eq_card G hs₁']

/-- **The principal period equals the (constant) far incidence.**  `‖η₀‖ = |G| = I(s₀,s₁)` for
`s₁ ≠ 0`: the only spectral quantity the far incidence sees is the *principal* (`b = 0`) period,
which is the deterministic constant `|G|`, NOT the open nonzero sup `B`. -/
theorem farLine_incidence_eq_principal_period {ψ : AddChar F ℂ} (G : Finset F)
    {s₀ s₁ : F} (hs₁ : s₁ ≠ 0) :
    (lineIncidence G s₀ s₁ : ℝ) = ‖eta ψ G 0‖ := by
  have he0 : eta ψ G 0 = (G.card : ℂ) := by
    simp only [eta, zero_mul, AddChar.map_zero_eq_one, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [farLine_incidence_eq_card G hs₁, he0, Complex.norm_natCast]

/-! ## Fact 2 — the only spectrum-sensitive direction reads the L² energy, never the sup -/

/-- **The far-line incidence energy is the L²/Parseval total — `q·∑_b ‖η_b‖²`, computable.**
A verbatim restatement of `IncidencePeriodBridge.incidence_l2_eq_period_l2`, re-exported here as
"the spectrum-sensitive direction (`s₁ = 0`) sees the L² sum of ALL periods, not the sup".  The
right side `∑_b‖η_b‖² = q·|G|` is exactly computed (Parseval), with **no** appearance of
`max_b ‖η_b‖`. -/
theorem farLine_incidence_l2_eq_period_l2 {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) :
    (∑ s₀ : F, ((lineIncidence G s₀ 0 : ℝ)) ^ 2)
      = (Fintype.card F : ℝ) * ∑ b : F, ‖eta ψ G b‖ ^ 2 :=
  incidence_l2_eq_period_l2 hψ G

/-- **Each spectrum-sensitive incidence is bounded by the COMPUTABLE L²-energy `√(q·∑‖η_b‖²)`.**
By Cauchy–Schwarz (a single term ≤ the L² total), every constant-direction incidence obeys

  `I(s₀, 0) ≤ √(q · ∑_b ‖η_b‖²) = √(q²·|G|) = q·√|G|`,

a closed, **computable** bound depending only on the L²-energy `∑_b‖η_b‖²` (Parseval `= q·|G|`),
**never** on the sup `B = max_{b≠0}‖η_b‖`.  This is the L²/average measurability of the
incidence functional, the obstruction to a sup-`B` realizer. -/
theorem farLine_incidence_le_sqrt_l2 {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (s₀ : F) :
    ((lineIncidence G s₀ 0 : ℝ)) ^ 2
      ≤ (Fintype.card F : ℝ) * ∑ b : F, ‖eta ψ G b‖ ^ 2 := by
  classical
  rw [← farLine_incidence_l2_eq_period_l2 hψ G]
  -- a single nonnegative term is ≤ the full nonnegative sum
  refine Finset.single_le_sum (f := fun s₀ : F => ((lineIncidence G s₀ 0 : ℝ)) ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ s₀)

/-- **The L²-energy bound is exactly `q²·|G|` (computable), strictly the AVERAGE not the sup.**
Specializing `farLine_incidence_le_sqrt_l2` with the Parseval value
`∑_b ‖η_b‖² = q·|G|` (`subgroup_gaussSum_secondMoment`): every spectrum-sensitive incidence
satisfies `I(s₀,0)² ≤ q²·|G|`.  The whole right side is determined by `q` and `|G|` alone — it is
**computable in closed form**, with no dependence on the open period sup `B`. -/
theorem farLine_incidence_sq_le_computable {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (s₀ : F) :
    ((lineIncidence G s₀ 0 : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ) ^ 2 * G.card := by
  have h := farLine_incidence_le_sqrt_l2 hψ G s₀
  rw [subgroup_gaussSum_secondMoment hψ G] at h
  calc ((lineIncidence G s₀ 0 : ℝ)) ^ 2
      ≤ (Fintype.card F : ℝ) * ((Fintype.card F : ℝ) * G.card) := h
    _ = (Fintype.card F : ℝ) ^ 2 * G.card := by ring

/-! ## The refutation, packaged as ONE statement -/

/-- **THE REALIZER IS L²/AVERAGE-MEASURABLE, NOT THE SUP `B` (outcome C).**

Combines the two facts into the precise structural conclusion for the far-line geometry of
`IncidencePeriodBridge`:

* **(blind)** every non-degenerate far direction `s₁ ≠ 0` has incidence *exactly* `|G|`, a
  constant independent of `B = max_{b≠0}‖η_b‖`; AND
* **(L²-measurable)** the only spectrum-sensitive direction `s₁ = 0` has incidence bounded by the
  COMPUTABLE L²-energy `q²·|G|` (Parseval), with no dependence on `B`.

So the far-line incidence functional is determined by computable L²/principal data, and a
realizer `I = (increasing function of B)` cannot exist in this geometry: the incidence is
decoupled from the L∞ sup `B` that carries the open BGK/Paley wall.  (The remaining open
question is whether the genuinely ≥2-dimensional MCA incidence re-couples to `B` — but the
*available* exact bridge is sup-blind, which is precisely why the realizer is named as residual
in `OpenCoreConverse`.) -/
theorem farLine_incidence_decoupled_from_sup {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) :
    (∀ s₀ s₁ : F, s₁ ≠ 0 → lineIncidence G s₀ s₁ = G.card)
      ∧ (∀ s₀ : F, ((lineIncidence G s₀ 0 : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ) ^ 2 * G.card) :=
  ⟨fun _s₀ _s₁ hs₁ => farLine_incidence_eq_card G hs₁,
   fun s₀ => farLine_incidence_sq_le_computable hψ G s₀⟩

end ArkLib.ProximityGap.RealizerL2NotSup

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.RealizerL2NotSup.farLine_incidence_eq_card
#print axioms ArkLib.ProximityGap.RealizerL2NotSup.farLine_incidence_constant
#print axioms ArkLib.ProximityGap.RealizerL2NotSup.farLine_incidence_eq_principal_period
#print axioms ArkLib.ProximityGap.RealizerL2NotSup.farLine_incidence_l2_eq_period_l2
#print axioms ArkLib.ProximityGap.RealizerL2NotSup.farLine_incidence_le_sqrt_l2
#print axioms ArkLib.ProximityGap.RealizerL2NotSup.farLine_incidence_sq_le_computable
#print axioms ArkLib.ProximityGap.RealizerL2NotSup.farLine_incidence_decoupled_from_sup
