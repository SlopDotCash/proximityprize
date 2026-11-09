/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAEquivariance

/-!
# A5 — the Lean equivariance pin at the `n = 12` instance `RS[F₁₃, ⟨2⟩, 6]` (#334)

`MCAEquivariance.lean` discharges the *engine* of the equivariance pin: the code-generic
RS domain-rotation lemma `mcaEvent_rs_rotate` (precomposition with a coordinate permutation
`σ` that multiplicatively scales the evaluation domain, `domain (σ i) = g · domain i` with
`g ≠ 0`, preserves the MCA event at every radius/stack/scalar), and the orbit-sup reduction
`epsMCA_eq_iSup_subtype_of_reps`. The R1 instance there is the `n = 4` code `RS[F₅, ⟨2⟩, 2]`.

This file pins the **`n = 12` profile** named in the A5 ledger: `RS[F₁₃, ⟨2⟩, 6]`, the rate-½
Reed–Solomon code on the full multiplicative group `F₁₃ˣ = ⟨2⟩` (`2` is a primitive root mod
`13`, so its powers enumerate all twelve nonzero points). The exact-bad-γ probe
(`probe_epsmca_orbit_exact_n12.py`: δ=0→1, δ=0.083→2, δ=0.167→3, δ=0.25→12, δ≥1/3→13)
reduces over the orbits of exactly this multiplicative rotation; this file makes the
rotation's MCA-invariance a machine-checked theorem at that instance, so the probe's orbit
reduction is certified rather than asserted.

## What is proven (axiom-clean: `propext, Classical.choice, Quot.sound`)

* `gdom12 i = 2^i` enumerates `F₁₃ˣ` (`gdom12_powers`, `gdom12_injective`);
* `gdom12 (finRotate 12 i) = 2 · gdom12 i` (`gdom12_rotate`) — the cyclic rotation `i ↦ i+1`
  scales the domain by the generator `2 ≠ 0`;
* `mcaEvent_rsN12_rotate` — the **A5 `n = 12` pin**: the MCA event of `RS[F₁₃, ⟨2⟩, 6]` is
  invariant under the smooth-domain rotation, at every radius `δ`, stack `(u₀, u₁)`, and
  scalar `γ` (consumes `MCAEquivariance.mcaEvent_rs_rotate`);
* `prob_mcaEvent_rsN12_rotate` — the probability-level statement: the per-stack bad-scalar
  probability is invariant under the rotation, so rotation-related stacks share an
  `ε_mca`-contribution (the orbit-reduction certificate);
* `epsMCA_rsN12_eq_iSup_reps` — the orbit-representative reduction at this instance: a stack
  set meeting every per-stack probability value computes `ε_mca` of `RS[F₁₃, ⟨2⟩, 6]` as a
  sup over representatives (consumes `epsMCA_eq_iSup_subtype_of_reps`).

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  ePrint 2026/680. Issue #334 A5 (the exact `n = 12` orbit-reduced profile).
-/

set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code
open ProximityGap.MCAEquivariance

namespace ProximityGap.EquivariancePinN12

/-- The base field `F₁₃`. -/
abbrev F13 := ZMod 13

instance primeFact_EquivariancePinN12_1 : Fact (Nat.Prime 13) := ⟨by decide⟩

/-- The smooth evaluation domain: the full multiplicative group `F₁₃ˣ = ⟨2⟩` of size
`n = 12`, enumerated as successive powers of the primitive root `2`. -/
def gdom12 : Fin 12 → F13 := ![1, 2, 4, 8, 3, 6, 12, 11, 9, 5, 10, 7]

/-- The domain really is the cyclic group `⟨2⟩`: `gdom12 i = 2^i`. -/
theorem gdom12_powers : ∀ i : Fin 12, gdom12 i = 2 ^ (i : ℕ) := by decide

/-- The domain enumeration is injective (12 distinct nonzero points). -/
theorem gdom12_injective : Function.Injective gdom12 := by decide

/-- The R1-style domain embedding for the `n = 12` instance. -/
def gdom12Emb : Fin 12 ↪ F13 := ⟨gdom12, gdom12_injective⟩

/-- `RS[F₁₃, ⟨2⟩, 6]`: evaluations of polynomials of degree `< 6` on the smooth domain.
Dimension `k = 6`, block length `n = 12`, rate `ρ = 1/2` (a production rate). -/
noncomputable def rsN12 : Submodule F13 (Fin 12 → F13) := ReedSolomon.code gdom12Emb 6

/-- **The cyclic rotation of the `n = 12` domain.** `finRotate 12 : i ↦ i+1` advances the
power of the generator, so it multiplies the evaluation point by the generator `2`:
`gdom12 (finRotate 12 i) = 2 · gdom12 i`. -/
theorem gdom12_rotate : ∀ i : Fin 12, gdom12 (finRotate 12 i) = 2 * gdom12 i := by decide

/-- **The A5 equivariance pin at the `n = 12` instance.** The MCA event of `RS[F₁₃, ⟨2⟩, 6]`
is invariant under the smooth-domain multiplicative rotation `finRotate 12` (which scales the
domain by the generator `2 ≠ 0`), at every radius `δ`, every stack `(u₀, u₁)`, and every
scalar `γ`. This is the `n = 12` analogue of `MCAEquivariance.mcaEvent_rsC_rotate`, certifying
the orbit reduction of the exact `n = 12` profile probe. -/
theorem mcaEvent_rsN12_rotate (δ : ℝ≥0) (γ : F13) (u₀ u₁ : Fin 12 → F13) :
    mcaEvent (F := F13) (rsN12 : Set (Fin 12 → F13)) δ
        (u₀ ∘ ⇑(finRotate 12)) (u₁ ∘ ⇑(finRotate 12)) γ ↔
      mcaEvent (F := F13) (rsN12 : Set (Fin 12 → F13)) δ u₀ u₁ γ :=
  mcaEvent_rs_rotate gdom12Emb 6 (finRotate 12) 2 (by decide)
    (fun i => gdom12_rotate i) δ γ u₀ u₁

open Classical in
/-- **The probability-level A5 pin at `n = 12`.** The per-stack bad-scalar probability of
`RS[F₁₃, ⟨2⟩, 6]` is invariant under the smooth-domain rotation, so any two stacks related by
the rotation contribute identically to `ε_mca` — the orbit-reduction certificate at this
instance. -/
theorem prob_mcaEvent_rsN12_rotate (δ : ℝ≥0) (u₀ u₁ : Fin 12 → F13) :
    Pr_{ let γ ←$ᵖ F13 }[mcaEvent (F := F13) (rsN12 : Set (Fin 12 → F13)) δ
        (u₀ ∘ ⇑(finRotate 12)) (u₁ ∘ ⇑(finRotate 12)) γ]
      = Pr_{ let γ ←$ᵖ F13 }[mcaEvent (F := F13) (rsN12 : Set (Fin 12 → F13)) δ u₀ u₁ γ] :=
  Pr_congr_iff _ fun γ => mcaEvent_rsN12_rotate δ γ u₀ u₁

open Classical in
/-- **The orbit-representative reduction at the `n = 12` instance.** A stack set `T` meeting
every per-stack probability value computes `ε_mca` of `RS[F₁₃, ⟨2⟩, 6]` as the sup over `T`.
A multiplicative-rotation orbit transversal (justified by `prob_mcaEvent_rsN12_rotate`, the
translation/scaling/γ-shift invariances of `MCAEquivariance`) qualifies — this is the engine
behind the exact `n = 12` profile probe's orbit reduction. -/
theorem epsMCA_rsN12_eq_iSup_reps (δ : ℝ≥0)
    (T : Set (WordStack F13 (Fin 2) (Fin 12)))
    (hT : ∀ u : WordStack F13 (Fin 2) (Fin 12), ∃ v ∈ T,
      Pr_{ let γ ←$ᵖ F13 }[mcaEvent (rsN12 : Set (Fin 12 → F13)) δ (v 0) (v 1) γ]
        = Pr_{ let γ ←$ᵖ F13 }[mcaEvent (rsN12 : Set (Fin 12 → F13)) δ (u 0) (u 1) γ]) :
    epsMCA (F := F13) (rsN12 : Set (Fin 12 → F13)) δ
      = ⨆ v : T, Pr_{ let γ ←$ᵖ F13 }[mcaEvent (rsN12 : Set (Fin 12 → F13)) δ
          ((v : WordStack F13 (Fin 2) (Fin 12)) 0)
          ((v : WordStack F13 (Fin 2) (Fin 12)) 1) γ] :=
  epsMCA_eq_iSup_subtype_of_reps (F := F13) (rsN12 : Set (Fin 12 → F13)) δ T hT

/-! ## Source audit -/

#print axioms gdom12_powers
#print axioms gdom12_injective
#print axioms gdom12_rotate
#print axioms mcaEvent_rsN12_rotate
#print axioms prob_mcaEvent_rsN12_rotate
#print axioms epsMCA_rsN12_eq_iSup_reps

end ProximityGap.EquivariancePinN12
