/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._R19ExplicitCharacterRung

/-!
# LANE SUBY (#466 round 25): the subfamily-Y `ChiDecompositionOff` gate — EXACT REDUCTION

The live gate (`_R24FullRungAssembly` §(iv)) needs, for a subfamily `Y ⊆ chiFamily χ` with
`15·|Y|² ≤ m = orderOf χ`, the decomposition
`ChiDecompositionOff ψ G (Gchi χ) D Y (gaussSum · ψ) m` — with the ORIGINAL hyperplane
`H = Gχ` and ORIGINAL factor `m`.  The natural candidate subfamily is the coarse power family
`Y = chiFamily (χ^d)` (`|Y| = orderOf (χ^d) − 1 ≈ m/d − 1`, so `d ≳ √(15m)` meets the gate
cardinality).  This brick pins EXACTLY what that route costs:

* **Free part** (`chiDecompositionOff_pow`): the r19 identity instantiates verbatim at `χ^d` —
  but it delivers the decomposition for the COARSER hyperplane `Gchi (χ^d) ⊇ Gchi χ` at the
  SMALLER factor `m' = orderOf (χ^d)`.  The subfamily route does secretly change the
  hyperplane.
* **The crux** (`chiDecompositionOff_powSubfamily_iff_hyperplaneTransfer`): the gate's
  decomposition for `Y = chiFamily (χ^d)` at the ORIGINAL `(Gchi χ, m)` holds **iff** the
  pointwise hyperplane-transfer identity
  `m·I_{Gχ}(s₀) = m'·I_{G_{χ^d}}(s₀)` holds at every `s₀ ∉ D` — i.e. iff the signed
  incidences over the coarser subgroup are EXACTLY equidistributed across its `Gχ`-cosets at
  every off-set offset.  (Probe `probe_r25_subfamily_gate.py`: the full identity checks to
  `1e-13`, the transfer identity FAILS at almost every offset with residual of full
  `√q·|G|`-scale — `max|res| ∈ [45, 87]` at `p ∈ {41, 73}`, zero residual at ≤ 3/36 offsets.
  The transfer identity is NOT a theorem; it is the exact open content of the coarse-power
  subfamily gate.)
* **Composed gate** (`wickForIncidenceAwayAt_two_of_hyperplaneTransfer`): granting the
  transfer identity as the one named input, the whole thin-subfamily consumer fires:
  `WickForIncidenceAwayAt ψ G (Gchi χ) D 2` for the ORIGINAL hyperplane, with the gate
  arithmetic `15·(m'−1)² ≤ m` (satisfiable, e.g. `m' − 1 ≤ √(m/15)`), quartic-Weil input on
  the full family, and the size regime.  The arithmetic composes; ONLY the transfer identity
  is open.

Net for the ledger: the subfamily-Y gate is NOT free.  Coarse instantiation changes the
hyperplane; keeping the original hyperplane costs the (numerically refuted-as-identity,
hence genuinely analytic) coset-equidistribution transfer.  Any future discharge must bound —
not cancel — the omitted-character residual.

Axiom-clean target (`propext, Classical.choice, Quot.sound`).  Issue #466, round 25.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset
open ArkLib.ProximityGap.ConstantIndexGaussSum
open ArkLib.ProximityGap.Frontier.R15IncidenceMomentInterchange
open ArkLib.ProximityGap.Frontier.R17QuadrupleWeilRung
open ArkLib.ProximityGap.Frontier.R19ChiDecomposition
open ArkLib.ProximityGap.Frontier.R19ExplicitCharacterRung

namespace ArkLib.ProximityGap.Frontier.R25SubfamilyGate

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable local instance localInstance_R25SubfamilyGate_1 : DecidableEq (MulChar F ℂ) := Classical.decEq _

/-! ### (0) The coarse power family is a subfamily -/

/-- The coarse power family sits inside the fine family: every nontrivial power of `χ^d` is a
nontrivial power of `χ` with exponent below `orderOf χ`. -/
theorem chiFamily_pow_subset (χ : MulChar F ℂ) (d : ℕ) :
    chiFamily (χ ^ d) ⊆ chiFamily χ := by
  classical
  intro χ' hχ'
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hχ'
  obtain ⟨hk0, hkm⟩ := Finset.mem_erase.mp hk
  have hkm' : k < orderOf (χ ^ d) := Finset.mem_range.mp hkm
  -- (χ^d)^k = χ^(d*k) = χ^(d*k % orderOf χ), and the reduced exponent is nonzero.
  have hpow : (χ ^ d) ^ k = χ ^ (d * k % orderOf χ) := by
    rw [← pow_mul, pow_mod_orderOf]
  have hne1 : (χ ^ d) ^ k ≠ 1 := pow_ne_one_of_lt_orderOf hk0 hkm'
  have hj0 : d * k % orderOf χ ≠ 0 := by
    intro h0
    apply hne1
    rw [hpow, h0, pow_zero]
  have hjlt : d * k % orderOf χ < orderOf χ :=
    Nat.mod_lt _ (MulChar.orderOf_pos χ)
  refine Finset.mem_image.mpr ⟨d * k % orderOf χ, ?_, hpow.symm⟩
  exact Finset.mem_erase.mpr ⟨hj0, Finset.mem_range.mpr hjlt⟩

/-! ### (1) The free coarse instantiation — note the CHANGED hyperplane and factor -/

/-- **Free instantiation.**  The r19 decomposition holds verbatim at `χ^d` — for the COARSER
hyperplane `Gchi (χ^d)` and the SMALLER factor `orderOf (χ^d)`.  This is what the coarse
route gets for free; it is NOT the gate's `hdec`, whose hyperplane and factor come from the
original `χ`. -/
theorem chiDecompositionOff_pow (χ : MulChar F ℂ) (d : ℕ) {ψ : AddChar F ℂ}
    (hψ : ψ.IsPrimitive) {G D : Finset F} (hGD : G ⊆ D) :
    ChiDecompositionOff ψ G (Gchi (χ ^ d)) D (chiFamily (χ ^ d))
      (fun χ' => gaussSum χ' ψ) (orderOf (χ ^ d)) :=
  chiDecompositionOff_holds (χ ^ d) hψ hGD

/-! ### (2) The crux: the original-hyperplane subfamily gate ⟺ hyperplane transfer -/

/-- The pointwise hyperplane-transfer identity: the fine incidence sum at factor `m` agrees
with the coarse incidence sum at factor `m'` off the deleted set.  Equivalently (via
`chiSubfamily_chiDecompositionOff_iff_residual_vanishes`): the omitted-character residual
`∑_{χ' ∈ chiFamily χ \ chiFamily (χ^d)} g(χ')·T_{χ'}` vanishes off `D`.  Numerically REFUTED
as an identity (`probe_r25_subfamily_gate.py`): residual is `√q·|G|`-scale at almost every
offset. -/
def HyperplaneTransferOff (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (G D : Finset F) (d : ℕ) :
    Prop :=
  ∀ s₀ : F, s₀ ∉ D →
    (orderOf χ : ℂ) * incidenceSum ψ G (Gchi χ) s₀
      = (orderOf (χ ^ d) : ℂ) * incidenceSum ψ G (Gchi (χ ^ d)) s₀

/-- **THE CRUX.**  For the coarse power subfamily `Y = chiFamily (χ^d)`, the gate's
`ChiDecompositionOff` at the ORIGINAL hyperplane `Gchi χ` and factor `orderOf χ` holds iff
the hyperplane-transfer identity holds off `D`.  The subfamily gate is exactly a coset
-equidistribution statement — not free, and not implied by the r19 machinery. -/
theorem chiDecompositionOff_powSubfamily_iff_hyperplaneTransfer
    (χ : MulChar F ℂ) (d : ℕ) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {G D : Finset F} (hGD : G ⊆ D) :
    ChiDecompositionOff ψ G (Gchi χ) D (chiFamily (χ ^ d))
        (fun χ' => gaussSum χ' ψ) (orderOf χ)
      ↔ HyperplaneTransferOff χ ψ G D d := by
  have hcoarse := chiDecompositionOff_pow χ d hψ hGD
  constructor
  · intro hdec s₀ hs₀
    have h1 := hdec s₀ hs₀
    have h2 := hcoarse s₀ hs₀
    rw [h1, h2]
  · intro htrans s₀ hs₀
    have h2 := hcoarse s₀ hs₀
    rw [htrans s₀ hs₀, h2]

/-! ### (3) The composed gate: transfer identity ⇒ the r = 2 away-Wick rung, ORIGINAL H -/

/-- **Composed subfamily gate.**  Granting the hyperplane-transfer identity as the single
named input, the thin-subfamily consumer fires end to end for the ORIGINAL hyperplane:
`WickForIncidenceAwayAt ψ G (Gchi χ) D 2`.  All arithmetic composes: the gate cardinality is
`15·(orderOf (χ^d) − 1)² ≤ orderOf χ` (satisfiable whenever `orderOf (χ^d) − 1 ≤ √(m/15)`),
and the Gauss-sum, fourth-moment, and Σ inputs restrict to the subfamily as in r19.  ONLY
`HyperplaneTransferOff` is open — and the probe shows it fails as an exact identity, so a
future discharge must replace exact vanishing by a bounded-residual variant of the consumer. -/
theorem wickForIncidenceAwayAt_two_of_hyperplaneTransfer
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (χ : MulChar F ℂ) (d : ℕ)
    (G D : Finset F) (hGD : G ⊆ D)
    (hm : 2 ≤ orderOf χ) (hn : 1 ≤ G.card)
    (hm' : 2 ≤ orderOf (χ ^ d))
    (horder : 15 * (orderOf (χ ^ d) - 1) ^ 2 ≤ orderOf χ)
    (htrans : HyperplaneTransferOff χ ψ G D d)
    (hW :
      ∀ χ' ∈ chiFamily χ,
        ArkLib.ProximityGap.Frontier.R18FourthMomentTwist.QuarticWeilInput χ' G)
    (hq1 : (1 : ℝ) ≤ (Fintype.card F : ℝ))
    (hnq : ((G.card : ℝ)) ^ 2 ≤ (Fintype.card F : ℝ))
    (hn4q : ((G.card : ℝ)) ^ 4 ≤ (Fintype.card F : ℝ))
    (hreg : 16 * (orderOf χ : ℝ) ^ 2 * (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    WickForIncidenceAwayAt ψ G (Gchi χ) D 2 := by
  classical
  have hY : chiFamily (χ ^ d) ⊆ chiFamily χ := chiFamily_pow_subset χ d
  have hcard : (chiFamily (χ ^ d)).card = orderOf (χ ^ d) - 1 := chiFamily_card (χ ^ d)
  have hX : (chiFamily (χ ^ d)).Nonempty := by
    rw [← Finset.card_pos, hcard]
    omega
  have horder' : 15 * (chiFamily (χ ^ d)).card ^ 2 ≤ orderOf χ := by
    rw [hcard]; exact horder
  have hdec :
      ChiDecompositionOff ψ G (Gchi χ) D (chiFamily (χ ^ d))
        (fun χ' => gaussSum χ' ψ) (orderOf χ) :=
    (chiDecompositionOff_powSubfamily_iff_hyperplaneTransfer χ d hψ hGD).mpr htrans
  exact
    wickForIncidenceAwayAt_two_of_chiSubfamily_quarticWeil_of_nonempty_fifteen_card_sq_le_order_nat
      ψ hψ χ G D hm hn hY hX horder' hdec hW hq1 hnq hn4q hreg

/-! ### (4) Sanity: the transfer identity is trivially true at `d = 1` (no thinning) -/

/-- Degenerate base case: at `d = 1` the transfer identity is reflexive, and the composed
gate collapses to the full-family route (whose cardinality gate is separately impossible —
`not_fifteen_chiFamily_card_sq_le_order`).  This pins that the content of
`HyperplaneTransferOff` lives strictly at `d ≥ 2`. -/
theorem hyperplaneTransferOff_one (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (G D : Finset F) :
    HyperplaneTransferOff χ ψ G D 1 := by
  intro s₀ _
  rw [pow_one]

end ArkLib.ProximityGap.Frontier.R25SubfamilyGate

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.R25SubfamilyGate.chiFamily_pow_subset
#print axioms ArkLib.ProximityGap.Frontier.R25SubfamilyGate.chiDecompositionOff_pow
#print axioms
  ArkLib.ProximityGap.Frontier.R25SubfamilyGate.chiDecompositionOff_powSubfamily_iff_hyperplaneTransfer
#print axioms
  ArkLib.ProximityGap.Frontier.R25SubfamilyGate.wickForIncidenceAwayAt_two_of_hyperplaneTransfer
#print axioms ArkLib.ProximityGap.Frontier.R25SubfamilyGate.hyperplaneTransferOff_one
