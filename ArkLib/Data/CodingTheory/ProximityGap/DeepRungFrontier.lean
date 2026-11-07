/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26CeilingMarch

/-!
# The deeper-rung ownership-cap residual (#389, route-2 constant-rate frontier)

The proven count `march_badScalars_card_mul_le` (KKH26CeilingMarch.lean) gives,
*unconditionally*, that at agreement threshold `> d+2` (the minimal witness, `m = 1`),
every stack has `#bad · (d+2) ≤ C(n,d+2)`: each bad scalar owns at least `d+2`
non-degenerate `(d+2)`-tuples, distinct scalars own disjoint tuples, and only `C(n,d+2)`
tuples exist.  At the constant-rate band radius (`w₀ = rm`, agreement `≫ d+2`) the count
goes loose: the proven per-witness ownership stalls at `d+2` (resp. the pair-bound's
`C(w₀+1,d+1)` of `OwnershipCensusSharpened.lean`), while the *tight* per-witness cap — the
one the deviation stacks realize — is `C(w−1, d+1) = C(w₀, d+1)` owned subsets per scalar
at witness size `w = w₀+1`.  Proving every bad scalar OWNS that many at the band radius is
the genuine open object: a different line-incidence counting surface for `k = Θ(ρn)`, with
no known technique (Weil/√q insufficient, sum-product helps supply not line incidence).

**This file's honest contribution.**  It does NOT prove the open cap.  It (1) names an
explicit `Prop` (`DeepRungOwnershipCap`) written in the shape of `march`'s ownership count,
targeting the constant-rate witness threshold `w₀` with floor `C(w₀, d+1)`; and (2) proves the
consumer chain machine-checked.  **Caveat:** the `Prop` chooses its tuple type, ownership map
and universe existentially, with no link to witness subsets or non-degenerate tuples, so it is
equivalent to the bare count `#bad · Ω ≤ U` (`deepRungOwnershipCap_iff_count`).  It is a direct
count assumption, not a structural ownership statement; the structural residual (with the
actual owned-subset type and ownership predicate) is not formalized here.  The chain:

* `deepRung_abstract_count` — the abstract ownership-to-count skeleton: any family of
  pairwise-disjoint owned-tuple sets, one per bad scalar, each of size `≥ Ω`, inside a
  universe of `U` tuples, forces `#bad · Ω ≤ U`.  This is the load-bearing combinatorial
  core both `march` and the sharpened census instantiate; isolating it pins the open input.
* `deepRung_badScalars_card_mul_le` — the cap discharges the count `#bad · Ω ≤ U`.
* `deepRung_epsMCA_le` — the count discharges the MCA error: `epsMCA ≤ (U/Ω)/p`.
* `deepRung_interiorCeiling` — the MCA error discharges the interior ceiling.
* `deepRung_deltaStar_pin` — the interior ceiling discharges the `δ*` pin
  `mcaDeltaStar = 1 − r/2^μ`, the same headline as `kkh26_march_deltaStar_pin` but now
  fed by the tight deep-rung floor instead of the minimal-witness `d+2`.

So the deep-band pin is reduced, machine-checked, to ONE named Prop, which is the bad-scalar
count at the constant-rate radius.  That count stays open (the recognized list-decoding
wall); everything from it to the prize pin is an axiom-clean reduction.
`deepRung_recovers_march` only checks that the chain's conclusion at `w₀ = d+2` has the same
shape as the proven `march` count; given the equivalence with the count, this is automatic.

Issue #389, route-2 constant-rate follow-up.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26
open ProximityGap.KKH26DeltaStarReduction
open ArkLib.ProximityGap.KKH26CeilingMarch

namespace ArkLib.ProximityGap.DeepRungFrontier

variable {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ} [NeZero n]

/-! ## The abstract ownership-to-count skeleton

This is the combinatorial core common to `march_badScalars_card_mul_le` and
`sharpened_badScalars_card_mul_choose_le`: bad scalars own pairwise-disjoint families of
tuples, each of size `≥ Ω`, all inside a `U`-element universe.  Isolating it makes the open
input precise — only the per-scalar ownership floor `Ω` and the disjointness are at issue. -/

open Classical in
/-- **The abstract deep-rung ownership-to-count law.**  Let `B` be a finset of bad scalars,
each assigned (via `Φ`) a family of owned tuples; suppose every scalar owns at least `Ω`
tuples (`hP`), distinct scalars own disjoint families (`hdisj`), and every owned tuple lives
in a fixed universe `G` of size `U` (`hsub`).  Then `#B · Ω ≤ U`.

This is the engine: `march` instantiates `Ω = d+2`, `U = C(n,d+2)`; the sharpened census
`Ω = C(w₀+1,d+1)`, `U = C(n,d+1)(n−d−1)`; the deep-rung cap targets the tight
`Ω = C(w₀,d+1)` at the constant-rate radius. -/
theorem deepRung_abstract_count {B : Finset (ZMod p)}
    {τ : Type} [DecidableEq τ] (Φ : {x // x ∈ B} → Finset τ) (G : Finset τ) {Ω U : ℕ}
    (hU : G.card = U)
    (hP : ∀ γ : {x // x ∈ B}, Ω ≤ (Φ γ).card)
    (hdisj : ∀ γ₁ ∈ B.attach, ∀ γ₂ ∈ B.attach, γ₁ ≠ γ₂ → Disjoint (Φ γ₁) (Φ γ₂))
    (hsub : B.attach.biUnion Φ ⊆ G) :
    B.card * Ω ≤ U := by
  have hbig : B.attach.card * Ω ≤ (B.attach.biUnion Φ).card := by
    rw [Finset.card_biUnion hdisj]
    calc B.attach.card * Ω = ∑ _γ ∈ B.attach, Ω := by
          rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun γ _ => hP γ)
  calc B.card * Ω = B.attach.card * Ω := by rw [Finset.card_attach]
    _ ≤ (B.attach.biUnion Φ).card := hbig
    _ ≤ G.card := Finset.card_le_card hsub
    _ = U := hU

/-! ## The named residual: the deeper-rung ownership cap -/

open Classical in
/-- **The deeper-rung count residual (#389), in ownership-shaped form.**  For the degree-`d`
evaluation code at agreement threshold above `w₀`, every stack `(u₀,u₁)` admits, for each bad
scalar `γ`, a finset `Φ γ` in some type `τ` and a finset `G` of size `U`, such that

* every bad scalar gets at least `Ω` elements,
* distinct bad scalars get disjoint finsets,
* all of them lie in `G`.

**What this Prop actually says.**  The type `τ`, the map `Φ` and the universe `G` are chosen
existentially, with no link to witness subsets, interpolation or non-degenerate tuples.  So
the Prop is *equivalent* to the bare count `#bad · Ω ≤ U` at every stack
(`deepRungOwnershipCap_iff_count`): one direction is the disjoint-union count, and conversely
one can label each bad scalar by `Ω` fresh tokens inside `range U`.  It is therefore a direct
count assumption written in ownership notation, not a structural ownership statement.  An
honest structural residual would fix `τ` to the actual owned-subset type and constrain `Φ` by
the ownership predicate; that statement is not formalized here.

The intended parameters are `Ω = C(w₀, d+1)` (the deviation-stack ceiling
`C(w−1,d+1)|_{w=w₀+1}`) and `U = C(n, d+1)·(n−d−1)`.  At the constant-rate radius
(`w₀ = rm`, `Ω = C(rm,(r−2)m+1)`) the count is open: no known technique supplies it for
`k = Θ(ρn)`. -/
def DeepRungOwnershipCap (g : ZMod p) (n d w₀ Ω U : ℕ) : Prop :=
  ∀ (u₀ u₁ : Fin n → ZMod p) {δ : ℝ≥0},
    ((w₀ : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) →
    ∃ (τ : Type) (_ : DecidableEq τ)
      (B : Finset (ZMod p))
      (_hBeq : B = Finset.univ.filter (fun γ : ZMod p =>
          mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ u₀ u₁ γ))
      (Φ : {x // x ∈ B} → Finset τ) (G : Finset τ),
      G.card = U ∧
      (∀ γ : {x // x ∈ B}, Ω ≤ (Φ γ).card) ∧
      (∀ γ₁ ∈ B.attach, ∀ γ₂ ∈ B.attach, γ₁ ≠ γ₂ → Disjoint (Φ γ₁) (Φ γ₂)) ∧
      B.attach.biUnion Φ ⊆ G

/-! ## The consumer chain: cap ⟹ count ⟹ epsMCA ⟹ interior ceiling ⟹ pin -/

open Classical in
/-- **Cap ⟹ count.**  Granting the deeper-rung ownership cap, at agreement threshold above
`w₀` every stack has `#bad · Ω ≤ U` — the tight deep-band count with the deviation-stack
ownership floor `Ω` in place of `march`'s minimal-witness `d+2`. -/
theorem deepRung_badScalars_card_mul_le {d w₀ Ω U : ℕ}
    (hcap : DeepRungOwnershipCap g n d w₀ Ω U) {δ : ℝ≥0}
    (hδ : ((w₀ : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (u₀ u₁ : Fin n → ZMod p) :
    (Finset.univ.filter (fun γ : ZMod p =>
        mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ u₀ u₁ γ)).card * Ω ≤ U := by
  obtain ⟨τ, hτ, B, hBeq, Φ, G, hU, hP, hdisj, hsub⟩ := hcap u₀ u₁ hδ
  have h := @deepRung_abstract_count p _ B τ hτ Φ G Ω U hU hP hdisj hsub
  rw [hBeq] at h
  exact h

open Classical in
/-- **The named cap is exactly the count.**  `DeepRungOwnershipCap g n d w₀ Ω U` holds iff
every stack has `#bad · Ω ≤ U` at every radius whose witness threshold exceeds `w₀`.  The
forward direction is `deepRung_badScalars_card_mul_le`.  For the converse, take `τ = ℕ`,
`G = range U`, and give the `i`-th bad scalar (in any enumeration) the block
`[i·Ω, i·Ω + Ω)`; the blocks are disjoint and lie in `range U` because `#bad · Ω ≤ U`.  So
the cap carries no structural information beyond the count. -/
theorem deepRungOwnershipCap_iff_count {d w₀ Ω U : ℕ} :
    DeepRungOwnershipCap g n d w₀ Ω U ↔
      ∀ (u₀ u₁ : Fin n → ZMod p) {δ : ℝ≥0},
        ((w₀ : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) →
        (Finset.univ.filter (fun γ : ZMod p =>
          mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ u₀ u₁ γ)).card * Ω ≤ U := by
  constructor
  · intro hcap u₀ u₁ δ hδ
    exact deepRung_badScalars_card_mul_le hcap hδ u₀ u₁
  · intro hcount u₀ u₁ δ hδ
    have hBU := hcount u₀ u₁ hδ
    generalize hB : Finset.univ.filter (fun γ : ZMod p =>
      mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ u₀ u₁ γ) = B at hBU
    let idx : {x // x ∈ B} → ℕ := fun γ => (B.equivFin γ : ℕ)
    have hidx_lt : ∀ γ, idx γ < B.card := fun γ => (B.equivFin γ).isLt
    have hidx_inj : Function.Injective idx := fun γ₁ γ₂ h =>
      B.equivFin.injective (Fin.ext h)
    refine ⟨ℕ, inferInstance, B, rfl,
      fun γ => Finset.Ico (idx γ * Ω) (idx γ * Ω + Ω), Finset.range U,
      Finset.card_range U, ?_, ?_, ?_⟩
    · intro γ
      simp
    · intro γ₁ _ γ₂ _ hne
      have hne' : idx γ₁ ≠ idx γ₂ := fun h => hne (hidx_inj h)
      rw [Finset.disjoint_left]
      intro x hx₁ hx₂
      rw [Finset.mem_Ico] at hx₁ hx₂
      rcases Nat.lt_or_gt_of_ne hne' with hlt | hlt
      · have hmul : (idx γ₁ + 1) * Ω ≤ idx γ₂ * Ω := Nat.mul_le_mul_right Ω hlt
        rw [Nat.add_one_mul] at hmul
        omega
      · have hmul : (idx γ₂ + 1) * Ω ≤ idx γ₁ * Ω := Nat.mul_le_mul_right Ω hlt
        rw [Nat.add_one_mul] at hmul
        omega
    · intro x hx
      obtain ⟨γ, _, hxγ⟩ := Finset.mem_biUnion.mp hx
      rw [Finset.mem_Ico] at hxγ
      rw [Finset.mem_range]
      have hmul : (idx γ + 1) * Ω ≤ B.card * Ω := Nat.mul_le_mul_right Ω (hidx_lt γ)
      rw [Nat.add_one_mul] at hmul
      omega

open Classical in
/-- **Count ⟹ MCA error.**  Granting the cap, the MCA error of the degree-`d` evaluation
code is at most `(U/Ω)/p` at every radius whose witness threshold exceeds `w₀` — the same
shape as `march_epsMCA_le` and `sharpened_epsMCA_le`, with the tight floor `Ω`. -/
theorem deepRung_epsMCA_le {d w₀ Ω U : ℕ} (hΩ : 0 < Ω)
    (hcap : DeepRungOwnershipCap g n d w₀ Ω U) {δ : ℝ≥0}
    (hδ : ((w₀ : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0)) :
    epsMCA (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
      ≤ ((U / Ω : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Nonempty (ZMod p) := ⟨0⟩
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card, ZMod.card p]
  simp only [ENNReal.coe_natCast]
  gcongr
  have h4 := deepRung_badScalars_card_mul_le (g := g) hcap hδ (u 0) (u 1)
  have hle : (Finset.filter (fun γ : ZMod p =>
      mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ (u 0) (u 1) γ)
      Finset.univ).card ≤ U / Ω :=
    (Nat.le_div_iff_mul_le hΩ).mpr h4
  exact_mod_cast hle

open Classical in
/-- **MCA error ⟹ interior ceiling.**  At the `m = 1` slice, granting the cap at witness
threshold `w₀ = r` (so the agreement bound below the KKH26 ceiling `1 − r/2^μ` is `> r`),
the `InteriorCeiling` obligation is discharged whenever `ε* ≥ (U/Ω)/p`. -/
theorem deepRung_interiorCeiling {μ r Ω U : ℕ} (_hr2 : 2 ≤ r) (hn : n = 2 ^ μ)
    (_hg : orderOf g = n) (hΩ : 0 < Ω)
    (hcap : DeepRungOwnershipCap g n (r - 2) r Ω U) (εstar : ℝ≥0∞)
    (hband : ((U / Ω : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) ≤ εstar) :
    InteriorCeiling p n g μ 1 r εstar := by
  intro δ hδ
  have hcode : (r - 2) * 1 = r - 2 := mul_one _
  rw [hcode]
  -- agreement threshold below the ceiling exceeds `r = w₀`
  have harith : ((r : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) := by
    have hsum : δ + (r : ℝ≥0) / (2 : ℝ≥0) ^ μ < 1 := lt_tsub_iff_right.mp hδ
    have hlt : (r : ℝ≥0) / (2 : ℝ≥0) ^ μ < 1 - δ := by
      rw [lt_tsub_iff_right]
      calc (r : ℝ≥0) / (2 : ℝ≥0) ^ μ + δ = δ + (r : ℝ≥0) / (2 : ℝ≥0) ^ μ := by ring
      _ < 1 := hsum
    have hpow0 : (0 : ℝ≥0) < (2 : ℝ≥0) ^ μ := by positivity
    have hmul : (r : ℝ≥0) < (1 - δ) * (2 : ℝ≥0) ^ μ := by
      have h := mul_lt_mul_of_pos_right hlt hpow0
      rwa [div_mul_cancel₀ _ (ne_of_gt hpow0)] at h
    have hcard : ((Fintype.card (Fin n) : ℕ) : ℝ≥0) = (2 : ℝ≥0) ^ μ := by
      rw [Fintype.card_fin, hn]; push_cast; ring
    rw [hcard]; exact hmul
  have h := deepRung_epsMCA_le (g := g) (d := r - 2) (δ := δ) hΩ hcap harith
  exact le_trans h hband

open Classical in
/-- **THE DEEP-RUNG PIN (#389, route-2 constant-rate, modulo the named cap).**  For the
degree-`(r−2)` code on the smooth `2^μ`-point domain, and every `ε*` in the band
`[(U/Ω)/p, (2^r·C(2^{μ−1},r))/p)`, granting the deeper-rung ownership cap:

  `mcaDeltaStar(evalCode g (2^μ) (r−2), ε*) = 1 − r/2^μ`.

Identical headline to `kkh26_march_deltaStar_pin`, but fed by the tight deep-rung floor
`Ω` (toward `C(w₀,d+1)`) instead of the minimal-witness `d+2` — so the band reaches the
constant-rate regime the moment the cap is supplied.  The cap is the open object. -/
theorem deepRung_deltaStar_pin {μ r Ω U : ℕ} (hμ : 1 ≤ μ) (hr2 : 2 ≤ r)
    (hr : r ≤ 2 ^ (μ - 1)) (hn : n = 2 ^ μ) (hg : orderOf g = 2 ^ μ) (hΩ : 0 < Ω)
    (hp : ((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) < p)
    (hcap : DeepRungOwnershipCap g n (r - 2) r Ω U) (εstar : ℝ≥0∞)
    (hlo : ((U / Ω : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) ≤ εstar)
    (hhi : εstar < ((2 ^ r * (2 ^ (μ - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n (r - 2)) εstar
      = 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) := by
  have hgn : orderOf g = n := by rw [hn]; exact hg
  have h := kkh26_deltaStar_pin_of_interior_ceiling (p := p) (n := n) (μ := μ) (m := 1)
    (r := r) (g := g) hμ le_rfl (by rw [hn, mul_one]) (by rw [mul_one]; exact hg) hp
    hr2 hr εstar hhi (deepRung_interiorCeiling hr2 hn hgn hΩ hcap εstar hlo)
  rwa [mul_one] at h

/-! ## Consistency check at the minimal witness

The consumer chain at `(w₀, Ω, U) = (d+2, d+2, C(n,d+2))` has the same conclusion
`#bad · (d+2) ≤ C(n,d+2)` as the proven `march_badScalars_card_mul_le`.  This is only a
shape check: since the named cap is equivalent to the count itself
(`deepRungOwnershipCap_iff_count`), matching conclusions at matching parameters is
automatic and does not show that the cap encodes any ownership structure. -/

open Classical in
/-- The named cap, instantiated at the minimal witness `(d+2, d+2, C(n,d+2))`, yields
literally the `march_badScalars_card_mul_le` conclusion.  This is a parameter-matching
check, not evidence of a structural relation (the cap is the count; see
`deepRungOwnershipCap_iff_count`). -/
theorem deepRung_recovers_march {d : ℕ}
    (hcap : DeepRungOwnershipCap g n d (d + 2) (d + 2) (n.choose (d + 2))) {δ : ℝ≥0}
    (hδ : ((d + 2 : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (u₀ u₁ : Fin n → ZMod p) :
    (Finset.univ.filter (fun γ : ZMod p =>
        mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ u₀ u₁ γ)).card * (d + 2)
      ≤ n.choose (d + 2) :=
  deepRung_badScalars_card_mul_le hcap hδ u₀ u₁

end ArkLib.ProximityGap.DeepRungFrontier
