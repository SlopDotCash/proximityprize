/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26DeltaStarReduction
import ArkLib.Data.CodingTheory.ProximityGap.KKH26DimOnePin
import Mathlib.LinearAlgebra.Lagrange

/-!
# The glueing law: the exact subset-ownership constant of the dimension ladder (#371)

> **Priority and dedup note.**  The glueing sharpening `#bad·(d+2) ≤ C(n, d+2)` landed
> first in `KKH26DimGeneralSharpPin.lean` (the sharp-ownership thread), via the same
> at-most-one argument on `polyFitOn`; this file derived it independently and landed
> second.  What is **new here relative to that file**: (i) the boundary band criterion
> `r² ≤ 2^μ + 1` — strictly wider than the landed strict `r² < 2^μ`, covering the
> perfect-square rungs `r = 2^{μ/2}` at every even `μ` (`(4,4)`, `(8,6)`, `(16,8)`, …)
> via the tight induction step `(r+1)² ≤ 2m+1`; (ii) the `(10, 5)` past-`√n` rung
> instance and the pair-law comparison (`march_opens_r10_mu5`); (iii) the widened-band
> NTT instance `δ* = 5/8` at `ε* = 18/12289` (`deltaStar_pin_F12289_dimTwo`).  The rest
> stands as an independent-route confirmation (`ExplainableOn` here, `polyFitOn` there).

The dimension-ladder arc (`KKH26DimOnePin.lean` `r = 2` · `KKH26DimTwoPin.lean` `r = 3` ·
`KKH26DimGeneralPin.lean` all `(r, m)`, per-scalar subset ownership `2` ·
`OwnershipCensusSharpened.lean` the pair law `2·C(n,r)/(r+1)` at the slice, plus the
*exact-minimum ceiling* `C(w−1, d+1)` attained by single-deviation stacks) left the
subset-counting scheme with a gap: the proven per-scalar **floor** (`2`, or `(r+1)/2`
pair-equivalent) sits below the proven **ceiling** (`r` at the minimal witness), and the
probes measure every stack at or above the ceiling value.  **This file closes that gap**:
the glueing argument proves the floor `= C(w−1, d+1)` at the minimal witness — every bad
scalar owns at least `r = d + 2` non-degenerate `(d+2)`-tuples — so the subset-counting
constant at the pin slice is now exact, two-sided:

  `#bad · r ≤ C(n, r)`    (`march_badScalars_card_mul_le`, every radius below the ceiling).

**The glueing step** (the new ingredient, `glue_erase`/`ownership_card`): inside a
non-explainable `(r+1)`-point set, two distinct points with explainable complements force
their two interpolants to agree on the `r−1` common nodes, hence to be equal, hence to
explain the whole set — contradiction.  So **at most one** of the `r+1` complements is
explainable: ownership `≥ r`, exactly matching the deviation-stack ceiling
`C(w−1, d+1)|_{w=r+1} = r` of `OwnershipCensusSharpened.lean`.  (At radii far below the
ceiling the pair law's witness-growing ownership takes over; at the band edge — the only
regime the pin consumes — the glueing constant is optimal for the scheme.)

**What the sharpening buys** (`r` vs the landed `2` and `(r+1)/2`):

* the canonical band edge drops to `(C(n,r)/r)/p` — factor `2r/(r+1)` below the pair law,
  factor `r/2` below the general-pin law: the **widest proven `ε*` band at every rung**
  (e.g. `18/p` vs the landed `28/p` at the `(3,3)` NTT instance; `873/p` vs `1456/p` at
  the `(5,4)` dimension-four pin);
* the clean nonemptiness criterion moves to **`r² ≤ 2^μ + 1`** (`march_band_nonempty`,
  descending-factorial induction) — covering e.g. `(r, μ) = (4, 4)` by the general law
  (both landed criteria miss it);
* **the `(10, 5)` past-`√n` rung instance**: the glueing/sharp floor
  `C(32,10)/10 = 6451224` clears the ceiling spectrum `2^10·C(16,10) = 8200192` while the
  pair-law floor `2·C(32,10)/11 = 11729498` does not (`march_opens_r10_mu5`) — the
  dimension-9, rate-`9/32` code joins the unconditional in-window pin family at
  `δ* = 11/16`, beyond Johnson (`10² < 9·2^5`).  (The sharp subset law of
  `KKH26DimGeneralSharpPin.lean` opens this rung equally — the instance lemma lands
  here; the *pair* law cannot reach it.)

**The mechanism, end to end** (independent route, shared substrate): witness ⟹ `u₁`
non-explainable (`not_expl_dir_of_witness`, else `q_w − γ·q₁` joint-explains) ⟹ a
non-explainable `(r+1)`-subset (`exists_nonExpl_subset`, via the extension lemma) ⟹ `≥ r`
owned tuples (`ownership_card`) ⟹ tuples determine scalars (`scalar_eq_of_shared_tuple`)
⟹ disjoint families, pigeonhole on `C(n, r)`.  `InteriorCeiling` is then discharged at
`m = 1` for every `r ≥ 2` (`interiorCeiling_march`), and the pin
`mcaDeltaStar(evalCode g (2^μ) (r−2), ε*) = 1 − r/2^μ` fires on the widened band
(`kkh26_march_deltaStar_pin{,_canonical}`).

**Honest scope.**  `m = 1` only (at `m ≥ 2` the witness floor `r+1` falls below
`dim + 2` and every word is explainable on witness-sized sets — `explainableOn_of_card_le`);
the scheme ceiling of `OwnershipCensusSharpened.lean` shows per-witness subset counting
caps at ownership `C(w−1,d+1)`, so this constant is final: production dimension
`k = Θ(ρn)` needs a different counting surface, and the genuine prize core is untouched.

Probe: `scripts/probes/probe_ceiling_march_r3.py` (criterion collapse, glueing
at-most-one, ownership `≥ 3`, tuple disjointness, the bound — all exact, zero violations
at `p ∈ {17, 97}`, `n = 8`, `r = 3`; hill-climbed max `9 ≤ 18`).

The concrete instantiation `deltaStar_pin_F12289_dimTwo` pins `δ* = 5/8` for the
dimension-two code on `⟨4043⟩ ⊆ F₁₂₂₈₉ˣ` at `ε* = 18/12289` — the same instance as the
landed `r = 3` rung, at a strictly smaller `ε*` than any landed bound reaches (`18` vs
`28`), certifying the widened band end to end.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

set_option linter.unusedSectionVars false

open Finset Polynomial
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26
open ProximityGap.KKH26DeltaStarReduction

namespace ArkLib.ProximityGap.KKH26CeilingMarch

variable {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ} [NeZero n]

/-! ## Explainability on a set -/

/-- A word is explainable on a set `S` at degree `d` when it agrees on `S` with the
evaluation of a polynomial of degree at most `d` on the smooth nodes `g^i`. -/
def ExplainableOn (g : ZMod p) (d : ℕ) (u : Fin n → ZMod p) (S : Finset (Fin n)) : Prop :=
  ∃ q : Polynomial (ZMod p), q.natDegree ≤ d ∧ ∀ i ∈ S, u i = q.eval (g ^ (i : ℕ))

theorem explainableOn_mono {d : ℕ} {u : Fin n → ZMod p} {S T : Finset (Fin n)}
    (hTS : T ⊆ S) (h : ExplainableOn g d u S) : ExplainableOn g d u T := by
  obtain ⟨q, hq, hagree⟩ := h
  exact ⟨q, hq, fun i hi => hagree i (hTS hi)⟩

/-- The nodes `i ↦ g^i` are injective on every subset of `Fin n` when `g` has order `n`. -/
theorem nodes_injOn (hg : orderOf g = n) (S : Finset (Fin n)) :
    Set.InjOn (fun i : Fin n => g ^ (i : ℕ)) ↑S := by
  intro i _ j _ hij
  have h1 : (i : ℕ) ∈ Set.Iio (orderOf g) := by rw [hg]; exact i.isLt
  have h2 : (j : ℕ) ∈ Set.Iio (orderOf g) := by rw [hg]; exact j.isLt
  exact Fin.ext (pow_injOn_Iio_orderOf h1 h2 hij)

/-- **Small sets are always explainable** (Lagrange interpolation): any word agrees with a
polynomial of degree `≤ d` on any set of at most `d + 1` nodes. -/
theorem explainableOn_of_card_le (hg : orderOf g = n) {d : ℕ} {u : Fin n → ZMod p}
    {S : Finset (Fin n)} (hS : S.card ≤ d + 1) : ExplainableOn g d u S := by
  refine ⟨Lagrange.interpolate S (fun i : Fin n => g ^ (i : ℕ)) u, ?_, fun i hi =>
    (Lagrange.eval_interpolate_at_node u (nodes_injOn hg S) hi).symm⟩
  have hdeg := Lagrange.degree_interpolate_lt (r := u) (nodes_injOn hg S)
  rcases eq_or_ne (Lagrange.interpolate S (fun i : Fin n => g ^ (i : ℕ)) u) 0 with h0 | h0
  · rw [h0]; simp
  · have hlt : (Lagrange.interpolate S (fun i : Fin n => g ^ (i : ℕ)) u).natDegree
        < S.card := (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hdeg
    omega

/-- **Uniqueness of low-degree explanations**: two polynomials of degree `≤ d` agreeing on
`d + 1` distinct nodes are equal. -/
theorem explain_unique (hg : orderOf g = n) {d : ℕ} {q q' : Polynomial (ZMod p)}
    (hq : q.natDegree ≤ d) (hq' : q'.natDegree ≤ d) {S : Finset (Fin n)}
    (hcard : d + 1 ≤ S.card)
    (hagree : ∀ i ∈ S, q.eval (g ^ (i : ℕ)) = q'.eval (g ^ (i : ℕ))) : q = q' := by
  have hd : ((d : ℕ) : WithBot ℕ) < (S.card : WithBot ℕ) := by
    exact_mod_cast Nat.lt_of_lt_of_le (Nat.lt_succ_self d) hcard
  exact Polynomial.eq_of_degrees_lt_of_eval_index_eq S (nodes_injOn hg S)
    (lt_of_le_of_lt (Polynomial.natDegree_le_iff_degree_le.mp hq) hd)
    (lt_of_le_of_lt (Polynomial.natDegree_le_iff_degree_le.mp hq') hd) hagree

/-- **The extension lemma**: if every `(d+2)`-subset of `S` is explainable, so is `S`. -/
theorem explainableOn_of_forall_subset (hg : orderOf g = n) {d : ℕ} {u : Fin n → ZMod p}
    {S : Finset (Fin n)} (hcard : d + 1 ≤ S.card)
    (h : ∀ T ⊆ S, T.card = d + 2 → ExplainableOn g d u T) : ExplainableOn g d u S := by
  obtain ⟨P, hPS, hPcard⟩ := Finset.exists_subset_card_eq hcard
  obtain ⟨ℓ, hℓd, hℓ⟩ : ExplainableOn g d u P :=
    explainableOn_of_card_le hg (le_of_eq hPcard)
  refine ⟨ℓ, hℓd, fun x hx => ?_⟩
  by_cases hxP : x ∈ P
  · exact hℓ x hxP
  · obtain ⟨qT, hqTd, hqT⟩ := h (insert x P) (Finset.insert_subset hx hPS)
      (by rw [Finset.card_insert_of_notMem hxP]; omega)
    have hQ : qT = ℓ := explain_unique hg hqTd hℓd (le_of_eq hPcard.symm)
      (fun i hi => by rw [← hqT i (Finset.mem_insert_of_mem hi), ← hℓ i hi])
    rw [← hQ]
    exact hqT x (Finset.mem_insert_self x P)

/-- A non-explainable set of size at least `d + 3` contains a non-explainable
`(d+3)`-subset. -/
theorem exists_nonExpl_subset (hg : orderOf g = n) {d : ℕ} {u : Fin n → ZMod p}
    {S : Finset (Fin n)} (hS : ¬ ExplainableOn g d u S) (hcard : d + 3 ≤ S.card) :
    ∃ S' : Finset (Fin n), S' ⊆ S ∧ S'.card = d + 3 ∧ ¬ ExplainableOn g d u S' := by
  have h2 : ∃ T, T ⊆ S ∧ T.card = d + 2 ∧ ¬ ExplainableOn g d u T := by
    by_contra hcon
    push_neg at hcon
    exact hS (explainableOn_of_forall_subset hg (by omega)
      (fun T hT hTc => hcon T hT hTc))
  obtain ⟨T, hTS, hTcard, hTnot⟩ := h2
  have hex : ∃ x ∈ S, x ∉ T := by
    by_contra hcon
    push_neg at hcon
    have hle := Finset.card_le_card (fun y hy => hcon y hy)
    omega
  obtain ⟨x, hxS, hxT⟩ := hex
  exact ⟨insert x T, Finset.insert_subset hxS hTS,
    by rw [Finset.card_insert_of_notMem hxT]; omega,
    fun hexp => hTnot (explainableOn_mono (Finset.subset_insert x T) hexp)⟩

/-- **The glueing lemma**: in a non-explainable `(d+3)`-set, two distinct points cannot
both have explainable complements — the two interpolants agree on the `d+1` common nodes,
hence are equal, hence explain the whole set. -/
theorem glue_erase (hg : orderOf g = n) {d : ℕ} {u : Fin n → ZMod p}
    {S' : Finset (Fin n)} (hcard : S'.card = d + 3) (hS' : ¬ ExplainableOn g d u S')
    {x y : Fin n} (hx : x ∈ S') (hy : y ∈ S') (hxy : x ≠ y)
    (hex : ExplainableOn g d u (S'.erase x)) (hey : ExplainableOn g d u (S'.erase y)) :
    False := by
  obtain ⟨qx, hqxd, hqx⟩ := hex
  obtain ⟨qy, hqyd, hqy⟩ := hey
  have hycard : ((S'.erase x).erase y).card = d + 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hxy, hy⟩),
      Finset.card_erase_of_mem hx, hcard]
    omega
  have heq : qx = qy := by
    refine explain_unique hg hqxd hqyd (le_of_eq hycard.symm) (fun i hi => ?_)
    have hix : i ∈ S'.erase x := Finset.mem_of_mem_erase hi
    have hiy : i ∈ S'.erase y := Finset.mem_erase.mpr
      ⟨(Finset.mem_erase.mp hi).1, Finset.mem_of_mem_erase hix⟩
    rw [← hqx i hix, ← hqy i hiy]
  refine hS' ⟨qx, hqxd, fun i hi => ?_⟩
  by_cases hix : i = x
  · subst hix
    rw [heq]
    exact hqy i (Finset.mem_erase.mpr ⟨hxy, hi⟩)
  · exact hqx i (Finset.mem_erase.mpr ⟨hix, hi⟩)

open Classical in
/-- **The ownership count**: a non-explainable `(d+3)`-set has at least `d + 2`
points whose complements are non-explainable `(d+2)`-tuples. -/
theorem ownership_card (hg : orderOf g = n) {d : ℕ} {u : Fin n → ZMod p}
    {S' : Finset (Fin n)} (hcard : S'.card = d + 3) (hS' : ¬ ExplainableOn g d u S') :
    d + 2 ≤ (S'.filter (fun x => ¬ ExplainableOn g d u (S'.erase x))).card := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := S')
    (fun x => ExplainableOn g d u (S'.erase x))
  have hle1 : (S'.filter (fun x => ExplainableOn g d u (S'.erase x))).card ≤ 1 := by
    refine Finset.card_le_one.mpr (fun a ha b hb => ?_)
    by_contra hab
    exact glue_erase hg hcard hS' (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1
      hab (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
  omega

/-- **The determination lemma**: a `u₁`-non-explainable tuple on which two combined words
`u₀ + γu₁` and `u₀ + γ'u₁` are both explainable forces `γ = γ'`. -/
theorem scalar_eq_of_shared_tuple (hg : orderOf g = n) {d : ℕ}
    {u₀ u₁ : Fin n → ZMod p} {T : Finset (Fin n)}
    (hT : ¬ ExplainableOn g d u₁ T) {γ γ' : ZMod p}
    (h1 : ExplainableOn g d (fun i => u₀ i + γ * u₁ i) T)
    (h2 : ExplainableOn g d (fun i => u₀ i + γ' * u₁ i) T) : γ = γ' := by
  by_contra hne
  obtain ⟨q, hqd, hq⟩ := h1
  obtain ⟨q', hqd', hq'⟩ := h2
  have hγ : γ - γ' ≠ 0 := sub_ne_zero.mpr hne
  refine hT ⟨Polynomial.C (γ - γ')⁻¹ * (q - q'), ?_, fun i hi => ?_⟩
  · calc (Polynomial.C (γ - γ')⁻¹ * (q - q')).natDegree
        ≤ (q - q').natDegree := Polynomial.natDegree_C_mul_le _ _
    _ ≤ max q.natDegree q'.natDegree := Polynomial.natDegree_sub_le q q'
    _ ≤ d := max_le hqd hqd'
  · have e1 := hq i hi
    have e2 := hq' i hi
    have hsub : (γ - γ') * u₁ i
        = q.eval (g ^ (i : ℕ)) - q'.eval (g ^ (i : ℕ)) := by
      rw [← e1, ← e2]; ring
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, ← hsub,
      inv_mul_cancel_left₀ hγ]

/-- **The criterion collapse**: at a bad scalar's witness, the direction row `u₁` is not
explainable — otherwise `q_w − γ·q₁` and `q₁` jointly explain the stack. -/
theorem not_expl_dir_of_witness {d : ℕ} {u₀ u₁ : Fin n → ZMod p} {γ : ZMod p}
    {S : Finset (Fin n)}
    (hwC : ∃ w ∈ evalCode g n d, ∀ i ∈ S, w i = u₀ i + γ • u₁ i)
    (hno : ¬ pairJointAgreesOn (evalCode g n d) S u₀ u₁) :
    ¬ ExplainableOn g d u₁ S := by
  rintro ⟨q₁, hq₁d, hq₁⟩
  obtain ⟨w, ⟨qw, hqwd, hqw⟩, hagree⟩ := hwC
  refine hno ⟨fun i => (qw - Polynomial.C γ * q₁).eval (g ^ (i : ℕ)),
    ⟨qw - Polynomial.C γ * q₁, ?_, fun i => rfl⟩,
    fun i => q₁.eval (g ^ (i : ℕ)), ⟨q₁, hq₁d, fun i => rfl⟩,
    fun i hi => ⟨?_, (hq₁ i hi).symm⟩⟩
  · calc (qw - Polynomial.C γ * q₁).natDegree
        ≤ max qw.natDegree (Polynomial.C γ * q₁).natDegree :=
          Polynomial.natDegree_sub_le _ _
    _ ≤ d := max_le hqwd (le_trans (Polynomial.natDegree_C_mul_le _ _) hq₁d)
  · show (qw - Polynomial.C γ * q₁).eval (g ^ (i : ℕ)) = u₀ i
    have h1 := hagree i hi
    have h2 := hqw i
    have h3 := hq₁ i hi
    rw [smul_eq_mul] at h1
    rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, ← h2, ← h3, h1]
    ring

/-! ## The tuple-ownership count -/

open Classical in
/-- **The tuple-ownership bound.**  For the degree-`d` evaluation code at agreement
threshold above `d + 2`, every stack has at most `C(n, d+2)/(d+2)` bad scalars: each bad
scalar owns at least `d + 2` non-degenerate `(d+2)`-tuples inside its witness, distinct
bad scalars own disjoint tuple sets, and only `C(n, d+2)` tuples exist.  Stated
multiplicatively to avoid `ℕ`-division. -/
theorem march_badScalars_card_mul_le (hg : orderOf g = n) {d : ℕ} {δ : ℝ≥0}
    (hδ : ((d + 2 : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0))
    (u₀ u₁ : Fin n → ZMod p) :
    (Finset.univ.filter (fun γ : ZMod p =>
        mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ u₀ u₁ γ)).card * (d + 2)
      ≤ n.choose (d + 2) := by
  set B := Finset.univ.filter (fun γ : ZMod p =>
      mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ u₀ u₁ γ) with hBdef
  -- Step 1: every bad scalar has a non-explainable (d+3)-set carrying its explanation.
  have hwit : ∀ γ ∈ B, ∃ S' : Finset (Fin n), S'.card = d + 3 ∧
      ¬ ExplainableOn g d u₁ S' ∧
      ExplainableOn g d (fun i => u₀ i + γ * u₁ i) S' := by
    intro γ hγ
    obtain ⟨S, hScard, hwC, hnojoint⟩ := (Finset.mem_filter.mp hγ).2
    have hcard : d + 3 ≤ S.card := by
      have h2 : ((d + 2 : ℕ) : ℝ≥0) < (S.card : ℝ≥0) := lt_of_lt_of_le hδ hScard
      have h2' : d + 2 < S.card := by exact_mod_cast h2
      omega
    have hnotexpl : ¬ ExplainableOn g d u₁ S := not_expl_dir_of_witness hwC hnojoint
    obtain ⟨S', hS'S, hS'card, hS'not⟩ := exists_nonExpl_subset hg hnotexpl hcard
    obtain ⟨w, ⟨qw, hqwd, hqw⟩, hagree⟩ := hwC
    refine ⟨S', hS'card, hS'not, ⟨qw, hqwd, fun i hi => ?_⟩⟩
    show u₀ i + γ * u₁ i = qw.eval (g ^ (i : ℕ))
    have h1 := hagree i (hS'S hi)
    rw [smul_eq_mul] at h1
    rw [← h1]
    exact hqw i
  choose Sf hSfcard hSfnot hSfcomb using hwit
  -- The tuple family of a bad scalar: complements of the non-explainable-erase points.
  set Φ : {x // x ∈ B} → Finset (Finset (Fin n)) := fun γ =>
    ((Sf γ.1 γ.2).filter
      (fun x => ¬ ExplainableOn g d u₁ ((Sf γ.1 γ.2).erase x))).image
      (fun x => (Sf γ.1 γ.2).erase x) with hΦdef
  -- Membership facts for Φ.
  have hmemΦ : ∀ (γ : {x // x ∈ B}) (T : Finset (Fin n)), T ∈ Φ γ →
      ¬ ExplainableOn g d u₁ T ∧
      ExplainableOn g d (fun i => u₀ i + γ.1 * u₁ i) T ∧ T.card = d + 2 := by
    intro γ T hT
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨hxS, hxnot⟩ := Finset.mem_filter.mp hx
    refine ⟨hxnot, explainableOn_mono (Finset.erase_subset _ _) (hSfcomb γ.1 γ.2), ?_⟩
    rw [Finset.card_erase_of_mem hxS, hSfcard γ.1 γ.2]
    omega
  -- Step 2: each bad scalar owns at least d + 2 tuples.
  have hP : ∀ γ : {x // x ∈ B}, d + 2 ≤ (Φ γ).card := by
    intro γ
    have hinj : Set.InjOn (fun x => (Sf γ.1 γ.2).erase x)
        ↑((Sf γ.1 γ.2).filter
          (fun x => ¬ ExplainableOn g d u₁ ((Sf γ.1 γ.2).erase x))) :=
      (Finset.erase_injOn _).mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))
    calc d + 2 ≤ ((Sf γ.1 γ.2).filter
          (fun x => ¬ ExplainableOn g d u₁ ((Sf γ.1 γ.2).erase x))).card :=
        ownership_card hg (hSfcard γ.1 γ.2) (hSfnot γ.1 γ.2)
    _ = (Φ γ).card := (Finset.card_image_of_injOn hinj).symm
  -- Step 3: tuple sets of distinct bad scalars are disjoint.
  have hdisj : ∀ γ₁ ∈ B.attach, ∀ γ₂ ∈ B.attach, γ₁ ≠ γ₂ → Disjoint (Φ γ₁) (Φ γ₂) := by
    intro γ₁ _ γ₂ _ hne
    rw [Finset.disjoint_left]
    intro T hT1 hT2
    obtain ⟨hnot1, hcomb1, _⟩ := hmemΦ γ₁ T hT1
    obtain ⟨_, hcomb2, _⟩ := hmemΦ γ₂ T hT2
    exact hne (Subtype.ext (scalar_eq_of_shared_tuple hg hnot1 hcomb1 hcomb2))
  -- Step 4: assemble through the tuple universe.
  have hbig : B.attach.card * (d + 2) ≤ (B.attach.biUnion Φ).card := by
    rw [Finset.card_biUnion hdisj]
    calc B.attach.card * (d + 2) = ∑ _γ ∈ B.attach, (d + 2) := by
          rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun γ _ => hP γ)
  have hsub : B.attach.biUnion Φ ⊆ Finset.powersetCard (d + 2) Finset.univ := by
    intro T hT
    obtain ⟨γ, _, hTΦ⟩ := Finset.mem_biUnion.mp hT
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (hmemΦ γ T hTΦ).2.2⟩
  calc B.card * (d + 2) = B.attach.card * (d + 2) := by rw [Finset.card_attach]
  _ ≤ (B.attach.biUnion Φ).card := hbig
  _ ≤ (Finset.powersetCard (d + 2) (Finset.univ : Finset (Fin n))).card :=
      Finset.card_le_card hsub
  _ = n.choose (d + 2) := by
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

open Classical in
/-- **The march `ε_mca` bound**: at agreement threshold above `d + 2`, the MCA error of
the degree-`d` evaluation code is at most `(C(n,d+2)/(d+2))/p` — uniformly in `δ`. -/
theorem march_epsMCA_le (hg : orderOf g = n) {d : ℕ} {δ : ℝ≥0}
    (hδ : ((d + 2 : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0)) :
    epsMCA (F := ZMod p) (A := ZMod p) (evalCode g n d) δ
      ≤ ((n.choose (d + 2) / (d + 2) : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Nonempty (ZMod p) := ⟨0⟩
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card, ZMod.card p]
  simp only [ENNReal.coe_natCast]
  gcongr
  have h4 := march_badScalars_card_mul_le (g := g) hg hδ (u 0) (u 1)
  have hle : (Finset.filter (fun γ : ZMod p =>
      mcaEvent (F := ZMod p) (A := ZMod p) (evalCode g n d) δ (u 0) (u 1) γ)
      Finset.univ).card ≤ n.choose (d + 2) / (d + 2) :=
    (Nat.le_div_iff_mul_le (by omega)).mpr h4
  exact_mod_cast hle

/-! ## The `InteriorCeiling` discharge at `m = 1`, every `r ≥ 2` -/

/-- **The interior ceiling holds unconditionally at every `m = 1` slice:** for every
`r ≥ 2`, every `ε* ≥ (C(n,r)/r)/p`, and every `δ` below the KKH26 ceiling `1 − r/2^μ`,
the agreement threshold exceeds `r`, so the tuple-ownership bound applies. -/
theorem interiorCeiling_march {μ r : ℕ} (hr2 : 2 ≤ r) (hn : n = 2 ^ μ)
    (hg : orderOf g = n) (εstar : ℝ≥0∞)
    (hband : ((n.choose r / r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) ≤ εstar) :
    InteriorCeiling p n g μ 1 r εstar := by
  intro δ hδ
  have hcode : (r - 2) * 1 = r - 2 := mul_one _
  rw [hcode]
  have hd2 : r - 2 + 2 = r := by omega
  have harith : ((r - 2 + 2 : ℕ) : ℝ≥0) < (1 - δ) * (Fintype.card (Fin n) : ℝ≥0) := by
    rw [hd2]
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
      rw [Fintype.card_fin, hn]
      push_cast
      ring
    rw [hcard]
    exact hmul
  have h := march_epsMCA_le (g := g) (d := r - 2) (δ := δ) hg harith
  rw [hd2] at h
  exact le_trans h hband

/-! ## Band nonemptiness -/

/-- The descending-factorial core of band nonemptiness:
`(2m)·(2m−1)⋯(2m−r+1) < r · 2^r · m·(m−1)⋯(m−r+1)` whenever `2 ≤ r` and
`r² ≤ 2m + 1`. -/
theorem march_band_lt : ∀ r : ℕ, 2 ≤ r → ∀ m : ℕ, r * r ≤ 2 * m + 1 →
    (2 * m).descFactorial r < r * (2 ^ r * m.descFactorial r) := by
  intro r
  induction r with
  | zero => intro h; exact absurd h (by norm_num)
  | succ r ih =>
    intro hr2 m hm
    rcases Nat.lt_or_ge r 2 with hr | hr
    · -- base case: r + 1 = 2
      have hr1 : r = 1 := by omega
      subst hr1
      obtain ⟨b, rfl⟩ : ∃ b, m = b + 2 := ⟨m - 2, by omega⟩
      rw [Nat.descFactorial_succ, Nat.descFactorial_one,
        Nat.descFactorial_succ, Nat.descFactorial_one]
      have h1 : 2 * (b + 2) - 1 = 2 * b + 3 := by omega
      have h2 : b + 2 - 1 = b + 1 := by omega
      rw [h1, h2]
      have h4 : (2 : ℕ) ^ 2 = 4 := by norm_num
      rw [h4]
      nlinarith [sq_nonneg b]
    · -- inductive step: 2 ≤ r
      have hmr' : r * r ≤ 2 * m + 1 := by nlinarith
      have hrm : r ≤ m := by nlinarith
      obtain ⟨a, rfl⟩ : ∃ a, m = r + a := ⟨m - r, by omega⟩
      have IH := ih hr (r + a) hmr'
      -- key linear comparison: (r + 2a) * r ≤ (r+1) * (2a), from r² ≤ 2a
      have hkey : (r + 2 * a) * r ≤ (r + 1) * (2 * a) := by nlinarith
      have h2m : 2 * (r + a) - r = r + 2 * a := by omega
      have hma : r + a - r = a := by omega
      rw [Nat.descFactorial_succ, Nat.descFactorial_succ, h2m, hma]
      calc (r + 2 * a) * (2 * (r + a)).descFactorial r
          < (r + 2 * a) * (r * (2 ^ r * (r + a).descFactorial r)) :=
            mul_lt_mul_of_pos_left IH (by omega)
      _ = ((r + 2 * a) * r) * (2 ^ r * (r + a).descFactorial r) := by ring
      _ ≤ ((r + 1) * (2 * a)) * (2 ^ r * (r + a).descFactorial r) :=
            Nat.mul_le_mul_right _ hkey
      _ = (r + 1) * (2 ^ (r + 1) * (a * (r + a).descFactorial r)) := by ring

/-- **Band nonemptiness**: the tuple bound `C(2^μ, r)/r` sits strictly below the KKH26
ceiling count `2^r·C(2^{μ−1}, r)` whenever `r² ≤ 2^μ + 1`. -/
theorem march_band_nonempty {r μ : ℕ} (hr2 : 2 ≤ r) (hμ : 1 ≤ μ)
    (hrn : r * r ≤ 2 ^ μ + 1) :
    (2 ^ μ).choose r / r < 2 ^ r * (2 ^ (μ - 1)).choose r := by
  have hm : 2 ^ μ = 2 * 2 ^ (μ - 1) := by
    conv_lhs => rw [show μ = (μ - 1) + 1 by omega]
    rw [pow_succ]
    ring
  have key : (2 * 2 ^ (μ - 1)).descFactorial r
      < r * (2 ^ r * (2 ^ (μ - 1)).descFactorial r) :=
    march_band_lt r hr2 (2 ^ (μ - 1)) (by rw [← hm]; exact hrn)
  rw [Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose] at key
  have hkey2 : r.factorial * ((2 * 2 ^ (μ - 1)).choose r)
      < r.factorial * (r * (2 ^ r * (2 ^ (μ - 1)).choose r)) := by
    calc r.factorial * ((2 * 2 ^ (μ - 1)).choose r)
        < r * (2 ^ r * (r.factorial * (2 ^ (μ - 1)).choose r)) := key
    _ = r.factorial * (r * (2 ^ r * (2 ^ (μ - 1)).choose r)) := by ring
  have hlt := Nat.lt_of_mul_lt_mul_left hkey2
  rw [Nat.div_lt_iff_lt_mul (by omega : 0 < r), hm]
  calc (2 * 2 ^ (μ - 1)).choose r < r * (2 ^ r * (2 ^ (μ - 1)).choose r) := hlt
  _ = 2 ^ r * (2 ^ (μ - 1)).choose r * r := by ring

/-! ## THE PIN: the ceiling march -/

/-- **THE CEILING MARCH.**  For every `r ≥ 2` and the degree-`(r−2)` code (dimension
`r−1`) on the smooth `2^μ`-point domain, and every `ε*` in the band
`[(C(n,r)/r)/p, (2^r·C(2^{μ−1},r))/p)`:

  `mcaDeltaStar(evalCode g (2^μ) (r−2), ε*) = 1 − r/2^μ`

with **no open obligation**: the good side is the tuple-ownership incidence bound, the
bad side is the in-tree KKH26 witness spread. -/
theorem kkh26_march_deltaStar_pin {μ r : ℕ} (hμ : 1 ≤ μ) (hr2 : 2 ≤ r)
    (hr : r ≤ 2 ^ (μ - 1)) {n : ℕ} (hn : n = 2 ^ μ) [NeZero n]
    (hg : orderOf g = 2 ^ μ)
    (hp : ((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) < p) (εstar : ℝ≥0∞)
    (hlo : ((n.choose r / r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞) ≤ εstar)
    (hhi : εstar < ((2 ^ r * (2 ^ (μ - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞)) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n (r - 2)) εstar
      = 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) := by
  have hgn : orderOf g = n := by rw [hn]; exact hg
  have h := kkh26_deltaStar_pin_of_interior_ceiling (p := p) (n := n) (μ := μ) (m := 1)
    (r := r) (g := g) hμ le_rfl (by rw [hn, mul_one]) (by rw [mul_one]; exact hg) hp
    hr2 hr εstar hhi (interiorCeiling_march hr2 hn hgn εstar hlo)
  rwa [mul_one] at h

/-- **The canonical march pin:** at `ε* = (C(n,r)/r)/p` itself the pin fires whenever
`r² ≤ 2^μ + 1` — band membership is definitional on the left and `march_band_nonempty`
on the right. -/
theorem kkh26_march_deltaStar_pin_canonical {μ r : ℕ} (hμ : 1 ≤ μ) (hr2 : 2 ≤ r)
    (hrn : r * r ≤ 2 ^ μ + 1) {n : ℕ} (hn : n = 2 ^ μ) [NeZero n]
    (hg : orderOf g = 2 ^ μ)
    (hp : ((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) < p) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p) (evalCode g n (r - 2))
        (((n.choose r / r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞))
      = 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) := by
  -- r ≤ 2^(μ−1) from r² ≤ 2^μ + 1
  have hr : r ≤ 2 ^ (μ - 1) := by
    have h2r : 2 * r ≤ r * r := Nat.mul_le_mul_right r hr2
    have h2 : 2 * r ≤ 2 ^ μ + 1 := le_trans h2r hrn
    have hp2 : 2 * 2 ^ (μ - 1) = 2 ^ μ := by
      conv_rhs => rw [show μ = (μ - 1) + 1 by omega]
      rw [pow_succ]
      ring
    omega
  refine kkh26_march_deltaStar_pin hμ hr2 hr hn hg hp _ le_rfl ?_
  have hp0 : (p : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpt : (p : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top p
  have hlt' : ((n.choose r / r : ℕ) : ℝ≥0∞)
      < ((2 ^ r * (2 ^ (μ - 1)).choose r : ℕ) : ℝ≥0∞) := by
    rw [hn]
    exact_mod_cast march_band_nonempty hr2 hμ hrn
  exact ENNReal.div_lt_div_right hp0 hpt hlt'

/-- **Beyond Johnson (squared form):** whenever `r² < (r−1)·2^μ`, the ceiling's distance
to `1` is strictly below the Johnson distance `√ρ` for the rate `ρ = (r−1)/2^μ` of the
dimension-`(r−1)` code — stated square-free as `(r/2^μ)² < (r−1)/2^μ`.  Hence the pinned
radius `1 − r/2^μ` lies strictly beyond the Johnson radius `1 − √ρ`. -/
theorem march_ceiling_beyond_johnson_sq {μ r : ℕ} (h : r * r < (r - 1) * 2 ^ μ) :
    ((r : ℝ≥0) / (2 : ℝ≥0) ^ μ) ^ 2 < ((r : ℝ≥0) - 1) / (2 : ℝ≥0) ^ μ := by
  have hpow0 : (0 : ℝ≥0) < (2 : ℝ≥0) ^ μ := by positivity
  rw [div_pow, div_lt_div_iff₀ (by positivity) hpow0]
  have hcast : (r : ℝ≥0) * (r : ℝ≥0) < ((r : ℝ≥0) - 1) * (2 : ℝ≥0) ^ μ := by
    exact_mod_cast h
  calc (r : ℝ≥0) ^ 2 * (2 : ℝ≥0) ^ μ
      = ((r : ℝ≥0) * (r : ℝ≥0)) * (2 : ℝ≥0) ^ μ := by ring
  _ < (((r : ℝ≥0) - 1) * (2 : ℝ≥0) ^ μ) * (2 : ℝ≥0) ^ μ :=
      mul_lt_mul_of_pos_right hcast hpow0
  _ = ((r : ℝ≥0) - 1) * ((2 : ℝ≥0) ^ μ) ^ 2 := by ring

/-! ## Rungs the glueing law opens or widens (instance arithmetic)

`Nat.choose` literals are computed through the descending factorial
(`Nat.choose` itself is Pascal-recursive — kernel-infeasible at these sizes). -/

/-- **The `(r, μ) = (5, 4)` band, glueing-sharpened**: the canonical edge drops from the
landed pair-law `1456` to `873` — the widest proven band at the dimension-four pin. -/
theorem march_band_at_r5_mu4 : (2 ^ 4).choose 5 / 5 < 2 ^ 5 * (2 ^ 3).choose 5 := by
  have h1 : (16 : ℕ).choose 5 = 4368 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  have h2 : (8 : ℕ).choose 5 = 56 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  show (16 : ℕ).choose 5 / 5 < 2 ^ 5 * (8 : ℕ).choose 5
  rw [h1, h2]
  norm_num

/-- **The `(r, μ) = (10, 5)` past-`√n` rung**: the glueing/sharp floor
`C(32,10)/10 = 6451224` clears the ceiling spectrum `2^10·C(16,10) = 8200192`, while the
pair-law floor `2·C(32,10)/11 = 11729498` does not.  The dimension-9 (rate `9/32`) code
joins the unconditional in-window family at `δ* = 11/16`, beyond Johnson
(`10·10 < 9·2^5`). -/
theorem march_opens_r10_mu5 :
    (2 ^ 5).choose 10 / 10 < 2 ^ 10 * (2 ^ 4).choose 10 ∧
      ¬ (2 * (2 ^ 5).choose 10 / 11 < 2 ^ 10 * (2 ^ 4).choose 10) := by
  have h1 : (32 : ℕ).choose 10 = 64512240 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  have h2 : (16 : ℕ).choose 10 = 8008 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]; decide
  constructor
  · show (32 : ℕ).choose 10 / 10 < 2 ^ 10 * (16 : ℕ).choose 10
    rw [h1, h2]
    norm_num
  · show ¬ (2 * (32 : ℕ).choose 10 / 11 < 2 ^ 10 * (16 : ℕ).choose 10)
    rw [h1, h2]
    norm_num

end ArkLib.ProximityGap.KKH26CeilingMarch

/-! ## The concrete instantiation: `δ* = 5/8` for the dimension-TWO code at the NTT prime -/

namespace ArkLib.ProximityGap.KKH26CeilingMarch

section Concrete

local instance fact_prime_12289 : Fact (Nat.Prime 12289) := ⟨by norm_num⟩

/-- **The first unconditional in-window `δ*` pin for a code of dimension ≥ 2:**
`δ* = 5/8` exactly, for the dimension-two code (affine polynomials, degree ≤ 1) on the
8-point smooth domain `⟨4043⟩ ⊆ F₁₂₂₈₉ˣ` at `ε* = 18/12289`.  The rate is `ρ = 1/4`, the
Johnson radius is `1 − 1/2 = 1/2 < 5/8`, capacity `3/4 > 5/8`: strictly inside the open
window, machine-checked end to end. -/
theorem deltaStar_pin_F12289_dimTwo :
    mcaDeltaStar (F := ZMod 12289) (A := ZMod 12289)
        (evalCode (4043 : ZMod 12289) 8 1) ((18 : ℝ≥0∞) / (12289 : ℝ≥0∞))
      = 5 / 8 := by
  haveI : NeZero (8 : ℕ) := ⟨by norm_num⟩
  have h := kkh26_march_deltaStar_pin_canonical (p := 12289) (μ := 3) (r := 3)
    (g := (4043 : ZMod 12289)) (n := 8) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ArkLib.ProximityGap.KKH26DimOne.orderOf_4043 (by norm_num)
  have e0 : (Nat.choose 8 3 / 3 : ℕ) = 18 := by decide
  have e1 : ((Nat.choose 8 3 / 3 : ℕ) : ℝ≥0∞) = (18 : ℝ≥0∞) := by rw [e0]; norm_num
  have e2 : ((12289 : ℕ) : ℝ≥0∞) = (12289 : ℝ≥0∞) := by norm_num
  have e3 : (1 : ℝ≥0) - (3 : ℝ≥0) / ((2 : ℝ≥0) ^ 3) = 5 / 8 := by
    have hd : (3 : ℝ≥0) / ((2 : ℝ≥0) ^ 3) = 3 / 8 := by norm_num
    rw [hd]
    refine tsub_eq_of_eq_add ?_
    norm_num
  have e4 : ((3 : ℕ) : ℝ≥0) = (3 : ℝ≥0) := by norm_num
  rw [show (3 : ℕ) - 2 = 1 by norm_num] at h
  rw [e1, e2, e4, e3] at h
  exact h

end Concrete

end ArkLib.ProximityGap.KKH26CeilingMarch

/-! ## Axiom audit — kernel-clean. -/
#print axioms ArkLib.ProximityGap.KKH26CeilingMarch.march_badScalars_card_mul_le
#print axioms ArkLib.ProximityGap.KKH26CeilingMarch.march_epsMCA_le
#print axioms ArkLib.ProximityGap.KKH26CeilingMarch.interiorCeiling_march
#print axioms ArkLib.ProximityGap.KKH26CeilingMarch.march_band_nonempty
#print axioms ArkLib.ProximityGap.KKH26CeilingMarch.kkh26_march_deltaStar_pin
#print axioms ArkLib.ProximityGap.KKH26CeilingMarch.kkh26_march_deltaStar_pin_canonical
#print axioms ArkLib.ProximityGap.KKH26CeilingMarch.march_band_at_r5_mu4
#print axioms ArkLib.ProximityGap.KKH26CeilingMarch.march_opens_r10_mu5
#print axioms ArkLib.ProximityGap.KKH26CeilingMarch.deltaStar_pin_F12289_dimTwo
