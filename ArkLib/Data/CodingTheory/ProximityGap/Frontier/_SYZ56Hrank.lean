/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ18PairJointSelfExclusion
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ22StripBridge

/-!
# SYZ56 — the `hrank` residual via cross-witness chaining: a NO-GO

SYZ43 (`realizabilityCore_of_overBudget_stack` / `realizabilityCore_of_mcaEvent_witnesses`) pinned
the sole surviving analytic content of the strip's realizability obligation to a single scalar
equality — the union-rank **lower bound**

> `hrank` : `finrank (span (range φ)) = 2 (Ucard − k)`

on the G87 bridge functionals `φ`.  G87's `plantable_span_cap` supplies only the *upper* bracket
`finrank (span) + 1 ≤ 2(n − k)`; SYZ22 (`block_source_dim_eq_shortening`) proved each per-witness
block is a **full** basis of its `S`-anchored punctured dual.  Hence

> `span (range φ)` is the join `⨆ᵢ (Sᵢ-anchored doubled shortening)`,

so `hrank` is exactly **union-generation over the witness-support family** `{Sᵢ}` — the `mcaEvent`
agreement sets, each of size `≥ t`, pairwise-distinct (SYZ18).

## The proposed route (verify): cross-witness chaining forces `u₁` near a codeword

The attempted discharge:

* **(a) cross-witness algebra.**  On the pairwise overlap `Sᵢ ∩ Sⱼ` of two witnesses with distinct
  scalars `γᵢ ≠ γⱼ`, the differenced lines give `(γᵢ − γⱼ)·u₁ = cᵢ − cⱼ`, so `u₁` **agrees with a
  codeword** `(γᵢ − γⱼ)⁻¹ • (cᵢ − cⱼ) ∈ C` on all of `Sᵢ ∩ Sⱼ`.  We prove this
  (`cross_witness_u1_codeword_agreement`) — it is a direct corollary of SYZ18's
  `shared_witness_forces_pairJoint` applied to the intersection.  **TRUE.**
* **(b) chaining.**  If a large witness family (over-budget) made these codeword-agreement regions
  glue into one region of size `≥ k`, MDS rigidity would force `u₁` globally close to a codeword,
  landing the stack in the near-degenerate *merged branch* — discharging `hrank` off the strip.

## Verdict: (a) holds; (b) does NOT close — the band obstruction recurs one level up

The forced single-codeword agreement regions are the **pairwise** overlaps `Sᵢ ∩ Sⱼ`, of size
`≥ 2t − n` (`cross_witness_region_card_ge`).  To fuse the pairwise codewords `cᵢⱼ`, `cᵢₗ` into one
(so `u₁` agrees with a *single* codeword on a larger set), MDS rigidity needs them to coincide, which
needs them to agree on `≥ k` common points — i.e. an `m`-fold intersection of size `≥ k`.  But the
minimal `m`-fold intersection is `m·t − (m−1)·n = n − m(n − t)`, which is **decreasing in `m`**
(`mfold_intersection_antitone`): the largest guaranteed forced region is the *pairwise* one at
`m = 2`.  In the rate-`1/2` strip (`k = n/2`, `t < 3n/4`, i.e. `2t < n + k`) that pairwise region is
already `< k` (`pairwise_region_lt_k`), and every deeper merge only shrinks it
(`chain_region_lt_k`).  So no chain of cross-witness merges ever certifies a single-codeword
agreement region of size `≥ k`: **`u₁` is never forced near a codeword by cross-witness chaining**,
and `hrank` does **not** discharge on this route.  The band shape that blocks the strip at scale `t`
reappears verbatim at the witness-overlap scale.

This is an honest **NO-GO**: the cross-witness lemma is genuine algebra, but the chaining that would
turn it into a `hrank` discharge is arithmetically obstructed inside the strip.  `hrank` remains an
open, independent realizability residual (separate from `uniformSylvester`), exactly as SYZ42/SYZ43
recorded.  No `δ*` gain.

Axiom-clean; `#print axioms` at the bottom.  No `sorry`, no `native_decide`.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.SYZ56

open Finset

/-! ## 1. (a) The cross-witness algebra — `u₁` codeword-agrees on pairwise overlaps -/

section CrossWitness

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F]
variable {A : Type} [AddCommGroup A] [Module F A]

/-- **(a) Cross-witness codeword agreement (pure algebra).**  Two `mcaEvent` witnesses for a stack
`(u₀, u₁)` — codewords `cᵢ, cⱼ ∈ C` explaining the lines `u₀ + γᵢ·u₁` on `Sᵢ` and `u₀ + γⱼ·u₁` on
`Sⱼ`, with **distinct** scalars `γᵢ ≠ γⱼ` — force `u₁` to agree with a *single codeword of `C`* on
the entire pairwise overlap `Sᵢ ∩ Sⱼ`.  (And simultaneously `u₀` agrees with a codeword there.)

This is the exact algebraic content the cross-witness route rests on; it follows from SYZ18's
`shared_witness_forces_pairJoint` applied to the set `Sᵢ ∩ Sⱼ`, on which both witnesses hold. -/
theorem cross_witness_u1_codeword_agreement
    (C : Submodule F (ι → A)) {Si Sj : Finset ι} {u₀ u₁ : ι → A} {γi γj : F}
    (hne : γi ≠ γj)
    (hi : ∃ c ∈ C, ∀ x ∈ Si, c x = u₀ x + γi • u₁ x)
    (hj : ∃ c ∈ C, ∀ x ∈ Sj, c x = u₀ x + γj • u₁ x) :
    ∃ v₁ ∈ C, ∀ x ∈ Si ∩ Sj, v₁ x = u₁ x := by
  -- Restrict both witnesses to the overlap and invoke SYZ18's pencil inversion.
  have h0 : ∃ w ∈ C, ∀ x ∈ Si ∩ Sj, w x = u₀ x + γi • u₁ x := by
    obtain ⟨c, hcC, hc⟩ := hi
    exact ⟨c, hcC, fun x hx => hc x (Finset.mem_inter.mp hx).1⟩
  have h1 : ∃ w ∈ C, ∀ x ∈ Si ∩ Sj, w x = u₀ x + γj • u₁ x := by
    obtain ⟨c, hcC, hc⟩ := hj
    exact ⟨c, hcC, fun x hx => hc x (Finset.mem_inter.mp hx).2⟩
  obtain ⟨v₀, hv₀C, v₁, hv₁C, hpair⟩ :=
    ProximityGap.SYZ18.shared_witness_forces_pairJoint C hne h0 h1
  exact ⟨v₁, hv₁C, fun x hx => (hpair x hx).2⟩

/-- **The forced agreement region is the pairwise overlap, of size `≥ 2t − n`.**  Two witness
supports of size `t` in an `n`-element universe overlap in at least `2t − n` positions — the size of
the region on which `(a)` pins `u₁` to a single codeword. -/
theorem cross_witness_region_card_ge {Si Sj : Finset ι} {t : ℕ}
    (hi : Si.card = t) (hj : Sj.card = t) :
    2 * t - Fintype.card ι ≤ (Si ∩ Sj).card := by
  have hunion : (Si ∪ Sj).card ≤ Fintype.card ι := by
    simpa using Finset.card_le_univ (Si ∪ Sj)
  have hce : (Si ∪ Sj).card + (Si ∩ Sj).card = Si.card + Sj.card :=
    Finset.card_union_add_card_inter Si Sj
  rw [hi, hj] at hce
  omega

end CrossWitness

/-! ## 2. (b)/(c) The arithmetic NO-GO — the merge escalation stays below `k` -/

section Escalation

/-- The minimal `m`-fold intersection of `m` witness supports of size `t` in a universe of size `n`,
as an integer: `m·t − (m−1)·n`.  (For `m = 2` this is the pairwise `2t − n`.) -/
def mfoldMin (n t m : ℕ) : ℤ := (m : ℤ) * t - (m - 1) * n

/-- **The escalation is antitone in `m`.**  If witness supports have size `t ≤ n`, then the minimal
`m`-fold overlap `n − m(n − t)` only *shrinks* as more supports are intersected: the largest
guaranteed single-codeword agreement region a cross-witness merge can produce is the **pairwise**
one, at `m = 2`.  There is no gain from chaining through more witnesses. -/
theorem mfoldMin_antitone {n t : ℕ} (htn : t ≤ n) {m m' : ℕ} (hm : m ≤ m') :
    mfoldMin n t m' ≤ mfoldMin n t m := by
  unfold mfoldMin
  have hnt : (0 : ℤ) ≤ (n : ℤ) - t := by
    have : (t : ℤ) ≤ n := by exact_mod_cast htn
    linarith
  have hmm : (m : ℤ) ≤ m' := by exact_mod_cast hm
  -- m*t - (m-1)*n = n - m*(n-t); larger m ⇒ subtract more.
  nlinarith [hnt, hmm]

/-- **Pairwise regions are below `k` in the strip.**  In the rate-`1/2` decisive strip the agreement
threshold obeys `2t < n + k` (equivalently `t < 3n/4` at `k = n/2`).  Then the pairwise overlap
`2t − n < k`: even the *largest* forced single-codeword agreement region falls strictly short of the
MDS rigidity threshold `k`. -/
theorem pairwise_region_lt_k {n t k : ℕ} (hstrip : 2 * t < n + k) :
    mfoldMin n t 2 < (k : ℤ) := by
  unfold mfoldMin
  have : (2 * t : ℤ) < n + k := by exact_mod_cast hstrip
  push_cast
  linarith

/-- **(b)/(c) NO-GO: no cross-witness merge reaches the rigidity threshold `k`.**  Combining the two
facts: for supports of size `t ≤ n` in the strip (`2t < n + k`), the minimal `m`-fold intersection is
`< k` for **every** `m ≥ 2`.  Hence no chain of cross-witness codeword-agreement merges can certify a
single-codeword agreement region of size `≥ k`, so MDS rigidity never fires and `u₁` is never forced
near a codeword.  The `hrank` union-rank lower bound is *not* discharged by cross-witness chaining. -/
theorem chain_region_lt_k {n t k m : ℕ} (htn : t ≤ n) (hm : 2 ≤ m) (hstrip : 2 * t < n + k) :
    mfoldMin n t m < (k : ℤ) :=
  lt_of_le_of_lt (mfoldMin_antitone htn hm) (pairwise_region_lt_k hstrip)

end Escalation

/-! ## 3. The honest verdict, as a `Prop`

The cross-witness route is captured by the predicate "some chain of `m ≥ 2` witnesses forces `u₁`
onto a single codeword over a size-`≥ k` region."  Section 2 shows the *combinatorial certificate*
that predicate would need — an `m`-fold overlap of size `≥ k` — is arithmetically unavailable in the
strip.  We record the two implications side by side. -/

section Verdict

/-- **The chaining hypothesis is combinatorially blocked in the strip.**  There is no `m ≥ 2` for
which the guaranteed `m`-fold witness overlap reaches the MDS rigidity threshold `k`, when the
supports live in the strip (`t ≤ n`, `2t < n + k`).  Equivalently: the cross-witness algebra of
Section 1 pins `u₁` only on regions of size `< k`, never enough to force a near-codeword. -/
theorem no_rigidity_certificate_in_strip {n t k : ℕ} (htn : t ≤ n) (hstrip : 2 * t < n + k) :
    ∀ m, 2 ≤ m → mfoldMin n t m < (k : ℤ) :=
  fun _ hm => chain_region_lt_k htn hm hstrip

/-- **Sanity: the strip hypothesis is exactly `t < 3n/4` at rate `1/2`.**  With `k = n/2` (n even,
`n = 2k`), the strip bound `2t < n + k` is `2t < 3k`, i.e. `t < 3k/2 = 3n/4`, matching the decisive
strip window `(Johnson, 1/3)` where G87 places the witness threshold. -/
theorem strip_hypothesis_iff_three_quarter {n k t : ℕ} (hn : n = 2 * k) :
    (2 * t < n + k) ↔ (2 * t < 3 * k) := by
  subst hn; constructor <;> intro h <;> omega

end Verdict

end ArkLib.ProximityGap.SYZ56

-- Honesty audit:
#print axioms ArkLib.ProximityGap.SYZ56.cross_witness_u1_codeword_agreement
#print axioms ArkLib.ProximityGap.SYZ56.cross_witness_region_card_ge
#print axioms ArkLib.ProximityGap.SYZ56.mfoldMin_antitone
#print axioms ArkLib.ProximityGap.SYZ56.pairwise_region_lt_k
#print axioms ArkLib.ProximityGap.SYZ56.chain_region_lt_k
#print axioms ArkLib.ProximityGap.SYZ56.no_rigidity_certificate_in_strip
#print axioms ArkLib.ProximityGap.SYZ56.strip_hypothesis_iff_three_quarter
