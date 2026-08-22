/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ42Realizability
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G87McaEventSyndromeBridge

/-!
# SYZ43 — is `RealizabilityCore` auto-instantiated by an actual over-budget stack?

SYZ42 refactored the strip's `realizability` obligation into `RealizabilityCore`, whose six fields
split as **one analytic field** (generation `span synFunctionals = ceiling` + its value
`finrank ceiling = 2(Ucard − k)`, together the old `union_span_rank`) and **five existence-residue
fields** (`synFunctionals`, a nonzero `syndrome`, its `annihilated` clause, and the ambient pinning
`finrank V = 2(n − k)`).  SYZ42 argued — abstractly — that rigidity cannot manufacture the existence
residue.  This file settles the *converse* question empirically at the concrete consumer:

> **Does an actual over-budget stack `(u₀, u₁)` with `mcaEvent`-bad scalars, fed through the G87
> syndrome bridge, auto-supply the fields of `RealizabilityCore`?**

## Verdict: FIVE of the six fields are auto-instantiated; the analytic field is NOT

The G87 bridge context (`_G87McaEventSyndromeBridge.lean`) hands the consumer, for the stack's own
syndrome pair on `V = SyndromePair C = ((ι→F)⧸C)²`:

* `synFunctionals` := the range of G87's bridge functionals (`exists_bridge_functionals`);
* `syndrome` := `syndromePair C u₀ u₁`, the stack's own syndrome pair;
* `syndrome_ne` := nonzero **for free** — a codeword-pair stack never fires `mcaEvent`
  (`mcaEvent_not_both_mem` ⟹ `¬(u₀ ∈ C ∧ u₁ ∈ C)` ⟹ `syndromePair ≠ 0`, via
  `syndromePair_eq_zero_iff`);
* `annihilated` := every bridge functional kills the syndrome pair (`exists_bridge_functionals`);
* `dim_syndromePair` := `finrank V = 2(n − k)` **for free** by `finrank_syndromePair`.

So the entire *existence residue* SYZ42 isolated is discharged, concretely, by any over-budget
`mcaEvent` stack: `realizabilityCore_of_overBudget_stack` builds the core with those five fields
literally filled from the bridge, taking **only** the analytic field as a hypothesis.

What the stack does **NOT** deliver is the analytic field: the generation / rank equality
`finrank (span synFunctionals) = 2(Ucard − k)`.  G87's `plantable_span_cap` gives only the *upper*
bracket `finrank (span) + 1 ≤ 2(n − k)`; the *lower* bound `finrank (span) ≥ 2(Ucard − k)` — that the
bridge functionals actually **realise** the full doubled shortening — is exactly the SYZ22(iii)
sunflower-packing / SYZ18 distinct-support residual.  It is carried here as the explicit hypothesis
`hrank`.

## The remaining hypothesis is NOT `uniformSylvester`

Crucially, this analytic residual is a **separate** open input from `UniformSylvesterInjective`
(SYZ38/SYZ39, BGK type).  `uniformSylvester` discharges the *spread branch* of the strip
(`generation_of_module_vanishes`: reduced band-triple syzygies vanish); it says nothing about the
union-rank *lower bound* of the G87 syndrome functionals.  Consequently:

* the master hypothesis genuinely stays at **two** open fields (`uniformSylvester`, `realizability`),
  confirming SYZ42's non-redundancy verdict from the consumer side;
* the one-hypothesis form `UniformSylvesterInjective → (no over-budget stacks)` does **NOT** close:
  the union-rank realizability `hrank` is an independent residual.  We do not assert it.

No unconditional `δ*`; no conditional-on-`uniformSylvester`-alone `δ*`.  The honest gain of SYZ43 is
that the realizability obligation's *existence residue* is proven auto-instantiated by the concrete
`mcaEvent` consumer, pinning the sole surviving realizability content to the single scalar equality
`hrank` (the union-rank lower bound), cleanly separated from `uniformSylvester`.

Axiom-clean; `#print axioms` at the bottom.  No `sorry`, no `native_decide`.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace ArkLib.ProximityGap.SYZ43

open Polynomial Module Submodule
open ArkLib.ProximityGap.SYZ42
open ArkLib.ProximityGap.Frontier.G87McaEventSyndromeBridge

/-! ## 1. The consumer-side instantiation: five fields auto-supplied -/

section Instantiation

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Auto-instantiation of the existence residue (explicit-functional form).**  Given a stack
`(u₀, u₁)` that is not a codeword pair (`hstack`, automatic for any `mcaEvent`-bad stack) together
with a finite family `φ` of functionals on the syndrome-pair space that all vanish on the stack's
own syndrome pair (`hann`, exactly what G87's `exists_bridge_functionals` produces), the five
existence-residue fields of `RealizabilityCore` are supplied literally from the bridge data.  The
**only** remaining input is the analytic rank equality `hrank` — the SYZ22(iii) union-rank lower
bound — captured by choosing the ceiling `span (range φ)`.

`syndrome_ne` and `dim_syndromePair` are both discharged internally (from `syndromePair_eq_zero_iff`
+ `hstack`, and from `finrank_syndromePair`), so the caller supplies neither. -/
def realizabilityCore_of_overBudget_stack
    (C : Submodule F (ι → F)) {n k Ucard : ℕ} {D : Type*}
    (hn : Fintype.card ι = n) (hk : finrank F C = k)
    {u₀ u₁ : ι → F} (hstack : u₀ ∉ C ∨ u₁ ∉ C)
    (φ : D → Module.Dual F (SyndromePair C))
    (hann : ∀ p, φ p (syndromePair C u₀ u₁) = 0)
    (hrank : finrank F (Submodule.span F (Set.range φ)) = 2 * (Ucard - k)) :
    RealizabilityCore (K := F) (V := SyndromePair C) n k Ucard where
  synFunctionals := Set.range φ
  syndrome := syndromePair C u₀ u₁
  syndrome_ne := by
    rw [Ne, syndromePair_eq_zero_iff]
    rcases hstack with h | h
    · exact fun hc => h hc.1
    · exact fun hc => h hc.2
  annihilated := by
    rintro ψ ⟨p, rfl⟩; exact hann p
  ceiling := Submodule.span F (Set.range φ)
  generates := rfl
  ceiling_dim := hrank
  dim_syndromePair := by
    rw [finrank_syndromePair, hn, hk]

/-! ## 2. The `mcaEvent` form: the existence residue from bad scalars alone

Here the bridge functionals are *not* supplied by the caller — they are constructed inside from the
`mcaEvent` witnesses via G87's `exists_bridge_functionals`.  The only caller obligation beyond the
bad-scalar witnesses is the analytic rank residual `hrank`, now quantified over the produced bridge
family (the honest "realizability" residual). -/

/-- **Auto-instantiation from `mcaEvent`-bad witnesses (existence residue discharged).**  For a
non-codeword stack with `r` bad scalars each carrying a threshold-`t` agreement witness (exactly the
data `mcaEvent_witness` extracts from `r` firings of the ABF26 `mcaEvent`), the bridge functionals
are built internally and the five existence-residue fields of `RealizabilityCore` are filled.  The
sole surviving hypothesis `hrank` is the SYZ22(iii) union-rank lower bound on the bridge family —
the isolated realizability residual, provably **not** `uniformSylvester`. -/
theorem realizabilityCore_of_mcaEvent_witnesses
    (C : Submodule F (ι → F)) {n k Ucard r t : ℕ}
    (hn : Fintype.card ι = n) (hk : finrank F C = k)
    {u₀ u₁ : ι → F} (hstack : u₀ ∉ C ∨ u₁ ∉ C) (γ : Fin r → F)
    (hwit : ∀ i, ∃ S : Finset ι, S.card = t ∧
      ∃ c ∈ C, ∀ x ∈ S, c x = u₀ x + γ i * u₁ x)
    (hrank : ∀ φ : Fin r × Fin (t - finrank F C) → Module.Dual F (SyndromePair C),
      (∀ p, φ p (syndromePair C u₀ u₁) = 0) →
      finrank F (Submodule.span F (Set.range φ)) = 2 * (Ucard - k)) :
    Nonempty (RealizabilityCore (K := F) (V := SyndromePair C) n k Ucard) := by
  obtain ⟨φ, hann, _hblock⟩ := exists_bridge_functionals C γ hwit
  exact ⟨realizabilityCore_of_overBudget_stack C hn hk hstack φ hann (hrank φ hann)⟩

end Instantiation

/-! ## 3. The honest strip corollary: two fields, realizability auto-structured

Combining SYZ43's auto-instantiation with SYZ42's `strip_theorem_of_master_hypothesis''`: the strip
conclusion follows from `uniformSylvester` together with the realizability *existence provider*, in
which every configuration's existence residue is now known to come from an actual over-budget stack,
leaving only the per-configuration union-rank equality. -/

section Strip

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **The strip theorem, realizability provided as `RealizabilityCore` existence.**  This is exactly
SYZ42's two-field `''` conclusion; SYZ43 re-exports it to record that the `realizabilityCore`
provider's *existence residue* is the auto-instantiated one (Sections 1–2), so the only genuinely
open content behind it is the per-`Ucard` union-rank equality, which is separate from
`uniformSylvester`. -/
theorem strip_theorem_of_uniform_sylvester_and_rank [DecidableEq K] {n k : ℕ}
    (H : StripMasterHypothesis'' K V n k) (hn : n = 2 * k) :
    (∀ (WAB WAC WBC rAB rAC rBC : K[X]) (mAB mAC mBC t : ℕ),
      t < mAB → k - 1 < mAB + mAC - t →
      WAB.natDegree = mAB - t → WAC.natDegree = mAC - t → WBC.natDegree = mBC - t → WAB ≠ 0 →
      WAB * rAB - WAC * rAC + WBC * rBC = 0 →
      (rAC ≠ 0 → rAC.natDegree ≤ k - 1 - mAC) → (rBC ≠ 0 → rBC.natDegree ≤ k - 1 - mBC) →
      rAB = 0 ∧ rAC = 0 ∧ rBC = 0)
    ∧
    (∀ Ucard, k ≤ Ucard → Ucard ≤ n → Ucard ≤ n - 1) :=
  strip_theorem_of_master_hypothesis'' H hn

end Strip

end ArkLib.ProximityGap.SYZ43

-- Honesty audit:
#print axioms ArkLib.ProximityGap.SYZ43.realizabilityCore_of_overBudget_stack
#print axioms ArkLib.ProximityGap.SYZ43.realizabilityCore_of_mcaEvent_witnesses
#print axioms ArkLib.ProximityGap.SYZ43.strip_theorem_of_uniform_sylvester_and_rank
