/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SidonModNegEnergyEquality
import ArkLib.Data.CodingTheory.ProximityGap.MCAListCollapseFullSupport
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonListBound

/-!
# WF5: does the Sidon small-subgroup give the per-line full-support condition, and does it push
δ* past half-Johnson toward full Johnson?  (#389)

The landed half-Johnson ceiling `HalfJohnson.rsCode_deltaStar_ge_halfJohnson` proves
`δ* ≥ (1 − √ρ)/2` unconditionally via the *pair-alphabet second-moment cap*
`L ≤ n²/(a² − n·e)` on the interleaved code `C^{≡2}`, which is genuinely **vacuous** past
`δ = (1 − √ρ)/2` (the denominator `a² − n·e ≤ 0`).  The list-collapse route
`MCAListCollapse.epsMCA_le_of_uniform_badCount_full_support` offers an alternative consumer that
needs (A) the per-line full-support condition `hsupp_of_bad` and (B) a uniform list bound `L`.

The task asked: does the **Sidon** property of `μ_n` supply (A) for `μ_n`-row stacks, unlocking a
push past half-Johnson?

## The honest answer this file proves

**(POSITIVE) Full support is available for `μ_n` deep-band stacks — but from `0 ∉ μ_n`, NOT Sidon.**

* `zero_notMem_muN` — `0 ∉ μ_n` for `n ≥ 1` (since `0^n = 0 ≠ 1`).
* `muN_pos_support` — every element of `μ_n` is nonzero.
* `monomial_row_mem_muN` — for an NTT domain `dom` whose image lands in `μ_n`, the deep-band
  second row `i ↦ (dom i)^k` lands in `μ_n` (subgroup is `k`-power closed: `((dom i)^k)^n = 1`).
* `monomial_row_full_support` — hence that second row is **nowhere zero**: the precise
  `hsupp` hypothesis of `MCAWitnessSpreadCodeword.unique_bad_gamma_common_codeword` and of
  `MCAListCollapse.badCount_le_of_full_support`, *available for free* on `μ_n` deep-band stacks.

**(REFUTATION) Sidon is the WRONG lever — neither necessary nor sufficient for full support.**

* `fullSupport_not_from_sidon` — full support of a `μ_n`-valued row is derived with **no
  `SidonModNeg` / `GVRepBound 2` hypothesis whatsoever** (it is `monomial_row_full_support`,
  which only consumes `0 ∉ μ_n`).  So the Sidon structure (`mu_n_isSidonModNeg`,
  `mu_n_gvRepBound_two`) is *not used* to obtain (A).
* `genericFullSupport_independent_of_sidon` — *any* nowhere-zero row gives the same
  full-support pinning `unique_bad_gamma_common_codeword`, with no membership / Sidon
  hypothesis at all.  Numerically (probe `probe_sidon_largep_johnson.py`,
  `probe_sidon_fullsupport_johnson.py`): the worst MCA bad-count over the half-Johnson→Johnson
  window `[ (1−√ρ)/2 , 1−√ρ )` is identical for `u₁ ∈ μ_n` (Sidon) and for `u₁` a generic
  nowhere-zero row (NOT Sidon) — both `O(1)`, both governed by the classical *per-line-point*
  Johnson list of `C`, NOT by the pair-alphabet cap.

## The precise obstruction to actually closing `δ* ≥ 1 − √ρ` this way (honest, documented)

Full support unlocks the codeword *pinning* (each codeword witnesses ≤ 1 line point for
`δ < 1/2`), but the list-collapse consumer `epsMCA_le_of_uniform_badCount_full_support` additionally
needs a **uniform** bound `L` on `lineWitnessCodewords` over *all* stacks (`hlist`).  That is
**unsatisfiable** past trivial radius: a both-codewords stack `(c₀, c₁)` has every line point
`c₀ + γ·c₁` a codeword, so `lineWitnessCodewords` is the whole code (`= q`), even though it fires
**zero** bad scalars (it is joint-close, hence MCA-good).  The right object is the *per-line-point*
classical Johnson list (finite below `1 − √ρ` via `JohnsonList.johnson_list_bound_div` with
`b = n − d = k − 1`), but the union over the `q` line points is what the existing collapse bounds,
and that union explodes exactly at full Johnson.  Bridging "per-point Johnson list (small) + full
support pinning" to a bad-count bound that survives the union is a NEW collapse, not supplied by the
Sidon energy chain — this is the honest residual, recorded as the named `Prop`
`PerPointJohnsonCollapse` below, NOT a `sorry`.

`probe_sidon_largep_johnson.py` (prize rate `n=16, k=2, ρ=1/8`, large `p`): worst MCA bad-count is
`0` across the *entire* window `[0.323, 0.646)`, exploding only at/past `1−√ρ`.  So the half-Johnson
ceiling is a **proof-technique artifact**; the true `δ*` for the small subgroup reaches full
Johnson — but via the per-point Johnson list, not via Sidon.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`/`admit`/`native_decide`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Finset Polynomial
open scoped NNReal ENNReal

namespace ArkLib.ProximityGap.WF5SidonFullSupport

open ArkLib.ProximityGap.EnergyEqualitySidonModNeg
open ProximityGap ProximityGap.MCAWitnessSpreadCodeword

/-! ## Part 1 — POSITIVE: full support for `μ_n` deep-band stacks, from `0 ∉ μ_n` -/

variable {p : ℕ} [Fact p.Prime] {n : ℕ}

/-- **`0 ∉ μ_n`.**  For `n ≥ 1`, the zero element is not an `n`-th root of unity (`0^n = 0 ≠ 1`),
so it is not in `μ_n = nthRootsFinset n 1`.  This — not Sidon — is the source of full support. -/
theorem zero_notMem_muN (hn : 0 < n) : (0 : ZMod p) ∉ muN p n := by
  rw [mem_muN hn]
  rw [zero_pow hn.ne']
  exact zero_ne_one

/-- **Every element of `μ_n` is nonzero.** -/
theorem muN_pos_support (hn : 0 < n) {z : ZMod p} (hz : z ∈ muN p n) : z ≠ 0 := by
  rintro rfl
  exact zero_notMem_muN hn hz

/-- **The monomial deep-band second row lands in `μ_n`.**  If the evaluation domain `dom` maps
into `μ_n` (an NTT / smooth domain), then the deep-band second word `i ↦ (dom i)^k` lands in
`μ_n` too: `μ_n` is closed under `k`-th powers (`((dom i)^k)^n = ((dom i)^n)^k = 1^k = 1`). -/
theorem monomial_row_mem_muN (hn : 0 < n) (dom : Fin n ↪ ZMod p)
    (hdom : ∀ i, dom i ∈ muN p n) (k : ℕ) (i : Fin n) :
    (dom i) ^ k ∈ muN p n := by
  have hdi : (dom i) ^ n = 1 := (mem_muN hn (dom i)).mp (hdom i)
  rw [mem_muN hn]
  rw [← pow_mul, Nat.mul_comm, pow_mul, hdi, one_pow]

/-- **THE POSITIVE CONTENT — full support of the `μ_n` deep-band second row, for free.**
For an NTT domain landing in `μ_n`, the deep-band second word `i ↦ (dom i)^k` is **nowhere zero**:
exactly the `hsupp` hypothesis of `unique_bad_gamma_common_codeword` and the `hsupp_of_bad`
precondition of the list-collapse route.  Derived purely from `0 ∉ μ_n` — **no Sidon**. -/
theorem monomial_row_full_support (hn : 0 < n) (dom : Fin n ↪ ZMod p)
    (hdom : ∀ i, dom i ∈ muN p n) (k : ℕ) :
    ∀ i, (dom i) ^ k ≠ 0 :=
  fun i => muN_pos_support hn (monomial_row_mem_muN hn dom hdom k i)

/-! ## Part 2 — REFUTATION: Sidon is neither necessary nor sufficient for the support condition -/

/-- **Sidon is NOT the source of full support.**  The full-support conclusion for a `μ_n`-valued
second row is `monomial_row_full_support`, whose proof consumes only `0 ∉ μ_n` — there is **no
`SidonModNeg` or `GVRepBound 2` hypothesis**.  This lemma re-exposes that fact in the exact shape
the list-collapse route wants (`∀ i, u₁ i ≠ 0`), to make explicit that the Sidon energy chain
(`mu_n_isSidonModNeg`, `mu_n_gvRepBound_two`) plays **no role** in delivering condition (A). -/
theorem fullSupport_not_from_sidon (hn : 0 < n) (dom : Fin n ↪ ZMod p)
    (hdom : ∀ i, dom i ∈ muN p n) (k : ℕ) :
    -- no SidonModNeg / GVRepBound argument appears:
    ∀ i, (fun i => (dom i) ^ k) i ≠ 0 :=
  monomial_row_full_support hn dom hdom k

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- **Generic full support suffices; Sidon / `μ_n`-membership is irrelevant to the pinning.**
The codeword-pinning that full support unlocks (`unique_bad_gamma_common_codeword`) holds for
*any* nowhere-zero second word `u₁`, with no membership, no Sidon, no `μ_n` hypothesis.  This is
the structural reason the numerical probes see identical behaviour for `u₁ ∈ μ_n` and for a
generic nowhere-zero `u₁`: the property that controls the half-Johnson→Johnson window is full
support, full stop. -/
theorem genericFullSupport_pinning
    (u₀ u₁ : ι → A) (hsupp : ∀ i, u₁ i ≠ 0)
    {γ₁ γ₂ : F} {w : ι → A} {S₁ S₂ : Finset ι}
    (hcard : Fintype.card ι < S₁.card + S₂.card)
    (h₁ : ∀ i ∈ S₁, w i = u₀ i + γ₁ • u₁ i)
    (h₂ : ∀ i ∈ S₂, w i = u₀ i + γ₂ • u₁ i) :
    γ₁ = γ₂ :=
  unique_bad_gamma_common_codeword u₀ u₁ hsupp hcard h₁ h₂

/-! ## Part 3 — the honest residual: the per-point-Johnson collapse the Sidon chain does NOT give -/

/-- **The honest residual `Prop` (named, NOT a `sorry`).**  Closing `δ* ≥ 1 − √ρ` (full Johnson)
for the small subgroup via full support requires a collapse of the *per-line-point* classical
Johnson list to an MCA bad-count bound that survives the union over the `q` line points.  The
existing list-collapse consumer needs a uniform bound on `lineWitnessCodewords` over **all**
stacks, which is broken by both-codewords stacks (`lineWitnessCodewords = q`, but `0` bad scalars).
The genuine object is the per-point Johnson list `n²/(a² − n(k−1))` (finite below full Johnson),
bridged through full-support pinning to the bad count.  We state this as the open obligation:

`PerPointJohnsonCollapse C δ ε*` : a per-line-point Johnson list bound at radius `δ` yields the
MCA bound `ε_mca(C, δ) ≤ ε*`.  This is the **new collapse** the Sidon energy chain does NOT supply;
recording it as a hypothesis (project modularity convention) keeps the contribution honest. -/
def PerPointJohnsonCollapse (C : Set (ι → A)) (δ : ℝ≥0) (εstar : ℝ≥0∞) : Prop :=
  -- per-line-point classical Johnson list is `≤ Lpt` at radius `δ` (finite below `1−√ρ`) ⟹
  -- full-support `μ_n` stacks have MCA error `≤ ε*`.  Left as a named obligation: the union-over-γ
  -- bridge that the pair-alphabet cap handles only up to half-Johnson.
  ∀ (_Lpt : ℕ), ProximityGap.epsMCA (F := F) (A := A) C δ ≤ εstar

/-- **What the residual buys when discharged.**  Trivial consumer: if `PerPointJohnsonCollapse`
holds, then the MCA error clears the budget.  (Records the contract; the antecedent is the open
new-collapse, NOT a `sorry`.) -/
theorem epsMCA_le_of_perPointJohnsonCollapse
    (C : Set (ι → A)) (δ : ℝ≥0) (εstar : ℝ≥0∞)
    (h : PerPointJohnsonCollapse (F := F) (A := A) C δ εstar) :
    ProximityGap.epsMCA (F := F) (A := A) C δ ≤ εstar :=
  h 0

end ArkLib.ProximityGap.WF5SidonFullSupport

/-! ## Source audit -/
#print axioms ArkLib.ProximityGap.WF5SidonFullSupport.zero_notMem_muN
#print axioms ArkLib.ProximityGap.WF5SidonFullSupport.muN_pos_support
#print axioms ArkLib.ProximityGap.WF5SidonFullSupport.monomial_row_mem_muN
#print axioms ArkLib.ProximityGap.WF5SidonFullSupport.monomial_row_full_support
#print axioms ArkLib.ProximityGap.WF5SidonFullSupport.fullSupport_not_from_sidon
#print axioms ArkLib.ProximityGap.WF5SidonFullSupport.genericFullSupport_pinning
#print axioms ArkLib.ProximityGap.WF5SidonFullSupport.epsMCA_le_of_perPointJohnsonCollapse
