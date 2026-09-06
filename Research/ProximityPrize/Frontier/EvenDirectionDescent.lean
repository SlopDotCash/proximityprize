/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.FarLineIncidenceEquivariance

/-!
# 2-adic even–odd descent on the real far-line incidence `explainableScalars` (issue #407)

This file wires the **squaring map** `sq : μ_n → μ_{n/2}, x ↦ x²` (the 2-adic even–odd
descent) to the **REAL** in-tree far-line incidence object
`ProximityGap.FarCosetExplosion.explainableScalars`, NOT to a fresh abstract `TwoToOne`
pullback.

## The descent, concretely

A monomial direction `x^{2a'}` on `μ_n` is the pullback of the direction `x^{a'}` on `μ_{n/2}`
under squaring: `(x²)^{a'}`. More generally, given any index map `f : ι → ι'` realizing the
squaring on the evaluation domains — `domain' (f i) = (domain i)²` — an *even/imprimitive*
half-domain stack `(u₀', u₁')` pulls back to the full-domain stack `(u₀' ∘ f, u₁' ∘ f)`. The two
governing facts proved here, **both stated over the real `explainableScalars`**:

* `code_pullback_sq_mem` — the codeword pullback. An `RS[domain', k]` codeword, precomposed with
  the squaring index map `f`, is an `RS[domain, 2k]` codeword. The witnessing polynomial is
  `q.comp(X²)` (`q(x²)`), whose degree is `< 2k`. This is a real statement about
  `ReedSolomon.code` / `evalOnPoints`.

* `explainableScalars_sq_pullback_subset` — **the descent on `explainableScalars`**. Every scalar
  `γ` bad for the half-domain even-direction line `(u₀', u₁')` against `RS[μ_{n/2}, k]` (witness
  set `S'`, witnessing codeword `q`) is bad for the full-domain pulled-back line
  `(u₀' ∘ f, u₁' ∘ f)` against `RS[μ_n, 2k]` (witness set `f⁻¹(S')`, witnessing codeword `q ∘ f`):

  `explainableScalars RS[μ_{n/2},k] δ' u₀' u₁'  ⊆  explainableScalars RS[μ_n,2k] δ (u₀'∘f) (u₁'∘f)`

  whenever the relabelled witness budget is met. The witness-set pullback `f⁻¹(S')` is the
  **agreement-set pullback of the actual RS even-part**: a point `i ∈ ι` agrees iff its square
  `f i ∈ ι'` agreed, exactly because the codeword pullback is `q(x²)`.

This is the genuine counting bridge the LEVER asked for: it relates `explainableScalars` for the
even/imprimitive direction on `μ_n` to `explainableScalars` for the descended direction on
`μ_{n/2}`, through the *actual* definition of `explainableScalars` (agreement of `u₀ + γ•u₁` with
the code on a witness set) and the *actual* RS even-part splitting (`q(x) ↦ q(x²)`).

## What is honest here (named residual)

The proved direction is the **forward lift** (half-domain bad ⟹ full-domain bad), which is the
one with a clean, unconditional witness transport: every fibre of `f` lands in the pulled-back
witness set, doubling the support. The *reverse* collapse (full-domain bad on an even direction
⟹ half-domain bad), which would give the exact incidence identity `I_n(even) = I_{n/2}`, is the
open part: it needs the even-part *projection* of an arbitrary `RS[μ_n,2k]` agreement back to a
`RS[μ_{n/2},k]` agreement, i.e. the codeword that explains the full line need not be even, so its
restriction to a single square-fibre representative need not descend. That reverse obligation is
named `EvenDirectionIncidenceCollapse` below as a `Prop` (not proved).

Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
-/

open Finset
open scoped NNReal ENNReal

namespace ProximityGap.FarCosetExplosion

variable {ι ι' : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  [Fintype ι'] [Nonempty ι'] [DecidableEq ι']
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## The codeword pullback under the squaring index map -/

/-- **Codeword pullback under squaring.** Let `f : ι → ι'` realize the squaring map on the
evaluation domains: `domain' (f i) = (domain i)²` for every coordinate `i`. Then precomposing an
`RS[domain', k]` codeword with `f` yields an `RS[domain, 2k]` codeword.

The witnessing polynomial is `q.comp (X²) = q(x²)`: evaluating `q` at `(domain i)² = domain' (f i)`
is the same as evaluating `q(x²)` at `domain i`, and `deg (q(x²)) = 2·deg q < 2k`. This is the
exact "even part" of `RS[μ_n, 2k]`: the image of `RS[μ_{n/2}, k]` under `x ↦ x²`. -/
theorem code_pullback_sq_mem (domain : ι ↪ F) (domain' : ι' ↪ F) (k : ℕ) (f : ι → ι')
    (hf : ∀ i, domain' (f i) = (domain i) ^ 2)
    {w : ι' → F} (hw : w ∈ ReedSolomon.code domain' k) :
    (w ∘ f) ∈ ReedSolomon.code domain (2 * k) := by
  rw [ReedSolomon.mem_code_iff_exists_polynomial] at hw ⊢
  obtain ⟨q, hqdeg, rfl⟩ := hw
  refine ⟨q.comp (Polynomial.X ^ 2), ?_, ?_⟩
  · -- degree: `deg (q(X²)) = 2 · deg q < 2k`
    rcases eq_or_ne q 0 with rfl | hq0
    · simpa using (WithBot.bot_lt_coe (2 * k))
    · -- work with `natDegree`: `natDegree (q.comp (X²)) = natDegree q * 2`
      have hq_nd : q.natDegree < k := (Polynomial.natDegree_lt_iff_degree_lt hq0).mpr hqdeg
      have hcomp0 : q.comp (Polynomial.X ^ 2) ≠ 0 := by
        intro h
        -- `q(X²) = 0 ↔ q = 0 ∨ (… ∧ X² = C _)`; the right disjunct is false (deg X² = 2 ≠ 0).
        rcases Polynomial.comp_eq_zero_iff.mp h with hq0' | ⟨_, hXC⟩
        · exact hq0 hq0'
        · -- `X² = C c` forces `natDegree (X²) = 2 = 0`, impossible
          have hnd2 := congrArg Polynomial.natDegree hXC
          rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_C] at hnd2
          exact absurd hnd2 (by decide)
      have hnd : (q.comp (Polynomial.X ^ 2)).natDegree = q.natDegree * 2 := by
        rw [Polynomial.natDegree_comp]
        simp [Polynomial.natDegree_X_pow]
      rw [Polynomial.degree_eq_natDegree hcomp0, hnd]
      have : q.natDegree * 2 < 2 * k := by omega
      exact_mod_cast this
  · -- evaluation: `(q.comp (X²))` at `domain i`  =  `q` at `domain' (f i)` = `(w ∘ f) i`
    funext i
    simp only [Function.comp_apply, ReedSolomon.evalOnPoints, LinearMap.coe_mk,
      AddHom.coe_mk, Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X]
    rw [hf i]

/-! ## The descent on the real `explainableScalars` -/

open Classical in
/-- **2-adic even–odd descent on the far-line incidence (forward lift).** Let `f : ι → ι'`
realize the squaring map `domain' (f i) = (domain i)²`. Then every scalar `γ` that is bad for the
*half-domain* line `(u₀', u₁')` against `RS[domain', k]` is bad for the *full-domain* pulled-back
line `(u₀' ∘ f, u₁' ∘ f)` against `RS[domain, 2k]`:

`explainableScalars RS[domain',k] δ' u₀' u₁'  ⊆  explainableScalars RS[domain,2k] δ (u₀'∘f) (u₁'∘f)`,

provided the relabelled witness budget is met (`(1-δ)·|ι| ≤ |f⁻¹ S'|` for the half-domain witness
`S'`; with `f` exactly 2-to-1 and `|ι| = 2|ι'|`, `|f⁻¹ S'| = 2|S'|`, so the same fractional radius
transports). The witness set is the **agreement-set pullback of the actual RS even-part**:
`i ∈ ι` agrees with the pulled-back codeword `q ∘ f` exactly when its square `f i` agreed with `q`,
because `q ∘ f` is the evaluation of the even polynomial `q(x²)` (`code_pullback_sq_mem`).

This references the REAL `explainableScalars` of `FarLineIncidenceEquivariance` and the REAL
`ReedSolomon.code`; the direction `u₁ = u₁' ∘ f` is precisely an *even/imprimitive* monomial
direction `x^{2a'}` when `u₁'(y) = y^{a'}`. -/
theorem explainableScalars_sq_pullback_subset
    (domain : ι ↪ F) (domain' : ι' ↪ F) (k : ℕ) (f : ι → ι')
    (hf : ∀ i, domain' (f i) = (domain i) ^ 2)
    (δ δ' : ℝ≥0) (u₀' u₁' : ι' → F)
    -- the witness budget transports: for any half-domain witness `S'` meeting the half radius,
    -- its fibre-pullback `{i : f i ∈ S'}` meets the full radius (with `f` exactly 2-to-1 and
    -- `|ι| = 2|ι'|` this is automatic, but we keep it as the explicit transport hypothesis).
    (hbudget : ∀ S' : Finset ι', ((S'.card : ℝ≥0) ≥ (1 - δ') * Fintype.card ι') →
      (((Finset.univ.filter (fun i : ι => f i ∈ S')).card : ℝ≥0)
        ≥ (1 - δ) * Fintype.card ι)) :
    explainableScalars (F := F) (ReedSolomon.code domain' k : Set (ι' → F)) δ' u₀' u₁'
      ⊆ explainableScalars (F := F) (ReedSolomon.code domain (2 * k) : Set (ι → F)) δ
          (u₀' ∘ f) (u₁' ∘ f) := by
  classical
  intro γ hγ
  simp only [explainableScalars, mem_filter, mem_univ, true_and] at hγ ⊢
  obtain ⟨S', hsz', w, hwC, hw⟩ := hγ
  -- the fibre-pullback witness set, the pulled-back codeword `w ∘ f ∈ RS[domain, 2k]`
  refine ⟨Finset.univ.filter (fun i : ι => f i ∈ S'), hbudget S' hsz',
    w ∘ f, code_pullback_sq_mem domain domain' k f hf hwC, ?_⟩
  intro i hi
  rw [mem_filter] at hi
  -- agreement transports along the fibre: `i` agrees iff `f i` agreed
  have hag := hw (f i) hi.2
  simp only [Function.comp_apply, Pi.smul_apply, Pi.add_apply] at hag ⊢
  exact hag

/-! ## The named open residual (the reverse collapse) -/

/-- **Named open obligation: the reverse even-direction incidence collapse.** The forward lift
`explainableScalars_sq_pullback_subset` shows the half-domain bad set *injects into* the
full-domain even-direction bad set. The *exact incidence identity* `I_n(x^{2a'}) = I_{n/2}(x^{a'})`
that the 2-adic descent is meant to deliver additionally needs the **reverse** containment: a
scalar bad for the full-domain even-direction line against `RS[μ_n, 2k]` is bad for the
half-domain line against `RS[μ_{n/2}, k]`.

This is OPEN (not proved here): the `RS[μ_n, 2k]` codeword that explains the full pulled-back line
need not be the even pullback of an `RS[μ_{n/2}, k]` codeword — its odd part can carry the
agreement on a non-fibre-symmetric witness set, so it need not descend through a single
square-fibre representative. Closing this `Prop` (e.g. via an even-part *projection* of the
agreement that preserves the witness budget) is exactly the missing reverse leg. -/
def EvenDirectionIncidenceCollapse
    (domain : ι ↪ F) (domain' : ι' ↪ F) (k : ℕ) (f : ι → ι')
    (δ δ' : ℝ≥0) (u₀' u₁' : ι' → F) : Prop :=
  explainableScalars (F := F) (ReedSolomon.code domain (2 * k) : Set (ι → F)) δ
      (u₀' ∘ f) (u₁' ∘ f)
    ⊆ explainableScalars (F := F) (ReedSolomon.code domain' k : Set (ι' → F)) δ' u₀' u₁'

/-- **Conditional exact incidence equality.** Given the named reverse collapse, the far-line
incidence *set* for the even/imprimitive direction `x^{2a'}` on `μ_n` against `RS[μ_n, 2k]`
coincides exactly with that for the descended direction `x^{a'}` on `μ_{n/2}` against
`RS[μ_{n/2}, k]` — the clean 2-adic even–odd identity `I_n(even) = I_{n/2}`. The forward leg is
the unconditional `explainableScalars_sq_pullback_subset`; only the reverse leg is hypothesised. -/
theorem explainableScalars_sq_pullback_eq_of_collapse
    (domain : ι ↪ F) (domain' : ι' ↪ F) (k : ℕ) (f : ι → ι')
    (hf : ∀ i, domain' (f i) = (domain i) ^ 2)
    (δ δ' : ℝ≥0) (u₀' u₁' : ι' → F)
    (hbudget : ∀ S' : Finset ι', ((S'.card : ℝ≥0) ≥ (1 - δ') * Fintype.card ι') →
      (((Finset.univ.filter (fun i : ι => f i ∈ S')).card : ℝ≥0)
        ≥ (1 - δ) * Fintype.card ι))
    (hcollapse : EvenDirectionIncidenceCollapse domain domain' k f δ δ' u₀' u₁') :
    explainableScalars (F := F) (ReedSolomon.code domain (2 * k) : Set (ι → F)) δ
        (u₀' ∘ f) (u₁' ∘ f)
      = explainableScalars (F := F) (ReedSolomon.code domain' k : Set (ι' → F)) δ' u₀' u₁' :=
  Finset.Subset.antisymm hcollapse
    (explainableScalars_sq_pullback_subset domain domain' k f hf δ δ' u₀' u₁' hbudget)

end ProximityGap.FarCosetExplosion

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms ProximityGap.FarCosetExplosion.code_pullback_sq_mem
#print axioms ProximityGap.FarCosetExplosion.explainableScalars_sq_pullback_subset
#print axioms ProximityGap.FarCosetExplosion.explainableScalars_sq_pullback_eq_of_collapse
