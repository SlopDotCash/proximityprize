/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAGS
import ArkLib.Data.CodingTheory.ProximityGap.MCALowerBound

/-!
# MCA → Johnson assembly (#232): per-line list bound and the isolated bivariate residual

This file lays the remaining **assembly** bricks of the MCA→Johnson reduction, on top of the
sorry-free machinery already in the tree, and *precisely isolates the genuine residual* — the open
"prize" core — as a named hypothesis (no `sorry`, no vacuous `: True`, no fake axiom). Everything
that can be assembled from existing pieces is proven; the open part is reified as an explicit
hypothesis that downstream proofs must supply.

## What is assembled here (proven, axiom-clean)

The scalar-code (`A = F`, Reed–Solomon / prize regime) machinery already provides:

* `MCAGS.gsList_bad_gamma_bound` — given a finite codeword list `L` and a coordinate `x` with
  `u₁ x ≠ 0` such that every bad scalar `γ ∈ S` has a witness `w ∈ L` with `w x = u₀ x + γ·u₁ x`,
  the bad-scalar count is `≤ |L|` (the affine-pin / two-linear-equations count, the replacement
  for the false double-coverage target).
* `mcaEvent_imp_agree_witness` — `mcaEvent` yields a witness codeword agreeing with the *line
  point* `u₀ + γ·u₁` on `≥ ⌈(1−δ)n⌉` coordinates.
* `epsMCA_le_of_badCount_le` — a uniform per-stack bad-scalar bound `ℓ` gives `epsMCA ≤ ℓ/|F|`.

This file composes them:

1. **`mcaEvent_witness_at_active_coord`** — the *semantic glue*: from `mcaEvent` and a
   coordinate `x` with `u₁ x ≠ 0` that lies in the witness set `S`, the witness codeword matches
   the line *at `x`*. This is the missing link between the high-agreement witness of
   `MCAEventAgreeWitness` and the single-coordinate affine pin of `MCAGS`. (The full hypothesis
   is stated explicitly: the chosen active coordinate lies in every bad scalar's witness set.)

2. **`mca_badCount_le_list_of_active_coord`** — the clean **per-line** bound: for a fixed line
   `(u₀, u₁)` with an active coordinate `x` (`u₁ x ≠ 0`), and a finite list `L` such that every
   bad `γ` has a list witness matching the line at `x`, the `mcaEvent` bad-scalar count is
   `≤ |L|`. (Direct from `gsList_bad_gamma_bound`.)

3. **`epsMCA_le_card_div_of_uniform_active_list`** — if a *single* uniform list `L` and a
   per-stack active coordinate work for every stack, then `epsMCA C δ ≤ |L| / |F|` — the prize
   `poly/q` shape, with `|L|` the clustering parameter. This is the formal statement that *the
   entire MCA prize over the scalar code reduces to a uniform bound on the witness count* `|L|`.

## The isolated residual (the genuine novel-math core)

The clustering hypothesis above — *every bad scalar's line-witness lives in one fixed finite
list `L` of small size* — is **not** a pure assembly of the univariate Reed–Solomon list-decoder.
The in-tree `reedSolomon_list_size` bounds the codewords near a **single** received word `y`; but
the line-witnesses `{w_γ}` are each close to their **own**, `γ`-dependent line point `u₀ + γ·u₁`.
So they do *not* a priori lie in one univariate Johnson ball. Clustering them is exactly the
bivariate Guruswami–Sudan list-decoder of `f₀ + Z·f₁` over `F(Z)` — a genuinely
**bivariate-in-`γ`** statement, not provided by the univariate brick.

We reify precisely this missing input as `LineWitnessClustering` (a `Prop`-valued predicate,
fully explicit, *not* a `sorry`-carrying theorem), and prove:

* **`epsMCA_le_of_lineWitnessClustering`** — `LineWitnessClustering C δ ℓ` ⟹ `epsMCA C δ ≤ ℓ/|F|`.

This is the honest boundary: everything *up to* the bivariate clustering is proven; the
clustering itself is the open core, carried as an explicit hypothesis. `LineWitnessClustering` is
exactly the shape a bivariate GS interpolation lemma would discharge — its precise Lean signature
is the isolated residual.

All theorems are axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  #232.
- [BCIKS20] Proximity gaps for Reed–Solomon codes.
- [Hab25] Habböck. *A summary on the FRI low degree test*. (GS list-decoder reduction.)
-/

set_option linter.unusedSectionVars false

namespace ProximityGap

open scoped NNReal ENNReal BigOperators
open Finset Code

namespace MCAJohnson

section Scalar

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## Part 1 — semantic glue and the per-line bound (assembly, proven) -/

/-- **Semantic glue: an `mcaEvent` witness matches the line at any active coordinate it covers.**

If `mcaEvent C δ u₀ u₁ γ` holds with a witness set containing a coordinate `x` where `u₁ x ≠ 0`,
then the witness codeword `w` satisfies `w x = u₀ x + γ·u₁ x`. This is the missing link feeding
the single-coordinate affine pin of `MCAGS.gsList_bad_gamma_bound`: `mcaEvent` provides agreement
on a *whole set* `S`; restricting to one active coordinate `x ∈ S` gives the scalar match the
counting brick consumes.

The hypothesis `hxS` (the active coordinate lies in the witness set) is exactly what must be
supplied per bad scalar; in the prize regime it follows from `|S| ≥ (1−δ)n` being large enough
to meet the support of `u₁`, but here we state it explicitly as the clustering-side input. -/
theorem mcaEvent_witness_at_active_coord
    (C : Set (ι → F)) (δ : ℝ≥0) (u₀ u₁ : ι → F) (γ : F) (x : ι)
    (h : mcaEvent (A := F) C δ u₀ u₁ γ)
    (hxS : ∀ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι →
      (∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i) → x ∈ S) :
    ∃ w ∈ C, w x = u₀ x + γ * u₁ x := by
  obtain ⟨S, hScard, ⟨w, hwC, hwS⟩, _⟩ := h
  refine ⟨w, hwC, ?_⟩
  have hx : x ∈ S := hxS S hScard ⟨w, hwC, hwS⟩
  have := hwS x hx
  rwa [smul_eq_mul] at this

open Classical in
/-- **Per-line MCA bad-scalar bound from a witness list (assembly).**

Fix a line `(u₀, u₁)` with an active coordinate `x` (`u₁ x ≠ 0`). Suppose a finite codeword list
`L` is a *witness list at `x`*: every `mcaEvent`-bad scalar `γ` carries a list witness `w ∈ L`
matching the line at `x`, i.e. `w x = u₀ x + γ·u₁ x`. Then the number of bad scalars is at most
`|L|`.

This is the clean per-line statement Task 1 asks for: it composes the `mcaEvent` witness
(`mcaEvent_imp_agree_witness` / `mcaEvent_witness_at_active_coord`) with the affine-pin count
`MCAGS.gsList_bad_gamma_bound`. The witness-list hypothesis `hwitness` is stated explicitly — it
is the clustering input (the bivariate residual isolated below). -/
theorem mca_badCount_le_list_of_active_coord
    (C : Set (ι → F)) (δ : ℝ≥0) (u₀ u₁ : ι → F) (x : ι) (hx : u₁ x ≠ 0)
    (L : Finset (ι → F))
    (hwitness : ∀ γ : F, mcaEvent (A := F) C δ u₀ u₁ γ →
      ∃ w ∈ L, w x = u₀ x + γ * u₁ x) :
    (univ.filter (fun γ : F => mcaEvent (A := F) C δ u₀ u₁ γ)).card ≤ L.card := by
  refine MCAGS.gsList_bad_gamma_bound (F := F) L u₀ u₁ x hx
    (univ.filter (fun γ : F => mcaEvent (A := F) C δ u₀ u₁ γ)) ?_
  intro γ hγ
  rw [Finset.mem_filter] at hγ
  exact hwitness γ hγ.2

open Classical in
/-- **Uniform-list prize bound (assembly): `epsMCA C δ ≤ |L|/|F|`.**

If a *single* finite codeword list `L` works for **every** word stack — i.e. for each stack `u`
there is an active coordinate `x` (`u₁ x ≠ 0`) such that every `mcaEvent`-bad `γ` has a list witness
`w ∈ L` matching the line at `x` — then the MCA error is bounded by `|L|/|F|`, the prize `poly/q`
shape with `ℓ = |L|`.

This is the precise reduction Task 1 targets: *the MCA prize over the scalar code reduces to a
uniform bound on the witness-codeword count* `|L|`. It composes the per-line bound
`mca_badCount_le_list_of_active_coord` with `epsMCA_le_of_badCount_le`. -/
theorem epsMCA_le_card_div_of_uniform_active_list
    (C : Set (ι → F)) (δ : ℝ≥0) (L : Finset (ι → F))
    (huniform : ∀ u : WordStack F (Fin 2) ι, ∃ x : ι, u 1 x ≠ 0 ∧
      ∀ γ : F, mcaEvent (A := F) C δ (u 0) (u 1) γ →
        ∃ w ∈ L, w x = (u 0) x + γ * (u 1) x) :
    epsMCA (F := F) (A := F) C δ ≤ (L.card : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  refine epsMCA_le_of_badCount_le (F := F) (A := F) C δ L.card (fun u => ?_)
  obtain ⟨x, hx, hwit⟩ := huniform u
  exact mca_badCount_le_list_of_active_coord C δ (u 0) (u 1) x hx L hwit

/-! ## Part 2 — the isolated bivariate residual (the genuine open core)

The clustering hypothesis of `epsMCA_le_card_div_of_uniform_active_list` — that *one* finite list
`L` of size `≤ ℓ` carries the line-witnesses for **all** bad scalars of **every** stack — is the
genuinely missing input. We isolate it as the predicate `LineWitnessClustering` below.

**Why it is not pure assembly.** The line-witnesses `{w_γ : γ bad}` are each `δ`-close to their own
line point `u₀ + γ·u₁`, which moves with `γ`. The univariate Reed–Solomon list decoder
(`reedSolomon_list_size`) bounds codewords close to a **single** word, so it does not bound this
moving-center family. Bounding the *number of distinct* `w_γ` across all `γ` is the bivariate
Guruswami–Sudan list decoder of `f₀ + Z·f₁` over `F(Z)` — a bivariate-in-`γ` statement. That is the
isolated residual; `LineWitnessClustering` is its exact interface. -/

/-- **The isolated bivariate residual (the open core), as an explicit predicate.**

`LineWitnessClustering C δ ℓ` asserts: for every word stack `u`, there is a finite codeword list
`L` of size `≤ ℓ` and an active coordinate `x` (`u 1 x ≠ 0`) such that every `mcaEvent`-bad scalar
`γ` has a list witness `w ∈ L` matching the line at `x`. Equivalently — *all line-witnesses across
all bad scalars cluster into one size-`≤ ℓ` list, witnessed at a common active coordinate.*

This is **not** a `sorry`-carrying theorem and **not** a vacuous placeholder: it is the precise
interface a bivariate Guruswami–Sudan list-decoding lemma for `f₀ + Z·f₁` would discharge. For
Reed–Solomon below the Johnson radius, `ℓ` is the bivariate GS list size. Carrying it as an
explicit hypothesis is the honest boundary between the proven assembly and the open prize core. -/
def LineWitnessClustering (C : Set (ι → F)) (δ : ℝ≥0) (ℓ : ℕ) : Prop :=
  ∀ u : WordStack F (Fin 2) ι, ∃ (L : Finset (ι → F)) (x : ι),
    L.card ≤ ℓ ∧ u 1 x ≠ 0 ∧
    ∀ γ : F, mcaEvent (A := F) C δ (u 0) (u 1) γ →
      ∃ w ∈ L, w x = (u 0) x + γ * (u 1) x

open Classical in
/-- **The prize bound from the isolated residual.**

`LineWitnessClustering C δ ℓ` ⟹ `epsMCA C δ ≤ ℓ/|F|`.

This is the formal statement that the *entire* MCA prize over the scalar code follows from the
bivariate clustering residual. Everything below the residual is proven; the residual is the open
bivariate Guruswami–Sudan core, carried as the explicit hypothesis `LineWitnessClustering`. -/
theorem epsMCA_le_of_lineWitnessClustering
    (C : Set (ι → F)) (δ : ℝ≥0) (ℓ : ℕ)
    (hcluster : LineWitnessClustering (F := F) C δ ℓ) :
    epsMCA (F := F) (A := F) C δ ≤ (ℓ : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) := by
  refine epsMCA_le_of_badCount_le (F := F) (A := F) C δ ℓ (fun u => ?_)
  obtain ⟨L, x, hLcard, hx, hwit⟩ := hcluster u
  exact le_trans (mca_badCount_le_list_of_active_coord C δ (u 0) (u 1) x hx L hwit) hLcard

end Scalar

/-! ## Part 3 — the bivariate residual is itself reducible to one univariate-per-line hypothesis

A sharper isolation: the clustering predicate `LineWitnessClustering` can be *derived* from a
purely per-line, per-active-coordinate witness-existence hypothesis plus a uniform list-size cap.
This pins down exactly what a bivariate lemma must produce, separating the (proven) bookkeeping
from the (open) list-size content. -/

section Reduction

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **Clustering from a per-stack list assignment.**

If for every stack `u` we are *handed* a list `L u` (size `≤ ℓ`), an active coordinate `x u`, and a
per-bad-scalar witness in `L u` at `x u`, then `LineWitnessClustering C δ ℓ` holds. This is the
trivial repackaging direction; it makes explicit that the only content a bivariate GS lemma must
supply is the family `(L u, x u)` with the size cap and the witness property — the bookkeeping is
free. -/
theorem lineWitnessClustering_of_assignment
    (C : Set (ι → F)) (δ : ℝ≥0) (ℓ : ℕ)
    (Lf : WordStack F (Fin 2) ι → Finset (ι → F))
    (xf : WordStack F (Fin 2) ι → ι)
    (hcard : ∀ u : WordStack F (Fin 2) ι, (Lf u).card ≤ ℓ)
    (hactive : ∀ u : WordStack F (Fin 2) ι, u 1 (xf u) ≠ 0)
    (hwit : ∀ u : WordStack F (Fin 2) ι, ∀ γ : F, mcaEvent (A := F) C δ (u 0) (u 1) γ →
      ∃ w ∈ Lf u, w (xf u) = (u 0) (xf u) + γ * (u 1) (xf u)) :
    LineWitnessClustering (F := F) C δ ℓ := by
  intro u
  exact ⟨Lf u, xf u, hcard u, hactive u, hwit u⟩

/-- **End-to-end prize bound from the per-stack assignment.** Composes
`lineWitnessClustering_of_assignment` with `epsMCA_le_of_lineWitnessClustering`: a per-stack list
family with a uniform size cap `ℓ` and the per-bad-scalar witness property yields `epsMCA ≤ ℓ/|F|`.
This is the most directly usable consumer form for a future bivariate GS list-decoder. -/
theorem epsMCA_le_of_assignment
    (C : Set (ι → F)) (δ : ℝ≥0) (ℓ : ℕ)
    (Lf : WordStack F (Fin 2) ι → Finset (ι → F))
    (xf : WordStack F (Fin 2) ι → ι)
    (hcard : ∀ u : WordStack F (Fin 2) ι, (Lf u).card ≤ ℓ)
    (hactive : ∀ u : WordStack F (Fin 2) ι, u 1 (xf u) ≠ 0)
    (hwit : ∀ u : WordStack F (Fin 2) ι, ∀ γ : F, mcaEvent (A := F) C δ (u 0) (u 1) γ →
      ∃ w ∈ Lf u, w (xf u) = (u 0) (xf u) + γ * (u 1) (xf u)) :
    epsMCA (F := F) (A := F) C δ ≤ (ℓ : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞) :=
  epsMCA_le_of_lineWitnessClustering C δ ℓ
    (lineWitnessClustering_of_assignment C δ ℓ Lf xf hcard hactive hwit)

end Reduction

end MCAJohnson

end ProximityGap

#print axioms ProximityGap.MCAJohnson.mcaEvent_witness_at_active_coord
#print axioms ProximityGap.MCAJohnson.mca_badCount_le_list_of_active_coord
#print axioms ProximityGap.MCAJohnson.epsMCA_le_card_div_of_uniform_active_list
#print axioms ProximityGap.MCAJohnson.epsMCA_le_of_lineWitnessClustering
#print axioms ProximityGap.MCAJohnson.lineWitnessClustering_of_assignment
#print axioms ProximityGap.MCAJohnson.epsMCA_le_of_assignment
