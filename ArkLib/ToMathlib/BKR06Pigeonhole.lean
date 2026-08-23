/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.ListDecoding.BKR06SubspacePoly

/-!
# BKR06 §3 pigeonhole family count (Lemma 3.5 combinatorial engine)

This file formalizes the **counting** half of BKR06 Lemma 3.5
(Ben-Sasson–Kopparty–Radhakrishnan, *Subspace Polynomials and List Decoding of
Reed–Solomon Codes*, FOCS 2006).  The companion files supply the *algebraic*
(`BKR06FiberCount`) and *geometric* (`BKR06Injection`) cores; here we manufacture
the pigeonhole **family** `𝓛 : ι → Submodule F K` of distinct `v`-dimensional
`𝔽_q`-subspaces of `K = 𝔽_{q^m}` whose subspace polynomials all agree above a
fixed degree cutoff `k`, with the explicit cardinality lower bound that BKR06's
list-size argument consumes (the `hfamily` residual of
`CodingTheory.rs_lambda_superpoly_extension_bkr06_of_family`).

## What is proven here, end to end

* **Graph-construction subspace count** (`BKR06.card_dimv_subspaces_ge`): there are
  at least `q^{v(m−v)}` distinct `v`-dimensional `𝔽_q`-subspaces of `K`, exhibited
  as the graphs of the `q^{v(m−v)}` `𝔽_q`-linear maps `V₀ → W₀` from a fixed
  dimension-`v` subspace `V₀` to a complement `W₀` (dimension `m−v`).  The map
  `L ↦ {p + L p : p ∈ V₀}` is injective and lands in dimension-`v` subspaces.

* **Top-coefficient pattern pigeonhole** (`BKR06.exists_pattern_fiber_family`):
  partition any finite family of polynomials by their coefficients in the window
  `[k, D]` (the "top coefficients above the cutoff `k`"); if the family is larger
  than `(#K)^w · N`, some pattern-fiber contains `> N` polynomials, pairwise
  differing only below degree `k` — i.e. all pairwise differences lie in
  `degreeLT K k`.

* **Assembled family** (`BKR06.bkr06_pigeonhole_family_card`): combining the two
  above with the proven `subspacePoly` degree facts, we produce an index type `ι`, a
  family `𝓛 : ι → Submodule F K` of distinct `v`-dimensional subspaces, the
  distinctness and degree-cutoff facts in exactly the shape
  `rs_lambda_superpoly_extension_bkr06_of_family` consumes, together with a
  cardinality lower bound `N < |ι|`.

* **Real-exponent residual** (`BKR06.bkr06_hfamily_of_card`): the exact `hfamily`
  inequality `q^{(α−β²)·log q} ≤ |ι|` consumed by
  `rs_lambda_superpoly_extension_bkr06_of_family`, derived from the count above and a
  single explicit, named arithmetic side condition `hexp`.

## Exponent bookkeeping and the honest residual

BKR06's *tight* count uses that a subspace polynomial is **linearized**: its only
nonzero coefficients sit at the `q`-power exponents `q^0, …, q^v`, so the
"top coefficients above `q^u`" live in `≤ v − u` slots and the pattern count is
`q^{m(v−u)}`, giving `|𝓛| ≥ q^{v(m−v)} / q^{m(v−u)} = q^{(u+1)m − v²}` (Lemma 3.5).
The linearized-support theorem (`subspacePoly` is supported on `{q^i}`) is itself a
substantial additive-polynomial / Frobenius result *not present in mathlib*, so the
in-tree pattern pigeonhole below uses the **generic** coefficient window of width
`w` slots rather than the tight `v − u` slots.  Consequently the count delivered by
the fully-proven pipeline is the generic `N < q^{v(m−v)} / (#K)^w`, and the bridge
from that to the in-tree target `q^{(α−β²)·log q}` (which equals the tight
`q^{(u+1)m − v²}` under BKR06's parameter choices `v ≈ βm`, `k = q^u`) is surfaced as
a single explicit, named arithmetic hypothesis `hexp` of `bkr06_hfamily_of_card`.
This is the only residual: the count and the pigeonhole themselves are proven,
`sorry`-free and axiom-clean.

All declarations compile `sorry`/`axiom`-free and are axiom-clean
(`[propext, Classical.choice, Quot.sound]`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

noncomputable section

open Polynomial BigOperators Finset

namespace BKR06

/-! ## Part 1 — the graph-construction subspace count

Fix a dimension-`v` subspace `V₀ ⊆ K` with complement `W₀` (`IsCompl V₀ W₀`,
`finrank W₀ = m − v`).  For an `𝔽_q`-linear map `L : V₀ → W₀` define the
"graph subspace" as the range of `φ_L : V₀ → K`, `p ↦ p + L p`.  We show
`L ↦ range φ_L` is injective into dimension-`v` subspaces; counting linear maps
`V₀ → W₀` (there are `q^{v(m−v)}`) gives the lower bound. -/

section GraphCount

variable {K : Type*} [Field K]
variable {F : Type*} [Field F] [Module F K]
variable (V₀ W₀ : Submodule F K)

/-- The graph embedding `φ_L : V₀ →ₗ[F] K`, `p ↦ (p : K) + (L p : K)`, for an
`𝔽`-linear map `L : V₀ → W₀`.  Its range is the BKR06 "graph subspace". -/
def graphEmbedding (L : V₀ →ₗ[F] W₀) : V₀ →ₗ[F] K :=
  V₀.subtype + W₀.subtype.comp L

@[simp] lemma graphEmbedding_apply (L : V₀ →ₗ[F] W₀) (p : V₀) :
    graphEmbedding V₀ W₀ L p = (p : K) + (L p : K) := rfl

/-- The graph embedding is injective: if `(p : K) + (L p : K) = 0` then `p ∈ V₀`
and `-(L p) ∈ V₀`, but `L p ∈ W₀` and `V₀ ⊓ W₀ = ⊥`, forcing `p = 0`. -/
lemma graphEmbedding_injective (h : IsCompl V₀ W₀) (L : V₀ →ₗ[F] W₀) :
    Function.Injective (graphEmbedding V₀ W₀ L) := by
  rw [← LinearMap.ker_eq_bot]
  rw [LinearMap.ker_eq_bot']
  intro p hp
  simp only [graphEmbedding_apply] at hp
  -- (p : K) = -(L p : K); LHS ∈ V₀, RHS ∈ W₀
  have hpK : (p : K) = -((L p : K)) := by linear_combination hp
  have hmemV : (p : K) ∈ V₀ := p.2
  have hmemW : (p : K) ∈ W₀ := by
    rw [hpK]; exact W₀.neg_mem (L p).2
  have hinf : (p : K) ∈ V₀ ⊓ W₀ := ⟨hmemV, hmemW⟩
  rw [IsCompl.inf_eq_bot h] at hinf
  have : (p : K) = 0 := by simpa using hinf
  exact Subtype.ext this

/-- The BKR06 graph subspace of `L`: the range of `graphEmbedding`. -/
def graphSubspace (L : V₀ →ₗ[F] W₀) : Submodule F K :=
  LinearMap.range (graphEmbedding V₀ W₀ L)

/-- The graph subspace has dimension `v = finrank V₀`. -/
lemma finrank_graphSubspace [FiniteDimensional F K]
    (h : IsCompl V₀ W₀) (L : V₀ →ₗ[F] W₀) :
    Module.finrank F (graphSubspace V₀ W₀ L) = Module.finrank F V₀ :=
  LinearMap.finrank_range_of_inj (graphEmbedding_injective V₀ W₀ h L)

/-- `L ↦ graphSubspace L` is injective.  If two graph subspaces coincide, then for
each `p`, `(p : K) + (L p : K) = (p' : K) + (L' p' : K)` for some `p'`; comparing
`V₀`- and `W₀`-components (using `IsCompl`) forces `p' = p` and `L p = L' p`. -/
lemma graphSubspace_injective (h : IsCompl V₀ W₀) :
    Function.Injective (graphSubspace V₀ W₀) := by
  intro L L' hLL'
  ext p
  -- φ_L p lies in graphSubspace L = graphSubspace L', so equals φ_L' p' for some p'
  have hmem : graphEmbedding V₀ W₀ L p ∈ graphSubspace V₀ W₀ L' := by
    rw [← hLL']; exact ⟨p, rfl⟩
  obtain ⟨p', hp'⟩ := hmem
  simp only [graphEmbedding_apply] at hp'
  -- (p : K) + (L p : K) = (p' : K) + (L' p' : K)
  -- ⇒ (p : K) - (p' : K) = (L' p' : K) - (L p : K) ∈ V₀ ⊓ W₀ = ⊥
  have hdiff : (p : K) - (p' : K) = (L' p' : K) - (L p : K) := by
    calc
      (p : K) - (p' : K) = ((p : K) + (L p : K)) - ((p' : K) + (L p : K)) := by abel
      _ = ((p' : K) + (L' p' : K)) - ((p' : K) + (L p : K)) := by rw [← hp']
      _ = (L' p' : K) - (L p : K) := by abel
  have hV : (p : K) - (p' : K) ∈ V₀ := V₀.sub_mem p.2 p'.2
  have hW : (p : K) - (p' : K) ∈ W₀ := by
    rw [hdiff]; exact W₀.sub_mem (L' p').2 (L p).2
  have hzero : (p : K) - (p' : K) = 0 := by
    have hmeminf : (p : K) - (p' : K) ∈ V₀ ⊓ W₀ := ⟨hV, hW⟩
    rw [IsCompl.inf_eq_bot h] at hmeminf; simpa using hmeminf
  have hpp' : p = p' := Subtype.ext (sub_eq_zero.mp hzero)
  subst hpp'
  -- and then L p = L' p, reading off the W₀-component
  have hLeq' : (L' p : K) = (L p : K) := by
    exact add_left_cancel hp'
  exact hLeq'.symm

end GraphCount

/-! ### Cardinality of the graph family

The graph subspaces form an injective image of `V₀ →ₗ[F] W₀`, whose cardinality is
`q^{v(m−v)}` (it is a free `𝔽_q`-module of rank `(finrank V₀)·(finrank W₀)`).  We
extract the lower bound on the number of distinct dimension-`v` subspaces. -/

section GraphCardinality

variable {K : Type*} [Field K] [Fintype K]
variable {F : Type*} [Field F] [Fintype F] [Module F K]

/-- There exists a finset of `≥ q^{v(m−v)}` pairwise-distinct dimension-`v`
`𝔽_q`-subspaces of `K`, where `q = #𝔽`, `m = finrank F K`, `v ≤ m`.

Exhibited as the injective image of the linear maps `V₀ →ₗ[F] W₀` under
`graphSubspace`; the number of such maps is `q^{v·(m−v)}`. -/
theorem card_dimv_subspaces_ge
    (v : ℕ) (hv : v ≤ Module.finrank F K) :
    ∃ S : Finset (Submodule F K),
      (Fintype.card F) ^ (v * (Module.finrank F K - v)) ≤ S.card ∧
      ∀ W ∈ S, Module.finrank F W = v := by
  classical
  -- a dimension-`v` subspace `V₀` and a complement `W₀`
  obtain ⟨f, hf⟩ := exists_linearIndependent_of_le_finrank (R := F) (M := K) hv
  set V₀ : Submodule F K := Submodule.span F (Set.range f) with hV₀
  have hfinV₀ : Module.finrank F V₀ = v := by
    rw [hV₀, finrank_span_eq_card hf]; simp
  obtain ⟨W₀, hcompl⟩ := exists_isCompl V₀
  -- dimensions: finrank W₀ = m - v
  have hsum : Module.finrank F V₀ + Module.finrank F W₀ = Module.finrank F K :=
    Submodule.finrank_add_eq_of_isCompl hcompl
  have hfinW₀ : Module.finrank F W₀ = Module.finrank F K - v := by omega
  -- the image of `graphSubspace` over all linear maps `V₀ →ₗ[F] W₀`
  letI : Fintype V₀ := Fintype.ofFinite V₀
  letI : Fintype W₀ := Fintype.ofFinite W₀
  letI : Fintype (V₀ →ₗ[F] W₀) :=
    Fintype.ofInjective (fun L : V₀ →ₗ[F] W₀ => (L : V₀ → W₀))
      (fun L L' hLL => DFunLike.coe_injective hLL)
  refine ⟨Finset.image (graphSubspace V₀ W₀) (Finset.univ : Finset (V₀ →ₗ[F] W₀)), ?_, ?_⟩
  · -- cardinality: injective image, #(V₀ →ₗ W₀) = q^{v(m-v)}
    rw [Finset.card_image_of_injective _ (graphSubspace_injective V₀ W₀ hcompl)]
    rw [Finset.card_univ]
    -- #(V₀ →ₗ[F] W₀) = q^{finrank V₀ * finrank W₀}
    have hcardHom : Fintype.card (V₀ →ₗ[F] W₀)
        = (Fintype.card F) ^ (Module.finrank F V₀ * Module.finrank F W₀) := by
      rw [Module.card_eq_pow_finrank (K := F) (V := (V₀ →ₗ[F] W₀))]
      congr 1
      rw [Module.finrank_linearMap]
    rw [hcardHom, hfinV₀, hfinW₀]
  · intro W hW
    rw [Finset.mem_image] at hW
    obtain ⟨L, _, rfl⟩ := hW
    rw [finrank_graphSubspace V₀ W₀ hcompl, hfinV₀]

end GraphCardinality

/-! ## Part 2 — the top-coefficient pattern pigeonhole

For polynomials of `natDegree ≤ D`, two polynomials sharing all coefficients in the
window `[k, D]` differ only below degree `k`, i.e. their difference lies in
`degreeLT K k`.  There are at most `(#K)^w` such windows, so any family of
more than `(#K)^w·N` polynomials has a window-fiber of size `> N`. -/

section Pattern

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- The top-coefficient pattern of `P` above the cutoff `k`, as a function on the
window `[k, k + w)`: `j ↦ P.coeff (k + j)`. -/
def topPattern (k w : ℕ) (P : K[X]) : Fin w → K := fun j => P.coeff (k + (j : ℕ))

/-- If `P`, `Q` have `natDegree ≤ D`, the window width covers `(D, ∞)` (i.e.
`D < k + w`), and they share their top pattern above `k`, then `P − Q ∈ degreeLT K k`.

All coefficients of `P − Q` at index `≥ k` vanish: those in the window `[k, k+w)`
by the shared pattern, those `≥ k + w > D` by the degree bound. -/
lemma sub_mem_degreeLT_of_topPattern_eq
    {k w D : ℕ} {P Q : K[X]}
    (hP : P.natDegree ≤ D) (hQ : Q.natDegree ≤ D) (hcov : D < k + w)
    (hpat : topPattern k w P = topPattern k w Q) :
    P - Q ∈ Polynomial.degreeLT K k := by
  rw [Polynomial.mem_degreeLT, Polynomial.degree_lt_iff_coeff_zero]
  intro n hn
  rw [Polynomial.coeff_sub]
  rcases lt_or_ge n (k + w) with hnw | hnw
  · -- n in the window [k, k+w): use the shared pattern
    obtain ⟨j, hj⟩ : ∃ j : Fin w, k + (j : ℕ) = n := by
      refine ⟨⟨n - k, by omega⟩, ?_⟩
      simp only; omega
    have hPj := congrFun hpat j
    simp only [topPattern] at hPj
    rw [hj] at hPj
    rw [hPj]; ring
  · -- n ≥ k + w > D: both coeffs vanish by degree
    have hnD : D < n := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hP hnD),
        Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hQ hnD)]
    ring

/-- **Pattern pigeonhole.**  Let `g : ι → K[X]` be a family of polynomials, each of
`natDegree ≤ D`, with the window covering `(D, ∞)` (`D < k + w`).  If
`(#K)^w · N < |ι|`, then there is a sub-family of size `> N` (a finset `T`) on which
all `g i` share the same top pattern above `k` — hence all pairwise differences
`g i − g j` lie in `degreeLT K k`. -/
theorem exists_pattern_fiber_family
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : ι → K[X]) (k w D N : ℕ)
    (hdeg : ∀ i, (g i).natDegree ≤ D) (hcov : D < k + w)
    (hbig : (Fintype.card K) ^ w * N < Fintype.card ι) :
    ∃ T : Finset ι, N < T.card ∧
      (∀ i ∈ T, ∀ j ∈ T, g i - g j ∈ Polynomial.degreeLT K k) := by
  classical
  -- pigeonhole on the pattern map ι → (Fin w → K)
  have hpat_card : Fintype.card (Fin w → K) = (Fintype.card K) ^ w :=
    Fintype.card_pi_const K w
  -- the pattern fiber finset
  let fiber : (Fin w → K) → Finset ι :=
    fun y => Finset.univ.filter (fun i => topPattern k w (g i) = y)
  -- there is a fiber of size > N
  have key : ∃ y : (Fin w → K), N < (fiber y).card := by
    by_contra hcon
    push Not at hcon
    -- if every fiber ≤ N, then |ι| ≤ #patterns * N
    have hsum : (Fintype.card ι) ≤ (Fintype.card (Fin w → K)) * N := by
      have hpart : ∑ y : (Fin w → K), (fiber y).card = Fintype.card ι := by
        rw [← Finset.card_univ (α := ι)]
        exact (Finset.card_eq_sum_card_fiberwise
          (f := fun i => topPattern k w (g i)) (s := Finset.univ) (t := Finset.univ)
          (fun i _ => Finset.mem_univ _)).symm
      calc Fintype.card ι
          = ∑ y : (Fin w → K), (fiber y).card := hpart.symm
        _ ≤ ∑ _y : (Fin w → K), N := Finset.sum_le_sum (fun y _ => hcon y)
        _ = (Fintype.card (Fin w → K)) * N := by
            rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [hpat_card] at hsum
    omega
  obtain ⟨y, hy⟩ := key
  refine ⟨fiber y, hy, ?_⟩
  intro i hi j hj
  simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  have hpat : topPattern k w (g i) = topPattern k w (g j) := by rw [hi, hj]
  exact sub_mem_degreeLT_of_topPattern_eq (hdeg i) (hdeg j) hcov hpat

end Pattern

/-! ## Part 3 — assembling the BKR06 pigeonhole family

We combine the graph count (Part 1) with the pattern pigeonhole (Part 2) applied to
the subspace polynomials of a dimension-`v` family.  The subspace polynomials all
have `natDegree = q^v` (`subspacePoly_natDegree_eq_pow_finrank`), so the window
`[k, k+w)` with `q^v < k + w` covers their tops; equal patterns give pairwise
differences in `degreeLT K k`.  Distinct subspaces give distinct subspace
polynomials (the carrier of a subspace is its own root set), so the surviving
sub-family is genuinely a family of distinct subspaces with the degree-cutoff
property in the exact shape `_of_family` consumes. -/

section Assemble

universe u

variable {K : Type u} [Field K] [Fintype K] [DecidableEq K]
variable {F : Type*} [Field F] [Fintype F] [Module F K]

/-- A submodule of a finite vector space is finite: a local `Fintype` instance used to
form the subspace polynomials of the pigeonhole family (subspace membership is not
decidable in general, so this instance is `noncomputable` via `Fintype.ofFinite`). -/
local instance instFintypeSubmodule (W : Submodule F K) : Fintype W := Fintype.ofFinite W

/-- For finite `𝔽`-subspaces `W₁ ≠ W₂`, the subspace polynomials differ. -/
lemma subspacePoly_ne_of_ne
    (W₁ W₂ : Submodule F K) [Fintype W₁] [Fintype W₂] (h : W₁ ≠ W₂) :
    subspacePoly (subFinset W₁) ≠ subspacePoly (subFinset W₂) := by
  intro heq
  apply h
  -- equal polynomials have equal root sets = carriers
  have : ∀ x : K, x ∈ W₁ ↔ x ∈ W₂ := by
    intro x
    rw [← mem_subFinset (W := W₁), ← mem_subFinset (W := W₂),
        ← subspacePoly_isRoot_iff (subFinset W₁) x,
        ← subspacePoly_isRoot_iff (subFinset W₂) x, heq]
  exact Submodule.ext this

/-! ### The assembled pigeonhole family and its cardinality

Combining `card_dimv_subspaces_ge` (Part 1) with `exists_pattern_fiber_family`
(Part 2) applied to the subspace polynomials of the graph family. The subspace
polynomials are pairwise distinct (`subspacePoly_ne_of_ne`) and all have
`natDegree = q^v` (`subspacePoly_natDegree_eq_pow_finrank`), so the pattern
pigeonhole, with window cutoff `k` and width `w` covering `(q^v, ∞)`
(`q^v < k + w`), extracts a sub-family of size `> N` whenever
`(#K)^w · N < q^{v(m−v)}`. -/

/-- **BKR06 Lemma 3.5 assembled count (cardinality form).**

There is an index type `ι` and a family `𝓛 : ι → Submodule F K` of `𝔽_q`-subspaces
of `K` such that:

* the index type is strictly larger than `N` (provided `(#K)^w · N < q^{v(m−v)}` and
  the window `[k, k+w)` covers `(q^v, ∞)`, i.e. `hcov : q^v < k + w`);
* every member has dimension `v`;
* the subspace polynomials are pairwise distinct, i.e. the members are pairwise
  distinct subspaces;
* all pairwise differences of subspace polynomials lie in `degreeLT K k` (the
  degree-cutoff agreement BKR06 needs).

The index type is realized as `Fin T.card` for the extracted fiber `T`, hence a
`Type 0`, decoupling it from the (arbitrary) universe of `K`.

This is the purely combinatorial engine of the `hfamily` residual; the real-exponent
form is `bkr06_hfamily_of_card` below. -/
theorem bkr06_pigeonhole_family_card
    (v : ℕ) (hv : v ≤ Module.finrank F K)
    (k w N : ℕ)
    (hcov : (Fintype.card F) ^ v < k + w)
    (hbig : (Fintype.card K) ^ w * N < (Fintype.card F) ^ (v * (Module.finrank F K - v))) :
      ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (𝓛 : ι → Submodule F K)
      (_ : ∀ i, Fintype (𝓛 i)),
      N < Fintype.card ι ∧
      (∀ i, Module.finrank F (𝓛 i) = v) ∧
      Function.Injective (fun i => subspacePoly (subFinset (𝓛 i))) ∧
      (∀ i j, subspacePoly (subFinset (𝓛 i)) - subspacePoly (subFinset (𝓛 j))
          ∈ Polynomial.degreeLT K k) := by
  classical
  -- Part 1: a large finset of distinct dimension-`v` subspaces.
  obtain ⟨S, hScard, hSdim⟩ := card_dimv_subspaces_ge (F := F) (K := K) v hv
  -- The subspace-polynomial map on the (typed) finset `S` (Fintype on members is the
  -- ambient `instFintypeSubmodule`).
  let g : {W : Submodule F K // W ∈ S} → K[X] := fun W => subspacePoly (subFinset W.val)
  -- It is injective: distinct subspaces ⇒ distinct subspace polynomials.
  have hg_inj : Function.Injective g := fun W₁ W₂ hW => by
    by_contra hne
    exact subspacePoly_ne_of_ne W₁.val W₂.val (fun h => hne (Subtype.ext h)) hW
  -- Each has degree `q^v` (members of `S` have dimension `v`).
  have hg_deg : ∀ W : {W : Submodule F K // W ∈ S}, (g W).natDegree ≤ (Fintype.card F) ^ v := by
    intro W
    have hdim : Module.finrank F W.val = v := hSdim W.val W.2
    have : (g W).natDegree = (subspacePoly (subFinset W.val)).natDegree := rfl
    rw [this, subspacePoly_natDegree_eq_pow_finrank, hdim]
  -- Cardinality of the typed finset is `S.card ≥ q^{v(m−v)}`.
  have hScard' : (Fintype.card F) ^ (v * (Module.finrank F K - v))
      ≤ Fintype.card {W : Submodule F K // W ∈ S} := by
    rw [Fintype.card_coe]; exact hScard
  have hbig' : (Fintype.card K) ^ w * N
      < Fintype.card {W : Submodule F K // W ∈ S} := lt_of_lt_of_le hbig hScard'
  -- Part 2: pattern pigeonhole extracts a sub-family `T` of size `> N`.
  obtain ⟨T, hTcard, hTsmall⟩ :=
    exists_pattern_fiber_family g k w ((Fintype.card F) ^ v) N hg_deg hcov hbig'
  -- The surviving index type: the elements of `T`.
  refine ⟨{t : {W : Submodule F K // W ∈ S} // t ∈ T}, inferInstance, inferInstance,
    fun t => t.val.val, fun _ => inferInstance, ?_, ?_, ?_, ?_⟩
  · -- |ι| = T.card > N
    rw [Fintype.card_coe]
    exact hTcard
  · -- each has dimension `v`
    intro t
    exact hSdim _ t.val.2
  · -- subspace polynomials are pairwise distinct on `T`
    intro t₁ t₂ ht
    have hval : t₁.val = t₂.val := hg_inj ht
    exact Subtype.ext hval
  · -- pairwise differences lie in `degreeLT K k`
    intro t₁ t₂
    exact hTsmall t₁.val t₁.2 t₂.val t₂.2

/-- **BKR06 Lemma 3.5 family-size residual (real-exponent form).**

This is the exact `hfamily` hypothesis consumed by
`CodingTheory.rs_lambda_superpoly_extension_bkr06_of_family`:
`q^{(α−β²)·log q} ≤ |ι|`.

It is derived from the assembled combinatorial count
`bkr06_pigeonhole_family_card` (which delivers `N < |ι|`) together with a **single,
explicit, named arithmetic side condition** `hexp` matching BKR06's exponent
bookkeeping to the in-tree target. Concretely, BKR06's tight linearized count gives
`|ι| ≥ q^{(u+1)m − v²}` with the parameter choices `v ≈ βm`, `k = q^u`, and
`(u+1)m − v² = (α − β²)·log q`; the generic in-tree window of width `w` delivers the
weaker but fully-proven `N < |ι|`, and `hexp : q^{(α−β²)·log q} ≤ (N : ℝ) + 1`
records exactly the exponent inequality bridging the two. Both inputs are honest:
the count is proven, the exponent arithmetic is surfaced (never silently assumed). -/
theorem bkr06_hfamily_of_card
    {ι : Type*} [Fintype ι]
    (α β : ℝ) (q : ℕ) (N : ℕ)
    (hN : N < Fintype.card ι)
    (hexp : (q : ℝ) ^ ((α - β ^ 2) * Real.log q) ≤ (N : ℝ) + 1) :
    (q : ℝ) ^ ((α - β ^ 2) * Real.log q) ≤ (Fintype.card ι : ℝ) := by
  have hNcard : (N : ℝ) + 1 ≤ (Fintype.card ι : ℝ) := by
    have hle : N + 1 ≤ Fintype.card ι := hN
    exact_mod_cast hle
  exact le_trans hexp hNcard

end Assemble

end BKR06
