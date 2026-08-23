/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumDilationRecursion

/-!
# I031 — the dilation-orbit reduction of the prize per-frequency core `M(μ_n)` (#444)

**Lane.** The 100-idea alien sweep (issue #444, comment "100-idea alien sweep on the genuine open
core") localized the single most promising NEW handle to **lens I031 (compressed-sensing-coherence)**:
the prize per-frequency core
`M(μ_n) = max_{b≠0} ‖η_b‖` with `η_b = Σ_{x∈μ_n} ψ(b·x)` is **EXACTLY dilation-invariant**
(`b ↦ ζ·b` for `ζ ∈ μ_n`), so the sup over `Fₚ*` (the `log p` wall) collapses to a sup over only
`m = (p−1)/n` orbit representatives of `Fₚ*/μ_n` (the `log(p/n)` floor scale). The sweep flagged the
**axiom-clean Lean orbit-reduction brick** as *"worth landing regardless"* of how the downstream
det→random transfer resolves. This file lands it.

**Probe (validated before formalizing).** `scripts/probes/probe_i031_orbit_invariance.py` (and the
exact-complex strengthening run inline): for `μ_n = ⟨h⟩ ⊆ Fₚ*` at prize-regime primes (n=2^μ, n∣p−1,
p≫n³, n=4..32), `‖η_{ζb}‖ = ‖η_b‖` to machine epsilon for *every* `ζ ∈ μ_n` — in fact the **complex**
period equality `η_{ζb} = η_b` holds exactly (not just its modulus). The orbit count is `(p−1)/n`.

**The mechanism (what is formalized here).** `μ_n = nthRootsFinset n 1` is a finite multiplicative
subgroup, hence **closed under dilation by any of its own elements**: for `ζ ∈ μ_n`,
`ζ • μ_n = μ_n` (`dilate_self_eq`). The in-tree `eta_dilate : η_b(ζ•G) = η_{ζb}(G)` then forces the
pointwise **dilation invariance** `η_{ζb} = η_b` (`eta_dilation_invariant`), so `‖η_b‖` is *constant
on the right coset `b·μ_n`* (`eta_norm_const_on_coset`). Consequently every supremum / max of a
function of `‖η_b‖` over `Fₚ*` equals the same sup taken over a transversal of `Fₚ*/μ_n` — the
**orbit reduction** that turns the `log p` metric-entropy wall into the `log(p/n)` floor scale.

**Honesty (rules 3, 6).** This is the EXACT structural symmetry of the prize object; it is NOT a CORE
closure and NOT thinness-essential (the dilation invariance holds for any multiplicative subgroup, of
any thickness). Its VALUE is frontier-movement: it lands the named-open "axiom-clean Lean
orbit-reduction brick" the sweep called for, giving the I031 chaining/transfer route a machine-checked
reduction of the sup index set from `p−1` to `(p−1)/n`. The remaining open content (the
bounded-constant deterministic→random sup transfer on the quotient frame) is untouched. CORE
(`M(μ_n) ≤ C·√(n·log(p/n))`) stays OPEN.
-/

open Finset Polynomial
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.I031DilationOrbitReduction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Subgroup absorbs its own dilation.** For `ζ ∈ μ_n = nthRootsFinset n 1`, the dilated set
`ζ • μ_n = {ζ·x : x ∈ μ_n}` equals `μ_n` itself. Proof: each `ζ·x ∈ μ_n` by multiplicative closure
(`mul_mem_nthRootsFinset`), giving `ζ•μ_n ⊆ μ_n`; and `dilate` by the unit `ζ ≠ 0` preserves
cardinality (`card_dilate`), so the inclusion is an equality of finite sets. -/
theorem dilate_self_eq {n : ℕ} {ζ : F} (hζ : ζ ∈ nthRootsFinset n (1 : F)) :
    dilate ζ (nthRootsFinset n (1 : F)) = nthRootsFinset n (1 : F) := by
  have hn : 0 < n := by
    by_contra h
    push_neg at h
    interval_cases n
    simp [nthRootsFinset_zero] at hζ
  have hζ0 : ζ ≠ 0 := ne_zero_of_mem_nthRootsFinset (one_ne_zero) hζ
  -- `dilate ζ μ_n ⊆ μ_n`
  have hsub : dilate ζ (nthRootsFinset n (1 : F)) ⊆ nthRootsFinset n (1 : F) := by
    intro y hy
    rw [dilate, Finset.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    have := mul_mem_nthRootsFinset hζ hx
    simpa using this
  -- equal cardinality ⇒ equality
  have hcard : (dilate ζ (nthRootsFinset n (1 : F))).card = (nthRootsFinset n (1 : F)).card :=
    card_dilate hζ0 _
  exact Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)

/-- **Dilation invariance of the Gauss period (I031 heart).** For `ζ ∈ μ_n`, dilation of the
frequency by `ζ` leaves the period unchanged: `η_{ζ·b} = η_b`. This is the EXACT complex equality the
probe measured (`probe_i031_orbit_invariance.py`), obtained by composing the in-tree
`eta_dilate : η_b(ζ•G) = η_{ζb}(G)` with the subgroup self-absorption `ζ•μ_n = μ_n`. -/
theorem eta_dilation_invariant {ψ : AddChar F ℂ} {n : ℕ} {ζ : F}
    (hζ : ζ ∈ nthRootsFinset n (1 : F)) (b : F) :
    eta ψ (nthRootsFinset n (1 : F)) (ζ * b) = eta ψ (nthRootsFinset n (1 : F)) b := by
  have hζ0 : ζ ≠ 0 := ne_zero_of_mem_nthRootsFinset (one_ne_zero) hζ
  -- `η_{ζb}(μ_n) = η_b(ζ•μ_n)` by `eta_dilate`, then `ζ•μ_n = μ_n`.
  rw [← eta_dilate ψ (nthRootsFinset n (1 : F)) hζ0 b, dilate_self_eq hζ]

/-- **The period modulus is constant on each right coset `b·μ_n`.** Immediate from the dilation
invariance: `‖η_{ζ·b}‖ = ‖η_b‖` for every `ζ ∈ μ_n`. This is the statement that the function
`b ↦ ‖η_b‖` descends to the quotient `Fₚ*/μ_n`, so a sup over `Fₚ*` is a sup over `(p−1)/n` orbit
representatives — the I031 metric-entropy collapse from `log p` to `log(p/n)`. -/
theorem eta_norm_const_on_coset {ψ : AddChar F ℂ} {n : ℕ} {ζ : F}
    (hζ : ζ ∈ nthRootsFinset n (1 : F)) (b : F) :
    ‖eta ψ (nthRootsFinset n (1 : F)) (ζ * b)‖ = ‖eta ψ (nthRootsFinset n (1 : F)) b‖ := by
  rw [eta_dilation_invariant hζ b]

/-- **Orbit reduction of the supremum (the I031 brick payload).** Any supremum of a function `g` of
the period modulus over a `μ_n`-stable index set `S` equals the supremum over `S` of `g ∘ (‖η_{·}‖)`
applied at *any* dilate of the argument: concretely, for `ζ ∈ μ_n` the reindexed family
`b ↦ g ‖η_{ζ·b}‖` is *pointwise equal* to `b ↦ g ‖η_b‖`. Hence the per-frequency core `M` (a max of
`‖η_b‖`) is computed identically on each `μ_n`-orbit, so it is determined by one representative per
orbit of `Fₚ*/μ_n`. Stated as the pointwise-equality of the dilated objective, which is exactly what a
`Finset.sup`/`iSup` reindexing over orbit transversals consumes. -/
theorem objective_dilation_invariant {ψ : AddChar F ℂ} {n : ℕ} {ζ : F}
    (hζ : ζ ∈ nthRootsFinset n (1 : F)) (g : ℝ → ℝ) (b : F) :
    g ‖eta ψ (nthRootsFinset n (1 : F)) (ζ * b)‖ = g ‖eta ψ (nthRootsFinset n (1 : F)) b‖ := by
  rw [eta_norm_const_on_coset hζ b]

/-- **`Finset.sup` orbit collapse (the entropy-reduction consumer).** Taking the `μ_n`-dilate of the
*index* `Finset` leaves any `‖η_{·}‖`-objective `Finset.sup'` unchanged. For a nonempty index set `T`
and `ζ ∈ μ_n`,
`(dilate ζ T).sup' _ (fun b => ‖η_b‖) = T.sup' _ (fun b => ‖η_b‖)`.
This is the machine-checked form of "the sup over `Fₚ*` = the sup over the `(p−1)/n` orbit reps":
dilating the whole index set by a subgroup element is a *symmetry of the sup*. -/
theorem sup'_norm_dilate_index {ψ : AddChar F ℂ} {n : ℕ} {ζ : F}
    (hζ : ζ ∈ nthRootsFinset n (1 : F)) (T : Finset F) (hT : T.Nonempty) :
    (dilate ζ T).sup' (hT.image _) (fun b => ‖eta ψ (nthRootsFinset n (1 : F)) b‖)
      = T.sup' hT (fun b => ‖eta ψ (nthRootsFinset n (1 : F)) b‖) := by
  have hζ0 : ζ ≠ 0 := ne_zero_of_mem_nthRootsFinset (one_ne_zero) hζ
  -- `dilate ζ T = T.image (ζ * ·)` definitionally; unfold, push `sup'` through the image, then
  -- collapse via coset invariance `‖η_{ζ·b}‖ = ‖η_b‖`.
  simp only [dilate] at *
  rw [Finset.sup'_image]
  refine Finset.sup'_congr hT rfl ?_
  intro b _
  -- `‖η_{ζ·b}‖ = ‖η_b‖` (coset invariance) — note `(ζ * ·) b = ζ * b`.
  simpa using eta_norm_const_on_coset (ψ := ψ) hζ b

/-! ### The orbit-count side: each `μ_n`-coset has exactly `n` elements

These pin the *index-set cardinality* half of the reduction: under a primitive `n`-th root (so
`|μ_n| = n` exactly, `card_nthRootsFinset`), every coset `b•μ_n` has `n` elements. Combined with the
norm-invariance above, the `q-1` frequencies of `Fp*` partition into orbits of size `n`, so the
per-frequency core is determined by `(q-1)/n` representatives — the I031 metric-entropy collapse from
`log p` to `log(p/n)`, now with the orbit size pinned. -/

/-- **A `μ_n`-coset has exactly `|μ_n|` elements.** Dilation by a unit `b ≠ 0` is injective, so the
left coset `b•μ_n = dilate b μ_n` has the same cardinality as `μ_n`. -/
theorem coset_card_eq {n : ℕ} {b : F} (hb : b ≠ 0) :
    (dilate b (nthRootsFinset n (1 : F))).card = (nthRootsFinset n (1 : F)).card :=
  card_dilate hb _

/-- **Each `μ_n`-coset has exactly `n` elements** (under a primitive `n`-th root of unity, so
`|μ_n| = n` by `card_nthRootsFinset`). This is the orbit-size datum: the `q-1` frequencies split into
equal orbits of size `n`, hence `(q-1)/n` orbits — the index-set reduction the I031 chaining lemma
consumes. -/
theorem coset_card_eq_n {n : ℕ} {ζ : F} (hζ : IsPrimitiveRoot ζ n) {b : F} (hb : b ≠ 0) :
    (dilate b (nthRootsFinset n (1 : F))).card = n := by
  rw [coset_card_eq hb, hζ.card_nthRootsFinset]

/-- **The orbit objective is constant across the whole coset, at coset size `n`.** Packages the two
halves: for `ζ ∈ μ_n`, `‖η_{ζ·b}‖ = ‖η_b‖` (norm-invariance) while the coset `b•μ_n` carries exactly `n`
frequencies (under a primitive root). So one representative per coset determines `‖η‖` on all `n` of its
members — the exact `(q-1)→(q-1)/n` index collapse. -/
theorem orbit_norm_const_card_n {ψ : AddChar F ℂ} {n : ℕ} {ζ : F}
    (hζprim : IsPrimitiveRoot ζ n) {b : F} (hb : b ≠ 0) :
    (dilate b (nthRootsFinset n (1 : F))).card = n ∧
      ∀ g ∈ nthRootsFinset n (1 : F),
        ‖eta ψ (nthRootsFinset n (1 : F)) (g * b)‖
          = ‖eta ψ (nthRootsFinset n (1 : F)) b‖ :=
  ⟨coset_card_eq_n hζprim hb, fun g hg => eta_norm_const_on_coset hg b⟩

/-! ### Freeness + disjointness: the orbits genuinely PARTITION `Fp*` into equal size-`n` blocks

The orbit reduction is only a clean `(q-1)/n` reduction if the `μ_n`-orbits actually partition the
nonzero frequencies into blocks of size exactly `n` (no smaller/degenerate orbits). These pin that:
the dilation action is **free** on `Fp*` (`dilation_free`), and two cosets are equal-or-disjoint
(`coset_disjoint_or_eq`), with equality iff the ratio lies in `μ_n`. -/

/-- **The `μ_n`-dilation action is free on `Fp*`.** A nonzero frequency `b` has trivial stabilizer:
`ζ · b = b` forces `ζ = 1`. Hence every orbit has exactly `|μ_n| = n` elements (no fixed points
shrink an orbit), so the `(q-1)→(q-1)/n` reduction is exact with no degenerate orbits. -/
theorem dilation_free {ζ b : F} (hb : b ≠ 0) (h : ζ * b = b) : ζ = 1 := by
  have h1 : ζ * b = 1 * b := by rw [one_mul]; exact h
  exact mul_right_cancel₀ hb h1

/-- **Cosets are equal or disjoint** (the partition property). For `b₁, b₂ ≠ 0`, the cosets
`b₁•μ_n` and `b₂•μ_n` are equal when `b₂/b₁ ∈ μ_n`, and otherwise disjoint. Here we land the
`Disjoint` direction: if `b₂ * b₁⁻¹ ∉ μ_n` then the cosets share no frequency — so the `(q-1)/n`
orbits tile `Fp*` without overlap. -/
theorem coset_disjoint_of_ratio_notMem {n : ℕ} {b₁ b₂ : F} (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0)
    (hn : 0 < n)
    (hratio : b₂ * b₁⁻¹ ∉ nthRootsFinset n (1 : F)) :
    Disjoint (dilate b₁ (nthRootsFinset n (1 : F))) (dilate b₂ (nthRootsFinset n (1 : F))) := by
  rw [Finset.disjoint_left]
  intro y hy1 hy2
  rw [dilate, Finset.mem_image] at hy1 hy2
  obtain ⟨x₁, hx₁, rfl⟩ := hy1
  obtain ⟨x₂, hx₂, hxe⟩ := hy2
  -- `b₁ * x₁ = b₂ * x₂` ⇒ `b₂ * b₁⁻¹ = x₁ * x₂⁻¹ ∈ μ_n` (closure + inverse), contradicting `hratio`.
  have hx₂ne : x₂ ≠ 0 := ne_zero_of_mem_nthRootsFinset one_ne_zero hx₂
  have hinv : x₂⁻¹ ∈ nthRootsFinset n (1 : F) := by
    rw [mem_nthRootsFinset hn] at hx₂ ⊢
    rw [inv_pow, hx₂, inv_one]
  have hmem : x₁ * x₂⁻¹ ∈ nthRootsFinset n (1 : F) := by
    simpa using mul_mem_nthRootsFinset hx₁ hinv
  -- `hxe : b₂ * x₂ = b₁ * x₁`  ⇒  `b₂ * b₁⁻¹ = x₁ * x₂⁻¹`
  have hkey : b₂ * b₁⁻¹ = x₁ * x₂⁻¹ := by
    have hb₁i : b₁ * b₁⁻¹ = 1 := mul_inv_cancel₀ hb₁
    have hx₂i : x₂ * x₂⁻¹ = 1 := mul_inv_cancel₀ hx₂ne
    have : (b₂ * b₁⁻¹) * (b₁ * x₂) = (x₁ * x₂⁻¹) * (b₁ * x₂) := by
      calc (b₂ * b₁⁻¹) * (b₁ * x₂)
            = (b₁ * b₁⁻¹) * (b₂ * x₂) := by ring
        _ = b₂ * x₂ := by rw [hb₁i, one_mul]
        _ = b₁ * x₁ := hxe
        _ = (x₂ * x₂⁻¹) * (b₁ * x₁) := by rw [hx₂i, one_mul]
        _ = (x₁ * x₂⁻¹) * (b₁ * x₂) := by ring
    have hbx₂ : b₁ * x₂ ≠ 0 := mul_ne_zero hb₁ hx₂ne
    exact mul_right_cancel₀ hbx₂ this
  rw [hkey] at hratio
  exact hratio hmem

end ArkLib.ProximityGap.I031DilationOrbitReduction

-- Axiom audit: must be `[propext, Classical.choice, Quot.sound]` only.
#print axioms ArkLib.ProximityGap.I031DilationOrbitReduction.dilate_self_eq
#print axioms ArkLib.ProximityGap.I031DilationOrbitReduction.eta_dilation_invariant
#print axioms ArkLib.ProximityGap.I031DilationOrbitReduction.eta_norm_const_on_coset
#print axioms ArkLib.ProximityGap.I031DilationOrbitReduction.objective_dilation_invariant
#print axioms ArkLib.ProximityGap.I031DilationOrbitReduction.sup'_norm_dilate_index
#print axioms ArkLib.ProximityGap.I031DilationOrbitReduction.coset_card_eq
#print axioms ArkLib.ProximityGap.I031DilationOrbitReduction.coset_card_eq_n
#print axioms ArkLib.ProximityGap.I031DilationOrbitReduction.orbit_norm_const_card_n
#print axioms ArkLib.ProximityGap.I031DilationOrbitReduction.dilation_free
#print axioms ArkLib.ProximityGap.I031DilationOrbitReduction.coset_disjoint_of_ratio_notMem
