/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SchurLagrangeBridge

/-!
# Spec S3 — Galois / naturality substrate for the complete-homogeneous value (#444)

⚠️ **STATUS — substrate, NOT a δ* pin.** This file re-derives the GALOIS / NATURALITY substrate
for the divided-difference / complete-homogeneous object `h_r` of `SchurLagrangeBridge`. It was
written toward the F1 "complete-homogeneous spectrum bound", but that route is now **REFUTED as a
δ* pin** (see `docs/kb/deltastar-444-BCHKS-correct-object-and-attack-2026-06-16.md` §D4 and
`_BchksF1_CompleteHomogeneousFloor`): the target form `#distinct h_r ≤ n·C(s+r−1,r)` is FALSE at
the prize scale `s = 32` (`probe_spectrum_polyN_REFUTED_s32.py`), and more fundamentally
`#distinct h_r` is EXPONENTIAL while the actual bad-scalar count at δ* is `~n`, so the spectrum is
exponentially LOOSE for `#bad`. The lemmas below are kept as honest substrate.

**Why the naturality lemma `(1)` is route-INDEPENDENT and worth keeping.** The crown jewel,
`dividedDifferencePow_map`, is a hypothesis-FREE statement that `dividedDifferencePow` (hence
`schurH = h_r`) is natural under *every* field hom `σ : F →+* K`. It is char-agnostic and total
(it holds on the vanishing-denominator boundary because `σ(0⁻¹) = 0⁻¹` for any
`MonoidWithZeroHom`). This is exactly the tool needed for the **reduction-mod-`p` collision
analysis**, which is the REAL good-prime residual of #444 (the prize is decided by whether short
`±1`-relations of `2^μ`-th roots vanish *modulo the prize prime* — a question about the reduction
map `ℤ[ζ] → 𝔽_p`, i.e. about a ring hom acting on these complete-homogeneous values). Naturality
of `h_r` under that reduction is what lets one pull a char-0 vanishing statement down to char-`p`.

## Contents

* `(1)` `dividedDifferencePow_map` — **hypothesis-free naturality** of the divided difference under
  any ring hom `σ : F →+* K` (and `dividedDifferencePow_mapEquiv` for a `RingEquiv`). PROVEN
  axiom-clean. This is the crown jewel.
* `(2)` `schurH_map` / `schurH_galois` — naturality of the complete-homogeneous surrogate `schurH`,
  transported across the bridge `dividedDifferencePow_eq_schurH` + `(1)`. (Needs the
  `Set.InjOn`/`Nonempty` regime of the bridge, AND that `σ ∘ v` stays injective on `s` — supplied
  by `σ` injective, e.g. a field hom or a `RingEquiv`.)
* `(3)` `schurH_galois_pow` — the roots-of-unity Galois action `σ_a : ζ ↦ ζ^a` specialization:
  `σ(schurH s v b) = schurH s (fun i => (v i)^a) b = h_r(R^{(a)})`, `R^{(a)} = {x^a : x ∈ R}`.
* `(4)` `spectrum_card_le_galoisOrbits_mul_phi` — the count reduction
  `#{distinct h_r-values} ≤ #(Galois-orbits)·φ(s)` (Finset orbit-cover). Honest scope: this
  REDUCES the spectrum to the Galois-orbit count; it does NOT pin δ*.

## Honest scope

Substrate only. The spectrum route is refuted-as-δ*-pin (§D4). The naturality lemma `(1)` is
route-independent and is the key tool for the good-prime / reduction-mod-`p` collision analysis.
-/

set_option autoImplicit false
set_option linter.style.longLine false
-- The capstone `(4)` carries a `[DecidableEq V]` instance used only at the statement level
-- (`Finset.image` of the value/representative maps), not in the proof term.
set_option linter.unusedDecidableInType false

open Finset

namespace ArkLib.ProximityGap.SpecS3

open ProximityGap.SchurLagrange

/-! ## Part 1 — the hypothesis-free naturality of the divided difference (crown jewel) -/

section Naturality

variable {F K : Type*} [Field F] [Field K] {ι : Type*} [DecidableEq ι]

/-- **(1) Hypothesis-free naturality of the divided difference under any ring hom.**
For ANY field hom `σ : F →+* K`, and for ANY node set `s`, value map `v : ι → F`, and degree
`b : ℕ` — with NO hypotheses on `s`, `v`, or `b` — the divided difference commutes with `σ`:

  `σ (dividedDifferencePow s v b) = dividedDifferencePow s (fun i => σ (v i)) b`.

This is the crown jewel: `dividedDifferencePow` is
`Σ_{i∈s} (v i)^b · (∏_{j∈s.erase i}(v i − v j))⁻¹`, a rational expression with `ℤ` coefficients,
so it is natural under every ring hom via `map_sum`/`map_mul`/`map_pow`/`map_prod`/`map_sub`/
`map_inv₀`. It is **char-agnostic** and **total**: it holds even on the vanishing-denominator
boundary, because a field hom is a `MonoidWithZeroHom` and so `σ(0⁻¹) = (σ 0)⁻¹ = 0⁻¹`
(`map_inv₀`), i.e. `σ` maps the "junk value" `0⁻¹ = 0` to the same junk value. This route-free
naturality is precisely the tool for reduction-mod-`p` collision analysis (the real good-prime
residual of #444). -/
theorem dividedDifferencePow_map (σ : F →+* K) (s : Finset ι) (v : ι → F) (b : ℕ) :
    σ (dividedDifferencePow s v b)
      = dividedDifferencePow s (fun i => σ (v i)) b := by
  unfold dividedDifferencePow
  -- push `σ` through the outer sum, the product, the difference, the power, and the inverse.
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_mul, map_pow, map_inv₀, map_prod]
  -- the denominator: σ (∏ (v i − v j)) = ∏ (σ (v i) − σ (v j))
  refine congrArg (fun t => σ (v i) ^ b * t⁻¹) ?_
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [map_sub]

/-- **(1′) Naturality under a `RingEquiv`.** The same naturality, packaged for a field
isomorphism `σ : F ≃+* K` (the form used for an actual Galois automorphism). It is the
`(σ : F →+* K)`-instance of `dividedDifferencePow_map`. -/
theorem dividedDifferencePow_mapEquiv (σ : F ≃+* K) (s : Finset ι) (v : ι → F) (b : ℕ) :
    σ (dividedDifferencePow s v b)
      = dividedDifferencePow s (fun i => σ (v i)) b :=
  dividedDifferencePow_map (σ : F →+* K) s v b

end Naturality

/-! ## Part 2 — naturality of the complete-homogeneous surrogate `schurH` -/

section SchurNaturality

variable {F K : Type*} [Field F] [Field K] {ι : Type*} [DecidableEq ι]

/-- **(2) Naturality of `schurH` (the complete-homogeneous surrogate) — `schurH_map`.**
Transports `dividedDifferencePow_map` across the bridge `dividedDifferencePow_eq_schurH`. For an
INJECTIVE field hom `σ : F →+* K` (so that `σ ∘ v` is still injective on `s`, keeping the node set
genuine on both sides), a nonempty node set `s` with `v` injective on `s`,

  `σ (schurH s v b) = schurH s (fun i => σ (v i)) b`.

Since `schurH s v b = h_{b−(#s−1)}(v_s)`, this is the Galois-naturality of the complete-homogeneous
symmetric value: `σ(h_r(R)) = h_r(σ(R))`. -/
theorem schurH_map (σ : F →+* K) (hσ : Function.Injective σ)
    {s : Finset ι} {v : ι → F} (hvs : Set.InjOn v s) (hs : s.Nonempty) (b : ℕ) :
    σ (schurH s v b) = schurH s (fun i => σ (v i)) b := by
  -- `σ ∘ v` is injective on `s`: σ injective + v injective on s.
  have hvs' : Set.InjOn (fun i => σ (v i)) s := by
    intro x hx y hy hxy
    exact hvs hx hy (hσ hxy)
  rw [← dividedDifferencePow_eq_schurH hvs hs b, dividedDifferencePow_map σ s v b,
      dividedDifferencePow_eq_schurH hvs' hs b]

/-- **(2′) Galois-naturality of `schurH` under a field automorphism — `schurH_galois`.**
The `RingEquiv` packaging: for an actual field isomorphism `σ : F ≃+* K` (injective automatically),
`σ(h_r(R)) = h_r(σ(R))`. This is the form used for the roots-of-unity Galois action and for the
reduction-mod-`p` analysis (specialized to the appropriate hom). -/
theorem schurH_galois (σ : F ≃+* K)
    {s : Finset ι} {v : ι → F} (hvs : Set.InjOn v s) (hs : s.Nonempty) (b : ℕ) :
    σ (schurH s v b) = schurH s (fun i => σ (v i)) b :=
  schurH_map (σ : F →+* K) σ.injective hvs hs b

end SchurNaturality

/-! ## Part 3 — the roots-of-unity Galois action `σ_a : ζ ↦ ζ^a`

The cyclotomic Galois group `Gal(ℚ(ζ_s)/ℚ) ≅ (ℤ/s)^×` acts by `σ_a : ζ ↦ ζ^a` (`gcd(a,s)=1`).
On the node set `R ⊆ μ_s`, this sends `R = {x : x∈R}` to `R^{(a)} = {x^a : x∈R}`. Combining the
Galois-naturality `(2′)` with the *power-map equality* (a Galois automorphism of a cyclotomic
field literally acts as `x ↦ x^a` on the roots of unity) gives the spectrum action: the
Galois conjugate of `h_r(R)` is `h_r(R^{(a)})`. We state this DIRECTLY in terms of the power-map
on values, so it does not need a cyclotomic ambient: GIVEN that the automorphism `σ` agrees with
`x ↦ x^a` on the nodes (`hpow`), the conjugate of `schurH` is the `schurH` of the power-set. -/

section GaloisPower

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]

/-- **(3) The roots-of-unity Galois action on the spectrum — `schurH_galois_pow`.**
For a field automorphism `σ : F ≃+* F` that acts on the nodes as the power map `x ↦ x^a` (the
hypothesis `hpow : ∀ i ∈ s, σ (v i) = (v i)^a`, satisfied verbatim by the cyclotomic Galois
automorphism `σ_a : ζ ↦ ζ^a` on `μ_s`), the Galois conjugate of the complete-homogeneous value is
the value of the power-set `R^{(a)} = {x^a : x∈R}`:

  `σ (schurH s v b) = schurH s (fun i => (v i)^a) b   ( = h_r(R^{(a)}) )`.

Proof: `schurH_galois` gives `σ(schurH s v b) = schurH s (σ ∘ v) b`, and `schurH` depends on the
node values only through their restriction to `s` (the recurrence/sum are over `s`), so `hpow`
(`σ(v i) = (v i)^a` on `s`) lets us replace `σ ∘ v` by `fun i => (v i)^a`. -/
theorem schurH_galois_pow (σ : F ≃+* F)
    {s : Finset ι} {v : ι → F} (hvs : Set.InjOn v s) (hs : s.Nonempty) (b : ℕ) (a : ℕ)
    (hpow : ∀ i ∈ s, σ (v i) = (v i) ^ a) :
    σ (schurH s v b) = schurH s (fun i => (v i) ^ a) b := by
  classical
  rw [schurH_galois σ hvs hs b]
  -- `schurH` over `s` depends only on the values on `s`; replace `σ ∘ v` by `x ↦ x^a` there.
  -- Use the bridge backward, the divided-difference sum is over `s`, so `Finset.sum_congr` applies.
  have hvσ : Set.InjOn (fun i => σ (v i)) s := fun x hx y hy hxy => hvs hx hy (σ.injective hxy)
  have hva : Set.InjOn (fun i => (v i) ^ a) s := by
    intro x hx y hy hxy
    simp only at hxy
    have : σ (v x) = σ (v y) := by rw [hpow x hx, hpow y hy, hxy]
    exact hvs hx hy (σ.injective this)
  rw [← dividedDifferencePow_eq_schurH hvσ hs b, ← dividedDifferencePow_eq_schurH hva hs b]
  -- both divided differences are sums over `s` of value-only integrands; congr on `s` via `hpow`.
  unfold dividedDifferencePow
  refine Finset.sum_congr rfl (fun i hi => ?_)
  -- beta-reduce the lambdas so `σ (v ·)` and `(v ·)^a` appear literally for `hpow`.
  simp only []
  rw [hpow i hi]
  refine congrArg (fun t => ((v i) ^ a) ^ b * t⁻¹) ?_
  refine Finset.prod_congr rfl (fun j hj => ?_)
  rw [hpow j (Finset.mem_of_mem_erase hj)]

end GaloisPower

/-! ## Part 4 — the count reduction to the Galois-orbit count

The Galois-naturality `(3)` means the spectrum `{h_r(R) : R}` is closed under the Galois action: a
Galois automorphism `σ_a` sends `h_r(R)` to `h_r(R^{(a)})`. So distinct values come in
Galois-orbits, and the number of distinct values is bounded by the number of Galois-orbits of node
sets times the size `φ(s) = #(ℤ/s)^×` of the Galois group. We land this as a CLEAN Finset
orbit-cover bound: GIVEN a representative map `gRep` whose image is the Galois-orbit reps and the
per-element membership "`h_r(R)` is a Galois-conjugate of `h_r(gRep R)`, one of at most `φ` of
them", the distinct-value count is `≤ #(Galois-orbits)·φ`.

⚠️ **Honest scope: this REDUCES the spectrum to the Galois-orbit count; it does NOT pin δ*.** The
Galois-orbit count is itself exponential (the spectrum route is refuted as a δ* pin, §D4); this
lemma is the abstract content of the reduction, kept as substrate. -/

section OrbitCount

variable {ι₀ V : Type*} [DecidableEq ι₀] [DecidableEq V]

/-- **(4) Spectrum count `≤ #(Galois-orbits)·φ(s)` — `spectrum_card_le_galoisOrbits_mul_phi`.**
Let `X : Finset ι₀` be the ground set of node sets, `gRep : ι₀ → ι₀` a Galois-orbit representative
map, `f : ι₀ → V` the spectrum value map (`f R = h_r(R)`), `conj : ℕ → V → V` the Galois action on
values (`conj a w = σ_a · w`, supplied by `(3)`: `conj a (f R) = f R^{(a)}`), and `φ : ℕ` the size
of the Galois group `(ℤ/s)^×`. If every node set's value is a Galois-conjugate of its
representative's value, chosen from at most `φ` automorphisms — `f R ∈ {conj a (f (gRep R)) : a < φ}`
(hypothesis `hconj`) — then the number of distinct spectrum values is at most `#(Galois-orbits)·φ`:

  `#(X.image f) ≤ #(X.image gRep) · φ`.

Pure Finset covering: `X.image f ⊆ ⋃_{u ∈ X.image gRep} {conj a (f u) : a < φ}`, then
`Finset.card_biUnion_le` + `Finset.card_image_le`. The hypothesis `hconj` is supplied by the
Galois-closure of a Galois-stable value family (each value is a conjugate of its orbit rep, and
there are at most `φ = #(ℤ/s)^×` conjugates). **This REDUCES the spectrum to the Galois-orbit
count; it does NOT pin δ* (the orbit count is itself exponential, §D4).** -/
theorem spectrum_card_le_galoisOrbits_mul_phi
    (X : Finset ι₀) (gRep : ι₀ → ι₀) (f : ι₀ → V) (conj : ℕ → V → V) (φ : ℕ)
    (hconj : ∀ R ∈ X, ∃ a < φ, f R = conj a (f (gRep R))) :
    (X.image f).card ≤ (X.image gRep).card * φ := by
  classical
  -- the cover: each value f R lies in the small (≤ φ) set attached to its orbit representative.
  have hsub : X.image f ⊆
      (X.image gRep).biUnion (fun u => (Finset.range φ).image (fun a => conj a (f u))) := by
    intro w hw
    rw [Finset.mem_image] at hw
    obtain ⟨R, hRX, rfl⟩ := hw
    obtain ⟨a, haφ, ha⟩ := hconj R hRX
    rw [Finset.mem_biUnion]
    refine ⟨gRep R, Finset.mem_image_of_mem gRep hRX, ?_⟩
    rw [Finset.mem_image]
    exact ⟨a, Finset.mem_range.mpr haφ, ha.symm⟩
  calc (X.image f).card
      ≤ ((X.image gRep).biUnion
          (fun u => (Finset.range φ).image (fun a => conj a (f u)))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ _u ∈ X.image gRep, φ := by
        refine le_trans (Finset.card_biUnion_le) ?_
        refine Finset.sum_le_sum (fun u _ => ?_)
        exact le_trans (Finset.card_image_le) (le_of_eq (Finset.card_range φ))
    _ = (X.image gRep).card * φ := by rw [Finset.sum_const, smul_eq_mul]

end OrbitCount

end ArkLib.ProximityGap.SpecS3

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SpecS3.dividedDifferencePow_map
#print axioms ArkLib.ProximityGap.SpecS3.dividedDifferencePow_mapEquiv
#print axioms ArkLib.ProximityGap.SpecS3.schurH_map
#print axioms ArkLib.ProximityGap.SpecS3.schurH_galois
#print axioms ArkLib.ProximityGap.SpecS3.schurH_galois_pow
#print axioms ArkLib.ProximityGap.SpecS3.spectrum_card_le_galoisOrbits_mul_phi
