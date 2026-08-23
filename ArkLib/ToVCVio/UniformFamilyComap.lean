/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import VCVio

/-!
# Uniform oracle-family comap along a range-preserving injection

This file proves the dependent generalization of VCVio's
`evalDist_uniformSample_map_comp_injective` (uniform table restriction along an injection):
for oracle specs `specA : OracleSpec ιA` and `specB : OracleSpec ιB`, an injection
`e : ιA → ιB`, and per-query range equivalences `re q : specB.Range (e q) ≃ specA.Range q`,
sampling a uniform full answer table for `specB` and pulling it back along `e` (transporting
each answer through `re`) is distributed exactly as a uniform full answer table for `specA`:

```
𝒟[do let g ← $ᵗ ((q : ιB) → specB.Range q); pure (fun q : ιA => re q (g (e q)))]
  = 𝒟[$ᵗ ((q : ιA) → specA.Range q)]
```

The statement is phrased against the raw dependent function type
`(q : spec.Domain) → spec.Range q`; since `OracleReduction.OracleFamily spec` is a reducible
abbreviation for exactly this type, all lemmas below apply transparently at
`OracleFamily`/`OracleDistribution.uniform` use sites (e.g. the DSFS §5.8 hybrid table
re-keyings: `gSpec`/`eSpec` → `fsChallengeOracle` keys, and the salted → unsalted
`fsChallengeOracle` re-keying).

Proof architecture (a dependent transplant of the VCVio proof):
1. `evalDist_uniformFamily_restrict_subtype` — restricting a uniform dependent table to a
   subdomain `{b // p b}` is uniform: split the table along `Equiv.piEquivPiSubtypeProd` and
   marginalize via `evalDist_map_fst_uniformSample_prod`.
2. `evalDist_map_bijective_uniformSample` — pushing a uniform sample through any bijection of
   sampleable types is uniform (the `evalDist` form of
   `probOutput_map_bijective_uniform_cross`).
3. The comap factors as (restriction to `Set.range e`) ∘ (reindex + per-range transport),
   where the second leg is the explicit `Equiv`
   `(piCongrLeft _ eqv).symm.trans (piCongrRight re)` for the index reindexing
   `eqv : ιA ≃ {b // b ∈ Set.range e}`.

Note on finiteness hypotheses: `Finite ιB` (and per-range `Fintype`/`Nonempty` for `specB`)
are required by this proof route. At call sites where the ambient index type is infinite
(e.g. an abstract `Salt` type), first restrict to the finite block actually read (e.g. the
`Set.range SaltCodec.encode` block) and apply the lemma there.
-/

open OracleComp OracleSpec

universe u

section UniformFamilyComap

/-- **Pushing a uniform sample through a bijection is uniform.** `evalDist` form of
`probOutput_map_bijective_uniform_cross`: for sampleable types `α`, `β` and a bijection
`f : α → β`, mapping the uniform sample on `α` through `f` gives the uniform distribution
on `β`. -/
lemma evalDist_map_bijective_uniformSample {α β : Type} [SampleableType α] [SampleableType β]
    [Finite α] (f : α → β) (hf : Function.Bijective f) :
    𝒟[f <$> ($ᵗ α)] = 𝒟[$ᵗ β] := by
  refine evalDist_ext fun y => ?_
  exact probOutput_map_bijective_uniform_cross α f hf y

/-- **Restricting a uniform dependent answer table to a subdomain is uniform.**

For a uniform full table `g : (q : ι) → spec.Range q` and a predicate `p` on the domain,
the restriction `fun s : {b // p b} => g s.1` is itself a uniform table for the restricted
spec. This is the dependent form of the "marginalize a product distribution onto a block of
coordinates" step. -/
lemma evalDist_uniformFamily_restrict_subtype
    {ι : Type} {spec : OracleSpec ι} (p : ι → Prop) [DecidablePred p]
    [Finite ι] [∀ q : ι, Fintype (spec.Range q)] [∀ q : ι, Nonempty (spec.Range q)]
    [SampleableType ((q : ι) → spec.Range q)]
    [SampleableType ((s : {b // p b}) → spec.Range s.1)] :
    𝒟[do let g ← $ᵗ ((q : ι) → spec.Range q); pure (fun s : {b // p b} => g s.1)]
      = 𝒟[$ᵗ ((s : {b // p b}) → spec.Range s.1)] := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  -- Complement block: coordinates outside `p`.
  letI : Fintype ((s : {b // ¬ p b}) → spec.Range s.1) := Pi.instFintype
  haveI : Nonempty ((s : {b // ¬ p b}) → spec.Range s.1) :=
    ⟨fun s => Classical.arbitrary _⟩
  letI instC : SampleableType ((s : {b // ¬ p b}) → spec.Range s.1) :=
    SampleableType.ofFintype _
  -- Restricted block instances for the product draw.
  letI : Fintype ((s : {b // p b}) → spec.Range s.1) := Fintype.ofFinite _
  haveI : Nonempty ((s : {b // p b}) → spec.Range s.1) :=
    ⟨fun s => Classical.arbitrary _⟩
  letI instP : SampleableType
      (((s : {b // p b}) → spec.Range s.1) × ((s : {b // ¬ p b}) → spec.Range s.1)) :=
    SampleableType.ofFintype _
  -- Split the full table into the `p`-block and its complement.
  set Φ : ((q : ι) → spec.Range q) ≃
      (((s : {b // p b}) → spec.Range s.1) × ((s : {b // ¬ p b}) → spec.Range s.1)) :=
    Equiv.piEquivPiSubtypeProd p spec.Range with hΦ
  have hmap : (do let g ← $ᵗ ((q : ι) → spec.Range q); pure (fun s : {b // p b} => g s.1))
      = (Prod.fst ∘ Φ) <$> ($ᵗ ((q : ι) → spec.Range q)) := by
    simp only [bind_pure_comp]
    rfl
  have hcross : 𝒟[Φ <$> ($ᵗ ((q : ι) → spec.Range q))]
      = 𝒟[$ᵗ (((s : {b // p b}) → spec.Range s.1) × ((s : {b // ¬ p b}) → spec.Range s.1))] :=
    evalDist_map_bijective_uniformSample Φ Φ.bijective
  calc 𝒟[do let g ← $ᵗ ((q : ι) → spec.Range q); pure (fun s : {b // p b} => g s.1)]
      = 𝒟[(Prod.fst ∘ Φ) <$> ($ᵗ ((q : ι) → spec.Range q))] := by rw [hmap]
    _ = 𝒟[Prod.fst <$> (Φ <$> ($ᵗ ((q : ι) → spec.Range q)))] := by
        simp only [Functor.map_map, Function.comp_def]
    _ = 𝒟[Prod.fst <$>
          ($ᵗ (((s : {b // p b}) → spec.Range s.1) × ((s : {b // ¬ p b}) → spec.Range s.1)))] := by
        rw [evalDist_map, hcross, ← evalDist_map]
    _ = 𝒟[$ᵗ ((s : {b // p b}) → spec.Range s.1)] := evalDist_map_fst_uniformSample_prod

/-- **Uniform oracle-family comap along a range-preserving injection** (dependent
generalization of `evalDist_uniformSample_map_comp_injective`).

For an injection `e : ιA → ιB` between oracle domains and per-query range equivalences
`re q : specB.Range (e q) ≃ specA.Range q`, drawing a uniform full table for `specB` and
pulling it back along `e` (transporting answers through `re`) is distributed as a uniform
full table for `specA`.

`Finite ιB` and the per-range `Fintype`/`Nonempty` hypotheses on `specB` are inherent to
the table-splitting proof; at call sites with an infinite ambient domain, restrict to the
finite block actually read before applying. -/
theorem evalDist_uniformFamily_comap_injective
    {ιA ιB : Type} {specA : OracleSpec ιA} {specB : OracleSpec ιB}
    [Finite ιA] [Finite ιB]
    [∀ q : ιB, Fintype (specB.Range q)] [∀ q : ιB, Nonempty (specB.Range q)]
    [SampleableType ((q : ιA) → specA.Range q)]
    [SampleableType ((q : ιB) → specB.Range q)]
    (e : ιA → ιB) (he : Function.Injective e)
    (re : ∀ q : ιA, specB.Range (e q) ≃ specA.Range q) :
    𝒟[do let g ← $ᵗ ((q : ιB) → specB.Range q); pure (fun q : ιA => re q (g (e q)))]
      = 𝒟[$ᵗ ((q : ιA) → specA.Range q)] := by
  classical
  letI : Fintype ιA := Fintype.ofFinite ιA
  letI : Fintype ιB := Fintype.ofFinite ιB
  letI : ∀ q : ιA, Fintype (specA.Range q) := fun q => Fintype.ofEquiv _ (re q)
  set p : ιB → Prop := fun b => b ∈ Set.range e with hp
  -- Restricted block: the coordinates of the `specB` table actually read by the comap.
  letI : Fintype ((s : {b // p b}) → specB.Range s.1) := Pi.instFintype
  haveI : Nonempty ((s : {b // p b}) → specB.Range s.1) :=
    ⟨fun s => Classical.arbitrary _⟩
  letI instR : SampleableType ((s : {b // p b}) → specB.Range s.1) :=
    SampleableType.ofFintype _
  -- Reindex + per-range transport from the restricted block to `specA` tables.
  set J : ((s : {b // p b}) → specB.Range s.1) → ((q : ιA) → specA.Range q) :=
    fun k q => re q (k ⟨e q, Set.mem_range_self q⟩) with hJ
  -- Index reindexing equivalence `ιA ≃ {b // p b}`, with `eqv a = ⟨e a, _⟩` definitionally.
  have heqv_left : ∀ a : ιA, (Set.mem_range_self (f := e) a).choose = a := fun a =>
    he (Set.mem_range_self (f := e) a).choose_spec
  set eqv : ιA ≃ {b // p b} :=
    { toFun := fun a => ⟨e a, Set.mem_range_self a⟩
      invFun := fun s => s.2.choose
      left_inv := heqv_left
      right_inv := fun s => Subtype.ext s.2.choose_spec } with heqv
  -- `J` is the forward map of an explicit dependent Pi equivalence: first reindex the
  -- restricted table along `eqv`, then transport each response through `re`.
  let K : ((s : {b // p b}) → specB.Range s.1) ≃ ((q : ιA) → specA.Range q) :=
    (Equiv.piCongrLeft (fun s : {b // p b} => specB.Range s.1) eqv).symm.trans
      (Equiv.piCongrRight re)
  have hJ_eq : J = K := by
    funext k q
    simp [J, K, Equiv.piCongrLeft, Equiv.piCongrLeft', eqv]
  have hJbij : Function.Bijective J := by
    rw [hJ_eq]
    exact K.bijective
  -- Factor the comap through the restricted block, then transport along `J`.
  have hfactor :
      (do let g ← $ᵗ ((q : ιB) → specB.Range q); pure (fun q : ιA => re q (g (e q))))
        = J <$> (do
            let g ← $ᵗ ((q : ιB) → specB.Range q)
            pure (fun s : {b // p b} => g s.1)) := by
    simp only [bind_pure_comp, Functor.map_map]
    rfl
  rw [hfactor, evalDist_map, evalDist_uniformFamily_restrict_subtype p, ← evalDist_map]
  exact evalDist_map_bijective_uniformSample J hJbij

/-- `cast` form of `evalDist_uniformFamily_comap_injective`: when the range preservation is
given as a type *equality* `hr q : specB.Range (e q) = specA.Range q` (the form arising from
definitional range agreement at DSFS use sites), pulling back a uniform `specB` table along
`e` with a `cast` transport is uniform for `specA`. -/
theorem evalDist_uniformFamily_comap_injective_cast
    {ιA ιB : Type} {specA : OracleSpec ιA} {specB : OracleSpec ιB}
    [Finite ιA] [Finite ιB]
    [∀ q : ιB, Fintype (specB.Range q)] [∀ q : ιB, Nonempty (specB.Range q)]
    [SampleableType ((q : ιA) → specA.Range q)]
    [SampleableType ((q : ιB) → specB.Range q)]
    (e : ιA → ιB) (he : Function.Injective e)
    (hr : ∀ q : ιA, specB.Range (e q) = specA.Range q) :
    𝒟[do let g ← $ᵗ ((q : ιB) → specB.Range q); pure (fun q : ιA => cast (hr q) (g (e q)))]
      = 𝒟[$ᵗ ((q : ιA) → specA.Range q)] :=
  evalDist_uniformFamily_comap_injective e he (fun q => Equiv.cast (hr q))

/-- Bijective-reindexing special case of `evalDist_uniformFamily_comap_injective`: comapping a
uniform table along an index *equivalence* (with per-range transports) is uniform. Useful for
re-keying eager tables along a renaming of the query domain (e.g. salt-erasure re-keyings). -/
theorem evalDist_uniformFamily_comap_equiv
    {ιA ιB : Type} {specA : OracleSpec ιA} {specB : OracleSpec ιB}
    [Finite ιA] [Finite ιB]
    [∀ q : ιB, Fintype (specB.Range q)] [∀ q : ιB, Nonempty (specB.Range q)]
    [SampleableType ((q : ιA) → specA.Range q)]
    [SampleableType ((q : ιB) → specB.Range q)]
    (e : ιA ≃ ιB) (re : ∀ q : ιA, specB.Range (e q) ≃ specA.Range q) :
    𝒟[do let g ← $ᵗ ((q : ιB) → specB.Range q); pure (fun q : ιA => re q (g (e q)))]
      = 𝒟[$ᵗ ((q : ιA) → specA.Range q)] :=
  evalDist_uniformFamily_comap_injective e e.injective re

end UniformFamilyComap

#print axioms evalDist_map_bijective_uniformSample
#print axioms evalDist_uniformFamily_restrict_subtype
#print axioms evalDist_uniformFamily_comap_injective
#print axioms evalDist_uniformFamily_comap_injective_cast
#print axioms evalDist_uniformFamily_comap_equiv
