/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#466)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ60TwoRamp
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SYZ57TextbookFacts
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# SYZ61 — the syzygy kernel of a coprime triple is free of rank **exactly 2**

SYZ60 landed the *free ⇒ rank ≤ 3* half of part (a) of the two-ramp decomposition (`kernel_free`:
every submodule of `K[X]³` is free over the PID `K[X]`).  The coprimality-driven **rank drop** —
"rank exactly `2`", part (a)'s remaining content — was folded into the named residual
`MuBasisWindowIso`.  This file **removes the rank-drop from that residual, axiom-clean**.

## What lands here

Fix a field `K` and the syzygy evaluation map of an arbitrary triple `(f, g, h) : K[X]³`,
`φ : K[X]³ → K[X]`, `r ↦ f·r₀ + g·r₁ + h·r₂` (`syzygyMap`).  When the triple is *coprime* — here
`IsCoprime f g` and `IsCoprime f h`, exactly SYZ57's hypotheses — `φ` is **surjective**
(`syzygyMap_surjective`, from SYZ57's `exists_triple_repr`).  Over the commutative **domain** `K[X]`
the rank–nullity theorem (`IsDomain.hasRankNullity`) then pins the kernel rank:

  `rank K[X]³ = rank K[X] + rank (ker φ)`,  i.e. `3 = 1 + rank (ker φ)`,

so `Module.rank K[X] (ker φ) = 2` (`rank_syzygyKernel`) and, the kernel being finite free,
`Module.finrank K[X] (ker φ) = 2` (`finrank_syzygyKernel`).  Combined with SYZ60's `kernel_free`
this gives the full structural statement **"the syzygy kernel of a coprime triple is a free
`K[X]`-module of rank exactly 2"** (`syzygyKernel_free_rank_two`) — part (a) in full, no longer a
hypothesis.

## Scrupulous honesty — what this does and does NOT close

This discharges **(a) rank exactly 2** unconditionally.  It does **not** by itself discharge
`SYZ60.MuBasisWindowIso` or `SYZ44.RankNullity`, which additionally require:

* **(b) a degree-minimal (μ-)basis** `(e₁,e₂)` with product-degrees `δ₁ ≤ δ₂` and the *graded*
  windowed-generation property (the leading-vector exchange argument) — the graded refinement of
  the rank-`2` freeness landed here, and Mathlib has no graded μ-basis for coprime triples;
* the **degree-controlled Bézout surjectivity** onto `{p : deg p ≤ D}` for the *balanced-window*
  restriction (`SYZ44.RankNullity`), of which SYZ57 landed the ungraded core.

So after SYZ61 the two-ramp residual `MuBasisWindowIso` is reduced from "(a)-rank-drop + (b)" to
"(b) alone" (the graded μ-basis window count), and the degree-sum law remains **conditional** on
`RankNullity ∧ TwoRamp`.  It is *not yet* unconditional.  This does **not** claim δ* closure.

Axiom-clean; `#print axioms` at the bottom.  No `sorry`, no `native_decide`.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

open Module Polynomial

namespace ArkLib.ProximityGap.SYZ61

variable {K : Type*} [Field K]

/-! ## 1. The syzygy evaluation map and its surjectivity -/

/-- **The syzygy evaluation map.**  `φ : K[X]³ → K[X]`, `r ↦ f·r₀ + g·r₁ + h·r₂`, whose kernel is
the syzygy module of the triple `(f, g, h)`. -/
noncomputable def syzygyMap (f g h : K[X]) : (Fin 3 → K[X]) →ₗ[K[X]] K[X] where
  toFun r := f * r 0 + g * r 1 + h * r 2
  map_add' x y := by simp only [Pi.add_apply]; ring
  map_smul' c x := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[simp] theorem syzygyMap_apply (f g h : K[X]) (r : Fin 3 → K[X]) :
    syzygyMap f g h r = f * r 0 + g * r 1 + h * r 2 := rfl

/-- **Surjectivity of the syzygy map (from the Bézout seed).**  For a coprime triple every target
`p` is `φ (![p·r₁, p·r₂, p·r₃])` where `(r₁,r₂,r₃)` is SYZ57's Bézout representation of `p`. -/
theorem syzygyMap_surjective {f g h : K[X]}
    (hfg : IsCoprime f g) (hfh : IsCoprime f h) :
    Function.Surjective (syzygyMap f g h) := by
  intro p
  obtain ⟨r₁, r₂, r₃, hr⟩ := ArkLib.ProximityGap.SYZ57.exists_triple_repr hfg hfh p
  exact ⟨![r₁, r₂, r₃], by simpa using hr⟩

/-! ## 2. The rank drop: `ker φ` has rank exactly 2 -/

/-- **The syzygy kernel has `Module.finrank` exactly 2.**  The kernel is finite (submodule of the
finite free `K[X]³` over the Noetherian ring `K[X]`).  Rank–nullity over the domain `K[X]`
(`LinearMap.rank_eq_of_surjective`, instance `IsDomain.hasRankNullity`) gives
`rank K[X]³ = rank K[X] + rank (ker φ)`, i.e. `3 = 1 + rank (ker φ)`; taking `Cardinal.toNat`
(both summands finite) yields `3 = 1 + finrank (ker φ)`, hence `finrank (ker φ) = 2`. -/
theorem finrank_syzygyKernel {f g h : K[X]}
    (hfg : IsCoprime f g) (hfh : IsCoprime f h) :
    Module.finrank K[X] (LinearMap.ker (syzygyMap f g h)) = 2 := by
  have hsurj := syzygyMap_surjective hfg hfh
  have hrn := LinearMap.rank_eq_of_surjective hsurj
  rw [rank_fin_fun, rank_self] at hrn
  -- hrn : ((3 : ℕ) : Cardinal) = 1 + Module.rank K[X] (ker φ)
  have hlt : Module.rank K[X] (LinearMap.ker (syzygyMap f g h)) < Cardinal.aleph0 :=
    rank_lt_aleph0 K[X] _
  have h3 := congrArg Cardinal.toNat hrn
  rw [Cardinal.toNat_natCast, Cardinal.toNat_add Cardinal.one_lt_aleph0 hlt] at h3
  rw [(map_one Cardinal.toNat : Cardinal.toNat 1 = 1)] at h3
  -- h3 : 3 = 1 + Cardinal.toNat (rank (ker φ)) = 1 + finrank (ker φ)
  rw [Module.finrank]
  omega

/-- **The syzygy kernel has `Module.rank` exactly 2** (cardinal form of the rank drop). -/
theorem rank_syzygyKernel {f g h : K[X]}
    (hfg : IsCoprime f g) (hfh : IsCoprime f h) :
    Module.rank K[X] (LinearMap.ker (syzygyMap f g h)) = 2 := by
  rw [← Module.finrank_eq_rank, finrank_syzygyKernel hfg hfh]
  norm_num

/-! ## 3. Assembled part (a): free of rank exactly 2 -/

/-- **Part (a), in full and unconditional.**  The syzygy kernel of a coprime triple is a *free*
`K[X]`-module (SYZ60's `kernel_free`, PID structure theory) of rank *exactly 2* (this file's rank
drop, from coprimality + rank–nullity over the domain `K[X]`).  This is the complete structural
content of part (a) of SYZ44/SYZ60's two-ramp decomposition, previously carried inside the
`MuBasisWindowIso` residual. -/
theorem syzygyKernel_free_rank_two {f g h : K[X]}
    (hfg : IsCoprime f g) (hfh : IsCoprime f h) :
    Module.Free K[X] (LinearMap.ker (syzygyMap f g h)) ∧
      Module.finrank K[X] (LinearMap.ker (syzygyMap f g h)) = 2 :=
  ⟨ArkLib.ProximityGap.SYZ60.kernel_free _, finrank_syzygyKernel hfg hfh⟩

end ArkLib.ProximityGap.SYZ61

/-! ## Axiom audit -/

#print axioms ArkLib.ProximityGap.SYZ61.syzygyMap_surjective
#print axioms ArkLib.ProximityGap.SYZ61.rank_syzygyKernel
#print axioms ArkLib.ProximityGap.SYZ61.finrank_syzygyKernel
#print axioms ArkLib.ProximityGap.SYZ61.syzygyKernel_free_rank_two
