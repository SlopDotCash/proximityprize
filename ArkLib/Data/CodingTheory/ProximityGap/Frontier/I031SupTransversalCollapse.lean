/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.I031OrbitCountPartition

/-!
# I031: the VALUE-level capstone: the per-frequency sup collapses onto a transversal (#444)

The orbit reduction (`I031DilationOrbitReduction.lean`) proved the period modulus is **constant on
each `μ_n`-coset** (`eta_norm_const_on_coset`), and `I031OrbitCountPartition.lean` proved the `q−1`
nonzero frequencies partition into **exactly `(q−1)/n` cosets** (`orbit_count`). Those two facts
were
landed separately; the named-open **value-level capstone**, the actual statement of the
`log p → log(p/n)` metric-entropy collapse as a *sup equation*, is:

> **the supremum of `b ↦ ‖η_b‖` over all of `Fₚ*` equals its supremum over any transversal of
> `Fₚ*/μ_n`** (one representative per coset, `(q−1)/n` of them).

`PeriodOrbitQuotientReduction` consumes exactly this ("the sup over `Fₚ*` = the sup over the
`(q−1)/n` orbit reps") but stated it as an assumption ("once a transversal is supplied"). This file
discharges it: it combines the proven per-coset constancy with the proven partition into a single
machine-checked `Finset.sup'` identity.

## What is landed

* `IsCosetTransversal n T`: a finset `T ⊆ Fₚ*` that meets each `μ_n`-coset of `Fₚ*` **exactly once**
  (every nonzero frequency shares a coset with a unique element of `T`).
* `eta_norm_sup'_eq_of_transversal`: for any nonempty transversal `T`,
  `(nonzeroFreqs F).sup' _ (‖η_·‖) = T.sup' _ (‖η_·‖)`. **The value collapse.** The sup over `q−1`
  frequencies is the sup over `(q−1)/n` representatives, with the SAME value (not just the same
  count). Mechanism: `nonzeroFreqs F` is the disjoint union of the cosets indexed by `T`
  (`coverPartition`), `‖η_·‖` is constant on each coset (`eta_norm_const_on_coset`), so the sup over
  the union is the sup over `T`.
* `transversal_card`: such a transversal has card exactly `(q−1)/n` (re-deriving the count from the
  value side, consistent with `orbit_count`).

## Scope (rules 3, 6, honesty contract)

This is the **value-level** I031 capstone: it completes the metric-entropy index collapse by showing
the per-frequency sup is genuinely determined by `(q−1)/n` representatives. It is **NOT** a CORE
closure and **NOT** thinness-essential: a sup of a function constant on the blocks of a partition
into `(q−1)/n` equal blocks equals the sup over a transversal **for any `n ∣ q−1`**, independent of
thickness. Its value is frontier-movement: it lands the previously-assumed sup-over-transversal
equation that `PeriodOrbitQuotientReduction` consumes, so the `log p → log(p/n)` collapse now has
its
value-level statement proven, not assumed. CORE (`M(μ_n) ≤ C·√(n·log(p/n))`) stays **OPEN**.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

Probe: `scripts/probes/probe_i031_sup_transversal_collapse.py` (prize-shaped `p ≫ n³`,
`p ≡ 1 mod n`,
`n = 8,16,32`): `sup` over `Fₚ*` equals `sup` over the `(q−1)/n` reps to machine precision; NEVER
`n = q−1`.
-/

open Finset Polynomial
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.I031DilationOrbitReduction

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **A coset transversal of `Fₚ*/μ_n`.** `T ⊆ Fₚ*` meets each `μ_n`-coset exactly once: every
nonzero
`b` shares its coset (`cosetLabel n b`) with a **unique** `t ∈ T`. Equivalently, the label map
`cosetLabel n` restricted to `T` is a bijection onto the set of all coset labels. -/
structure IsCosetTransversal (n : ℕ) (T : Finset F) : Prop where
  subset : T ⊆ nonzeroFreqs F
  /-- every nonzero frequency is labelled by some element of `T` -/
  surj : ∀ b ∈ nonzeroFreqs F, ∃ t ∈ T, cosetLabel n t = cosetLabel n b
  /-- distinct transversal elements carry distinct labels -/
  inj : ∀ t₁ ∈ T, ∀ t₂ ∈ T, cosetLabel n t₁ = cosetLabel n t₂ → t₁ = t₂

/-- **`Fₚ*` is the disjoint union of the cosets of a transversal.** Each nonzero frequency lies
in the
coset of a unique transversal element, so `nonzeroFreqs F` is the biUnion over `T` of the fibers
`{x | cosetLabel n x = cosetLabel n t}`. -/
theorem nonzeroFreqs_eq_biUnion_fibers {n : ℕ} {T : Finset F}
    (hT : IsCosetTransversal n T) :
    nonzeroFreqs F
      = T.biUnion
          (fun t => (nonzeroFreqs F).filter (fun x => cosetLabel n x = cosetLabel n t)) := by
  apply Finset.ext
  intro b
  simp only [Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · intro hb
    obtain ⟨t, htT, htlabel⟩ := hT.surj b hb
    exact ⟨t, htT, hb, htlabel.symm⟩
  · rintro ⟨t, _, hb, _⟩
    exact hb

/-- **The per-frequency sup collapses onto a transversal (the I031 value capstone).** For any
nonempty coset transversal `T` of `Fₚ*/μ_n` (one representative per `μ_n`-coset), the supremum
of the
modulus `‖η_b‖` over all `q−1` nonzero frequencies equals its supremum over the `(q−1)/n`
representatives:
`(nonzeroFreqs F).sup' _ (‖η_·‖) = T.sup' _ (‖η_·‖)`.
This is the value-level `log p → log(p/n)` metric-entropy collapse: the sup is determined by one
representative per orbit. Mechanism: `nonzeroFreqs F` is the disjoint union of the cosets indexed by
`T`, and `‖η_·‖` is constant on each coset (`eta_norm_const_on_coset`), so the union-sup is the
transversal-sup. -/
theorem eta_norm_sup'_eq_of_transversal {ψ : AddChar F ℂ} {n : ℕ} (hn : 0 < n) {T : Finset F}
    (hT : IsCosetTransversal n T) (hTne : T.Nonempty)
    (hFne : (nonzeroFreqs F).Nonempty) :
    (nonzeroFreqs F).sup' hFne (fun b => ‖eta ψ (nthRootsFinset n (1 : F)) b‖)
      = T.sup' hTne (fun b => ‖eta ψ (nthRootsFinset n (1 : F)) b‖) := by
  -- abbreviation for the objective
  set obj : F → ℝ := fun b => ‖eta ψ (nthRootsFinset n (1 : F)) b‖ with hobj
  apply le_antisymm
  · -- every frequency is dominated by its transversal representative (same coset ⇒ same value)
    apply Finset.sup'_le
    intro b hb
    obtain ⟨t, htT, htlabel⟩ := hT.surj b hb
    -- `cosetLabel n t = cosetLabel n b` ⇒ `obj b = obj t` (constant on the coset)
    have hbne : b ≠ 0 := by rwa [mem_nonzeroFreqs] at hb
    have htne : t ≠ 0 := by have := hT.subset htT; rwa [mem_nonzeroFreqs] at this
    have hb_in_t : b ∈ cosetLabel n t := by
      rw [htlabel]; exact self_mem_cosetLabel hn b
    -- `b = t * x` with `x ∈ μ_n`, so `obj b = obj (t * x) = obj t` by coset constancy
    rw [cosetLabel, dilate, Finset.mem_image] at hb_in_t
    obtain ⟨x, hx, hbx⟩ := hb_in_t
    have hobjbt : obj b = obj t := by
      rw [hobj]
      simp only
      rw [← hbx, mul_comm t x]
      exact eta_norm_const_on_coset hx t
    rw [hobjbt]
    exact Finset.le_sup' obj htT
  · -- the transversal is a subset of `nonzeroFreqs`, so its sup is ≤ the full sup
    apply Finset.sup'_le
    intro t htT
    exact Finset.le_sup' obj (hT.subset htT)

/-- **A coset transversal has card exactly `(q−1)/n`** (under a primitive `n`-th root). The label
map is injective on `T` (`hT.inj`) with image all of the `(q−1)/n` coset labels (`hT.surj` + the
labels of `T` are exactly the labels of `Fₚ*`), so `|T| = #cosets = (q−1)/n` by `orbit_count`. -/
theorem transversal_card {n : ℕ} {ζ : F} (hζprim : IsPrimitiveRoot ζ n) (hn : 0 < n)
    {T : Finset F} (hT : IsCosetTransversal n T) :
    T.card = (Fintype.card F - 1) / n := by
  rw [← orbit_count (ζ := ζ) hζprim hn]
  -- `cosetLabel n` is injective on `T`, and its image on `T` equals its image on `nonzeroFreqs`.
  have hinj : Set.InjOn (cosetLabel n) (T : Set F) := by
    intro a ha b hb hab
    exact hT.inj a (by simpa using ha) b (by simpa using hb) hab
  rw [← Finset.card_image_of_injOn hinj]
  congr 1
  -- image of `T` = image of `nonzeroFreqs` under `cosetLabel n`
  apply Finset.ext
  intro L
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨t, htT, rfl⟩
    exact ⟨t, hT.subset htT, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨t, htT, htlabel⟩ := hT.surj b hb
    exact ⟨t, htT, htlabel⟩

#print axioms eta_norm_sup'_eq_of_transversal
#print axioms transversal_card
#print axioms nonzeroFreqs_eq_biUnion_fibers

end ArkLib.ProximityGap.I031DilationOrbitReduction
