/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G136AccidentTolerance

/-!
# G136 (part 2a): the energy–solution bijection — `E₂ = n · #solutions`

For a multiplicatively closed `H ∌ 0`, dividing an equal-sum quadruple `x + y = z + u` by
its fourth coordinate gives the normalized equation `a + b = c + 1`; the map

```text
(x, y; z, u)  ↦  ((x·u⁻¹, y·u⁻¹, z·u⁻¹), u)
```

is a bijection between the rung-2 equal-sum pair set and `solutions × H`.  Hence

```text
E₂(H) = #H · #{(a, b, c) ∈ H³ : a + b = c + 1}.
```

No discrete logarithms, no generator bookkeeping — multiplicative closure alone.  Combined
with part 3a, the rung-2 anchor for `#H = n` is equivalent to
`q · #solutions ≤ 3·q·n + n³`; the remaining lawful count (part 2b:
`#solutions = 3n − 3 + A` via parts 0/1) closes the accident law.

**Honest scope.**  Exact bijection; the lawful count and the accident count at the
certified primes remain.  CORE remains OPEN.  Issue #466 (G136).
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G136EnergySolutionBijection

open Finset Fintype
open ArkLib.ProximityGap.Frontier.G95CardinalityDeepCapNoGo

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The normalized rung-2 solution set `{(a,b,c) ∈ H³ : a + b = c + 1}`. -/
noncomputable def solutions (H : Finset F) : Finset ((F × F) × F) :=
  ((H ×ˢ H) ×ˢ H).filter (fun p => p.1.1 + p.1.2 = p.2 + 1)

private theorem vec_pair_eq {a b c d : F} :
    (![a, b] : Fin 2 → F) = ![c, d] ↔ a = c ∧ b = d := by
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

private theorem mem_pi2' {x y : F} {H : Finset F} (hx : x ∈ H) (hy : y ∈ H) :
    (![x, y] : Fin 2 → F) ∈ Fintype.piFinset (fun _ : Fin 2 => H) := by
  refine Fintype.mem_piFinset.mpr (fun i => ?_)
  fin_cases i
  · simpa using hx
  · simpa using hy

/-- **The energy–solution bijection.**  For multiplicatively closed `H` avoiding `0`,
`E₂(H) = #H · #solutions`. -/
theorem addREnergy_two_eq_card_mul_solutions (H : Finset F)
    (h0 : (0 : F) ∉ H)
    (hmul : ∀ x ∈ H, ∀ u ∈ H, x * u ∈ H)
    (hinv : ∀ x ∈ H, x⁻¹ ∈ H) :
    Finset.addREnergy 2 H = H.card * (solutions H).card := by
  classical
  have hne : ∀ {u : F}, u ∈ H → u ≠ 0 := by
    intro u hu h
    rw [h] at hu
    exact h0 hu
  rw [← card_energySet, ← Finset.card_product]
  apply Finset.card_bij'
    (fun (y : (Fin 2 → F) × (Fin 2 → F)) (_ : y ∈ energySet H 2) => ((y.2 1),
      (((y.1 0) * (y.2 1)⁻¹, (y.1 1) * (y.2 1)⁻¹), (y.2 0) * (y.2 1)⁻¹)))
    (fun (z : F × ((F × F) × F)) (_ : z ∈ H ×ˢ solutions H) =>
      ((![z.2.1.1 * z.1, z.2.1.2 * z.1] : Fin 2 → F),
        (![z.2.2 * z.1, z.1] : Fin 2 → F)))
  -- forward maps into H × solutions
  · intro y hy
    have hy' := Finset.mem_filter.mp hy
    have hprod := Finset.mem_product.mp hy'.1
    have hx : y.1 0 ∈ H := Fintype.mem_piFinset.mp hprod.1 0
    have hyy : y.1 1 ∈ H := Fintype.mem_piFinset.mp hprod.1 1
    have hz : y.2 0 ∈ H := Fintype.mem_piFinset.mp hprod.2 0
    have hu : y.2 1 ∈ H := Fintype.mem_piFinset.mp hprod.2 1
    have hsum : y.1 0 + y.1 1 = y.2 0 + y.2 1 := by
      have := hy'.2
      simpa [Fin.sum_univ_two] using this
    have huinv : (y.2 1)⁻¹ ∈ H := hinv _ hu
    refine Finset.mem_product.mpr ⟨hu, ?_⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨hmul _ hx _ huinv, hmul _ hyy _ huinv⟩,
        hmul _ hz _ huinv⟩, ?_⟩
    have hune := hne hu
    field_simp
    linear_combination hsum
  -- inverse maps into the energy set
  · intro z hz
    have hz' := Finset.mem_product.mp hz
    have hu : z.1 ∈ H := hz'.1
    have hsol := Finset.mem_filter.mp hz'.2
    have hzprod := Finset.mem_product.mp hsol.1
    have hab := Finset.mem_product.mp hzprod.1
    have ha : z.2.1.1 ∈ H := hab.1
    have hb : z.2.1.2 ∈ H := hab.2
    have hc : z.2.2 ∈ H := hzprod.2
    have heq : z.2.1.1 + z.2.1.2 = z.2.2 + 1 := hsol.2
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨mem_pi2' (hmul _ ha _ hu) (hmul _ hb _ hu),
        mem_pi2' (hmul _ hc _ hu) hu⟩, ?_⟩
    simp only [Fin.sum_univ_two]
    have : (z.2.1.1 + z.2.1.2) * z.1 = (z.2.2 + 1) * z.1 := by rw [heq]
    calc
      (![z.2.1.1 * z.1, z.2.1.2 * z.1] : Fin 2 → F) 0
          + (![z.2.1.1 * z.1, z.2.1.2 * z.1] : Fin 2 → F) 1
          = (z.2.1.1 + z.2.1.2) * z.1 := by
        simp [Matrix.cons_val_zero, Matrix.cons_val_one]
        ring
      _ = (z.2.2 + 1) * z.1 := this
      _ = (![z.2.2 * z.1, z.1] : Fin 2 → F) 0
          + (![z.2.2 * z.1, z.1] : Fin 2 → F) 1 := by
        simp [Matrix.cons_val_zero, Matrix.cons_val_one]
        ring
  -- left inverse
  · intro y hy
    have hy' := Finset.mem_filter.mp hy
    have hprod := Finset.mem_product.mp hy'.1
    have hu : y.2 1 ∈ H := Fintype.mem_piFinset.mp hprod.2 1
    have hune := hne hu
    refine Prod.ext ?_ ?_
    · funext i
      fin_cases i <;> simp <;> field_simp
    · funext i
      fin_cases i <;> simp <;> field_simp
  -- right inverse
  · intro z hz
    have hz' := Finset.mem_product.mp hz
    have hune := hne hz'.1
    refine Prod.ext ?_ (Prod.ext (Prod.ext ?_ ?_) ?_) <;> simp <;> field_simp

end ArkLib.ProximityGap.Frontier.G136EnergySolutionBijection

/-! ## Axiom audit -/
#print axioms
  ArkLib.ProximityGap.Frontier.G136EnergySolutionBijection.addREnergy_two_eq_card_mul_solutions
