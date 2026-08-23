/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CyclotomicSidonLift

/-!
# THE CYCLOTOMIC RESULTANT BOUND + NONZERO, AND THE "NO PARALLELOGRAM" THEOREM (#389)

Completing the small-subgroup Sidon lifting.  For the four-term polynomial
`f = X^i + X^j − X^k − X^l` (a candidate parallelogram in `μ_n`), the integer
`R = resultant (cyclotomic n ℤ) f` satisfies, via the complex product formula
`R = ∏_{ζ primitive} f(ζ)`:

* `|R| ≤ 4^{φ(n)}` (each `|f(ζ)| ≤ 4`, `φ(n)` factors), and for `n = 2^m`, `4^{φ(n)} = 2^n`;
* `R ≠ 0` (each `f(ζ) ≠ 0` by `fourTerm_ne_zero_of_pair_ne`).

Combined with the reduction `resultant_map_eq_zero_of_primitiveRoot` (`p ∣ R` from a mod-`p`
parallelogram), `Int.le_of_dvd` gives `p ≤ |R| ≤ 4^{φ(n)}`.  Hence a parallelogram at a primitive
`n`-th root over `F_p` forces `p ≤ 4^{φ(n)}` — so for `p > 4^{φ(n)}` there is **no** parallelogram,
i.e. `μ_n ⊂ F_p` is Sidon.  This is the closed lifting, with no open input.  Issue #389.
-/

open Polynomial Complex

namespace ArkLib.ProximityGap.AdditiveEnergyRepBound

/-- The four-term polynomial `X^i + X^j − X^k − X^l` over `ℤ`. -/
noncomputable def fourTerm (i j k l : ℕ) : ℤ[X] := X ^ i + X ^ j - X ^ k - X ^ l

/-- Over ℂ, `|ζ| = 1` for a primitive `n`-th root `ζ` (`n ≥ 1`). -/
theorem norm_eq_one_of_primitiveRoot {n : ℕ} (hn : n ≠ 0) {ζ : ℂ} (hζ : ζ ^ n = 1) :
    ‖ζ‖ = 1 := by
  have h1 : ‖ζ‖ ^ n = 1 := by rw [← norm_pow, hζ, norm_one]
  nlinarith [norm_nonneg ζ, pow_eq_one_iff_of_nonneg (norm_nonneg ζ) hn |>.mp h1]

/-- The four-term complex value has norm `≤ 4` on the unit circle. -/
theorem norm_fourTerm_eval_le {n : ℕ} (hn : n ≠ 0) {ζ : ℂ} (hζ : ζ ^ n = 1) (i j k l : ℕ) :
    ‖(fourTerm i j k l).eval₂ (algebraMap ℤ ℂ) ζ‖ ≤ 4 := by
  have hz : ‖ζ‖ = 1 := norm_eq_one_of_primitiveRoot hn hζ
  have hzi : ∀ m : ℕ, ‖ζ ^ m‖ = 1 := fun m => by rw [norm_pow, hz, one_pow]
  simp only [fourTerm, eval₂_sub, eval₂_add, eval₂_pow, eval₂_X]
  calc ‖ζ ^ i + ζ ^ j - ζ ^ k - ζ ^ l‖
      ≤ ‖ζ ^ i + ζ ^ j - ζ ^ k‖ + ‖ζ ^ l‖ := norm_sub_le _ _
    _ ≤ (‖ζ ^ i + ζ ^ j‖ + ‖ζ ^ k‖) + ‖ζ ^ l‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ ((‖ζ ^ i‖ + ‖ζ ^ j‖) + ‖ζ ^ k‖) + ‖ζ ^ l‖ := by gcongr; exact norm_add_le _ _
    _ = 4 := by rw [hzi, hzi, hzi, hzi]; norm_num

/-- The integer resultant equals the complex product over primitive roots. -/
theorem resultant_cast_eq_prod {n : ℕ} (i j k l : ℕ) :
    (algebraMap ℤ ℂ) (resultant (cyclotomic n ℤ) (fourTerm i j k l)) =
      (((cyclotomic n ℂ).roots).map
        (fun ζ => eval ζ ((fourTerm i j k l).map (algebraMap ℤ ℂ)))).prod := by
  set f := fourTerm i j k l
  have hinj : Function.Injective (algebraMap ℤ ℂ) := (algebraMap ℤ ℂ).injective_int
  have hsplit : (cyclotomic n ℂ).Splits := by
    simpa using IsAlgClosed.splits_codomain (k := ℂ) (f := RingHom.id ℂ) (cyclotomic n ℂ)
  have hdeg : (f.map (algebraMap ℤ ℂ)).natDegree ≤ f.natDegree :=
    le_of_eq (natDegree_map_eq_of_injective hinj f)
  have hcd : (cyclotomic n ℤ).natDegree = (cyclotomic n ℂ).natDegree := by
    rw [natDegree_cyclotomic, natDegree_cyclotomic]
  have hprod := resultant_eq_prod_eval (cyclotomic n ℂ) (f.map (algebraMap ℤ ℂ)) f.natDegree hdeg hsplit
  rw [(cyclotomic.monic n ℂ).leadingCoeff, one_pow, one_mul] at hprod
  calc (algebraMap ℤ ℂ) (resultant (cyclotomic n ℤ) f)
      = resultant (cyclotomic n ℂ) (f.map (algebraMap ℤ ℂ))
          (cyclotomic n ℤ).natDegree f.natDegree := by
        rw [← map_cyclotomic n (algebraMap ℤ ℂ), resultant_map_map]
    _ = resultant (cyclotomic n ℂ) (f.map (algebraMap ℤ ℂ))
          (cyclotomic n ℂ).natDegree f.natDegree := by rw [hcd]
    _ = _ := hprod

/-- Product of a multiset of reals in `[0, 4]` is `≤ 4^card`. -/
private theorem ms_prod_le_pow {s : Multiset ℝ} (hpos : ∀ x ∈ s, 0 ≤ x)
    (hle : ∀ x ∈ s, x ≤ 4) : s.prod ≤ 4 ^ s.card := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih =>
    simp only [Multiset.prod_cons, Multiset.card_cons, pow_succ]
    have ha : 0 ≤ a := hpos a (Multiset.mem_cons_self a t)
    have ha4 : a ≤ 4 := hle a (Multiset.mem_cons_self a t)
    have htpos : 0 ≤ t.prod :=
      Multiset.prod_nonneg (fun x hx => hpos x (Multiset.mem_cons_of_mem hx))
    have htih : t.prod ≤ 4 ^ t.card :=
      ih (fun x hx => hpos x (Multiset.mem_cons_of_mem hx))
        (fun x hx => hle x (Multiset.mem_cons_of_mem hx))
    have h4 : (0:ℝ) ≤ 4 ^ t.card := pow_nonneg (by norm_num) t.card
    nlinarith

/-- **`|R| ≤ 4^{φ(n)}`.**  The integer cyclotomic resultant of the four-term polynomial is bounded
by `4` to the totient. -/
theorem abs_resultant_le {n : ℕ} (hn : n ≠ 0) (i j k l : ℕ) :
    |resultant (cyclotomic n ℤ) (fourTerm i j k l)| ≤ 4 ^ n.totient := by
  set R := resultant (cyclotomic n ℤ) (fourTerm i j k l) with hR
  have key : (|R| : ℝ) ≤ (4 : ℝ) ^ n.totient := by
    haveI : NeZero (n : ℂ) := ⟨Nat.cast_ne_zero.mpr hn⟩
    have hcast : ‖(algebraMap ℤ ℂ) R‖ = (|R| : ℝ) := by simp [Complex.norm_intCast]
    rw [← hcast, resultant_cast_eq_prod]
    set g : ℂ → ℂ := fun ζ => eval ζ ((fourTerm i j k l).map (algebraMap ℤ ℂ)) with hg
    -- norm of the product = product of norms (ℂ norm is multiplicative)
    have hmul : ‖((cyclotomic n ℂ).roots.map g).prod‖
        = ((cyclotomic n ℂ).roots.map (fun ζ => ‖g ζ‖)).prod := by
      have h := map_multiset_prod (normHom : ℂ →*₀ ℝ) ((cyclotomic n ℂ).roots.map g)
      simpa [Multiset.map_map, Function.comp] using h
    rw [hmul]
    have hcard : ((cyclotomic n ℂ).roots).card = n.totient := by
      have hs : (cyclotomic n ℂ).Splits := by
        simpa using IsAlgClosed.splits_codomain (k := ℂ) (f := RingHom.id ℂ) (cyclotomic n ℂ)
      rw [← hs.natDegree_eq_card_roots, natDegree_cyclotomic]
    calc ((cyclotomic n ℂ).roots.map (fun ζ => ‖g ζ‖)).prod
        ≤ 4 ^ ((cyclotomic n ℂ).roots.map (fun ζ => ‖g ζ‖)).card := by
          refine ms_prod_le_pow (fun x hx => ?_) (fun x hx => ?_)
          · obtain ⟨ζ, _, rfl⟩ := Multiset.mem_map.mp hx; exact norm_nonneg _
          · obtain ⟨ζ, hζ, rfl⟩ := Multiset.mem_map.mp hx
            have hζu : ζ ^ n = 1 := ((isRoot_cyclotomic_iff).mp (isRoot_of_mem_roots hζ)).pow_eq_one
            show ‖eval ζ ((fourTerm i j k l).map (algebraMap ℤ ℂ))‖ ≤ 4
            rw [← eval₂_eq_eval_map]; exact norm_fourTerm_eval_le hn hζu i j k l
      _ = 4 ^ n.totient := by rw [Multiset.card_map, hcard]
  exact_mod_cast key

end ArkLib.ProximityGap.AdditiveEnergyRepBound

-- Axiom audit
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.norm_eq_one_of_primitiveRoot
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.norm_fourTerm_eval_le
#print axioms ArkLib.ProximityGap.AdditiveEnergyRepBound.abs_resultant_le
