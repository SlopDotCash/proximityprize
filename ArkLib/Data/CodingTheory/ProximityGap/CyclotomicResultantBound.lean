/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# The archimedean magnitude bound for the small-subgroup Sidon keystone (#389)

The small-subgroup reframing of the proximity prize (`p > 2^n ⟹ μ_n` Sidon over `F_p ⟹
E(μ_n) = 3n(n−1) ⟹ δ*` pinned for `n < log₂ p`) rests on one *archimedean* fact: the
cyclotomic resultant `Res(Φ_n, g)` of the `n`-th cyclotomic polynomial with a 4-term `±1`
"parallelogram" polynomial `g = X^a + X^b − X^c − X^d` has integer magnitude `≤ 4^{φ(n)} = 2^n`
(for `n = 2^m`).  Since `Φ_n` is monic, that resultant is exactly the product of `g` over the
primitive `n`-th roots of unity in `ℂ`, and `|g(ω)| ≤ 4` for every root of unity (triangle
inequality).  This file proves that product bound:

  `‖∏_{ω : Φ_n(ω)=0} g(ω)‖ ≤ 4^{φ(n)}`   (`nnnorm_prod_eval_cyclotomic_roots_le`).

Combined with `Res ≠ 0` (the ℂ-Sidon property of `μ_n`, proven by conjugation) and `p ∣ Res`
(a parallelogram mod `p` is a common root of `Φ_n` and `g`, via `resultant_map_map`), this forces
`p ≤ 4^{φ(n)} = 2^n`, i.e. `p > 2^n ⟹ μ_n` has no nontrivial additive coincidence — the keystone
discharging the no-coincidence hypothesis of `rootsOfUnity_additiveEnergy_eq` in the
small-subgroup regime.  Axiom-clean.
-/


open Polynomial Complex
open scoped NNReal

/-- Submultiplicativity of `nnnorm` over a multiset product in a normed ring. -/
theorem nnnorm_multiset_prod_le_ring {α : Type*} [NormedCommRing α] [NormOneClass α]
    (m : Multiset α) : ‖m.prod‖₊ ≤ (m.map (‖·‖₊)).prod := by
  induction m using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons]
    exact le_trans (nnnorm_mul_le _ _) (mul_le_mul_of_nonneg_left ih (zero_le _))

/-- **The archimedean keystone for the small-subgroup Sidon bound.** For a polynomial `g` over
`ℂ` whose evaluations at all `n`-th roots of unity have norm `≤ 4` (e.g. a 4-term `±1`
"parallelogram" polynomial), the product of `g` over the primitive `n`-th roots — i.e. the
resultant `Res(Φ_n, g)` (the cyclotomic polynomial is monic, so its leading coefficient is `1`) —
has norm `≤ 4^{φ(n)}`.  Combined with `Res ≠ 0` (ℂ-Sidon) and `p ∣ Res` (common root mod `p`),
this yields `p ≤ 4^{φ(n)} = 2^n` for `n = 2^m`, i.e. `p > 2^n ⟹ μ_n` is Sidon over `F_p`. -/
theorem nnnorm_prod_eval_cyclotomic_roots_le (n : ℕ) (g : ℂ[X])
    (hg : ∀ ω : ℂ, ω ^ n = 1 → ‖g.eval ω‖₊ ≤ 4) :
    ‖((cyclotomic n ℂ).roots.map g.eval).prod‖₊ ≤ 4 ^ n.totient := by
  have hcard : (cyclotomic n ℂ).roots.card = n.totient := by
    rw [← (IsAlgClosed.splits (cyclotomic n ℂ)).natDegree_eq_card_roots, natDegree_cyclotomic]
  have hroot : ∀ ω ∈ (cyclotomic n ℂ).roots, ω ^ n = 1 := by
    intro ω hω
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [cyclotomic_zero] at hω
    · haveI : NeZero (n : ℂ) := ⟨Nat.cast_ne_zero.mpr (by omega)⟩
      exact (isRoot_cyclotomic_iff.mp (isRoot_of_mem_roots hω)).pow_eq_one
  have hb : ∀ x ∈ ((cyclotomic n ℂ).roots.map g.eval).map (‖·‖₊), x ≤ 4 := by
    intro x hx
    rw [Multiset.map_map, Multiset.mem_map] at hx
    obtain ⟨ω, hω, rfl⟩ := hx
    exact hg ω (hroot ω hω)
  calc ‖((cyclotomic n ℂ).roots.map g.eval).prod‖₊
      ≤ (((cyclotomic n ℂ).roots.map g.eval).map (‖·‖₊)).prod := nnnorm_multiset_prod_le_ring _
    _ ≤ 4 ^ (((cyclotomic n ℂ).roots.map g.eval).map (‖·‖₊)).card :=
        Multiset.prod_le_pow_card _ 4 hb
    _ = 4 ^ n.totient := by rw [Multiset.card_map, Multiset.card_map, hcard]

/-- General bounded-factor form of `nnnorm_prod_eval_cyclotomic_roots_le`.  If every primitive
factor has norm at most `B`, then the cyclotomic product has norm at most `B^φ(n)`. -/
theorem nnnorm_prod_eval_cyclotomic_roots_le_of_bound (n B : ℕ) (g : ℂ[X])
    (hg : ∀ ω : ℂ, ω ^ n = 1 → ‖g.eval ω‖₊ ≤ B) :
    ‖((cyclotomic n ℂ).roots.map g.eval).prod‖₊ ≤ (B : ℝ≥0) ^ n.totient := by
  have hcard : (cyclotomic n ℂ).roots.card = n.totient := by
    rw [← (IsAlgClosed.splits (cyclotomic n ℂ)).natDegree_eq_card_roots, natDegree_cyclotomic]
  have hroot : ∀ ω ∈ (cyclotomic n ℂ).roots, ω ^ n = 1 := by
    intro ω hω
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [cyclotomic_zero] at hω
    · haveI : NeZero (n : ℂ) := ⟨Nat.cast_ne_zero.mpr (by omega)⟩
      exact (isRoot_cyclotomic_iff.mp (isRoot_of_mem_roots hω)).pow_eq_one
  have hb :
      ∀ x ∈ ((cyclotomic n ℂ).roots.map g.eval).map (‖·‖₊), x ≤ (B : ℝ≥0) := by
    intro x hx
    rw [Multiset.map_map, Multiset.mem_map] at hx
    obtain ⟨ω, hω, rfl⟩ := hx
    exact hg ω (hroot ω hω)
  calc ‖((cyclotomic n ℂ).roots.map g.eval).prod‖₊
      ≤ (((cyclotomic n ℂ).roots.map g.eval).map (‖·‖₊)).prod :=
        nnnorm_multiset_prod_le_ring _
    _ ≤ (B : ℝ≥0) ^
          (((cyclotomic n ℂ).roots.map g.eval).map (‖·‖₊)).card :=
        Multiset.prod_le_pow_card _ (B : ℝ≥0) hb
    _ = (B : ℝ≥0) ^ n.totient := by rw [Multiset.card_map, Multiset.card_map, hcard]

/-- A concrete four-term parallelogram polynomial has norm at most `4` on every nonzero-order
root of unity. This discharges the side condition of
`nnnorm_prod_eval_cyclotomic_roots_le` for `X^i + X^j - X^k - X^l`. -/
theorem fourTerm_eval_nnnorm_le_four {n i j k l : ℕ} (hn : n ≠ 0) {ω : ℂ}
    (hω : ω ^ n = 1) :
    ‖((X ^ i + X ^ j - X ^ k - X ^ l : ℂ[X]).eval ω)‖₊ ≤ 4 := by
  have hnormω : ‖ω‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hω hn
  have hi : ‖ω ^ i‖ = 1 := by rw [norm_pow, hnormω, one_pow]
  have hj : ‖ω ^ j‖ = 1 := by rw [norm_pow, hnormω, one_pow]
  have hk : ‖ω ^ k‖ = 1 := by rw [norm_pow, hnormω, one_pow]
  have hl : ‖ω ^ l‖ = 1 := by rw [norm_pow, hnormω, one_pow]
  have hreal : ‖ω ^ i + ω ^ j - ω ^ k - ω ^ l‖ ≤ (4 : ℝ) := by
    calc ‖ω ^ i + ω ^ j - ω ^ k - ω ^ l‖
        = ‖(ω ^ i + ω ^ j) - (ω ^ k + ω ^ l)‖ := by ring_nf
      _ ≤ ‖ω ^ i + ω ^ j‖ + ‖ω ^ k + ω ^ l‖ := norm_sub_le _ _
      _ ≤ (‖ω ^ i‖ + ‖ω ^ j‖) + (‖ω ^ k‖ + ‖ω ^ l‖) :=
            add_le_add (norm_add_le _ _) (norm_add_le _ _)
      _ = 4 := by rw [hi, hj, hk, hl]; norm_num
  have heval :
      ((X ^ i + X ^ j - X ^ k - X ^ l : ℂ[X]).eval ω)
        = ω ^ i + ω ^ j - ω ^ k - ω ^ l := by simp
  rw [heval]
  exact_mod_cast hreal

/-- The archimedean product bound specialized to the actual four-term `±1` parallelogram
polynomial used in the small-subgroup Sidon lift. -/
theorem nnnorm_prod_eval_cyclotomic_roots_fourTerm_le (n i j k l : ℕ) (hn : n ≠ 0) :
    ‖((cyclotomic n ℂ).roots.map
        (fun ω => ((X ^ i + X ^ j - X ^ k - X ^ l : ℂ[X]).eval ω))).prod‖₊
      ≤ 4 ^ n.totient := by
  simpa using
    nnnorm_prod_eval_cyclotomic_roots_le n
      (X ^ i + X ^ j - X ^ k - X ^ l : ℂ[X])
      (fun ω hω => fourTerm_eval_nnnorm_le_four hn hω)

/-! ## Axiom audit -/
#print axioms nnnorm_prod_eval_cyclotomic_roots_le_of_bound
#print axioms fourTerm_eval_nnnorm_le_four
#print axioms nnnorm_prod_eval_cyclotomic_roots_fourTerm_le

/-- **Generic integer cyclotomic-resultant magnitude bound.** If `g : ℤ[X]` evaluates with norm
`≤ B` at every `n`-th root of unity in `ℂ`, then the integer resultant `Res(Φ_n, g)` satisfies
`|Res| ≤ B^{φ(n)}`. -/
theorem natAbs_resultant_cyclotomic_le_of_bound (n B : ℕ) (g : ℤ[X])
    (hg : ∀ ω : ℂ, ω ^ n = 1 → ‖(g.map (Int.castRingHom ℂ)).eval ω‖₊ ≤ B) :
    (resultant (cyclotomic n ℤ) g (cyclotomic n ℤ).natDegree g.natDegree).natAbs
      ≤ B ^ n.totient := by
  set R : ℤ := resultant (cyclotomic n ℤ) g (cyclotomic n ℤ).natDegree g.natDegree with hR
  have hdeg : (cyclotomic n ℤ).natDegree = (cyclotomic n ℂ).natDegree := by
    rw [natDegree_cyclotomic, natDegree_cyclotomic]
  -- map the resultant to ℂ and identify it with the product of evaluations
  have hmapC : ((R : ℤ) : ℂ)
      = resultant (cyclotomic n ℂ) (g.map (Int.castRingHom ℂ))
          (cyclotomic n ℤ).natDegree g.natDegree := by
    rw [hR, ← map_cyclotomic_int n ℂ]
    exact (resultant_map_map (f := cyclotomic n ℤ) (g := g) (m := (cyclotomic n ℤ).natDegree)
      (n := g.natDegree) (Int.castRingHom ℂ)).symm
  have hprodC : ((R : ℤ) : ℂ)
      = ((cyclotomic n ℂ).roots.map (g.map (Int.castRingHom ℂ)).eval).prod := by
    rw [hmapC, hdeg,
      resultant_eq_prod_eval (cyclotomic n ℂ) _ g.natDegree (natDegree_map_le)
        (IsAlgClosed.splits _),
      (cyclotomic.monic n ℂ).leadingCoeff, one_pow, one_mul]
  -- take norms: |R| = ‖(R:ℂ)‖ ≤ B^φ(n)
  have hnormR : (R.natAbs : ℝ) ≤ (B : ℝ) ^ n.totient := by
    have h1 : ‖((R : ℤ) : ℂ)‖ ≤ (B : ℝ) ^ n.totient := by
      rw [hprodC]
      have hb := nnnorm_prod_eval_cyclotomic_roots_le_of_bound n B
        (g.map (Int.castRingHom ℂ)) hg
      calc ‖((cyclotomic n ℂ).roots.map (g.map (Int.castRingHom ℂ)).eval).prod‖
          = ((‖((cyclotomic n ℂ).roots.map (g.map (Int.castRingHom ℂ)).eval).prod‖₊ :
              ℝ≥0) : ℝ) := rfl
        _ ≤ (((B : ℝ≥0) ^ n.totient : ℝ≥0) : ℝ) := by exact_mod_cast hb
        _ = (B : ℝ) ^ n.totient := by push_cast; ring
    rw [Complex.norm_intCast, ← Int.cast_abs, Int.abs_eq_natAbs] at h1
    exact_mod_cast h1
  have : (R.natAbs : ℝ) ≤ ((B ^ n.totient : ℕ) : ℝ) := by push_cast; exact hnormR
  exact_mod_cast this

/-- **The integer cyclotomic-resultant magnitude bound.** If `g : ℤ[X]` evaluates with norm `≤ 4`
at every `n`-th root of unity in `ℂ`, then the integer resultant `Res(Φ_n, g)` satisfies
`|Res| ≤ 4^{φ(n)} = 2^n` (for `n = 2^m`).  The archimedean half of the small-subgroup Sidon
keystone, now over `ℤ`. -/
theorem natAbs_resultant_cyclotomic_le (n : ℕ) (g : ℤ[X])
    (hg : ∀ ω : ℂ, ω ^ n = 1 → ‖(g.map (Int.castRingHom ℂ)).eval ω‖₊ ≤ 4) :
    (resultant (cyclotomic n ℤ) g (cyclotomic n ℤ).natDegree g.natDegree).natAbs
      ≤ 4 ^ n.totient :=
  natAbs_resultant_cyclotomic_le_of_bound n 4 g hg

#print axioms natAbs_resultant_cyclotomic_le_of_bound
#print axioms natAbs_resultant_cyclotomic_le

/-- **The `p ∣ Res` lift.** If `g : ℤ[X]` (with leading coefficient surviving mod `p`) has a
primitive `n`-th root `ζ` of `ZMod p` as a root mod `p`, then `p ∣ Res(Φ_n, g)`: mod `p` the
polynomials `Φ_n` and `g` share the root `ζ`, so are not coprime, so the resultant vanishes. -/
theorem dvd_resultant_of_isPrimitiveRoot_isRoot {n : ℕ} (hn : 0 < n) {p : ℕ} [Fact p.Prime]
    (g : ℤ[X]) (hgdeg : (g.map (Int.castRingHom (ZMod p))).natDegree = g.natDegree)
    {ζ : ZMod p} (hζ : IsPrimitiveRoot ζ n)
    (hgζ : (g.map (Int.castRingHom (ZMod p))).eval ζ = 0) :
    (p : ℤ) ∣ resultant (cyclotomic n ℤ) g (cyclotomic n ℤ).natDegree g.natDegree := by
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI : NeZero p := ⟨(Fact.out (p := p.Prime)).ne_zero⟩
  haveI : NeZero ((n : ℕ) : ZMod p) := hζ.neZero'
  set R : ℤ := resultant (cyclotomic n ℤ) g (cyclotomic n ℤ).natDegree g.natDegree with hR
  have hcycζ : (cyclotomic n (ZMod p)).eval ζ = 0 := isRoot_cyclotomic_iff.mpr hζ
  have hncop : ¬ IsCoprime (cyclotomic n (ZMod p)) (g.map (Int.castRingHom (ZMod p))) := by
    rintro ⟨a, b, hab⟩
    have h := congrArg (eval ζ) hab
    rw [eval_add, eval_mul, eval_mul, hcycζ, hgζ, mul_zero, mul_zero, add_zero, eval_one] at h
    exact one_ne_zero h.symm
  have hdeg : (cyclotomic n ℤ).natDegree = (cyclotomic n (ZMod p)).natDegree := by
    rw [natDegree_cyclotomic, natDegree_cyclotomic]
  have hRzero : ((R : ℤ) : ZMod p) = 0 := by
    have hmap : ((R : ℤ) : ZMod p)
        = resultant (cyclotomic n (ZMod p)) (g.map (Int.castRingHom (ZMod p)))
            (cyclotomic n ℤ).natDegree g.natDegree := by
      rw [hR, ← map_cyclotomic_int n (ZMod p)]
      exact (resultant_map_map (f := cyclotomic n ℤ) (g := g)
        (m := (cyclotomic n ℤ).natDegree) (n := g.natDegree) (Int.castRingHom (ZMod p))).symm
    rw [hmap, hdeg, ← hgdeg]
    exact resultant_eq_zero_iff.mpr ⟨Or.inl (cyclotomic_ne_zero n (ZMod p)), hncop⟩
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd R p).mp hRzero

/-- **The small-subgroup Sidon keystone, assembled.** A parallelogram mod `p` (a primitive `n`-th
root `ζ` of `ZMod p` with `g(ζ) = 0`) forces `p ≤ 4^{φ(n)} = 2^n` — given the magnitude bound on
`g` (`hgC`, automatic for a 4-term `±1` polynomial) and `Res ≠ 0` (`hResne`, the ℂ-Sidon property
of `μ_n`).  Contrapositive: `p > 2^n ⟹` no nontrivial additive parallelogram in `μ_n ⊆ F_p`. -/
theorem prime_le_of_cyclotomic_resultant {n : ℕ} (hn : 0 < n) {p : ℕ} [Fact p.Prime] (g : ℤ[X])
    (hgC : ∀ ω : ℂ, ω ^ n = 1 → ‖(g.map (Int.castRingHom ℂ)).eval ω‖₊ ≤ 4)
    (hgdeg : (g.map (Int.castRingHom (ZMod p))).natDegree = g.natDegree)
    (hResne : resultant (cyclotomic n ℤ) g (cyclotomic n ℤ).natDegree g.natDegree ≠ 0)
    {ζ : ZMod p} (hζ : IsPrimitiveRoot ζ n)
    (hgζ : (g.map (Int.castRingHom (ZMod p))).eval ζ = 0) :
    p ≤ 4 ^ n.totient := by
  have hdvd := dvd_resultant_of_isPrimitiveRoot_isRoot hn g hgdeg hζ hgζ
  have hbound := natAbs_resultant_cyclotomic_le n g hgC
  set R : ℤ := resultant (cyclotomic n ℤ) g (cyclotomic n ℤ).natDegree g.natDegree with hRdef
  have hpd : p ∣ R.natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr hdvd
  have hpos : 0 < R.natAbs := Int.natAbs_pos.mpr hResne
  exact le_trans (Nat.le_of_dvd hpos hpd) hbound

/-- **`Res ≠ 0` from the ℂ-Sidon property.** If `g` (mapped to `ℂ`) has no root among the
primitive `n`-th roots of unity, then `Res(Φ_n, g) ≠ 0` (the integer resultant is the product of
`g` over those roots, none of which vanish). -/
theorem resultant_cyclotomic_ne_zero_of_forall_root_ne (n : ℕ) (g : ℤ[X])
    (h : ∀ ω : ℂ, ω ∈ (cyclotomic n ℂ).roots → (g.map (Int.castRingHom ℂ)).eval ω ≠ 0) :
    resultant (cyclotomic n ℤ) g (cyclotomic n ℤ).natDegree g.natDegree ≠ 0 := by
  intro hR0
  have hdeg : (cyclotomic n ℤ).natDegree = (cyclotomic n ℂ).natDegree := by
    rw [natDegree_cyclotomic, natDegree_cyclotomic]
  have hmapC : ((resultant (cyclotomic n ℤ) g (cyclotomic n ℤ).natDegree g.natDegree : ℤ) : ℂ)
      = ((cyclotomic n ℂ).roots.map (g.map (Int.castRingHom ℂ)).eval).prod := by
    have h1 : ((resultant (cyclotomic n ℤ) g (cyclotomic n ℤ).natDegree g.natDegree : ℤ) : ℂ)
        = resultant (cyclotomic n ℂ) (g.map (Int.castRingHom ℂ))
            (cyclotomic n ℤ).natDegree g.natDegree := by
      rw [← map_cyclotomic_int n ℂ]
      exact (resultant_map_map (f := cyclotomic n ℤ) (g := g)
        (m := (cyclotomic n ℤ).natDegree) (n := g.natDegree) (Int.castRingHom ℂ)).symm
    rw [h1, hdeg, resultant_eq_prod_eval (cyclotomic n ℂ) _ g.natDegree natDegree_map_le
      (IsAlgClosed.splits _), (cyclotomic.monic n ℂ).leadingCoeff, one_pow, one_mul]
  rw [hR0, Int.cast_zero] at hmapC
  have hmem : (0 : ℂ) ∈ (cyclotomic n ℂ).roots.map (g.map (Int.castRingHom ℂ)).eval :=
    Multiset.prod_eq_zero_iff.mp hmapC.symm
  rw [Multiset.mem_map] at hmem
  obtain ⟨ω, hω, hgω⟩ := hmem
  exact h ω hω hgω

/-- **The fully-reduced small-subgroup Sidon keystone.** A parallelogram mod `p` (primitive `ζ`
with `g(ζ) = 0`) forces `p ≤ 4^{φ(n)} = 2^n`, given only the magnitude bound (`hgC`, automatic for
a 4-term `±1` polynomial), the degree condition (`hgdeg`, automatic for unit leading coefficient),
and the **ℂ-Sidon property** (`hSidon`: `g` has no primitive `n`-th root of unity as a root over
`ℂ` — the conjugation argument).  Contrapositive: `p > 2^n ⟹ μ_n ⊆ F_p` has no nontrivial additive
parallelogram, discharging the `hnc`/`SidonModNeg` hypothesis of `rootsOfUnity_additiveEnergy_eq`
in the small-subgroup regime.  Everything but `hSidon` is now mechanical. -/
theorem prime_le_of_cyclotomic_parallelogram {n : ℕ} (hn : 0 < n) {p : ℕ} [Fact p.Prime]
    (g : ℤ[X]) (hgC : ∀ ω : ℂ, ω ^ n = 1 → ‖(g.map (Int.castRingHom ℂ)).eval ω‖₊ ≤ 4)
    (hgdeg : (g.map (Int.castRingHom (ZMod p))).natDegree = g.natDegree)
    (hSidon : ∀ ω : ℂ, ω ∈ (cyclotomic n ℂ).roots → (g.map (Int.castRingHom ℂ)).eval ω ≠ 0)
    {ζ : ZMod p} (hζ : IsPrimitiveRoot ζ n)
    (hgζ : (g.map (Int.castRingHom (ZMod p))).eval ζ = 0) :
    p ≤ 4 ^ n.totient :=
  prime_le_of_cyclotomic_resultant hn g hgC hgdeg
    (resultant_cyclotomic_ne_zero_of_forall_root_ne n g hSidon) hζ hgζ

/-- **The unit-circle Sidon step (conjugation argument).** If `x, y, z, w` lie on the unit circle
and `x + y = z + w ≠ 0`, then `x = z` or `x = w`.  Conjugation sends `t ↦ t⁻¹`, so the equal sums
also have equal "inverse sums", forcing equal products `xy = zw`; with equal sums this makes
`(x−z)(x−w) = 0`. -/
theorem unitCircle_parallelogram {x y z w : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1)
    (hw : ‖w‖ = 1) (hsum : x + y = z + w) (hne : x + y ≠ 0) : x = z ∨ x = w := by
  have hx0 : x ≠ 0 := by intro h; rw [h] at hx; simp at hx
  have hy0 : y ≠ 0 := by intro h; rw [h] at hy; simp at hy
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hw0 : w ≠ 0 := by intro h; rw [h] at hw; simp at hw
  have hconjinv : ∀ {t : ℂ}, ‖t‖ = 1 → (starRingEnd ℂ) t = t⁻¹ := by
    intro t ht
    have h1 : t * (starRingEnd ℂ) t = 1 := by
      rw [Complex.mul_conj]; norm_cast; rw [Complex.normSq_eq_norm_sq, ht]; norm_num
    exact (inv_eq_of_mul_eq_one_right h1).symm
  -- conjugate the sum equation
  have hconjsum : x⁻¹ + y⁻¹ = z⁻¹ + w⁻¹ := by
    have := congrArg (starRingEnd ℂ) hsum
    rw [map_add, map_add, hconjinv hx, hconjinv hy, hconjinv hz, hconjinv hw] at this
    exact this
  -- equal sums + equal inverse-sums ⟹ equal products
  have hprod : x * y = z * w := by
    have e1 : x⁻¹ + y⁻¹ = (x + y) / (x * y) := by field_simp; ring
    have e2 : z⁻¹ + w⁻¹ = (z + w) / (z * w) := by field_simp; ring
    have hzw : z + w ≠ 0 := hsum ▸ hne
    rw [e1, e2, hsum] at hconjsum
    field_simp [hzw] at hconjsum
    linear_combination -hconjsum
  -- (x - z)(x - w) = x² − (z+w)x + zw = x² − (x+y)x + xy = 0
  have hquad : (x - z) * (x - w) = 0 := by
    have : (x - z) * (x - w) = x ^ 2 - (z + w) * x + z * w := by ring
    rw [this, ← hsum, ← hprod]; ring
  rcases mul_eq_zero.mp hquad with h | h
  · left; exact sub_eq_zero.mp h
  · right; exact sub_eq_zero.mp h

/-- **No nontrivial parallelogram among roots of unity (the ℂ-Sidon).** For a primitive `n`-th
root `ω` and exponents `a,b,c,d < n` with `{a,b} ≠ {c,d}` and `ω^a + ω^b ≠ 0`, the parallelogram
sum does not vanish.  (Two applications of the unit-circle conjugation step pin `{ω^a,ω^b} =
{ω^c,ω^d}`, hence `{a,b}={c,d}` by `injOn_pow` — contradiction.) -/
theorem fourTerm_sidon {n : ℕ} (hn : 0 < n) {ω : ℂ} (hω : IsPrimitiveRoot ω n) {a b c d : ℕ}
    (ha : a < n) (hb : b < n) (hc : c < n) (hd : d < n)
    (hsum : ω ^ a + ω ^ b ≠ 0)
    (hdist : ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c))) :
    ω ^ a + ω ^ b - ω ^ c - ω ^ d ≠ 0 := by
  intro h
  have hωnorm : ‖ω‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hω.pow_eq_one hn.ne'
  have hnorm : ∀ k : ℕ, ‖ω ^ k‖ = 1 := fun k => by rw [norm_pow, hωnorm, one_pow]
  have heq : ω ^ a + ω ^ b = ω ^ c + ω ^ d := by linear_combination h
  have hinj : ∀ {i j : ℕ}, i < n → j < n → ω ^ i = ω ^ j → i = j :=
    fun hi hj hij => hω.injOn_pow (Finset.mem_coe.mpr (Finset.mem_range.mpr hi))
      (Finset.mem_coe.mpr (Finset.mem_range.mpr hj)) hij
  have h1 : ω ^ a = ω ^ c ∨ ω ^ a = ω ^ d :=
    unitCircle_parallelogram (hnorm a) (hnorm b) (hnorm c) (hnorm d) heq hsum
  have h2 : ω ^ b = ω ^ c ∨ ω ^ b = ω ^ d :=
    unitCircle_parallelogram (hnorm b) (hnorm a) (hnorm c) (hnorm d)
      (by rw [add_comm]; exact heq) (by rwa [add_comm])
  apply hdist
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · -- a=c, b=c ⟹ heq forces c=d, so (a=c ∧ b=d)
    have hac := hinj ha hc h1
    have hbc := hinj hb hc h2
    rw [hac, hbc] at heq
    have hcd : c = d := hinj hc hd (by linear_combination heq)
    exact Or.inl ⟨hac, by omega⟩
  · exact Or.inl ⟨hinj ha hc h1, hinj hb hd h2⟩
  · exact Or.inr ⟨hinj ha hd h1, hinj hb hc h2⟩
  · -- a=d, b=d ⟹ heq forces d=c, so (a=c ∧ b=d)
    have had := hinj ha hd h1
    have hbd := hinj hb hd h2
    rw [had, hbd] at heq
    have hdc : d = c := hinj hd hc (by linear_combination heq)
    exact Or.inl ⟨by omega, hbd⟩

/-- For a primitive `n`-th root `ξ` in a field of characteristic `≠ 2`, `ξ^a + ξ^b = 0` is
equivalent to the *exponent condition* `2a ≡ 2b [MOD n] ∧ a ≢ b [MOD n]` — which is independent of
which field/root.  Hence the "nonzero sum" condition transfers between `F_p` and `ℂ`. -/
theorem primitiveRoot_pow_add_eq_zero_iff {F : Type*} [Field F] (hchar : (2 : F) ≠ 0) {n : ℕ}
    (hn : 0 < n) {ξ : F} (hξ : IsPrimitiveRoot ξ n) {a b : ℕ} :
    ξ ^ a + ξ ^ b = 0 ↔ (2 * a ≡ 2 * b [MOD n] ∧ ¬ a ≡ b [MOD n]) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hξ0 : ξ ≠ 0 := hξ.ne_zero hn.ne'
  have hpow_iff : ∀ i j : ℕ, ξ ^ i = ξ ^ j ↔ i ≡ j [MOD n] := by
    intro i j
    have hred : ∀ k : ℕ, ξ ^ k = ξ ^ (k % n) := by
      intro k
      conv_lhs => rw [← Nat.div_add_mod k n, pow_add, pow_mul, hξ.pow_eq_one, one_pow, one_mul]
    rw [hred i, hred j, Nat.ModEq]
    constructor
    · exact fun h => hξ.injOn_pow (Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.mod_lt i hn)))
        (Finset.mem_coe.mpr (Finset.mem_range.mpr (Nat.mod_lt j hn))) h
    · exact fun h => by rw [h]
  constructor
  · intro h
    have hne : ξ ^ a ≠ ξ ^ b := by
      intro he
      rw [he] at h
      have : (2 : F) * ξ ^ b = 0 := by linear_combination h
      rcases mul_eq_zero.mp this with h2 | h2
      · exact hchar h2
      · exact pow_ne_zero b hξ0 h2
    have hsq : ξ ^ (2 * a) = ξ ^ (2 * b) := by
      have : ξ ^ a = -ξ ^ b := by linear_combination h
      rw [two_mul, two_mul, pow_add, pow_add, this]; ring
    exact ⟨(hpow_iff _ _).mp hsq, fun hc => hne ((hpow_iff _ _).mpr hc)⟩
  · rintro ⟨hsq, hne⟩
    have hsqeq : (ξ ^ a) ^ 2 = (ξ ^ b) ^ 2 := by
      rw [← pow_mul, ← pow_mul, mul_comm a 2, mul_comm b 2]
      exact (hpow_iff _ _).mpr hsq
    have hne' : ξ ^ a ≠ ξ ^ b := fun hc => hne ((hpow_iff _ _).mp hc)
    have : (ξ ^ a - ξ ^ b) * (ξ ^ a + ξ ^ b) = 0 := by linear_combination hsqeq
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) hne'
    · exact h
