/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Agent
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# The cyclotomic norm-defect threshold (Proximity Prize #407)

This file formalizes, **axiom-clean**, the *norm-bound threshold* that pins the rigorous "clean
range" of the additive energy `E_r(μ_n)` in the prize-regime character-sum problem
([ABF26] eprint 2026/680; <https://proximityprize.org/>).

## The mathematical content

Let `p` be a prime with `p ≡ 1 mod n` and let `𝔭` be a prime of `ℤ[ζ_n]` above `p`. A *spurious*
balanced `2r`-tuple of the order-`n` subgroup `μ_n ⊆ 𝔽_p^*` is a nonzero element
`α ∈ ℤ[ζ_n]` that is a *signed sum of at most `2r` roots of unity* (the obstruction shape of a
deep additive-energy coincidence) and that reduces to `0` modulo `𝔭` (equivalently, modulo `p`
after evaluating at a primitive root `ζ ∈ ZMod p`). The threshold states:

> If such an `α` exists and `α ≠ 0` (in characteristic `0`), then `p ≤ |Norm(α)| ≤ (2r)^{φ(n)}`.

Contrapositively, **`(2r)^{φ(n)} < p ⟹` no spurious tuple exists**, so the additive energy is
*exactly* its characteristic-0 (antipodal/Gaussian) value `E_r = E_r^{(0)}` — the proven clean
range `r < log_n p / log_n 2` (`2r < p^{1/φ(n)}`).

### Why this is the right object

Realize `α` concretely as `g(ζ_n)` for an integer "signed monomial" polynomial
`g ∈ ℤ[X]` with at most `2r` terms each of coefficient `±1`. The `φ(n)` algebraic conjugates of
`α` are exactly the values `g(ω)` over the primitive `n`-th roots of unity `ω ∈ ℂ`, and the
algebraic norm is their product, which equals the integer cyclotomic resultant
`Res(Φ_n, g) = ∏_{Φ_n(ω)=0} g(ω)` (because `Φ_n` is monic). Three elementary facts then close it:

* **Archimedean bound.** `|g(ω)| ≤ 2r` for every root of unity `ω` (triangle inequality on at most
  `2r` unit-modulus terms), so `|Res| = ∏ |g(ω)| ≤ (2r)^{φ(n)}`
  (`natAbs_resultant_cyclotomic_le_bound`).
* **`p`-divisibility.** A primitive root `ζ ∈ ZMod p` with `g(ζ) = 0` makes `Φ_n` and `g` share a
  root mod `p`, so `p ∣ Res` (`dvd_resultant_of_isPrimitiveRoot_isRoot_bound`).
* **Nonvanishing.** `α ≠ 0` in char `0` (no primitive `n`-th root of unity is a root of `g` over
  `ℂ`) gives `Res ≠ 0` (`resultant_ne_zero_of_forall_root_ne`).

Combining: `p ∣ |Res|`, `0 < |Res|`, `|Res| ≤ (2r)^{φ(n)}` ⟹ `p ≤ (2r)^{φ(n)}`
(`prime_le_of_cyclotomic_signed_sum`). The clean-range contrapositive is
`no_spurious_tuple_of_lt_prime`.

### Honesty contract (does NOT prove DGPH / the prize)

This is the *easy, true* half — the rigorous **clean range** `2r < p^{1/φ(n)}`. In the prize regime
`n = p^{1/β}` with `β ∈ [4,5]` we have `φ(n) = n/2` so `p^{1/φ(n)} → 1`: the threshold is
**VACUOUS** there (it only certifies char-0 exactness for `r = O(1)`, far below the moment-optimal
`r ≍ log p`). The genuinely **open** wall — controlling the representation mass once the prime
sublattice meets the `2r`-box (`(2r)^{φ(n)} ≥ p`, the Bourgain–Shkredov equidistribution problem) —
is NOT addressed here and is not claimed. See
`docs/kb/deltastar-cyclotomic-lattice-collision-core-2026-06-13.md`.

This refines `…/CleanRangeNorm.lean`, which discharges only the *logical skeleton* with the norm
value `N` and the bound `|N| ≤ (2r)^φ` taken as abstract hypotheses. Here the bound is **proven**
from the geometry of `α` as a signed sum of roots of unity, via the actual `Polynomial.resultant`
and complex-embedding machinery.

Axiom target: `[propext, Classical.choice, Quot.sound]`.
-/

open Polynomial Complex
open scoped NNReal

namespace ArkLib.ProximityGap.CyclotomicNormDefectThreshold

/-! ## §1  The archimedean magnitude bound (general `2r` ceiling) -/

/-- Submultiplicativity of `nnnorm` over a multiset product in a normed ring. -/
theorem nnnorm_multiset_prod_le_ring {α : Type*} [NormedCommRing α] [NormOneClass α]
    (m : Multiset α) : ‖m.prod‖₊ ≤ (m.map (‖·‖₊)).prod := by
  induction m using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons]
    exact le_trans (nnnorm_mul_le _ _) (mul_le_mul_of_nonneg_left ih (zero_le _))

/-- **The archimedean keystone (general bound).** For a polynomial `g : ℂ[X]` whose evaluations at
all `n`-th roots of unity have norm `≤ M` (e.g. a signed sum of at most `M` roots of unity), the
product of `g` over the primitive `n`-th roots — i.e. the resultant `Res(Φ_n, g)` (the cyclotomic
polynomial is monic) — has norm `≤ M^{φ(n)}`. The `M = 2r` instance is the additive-energy
defect threshold. -/
theorem nnnorm_prod_eval_cyclotomic_roots_le_bound (n : ℕ) (M : ℝ≥0) (g : ℂ[X])
    (hg : ∀ ω : ℂ, ω ^ n = 1 → ‖g.eval ω‖₊ ≤ M) :
    ‖((cyclotomic n ℂ).roots.map g.eval).prod‖₊ ≤ M ^ n.totient := by
  have hcard : (cyclotomic n ℂ).roots.card = n.totient := by
    rw [← (IsAlgClosed.splits (cyclotomic n ℂ)).natDegree_eq_card_roots, natDegree_cyclotomic]
  have hroot : ∀ ω ∈ (cyclotomic n ℂ).roots, ω ^ n = 1 := by
    intro ω hω
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [cyclotomic_zero] at hω
    · haveI : NeZero (n : ℂ) := ⟨Nat.cast_ne_zero.mpr (by omega)⟩
      exact (isRoot_cyclotomic_iff.mp (isRoot_of_mem_roots hω)).pow_eq_one
  have hb : ∀ x ∈ ((cyclotomic n ℂ).roots.map g.eval).map (‖·‖₊), x ≤ M := by
    intro x hx
    rw [Multiset.map_map, Multiset.mem_map] at hx
    obtain ⟨ω, hω, rfl⟩ := hx
    exact hg ω (hroot ω hω)
  calc ‖((cyclotomic n ℂ).roots.map g.eval).prod‖₊
      ≤ (((cyclotomic n ℂ).roots.map g.eval).map (‖·‖₊)).prod := nnnorm_multiset_prod_le_ring _
    _ ≤ M ^ (((cyclotomic n ℂ).roots.map g.eval).map (‖·‖₊)).card :=
        Multiset.prod_le_pow_card _ M hb
    _ = M ^ n.totient := by rw [Multiset.card_map, Multiset.card_map, hcard]

/-! ## §2  The triangle bound for a signed sum of `≤ 2r` roots of unity

A *signed monomial* polynomial `∑_{i} sgn i • X^{e i}` with `s ≤ 2r` terms, each `sgn i = ±1`,
evaluates at any root of unity `ω` to a sum of `s` unit-modulus complex numbers; its norm is at
most `s ≤ 2r`. This is the concrete shape of an additive-energy obstruction `x₁+…+x_r = y₁+…+y_r`
rewritten as `x₁+…+x_r − y₁−…−y_r = 0`, a signed sum of `2r` elements of `μ_n`. -/

/-- A length-`s` signed sum of `n`-th roots of unity, written as a polynomial, evaluates with norm
`≤ s` at every `n`-th root of unity. Here `e : Fin s → ℕ` are the exponents and `c : Fin s → ℂ`
the unit-modulus coefficients (`‖c i‖ = 1`, e.g. `±1`). The polynomial is `∑ i, C (c i) * X^(e i)`. -/
theorem signedSum_eval_nnnorm_le {n s : ℕ} (hn : n ≠ 0) (e : Fin s → ℕ) (c : Fin s → ℂ)
    (hc : ∀ i, ‖c i‖ = 1) {ω : ℂ} (hω : ω ^ n = 1) :
    ‖((∑ i, C (c i) * X ^ (e i) : ℂ[X]).eval ω)‖₊ ≤ (s : ℝ≥0) := by
  have hnormω : ‖ω‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hω hn
  have heval : (∑ i, C (c i) * X ^ (e i) : ℂ[X]).eval ω = ∑ i, c i * ω ^ (e i) := by
    simp [eval_finset_sum]
  have hterm : ∀ i, ‖c i * ω ^ (e i)‖ = 1 := by
    intro i
    rw [norm_mul, norm_pow, hnormω, one_pow, mul_one, hc i]
  have hreal : ‖(∑ i, C (c i) * X ^ (e i) : ℂ[X]).eval ω‖ ≤ (s : ℝ) := by
    rw [heval]
    calc ‖∑ i, c i * ω ^ (e i)‖
        ≤ ∑ _i : Fin s, (1 : ℝ) := by
          refine le_trans (norm_sum_le _ _) ?_
          exact Finset.sum_le_sum (fun i _ => le_of_eq (hterm i))
      _ = (s : ℝ) := by simp
  exact_mod_cast hreal

/-- The same triangle bound stated for the `2r`-term obstruction directly: any signed sum of at
most `2r` roots of unity evaluates with norm `≤ 2r`. Restatement of `signedSum_eval_nnnorm_le`
with `s = 2*r`. -/
theorem twoR_signedSum_eval_nnnorm_le {n r : ℕ} (hn : n ≠ 0)
    (e : Fin (2 * r) → ℕ) (c : Fin (2 * r) → ℂ) (hc : ∀ i, ‖c i‖ = 1) {ω : ℂ} (hω : ω ^ n = 1) :
    ‖((∑ i, C (c i) * X ^ (e i) : ℂ[X]).eval ω)‖₊ ≤ ((2 * r : ℕ) : ℝ≥0) :=
  signedSum_eval_nnnorm_le hn e c hc hω

/-! ## §3  The integer resultant magnitude bound `|Res(Φ_n, g)| ≤ M^{φ(n)}` -/

/-- **The integer cyclotomic-resultant magnitude bound (general `M`).** If `g : ℤ[X]` evaluates
with norm `≤ M` at every `n`-th root of unity in `ℂ`, then the integer resultant `Res(Φ_n, g)`
satisfies `|Res| ≤ M^{φ(n)}` for every natural `M`. This is `|Norm(α)| ≤ M^{φ(n)}` realized via the
complex embeddings. -/
theorem natAbs_resultant_cyclotomic_le_bound (n M : ℕ) (g : ℤ[X])
    (hg : ∀ ω : ℂ, ω ^ n = 1 → ‖(g.map (Int.castRingHom ℂ)).eval ω‖₊ ≤ (M : ℝ≥0)) :
    (resultant (cyclotomic n ℤ) g (cyclotomic n ℤ).natDegree g.natDegree).natAbs
      ≤ M ^ n.totient := by
  set R : ℤ := resultant (cyclotomic n ℤ) g (cyclotomic n ℤ).natDegree g.natDegree with hR
  have hdeg : (cyclotomic n ℤ).natDegree = (cyclotomic n ℂ).natDegree := by
    rw [natDegree_cyclotomic, natDegree_cyclotomic]
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
  have hnormR : (R.natAbs : ℝ) ≤ (M : ℝ) ^ n.totient := by
    have h1 : ‖((R : ℤ) : ℂ)‖ ≤ (M : ℝ) ^ n.totient := by
      rw [hprodC]
      have hb := nnnorm_prod_eval_cyclotomic_roots_le_bound n (M : ℝ≥0)
        (g.map (Int.castRingHom ℂ)) hg
      calc ‖((cyclotomic n ℂ).roots.map (g.map (Int.castRingHom ℂ)).eval).prod‖
          = ((‖((cyclotomic n ℂ).roots.map (g.map (Int.castRingHom ℂ)).eval).prod‖₊ : ℝ≥0) : ℝ) :=
            rfl
        _ ≤ ((((M : ℝ≥0)) ^ n.totient : ℝ≥0) : ℝ) := by exact_mod_cast hb
        _ = (M : ℝ) ^ n.totient := by push_cast; ring
    rw [Complex.norm_intCast, ← Int.cast_abs, Int.abs_eq_natAbs] at h1
    exact_mod_cast h1
  have : (R.natAbs : ℝ) ≤ ((M ^ n.totient : ℕ) : ℝ) := by push_cast; exact hnormR
  exact_mod_cast this

/-! ## §4  `p`-divisibility of the resultant when `α ≡ 0 (mod 𝔭)` -/

/-- **The `p ∣ Res` lift.** If `g : ℤ[X]` (with leading coefficient surviving mod `p`) has a
primitive `n`-th root `ζ` of `ZMod p` as a root mod `p`, then `p ∣ Res(Φ_n, g)`: mod `p` the
polynomials `Φ_n` and `g` share the root `ζ`, so are not coprime, so the resultant vanishes. This
is `p ∣ Norm(α)` from `𝔭 ∣ α`. -/
theorem dvd_resultant_of_isPrimitiveRoot_isRoot_bound {n : ℕ} (hn : 0 < n) {p : ℕ} [Fact p.Prime]
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

/-! ## §5  Nonvanishing of the resultant from `α ≠ 0` in characteristic `0` -/

/-- **`Res ≠ 0` from char-0 nonvanishing.** If `g` (mapped to `ℂ`) has no root among the primitive
`n`-th roots of unity, then `Res(Φ_n, g) ≠ 0` (the integer resultant is the product of `g` over
those roots, none of which vanish). This is `Norm(α) ≠ 0` from `α ≠ 0`. -/
theorem resultant_ne_zero_of_forall_root_ne (n : ℕ) (g : ℤ[X])
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

/-! ## §6  The assembled norm-defect threshold -/

/-- **THE NORM-DEFECT THRESHOLD (assembled, axiom-clean).** Let `g : ℤ[X]` be a representation of
the cyclotomic integer `α = g(ζ_n)` whose complex conjugates `g(ω)` all have norm `≤ M` (e.g. a
signed sum of at most `M = 2r` roots of unity, via `signedSum_eval_nnnorm_le`). Suppose

* `hSidon`: `α ≠ 0` in characteristic `0` — no primitive `n`-th root of unity is a root of `g`
  over `ℂ`; and
* `hgζ`: `α ≡ 0 (mod 𝔭)` — a primitive `n`-th root `ζ ∈ ZMod p` satisfies `g(ζ) = 0`.

Then `p ≤ M^{φ(n)} = |Norm(α)|`-bound. With `M = 2r`: `p ≤ (2r)^{φ(n)}`. -/
theorem prime_le_of_cyclotomic_signed_sum {n : ℕ} (hn : 0 < n) {p M : ℕ} [Fact p.Prime] (g : ℤ[X])
    (hgC : ∀ ω : ℂ, ω ^ n = 1 → ‖(g.map (Int.castRingHom ℂ)).eval ω‖₊ ≤ (M : ℝ≥0))
    (hgdeg : (g.map (Int.castRingHom (ZMod p))).natDegree = g.natDegree)
    (hSidon : ∀ ω : ℂ, ω ∈ (cyclotomic n ℂ).roots → (g.map (Int.castRingHom ℂ)).eval ω ≠ 0)
    {ζ : ZMod p} (hζ : IsPrimitiveRoot ζ n)
    (hgζ : (g.map (Int.castRingHom (ZMod p))).eval ζ = 0) :
    p ≤ M ^ n.totient := by
  have hdvd := dvd_resultant_of_isPrimitiveRoot_isRoot_bound hn g hgdeg hζ hgζ
  have hbound := natAbs_resultant_cyclotomic_le_bound n M g hgC
  have hResne := resultant_ne_zero_of_forall_root_ne n g hSidon
  set R : ℤ := resultant (cyclotomic n ℤ) g (cyclotomic n ℤ).natDegree g.natDegree with hRdef
  have hpd : p ∣ R.natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr hdvd
  have hpos : 0 < R.natAbs := Int.natAbs_pos.mpr hResne
  exact le_trans (Nat.le_of_dvd hpos hpd) hbound

/-- **THE NORM-DEFECT THRESHOLD, `2r` form.** Specialization of `prime_le_of_cyclotomic_signed_sum`
to `M = 2r`, matching the additive-energy obstruction `x₁+…+x_r − y₁−…−y_r = 0` (a signed sum of
`2r` roots of unity): a spurious balanced `2r`-tuple mod `p` forces `p ≤ (2r)^{φ(n)}`. -/
theorem prime_le_of_balanced_tuple {n : ℕ} (hn : 0 < n) {p r : ℕ} [Fact p.Prime] (g : ℤ[X])
    (hgC : ∀ ω : ℂ, ω ^ n = 1 → ‖(g.map (Int.castRingHom ℂ)).eval ω‖₊ ≤ ((2 * r : ℕ) : ℝ≥0))
    (hgdeg : (g.map (Int.castRingHom (ZMod p))).natDegree = g.natDegree)
    (hSidon : ∀ ω : ℂ, ω ∈ (cyclotomic n ℂ).roots → (g.map (Int.castRingHom ℂ)).eval ω ≠ 0)
    {ζ : ZMod p} (hζ : IsPrimitiveRoot ζ n)
    (hgζ : (g.map (Int.castRingHom (ZMod p))).eval ζ = 0) :
    p ≤ (2 * r) ^ n.totient :=
  prime_le_of_cyclotomic_signed_sum hn g hgC hgdeg hSidon hζ hgζ

/-- **THE CLEAN RANGE (contrapositive).** If `(2r)^{φ(n)} < p`, then there is **no** spurious
balanced `2r`-tuple of `μ_n` mod `p`: no integer "signed monomial" polynomial `g` (≤ `2r` ±1 terms,
char-0 nonvanishing on primitive roots) has a primitive `n`-th root `ζ ∈ ZMod p` as a root. Hence
the additive energy is exactly its char-0 value, `E_r = E_r^{(0)}`, throughout the clean range
`2r < p^{1/φ(n)}`. (VACUOUS in the prize regime `n = p^{1/β}`, `φ(n) = n/2`, where `p^{1/φ(n)} → 1`;
the open wall is the complementary `(2r)^{φ(n)} ≥ p` regime — not proven here.) -/
theorem no_spurious_tuple_of_lt_prime {n : ℕ} (hn : 0 < n) {p r : ℕ} [Fact p.Prime] (g : ℤ[X])
    (hgC : ∀ ω : ℂ, ω ^ n = 1 → ‖(g.map (Int.castRingHom ℂ)).eval ω‖₊ ≤ ((2 * r : ℕ) : ℝ≥0))
    (hgdeg : (g.map (Int.castRingHom (ZMod p))).natDegree = g.natDegree)
    (hSidon : ∀ ω : ℂ, ω ∈ (cyclotomic n ℂ).roots → (g.map (Int.castRingHom ℂ)).eval ω ≠ 0)
    (hlt : (2 * r) ^ n.totient < p)
    {ζ : ZMod p} (hζ : IsPrimitiveRoot ζ n) :
    (g.map (Int.castRingHom (ZMod p))).eval ζ ≠ 0 := by
  intro hgζ
  exact absurd (prime_le_of_balanced_tuple hn g hgC hgdeg hSidon hζ hgζ) (Nat.not_le.mpr hlt)

end ArkLib.ProximityGap.CyclotomicNormDefectThreshold

/-! ## Axiom audit -/
section AxiomAudit
open ArkLib.ProximityGap.CyclotomicNormDefectThreshold
#print axioms nnnorm_prod_eval_cyclotomic_roots_le_bound
#print axioms signedSum_eval_nnnorm_le
#print axioms natAbs_resultant_cyclotomic_le_bound
#print axioms dvd_resultant_of_isPrimitiveRoot_isRoot_bound
#print axioms resultant_ne_zero_of_forall_root_ne
#print axioms prime_le_of_cyclotomic_signed_sum
#print axioms prime_le_of_balanced_tuple
#print axioms no_spurious_tuple_of_lt_prime
end AxiomAudit
