/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Tactic

/-!
# Loop 52 (O16 kernel) — the resultant heart of the finite-field lifting: a common root mod `p`
# forces `p ∣ Res_ℤ`, and coprime integer polynomials have nonzero resultant.

Loop51 reduced the finite-field §7 disproof to one input: an injective reduction `ℤ[ζ] → F_p` on the
`2^{2^{m-1}}` subset sums. The obstruction to injectivity at a prime `p` is precisely a **collision**:
two subset sums `f_S(ζ_p) = f_T(ζ_p)`, i.e. the difference `g = f_S − f_T` and `ζ_p` (a primitive
`2^m`-th root, hence a root of `Φ_{2^m}`) share a root mod `p`. This loop proves the two facts that
turn "collision" into "`p` divides a fixed nonzero integer", so that only **finitely many** primes can
collide — the quantitative core of the lifting.

* `prime_dvd_resultant_of_common_root`: if `g, h ∈ ℤ[X]` keep their leading coefficients mod `p` and
  share a root `α ∈ F_p`, then `p ∣ Res_ℤ(g, h)`. Proof: a shared root makes the Bézout identity of
  any coprimality evaluate to `0 = 1`, so `g, h` are *not* coprime over `F_p`, hence
  `Res_{F_p}(ḡ, h̄) = 0` (`resultant_eq_zero_iff`); and `Res_{F_p}(ḡ, h̄) = Res_ℤ(g,h) mod p`
  (`resultant_map_map`), so `p ∣ Res_ℤ(g, h)`.
* `resultant_int_ne_zero_of_isCoprime_rat`: if `g, h` are coprime over `ℚ` (e.g. `Φ_{2^m}` irreducible
  and `deg g < deg Φ`), then `Res_ℤ(g, h) ≠ 0`.

Together: for coprime `g, h` over `ℚ`, `Res_ℤ(g,h)` is a *fixed nonzero integer*, so a common root
mod `p` happens for only finitely many `p` (those dividing it). With Dirichlet (infinitely many
`p ≡ 1 mod 2^m`) this yields a collision-free prime — the existence the Loop51 residual needs. That
final assembly (Dirichlet + primitive-root existence in `ZMod p` + the union over difference pairs) is
the remaining residual; this loop proves its load-bearing arithmetic. See `DISPROOF_LOG.md`
(O16/Loop52).
-/

open Polynomial

namespace ArkLib.ProximityGap.ResultantLiftLoop52

/-- **A common root mod `p` forces `p ∣ Res_ℤ(g, h)`.** If `g, h : ℤ[X]` keep their leading
coefficients nonzero mod the prime `p` (so reduction preserves their degrees) and share a root
`α : ZMod p`, then `p` divides the integer resultant `Res_ℤ(g, h)`. -/
theorem prime_dvd_resultant_of_common_root {p : ℕ} [Fact p.Prime]
    (g h : Polynomial ℤ)
    (hg : (g.leadingCoeff : ZMod p) ≠ 0) (hh : (h.leadingCoeff : ZMod p) ≠ 0)
    {α : ZMod p}
    (hgroot : (g.map (Int.castRingHom (ZMod p))).IsRoot α)
    (hhroot : (h.map (Int.castRingHom (ZMod p))).IsRoot α) :
    (p : ℤ) ∣ Polynomial.resultant g h := by
  set φ : ℤ →+* ZMod p := Int.castRingHom (ZMod p) with hφ
  -- reduction preserves the (formal) degrees, since the leading coefficients survive
  have hlcg : φ g.leadingCoeff ≠ 0 := hg
  have hlch : φ h.leadingCoeff ≠ 0 := hh
  have hdg : (g.map φ).natDegree = g.natDegree := natDegree_map_of_leadingCoeff_ne_zero φ hlcg
  have hdh : (h.map φ).natDegree = h.natDegree := natDegree_map_of_leadingCoeff_ne_zero φ hlch
  -- `g.map φ ≠ 0`, since its leading coefficient is nonzero
  have hgne : g.map φ ≠ 0 := by
    intro hz
    apply hlcg
    rw [leadingCoeff, ← coeff_map, hz, coeff_zero]
  -- a common root kills coprimality: the Bézout identity evaluates to `0 = 1`
  have hnc : ¬ IsCoprime (g.map φ) (h.map φ) := by
    rintro ⟨a, b, hab⟩
    have hev := congrArg (Polynomial.eval α) hab
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
      hgroot.eq_zero, hhroot.eq_zero, mul_zero, mul_zero, add_zero, Polynomial.eval_one] at hev
    exact zero_ne_one hev
  -- hence the resultant over `F_p` vanishes …
  have hres0 : Polynomial.resultant (g.map φ) (h.map φ) = 0 :=
    resultant_eq_zero_iff.mpr ⟨Or.inl hgne, hnc⟩
  -- … and it equals `Res_ℤ(g,h)` reduced mod `p`
  have hmap : Polynomial.resultant (g.map φ) (h.map φ) = φ (Polynomial.resultant g h) := by
    rw [show Polynomial.resultant (g.map φ) (h.map φ)
          = Polynomial.resultant (g.map φ) (h.map φ) g.natDegree h.natDegree by rw [hdg, hdh],
      Polynomial.resultant_map_map]
  rw [hmap] at hres0
  -- `φ x = 0 ↔ (p : ℤ) ∣ x`
  rwa [hφ, Int.coe_castRingHom, ZMod.intCast_zmod_eq_zero_iff_dvd] at hres0

/-- **Coprime integer polynomials have a nonzero resultant.** If `g, h : ℤ[X]` map to coprime
polynomials over `ℚ`, then `Res_ℤ(g, h) ≠ 0`. (`ℤ ↪ ℚ` is injective, so it preserves the resultant
and reflects nonvanishing.) The intended use: `h = Φ_{2^m}` is irreducible over `ℚ` and `g = f_S − f_T`
has degree `< deg Φ` and is nonzero, so they are coprime over `ℚ`. -/
theorem resultant_int_ne_zero_of_isCoprime_rat (g h : Polynomial ℤ)
    (H : IsCoprime (g.map (Int.castRingHom ℚ)) (h.map (Int.castRingHom ℚ))) :
    Polynomial.resultant g h ≠ 0 := by
  have hinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  intro hz
  -- map the (vanishing) integer resultant to `ℚ`; injectivity ⟹ the `ℚ`-resultant also vanishes
  have hdg : (g.map (Int.castRingHom ℚ)).natDegree = g.natDegree :=
    natDegree_map_eq_of_injective hinj g
  have hdh : (h.map (Int.castRingHom ℚ)).natDegree = h.natDegree :=
    natDegree_map_eq_of_injective hinj h
  have hmap : Polynomial.resultant (g.map (Int.castRingHom ℚ)) (h.map (Int.castRingHom ℚ))
      = (Int.castRingHom ℚ) (Polynomial.resultant g h) := by
    rw [show Polynomial.resultant (g.map (Int.castRingHom ℚ)) (h.map (Int.castRingHom ℚ))
          = Polynomial.resultant (g.map (Int.castRingHom ℚ)) (h.map (Int.castRingHom ℚ))
              g.natDegree h.natDegree by rw [hdg, hdh],
      Polynomial.resultant_map_map]
  -- but coprimality forces the `ℚ`-resultant nonzero — contradiction
  have hne : Polynomial.resultant (g.map (Int.castRingHom ℚ)) (h.map (Int.castRingHom ℚ)) ≠ 0 :=
    resultant_ne_zero _ _ H
  rw [hmap, hz] at hne
  simp at hne

/-- **A prime `p ≡ 1 (mod q)` avoiding any fixed nonzero integer `R`.** By Dirichlet there are
infinitely many primes `≡ 1 (mod q)`; choosing one larger than `|R|` guarantees `p ∤ R`. Applied with
`q = 2^m` (so `ζ` exists in `F_p`) and `R = ∏ Res_ℤ(f_S − f_T, Φ)` (the collision product), this is
the prime at which **no** subset-sum collision occurs. -/
theorem exists_prime_eq_one_mod_not_dvd {q : ℕ} (hq : 2 ≤ q) (R : ℤ) (hR : R ≠ 0) :
    ∃ p : ℕ, p.Prime ∧ (p : ZMod q) = 1 ∧ ¬ (p : ℤ) ∣ R := by
  haveI : NeZero q := ⟨by omega⟩
  obtain ⟨p, hpgt, hpp, hpmod⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (q := q) (a := 1) isUnit_one R.natAbs
  refine ⟨p, hpp, hpmod, ?_⟩
  intro hdvd
  -- `p ∣ R ⟹ p ≤ |R| = R.natAbs`, contradicting `p > R.natAbs`
  have hpos : 0 < R.natAbs := Int.natAbs_pos.mpr hR
  have hpdvd : p ∣ R.natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa using this
  have hle : p ≤ R.natAbs := Nat.le_of_dvd hpos hpdvd
  omega

private theorem totient_two_pow' {m : ℕ} (hm : 1 ≤ m) : Nat.totient (2 ^ m) = 2 ^ (m - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hm
  rw [Nat.zero_add, Nat.totient_prime_pow_succ Nat.prime_two]; simp

/-- **A low-degree nonzero integer polynomial is coprime to `Φ_{2^m}` over `ℚ`.** Since
`cyclotomic (2^m) ℚ` is irreducible of degree `φ(2^m) = 2^{m-1}` and `g ≠ 0` has degree `< 2^{m-1}`,
`Φ` cannot divide `g`, so they are coprime. This supplies the `hcop` hypothesis of
`exists_good_prime_no_common_resultant` for every difference `g = f_S − f_T` (`deg < 2^{m-1}`). -/
theorem diff_coprime_cyclotomic_rat {m : ℕ} (hm : 1 ≤ m) (g : Polynomial ℤ)
    (hdeg : g.natDegree < 2 ^ (m - 1)) (hg0 : g ≠ 0) :
    IsCoprime (g.map (Int.castRingHom ℚ))
      ((cyclotomic (2 ^ m) ℤ).map (Int.castRingHom ℚ)) := by
  rw [Polynomial.map_cyclotomic_int]
  have hirr : Irreducible (cyclotomic (2 ^ m) ℚ) := cyclotomic.irreducible_rat (by positivity)
  rw [isCoprime_comm, hirr.coprime_iff_not_dvd]
  intro hdvd
  have hinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  have hgmap0 : g.map (Int.castRingHom ℚ) ≠ 0 := by
    simpa [Polynomial.map_eq_zero_iff hinj] using hg0
  have hdeg_le : (cyclotomic (2 ^ m) ℚ).natDegree ≤ (g.map (Int.castRingHom ℚ)).natDegree :=
    Polynomial.natDegree_le_of_dvd hdvd hgmap0
  rw [natDegree_cyclotomic, totient_two_pow' hm] at hdeg_le
  rw [natDegree_map_eq_of_injective hinj g] at hdeg_le
  omega

/-- **A primitive `2^m`-th root of unity exists in `F_p` when `2^m ∣ p − 1`.** The unit group
`(ZMod p)ˣ` is cyclic of order `p − 1`; since `2^m ∣ p − 1`, `IsCyclic.card_orderOf_eq_totient` gives
`φ(2^m) = 2^{m-1} > 0` units of order exactly `2^m`, any of which is a primitive `2^m`-th root. -/
theorem exists_primitiveRoot_zmod {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    (hdvd : 2 ^ m ∣ p - 1) :
    ∃ ζ : ZMod p, IsPrimitiveRoot ζ (2 ^ m) := by
  classical
  have hd : 2 ^ m ∣ Fintype.card (ZMod p)ˣ := by rw [ZMod.card_units p]; exact hdvd
  have hcnt : (Finset.univ.filter (fun u : (ZMod p)ˣ => orderOf u = 2 ^ m)).card
      = Nat.totient (2 ^ m) := IsCyclic.card_orderOf_eq_totient hd
  have hpos : 0 < (Finset.univ.filter (fun u : (ZMod p)ˣ => orderOf u = 2 ^ m)).card := by
    rw [hcnt, totient_two_pow' hm]; positivity
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hu
  exact ⟨(u : ZMod p),
    IsPrimitiveRoot.coe_units_iff.mpr (IsPrimitiveRoot.iff_orderOf.mpr hu.2)⟩

/-- **Consolidation: a prime `≡ 1 (mod q)` at which no member of a finite family shares a root with
`h`.** Given polynomials `gs i`, each coprime to `h` over `ℚ`, the product `R = ∏ Res_ℤ(gs i, h)` is a
nonzero integer; a Dirichlet prime `p ≡ 1 (mod q)` with `p ∤ R` then satisfies `p ∤ Res_ℤ(gs i, h)`
for every `i`. Combined (via `prime_dvd_resultant_of_common_root`) this is exactly "no collision at
`p`": no `gs i` shares a root with `h` mod `p`. This is the form the §7 finite-field disproof consumes
with `h = Φ_{2^m}`, `gs = {f_S − f_T}`. -/
theorem exists_good_prime_no_common_resultant {ι : Type*} [Fintype ι]
    {q : ℕ} (hq : 2 ≤ q) (h : Polynomial ℤ) (gs : ι → Polynomial ℤ)
    (hcop : ∀ i, IsCoprime ((gs i).map (Int.castRingHom ℚ)) (h.map (Int.castRingHom ℚ))) :
    ∃ p : ℕ, p.Prime ∧ (p : ZMod q) = 1 ∧
      ∀ i, ¬ (p : ℤ) ∣ Polynomial.resultant (gs i) h := by
  classical
  set R : ℤ := ∏ i, Polynomial.resultant (gs i) h with hR
  have hRne : R ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => resultant_int_ne_zero_of_isCoprime_rat _ _ (hcop i)
  obtain ⟨p, hpp, hpmod, hpndvd⟩ := exists_prime_eq_one_mod_not_dvd hq R hRne
  refine ⟨p, hpp, hpmod, fun i hdvd => hpndvd ?_⟩
  exact hR ▸ hdvd.trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))

end ArkLib.ProximityGap.ResultantLiftLoop52

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.ResultantLiftLoop52.diff_coprime_cyclotomic_rat
#print axioms ArkLib.ProximityGap.ResultantLiftLoop52.exists_good_prime_no_common_resultant
#print axioms ArkLib.ProximityGap.ResultantLiftLoop52.prime_dvd_resultant_of_common_root
#print axioms ArkLib.ProximityGap.ResultantLiftLoop52.resultant_int_ne_zero_of_isCoprime_rat
#print axioms ArkLib.ProximityGap.ResultantLiftLoop52.exists_prime_eq_one_mod_not_dvd
