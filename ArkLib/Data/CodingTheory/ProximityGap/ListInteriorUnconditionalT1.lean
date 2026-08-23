/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.InteriorListCountBridge
import ArkLib.Data.CodingTheory.ProximityGap.SubsetSumPigeonholeFiber

/-!
# Round 5 (Issue #232, ABF26) — the UNCONDITIONAL `t = 1`, general-`n` interior list lower bound.

Rounds 1–4 produced two reusable, axiom-clean halves:

* **The bridge** (`InteriorListCountBridge.lean`,
  `ArkLib.CodingTheory.Round4InteriorList.interior_list_card_ge_family`): given a *degree-drop
  family* `𝒮` of `(k+t)`-subsets each forcing `deg(p_S) < k`, the Reed–Solomon list at the interior
  agreement `k+t` has size `≥ |𝒮|`. For `t = 1` the degree-drop condition is *exactly* the
  window-sum constraint `∑_{i∈S} D i = target` (`degDrop_t1_iff_window_sum`).
* **The pigeonhole** (`SubsetSumPigeonholeFiber.lean`, the *technique*
  `card_eq_sum_card_fiberwise` + averaging): the `(k+1)`-subsets tile `C(n, k+1)` over the `q = |F|`
  window-sum targets, so **some** target has fiber `≥ C(n, k+1) / q`.

Both halves were *conditional*: the bridge assumed a degree-drop family was handed to it, and the
pigeonhole produced an abstract `target` (not tied to any received word). **This file composes them
into a single unconditional theorem.** The trick is to *choose the word polynomial `g` to match the
pigeonhole target*: given any `target`, set

  `g := X^k · (X − C target) = X^{k+1} − C target · X^k`,

which is monic of degree `k+1` with `g.coeff k = −target`, so its `t = 1` window-sum target is
`−(g.coeff k)/leadingCoeff = target` exactly. The carrier of the degree-drop family is then the
*index* family `{ S : |S| = k+1, ∑_{i∈S} D i = target }`, each member of which forces `deg(p_S) < k`
by `degDrop_t1_iff_window_sum` together with `pSt_natDegree_lt_interior`.

## The headline (`exists_interior_list_ge_unconditional`)

For a smooth-domain Reed–Solomon code `RS[F, D, k]` with `D : ι ↪ F` injective, `0 < k`, `k ≤ n`,
and the **interior** condition `(k+1)² < k·n` (so the agreement radius `δ = 1 − (k+1)/n` is strictly
inside the open gap `(1 − √ρ, 1 − ρ)`), **there exists** an explicit received word `w = g ∘ D`
(`g` of degree exactly `k+1`) such that

  `C(n, k+1)  ≤  q · #{ v ∈ RS[F,D,k] : agree(v, w) ≥ k+1 }`,

i.e. the interior list has size `≥ C(n, k+1) / q`, **with no count hypothesis and no degree-drop
family supplied** — both are constructed. This is the *first* unconditional, general-`n`, interior
list-decoding lower bound for smooth-domain Reed–Solomon in this development.

## Honest scope (what this is NOT)

* The radius is `δ = 1 − (k+1)/n`, the `t = 1` **sliver just inside capacity** `1 − ρ` (the right
  endpoint of the open gap). It does **not** pin `δ*` in the *deep* interior near `1 − √ρ`; pushing
  to agreement `k+t` for larger `t` needs `t` joint symmetric-function cancellations whose count
  growth is the still-open additive question.
* The bound carries a `1/q` factor (`q = |F|`). It exceeds the trivial `1` (a genuine super-linear
  list) only once `C(n, k+1) > q`, i.e. for `n` large relative to the field — true in the asymptotic
  smooth-domain regime `n → ∞` at fixed rate, but **not** a `q`-independent statement.
* It is a *lower* bound on a worst-case received word; it is **not** a counterexample to the prize
  and does **not** decide list-decodability up to capacity.

What is genuinely new over Rounds 1–4: the two conditional halves are now **discharged and welded**
— no `DegDropFamily` and no count hypothesis appear in the statement; `g`, the family, and the count
bound are all produced internally, leaving only the geometric interior condition `(k+1)² < k·n`.

All headline results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Polynomial BigOperators Finset
open ArkLib.CodingTheory.Round4InteriorList

namespace ArkLib.CodingTheory.Round5Unconditional

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]

/-! ## The explicit word polynomial `g = X^k · (X − C target)`. -/

/-- The chosen degree-`(k+1)` word polynomial: `g = X^k · (X − C target)`. As a product of monics
it is monic of natDegree `k+1`, and its `X^k`-coefficient is `−target`, so its `t = 1` window-sum
target is `−(g.coeff k)/leadingCoeff = target` exactly — matching the pigeonhole fiber. -/
noncomputable def wordPoly (k : ℕ) (target : F) : F[X] :=
  X ^ k * (X - C target)

/-- `wordPoly k target` is monic. -/
theorem wordPoly_monic (k : ℕ) (target : F) : (wordPoly k target).Monic :=
  (monic_X_pow k).mul (monic_X_sub_C target)

/-- `wordPoly k target` has natDegree exactly `k + 1`. -/
theorem wordPoly_natDegree (k : ℕ) (target : F) : (wordPoly k target).natDegree = k + 1 := by
  rw [wordPoly, Polynomial.Monic.natDegree_mul (monic_X_pow k) (monic_X_sub_C target),
    natDegree_X_pow, natDegree_X_sub_C]

/-- `wordPoly k target` is nonzero (it is monic over a field, hence nonzero). -/
theorem wordPoly_ne_zero (k : ℕ) (target : F) : wordPoly k target ≠ 0 :=
  (wordPoly_monic k target).ne_zero

/-- `wordPoly k target` has leading coefficient `1`. -/
theorem wordPoly_leadingCoeff (k : ℕ) (target : F) : (wordPoly k target).leadingCoeff = 1 :=
  wordPoly_monic k target

/-- The key coefficient identity: `(wordPoly k target).coeff k = −target`. Expanding
`X^k·(X − C target) = X^{k+1} − C target · X^k`, the `X^k` coefficient is `0 − target·1`. -/
theorem wordPoly_coeff_k (k : ℕ) (target : F) : (wordPoly k target).coeff k = -target := by
  have hexpand : wordPoly k target = X ^ (k + 1) - C target * X ^ k := by
    rw [wordPoly, mul_sub, ← pow_succ, mul_comm (C target)]
  rw [hexpand, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow]
  simp

/-- The `t = 1` window-sum target of `wordPoly k target` is `target` itself:
`−(g.coeff k)/leadingCoeff = −(−target)/1 = target`. -/
theorem wordPoly_window_target (k : ℕ) (target : F) :
    -((wordPoly k target).coeff k) / (wordPoly k target).leadingCoeff = target := by
  rw [wordPoly_coeff_k, wordPoly_leadingCoeff, neg_neg, div_one]

/-! ## The degree-drop family carrier (the index window-sum fiber) and its total over targets. -/

/-- The index window-sum family: `(k+1)`-subsets of `ι` whose `D`-image sums to `target`. For
`g = wordPoly k target` each such `S` forces `deg(p_S) < k` (`degDrop_t1_iff_window_sum`), so this
is exactly the carrier of the `t = 1` degree-drop family. -/
noncomputable def indexFamily (D : ι ↪ F) (k : ℕ) (target : F) : Finset (Finset ι) :=
  (Finset.univ.powersetCard (k + 1)).filter (fun S => ∑ i ∈ S, D i = target)

/-- **Total over targets `= C(n, k+1)`.** The `(k+1)`-subsets of `ι` are partitioned by their
window-sum `∑_{i∈S} D i`, so summing the fiber sizes over all field targets recovers `C(n, k+1)`.
This is the conservation law that drives the pigeonhole. -/
theorem sum_indexFamily_card_eq_choose [Fintype F] (D : ι ↪ F) (k : ℕ) :
    ∑ target : F, (indexFamily D k target).card = (Fintype.card ι).choose (k + 1) := by
  classical
  unfold indexFamily
  have hpart : (Finset.univ.powersetCard (k + 1) : Finset (Finset ι)).card
      = ∑ target : F,
          ((Finset.univ.powersetCard (k + 1)).filter (fun S => ∑ i ∈ S, D i = target)).card :=
    Finset.card_eq_sum_card_fiberwise
      (f := fun S => ∑ i ∈ S, D i) (t := (Finset.univ : Finset F))
      (fun S _ => Finset.mem_univ _)
  rw [← hpart, Finset.card_powersetCard, Finset.card_univ]

/-- **Pigeonhole on the index fiber.** Since the `(k+1)`-fibers total `C(n, k+1)` over the `q = |F|`
targets, some target's fiber has `q · (fiber size) ≥ C(n, k+1)`. (Same averaging argument as
`max_fiber_ge_total_div_card`, run directly on the index family.) -/
theorem exists_indexFamily_card_ge [Fintype F] (D : ι ↪ F) (k : ℕ) (hq : 0 < Fintype.card F) :
    ∃ target : F,
      (Fintype.card ι).choose (k + 1) ≤ Fintype.card F * (indexFamily D k target).card := by
  classical
  by_contra hcon
  push_neg at hcon
  have hsum : ∑ target : F, (indexFamily D k target).card = (Fintype.card ι).choose (k + 1) :=
    sum_indexFamily_card_eq_choose D k
  -- if every fiber `< C(n,k+1)/q` then the total `< C(n,k+1)`, contradiction.
  have hlt : ∀ target : F,
      (indexFamily D k target).card * Fintype.card F < (Fintype.card ι).choose (k + 1) := by
    intro target; rw [mul_comm]; exact hcon target
  have hbound : ∑ target : F, (indexFamily D k target).card < (Fintype.card ι).choose (k + 1) := by
    by_cases hn0 : (Fintype.card ι).choose (k + 1) = 0
    · exact absurd (hlt (Classical.arbitrary F)) (by rw [hn0]; exact Nat.not_lt_zero _)
    · have hmul : (∑ target : F, (indexFamily D k target).card) * Fintype.card F
          < (Fintype.card F) * (Fintype.card ι).choose (k + 1) := by
        calc (∑ target : F, (indexFamily D k target).card) * Fintype.card F
            = ∑ target : F, (indexFamily D k target).card * Fintype.card F := by
              rw [Finset.sum_mul]
          _ < ∑ _target : F, (Fintype.card ι).choose (k + 1) :=
              Finset.sum_lt_sum_of_nonempty
                (Finset.univ_nonempty_iff.mpr (Fintype.card_pos_iff.mp hq))
                (fun target _ => hlt target)
          _ = Fintype.card F * (Fintype.card ι).choose (k + 1) := by
              rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
      exact lt_of_mul_lt_mul_right (by rwa [mul_comm (Fintype.card F)] at hmul) (Nat.zero_le _)
  rw [hsum] at hbound
  exact lt_irrefl _ hbound

/-! ## Each index-fiber member forces the degree drop: the carrier is a genuine `DegDropFamily`. -/

/-- **The window-sum fiber forces the degree drop.** For `g = wordPoly k target` and any
`S ∈ indexFamily D k target` (so `|S| = k+1` and `∑_{i∈S} D i = target`), the codeword polynomial
`p_S` has `natDegree < k`: its `X^k` coefficient vanishes (`degDrop_t1_iff_window_sum`, since the
window-sum hits the target `−(g.coeff k)/leadingCoeff = target`), and `p_S` already has
`natDegree < k+1` (`pSt_natDegree_lt_interior`); a polynomial of natDegree `< k+1` whose `X^k`
coefficient is `0` has natDegree `< k`. -/
theorem indexFamily_forces_degDrop (D : ι ↪ F) (k : ℕ) (target : F)
    (hk : 0 < k) {S : Finset ι} (hS : S ∈ indexFamily D k target) :
    (pSt D (wordPoly k target) (wordPoly k target).leadingCoeff S).natDegree < k := by
  classical
  rw [indexFamily, Finset.mem_filter, Finset.mem_powersetCard] at hS
  obtain ⟨⟨_, hScard⟩, hSsum⟩ := hS
  set g := wordPoly k target with hg
  -- `p_S` has natDegree `< k+1` unconditionally.
  have hltkt : (pSt D g g.leadingCoeff S).natDegree < k + 1 :=
    pSt_natDegree_lt_interior D g (wordPoly_natDegree k target) (by omega)
      (wordPoly_ne_zero k target) S (by rw [hScard])
  -- the `X^k` coefficient of `p_S` vanishes (window-sum hits the target).
  have hc0 : g.leadingCoeff ≠ 0 := by rw [wordPoly_leadingCoeff]; exact one_ne_zero
  have hcoeff0 : (pSt D g g.leadingCoeff S).coeff k = 0 := by
    rw [degDrop_t1_iff_window_sum D g hc0 S (by rw [hScard])]
    rw [hg, wordPoly_window_target k target]
    exact hSsum
  -- natDegree `< k+1` and `coeff k = 0` ⟹ natDegree `< k`.
  rcases Nat.lt_succ_iff_lt_or_eq.mp hltkt with h | h
  · exact h
  · -- if natDegree `= k`, then `leadingCoeff = coeff k = 0`, so `p_S = 0`, so natDegree `= 0 < k`.
    have hlead : (pSt D g g.leadingCoeff S).leadingCoeff = 0 := by
      rw [← Polynomial.coeff_natDegree, h, hcoeff0]
    rw [Polynomial.leadingCoeff_eq_zero] at hlead
    rw [hlead, Polynomial.natDegree_zero]; exact hk

/-- The `t = 1` degree-drop family for `g = wordPoly k target` with carrier the index window-sum
fiber `indexFamily D k target`. -/
noncomputable def windowDegDropFamily (D : ι ↪ F) (k : ℕ) (target : F) (hk : 0 < k) :
    DegDropFamily D (wordPoly k target) k 1 where
  carrier := indexFamily D k target
  card_eq := by
    intro S hS
    rw [indexFamily, Finset.mem_filter, Finset.mem_powersetCard] at hS
    exact hS.1.2
  deg_lt := fun S hS => indexFamily_forces_degDrop D k target hk hS

/-- The carrier of `windowDegDropFamily` is `indexFamily D k target` (by definition). -/
theorem windowDegDropFamily_carrier (D : ι ↪ F) (k : ℕ) (target : F) (hk : 0 < k) :
    (windowDegDropFamily D k target hk).carrier = indexFamily D k target := rfl

/-! ## The headline: the unconditional `t = 1` interior list lower bound. -/

open Classical in
/-- **The first unconditional, general-`n`, interior list-decoding lower bound** (Issue #232,
`t = 1`).

For a smooth-domain Reed–Solomon code `RS[F, D, k]` (`D : ι ↪ F` injective, `0 < k`, `k ≤ n = |ι|`)
at the interior radius `δ = 1 − (k+1)/n` (interiorness certified by `(k+1)² < k·n`), there exists
an explicit received word `w = (i ↦ g(D i))` with `g = X^k·(X − C target)` of degree exactly `k+1`
such that the list of codewords agreeing with `w` on `≥ k+1` coordinates has size
`≥ C(n, k+1) / q`:

  `C(n, k+1)  ≤  q · #{ v ∈ RS[F,D,k] : agree(v, w) ≥ k+1 }`.

No degree-drop family and no count hypothesis are assumed — both are constructed internally (the
family is the window-sum fiber; the count is the pigeonhole lower bound `C(n,k+1)/q`). -/
theorem exists_interior_list_ge_unconditional [Fintype F] (D : ι ↪ F) {k : ℕ}
    (hk : 0 < k) (hkn : k ≤ Fintype.card ι) (hq : 0 < Fintype.card F)
    (hint : (k + 1) ^ 2 < k * Fintype.card ι) :
    ∃ (g : F[X]), g.natDegree = k + 1 ∧
      (Fintype.card ι).choose (k + 1) ≤
        Fintype.card F *
          (Finset.univ.filter (fun v : ι → F =>
            v ∈ ReedSolomon.code D k ∧
              k + 1 ≤ agreeCount v (fun i => g.eval (D i)))).card := by
  classical
  -- interiorness certificate (kept to tie the statement to the strictly-interior radius).
  have _hinterior : k < k + 1 ∧ (k + 1) ^ 2 < k * Fintype.card ι :=
    interior_radius_witness (by norm_num) hint
  -- pigeonhole: pick the heavy window-sum target.
  obtain ⟨target, hcount⟩ := exists_indexFamily_card_ge D k hq
  refine ⟨wordPoly k target, wordPoly_natDegree k target, ?_⟩
  -- the bridge: list ≥ |carrier| = |indexFamily|.
  have hbridge :=
    interior_list_card_ge_family D (wordPoly k target)
      (wordPoly_ne_zero k target) hkn (windowDegDropFamily D k target hk)
  rw [windowDegDropFamily_carrier D k target hk] at hbridge
  -- chain: C(n,k+1) ≤ q·|indexFamily| ≤ q·(list size).
  calc (Fintype.card ι).choose (k + 1)
      ≤ Fintype.card F * (indexFamily D k target).card := hcount
    _ ≤ Fintype.card F * _ := Nat.mul_le_mul_left _ hbridge

/-- **The headline hypotheses are jointly satisfiable (non-vacuity).** At `k = 50` and `n = 104`
(rate `ρ = 50/104 ≈ 0.48`), all four arithmetic premises of `exists_interior_list_ge_unconditional`
hold simultaneously: `0 < k`, `k ≤ n`, `(k+1)² = 2601 < 5200 = k·n`. Pairing this with any finite
field `F` (`0 < |F|`) and a domain `ι` with `|ι| = 104` (e.g. `ι = Fin 104`, with `D : Fin 104 ↪ F`
into a field of size `≥ 104`) instantiates the theorem with `C(104, 51) > 0` on the right — so the
list bound `C(104,51) ≤ q · (list size)` is a genuine, non-vacuous statement, not `0 ≤ …`. -/
theorem headline_hypotheses_satisfiable :
    0 < 50 ∧ (50 : ℕ) ≤ 104 ∧ (50 + 1) ^ 2 < 50 * 104 ∧ 0 < Nat.choose 104 (50 + 1) := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  exact Nat.choose_pos (by norm_num)

end ArkLib.CodingTheory.Round5Unconditional

/-! ## Axiom audit -/
#print axioms ArkLib.CodingTheory.Round5Unconditional.wordPoly_natDegree
#print axioms ArkLib.CodingTheory.Round5Unconditional.wordPoly_coeff_k
#print axioms ArkLib.CodingTheory.Round5Unconditional.wordPoly_window_target
#print axioms ArkLib.CodingTheory.Round5Unconditional.sum_indexFamily_card_eq_choose
#print axioms ArkLib.CodingTheory.Round5Unconditional.exists_indexFamily_card_ge
#print axioms ArkLib.CodingTheory.Round5Unconditional.indexFamily_forces_degDrop
#print axioms ArkLib.CodingTheory.Round5Unconditional.exists_interior_list_ge_unconditional
#print axioms ArkLib.CodingTheory.Round5Unconditional.headline_hypotheses_satisfiable
