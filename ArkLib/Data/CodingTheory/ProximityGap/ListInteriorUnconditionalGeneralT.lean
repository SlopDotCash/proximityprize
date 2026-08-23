/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ListInteriorUnconditionalT2
import Mathlib.Data.Fintype.BigOperators

/-!
# Round 7 (Issue #232, ABF26) — the UNCONDITIONAL, GENERAL-`t`, general-`n` interior list lower
# bound: the `t`-fold pigeonhole pattern, reaching agreement `k + t` for *any* `t` with `(k+t)² < kn`.

Rounds 5–6 produced the unconditional interior list lower bounds at the first two agreement steps
past capacity:

* **`t = 1`** (`ListInteriorUnconditionalT1.lean`, `exists_interior_list_ge_unconditional`):
  `C(n,k+1) ≤ q · #{list}` at `δ = 1 − (k+1)/n` (the sliver just inside capacity `1 − ρ`), via a
  *single* pigeonhole over the window-sum target `∑_{i∈S} D i = target ∈ F`.
* **`t = 2`** (`ListInteriorUnconditionalT2.lean`, `exists_interior_list_ge_unconditional_t2`):
  `C(n,k+2) ≤ q² · #{list}` at `δ = 1 − (k+2)/n`, via a *double* pigeonhole over the pair of targets
  `(c₁, c₂) ∈ F × F` (`e_1` and `e_2`).

Both went through the *symmetric-function* coordinates of `∏_{i∈S}(X − D i)`. This file pushes the
weld to **general `t`** with a cleaner, coordinate-free engine: the **top-`t`-coefficient vector** of
the root product.

## What this file does — the `t`-fold pigeonhole over `Fin t → F`

The degree drop `deg(p_S) < k` (for `p_S = g − c·∏_{i∈S}(X − D i)`, `S` of card `k+t`) is exactly the
vanishing of the `t` top coefficients `p_S.coeff k, …, p_S.coeff (k+t−1)`. Writing
`c = g.leadingCoeff` and `P_S = ∏_{i∈S}(X − D i)`, `p_S.coeff (k+j) = g.coeff (k+j) − c·P_S.coeff (k+j)`,
so the drop is `g.coeff (k+j) = c·P_S.coeff (k+j)` for all `j < t`. The **top-`t`-coefficient vector**

  `coeffVec D k t S : Fin t → F,  j ↦ (∏_{i∈S}(X − D i)).coeff (k + j)`

is the natural pigeonhole statistic: the `(k+t)`-subsets are partitioned by `coeffVec ∈ (Fin t → F)`,
a set of size `q^t`. We:

* `sum_tFamily_card_eq_choose` — partition the `(k+t)`-subsets by `coeffVec`: the fibers total
  `C(n, k+t)` over all `q^t` target vectors.
* `exists_tFamily_card_ge` — therefore **some** target vector `cs` has `q^t · (fiber size) ≥ C(n,k+t)`
  (the `t`-fold pigeonhole; the `q^t = |Fin t → F|` denominator).
* `wordPolyT k t cs := X^k · (X^t + ∑_{j<t} C (cs j)·X^j)` — the explicit **monic** degree-`(k+t)` word
  polynomial whose top-`t` coefficients are exactly `cs`: `coeff (k+j) = cs j` for `j < t`. For
  `S` in the `cs`-fiber and `g = wordPolyT k t cs` (leading coeff `1`), every top coefficient of
  `p_S` cancels: `p_S.coeff (k+j) = cs j − 1·cs j = 0`, so `deg(p_S) < k`.

Welding (the `cs`-fiber forces `deg(p_S) < k`, the Round-4 bridge `interior_list_card_ge_family` turns
the family into a list lower bound) gives the headline.

## The headline (`exists_interior_list_ge_unconditional_t`)

For a smooth-domain Reed–Solomon code `RS[F, D, k]` (`D : ι ↪ F` injective, `0 < k`, `k ≤ n = |ι|`)
and **any** `t ≥ 1` at the **interior** radius `δ = 1 − (k+t)/n` (interiorness `(k+t)² < k·n`), there
exists an explicit received word `w = g ∘ D` (`g` of degree exactly `k+t`) such that

  `C(n, k+t)  ≤  q^t · #{ v ∈ RS[F,D,k] : agree(v, w) ≥ k+t }`,

i.e. the interior list has size `≥ C(n,k+t)/q^t`, **with no count hypothesis and no degree-drop family
supplied** — all of `g`, the fiber family, and the count bound are constructed internally. This is the
`t = 1` / `t = 2` welds (`exists_interior_list_ge_unconditional`,
`exists_interior_list_ge_unconditional_t2`) generalized to *every* `t` in one stroke; specializing to
`t = 1` and `t = 2` recovers (up to the `q` vs `q^t` denominator) those results.

## Honest scope — what this is and is NOT

* The **interior radius is real and reaches deep**: `δ = 1 − (k+t)/n` is strictly inside the gap
  `(1 − √ρ, 1 − ρ)` precisely when `0 < t` and `(k+t)² < k·n`, which allows `t` up to `≈ √(kn) − k`,
  i.e. **well past the `O(1)` steps** of `t = 1, 2`. At rate `ρ = 1/2` (`n = 2k`), `(k+t)² < 2k²`
  permits `t` up to `≈ (√2 − 1)·k ≈ 0.414·k`, a *constant fraction* of `k` into the interior — the
  first unconditional brick to reach the deep interior at all.
* The **denominator is `q^t`** (`q = |F|`), the `t`-fold worst-case pigeonhole loss. The bound exceeds
  the trivial `1` only once `C(n, k+t) > q^t`. This is **strongly `q`-dependent** — strictly worse on
  the `q`-axis than `t = 1`'s `/q` and `t = 2`'s `/q²`. It is NOT a `q`-independent statement, and the
  threshold `C(n,k+t) > q^t` is demanding: it needs `n` super-polynomially large relative to `q^t`.
* It is a **lower** bound on a worst-case received word; it is NOT a counterexample to the prize and
  does NOT pin `δ*`. The prize-deciding question — whether the count *concentrates* on `O(1)` target
  vectors (so the `/q^t` collapses to `/O(1)`, the `q`-independent regime) — is untouched: this is the
  generic worst-case averaging, which provably loses `q^t` (`ListInteriorQDependenceNoGo` shows the
  averaging method cannot do better). The open door is a *concentrating construction*, not this bound.

What is genuinely new over Round 6: the `t = 2` weld is generalized to **arbitrary `t`** through the
coordinate-free top-coefficient-vector pigeonhole, removing the per-`t` symmetric-function bookkeeping
(`degDrop_t1_iff_window_sum`, `degDrop_t2_iff_two_symmetric`) entirely. The degree drop is forced
*directly* by matching the word polynomial's top-`t` coefficients to the chosen fiber — no Vieta /
Newton identities needed.

All headline results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Polynomial BigOperators Finset
open ArkLib.CodingTheory.Round4InteriorList

namespace ArkLib.CodingTheory.Round7GeneralT

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F]

/-! ## The explicit word polynomial `g = X^k · (X^t + ∑_{j<t} C (cs j)·X^j)` for general `t`. -/

/-- The lower block `∑_{j : Fin t} C (cs j)·X^j` — a polynomial of degree `< t` carrying the `t`
prescribed low coefficients. -/
noncomputable def lowerBlock (t : ℕ) (cs : Fin t → F) : F[X] :=
  ∑ j : Fin t, C (cs j) * X ^ (j : ℕ)

/-- The lower block has `degree < t`. -/
theorem lowerBlock_degree_lt (t : ℕ) (cs : Fin t → F) : (lowerBlock t cs).degree < t :=
  degree_sum_fin_lt cs

/-- The coefficient of the lower block at any index `i : Fin t` is `cs i`. -/
theorem lowerBlock_coeff (t : ℕ) (cs : Fin t → F) (i : Fin t) :
    (lowerBlock t cs).coeff (i : ℕ) = cs i := by
  classical
  rw [lowerBlock, Polynomial.finset_sum_coeff, Finset.sum_eq_single i]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro b _ hb
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
    intro h; exact hb (Fin.ext h.symm)
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The degree-`t` "shape" polynomial `X^t + ∑_{j<t} C (cs j)·X^j`: monic of natDegree `t`, with the
`t` lower coefficients prescribed by `cs`. -/
noncomputable def hPoly (t : ℕ) (cs : Fin t → F) : F[X] :=
  X ^ t + lowerBlock t cs

/-- `hPoly t cs` is monic (leading term `X^t`, lower part of degree `< t`). -/
theorem hPoly_monic (t : ℕ) (cs : Fin t → F) : (hPoly t cs).Monic :=
  monic_X_pow_add (lowerBlock_degree_lt t cs)

/-- `hPoly t cs` has natDegree exactly `t`. -/
theorem hPoly_natDegree (t : ℕ) (cs : Fin t → F) : (hPoly t cs).natDegree = t := by
  have hdeglt : (lowerBlock t cs).degree < ((X : F[X]) ^ t).degree := by
    rw [degree_X_pow]; exact lowerBlock_degree_lt t cs
  have hdeg : (hPoly t cs).degree = (t : ℕ) := by
    rw [hPoly, degree_add_eq_left_of_degree_lt hdeglt, degree_X_pow]
  exact natDegree_eq_of_degree_eq_some hdeg

/-- The chosen degree-`(k+t)` word polynomial: `g = X^k · (X^t + ∑_{j<t} C (cs j)·X^j)`. As a product
of two monics it is monic of natDegree `k+t`; its `X^{k+j}` coefficient is `cs j` for `j < t` (and `1`
at `j = t`). Hence the `t` cancellation targets of `p_S` are realized at the chosen fiber `cs`. -/
noncomputable def wordPolyT (k t : ℕ) (cs : Fin t → F) : F[X] :=
  X ^ k * hPoly t cs

/-- `wordPolyT k t cs` is monic (a product of two monics). -/
theorem wordPolyT_monic (k t : ℕ) (cs : Fin t → F) : (wordPolyT k t cs).Monic :=
  (monic_X_pow k).mul (hPoly_monic t cs)

/-- `wordPolyT k t cs` has natDegree exactly `k + t`. -/
theorem wordPolyT_natDegree (k t : ℕ) (cs : Fin t → F) : (wordPolyT k t cs).natDegree = k + t := by
  rw [wordPolyT, Polynomial.Monic.natDegree_mul (monic_X_pow k) (hPoly_monic t cs),
    natDegree_X_pow, hPoly_natDegree]

/-- `wordPolyT k t cs` is nonzero (monic over a field). -/
theorem wordPolyT_ne_zero (k t : ℕ) (cs : Fin t → F) : wordPolyT k t cs ≠ 0 :=
  (wordPolyT_monic k t cs).ne_zero

/-- `wordPolyT k t cs` has leading coefficient `1`. -/
theorem wordPolyT_leadingCoeff (k t : ℕ) (cs : Fin t → F) :
    (wordPolyT k t cs).leadingCoeff = 1 := wordPolyT_monic k t cs

/-- **The key coefficient identity.** For `i : Fin t`, `(wordPolyT k t cs).coeff (k + i) = cs i`.
From `g = X^k · h`, `g.coeff (k + i) = h.coeff i` (the `X^k` factor shifts by `k`), and
`h.coeff i = cs i` by `lowerBlock_coeff`. -/
theorem wordPolyT_coeff_add (k t : ℕ) (cs : Fin t → F) (i : Fin t) :
    (wordPolyT k t cs).coeff (k + (i : ℕ)) = cs i := by
  classical
  rw [wordPolyT, hPoly, mul_add, Polynomial.coeff_add]
  -- the `X^k * X^t` term contributes `0` at index `k + i` since `i < t`.
  have hXkXt : (X ^ k * X ^ t : F[X]).coeff (k + (i : ℕ)) = 0 := by
    rw [← pow_add, Polynomial.coeff_X_pow, if_neg]
    intro h; have : (i : ℕ) = t := by omega
    exact absurd this (by have := i.isLt; omega)
  -- the `X^k * lowerBlock` term contributes `lowerBlock.coeff i = cs i` at index `k + i`.
  have hXkL : (X ^ k * lowerBlock t cs : F[X]).coeff (k + (i : ℕ)) = cs i := by
    rw [Polynomial.coeff_X_pow_mul', if_pos (Nat.le_add_right k _),
      Nat.add_sub_cancel_left, lowerBlock_coeff]
  rw [hXkXt, hXkL, zero_add]

/-! ## The top-`t`-coefficient vector of the root product and the `t`-fold fiber. -/

/-- The **top-`t`-coefficient vector** of the monic root product `∏_{i∈S}(X − D i)` over the index
window `[k, k+t)`: `coeffVec D k t S j = (∏_{i∈S}(X − D i)).coeff (k + j)`. This is the natural
pigeonhole statistic — the `t` coefficients whose matching forces the degree drop of `p_S`. -/
noncomputable def coeffVec (D : ι ↪ F) (k t : ℕ) (S : Finset ι) : Fin t → F :=
  fun j => (∏ i ∈ S, (X - C (D i))).coeff (k + (j : ℕ))

variable [DecidableEq F]

/-- The `t`-fold fiber family: `(k+t)`-subsets of `ι` whose root-product top-`t`-coefficient vector
equals the target `cs ∈ (Fin t → F)`. For `g = wordPolyT k t cs` each such `S` forces `deg(p_S) < k`
(`tFamily_forces_degDrop`), so this is the carrier of the general-`t` degree-drop family. -/
noncomputable def tFamily (D : ι ↪ F) (k t : ℕ) (cs : Fin t → F) : Finset (Finset ι) :=
  (Finset.univ.powersetCard (k + t)).filter (fun S => coeffVec D k t S = cs)

set_option linter.unusedSectionVars false in
/-- **Total over target vectors `= C(n, k+t)`.** The `(k+t)`-subsets of `ι` are partitioned by their
top-`t`-coefficient vector `coeffVec D k t S ∈ (Fin t → F)`, so summing the fiber sizes over all `q^t`
target vectors recovers `C(n, k+t)`. The conservation law driving the `t`-fold pigeonhole. -/
theorem sum_tFamily_card_eq_choose [Fintype F] (D : ι ↪ F) (k t : ℕ) :
    ∑ cs : Fin t → F, (tFamily D k t cs).card = (Fintype.card ι).choose (k + t) := by
  classical
  unfold tFamily
  have hpart : (Finset.univ.powersetCard (k + t) : Finset (Finset ι)).card
      = ∑ cs : Fin t → F,
          ((Finset.univ.powersetCard (k + t)).filter
            (fun S => coeffVec D k t S = cs)).card :=
    Finset.card_eq_sum_card_fiberwise
      (f := fun S => coeffVec D k t S) (t := (Finset.univ : Finset (Fin t → F)))
      (fun S _ => Finset.mem_univ _)
  rw [← hpart, Finset.card_powersetCard, Finset.card_univ]

/-- **The `t`-fold pigeonhole.** Since the `(k+t)`-fibers total `C(n, k+t)` over the
`q^t = |Fin t → F|` target vectors, some vector `cs` has `q^t · (fiber size) ≥ C(n, k+t)`. (Same
averaging argument as the `t = 1` / `t = 2` cases, run over the product index set `Fin t → F` of size
`q^t`.) -/
theorem exists_tFamily_card_ge [Fintype F] (D : ι ↪ F) (k t : ℕ) (hq : 0 < Fintype.card F) :
    ∃ cs : Fin t → F,
      (Fintype.card ι).choose (k + t)
        ≤ Fintype.card F ^ t * (tFamily D k t cs).card := by
  classical
  by_contra hcon
  push_neg at hcon
  have hsum : ∑ cs : Fin t → F, (tFamily D k t cs).card = (Fintype.card ι).choose (k + t) :=
    sum_tFamily_card_eq_choose D k t
  -- average argument: every fiber `< C(n,k+t)/q^t` forces the total `< C(n,k+t)`.
  have hcardF : Fintype.card (Fin t → F) = Fintype.card F ^ t := by
    rw [Fintype.card_fun, Fintype.card_fin]
  have hcon' : ∀ cs : Fin t → F,
      (tFamily D k t cs).card * Fintype.card F ^ t < (Fintype.card ι).choose (k + t) := by
    intro cs; rw [mul_comm]; exact hcon cs
  have hprodne : (Finset.univ : Finset (Fin t → F)).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    refine Fintype.card_pos_iff.mp ?_
    rw [hcardF]; exact pow_pos hq t
  have hbound : ∑ cs : Fin t → F, (tFamily D k t cs).card < (Fintype.card ι).choose (k + t) := by
    by_cases hn0 : (Fintype.card ι).choose (k + t) = 0
    · exact absurd (hcon' (Classical.arbitrary (Fin t → F)))
        (by rw [hn0]; exact Nat.not_lt_zero _)
    · have hmul : (∑ cs : Fin t → F, (tFamily D k t cs).card) * Fintype.card F ^ t
            < Fintype.card F ^ t * (Fintype.card ι).choose (k + t) := by
        calc (∑ cs : Fin t → F, (tFamily D k t cs).card) * Fintype.card F ^ t
            = ∑ cs : Fin t → F, (tFamily D k t cs).card * Fintype.card F ^ t := by
              rw [Finset.sum_mul]
          _ < ∑ _cs : Fin t → F, (Fintype.card ι).choose (k + t) :=
              Finset.sum_lt_sum_of_nonempty hprodne (fun cs _ => hcon' cs)
          _ = Fintype.card F ^ t * (Fintype.card ι).choose (k + t) := by
              rw [Finset.sum_const, Finset.card_univ, hcardF, smul_eq_mul]
      exact lt_of_mul_lt_mul_right
        (by rwa [mul_comm (Fintype.card F ^ t)] at hmul) (Nat.zero_le _)
  rw [hsum] at hbound
  exact lt_irrefl _ hbound

/-! ## Each fiber member forces the degree drop: the carrier is a genuine `DegDropFamily`. -/

set_option linter.unusedSectionVars false in
/-- Every member of `tFamily D k t cs` has card `k + t` (by definition of the carrier). -/
theorem tFamily_card (D : ι ↪ F) (k t : ℕ) (cs : Fin t → F)
    {S : Finset ι} (hS : S ∈ tFamily D k t cs) : S.card = k + t := by
  rw [tFamily, Finset.mem_filter, Finset.mem_powersetCard] at hS
  exact hS.1.2

set_option linter.unusedSectionVars false in
/-- **The fiber forces all top-`t` coefficients of `p_S` to vanish.** For `g = wordPolyT k t cs` (so
`g.leadingCoeff = 1` and `g.coeff (k+j) = cs j`) and any `S ∈ tFamily D k t cs` (so
`(∏_{i∈S}(X − D i)).coeff (k+j) = cs j`), each top coefficient cancels:
`p_S.coeff (k+j) = g.coeff (k+j) − 1·(∏_S).coeff (k+j) = cs j − cs j = 0`, for every `j : Fin t`. -/
theorem tFamily_coeff_zero (D : ι ↪ F) (k t : ℕ) (cs : Fin t → F)
    {S : Finset ι} (hS : S ∈ tFamily D k t cs) (j : Fin t) :
    (pSt D (wordPolyT k t cs) (wordPolyT k t cs).leadingCoeff S).coeff (k + (j : ℕ)) = 0 := by
  classical
  rw [tFamily, Finset.mem_filter] at hS
  obtain ⟨_, hvec⟩ := hS
  have hPcoeff : (∏ i ∈ S, (X - C (D i))).coeff (k + (j : ℕ)) = cs j := by
    have := congrFun hvec j
    rwa [coeffVec] at this
  rw [pSt, wordPolyT_leadingCoeff, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    wordPolyT_coeff_add, hPcoeff, one_mul, sub_self]

/-- **All top-`t` coefficients vanishing ⟹ degree drop to `< k`.** With `g = wordPolyT k t cs` of
natDegree `k+t`, `0 < k`, and `S` of card `k+t`, if `p_S.coeff (k+j) = 0` for every `j : Fin t`, then
`p_S.natDegree < k`. `p_S` already has natDegree `< k+t` (`pSt_natDegree_lt_interior`); if its natDegree
were `≥ k` it would be some `k + j` with `j < t`, but then the leading coefficient
`p_S.coeff (p_S.natDegree) = p_S.coeff (k+j) = 0` forces `p_S = 0` of natDegree `0 < k`, contradiction. -/
theorem tFamily_forces_degDrop (D : ι ↪ F) (k t : ℕ) (cs : Fin t → F) (hk : 0 < k)
    {S : Finset ι} (hS : S ∈ tFamily D k t cs) :
    (pSt D (wordPolyT k t cs) (wordPolyT k t cs).leadingCoeff S).natDegree < k := by
  classical
  set g := wordPolyT k t cs with hg
  set p := pSt D g g.leadingCoeff S with hp
  have hScard : S.card = k + t := tFamily_card D k t cs hS
  -- `p` has natDegree `< k + t` unconditionally.
  have hlt : p.natDegree < k + t :=
    pSt_natDegree_lt_interior D g (wordPolyT_natDegree k t cs) (by omega)
      (wordPolyT_ne_zero k t cs) S hScard
  by_contra hge
  push_neg at hge  -- k ≤ p.natDegree
  -- `p.natDegree = k + j` for some `j < t`.
  have hjlt : p.natDegree - k < t := by omega
  set j : Fin t := ⟨p.natDegree - k, hjlt⟩ with hj
  have hjval : k + (j : ℕ) = p.natDegree := by simp [hj]; omega
  -- the chosen coefficient vanishes (fiber condition), but it is the leading coefficient.
  have hcoeff0 : p.coeff (k + (j : ℕ)) = 0 := by
    rw [hp]; exact tFamily_coeff_zero D k t cs hS j
  rw [hjval] at hcoeff0
  -- `p.coeff p.natDegree = leadingCoeff = 0 ⟹ p = 0 ⟹ natDegree 0 < k`, contradicting `k ≤ natDegree`.
  rw [← Polynomial.leadingCoeff, Polynomial.leadingCoeff_eq_zero] at hcoeff0
  rw [hcoeff0, Polynomial.natDegree_zero] at hge
  omega

/-- The general-`t` degree-drop family for `g = wordPolyT k t cs` with carrier the `t`-fold fiber
`tFamily D k t cs`. Each member's `(k+t)`-card and degree drop are supplied by `tFamily_card` and
`tFamily_forces_degDrop`. -/
noncomputable def tDegDropFamily (D : ι ↪ F) (k t : ℕ) (cs : Fin t → F) (hk : 0 < k) :
    DegDropFamily D (wordPolyT k t cs) k t where
  carrier := tFamily D k t cs
  card_eq := fun _S hS => tFamily_card D k t cs hS
  deg_lt := fun _S hS => tFamily_forces_degDrop D k t cs hk hS

/-- The carrier of `tDegDropFamily` is `tFamily D k t cs` (by definition). -/
theorem tDegDropFamily_carrier (D : ι ↪ F) (k t : ℕ) (cs : Fin t → F) (hk : 0 < k) :
    (tDegDropFamily D k t cs hk).carrier = tFamily D k t cs := rfl

/-! ## The headline: the unconditional general-`t` interior list lower bound. -/

open Classical in
/-- **The unconditional, general-`t`, general-`n`, interior list-decoding lower bound** (Issue #232).

For a smooth-domain Reed–Solomon code `RS[F, D, k]` (`D : ι ↪ F` injective, `0 < k`, `k ≤ n = |ι|`)
and **any** `t ≥ 1` at the interior radius `δ = 1 − (k+t)/n` (interiorness certified by `(k+t)² < k·n`,
allowing `t` up to `≈ √(kn) − k` — a constant fraction of `k` into the deep interior), there exists an
explicit received word `w = (i ↦ g(D i))` with `g = X^k·(X^t + ∑_{j<t} C (cs j)·X^j)` of degree
exactly `k+t` such that the list of codewords agreeing with `w` on `≥ k+t` coordinates has size
`≥ C(n,k+t)/q^t`:

  `C(n, k+t)  ≤  q^t · #{ v ∈ RS[F,D,k] : agree(v, w) ≥ k+t }`.

No degree-drop family and no count hypothesis are assumed — all are constructed internally (the family
is the top-`t`-coefficient-vector fiber; the count is the `t`-fold pigeonhole lower bound
`C(n,k+t)/q^t`). This is the Round-5/6 `t = 1, 2` welds generalized to *every* `t` at once, via the
coordinate-free top-coefficient-vector pigeonhole, at the cost of the worst-case `1/q^t` denominator. -/
theorem exists_interior_list_ge_unconditional_t [Fintype F] (D : ι ↪ F) {k t : ℕ}
    (hk : 0 < k) (ht : 0 < t) (hkn : k ≤ Fintype.card ι) (hq : 0 < Fintype.card F)
    (hint : (k + t) ^ 2 < k * Fintype.card ι) :
    ∃ (g : F[X]), g.natDegree = k + t ∧
      (Fintype.card ι).choose (k + t) ≤
        Fintype.card F ^ t *
          (Finset.univ.filter (fun v : ι → F =>
            v ∈ ReedSolomon.code D k ∧
              k + t ≤ agreeCount v (fun i => g.eval (D i)))).card := by
  classical
  -- interiorness certificate (kept to tie the statement to the strictly-interior radius).
  have _hinterior : k < k + t ∧ (k + t) ^ 2 < k * Fintype.card ι :=
    interior_radius_witness ht hint
  -- `t`-fold pigeonhole: pick the heavy top-`t`-coefficient-vector target.
  obtain ⟨cs, hcount⟩ := exists_tFamily_card_ge D k t hq
  refine ⟨wordPolyT k t cs, wordPolyT_natDegree k t cs, ?_⟩
  -- the bridge: list ≥ |carrier| = |tFamily|.
  have hbridge :=
    interior_list_card_ge_family D (wordPolyT k t cs)
      (wordPolyT_ne_zero k t cs) hkn (tDegDropFamily D k t cs hk)
  rw [tDegDropFamily_carrier D k t cs hk] at hbridge
  -- chain: C(n,k+t) ≤ q^t·|tFamily| ≤ q^t·(list size).
  calc (Fintype.card ι).choose (k + t)
      ≤ Fintype.card F ^ t * (tFamily D k t cs).card := hcount
    _ ≤ Fintype.card F ^ t * _ := Nat.mul_le_mul_left _ hbridge

/-! ## Specializations to `t = 1` and `t = 2` (sanity: the general engine recovers the prior radii). -/

open Classical in
/-- **Specialization to `t = 1`** (recovers the Round-5 radius `δ = 1 − (k+1)/n`, with the general
engine's `q^1 = q` denominator). -/
theorem exists_interior_list_ge_unconditional_t_at1 [Fintype F] (D : ι ↪ F) {k : ℕ}
    (hk : 0 < k) (hkn : k ≤ Fintype.card ι) (hq : 0 < Fintype.card F)
    (hint : (k + 1) ^ 2 < k * Fintype.card ι) :
    ∃ (g : F[X]), g.natDegree = k + 1 ∧
      (Fintype.card ι).choose (k + 1) ≤
        Fintype.card F ^ 1 *
          (Finset.univ.filter (fun v : ι → F =>
            v ∈ ReedSolomon.code D k ∧
              k + 1 ≤ agreeCount v (fun i => g.eval (D i)))).card :=
  exists_interior_list_ge_unconditional_t D hk (by norm_num) hkn hq hint

open Classical in
/-- **Specialization to `t = 2`** (recovers the Round-6 radius `δ = 1 − (k+2)/n`, with `q^2`
denominator — matching `exists_interior_list_ge_unconditional_t2`). -/
theorem exists_interior_list_ge_unconditional_t_at2 [Fintype F] (D : ι ↪ F) {k : ℕ}
    (hk : 0 < k) (hkn : k ≤ Fintype.card ι) (hq : 0 < Fintype.card F)
    (hint : (k + 2) ^ 2 < k * Fintype.card ι) :
    ∃ (g : F[X]), g.natDegree = k + 2 ∧
      (Fintype.card ι).choose (k + 2) ≤
        Fintype.card F ^ 2 *
          (Finset.univ.filter (fun v : ι → F =>
            v ∈ ReedSolomon.code D k ∧
              k + 2 ≤ agreeCount v (fun i => g.eval (D i)))).card :=
  exists_interior_list_ge_unconditional_t D hk (by norm_num) hkn hq hint

/-! ## Non-vacuity: the hypotheses are jointly satisfiable, and the interior radius is genuinely deep. -/

/-- **The headline hypotheses are jointly satisfiable, with `t` a constant fraction of `k`
(non-vacuity, deep interior).** At `k = 100`, `t = 40`, `n = 400` (rate `ρ = 1/4`), all five
arithmetic premises of `exists_interior_list_ge_unconditional_t` hold: `0 < k`, `0 < t`, `k ≤ n`,
`(k+t)² = 140² = 19600 < 40000 = k·n`. Here `t = 40 = 0.4·k` is **well past the `O(1)` steps** of
the `t = 1, 2` welds — a genuinely deep interior agreement `k + t = 140` out of `n = 400`. Pairing
with any finite field `F` (`0 < |F|`) and `|ι| = 400` instantiates the theorem with
`C(400, 140) > 0` on the right — a genuine, non-vacuous list bound
`C(400,140) ≤ q^{40} · (list size)`. -/
theorem headline_hypotheses_satisfiable_t :
    0 < 100 ∧ 0 < 40 ∧ (100 : ℕ) ≤ 400 ∧ (100 + 40) ^ 2 < 100 * 400
      ∧ 0 < Nat.choose 400 (100 + 40) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, ?_⟩
  exact Nat.choose_pos (by norm_num)

/-- **The interior radius reaches a constant fraction of `k` for any rate (qualitative depth).** At
rate `ρ = 1/2` (`n = 2k`), the interiorness `(k+t)² < k·n = 2k²` holds for all `t` with
`(k+t)² < 2k²`, e.g. `t = ⌊0.4·k⌋`: at `k = 100`, `t = 40`, `n = 200`, `(140)² = 19600 < 20000`. So
even at rate `1/2` the deep interior (`t` a constant fraction of `k`) is reached — far beyond the
`O(1)` steps of `t = 1, 2`. -/
theorem interior_depth_rate_half : (100 + 40) ^ 2 < 100 * 200 ∧ 0 < 40 := by norm_num

end ArkLib.CodingTheory.Round7GeneralT

/-! ## Axiom audit -/
#print axioms ArkLib.CodingTheory.Round7GeneralT.lowerBlock_coeff
#print axioms ArkLib.CodingTheory.Round7GeneralT.hPoly_natDegree
#print axioms ArkLib.CodingTheory.Round7GeneralT.wordPolyT_natDegree
#print axioms ArkLib.CodingTheory.Round7GeneralT.wordPolyT_coeff_add
#print axioms ArkLib.CodingTheory.Round7GeneralT.sum_tFamily_card_eq_choose
#print axioms ArkLib.CodingTheory.Round7GeneralT.exists_tFamily_card_ge
#print axioms ArkLib.CodingTheory.Round7GeneralT.tFamily_coeff_zero
#print axioms ArkLib.CodingTheory.Round7GeneralT.tFamily_forces_degDrop
#print axioms ArkLib.CodingTheory.Round7GeneralT.tDegDropFamily_carrier
#print axioms ArkLib.CodingTheory.Round7GeneralT.exists_interior_list_ge_unconditional_t
#print axioms ArkLib.CodingTheory.Round7GeneralT.exists_interior_list_ge_unconditional_t_at1
#print axioms ArkLib.CodingTheory.Round7GeneralT.exists_interior_list_ge_unconditional_t_at2
#print axioms ArkLib.CodingTheory.Round7GeneralT.headline_hypotheses_satisfiable_t
