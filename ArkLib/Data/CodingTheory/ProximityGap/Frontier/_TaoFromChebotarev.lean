/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrimeCapacityUncertainty
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Reducing Tao's additive uncertainty to Chebotarev's minor-nonvanishing theorem (#407)

The prime side of the #407 [349] DFT-uncertainty dichotomy
(`_PrimeCapacityUncertainty.lean`) is conditional on a single NAMED OPEN input,
`TaoUncertainty p` (Tao 2005, MRL 12(1):121–127):

> `∀ f : ZMod p → ℂ, f ≠ 0 → |supp f| + |supp 𝓕f| ≥ p + 1`.

Tao's own proof of this principle has exactly one non-elementary ingredient: a classical
theorem of **Chebotarev (1926)** that *every minor of the prime-order DFT matrix is nonzero*
(equivalently: every square submatrix of the Vandermonde-in-`p`-th-roots-of-unity matrix is
invertible). Chebotarev's theorem is itself a deep Galois / cyclotomic-irreducibility fact —
genuinely *false* for composite order, which is the structural reason Tao's additive bound holds
only for primes — and it is **not in Mathlib**.

This file performs the *standard Tao reduction*, isolating Chebotarev as the sole open input:

* **`ChebotarevMinorNonvanishing p` is a NAMED `Prop` (not proven in general).** It is
  Chebotarev's theorem, phrased on the DFT matrix entries `stdAddChar (-(j * k))` actually used by
  `ZMod.dft`: for any `n` and any two *injective* index selections `ri ci : Fin n → ZMod p`
  (distinct rows and distinct columns), the `n × n` submatrix `M i j = stdAddChar (-(ci j * ri i))`
  has nonzero determinant.

* **`tao_of_chebotarev : ChebotarevMinorNonvanishing p → TaoUncertainty p` IS PROVEN here**
  (axiom-clean). The argument: given `f ≠ 0` with `|supp f| + |supp (𝓕 f)| ≤ p`, take `A = supp f`,
  `B = supp (𝓕 f)`, so `|A| ≤ p − |B| = |Bᶜ|`; pick `R ⊆ Bᶜ` with `|R| = |A|`; on `R` the transform
  `𝓕 f` vanishes (`R ⊆ Bᶜ`). Enumerating `R` and `A` by injections `ri, ci : Fin |A| → ZMod p`, the
  restriction of `𝓕 f` to `R` *is* the matrix–vector product `M *ᵥ (f ∘ ci) = 0` with `M` the
  Chebotarev submatrix; `M.det ≠ 0` forces `f ∘ ci = 0`, i.e. `f` vanishes on `A` too, so `f = 0`,
  contradiction.

* **`chebotarev_one : ChebotarevMinorNonvanishing` at `n = 1` IS PROVEN** (trivial: a `1 × 1`
  minor is a single root of unity `stdAddChar (-(ci 0 * ri 0)) ≠ 0`). This de-names the smallest
  case; the general `n` case stays the named open input `ChebotarevMinorNonvanishing`.

* **`chebotarev_two : the `n = 2` case (FULL general exponents) IS PROVEN.** For injective
  `ri ci : Fin 2 → ZMod p`, `det = stdAddChar A − stdAddChar B` with `A − B = (c0 − c1)(r1 − r0) ≠ 0`
  in the field `ZMod p`, so by `ZMod.injective_stdAddChar` the two character values differ and the
  det is nonzero. This de-names the *whole* `n = 2` instance (arbitrary exponents), not a slice.

* **The equal-spacing exponent sub-case for general `n` IS PROVEN** (`chebotarev_equalExponents`,
  `chebotarev_minor_equalExponents`, any `n ≤ p`). When the column selection is the consecutive
  exponent run `c_j = j` (here encoded as `ci j = -(↑j : ZMod p)` to match the DFT sign convention),
  the minor entry is `stdAddChar(j·r_i) = (ζ^{r_i})^j`, i.e. the matrix *is* a Vandermonde in the
  distinct nodes `ζ^{r_i} = stdAddChar (ri i)`. Mathlib's `Matrix.det_vandermonde_ne_zero_iff` then
  gives `det = ∏_{i<i'} (ζ^{r_{i'}} − ζ^{r_i}) ≠ 0` directly from injectivity (the nodes are distinct
  by `ZMod.injective_stdAddChar`). This is genuinely general-`n`. We also expose the underlying kernel
  as a named `Prop` `StandardVandermondeNonzeroModP` with its proof `standardVandermondeNonzeroModP_holds`.

  **Boundary:** this is ONLY the equal-spacing exponent slice. The deep content of Chebotarev's
  theorem is precisely that *arbitrary* distinct exponents `c_j` (generalized Vandermonde, where the
  Mathlib `det_vandermonde` formula does **not** apply and over a generic field the det **can**
  vanish) still give a nonzero det for prime `p`. That general-exponent reduction (viewing
  `D(ζ) ∈ ℤ[ζ_p]` and reducing mod the prime above `p` to a standard Vandermonde in the distinct
  `r_i mod p`) is multi-file algebraic number theory not attempted here; the general `n` case stays
  the named open input `ChebotarevMinorNonvanishing`.

## Honesty contract (per #407)

`ChebotarevMinorNonvanishing` is a `def … : Prop` (a named classical hypothesis), so it carries no
axioms; we never `sorry` it and never claim the general case proven. What is PROVEN here is the
*reduction* `tao_of_chebotarev`, plus the `1 × 1` case `chebotarev_one`, the FULL `2 × 2` case
`chebotarev_two` (general exponents), and the equal-spacing general-`n` sub-case
`chebotarev_equalExponents` (via `Matrix.det_vandermonde`). The general-exponent general-`n` case
remains the named open input. This sharpens `_PrimeCapacityUncertainty`: the prime-capacity dichotomy
is now conditional on the *canonical classical theorem of Chebotarev*, not on the looser folklore
statement `TaoUncertainty`.

Reference for the reduction and for Chebotarev's theorem: T. Tao, *An uncertainty principle for
cyclic groups of prime order*, Math. Res. Lett. 12 (2005), 121–127; P. Stevenhagen & H. W. Lenstra,
*Chebotarëv and his density theorem*, Math. Intelligencer 18 (1996) (exposition of Chebotarev's
minor theorem); Tao's blog post of the same title (2005).

Axiom-clean (`propext, Classical.choice, Quot.sound`; no `sorryAx`). Issue #407.
-/

open Finset ZMod Matrix
open ProximityGap.Frontier.ZModDonohoStark
open ProximityGap.Frontier.PrimeCapacityUncertainty

namespace ProximityGap.Frontier.TaoFromChebotarev

variable {p : ℕ} [Fact p.Prime]

/-- **Chebotarev's minor-nonvanishing theorem for the prime DFT matrix (NAMED OPEN INPUT — only the
`n = 1` case is proven, as `chebotarev_one`).**

> For `p` prime, *every minor of the `p × p` DFT matrix is nonzero*.

Phrased on the DFT entries `stdAddChar (-(j * k))` that `ZMod.dft` actually uses: for any `n` and
any pair of *injective* selections `ri ci : Fin n → ZMod p` (so distinct rows and distinct columns),
the `n × n` submatrix `M i j = stdAddChar (-(ci j * ri i))` has nonzero determinant.

This is the classical theorem of **Chebotarev (1926)** — equivalently, every square submatrix of the
Vandermonde matrix in the `p`-th roots of unity is invertible. It is a deep
Galois/cyclotomic-irreducibility fact, **not present in Mathlib**, and *false* for composite order
(which is exactly why Tao's additive uncertainty principle is prime-only). Per the #407 honesty
contract it is a named `Prop` (carries no axioms); we never prove the general case nor `sorry` it.
The smallest case (`n = 1`) IS discharged below (`chebotarev_one`). -/
def ChebotarevMinorNonvanishing (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (n : ℕ) (ri ci : Fin n → ZMod p), Function.Injective ri → Function.Injective ci →
    (Matrix.of fun (i j : Fin n) => (stdAddChar (-(ci j * ri i)) : ℂ)).det ≠ 0

/-- **The `1 × 1` case of Chebotarev's theorem (PROVEN).** A single DFT entry
`stdAddChar (-(ci 0 * ri 0))` is a root of unity, hence nonzero, so the `1 × 1` minor has nonzero
determinant. This de-names the smallest instance of `ChebotarevMinorNonvanishing`; the general `n`
case remains the named open input. -/
theorem chebotarev_one (ri ci : Fin 1 → ZMod p) :
    (Matrix.of fun (i j : Fin 1) => (stdAddChar (-(ci j * ri i)) : ℂ)).det ≠ 0 := by
  rw [Matrix.det_fin_one]
  -- a single DFT entry is a unit-modulus complex number, hence nonzero.
  have hnorm : ‖(stdAddChar (-(ci 0 * ri 0)) : ℂ)‖ = 1 := norm_stdAddChar (N := p) (-(ci 0 * ri 0))
  intro hzero
  simp only [Matrix.of_apply] at hzero
  rw [hzero, norm_zero] at hnorm
  exact one_ne_zero hnorm.symm

/-- **The `2 × 2` case of Chebotarev's theorem (PROVEN, general exponents).** For `p` prime and any
two *injective* selections `ri ci : Fin 2 → ZMod p` (so `ri 0 ≠ ri 1` and `ci 0 ≠ ci 1`), the `2 × 2`
minor `M i j = stdAddChar (-(ci j * ri i))` has nonzero determinant.

Proof (Tao's argument specialised to `n = 2`): by `Matrix.det_fin_two`,
`det = stdAddChar(-(c0 r0))·stdAddChar(-(c1 r1)) − stdAddChar(-(c1 r0))·stdAddChar(-(c0 r1))`.
Each product is a single character value (`AddChar.map_add_eq_mul`), so
`det = stdAddChar A − stdAddChar B` with `A = -(c0 r0 + c1 r1)`, `B = -(c1 r0 + c0 r1)`. Then
`A − B = (c0 − c1)(r1 − r0) ≠ 0` because `ZMod p` is a field (prime `p` ⟹ integral domain) and both
factors are nonzero (injectivity). Hence `A ≠ B`, and by `ZMod.injective_stdAddChar` the two
character values differ, so `det ≠ 0`. This de-names the `n = 2` instance of
`ChebotarevMinorNonvanishing` in full (arbitrary exponents); the general `n` case stays open. -/
theorem chebotarev_two (ri ci : Fin 2 → ZMod p)
    (hri : Function.Injective ri) (hci : Function.Injective ci) :
    (Matrix.of fun (i j : Fin 2) => (stdAddChar (-(ci j * ri i)) : ℂ)).det ≠ 0 := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.of_apply]
  -- Collapse each product of two character values into one (`stdAddChar` is multiplicative).
  set A : ZMod p := -(ci 0 * ri 0) + -(ci 1 * ri 1) with hAdef
  set B : ZMod p := -(ci 1 * ri 0) + -(ci 0 * ri 1) with hBdef
  have hprod1 : (stdAddChar (-(ci 0 * ri 0)) : ℂ) * stdAddChar (-(ci 1 * ri 1))
      = stdAddChar A := (AddChar.map_add_eq_mul _ _ _).symm
  have hprod2 : (stdAddChar (-(ci 1 * ri 0)) : ℂ) * stdAddChar (-(ci 0 * ri 1))
      = stdAddChar B := (AddChar.map_add_eq_mul _ _ _).symm
  rw [hprod1, hprod2]
  -- `det = stdAddChar A − stdAddChar B`; nonzero iff `A ≠ B` (injectivity of `stdAddChar`).
  rw [sub_ne_zero]
  intro hAB
  have hABeq : A = B := ZMod.injective_stdAddChar hAB
  -- But `A − B = (ci 0 − ci 1)·(ri 1 − ri 0) ≠ 0` in the field `ZMod p`.
  have hc01 : ci 0 ≠ ci 1 := fun h => by simpa using hci h
  have hr01 : ri 0 ≠ ri 1 := fun h => by simpa using hri h
  have hfac : A - B = (ci 0 - ci 1) * (ri 1 - ri 0) := by rw [hAdef, hBdef]; ring
  have hne : (ci 0 - ci 1) * (ri 1 - ri 0) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hc01) (sub_ne_zero.mpr (fun h => hr01 h.symm))
  rw [hABeq, sub_self] at hfac
  exact hne hfac.symm

/-- **The standard (equal-spacing) Vandermonde determinant is nonzero mod `p` for distinct nodes
(NAMED — but PROVEN below, `chebotarev_equalExponents`).** For distinct `r_i : ZMod p`, the
determinant of the matrix `((ζ^{r_i})^{c_j})` with consecutive exponents `c_j = j` is nonzero. This
is the elementary number-theoretic kernel of Chebotarev's theorem (the equal-spacing exponent
slice), discharged directly from Mathlib's `Matrix.det_vandermonde` (since the nodes `ζ^{r_i}` are
distinct). The *general*-exponent case is the deep part of Chebotarev's theorem and remains open. -/
def StandardVandermondeNonzeroModP (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (n : ℕ) (ri : Fin n → ZMod p), Function.Injective ri →
    (Matrix.of fun (i j : Fin n) => (stdAddChar (ri i) : ℂ) ^ (j : ℕ)).det ≠ 0

/-- The nodes `ζ^{r_i} = stdAddChar (ri i)` are distinct when the `ri` are distinct, since
`ZMod.injective_stdAddChar` makes `stdAddChar` injective for prime `p`. -/
theorem injective_stdAddChar_comp {n : ℕ} (ri : Fin n → ZMod p) (hri : Function.Injective ri) :
    Function.Injective (fun i => (stdAddChar (ri i) : ℂ)) :=
  ZMod.injective_stdAddChar.comp hri

/-- **The equal-spacing Vandermonde kernel is PROVEN.** Directly from Mathlib's
`Matrix.det_vandermonde_ne_zero_iff`: the determinant of the Vandermonde matrix in the distinct
nodes `ζ^{r_i}` is `∏_{i<i'} (ζ^{r_{i'}} − ζ^{r_i}) ≠ 0`. -/
theorem standardVandermondeNonzeroModP_holds : StandardVandermondeNonzeroModP p := by
  intro n ri hri
  -- the matrix `i j ↦ (stdAddChar (ri i))^j` IS `Matrix.vandermonde (fun i => stdAddChar (ri i))`.
  have hmat : (Matrix.of fun (i j : Fin n) => (stdAddChar (ri i) : ℂ) ^ (j : ℕ))
      = Matrix.vandermonde (fun i => (stdAddChar (ri i) : ℂ)) := by
    ext i j; rfl
  rw [hmat]
  exact Matrix.det_vandermonde_ne_zero_iff.mpr (injective_stdAddChar_comp ri hri)

/-- **The equal-exponents (`c_j = j`) general-`n` sub-case of Chebotarev's theorem (PROVEN, any
`n`).** For `p` prime, any `n`, and any *injective* `ri : Fin n → ZMod p`, the `n × n` minor
`M i j = stdAddChar (-(ci j * ri i))` with the *consecutive* columns `ci j = -(↑j : ZMod p)`
has nonzero determinant.

This is a genuine general-`n` slice of `ChebotarevMinorNonvanishing`: the columns use the equal-
spacing exponents `0, 1, …, n−1` (up to the fixed sign convention of the DFT entry), and the result
follows from Mathlib's `Matrix.det_vandermonde` because the nodes `ζ^{r_i} = stdAddChar (ri i)` are
distinct (no `n ≤ p` needed for the determinant itself — the nodes are distinct complex numbers as
soon as `ri` is injective). The *general*-exponent case (arbitrary injective `ci`) is the deep
Chebotarev miracle and stays open. PROVEN, axiom-clean.

Concretely the entry rewrites as `stdAddChar(-((-j)·r_i)) = stdAddChar(j·r_i)
= stdAddChar(r_i)^j = (ζ^{r_i})^j`, the Vandermonde entry. -/
theorem chebotarev_equalExponents {n : ℕ} (ri : Fin n → ZMod p)
    (hri : Function.Injective ri) :
    (Matrix.of fun (i j : Fin n) =>
        (stdAddChar (-((-(↑(j : ℕ) : ZMod p)) * ri i)) : ℂ)).det ≠ 0 := by
  -- rewrite each entry into the Vandermonde entry `(stdAddChar (ri i))^j`.
  have hentry : ∀ i j : Fin n,
      (stdAddChar (-((-(↑(j : ℕ) : ZMod p)) * ri i)) : ℂ)
        = (stdAddChar (ri i) : ℂ) ^ (j : ℕ) := by
    intro i j
    have h1 : -((-(↑(j : ℕ) : ZMod p)) * ri i) = (j : ℕ) • ri i := by
      rw [neg_mul, neg_neg, nsmul_eq_mul]
    rw [h1, AddChar.map_nsmul_eq_pow]
  have hmat : (Matrix.of fun (i j : Fin n) =>
        (stdAddChar (-((-(↑(j : ℕ) : ZMod p)) * ri i)) : ℂ))
      = Matrix.of fun (i j : Fin n) => (stdAddChar (ri i) : ℂ) ^ (j : ℕ) := by
    ext i j; exact hentry i j
  rw [hmat]
  exact standardVandermondeNonzeroModP_holds n ri hri

/-- The consecutive column selection `ci = fun j => -(↑(j : ℕ) : ZMod p)` is **injective when
`n ≤ p`** (the nats `0, 1, …, n−1` are distinct mod `p`). This is exactly the hypothesis needed for
`ci` to be an admissible column selection of `ChebotarevMinorNonvanishing`, and the only place the
`n ≤ p` size restriction is genuinely used. -/
theorem injective_consecutive_cols {n : ℕ} (hn : n ≤ p) :
    Function.Injective (fun j : Fin n => -(↑(j : ℕ) : ZMod p)) := by
  intro a b hab
  -- strip the negation, then read off equal `val`s (both `< n ≤ p`).
  have hcast : (↑(a : ℕ) : ZMod p) = (↑(b : ℕ) : ZMod p) := by
    simpa using neg_injective hab
  have ha : (↑(a : ℕ) : ZMod p).val = (a : ℕ) := ZMod.val_natCast_of_lt (lt_of_lt_of_le a.2 hn)
  have hb : (↑(b : ℕ) : ZMod p).val = (b : ℕ) := ZMod.val_natCast_of_lt (lt_of_lt_of_le b.2 hn)
  have : (a : ℕ) = (b : ℕ) := by rw [← ha, ← hb, hcast]
  exact Fin.ext this

/-- **The equal-exponents sub-case, exhibited as a genuine admissible instance of the
`ChebotarevMinorNonvanishing` minor shape (PROVEN, `n ≤ p`).** The named hypothesis quantifies over
*both* injective selections `ri ci`; here we discharge it for the specific consecutive column
selection `ci = fun j => -(↑j : ZMod p)`, which (by `injective_consecutive_cols`) is injective when
`n ≤ p` — so this `ci` is an admissible column selection and the conclusion is a true instance of the
minor shape, with the determinant nonzero by `chebotarev_equalExponents`. The `n ≤ p` is needed only
to make `ci` injective; the determinant fact itself holds for any `n`. The general-exponent `ci`
(arbitrary injective columns) stays the named open input. -/
theorem chebotarev_minor_equalExponents {n : ℕ} (hn : n ≤ p) (ri : Fin n → ZMod p)
    (hri : Function.Injective ri) :
    Function.Injective (fun j : Fin n => -(↑(j : ℕ) : ZMod p)) ∧
      (Matrix.of fun (i j : Fin n) =>
        (stdAddChar (-(((fun j => -(↑(j : ℕ) : ZMod p)) j) * ri i)) : ℂ)).det ≠ 0 :=
  ⟨injective_consecutive_cols hn, chebotarev_equalExponents ri hri⟩

/-- **Tao's additive uncertainty principle, reduced to Chebotarev (PROVEN reduction).**

`ChebotarevMinorNonvanishing p ⟹ TaoUncertainty p`, i.e. granting that every minor of the prime DFT
matrix is nonzero, every nonzero `f : ZMod p → ℂ` satisfies `|supp f| + |supp 𝓕f| ≥ p + 1`.

This is the standard Tao argument: by contradiction assume `|A| + |B| ≤ p` for `A = supp f`,
`B = supp (𝓕 f)`; then `|A| ≤ |Bᶜ|`, pick `R ⊆ Bᶜ` of size `|A|`; the restriction of `𝓕 f` to `R`
is `M *ᵥ (f ∘ enum A) = 0` for the Chebotarev submatrix `M` (rows = `R`, columns = `A`); Chebotarev
makes `M` invertible, forcing `f ∘ enum A = 0`, i.e. `f` vanishes on `A` (also off `A` by
definition), so `f = 0` — contradiction.

PROVEN (axiom-clean), consuming only the named `ChebotarevMinorNonvanishing`. -/
theorem tao_of_chebotarev (hCheb : ChebotarevMinorNonvanishing p) : TaoUncertainty p := by
  intro f hf
  -- By contradiction: suppose `|supp f| + |supp (𝓕 f)| ≤ p`.
  by_contra hlt
  set A : Finset (ZMod p) := supp f with hA
  set B : Finset (ZMod p) := supp (𝓕 f) with hB
  -- `hlt : ¬ (p + 1 ≤ |A| + |B|)`, i.e. `|A| + |B| ≤ p`.
  have hle : A.card + B.card ≤ p := by omega
  -- `|univ| = p`.
  have hcardp : Fintype.card (ZMod p) = p := ZMod.card p
  -- `|A| ≤ |Bᶜ|`.
  have hBc : Bᶜ.card = p - B.card := by
    rw [Finset.card_compl, hcardp]
  have hAleBc : A.card ≤ Bᶜ.card := by omega
  -- Pick `R ⊆ Bᶜ` with `|R| = |A|`.
  obtain ⟨R, hRsub, hRcard⟩ := Finset.exists_subset_card_eq hAleBc
  -- Enumerate `R` and `A` by injections `Fin |A| → ZMod p`.
  set n := A.card with hn
  -- equivalences from `Fin n` onto the (sub)types of `R` and `A`.
  let eR : Fin n ≃ R := (R.equivFinOfCardEq hRcard).symm
  let eA : Fin n ≃ A := (A.equivFinOfCardEq hn.symm).symm
  let ri : Fin n → ZMod p := fun i => ((eR i : R) : ZMod p)
  let ci : Fin n → ZMod p := fun j => ((eA j : A) : ZMod p)
  -- both selections are injective.
  have hri_inj : Function.Injective ri := by
    intro a b hab
    exact eR.injective (Subtype.ext (by simpa [ri] using hab))
  have hci_inj : Function.Injective ci := by
    intro a b hab
    exact eA.injective (Subtype.ext (by simpa [ci] using hab))
  -- `ci j ∈ A` and `ri i ∈ Bᶜ`.
  have hci_mem : ∀ j, ci j ∈ A := fun j => (eA j).2
  have hri_mem : ∀ i, ri i ∈ Bᶜ := fun i => hRsub (eR i).2
  -- the Chebotarev submatrix.
  set M : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.of (fun (i j : Fin n) => (stdAddChar (-(ci j * ri i)) : ℂ)) with hM
  -- the candidate kernel vector `v j = f (ci j)`.
  set v : Fin n → ℂ := fun j => f (ci j) with hv
  -- KEY: `(M *ᵥ v) i = (𝓕 f) (ri i)`, which is `0` since `ri i ∈ Bᶜ`.
  have hkey : M *ᵥ v = 0 := by
    funext i
    -- `(𝓕 f) (ri i) = 0` because `ri i ∉ supp (𝓕 f) = B`.
    have hzero : (𝓕 f) (ri i) = 0 := by
      have : ri i ∉ B := by
        have := hri_mem i
        simpa [Finset.mem_compl] using this
      by_contra hne
      exact this (by simp [hB, supp, Finset.mem_filter, hne])
    -- expand `(M *ᵥ v) i` as `∑ j, M i j * v j`, reindex to `A`, then back to the full `dft`.
    change (∑ j : Fin n, M i j * v j) = (0 : ℂ)
    simp only [hM, hv, Matrix.of_apply]
    -- the goal is now `∑ j, stdAddChar (-(ci j * ri i)) * f (ci j) = 0`.
    -- reindex `Fin n` → `A` via `eA`, getting a sum over `A`; then re-add the zero terms
    -- (off `A`, `f` vanishes) to recover the full `dft` sum.
    have hreidx : (∑ j : Fin n, (stdAddChar (-(ci j * ri i)) : ℂ) * f (ci j))
        = ∑ a ∈ A, (stdAddChar (-(a * ri i)) : ℂ) * f a := by
      rw [← Finset.sum_coe_sort A (fun a => (stdAddChar (-((a : ZMod p) * ri i)) : ℂ) * f a)]
      exact (Equiv.sum_comp eA
        (fun a => (stdAddChar (-((a : ZMod p) * ri i)) : ℂ) * f a))
    rw [hreidx]
    -- the full dft sum over `ZMod p` equals the sum over `A` (terms off `A = supp f` vanish).
    have hfull : (𝓕 f) (ri i)
        = ∑ a ∈ A, (stdAddChar (-(a * ri i)) : ℂ) * f a := by
      rw [dft_apply]
      simp only [smul_eq_mul]
      refine (Finset.sum_subset (Finset.filter_subset _ _) (fun a _ ha => ?_)).symm
      -- `a ∉ A = supp f` means `f a = 0`.
      have : f a = 0 := by
        simpa [hA, supp, Finset.mem_filter] using ha
      rw [this, mul_zero]
    rw [← hfull, hzero]
  -- Chebotarev: `M.det ≠ 0`, so `M *ᵥ v = 0` forces `v = 0`.
  have hdet : M.det ≠ 0 := hCheb n ri ci hri_inj hci_inj
  have hv0 : v = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hkey
  -- `v = 0` means `f` vanishes on `A`; `f` also vanishes off `A` by definition of `supp`.
  -- Conclude `f = 0`, contradicting `hf`.
  apply hf
  funext x
  by_cases hx : x ∈ A
  · -- `x ∈ A`, write `x = ci j` for some `j` and use `v j = 0`.
    obtain ⟨j, hj⟩ : ∃ j, ci j = x := ⟨eA.symm ⟨x, hx⟩, by simp [ci, Equiv.apply_symm_apply]⟩
    have := congrFun hv0 j
    simp only [hv, Pi.zero_apply] at this
    rw [← hj]; simpa using this
  · -- `x ∉ A = supp f` means `f x = 0`.
    have : f x = 0 := by simpa [hA, supp, Finset.mem_filter] using hx
    simpa using this

end ProximityGap.Frontier.TaoFromChebotarev

/-! ## Axiom audit (expected: `propext, Classical.choice, Quot.sound` only — no `sorryAx`).
`ChebotarevMinorNonvanishing` is a `def … : Prop` (a named classical hypothesis), so it carries no
axioms; the PROVEN content below consumes / discharges it. -/
#print axioms ProximityGap.Frontier.TaoFromChebotarev.chebotarev_one
#print axioms ProximityGap.Frontier.TaoFromChebotarev.chebotarev_two
#print axioms ProximityGap.Frontier.TaoFromChebotarev.standardVandermondeNonzeroModP_holds
#print axioms ProximityGap.Frontier.TaoFromChebotarev.chebotarev_equalExponents
#print axioms ProximityGap.Frontier.TaoFromChebotarev.injective_consecutive_cols
#print axioms ProximityGap.Frontier.TaoFromChebotarev.chebotarev_minor_equalExponents
#print axioms ProximityGap.Frontier.TaoFromChebotarev.tao_of_chebotarev
