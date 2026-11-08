/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# SURFACE 5 — Geometry of numbers controls the wrap-around energy `Q4` (#407)

## What this is

The prize per-frequency carrier `B = max_{b≠0}|η_b|` is bracketed through the additive-energy
moment identity `∑_b |η_b|^{2r} = p·E_r(μ_n)` (Plancherel). The energy splits as
`E_r = E_r^{char0} + Q4`, where `E_r^{char0}` is the **finite** char-0 energy (the number of
pairs of `r`-tuples with equal sums in `ℤ[ζ_n]`) and `Q4 ≥ 0` is the **wrap-around excess**.
The Gaussian-Wick value `(2r-1)‼·n^r` is only the leading-order *envelope* of `E_r^{char0}`, not
its exact value: finite corrections are present, e.g. for an even (dyadic) `n` one has
`E_2^{char0} = 3n² − 3n`, not `3n²` (antipodal zero-sum pairs). `Q4` counts pairs of `r`-tuples
`(a, b) ∈ μ_n^r × μ_n^r` whose char-0 difference `α := ∑ζ^{a_i} − ∑ζ^{b_j} ∈ ℤ[ζ_n]` is
**nonzero** as a cyclotomic integer yet **vanishes mod the prize prime** (`α ≡ 0` in `F_p`
under the fixed embedding `ζ ↦ g`, `g` a primitive `n`-th root of unity in `F_p`).

The numerics (`scripts/probes` + memory `arklib-407-*`) show `Q4 = 0` exactly below a
`β`-dependent depth `r*` and turn on past it. SURFACE 5 explains and bounds `r*` by the
**geometry of the cyclotomic ideal lattice**, and pins exactly where it does and does not
help the prize.

## The geometric reframing (this file's content)

Write `n = 2^μ`, so `ℤ[ζ_n]` has the power basis `1, ζ, …, ζ^{d−1}` with `ζ^d = −1`, `d = n/2`.
Every `α` above is a `ℤ`-combination `∑_{k<d} c_k ζ^k` whose coefficient vector `c ∈ ℤ^d` is a
difference of two `r`-fold sums of signed standard basis vectors (each root `ζ^j`, reduced via
`ζ^d = −1`, is `±e_{j mod d}`). Hence **the `ℓ¹`-norm `∑_k |c_k| ≤ 2r`** (the `WrapWeightBudget`).

The embedding-vanishing condition `α ≡ 0 (mod p)` says `c` lies in the **ideal lattice**
`𝔭₀ = ker(c ↦ ∑_k c_k g^k mod p) ⊆ ℤ^d`, an **index-`p`** sublattice of `ℤ^d`
(`det 𝔭₀ = N(𝔭₀) = p`, since `p` splits completely so the chosen prime above `p` has norm `p`).

> **`Q4 = 0` whenever `2r < λ₁^{ℓ¹}(𝔭₀)`** — no `α` of `ℓ¹`-budget `≤ 2r` can be a *nonzero*
> point of `𝔭₀`, so the only zero-mod-`p` differences are the genuinely-zero char-0 ones.

This file proves that *discrete core* unconditionally (no field, no lattice library): see
`wrapExcess_eq_zero_below_minWeight`. The lower bound `λ₁^{ℓ¹}(𝔭₀) ≥ p^{1/d}` is recorded as
the named obligation `MinkowskiL1ShortestVectorBound`. It does **not** come from Minkowski's
convex-body theorem, which goes the other way (it gives the *upper* bound
`λ₁^{ℓ¹}(𝔭₀) ≤ (d!·p)^{1/d}`); the lower bound follows from the arithmetic-norm argument of
`minkowski_of_norm_bound`, under the stated assumptions `p ≤ ∏_j |σ_j(α)|` (ideal-norm
divisibility for the degree-one prime above `p`) and `|σ_j(α)| ≤ l1Norm c` (unit-modulus
embeddings). The numerics (`scripts/probes/surface5_*`) report `λ₁^{ℓ¹}(𝔭₀) ≈ p^{1/d}` and an
onset `r* ≈ ⌈λ₁^{ℓ¹}/2⌉` across `n ∈ {4,8,16}`.

## Where it lands and where it re-collapses (HONEST)

* **It does NOT remove the `Q4` face at the needed depth.** The provable threshold is
  `λ₁^{ℓ¹}(𝔭₀) ≳ p^{1/d} = p^{2/n} = n^{2β/n}` (for `p = n^β`, `d = n/2`). For fixed `β > 0`,
  `n^{2β/n} = exp(2β·ln n / n) → 1`, while the budget at the *needed* depth `r ≈ ln q = β ln n`
  is `2r ≈ 2β ln n → ∞`. So the inequality `2β ln n < n^{2β/n}` is **eventually reversed**: the
  provable onset is `O(1)` and does not reach the logarithmic depth the carrier needs (see the
  honest-scope paragraph of `minkowski_of_norm_bound`). What *is* proved: below any genuine
  `ℓ¹` threshold, `Q4 = 0` and `E_r` equals the finite char-0 energy `E_r^{char0}` exactly
  (which is itself only asymptotic to the Wick envelope `(2r-1)‼·n^r`).
* **It does NOT close the prize either.** Even granting `Q4 = 0` at the needed depth (which this
  file does not establish), `p·E_r = p·E_r^{char0} ≈ p·(2r-1)‼·n^r`, and the `b = 0` term
  alone contributes `η_0^{2r} = n^{2r}` to the left side `∑_b|η_b|^{2r}`. The moment no-go
  (`(p·E_r)^{1/2r} ≥ n`, machine-checked in `_MomentMethodNoGo.lean`) means subtracting the known
  `b=0` term leaves the residual `p·Wick − n^{2r}`, whose `2r`-th root at `r ≈ ln q` is the SAME
  `√(2n ln q)`-vs-`n` gap as BGK / the Paley-graph conjecture. The geometry kills `Q4` but lands
  back on the `b ≠ 0` square-root-cancellation wall (W4/BGK). Verified numerically in
  `scripts/probes/surface5_transfer.py`: `min_r (p·Wick − n^{2r})^{1/2r}` tracks `√(2n ln q)`,
  not the true `B`, leaving the `O(1)`-constant gap open.

**Axiom target:** `[propext, Classical.choice, Quot.sound]`.
-/

open Finset

namespace ArkLib.ProximityGap.CyclotomicLatticeWrapOnset

/-- The `ℓ¹`-norm of an integer coefficient vector `c : Fin d → ℤ`. The wrap-around excess `Q4`
only ever sees difference vectors `α = ∑ c_k ζ^k` arising as a difference of two `r`-fold sums of
roots, so `ℓ¹ c ≤ 2r` (the `WrapWeightBudget`). -/
def l1Norm {d : ℕ} (c : Fin d → ℤ) : ℕ := ∑ k, (c k).natAbs

/-- `l1Norm c = 0 ↔ c = 0`. The `ℓ¹`-norm detects the zero vector. -/
theorem l1Norm_eq_zero_iff {d : ℕ} (c : Fin d → ℤ) : l1Norm c = 0 ↔ c = 0 := by
  unfold l1Norm
  rw [Finset.sum_eq_zero_iff]
  constructor
  · intro h
    funext k
    have := h k (Finset.mem_univ k)
    simpa [Int.natAbs_eq_zero] using this
  · rintro rfl k _
    simp

/-- **The ideal lattice `𝔭₀` as a coefficient predicate.** A coefficient vector `c : Fin d → ℤ`
lies in the ideal above `p` determined by the embedding `ζ ↦ g` exactly when its evaluation
`∑_k c_k g^k` vanishes mod `p`. This is the kernel of an `ℤ`-linear map `ℤ^d → ℤ/p`, hence an
index-`p` (when surjective) sublattice; here we only need the predicate. -/
def InIdeal {d : ℕ} (p : ℕ) (g : Fin d → ℤ) (c : Fin d → ℤ) : Prop :=
  (p : ℤ) ∣ ∑ k, c k * g k

/-- **The `ℓ¹` shortest-vector threshold of the ideal lattice `𝔭₀`.** `L` is a valid lower
threshold if every *nonzero* `c` in the ideal has `ℓ¹`-norm at least `L`. (The geometry-of-
numbers content — that the largest such `L` satisfies `L ≳ p^{1/d}` by Minkowski on the
`ℓ¹`-ball of volume `(2t)^d/d!` against a determinant-`p` lattice — is the named obligation
`MinkowskiL1ShortestVectorBound`; here `L` is an abstract parameter.) -/
def IsL1Threshold {d : ℕ} (p : ℕ) (g : Fin d → ℤ) (L : ℕ) : Prop :=
  ∀ c : Fin d → ℤ, InIdeal p g c → c ≠ 0 → L ≤ l1Norm c

/-- **The discrete core of SURFACE 5 (unconditional).** If `L` is an `ℓ¹` threshold of the ideal
lattice `𝔭₀` and a coefficient vector `c` lies in the ideal with `ℓ¹`-budget strictly below `L`,
then `c = 0`. Equivalently: no *nonzero* cyclotomic integer of `ℓ¹`-weight `< L` can vanish mod
`p`. This is the mechanism behind `Q4 = 0` below the onset depth. -/
theorem ideal_below_threshold_eq_zero {d : ℕ} (p : ℕ) (g : Fin d → ℤ) (L : ℕ)
    (hL : IsL1Threshold p g L) (c : Fin d → ℤ) (hc : InIdeal p g c) (hbudget : l1Norm c < L) :
    c = 0 := by
  by_contra hne
  exact absurd (hL c hc hne) (Nat.not_le.mpr hbudget)

/-- **`Q4 = 0` below the onset depth (the headline).** Model the wrap-excess witnesses at depth
`r` as the set of nonzero difference vectors `c` that (i) lie in the ideal `𝔭₀` and (ii) respect
the wrap weight budget `l1Norm c ≤ 2r`. If `2r < L` for an `ℓ¹` threshold `L` of `𝔭₀`, this
witness set is **empty** — the only zero-mod-`p` differences are char-0-zero, so `Q4 = 0`.

This is the clean, field-free statement of: for `r < (1/2)·λ₁^{ℓ¹}(𝔭₀)`, the mod-`p` energy
equals the finite char-0 energy `E_r^{char0}` exactly (not the Gaussian-Wick envelope
`(2r-1)‼·n^r`, which is only its leading-order asymptotic). -/
theorem wrapExcess_eq_zero_below_minWeight {d : ℕ} (p : ℕ) (g : Fin d → ℤ) (L r : ℕ)
    (hL : IsL1Threshold p g L) (hr : 2 * r < L) :
    {c : Fin d → ℤ | InIdeal p g c ∧ l1Norm c ≤ 2 * r ∧ c ≠ 0} = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro c ⟨hc, hbudget, hne⟩
  exact hne (ideal_below_threshold_eq_zero p g L hL c hc (lt_of_le_of_lt hbudget hr))

/-- **The `ℓ¹` lower-bound input (named obligation, NOT proven here).** The claim that the
cyclotomic ideal lattice `𝔭₀` above a split prime `p` — index `p` in `ℤ^d`, `d = n/2` — has `ℓ¹`
shortest vector `λ₁^{ℓ¹}(𝔭₀) = L` with `L^d ≥ p` (so `L ≥ p^{1/d}`).

Minkowski's convex-body theorem gives only the opposite, *upper* bound: the symmetric convex
`ℓ¹`-ball of radius `t` has volume `(2t)^d / d!`; when this exceeds `2^d · det(𝔭₀) = 2^d · p` it
contains a nonzero lattice point, so `λ₁^{ℓ¹} ≤ (d!·p)^{1/d} ≈ d·p^{1/d}`. Mathlib's
`ZLattice` / Minkowski API therefore does not discharge this predicate. The *lower* bound is
instead supplied, conditionally, by the arithmetic-norm argument `minkowski_of_norm_bound`, whose
two assumptions (`p ≤ ∏_j |σ_j(α)|` and `|σ_j(α)| ≤ l1Norm c`) remain explicit. The numerics
report `λ₁^{ℓ¹}(𝔭₀) ≈ p^{1/d}` and onset `r* ≈ ⌈λ₁^{ℓ¹}/2⌉`. Stated as a `Prop`-valued
predicate; it is not needed for the discrete core above. -/
def MinkowskiL1ShortestVectorBound (d p L : ℕ) : Prop :=
  -- `L = λ₁^{ℓ¹}(𝔭₀)` satisfies the volume lower reach `L^d ≥ p` (so `L ≥ p^{1/d}`).
  p ≤ L ^ d

/-- **The transfer gap, stated honestly.** The needed depth is `r ≈ ln q = β·ln n`; the provable
onset depth is `r* ≈ (1/2)·L ≈ (1/2)·p^{1/d} = (1/2)·n^{2β/n}`. So this route gives `Q4 = 0` at the
needed depth only if `2·(β ln n) < n^{2β/n}`. For fixed `β > 0` this **fails for all large `n`**:
`n^{2β/n} = exp(2β ln n / n) → 1` while `2β ln n → ∞`. This predicate packages "the geometry
covers the needed depth" as the inequality a caller must check in each instance; it is not
asserted asymptotically here, and it does NOT assert the prize (the residual is the `b≠0` BGK
gap, see file docstring). -/
def GeometryCoversNeededDepth (needed onset : ℕ) : Prop := needed < onset

/-- The geometry covers the needed depth precisely when the no-wrap onset `(L is the ℓ¹ shortest
vector, onset = L/2 in `2r`-budget terms) clears the needed depth. Trivial unfolding lemma that
ties the named obligations together for the consumer chain. -/
theorem coversNeededDepth_of_threshold {d p L needed : ℕ}
    (hgeo : MinkowskiL1ShortestVectorBound d p L) (hclear : 2 * needed < L) :
    GeometryCoversNeededDepth needed (L) := by
  unfold GeometryCoversNeededDepth
  omega


/-- **The arithmetic-norm core of the Minkowski obligation (the AM-GM step) — DISCHARGES it modulo two
standard number-theory facts.** If `α` is a nonzero element of the degree-1 prime `𝔭 ∣ p`, its norm is
a nonzero integer divisible by `N(𝔭)=p`, so `p ≤ |N(α)| = ∏_j |σ_j(α)|`, while each embedding has
`|σ_j(α)| ≤ l1Norm c` (unit-modulus generators). Abstracting `a j := |σ_j(α)|`, `L := l1Norm c`:
`d` terms each `≤ L` with product `≥ p` force `p ≤ L^d` = `MinkowskiL1ShortestVectorBound d p L`. Reduces
the obligation to `p ≤ ∏ a_j` (ideal-norm divisibility) + `a_j ≤ L` (unit-modulus embeddings).

HONEST SCOPE (corrects the synthesis over-claim): the provable threshold is `L = ⌈p^{1/d}⌉`, `d=n/2`, so
onset `r* ~ ½p^{1/d}`. As `p = n^β`, `p^{1/d} = n^{2β/n} → 1`, the provable onset is `O(1)`, NOT `≫ ln q`
— the LOOSE side. The true onset `r* ~ β` needs the deeper cyclotomic minimal-weight (Mann/Lam–Leung).
Completes the conditional norm-route lower bound for the Surface-5 threshold (with the two
arithmetic-norm assumptions explicit); it does NOT close the wrap-around face at the needed depth
and does NOT cover the prize depth. -/
theorem minkowski_of_norm_bound {d : ℕ} (p L : ℕ) (a : Fin d → ℕ)
    (hbound : ∀ j, a j ≤ L) (hnorm : p ≤ ∏ j, a j) : p ≤ L ^ d := by
  calc p ≤ ∏ j, a j := hnorm
    _ ≤ ∏ _j : Fin d, L := Finset.prod_le_prod' (fun j _ => hbound j)
    _ = L ^ d := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end ArkLib.ProximityGap.CyclotomicLatticeWrapOnset

#print axioms ArkLib.ProximityGap.CyclotomicLatticeWrapOnset.l1Norm_eq_zero_iff
#print axioms ArkLib.ProximityGap.CyclotomicLatticeWrapOnset.ideal_below_threshold_eq_zero
#print axioms ArkLib.ProximityGap.CyclotomicLatticeWrapOnset.wrapExcess_eq_zero_below_minWeight
#print axioms ArkLib.ProximityGap.CyclotomicLatticeWrapOnset.coversNeededDepth_of_threshold
#print axioms ArkLib.ProximityGap.CyclotomicLatticeWrapOnset.minkowski_of_norm_bound
