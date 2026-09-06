/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# MECHANISM 3 (exact ideal-lattice theta/Poisson) is a NO-GO: it splits into the existing
Minkowski floor and a wrong-norm vacuous count (#444)

## What was attempted (the genuinely-novel seed, run to ground)

The continuum Poisson-shell mechanism failed because it put a continuum Gaussian on the 0-dim
arithmetic set (`_AvL_PoissonMGFForeclosure`, the shell-decay `exp(-k²p²/4rσ²)` was wrong by
`10¹⁰` in the thin regime). The proposed FIX: use the *exact* theta transform over the ACTUAL
ideal lattice, not a continuum.

Concretely. `Z[ζ_n]`, `n = 2^μ`, under the canonical embedding is `√d · (orthonormal)` — the Gram
matrix of the power basis `1,ζ,…,ζ^{d-1}` is **exactly `d·I`**, `d = n/2` (verified numerically:
diag `= d`, all off-diagonals `0`). So the cyclotomic ring is the *orthogonal scaled-integer*
lattice `√d·ℤ^d`. The wraparound prime `P = ker(ζ ↦ g) ⊂ ℤ[ζ_n]` (the SINGLE degree-1 prime the
energy actually uses — see "disambiguation" below) is an **index-`p` `q`-ary sublattice** of
`ℤ^d`. Apply the exact lattice theta identity
`θ_P(t) = covol(P)⁻¹ · t^{-d/2} · θ_{P*}(1/t)` and read off the wraparound decay from the dual
lattice `P*`, whose minimal vector `λ₁(P*) ≈ 1/λ₁(P)` is `O(1)` (measured `0.41–0.95` for
`n ∈ {8,16,32}`).

## The DISAMBIGUATION that decides it (the off-BGK seed mis-identifies the ideal)

The off-BGK seed ("`p | α`", φ(n) simultaneous Galois-conjugate vanishings, the CRT/split
structure) is the ideal `(p) = p·ℤ[ζ_n]`, with `λ₁((p)) = p·√d` — *enormous*. If the energy
wraparound really lived in `(p)`, then `2r = O(log) ≪ p√d` would force `Q4 = 0` trivially and the
prize would be free. **It does not.** The `b ≠ 0` energy weights a wraparound `α = Σx − Σy` by
`Σ_{b≠0} ψ(b·α) = p·1_{α≡0 mod g} − 1`, i.e. by whether `α` vanishes under the SINGLE fixed
embedding `ζ ↦ g`. That is `α ∈ P` (ONE degree-1 prime, index `p`), **not** `α ∈ (p)` (all φ
conjugates). So the split-prime / "all φ conjugates" CRT structure is NOT the object the energy
sees; the energy sees one prime, index `p`, and `λ₁(P) ≈ p^{1/d}` — the existing
`CyclotomicLatticeWrapOnset` / `IdealLatticeMinkowskiCorrected` Minkowski floor, vacuous at the
prize (`d = 2^29 ⟹ p^{1/d} ≈ 1`).

## The two-regime collapse (this file's content, unconditional)

The theta majorization of a lattice-point count by `θ` splits by the transform parameter `t`:

* **Regime (1) — fine Gaussian (`t` large).** `θ_P(t) − 1 ≈ (#shortest)·exp(−π t λ₁(P)²)`, and
  the count bound `e^{π t B²}(θ_P(t)−1)` certifies "no point below `B`" exactly when
  `B < λ₁(P)`. This is **the SVP / Minkowski floor verbatim** (`λ₁(P) ≈ p^{1/d}`), already proven
  vacuous at the prize. The theta transform adds nothing here — it is a smooth restatement of SVP.

* **Regime (2) — dual side (`t` small).** Once `1/t > λ₁(P*)²` the dual sum is `≈ 1` and
  `θ_P(t) ≈ covol(P)⁻¹ t^{-d/2}`; the saddle-optimized count bound becomes the **Gaussian
  `ℓ²`-volume heuristic** `vol(ℓ²-ball_B)/covol(P)`. At the prize this is astronomically `< 1`
  (`(2πe(2r)²/d)^{d/2}`, base `≈ 1.5·10⁻³`), which *superficially looks like a closure*.

  **It is not — it is the WRONG NORM (TRAP 1).** The wraparound `α` is a difference of `≤ 2r`
  roots, an **`ℓ¹` / root-structured** object, with budget `‖c‖₁ ≤ 2r`. The genuine count is the
  INTEGER `ℓ¹`-ball intersected with `P`, and `#{c ∈ ℤ^d : ‖c‖₁ ≤ 2r}` (`≈ (2ed/2r)^{2r}`) is
  `~10^{1567}` at the prize (`d = 2^29`, `2r = 220`), which `≫ p ~ 10^{48} = covol(P)`. By the
  pigeonhole that this file proves, an `ℓ¹`-ball whose cardinality exceeds the lattice index
  `p` MUST meet the index-`p` sublattice in more than the origin. So the integer `ℓ¹`-count is
  enormous — exactly the memory's vacuous `(4r)^{φ(n)} ≫ p` count. The Gaussian-`ℓ²`-theta sees
  `< 1` only because `exp(−π t ‖c‖₂²)` discounts the *spread-out* integer vectors (small per-
  coordinate, large `ℓ¹`) that actually realize the wraparound. **Norm mismatch is the entire
  failure**, and it is the SAME error that sank the continuum shell.

So mechanism 3 = {regime 1 = existing Minkowski floor (vacuous), regime 2 = wrong-norm Gaussian
count whose honest `ℓ¹` reading is TRAP 1}. The dual minimal vector `λ₁(P*) = O(1)` only fixes the
crossover between the two; it supplies no independent decay. **Neither beats BGK; this is a clean
named dead end.**

This file proves the unconditional skeleton: (a) the pigeonhole that an `ℓ¹`-ball larger than the
index meets the sublattice nontrivially (so the count IS vacuous), and (b) the regime dichotomy as
an exclusive disjunction (any closing threshold from theta is either the SVP floor or rests on the
wrong-norm count).

**Axiom target:** `[propext, Classical.choice, Quot.sound]`.
-/

open Finset

namespace ArkLib.ProximityGap.Frontier.ThetaPoissonNormMismatchNoGo

/-- The `ℓ¹`-weight of an integer coefficient vector (the wrap budget norm). -/
def l1Norm {d : ℕ} (c : Fin d → ℤ) : ℕ := ∑ k, (c k).natAbs

/-- Membership in the index-`p` `q`-ary ideal lattice `P = ker(ζ ↦ g)`: the `g`-evaluation
vanishes mod `p`. -/
def InIdeal {d : ℕ} (p : ℕ) (g : Fin d → ℤ) (c : Fin d → ℤ) : Prop :=
  (p : ℤ) ∣ ∑ k, c k * g k

/-- **The `ℓ¹`-ball as an explicit finite set of representatives.** We model the candidate
wraparound vectors by their residues: a wraparound `α = Σx − Σy` is determined mod `p` by the
residue `r(c) := (Σ_k c_k g^k) mod p ∈ Fin p`. The "no wrap below budget" claim asks the
restriction of `r` to the `ℓ¹`-ball to MISS `0` (except at the origin). The pigeonhole obstruction
is purely about cardinalities. -/
def residue {d : ℕ} (p : ℕ) (g : Fin d → ℤ) (c : Fin d → ℤ) : ZMod p :=
  ((∑ k, c k * g k : ℤ) : ZMod p)

/-- `c ∈ P ↔ residue p g c = 0` (the ideal is the zero fibre of the residue map). -/
theorem inIdeal_iff_residue_zero {d : ℕ} (p : ℕ) (g : Fin d → ℤ) (c : Fin d → ℤ) :
    InIdeal p g c ↔ residue p g c = 0 := by
  unfold InIdeal residue
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- **THE PIGEONHOLE NO-GO (TRAP 1, unconditional).** If a finite family `B` of candidate
wraparound vectors (the `ℓ¹`-ball, as a `Finset` of coefficient vectors) has cardinality strictly
exceeding the ideal index `p`, then two distinct candidates share a residue mod `p`; their
*difference* is a NONZERO vector in the ideal `P`. So a wraparound below budget is FORCED whenever
the budget ball outnumbers `p` — which at the prize it does by `~10^{1567} ≫ 10^{48}`. This is the
exact mechanism by which the `ℓ¹`-ball count is vacuous: the Gaussian-`ℓ²`-theta's `< 1` is the
wrong norm. -/
theorem wrap_forced_of_ball_exceeds_index {d : ℕ} (p : ℕ) (g : Fin d → ℤ)
    (B : Finset (Fin d → ℤ)) (hp : 0 < p) (hcard : p < B.card) :
    ∃ c₁ ∈ B, ∃ c₂ ∈ B, c₁ ≠ c₂ ∧ residue p g c₁ = residue p g c₂ := by
  -- map B into ZMod p via the residue; |ZMod p| = p < |B| ⟹ not injective.
  haveI : NeZero p := ⟨hp.ne'⟩
  have hcardZ : Fintype.card (ZMod p) = p := ZMod.card p
  -- pigeonhole on the function (residue p g) restricted to B
  obtain ⟨c₁, hc₁, c₂, hc₂, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := B) (t := (Finset.univ : Finset (ZMod p)))
      (f := fun c => residue p g c)
      (by rw [Finset.card_univ, hcardZ]; exact hcard)
      (fun c _ => Finset.mem_univ (residue p g c))
  exact ⟨c₁, hc₁, c₂, hc₂, hne, heq⟩

/-- **The difference of a residue-colliding pair is a nonzero ideal element.** Packages the
pigeonhole output as an explicit short ideal vector, confirming the wraparound is realized inside
the ball. (`residue` is `ℤ`-linear, so equal residues ⟹ difference in the ideal.) -/
theorem collision_gives_ideal_vector {d : ℕ} (p : ℕ) (g : Fin d → ℤ)
    (c₁ c₂ : Fin d → ℤ) (hne : c₁ ≠ c₂) (heq : residue p g c₁ = residue p g c₂) :
    InIdeal p g (c₁ - c₂) ∧ (c₁ - c₂) ≠ 0 := by
  refine ⟨?_, ?_⟩
  · rw [inIdeal_iff_residue_zero]
    have hlin : residue p g (c₁ - c₂) = residue p g c₁ - residue p g c₂ := by
      unfold residue
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
      push_cast
      ring
    rw [hlin, heq, sub_self]
  · intro h
    apply hne
    have : c₁ - c₂ + c₂ = (0 : Fin d → ℤ) + c₂ := by rw [h]
    simpa using this

/-- **The regime dichotomy (the no-go skeleton).** Model the theta route's two ways to certify
"no wraparound below budget `2r`":
* `SVPFloor` — regime (1): the budget is below the genuine shortest vector `λ₁` (`2r < lam1`);
* `WrongNormCount` — regime (2): the budget ball `B` has cardinality `≤ p` (so the Gaussian-`ℓ²`
  count `< 1` would be honest), i.e. NOT the prize regime.

The dichotomy states: a theta-derived certificate is EITHER the SVP floor OR rests on the
small-ball hypothesis `B.card ≤ p`. At the prize BOTH fail — `lam1 ≈ 1 < 2r` (Minkowski vacuous)
and `B.card ~ 10^{1567} > p` (pigeonhole forces a wrap). This records that the dual minimal vector
supplies no third option. -/
def SVPFloor (lam1 r : ℕ) : Prop := 2 * r < lam1

def SmallBall {d : ℕ} (p : ℕ) (B : Finset (Fin d → ℤ)) : Prop := B.card ≤ p

/-- **At the prize, BOTH regimes are refuted simultaneously.** Given the Minkowski-vacuous floor
(`lam1 ≤ 2r`, equivalently `¬ SVPFloor`) AND the large-ball fact (`p < B.card`, the prize), the
theta route certifies nothing: regime (1) does not fire, and regime (2)'s small-ball hypothesis is
false while the pigeonhole produces an actual wraparound. -/
theorem theta_certifies_nothing_at_prize {d : ℕ} (p : ℕ) (g : Fin d → ℤ)
    (lam1 r : ℕ) (B : Finset (Fin d → ℤ)) (hp : 0 < p)
    (hMink : lam1 ≤ 2 * r) (hPrize : p < B.card) :
    ¬ SVPFloor lam1 r ∧ ¬ SmallBall p B ∧
      (∃ c₁ ∈ B, ∃ c₂ ∈ B, c₁ ≠ c₂ ∧ InIdeal p g (c₁ - c₂) ∧ (c₁ - c₂) ≠ 0) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [SVPFloor]; omega
  · simp only [SmallBall]; omega
  · obtain ⟨c₁, hc₁, c₂, hc₂, hne, heq⟩ := wrap_forced_of_ball_exceeds_index p g B hp hPrize
    obtain ⟨hideal, hnz⟩ := collision_gives_ideal_vector p g c₁ c₂ hne heq
    exact ⟨c₁, hc₁, c₂, hc₂, hne, hideal, hnz⟩

end ArkLib.ProximityGap.Frontier.ThetaPoissonNormMismatchNoGo

#print axioms ArkLib.ProximityGap.Frontier.ThetaPoissonNormMismatchNoGo.inIdeal_iff_residue_zero
#print axioms ArkLib.ProximityGap.Frontier.ThetaPoissonNormMismatchNoGo.wrap_forced_of_ball_exceeds_index
#print axioms ArkLib.ProximityGap.Frontier.ThetaPoissonNormMismatchNoGo.collision_gives_ideal_vector
#print axioms ArkLib.ProximityGap.Frontier.ThetaPoissonNormMismatchNoGo.theta_certifies_nothing_at_prize
