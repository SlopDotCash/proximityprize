/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# LEVER 3 — Ring-LWE / ideal-SVP is the WRONG direction & norm for the cross-surplus (#407)

## What this is (HONEST verdict, not a closure)

The prize cross-surplus `Q4` counts nonzero cyclotomic integers `α = ∑_{k<d} c_k ζ^k`
(`d = n/2`, `ζ^d = −1`, `n = 2^μ`) of `ℓ¹`-budget `‖c‖₁ ≤ 2r` that vanish mod the prize prime
`p` (i.e. `c` lies in the degree-1 prime ideal `𝔭₀ ⊂ ℤ^d`, norm `p`). `Q4 = 0` iff the *minimum*
`ℓ¹`-weight of a nonzero ideal element exceeds the budget `2r`.

LEVER 3 asks whether the **Ring-LWE / ideal-SVP cryptanalysis machinery** for `2`-power
cyclotomic fields — CDPR (recover short generators via the log-unit lattice, [Cramer–Ducas–
Peikert–Regev EUROCRYPT'16]), Biasse–Song (quantum poly-time mildly-short vectors, factor
`exp(Õ(√deg))`, [JACM 2021]), and the 2026 power-of-two bound `λ₁ ≤ (2·d²·p)^{1/4}`
([arXiv 2601.07511]) — gives a sharp handle on this count. The closest prior in-tree contact is
`Research/ProximityPrize/DISPROOF_LOG.md` O39 (collisions ARE box-short generators of `(1−ζ)^j·𝔭`, CDPR regime; retired
for the lower half) and `_CyclotomicLatticeWrapOnset.lean` (the Minkowski-`ℓ¹` onset).

## The verdict: a THREE-fold mismatch (restatement, not a handle). HONEST: re-collapses to BGK.

The ideal-SVP machinery is structurally the wrong tool, for three independent reasons:

1. **DIRECTION.** Every SVP result is an *upper* bound on `λ₁` (a short vector EXISTS / is
   recoverable). To force `Q4 = 0` you need a *lower* bound on `λ₁` (NO short vector). The
   machinery therefore certifies the OPPOSITE of what the prize needs: it says witnesses exist.

2. **NORM.** SVP controls the `ℓ²` / canonical-embedding norm; the wrap budget is the `ℓ¹`
   coefficient weight. For a power-of-two cyclotomic the canonical embedding is an exact scalar
   `√d` of the coefficient `ℓ²`, so `ℓ¹ ≤ √d·ℓ²` and the SVP `ℓ²` upper bound `(2d²p)^{1/4}`
   converts to an `ℓ¹` *upper* bound `√d·(2d²p)^{1/4} ≈ 10^{12}` at `n = 128` — useless as a
   witness-existence certificate against the `2r ≈ 187` budget (verified
   `scripts/probes/lever3_verdict.py`).

3. **COUNT.** SVP recovers/bounds ONE vector. `Q4` is a COUNT. The small-`n` probes suggest
   (HEURISTIC, not proved) that its onset follows an empirical Cayley-girth trend: BFS over
   `Cay(ℤ/p, ±μ_n)` (`n ≤ 64`, `scripts/probes/lever3_direct_minweight.py`,
   `lever3_scaling.py`) found minimum `ℓ¹`-weights close to `log_n p`, well below the
   geometric-mean value `p^{1/d}` the wrap-onset docstring used.
   **The naive counting justification for that trend is NOT valid.** Counting the `(2d)^w = n^w`
   *ordered* signed length-`w` words does not count distinct coefficient vectors: reordering a
   word gives the same vector and backtracking gives smaller (possibly zero) vectors, so
   `n^w > p` does not force a nonzero ideal element of weight `≤ w`. The correct pigeonhole
   counts lattice points: the `ℓ¹` ball of radius `w` in `ℤ^d` has
   `B_d(w) = ∑_j 2^j·C(d,j)·C(w,j)` points, and `B_d(w) > p` forces a nonzero ideal element of
   weight `≤ 2w` (a difference of two points with the same residue).

**What the counting does and does not give at the prize scale** (`n = 128`, `d = 64`,
`p ≈ 2^128`; exact integer counts, checked in the 2026-10-28 audit, not in Lean).
`B_64(19) ≈ 1.18·10^23 < 2^77`, far below `p`, so the ordered-word figure `log_n p ≈ 19` is
**not** certified by any counting argument. The first radius with `B_64(w) > 2^128` is `w = 43`,
so ordinary pigeonhole gives a nonzero ideal element of `ℓ¹`-weight `≤ 86` (for `p < B_64(43)`).
That bound still lies below the module's quoted budget `2r ≈ 2 ln q ≈ 187`, so the qualitative
conclusion "short ideal elements exist inside the budget, the SVP lower-bound hope cannot hold
at that depth" is supported by the corrected count — with weight `≤ 86`, not `≈ 19`. Neither the
ball-count bound nor its cyclotomic/prize instantiation is formalized here; this does not prove
that no weight-`19` relation exists, only that the stated certificate does not establish one.
The comparison with the `H(n) ~ 2^192 > p ~ 2^128` height-gate failure and with the
`_CyclotomicLatticeWrapOnset` heuristic (which assumed a `p^{1/d}`-scale girth) is
interpretive, not a machine-checked statement.

**Why the SVP `exp(√deg)` factor is not the cancellation.** The 2601-over-Minkowski gain is a
`poly(d) ≈ √d` geometric improvement on `λ₁`, NOT a square-root collapse of an exponential
character sum. The prize needs the `b≠0` Gauss-period sum `n → √n` (Paley/BGK eigenvalue bound);
a polynomial `λ₁`-shave is orthogonal to that. So the SVP angle, once unfolded, is a
**restatement** of "short relations exist", and lands back on the open `b≠0` BGK/Paley wall —
the same wall every other lever funnels to.

## What is actually proved here (witness-conditional, field-free)

Every theorem below takes the desired ideal witness `c` (nonzero, in `𝔭₀`, within the budget)
as an **explicit premise** and derives a valid consequence; no theorem here proves that such a
witness exists, and no counting lemma is formalized:

* `svp_lower_bound_capped_by_witness` — a witness of weight `≤ 2r` caps any lower reach `L`
  satisfying `IdealSVPLowerBoundHope` at `2r`;
* `wrapExcess_nonempty_of_witness`, `prize_scale_wrap_on` — such a witness makes the
  wrap-excess set nonempty;
* `svp_hope_incompatible_with_counting` — `IdealSVPLowerBoundHope` with `L > 2r` contradicts
  the existence of such a witness.

The SVP lower-bound hope is recorded as the named obligation `IdealSVPLowerBoundHope`. Its
failure at the prize scale is supported only by the informal (corrected) pigeonhole count
above, not by a checked theorem. (Earlier versions of this docstring cited declarations
`girth_le_of_witness`, `witness_exists_of_count_exceeds`, and `svp_lower_hope_fails_at_prize`;
none of them exists.)

**Axiom target:** `[propext, Classical.choice, Quot.sound]`.
-/

open Finset

namespace ArkLib.ProximityGap.IdealSVPGirthVerdict

/-- `ℓ¹`-weight of an integer coefficient vector (the wrap budget norm). -/
def l1Norm {d : ℕ} (c : Fin d → ℤ) : ℕ := ∑ k, (c k).natAbs

/-- The degree-1 prime ideal `𝔭₀` above `p` (embedding `ζ ↦ g`), as a coefficient predicate:
`∑_k c_k g^k ≡ 0 (mod p)`. (Same object as `_CyclotomicLatticeWrapOnset.InIdeal`.) -/
def InIdeal {d : ℕ} (p : ℕ) (g : Fin d → ℤ) (c : Fin d → ℤ) : Prop :=
  (p : ℤ) ∣ ∑ k, c k * g k

/-- **The ideal-SVP LOWER-bound hope (named obligation; the SVP machinery does NOT supply it).**
A geometric lower reach `L` on the SHORTEST `ℓ¹` vector of `𝔭₀`: every nonzero ideal element has
`ℓ¹`-weight `≥ L`. To force `Q4 = 0` one needs `L > 2r`. CDPR / Biasse–Song / [2601.07511] all
deliver the OPPOSITE inequality (an `ℓ²` *upper* bound on `λ₁`), so this hope is exactly the
content the SVP angle fails to provide. (Identical shape to `_CyclotomicLatticeWrapOnset`'s
`IsL1Threshold`; isolated here to name the direction mismatch.) -/
def IdealSVPLowerBoundHope {d : ℕ} (p : ℕ) (g : Fin d → ℤ) (L : ℕ) : Prop :=
  ∀ c : Fin d → ℤ, InIdeal p g c → c ≠ 0 → L ≤ l1Norm c

/-- **A witness caps the SVP lower reach (witness-conditional).**
If a nonzero coefficient vector `c` lies in the ideal with `ℓ¹`-budget `≤ 2r`, then any claimed
SVP lower threshold `L` for `𝔭₀` must satisfy `L ≤ 2r`. Contrapositive form: a witness inside
the budget ball CAPS the achievable lower reach. The witness is a premise; its existence is not
proved here. -/
theorem svp_lower_bound_capped_by_witness {d : ℕ} (p : ℕ) (g : Fin d → ℤ) (L r : ℕ)
    (hL : IdealSVPLowerBoundHope p g L) (c : Fin d → ℤ)
    (hc : InIdeal p g c) (hne : c ≠ 0) (hbudget : l1Norm c ≤ 2 * r) :
    L ≤ 2 * r :=
  le_trans (hL c hc hne) hbudget

/-- **`Q4 ≠ 0` from any in-budget witness (the headline negative result).** If a nonzero ideal
element exists within the `2r` wrap budget, then the wrap-excess witness set is NONEMPTY — `Q4`
turns on. The witness is a premise: the heuristic girth `≈ log_n p ≈ 19` is not certified by any
counting argument (see the module docstring; a correct lattice-point pigeonhole gives weight
`≤ 86` at the prize scale, informally and outside Lean). -/
theorem wrapExcess_nonempty_of_witness {d : ℕ} (p : ℕ) (g : Fin d → ℤ) (r : ℕ)
    (c : Fin d → ℤ) (hc : InIdeal p g c) (hne : c ≠ 0) (hbudget : l1Norm c ≤ 2 * r) :
    {c : Fin d → ℤ | InIdeal p g c ∧ l1Norm c ≤ 2 * r ∧ c ≠ 0}.Nonempty :=
  ⟨c, hc, hbudget, hne⟩

/-- **The onset predicate (a bare numeric comparison).** `CountingGirthOnset w r` is just
`w ≤ 2r`: "a weight-`w` witness would fit the budget `2r`". It says nothing about whether a
weight-`w` ideal element exists. The minimum `ℓ¹`-weight of a nonzero `𝔭₀`-element is the
Cayley girth of `Cay(ℤ/p, ±μ_n)`; the small-`n` probes empirically put it near `log_n p`, but
that is a heuristic trend, not a theorem, and the ordered-word count `n^w > p` does not certify
it (see the module docstring). -/
def CountingGirthOnset (w r : ℕ) : Prop := w ≤ 2 * r

/-- **Witness-conditional wrap onset.** Given (i) the numeric comparison `w ≤ 2r` and (ii) an
actual nonzero ideal witness `c` of weight `≤ w` (an explicit premise — no counting lemma here
produces it), the wrap-excess set is nonempty. -/
theorem prize_scale_wrap_on {d : ℕ} (p : ℕ) (g : Fin d → ℤ) (w r : ℕ)
    (honset : CountingGirthOnset w r) (c : Fin d → ℤ)
    (hc : InIdeal p g c) (hne : c ≠ 0) (hweight : l1Norm c ≤ w) :
    {c : Fin d → ℤ | InIdeal p g c ∧ l1Norm c ≤ 2 * r ∧ c ≠ 0}.Nonempty := by
  refine ⟨c, hc, ?_, hne⟩
  exact le_trans hweight honset

/-- **The direction mismatch, recorded as a no-go.** If the SVP lower-bound hope held with
`L > 2r` (what would close `Q4`) AND a nonzero ideal witness of weight `≤ 2r` exists, we get a
contradiction. So the two cannot both hold. Whether such a witness exists at the prize scale is
not proved here (the informal lattice-point pigeonhole in the module docstring suggests one of
weight `≤ 86` does). -/
theorem svp_hope_incompatible_with_counting {d : ℕ} (p : ℕ) (g : Fin d → ℤ) (L r : ℕ)
    (hL : IdealSVPLowerBoundHope p g L) (hbig : 2 * r < L)
    (c : Fin d → ℤ) (hc : InIdeal p g c) (hne : c ≠ 0) (hbudget : l1Norm c ≤ 2 * r) :
    False :=
  absurd (svp_lower_bound_capped_by_witness p g L r hL c hc hne hbudget) (Nat.not_le.mpr hbig)

end ArkLib.ProximityGap.IdealSVPGirthVerdict

#print axioms ArkLib.ProximityGap.IdealSVPGirthVerdict.svp_lower_bound_capped_by_witness
#print axioms ArkLib.ProximityGap.IdealSVPGirthVerdict.wrapExcess_nonempty_of_witness
#print axioms ArkLib.ProximityGap.IdealSVPGirthVerdict.prize_scale_wrap_on
#print axioms ArkLib.ProximityGap.IdealSVPGirthVerdict.svp_hope_incompatible_with_counting
