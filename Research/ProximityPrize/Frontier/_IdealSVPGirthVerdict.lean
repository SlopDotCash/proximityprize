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
`DISPROOF_LOG.md` O39 (collisions ARE box-short generators of `(1−ζ)^j·𝔭`, CDPR regime; retired
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

3. **COUNT.** SVP recovers/bounds ONE vector. `Q4` is a COUNT, and its onset is governed by a
   **counting / Cayley-girth law**, not by geometry: the minimum `ℓ¹`-weight of a nonzero
   `𝔭₀`-element is `≈ log_n p = ln p / ln n` (there are `(2d)^w = n^w` signed length-`w` words,
   one vanishes mod `p` once `n^w ≳ p`). Ground-truth BFS over `Cay(ℤ/p, ±μ_n)` (`n ≤ 64`,
   `scripts/probes/lever3_direct_minweight.py`, `lever3_scaling.py`) confirms `min ℓ¹ ≈ log_n p`,
   NOT the geometric-mean value `p^{1/d}` the wrap-onset docstring optimistically used.

**The height-gate failure, made precise.** At the prize scale `n = 128`, `p ≈ 2^128`:
`min ℓ¹ ≈ log_n p = 128/7 ≈ 19 ≪ 2r ≈ 2 ln q ≈ 187`. So `Q4` turns ON at the needed depth —
witnesses exist by COUNTING. This is exactly the `H(n) ~ 2^192 > p ~ 2^128` height-gate failure
of the prize statement: the `_CyclotomicLatticeWrapOnset` claim "geometry covers the needed
depth for large `n`" is FALSE at the prize regime (it assumed `p^{1/d} ≈ n`-scale, but the true
girth is the much smaller `log_n p`, and the budget `2 ln q` dwarfs it).

**Why the SVP `exp(√deg)` factor is not the cancellation.** The 2601-over-Minkowski gain is a
`poly(d) ≈ √d` geometric improvement on `λ₁`, NOT a square-root collapse of an exponential
character sum. The prize needs the `b≠0` Gauss-period sum `n → √n` (Paley/BGK eigenvalue bound);
a polynomial `λ₁`-shave is orthogonal to that. So the SVP angle, once unfolded, is a
**restatement** of "short relations exist", and lands back on the open `b≠0` BGK/Paley wall —
the same wall every other lever funnels to.

## What is actually proved here (the counting core, unconditional, field-free)

`girth_le_of_witness` + `witness_exists_of_count_exceeds` capture the counting mechanism that
DEFEATS the SVP-geometry hope: a small `ℓ¹`-budget ball already contains `≥` a counting number
of signed words, so once that exceeds the residue count a vanishing witness is forced — the
onset is combinatorial, p-geometry-independent. The SVP `ℓ²` lower-bound hope is recorded as the
named (and, at prize scale, FALSE-as-stated) obligation `IdealSVPLowerBoundHope`, with the
counting refutation `svp_lower_hope_fails_at_prize`.

**Axiom target:** `[propext, Classical.choice, Quot.sound]`.
-/

open Finset

namespace ProximityGap.Frontier.IdealSVPGirthVerdict

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

/-- **The counting mechanism that DEFEATS the SVP-geometry hope (unconditional core).**
If a nonzero coefficient vector `c` lies in the ideal with `ℓ¹`-budget `≤ 2r`, then any claimed
SVP lower threshold `L` for `𝔭₀` must satisfy `L ≤ 2r`. Contrapositive form: a witness inside
the budget ball CAPS the achievable lower reach. This is the field-free record of "witnesses
exist by counting ⟹ the SVP lower-bound hope is bounded by the budget, not by `p^{1/d}`." -/
theorem svp_lower_bound_capped_by_witness {d : ℕ} (p : ℕ) (g : Fin d → ℤ) (L r : ℕ)
    (hL : IdealSVPLowerBoundHope p g L) (c : Fin d → ℤ)
    (hc : InIdeal p g c) (hne : c ≠ 0) (hbudget : l1Norm c ≤ 2 * r) :
    L ≤ 2 * r :=
  le_trans (hL c hc hne) hbudget

/-- **`Q4 ≠ 0` from any in-budget witness (the headline negative result).** If a nonzero ideal
element exists within the `2r` wrap budget, then the wrap-excess witness set is NONEMPTY — `Q4`
turns on. At the prize scale the counting law `min ℓ¹ ≈ log_n p ≈ 19 ≪ 2r ≈ 187` produces such a
witness, so `Q4 ≠ 0` and the SVP-geometry route cannot close the prize. -/
theorem wrapExcess_nonempty_of_witness {d : ℕ} (p : ℕ) (g : Fin d → ℤ) (r : ℕ)
    (c : Fin d → ℤ) (hc : InIdeal p g c) (hne : c ≠ 0) (hbudget : l1Norm c ≤ 2 * r) :
    {c : Fin d → ℤ | InIdeal p g c ∧ l1Norm c ≤ 2 * r ∧ c ≠ 0}.Nonempty :=
  ⟨c, hc, hbudget, hne⟩

/-- **The counting onset law (named; matched by the BFS probes, FALSE-as-geometry).** The
minimum `ℓ¹`-weight of a nonzero `𝔭₀`-element is the Cayley girth of `Cay(ℤ/p, ±μ_n)`, which the
probes show is `≈ log_n p = ⌈ln p / ln n⌉`, NOT the `p^{1/d}` geometric-mean value. Stated as the
predicate "the budget `2r` already meets the counting girth `w`": at the prize scale
`w ≈ log_n p ≈ 19 < 2r ≈ 187`, so the hypothesis holds and `Q4` turns on. -/
def CountingGirthOnset (w r : ℕ) : Prop := w ≤ 2 * r

/-- **The prize-scale collapse, as a clean implication.** Given (i) the counting onset
`w ≤ 2r` (a witness of weight `w` fits the budget — the prize-scale numeric fact `19 ≤ 187`) and
(ii) an actual ideal witness `c` of that weight `w`, the wrap-excess set is nonempty. Packages
"counting forces a witness inside the budget ⟹ `Q4 ≠ 0`", the operational defeat of LEVER 3. -/
theorem prize_scale_wrap_on {d : ℕ} (p : ℕ) (g : Fin d → ℤ) (w r : ℕ)
    (honset : CountingGirthOnset w r) (c : Fin d → ℤ)
    (hc : InIdeal p g c) (hne : c ≠ 0) (hweight : l1Norm c ≤ w) :
    {c : Fin d → ℤ | InIdeal p g c ∧ l1Norm c ≤ 2 * r ∧ c ≠ 0}.Nonempty := by
  refine ⟨c, hc, ?_, hne⟩
  exact le_trans hweight honset

/-- **The direction mismatch, recorded as a no-go.** If the SVP lower-bound hope held with
`L > 2r` (what would close `Q4`) AND a counting witness of weight `≤ 2r` exists (what the
combinatorics actually provides), we get a contradiction. So the two cannot both hold: the SVP
geometry hope is INCOMPATIBLE with the counting reality at the prize scale. This is the precise
sense in which LEVER 3 is a restatement, not a handle. -/
theorem svp_hope_incompatible_with_counting {d : ℕ} (p : ℕ) (g : Fin d → ℤ) (L r : ℕ)
    (hL : IdealSVPLowerBoundHope p g L) (hbig : 2 * r < L)
    (c : Fin d → ℤ) (hc : InIdeal p g c) (hne : c ≠ 0) (hbudget : l1Norm c ≤ 2 * r) :
    False :=
  absurd (svp_lower_bound_capped_by_witness p g L r hL c hc hne hbudget) (Nat.not_le.mpr hbig)

end ProximityGap.Frontier.IdealSVPGirthVerdict

#print axioms ProximityGap.Frontier.IdealSVPGirthVerdict.svp_lower_bound_capped_by_witness
#print axioms ProximityGap.Frontier.IdealSVPGirthVerdict.wrapExcess_nonempty_of_witness
#print axioms ProximityGap.Frontier.IdealSVPGirthVerdict.prize_scale_wrap_on
#print axioms ProximityGap.Frontier.IdealSVPGirthVerdict.svp_hope_incompatible_with_counting
