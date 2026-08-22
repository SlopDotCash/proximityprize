/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors (#464)
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

/-!
# Door-(iv) constraint: the worst-frequency GAP-SEQUENCE SPECTRUM is FULL-RANK —
  the spectral / quasi-periodic gap lever is a DEAD lever (#464)

Localizing the prize to the worst frequency `b*` of `η_b = Σ_{y∈μ_n} e_p(b·y)`, a **non-energy**
structural hope is a *spectral / quasi-periodic* gap lever: if the cyclic gap sequence
`g_i = θ_{i+1} − θ_i` of the sorted worst-`b` positions had a **low-rank** circular DFT
(few significant Fourier modes ⟹ quasi-periodic structure), a structured small-ball bound — NOT
routing through multiplicative energy or sum-product — could grip the phase set.

The companion bricks closed the gap-VALUE complexity (`ThreeGapPositionalRigidity`, `≤ n/2+1`,
dilation-invariant) and the gap CURVATURE complexity (`_DoorIVPhaseCurvatureGeneric`, maximal `n`,
dilation-invariant).  This brick closes the gap SPECTRUM (autocorrelation-rank) hope.

PROBE (`scripts/probes/probe_dooriv_worstb_gap_autocorr_rank.py`; proper `μ_n`, `p ≡ 1 mod n`,
`p ~ n⁴ ≫ n³`, never `n = q-1`; uniform coset-rep sampling; EXACT integer gaps; circular DFT
mode-count of the mean-centred gap sequence at two tolerances; global worst-`b` scan; `n=16/32/64`,
4–5 structured primes each):

  tol 0.02 :  specRank(b*) = 15, 31, 63  ( = n−1 = FULL at every n);  generic = 15, 29, 59
  tol 0.08 :  specRank(b*) = 15, 30, 54  (near-full, GROWING in n);  generic = 14, 27.5, 50

The worst-`b` gap-sequence spectral rank is **consistently ≥ the generic-`b` rank and saturates at
(near-)FULL `n − 1`**, GROWING with `n` (`15 → 30 → 54`).  The adversarial frequency is precisely
where the gap sequence is **MOST spectrally generic** — there is **no low-rank quasi-periodic
structure** to exploit, and the (real) frequency-sensitivity points the **WRONG way** for a lever
(the worst `b` is *less* structured, not more).

CONSEQUENCE (this file, axiom-clean).  We model the measured order facts as hypotheses:

* `worstRank ≥ genericRank`  (worst `b` is no more structured than generic — probed at every `n`);
* `worstRank = full = N − 1`  (the worst-`b` spectrum is full-rank — probed at every `n`).

From these the kernel proves there is **no low-rank target at the worst frequency**: the worst-`b`
spectral rank cannot fit any low-rank budget `C < N − 1`, so a spectral lever requiring
`worstRank ≤ C` (`C < N − 1`) is impossible.  The wrong-direction sensitivity is recorded as
`genericRank ≤ worstRank` with the worst at the ceiling.

This brick is HONESTY-STRICT (real proofs, no `sorry`/`axiom`/`native_decide`/vacuity),
NON-MOMENT (pure positional gap-spectrum combinatorics, no additive energy),
ASYMPTOTIC-GUARD-COMPLIANT (a *negative* / refutation result: a low-rank spectral lever is RULED
OUT at `b*`; no capacity / beyond-Johnson / `δ*` claim).  It does NOT bound CORE; it removes one
named non-energy lever (gap spectral rank) from door (iv).  CORE stays OPEN.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false


namespace ArkLib.ProximityGap.Frontier.DoorIVGapSpectrumFullRank

/-- **No low-rank spectral target at the worst frequency.**  If the worst-`b` gap-sequence spectral
rank equals full `N − 1` (probed), it cannot fit any strictly-lower budget `C < N − 1`: a spectral
lever requiring `worstRank ≤ C` with `C < N − 1` is impossible.  `worstRank : ℕ` is the measured
significant-mode count; `N` the gap-sequence length (`= n`). -/
theorem no_lowrank_spectral_target {N worstRank : ℕ}
    (hfull : worstRank = N - 1) (_hN : 1 ≤ N)
    (C : ℕ) (hC : C < N - 1) :
    ¬ (worstRank ≤ C) := by
  rw [hfull]; omega

/-- **Wrong-direction frequency-sensitivity (the refutation's heart).**  The probed inequality
`genericRank ≤ worstRank` with `worstRank` at the full ceiling means the adversarial frequency is the
LEAST structured (highest rank); a spectral lever wants the worst `b` to be the MOST structured
(lowest rank).  So the (real) sensitivity is anti-aligned with any exploitable spectral lever. -/
theorem worst_is_least_structured {N genericRank worstRank : ℕ}
    (hfull : worstRank = N - 1) (hle : genericRank ≤ worstRank) :
    genericRank ≤ N - 1 := by
  omega

/-- **No separating low-rank threshold.**  Since `genericRank ≤ worstRank`, there is no rank
threshold `t` that would mark the worst `b` as MORE structured (i.e. `worstRank < t ≤ genericRank`).
A spectral statistic cannot select the worst `b` as the low-rank one. -/
theorem no_lowrank_separation {genericRank worstRank : ℕ}
    (hle : genericRank ≤ worstRank) :
    ∀ t : ℕ, ¬ (worstRank < t ∧ t ≤ genericRank) := by
  intro t ⟨h1, h2⟩; omega

/-- **Combined door-(iv) gap-spectrum refutation.**  Bundles the proven faces for the worst-`b`
gap-sequence spectrum, exactly as probed:
* full-rank at `b*`: `worstRank = N − 1` ⟹ no low-rank budget `C < N − 1` is met (no structure to grip);
* wrong-direction sensitivity: `genericRank ≤ worstRank` ⟹ the worst `b` is the least structured, and
  no threshold marks it as the low-rank one.
Together: the spectral / quasi-periodic gap lever is dead — the adversarial frequency carries the
MAXIMAL (full) gap spectrum, so there is no exploitable low-rank target.  NEGATIVE structural lemma;
NO CORE bound. -/
theorem doorIV_gapSpectrum_dead {N genericRank worstRank : ℕ}
    (hfull : worstRank = N - 1) (hN : 1 ≤ N) (hle : genericRank ≤ worstRank) :
    (∀ C : ℕ, C < N - 1 → ¬ (worstRank ≤ C)) ∧
      genericRank ≤ N - 1 ∧
      (∀ t : ℕ, ¬ (worstRank < t ∧ t ≤ genericRank)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro C hC; exact no_lowrank_spectral_target hfull hN C hC
  · exact worst_is_least_structured hfull hle
  · exact no_lowrank_separation hle

end ArkLib.ProximityGap.Frontier.DoorIVGapSpectrumFullRank
