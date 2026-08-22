/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.PrizeStructuralConstant

/-!
# The restriction / extension `L^q` angle reduces to the moment bridge, and its
# **natural `L^∞` endpoint is DC-blind** (#444/#334)

Angle attacked: *Sárközy/Bourgain restriction (extension) estimate for the multiplicative
subgroup `μ_n`*. The hope: an extension estimate
  `(1/p · ∑_{b ∈ ℤ/p} ‖η_b‖^q)^{1/q} ≤ R(q)`
with `η_b = (1_{μ_n} dσ)^∧(b)` would, at the `q → ∞` endpoint, bound `‖η‖_∞ = house`. Since
`L^∞` is the `q → ∞` endpoint of the restriction inequality, a good restriction exponent for the
multiplicative subgroup looks like a direct house bound.

## Why it reduces (two exact obstructions, both verified by `python3` at `n = 16, 32`)

**(O1) The restriction `L^q` norm IS the additive-energy moment — the same object as the BGK
moment bridge.** Orthogonality of additive characters gives the exact identity
  `∑_{b ∈ ℤ/p} ‖η_b‖^{2r} = p · E_r`,   `E_r = #{x₁+…+x_r = y₁+…+y_r : x_i, y_i ∈ μ_n}`
(verified exactly: `n=16,r=2` gives `47186640 = p·720`, `E_2 = 3n²−3n`). So the even-exponent
restriction norm `(p E_r)^{1/2r}` is precisely the `2r`-th power-sum already used by
`prizeRadiusSq_pow_le_sum` (`_AvBGK_MomentMethodFloor`). The restriction route therefore consumes
the **same** energy bound `E_r ≤ S_r`, and inherits the **same wall**: the bound is tight at the
optimal `r* ≈ log p`, but the char-`0` Wick bound `E_r ≤ (2r−1)‼ nʳ` **fails** there — exactly at
`r = 9` for `n = 32` (verified: `E_9/Wick = 1.27 > 1`), in the wraparound/BGK regime. At `r* ≈ log p`
the bound is `house ≤ √(2 n log p) = √2 · √(n log p)`, the `√2`-EVT factor over the prize.

**(O2) The natural `L^∞` endpoint is the *trivial DC peak*, not house.** The restriction sum runs
over **all** `b ∈ ℤ/p`, including `b = 0`, where `η_0 = |μ_n| = n`. In the prize regime
`house ≈ √(2 n log f) < n` (since `log f ≈ log p ≈ 4 log n ≪ n`), so `n > house` (verified:
`n=16 → η_0 = 16 > house = 13.84`; `n=32 → 32 > 22.98`). Hence
  `lim_{q→∞} (1/p ∑_b ‖η_b‖^q)^{1/q} = max_b ‖η_b‖ = η_0 = n`,
the **trivial** Parseval/`L¹`-`L^∞` peak: the un-subtracted restriction endpoint is blind to house.
To see house at all one must **DC-subtract** (restrict to `b ≠ 0`), at which point the route is
*identical* to the existing moment bridge `prizeRadiusSq_pow_le_sum` and reduces via (O1).

This file records the two elementary inequalities that pin the reduction, both fully proven:
* `dc_le_powerSum` — the DC term `(η_0)^{2r} = n^{2r}` is one summand of the **full** power-sum,
  so the un-subtracted endpoint is `≥ n` (DC-blindness of (O2));
* `prizeRadiusSq_pow_le_dcSubtracted_powerSum` — the **DC-subtracted** restriction power-sum (over
  `b ≠ 0`) dominates `(prizeRadiusSq)^r`, i.e. the only house-relevant restriction estimate is the
  one that has already removed DC, which is the moment bridge (O1).

**Verdict: REDUCES** to the BGK/Wick energy wall at `r ≈ log p`. The restriction angle is *not*
phase-blind (`E_r` uses the additive arithmetic of `μ_n`), but its `L^∞` endpoint is DC-blind, and
its DC-subtracted form is the moment bridge, which stalls at the same Wick-energy crossover the
whole project hits. No new bound on the MAX conjugate; the route collapses to the energy average.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace ArkLib.ProximityGap.Frontier.AvRT

open ArkLib.ProximityGap.PrizeStructuralConstant
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment (eta)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **(O2) DC-blindness of the un-subtracted restriction endpoint.** The `b = 0` (DC) term
`‖η_0‖^{2r}` is one nonnegative summand of the **full** power-sum `∑_{b ∈ univ} ‖η_b‖^{2r}`, hence
is dominated by it. Combined with the exact value `η_0 = ∑_{x ∈ μ_n} ψ(0·x) = |μ_n| = n`, the
`q → ∞` endpoint of the full restriction norm is `≥ n`, which in the prize regime exceeds house —
so the natural restriction `L^∞` endpoint sees only the trivial DC peak, never house. -/
theorem dc_le_powerSum (ψ : AddChar F ℂ) (G : Finset F) (r : ℕ) :
    ‖eta ψ G 0‖ ^ (2 * r) ≤ ∑ b ∈ (Finset.univ : Finset F), ‖eta ψ G b‖ ^ (2 * r) := by
  classical
  refine Finset.single_le_sum (f := fun b => ‖eta ψ G b‖ ^ (2 * r)) ?_ (Finset.mem_univ 0)
  intro b _
  positivity

/-- **(O1)→(O2) The only house-relevant restriction estimate is DC-subtracted, and it equals the
moment bridge.** The worst-case squared period `(prizeRadiusSq)^r` is dominated by the
**DC-subtracted** restriction power-sum `∑_{b ≠ 0} ‖η_b‖^{2r}`. This is verbatim the BGK moment
bridge: the restriction route, once forced to remove the trivial DC peak (O2), consumes the
identical additive-energy moment `∑_{b≠0}‖η_b‖^{2r} = p·E_r − n^{2r}` (O1) and inherits its
`r ≈ log p` Wick wall. No independent control of the MAX is produced. (Proof inlined from the
`PrizeStructuralConstant` substrate: the `sup'` defining `prizeRadiusSq` is attained at some
`b₀ ≠ 0`, whose term is one nonnegative summand of the DC-subtracted power-sum.) -/
theorem prizeRadiusSq_pow_le_dcSubtracted_powerSum
    (ψ : AddChar F ℂ) (G : Finset F) (r : ℕ) :
    (prizeRadiusSq ψ G) ^ r
      ≤ ∑ b ∈ (Finset.univ.erase (0 : F)), ‖eta ψ G b‖ ^ (2 * r) := by
  classical
  obtain ⟨b₀, hb₀mem, hb₀eq⟩ :=
    Finset.exists_mem_eq_sup' (erase_zero_nonempty (F := F)) (fun b => ‖eta ψ G b‖ ^ 2)
  have hpow : (prizeRadiusSq ψ G) ^ r = ‖eta ψ G b₀‖ ^ (2 * r) := by
    unfold prizeRadiusSq
    rw [hb₀eq, ← pow_mul, Nat.mul_comm]
  rw [hpow]
  refine Finset.single_le_sum (f := fun b => ‖eta ψ G b‖ ^ (2 * r)) ?_ hb₀mem
  intro b _
  positivity

/-- **The reduction, packaged.** Sandwiching the two: the *full* restriction power-sum dominates
*both* the trivial DC peak `‖η_0‖^{2r}` (O2: its `L^∞` endpoint is `≥ n > house`) *and* the
house-relevant DC-subtracted bridge term `(prizeRadiusSq)^r` (O1). The restriction angle thus splits
into a trivial DC contribution and the moment bridge; it produces no bound on the MAX beyond the
energy average already available, so it **reduces** to the Wick-energy wall. -/
theorem restriction_splits_dc_and_bridge
    (ψ : AddChar F ℂ) (G : Finset F) (r : ℕ) :
    ‖eta ψ G 0‖ ^ (2 * r) ≤ ∑ b ∈ (Finset.univ : Finset F), ‖eta ψ G b‖ ^ (2 * r)
      ∧ (prizeRadiusSq ψ G) ^ r ≤ ∑ b ∈ (Finset.univ.erase (0 : F)), ‖eta ψ G b‖ ^ (2 * r) :=
  ⟨dc_le_powerSum ψ G r, prizeRadiusSq_pow_le_dcSubtracted_powerSum ψ G r⟩

-- axiom audit
#print axioms dc_le_powerSum
#print axioms prizeRadiusSq_pow_le_dcSubtracted_powerSum
#print axioms restriction_splits_dc_and_bridge

end ArkLib.ProximityGap.Frontier.AvRT
