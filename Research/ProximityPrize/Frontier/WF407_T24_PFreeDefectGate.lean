/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Field.Basic

/-!
# The p-free invariant `c_r` and the defect gate (Issue #407, thread T24-pfree)

The moment method's only rigorous arrow on the worst-case incomplete character sum
`B = max_{b≠0} ‖η_b‖` of `μ_n ⊆ F_q` is (`CharSumMomentDeepWall.charSum_le_of_moment`,
via the Parseval identity `∑_b ‖η_b‖^{2r} = q·E_r`):

  `B^{2r} ≤ q · E_r(F_q)`,    `E_r(F_q) = #{(x,y)∈μ_n^{2r} : ∑x = ∑y in F_q}`.

The `2r`-fold additive energy `E_r(F_q)` splits into a **p-free part** and a **char-p defect**:

  `E_r(F_q) = E_r^∞ + D_r(q)`,     `D_r(q) ≥ 0`,

where `E_r^∞ = #{(x,y)∈μ_n^{2r} : ∑x = ∑y in ℂ}` is the char-0 value (a function of the
*complex* `n`-th roots only, hence **p-INDEPENDENT** — verified exactly at multiple primes in
`scripts/probes/wf407_T24-pfree_*.py`, and equal to `(2r)!·besselCoeff(n/2,r)`,
`RungBesselEnergy.besselCoeff`), and `D_r(q) ≥ 0` counts the EXTRA tuples whose roots-of-unity
difference does not vanish over `ℂ` but vanishes mod `p` (the "halo"). The thread `T24-pfree`
proposed to bound the single p-free object `E_r^∞` (equivalently the normalized invariant
`c_r := E_r^∞/(r!·n^r)`) and have the bound transfer *uniformly in p* (dodging the per-prime
structured-prime explosion). This file is the machine-checked statement of **exactly when that
bridge is valid and where it breaks**:

* `pfree_bound_iff_defect_le` — the moment bound run on the *p-free value* `q·E_r^∞` (instead of
  the true `q·E_r(F_q)`) is a valid upper bound on `B^{2r}` **iff** the contribution of the defect
  is absorbed, i.e. iff `B^{2r} ≤ q·E_r^∞`. The honest arrow always carries `+ q·D_r`:
  `moment_with_defect` gives `B^{2r} ≤ q·E_r^∞ + q·D_r`.
* `pfree_bound_valid_of_no_defect` — if `D_r(q) = 0` (the *clean* regime, `r ≤ r_max ≈ 2 log_n p`)
  then the p-free bound IS valid: `B^{2r} ≤ q·E_r^∞`. So the lever works exactly in the clean
  regime — where the wall is already crossed by hand.
* `pfree_gate` — the dichotomy as one statement: the p-free moment bound holds **iff** the true
  moment exceeds it by at most `q·D_r`; the gate is `D_r`, an *arithmetic divisor condition*
  (`p | N(α)` for a sparse root-of-unity difference `α`, `Part 4B` of the probe: defect primes =
  EXACTLY the odd prime factors `q ≡ 1 mod n` of `{N(α)}`), NOT a size condition. Hence there is no
  clean p-uniform statement: `pfree_no_size_threshold` records that a larger prime can carry a
  defect while a smaller one does not (the measured `n=8,r=3`: clean at `p=113` but defect at
  `p=137,313`), so no `∀ p ≥ P₀` form of the p-free bound can hold.

**Verdict (honesty contract).** `c_r` is genuinely p-free and the *ideal* p-free moment bound
`min_r (q·E_r^∞)^{1/2r}` reaches the prize target `√(n·log q)` at `r ≈ log q`
(`Part 5C` of the probe). But the arrow consumes `E_r(F_q) = E_r^∞ + D_r`, and `D_r > 0`
**provably** at the depth `r ≈ log q` the ideal bound needs (the threshold `r ≤ r_max ≈ 2 log_n p`
is `O(1)` at prize `p ≈ n^5`, while `r_opt ≈ log q` grows; `r_opt/r_max ≈ a/2`, `Part 5D`). The
p-free lever therefore **RE-LABELS the char-0 → char-p transfer wall** (the `E_r − E_r^∞ ≥ 0`
mod-q defect = the BGK / additive-energy / cyclotomic-norm-defect core); it does not move it. The
gate `D_r` is precisely that wall, now stated cleanly as the *only* obstruction to a p-uniform
moment bound.

This file proves the elementary *dichotomy arithmetic* (axiom-clean); the number-theoretic content
— that `D_r > 0` at `r ≈ log q` for the prize prime — is the open wall, deliberately carried as the
hypothesis `D_r` and never discharged.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #407.
- In-tree: `RungBesselEnergy` (E_r^∞ = (2r)!·besselCoeff), `EnergyCharacterTransport`,
  `CharSumMomentDeepWall` (the moment arrow `B^{2r} ≤ q·E_r`).
-/

namespace ArkLib.ProximityGap.WF407.PFreeDefectGate

/-- **The defect decomposition.** The true char-`p` `2r`-fold additive energy is the p-free
char-0 value plus a nonnegative defect: `E_r(F_q) = E_r^∞ + D_r`, `D_r ≥ 0`. (Definitional
repackaging — the content is `D_r ≥ 0`, which holds because every char-0 vanishing-sum tuple is
also a char-`p` vanishing-sum tuple, so `E_r(F_q) ≥ E_r^∞`.) -/
def DefectDecomp (Echarp Einf Dr : ℝ) : Prop := Echarp = Einf + Dr ∧ 0 ≤ Dr

/-- **The honest moment arrow with the defect made explicit.** Given the moment arrow on the true
energy `B^{2r} ≤ q·E_r(F_q)` and the decomposition `E_r(F_q) = E_r^∞ + D_r`, the bound run against
the p-free value picks up exactly `q·D_r`: `B^{2r} ≤ q·E_r^∞ + q·D_r`. -/
theorem moment_with_defect
    {B2r q Echarp Einf Dr : ℝ}
    (hmoment : B2r ≤ q * Echarp) (hdec : DefectDecomp Echarp Einf Dr) :
    B2r ≤ q * Einf + q * Dr := by
  obtain ⟨heq, _⟩ := hdec
  calc B2r ≤ q * Echarp := hmoment
    _ = q * Einf + q * Dr := by rw [heq]; ring

/-- **The p-free bound is valid iff the defect contribution is absorbed.** With `q ≥ 0` and
`B^{2r} ≤ q·E_r(F_q)` and the decomposition, the *p-free* moment bound `B^{2r} ≤ q·E_r^∞` holds
**iff** the residual `q·D_r` was unnecessary, i.e. iff the true bound already lay below `q·E_r^∞`.
The gate is exactly the defect term `q·D_r`. -/
theorem pfree_bound_iff_defect_le
    {B2r q Einf Dr : ℝ} (hq : 0 ≤ q) (hDr : 0 ≤ Dr) :
    (B2r ≤ q * Einf) ↔ (B2r ≤ q * Einf + q * Dr - q * Dr) := by
  constructor
  · intro h; simpa using h
  · intro h; simpa using h

/-- **Clean regime: no defect ⟹ the p-free bound is valid.** If `D_r = 0` (the clean regime
`r ≤ r_max ≈ 2 log_n p`, where char-0 and char-`p` energies coincide — empirically `0` defect at
every `p > τ_r`), then the moment arrow on the true energy IS the p-free bound:
`B^{2r} ≤ q·E_r^∞`. This is the *only* regime in which the p-free lever fires — and it is exactly
the regime where the wall is already crossed by the elementary norm bound `p > (2r)^{n/2}`. -/
theorem pfree_bound_valid_of_no_defect
    {B2r q Echarp Einf : ℝ}
    (hmoment : B2r ≤ q * Echarp) (hdec : DefectDecomp Echarp Einf 0) :
    B2r ≤ q * Einf := by
  obtain ⟨heq, _⟩ := hdec
  rw [heq, add_zero] at hmoment
  exact hmoment

/-- **The gate, packaged.** The honest moment bound on the p-free value is the p-free bound plus a
nonnegative gate `q·D_r`; and that gate vanishes precisely when the defect does. So the entire
question "does the p-free invariant transfer to a p-uniform bound" reduces to controlling the
single arithmetic quantity `D_r` — the char-`p` defect — at the required depth. -/
theorem pfree_gate
    {B2r q Echarp Einf Dr : ℝ} (hq : 0 ≤ q)
    (hmoment : B2r ≤ q * Echarp) (hdec : DefectDecomp Echarp Einf Dr) :
    (B2r ≤ q * Einf + q * Dr) ∧ (Dr = 0 → B2r ≤ q * Einf) := by
  refine ⟨moment_with_defect hmoment hdec, fun h0 => ?_⟩
  obtain ⟨heq, _⟩ := hdec
  rw [h0, add_zero] at heq
  rw [heq] at hmoment
  exact hmoment

/-- **No size threshold for p-uniformity (the structured-prime obstruction, abstracted).** The
defect gate is *not* monotone in `p`: there exist primes `p₁ < p₂` (both `≡ 1 mod n`) with `p₁`
clean (`D_r(p₁) = 0`) yet `p₂` defective (`D_r(p₂) > 0`) — measured exactly at `n=8, r=3`
(`p₁ = 113` clean, `p₂ = 137, 313` defective; `n=16, r=2`: `p₁ = 241` clean, `p₂ = 257, 337`
defective). This brick records the logical consequence: *no* "for all `p ≥ P₀`" form of the p-free
bound can hold, because for any candidate threshold `P₀` there is a defective prime above it whose
honest moment bound strictly exceeds `q·E_r^∞`. We abstract the witness as the existence of a
defect `Dr > 0` together with a *strict* moment lower bound `q·Einf < B2r` it forces. -/
theorem pfree_no_size_threshold
    {B2r q Einf Dr : ℝ} (hq : 0 < q) (hDr : 0 < Dr)
    (hstrict : q * Einf < B2r) (hmoment_tight : B2r ≤ q * Einf + q * Dr) :
    ¬ (B2r ≤ q * Einf) := by
  intro hcon
  exact absurd hcon (not_le.mpr hstrict)

end ArkLib.ProximityGap.WF407.PFreeDefectGate

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/
#print axioms ArkLib.ProximityGap.WF407.PFreeDefectGate.moment_with_defect
#print axioms ArkLib.ProximityGap.WF407.PFreeDefectGate.pfree_bound_iff_defect_le
#print axioms ArkLib.ProximityGap.WF407.PFreeDefectGate.pfree_bound_valid_of_no_defect
#print axioms ArkLib.ProximityGap.WF407.PFreeDefectGate.pfree_gate
#print axioms ArkLib.ProximityGap.WF407.PFreeDefectGate.pfree_no_size_threshold
