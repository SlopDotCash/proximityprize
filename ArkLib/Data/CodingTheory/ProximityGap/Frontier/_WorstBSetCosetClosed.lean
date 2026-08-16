/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._EtaCosetInvariance

/-!
# The near-max ("worst-`b`") set is exactly a union of multiplicative `μ_n`-cosets (#444, door-(iv))

This file formalises, as an axiom-clean **constraint lemma** for the door-(iv) Lane-1/Lane-3 program,
the precise structural ceiling on the *worst-frequency set*

> `W(thr) = { b ∈ F_q* : ‖η_b‖ ≥ thr }`,    `η_b = Σ_{x∈μ_n} ψ(b·x)`,

namely: **`W(thr)` is invariant under the whole `μ_n`-action on the frequency line**, i.e. it is exactly
a union of full multiplicative `μ_n`-cosets. This is an immediate downstream consequence of the proven
coset-invariance `norm_eta_dilate_eq` (`_EtaCosetInvariance`), packaged as a statement *about the
argmax set itself* (`mem_worstSet_of_dilate`, `worstSet_dilate_mem`).

## Why this is the relevant door-(iv) constraint (NOT a closure, NOT a refutation)

The brief's single live target (Shaw-value essay 2026-06-18, Lane 1) asks: *"what arithmetic of `b`
selects the worst coset alignment? is the worst-`b` SET itself structured?"* — the hope being an
**arithmetic anti-concentration** for the worst-`b` set that a moment-free / completion-free bound
could grip.

This lemma pins the answer's PROVEN half: the only forced structure of `W(thr)` is the multiplicative
`μ_n`-coset-invariance (plus the antipodal `c = −1` special case, when `−1 ∈ μ_n`). Equivalently, `‖η‖`
descends to a function on the quotient `F_q*/μ_n ≅ ℤ_m` (`m = (q−1)/n`), and `W(thr)` is the full
preimage of a subset `W_q ⊆ ℤ_m`. **Any exploitable additive structure of the worst-`b` set must live
in `W_q ⊆ ℤ_m`** — there is no additive structure on the `F_q*` line beyond the (multiplicatively
forced) coset-closure.

### Empirical refutation of the exploit (probes; honesty §6)

The companion probes `scripts/probes/probe_444_worstcoset_quotient_structure{,_b}.py` measure `W_q ⊆ ℤ_m`
directly in the genuine prize regime (proper thin `μ_n`, `p ≫ n³`, `p ≡ 1 mod n`, `m` odd, NEVER
`n = q−1`; `n = 8..32`, `β = 4..5`, structured Fermat-type primes with `v₂(p−1)` up to `16` incl.
`p = 65537 = F₄`). Verdict, after adversarial re-checks (generator-independence + structured primes):

- `W_q` is **NOT** dilation-closed in `ℤ_m^×` (not a multiplicative orbit): `dilClosed = False` always.
- `W_q` has **NO** nontrivial arithmetic progression: `longestAP_{ℤ_m} ≤ 4`.
- `W_q` is additively **spread**: `|W_q + W_q| / |W_q|` grows toward `|W_q|` (Sidon-like).
- the magnitude profile `f(j) = ‖η(g^j)‖` on `ℤ_m` is **Fourier-flat**: `‖f̂‖_∞ / ‖f̂‖_2` stays within
  `≈ 1.2–2.0×` of the flat random baseline `1/√(m/2)` and shrinks toward it as `m` grows; this ratio is
  **generator-independent** (it must be: a different generator is a dilation of `ℤ_m`, and the statistic
  is dilation-invariant — IDENTICAL across two generators in the probe). Structured high-`v₂` primes do
  **not** create concentration.

So once the *proven* coset-invariance (this file) is quotiented out, the worst-coset set on `ℤ_m`
carries **no residual additive structure** for a moment-free / completion-free anti-concentration lever
to grip. This is a **constraint** on door (iv): it does not bound `M` (the prize `M ≤ C√(n·log p)` /
char-`p` BGK wall stays OPEN), and it is not a refutation of door (iv) as a whole — it refutes the
specific Lane-1 sub-hope "the worst-`b` SET is additively structured." The structure is *purely
multiplicative* (the coset-invariance) and additively generic.

## Honesty (project §6)

POSITIVE constraint lemma, axiom-clean, downstream of the proven `norm_eta_dilate_eq` by a single
threshold-membership rewrite. Bounds NOTHING from above. No CORE/capacity/growth-law claim. The probe
verdict is recorded as a NOTE (empirical, regime-bounded); only the coset-closure of `W(thr)` is
formalised in Lean (it is exactly the proven coset-invariance, re-expressed about the argmax set).
Issue #444.

## References
- `Frontier/_EtaCosetInvariance.norm_eta_dilate_eq` (the `‖η_{cb}‖ = ‖η_b‖` keystone this re-expresses).
- `Frontier/_EtaFrequencyParity` (the antipodal `c = −1` special case).
- `scripts/probes/probe_444_worstb_set_arithmetic.py` (W is a union of `μ_n`-cosets, neg-symmetric).
- `scripts/probes/probe_444_worstcoset_quotient_structure{,_b}.py` (the `ℤ_m` quotient is flat).
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #444.
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ProximityGap.Frontier.WorstBSetCosetClosed

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The near-max ("worst-`b`") set at threshold `thr`:  `{ b : thr ≤ ‖η_b‖ }`. -/
def worstSet (ψ : AddChar F ℂ) (G : Finset F) (thr : ℝ) : Set F :=
  {b | thr ≤ ‖eta ψ G b‖}

/-- **★ Coset-closure of the worst-`b` set.** If `c ∈ μ_n` (`c ≠ 0`, `c·G = G`) then `b` is in the
worst set iff its dilate `c·b` is: the threshold condition `thr ≤ ‖η_b‖` is `μ_n`-invariant. Hence
`worstSet` is exactly a union of full multiplicative `μ_n`-cosets — the ONLY forced structure of the
argmax set. Immediate from `norm_eta_dilate_eq`. -/
theorem mem_worstSet_dilate_iff {ψ : AddChar F ℂ} (G : Finset F) {c : F} (hc : c ≠ 0)
    (hcG : ∀ x ∈ G, c * x ∈ G) (thr : ℝ) (b : F) :
    c * b ∈ worstSet ψ G thr ↔ b ∈ worstSet ψ G thr := by
  unfold worstSet
  simp only [Set.mem_setOf_eq]
  rw [EtaCosetInvariance.norm_eta_dilate_eq G hc hcG b]

/-- Forward form: membership transports along the `μ_n`-dilation `b ↦ c·b`. -/
theorem worstSet_dilate_mem {ψ : AddChar F ℂ} (G : Finset F) {c : F} (hc : c ≠ 0)
    (hcG : ∀ x ∈ G, c * x ∈ G) (thr : ℝ) {b : F} (hb : b ∈ worstSet ψ G thr) :
    c * b ∈ worstSet ψ G thr :=
  (mem_worstSet_dilate_iff G hc hcG thr b).mpr hb

/-- The maximiser is never isolated: if `b` attains the sup-norm value `v = ‖η_b‖` then so does every
`μ_n`-dilate `c·b`. Modulus form of the coset-closure, with `thr := ‖η_b‖`. -/
theorem maximiser_orbit {ψ : AddChar F ℂ} (G : Finset F) {c : F} (hc : c ≠ 0)
    (hcG : ∀ x ∈ G, c * x ∈ G) (b : F) :
    ‖eta ψ G (c * b)‖ = ‖eta ψ G b‖ :=
  EtaCosetInvariance.norm_eta_dilate_eq G hc hcG b

end ProximityGap.Frontier.WorstBSetCosetClosed

/-! ## Axiom audit (expected: `propext, Classical.choice, Quot.sound` only). -/
#print axioms ProximityGap.Frontier.WorstBSetCosetClosed.mem_worstSet_dilate_iff
#print axioms ProximityGap.Frontier.WorstBSetCosetClosed.worstSet_dilate_mem
#print axioms ProximityGap.Frontier.WorstBSetCosetClosed.maximiser_orbit
