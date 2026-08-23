/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.HaloFreeThreshold

/-!
# The SHARP (divisibility-form) depth-1 halo-free certificate (#444 / #389)

`HaloFreeThreshold.sum_pow_eq_zero_iff_antipodalClosed` discharges the depth-1 census halo
through the **size** threshold `p > (2^{m−1})^{2^{m−1}} = (n/2)^{n/2}` (`n = 2^m`). That size
threshold is **doubly exponential** and sits FAR ABOVE the deployed/prize regime `p ≈ n^4`
(`β = log_n p ≈ 4`). Probe `probe_haloprime_vs_prizeregime.py` measures the actual halo locus:
the largest prime `p ≡ 1 mod n` admitting a NON-antipodal vanishing subset sum has
`β = log_n p* ≈ 2.45, 5.80, 11.28` at `n = 16, 32, 64` — genuinely super-polynomial, crossing
the prize regime `β = 4` between `n = 16` and `n = 32`. So at prize primes the SIZE threshold
gives no certificate, and the per-prime halo is in general present.

What *does* survive at prize primes is the **divisibility** form: the engine
`KKH26.not_isRoot_of_not_dvd_resultant` replaces the size hypothesis with the sharp condition
"`p` divides no antipodal-differential resultant `Res_ℤ(R_E, Φ_{2^m})`", needing only the mild
`‖R_E‖₁ < p` (automatic for `p > n/2`, hence everywhere in the prize regime). This file welds
that engine onto the depth-1 antipodal census:

> **`sum_pow_eq_zero_iff_antipodalClosed_of_not_dvd`** — for a prime `p > 2^{m−1}` and a
> primitive `2^m`-th root `g ∈ F_p`, IF `p` divides no resultant `Res_ℤ(R_E, Φ_{2^m})` of a
> non-antipodal-closed `E ⊆ [0, 2^m)`, then `∑_{e∈E} g^e = 0 ↔ E` is antipodal-closed.

The mild `‖R_E‖₁ < p` is provided by `l1On_antipodalDiff_le` (`‖R_E‖₁ ≤ 2^{m−1} < p`). This is
the form usable at `p = Θ(n^β)` (`β` constant): the depth-1 halo is empty at exactly the primes
that avoid the (super-polynomial, but *sparse*) antipodal-differential resultant divisor set —
NOT only above the `(n/2)^{n/2}` size wall. It localizes the residual obstruction to the divisor
set, which is the form the [TZ24] good-prime supply (`KKH26ThornerZaman.lean`) is built to feed.

## Honest scope (rules 3, 6)
This is a route-sharpening for the census→`F_p` transfer, NOT a CORE proof or refutation. CORE
(`M(μ_n) ≤ C√(n·log(p/n))`) stays open. The probe verdict (halo locus is super-polynomial and
crosses `n^4` at `n ≥ 32`) is a constraint on the size-threshold route; this theorem records the
divisibility route that is NOT size-walled. It does not, by itself, prove the divisor set is
avoidable at prize primes — that is the residual.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## References
* Issue #444 (CORE), #389/#357 (census halo); DISPROOF_LOG O145/O149.
* `HaloFreeThreshold.lean` (size form); `KKH26SumsOfRootsOfUnity.not_isRoot_of_not_dvd_resultant`.
-/

set_option linter.unusedSectionVars false

namespace ArkLib.ProximityGap.KKH26

open Polynomial Finset

/-- **The sharp (divisibility-form) depth-1 halo-free certificate.** For a prime `p > 2^{m−1}`
and a primitive `2^m`-th root `g ∈ F_p`: if `p` divides no antipodal-differential resultant
`Res_ℤ(antipodalDiff (2^{m−1}) E, Φ_{2^m})` over the non-antipodal-closed `E ⊆ [0, 2^m)`, then a
vanishing subset sum `∑_{e∈E} g^e = 0` forces `E` antipodal-closed — and conversely. Unlike the
size form `(2^{m−1})^{2^{m−1}} < p`, the only size hypothesis here is the mild `2^{m−1} < p`
(automatic in the prize regime `p ≈ n^4`); the genuine content is the divisibility condition,
which is the sharp boundary of the depth-1 halo. -/
theorem sum_pow_eq_zero_iff_antipodalClosed_of_not_dvd
    {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m)
    {g : ZMod p} (hg : IsPrimitiveRoot g (2 ^ m))
    {E : Finset ℕ} (hE : E ⊆ range (2 ^ m))
    (hpN : (2 : ℕ) ^ (m - 1) < p)
    (hndvd : ¬ AntipodalClosed (2 ^ (m - 1)) E →
      ¬ (p : ℤ) ∣ Polynomial.resultant (antipodalDiff (2 ^ (m - 1)) E)
          (cyclotomic (2 ^ m) ℤ)) :
    (∑ e ∈ E, g ^ e = 0) ↔ AntipodalClosed (2 ^ (m - 1)) E := by
  classical
  set N : ℕ := 2 ^ (m - 1) with hN
  have hNpos : 0 < N := by positivity
  have h2N : 2 * N = 2 ^ m := by
    rw [hN, ← pow_succ']
    congr 1
    omega
  have hgN : g ^ N = -1 := by
    have := R12.pow_half_eq_neg_one hm hg
    simpa [hN] using this
  have hE' : E ⊆ range (2 * N) := by rwa [h2N]
  have heval := sum_pow_eq_antipodalDiff_eval hgN hE'
  constructor
  · intro hsum
    by_contra hnot
    have hR0 : antipodalDiff N E ≠ 0 := by
      intro h
      exact hnot ((antipodalDiff_eq_zero_iff N E).mp h)
    have hdeg : (antipodalDiff N E).natDegree < N := antipodalDiff_natDegree_lt hNpos E
    -- the mild l¹ residual: ‖R_E‖₁ ≤ N < p
    have hl1 : l1On N (antipodalDiff N E) < p :=
      lt_of_le_of_lt (l1On_antipodalDiff_le N E) (by simpa [hN] using hpN)
    -- the divisibility hypothesis fires because E is not antipodal-closed
    have hnd : ¬ (p : ℤ) ∣ Polynomial.resultant (antipodalDiff N E) (cyclotomic (2 ^ m) ℤ) := by
      have hnotE : ¬ AntipodalClosed N E := hnot
      simpa [hN] using hndvd (by simpa [hN] using hnotE)
    have := not_isRoot_of_not_dvd_resultant hg hR0 (by simpa [hN] using hdeg)
      (by simpa [hN] using hl1) (by simpa [hN] using hnd)
    apply this
    rw [Polynomial.IsRoot.def, ← heval]
    exact hsum
  · intro hclosed
    rw [heval, (antipodalDiff_eq_zero_iff N E).mpr hclosed]
    simp

/-! ## Source audit -/

#print axioms sum_pow_eq_zero_iff_antipodalClosed_of_not_dvd

end ArkLib.ProximityGap.KKH26
