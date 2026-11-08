# Borrow-from-provable-regimes (transfer workflow) — FINAL result (wf_07f3052a, T2 taken over manually)

Strategy: for each regime where the prize/√n-bound IS provable, extract the mechanism, pinpoint the exact
failing step at prize scale (explicit thin n=p^0.19 2-power μ_{2^a}, large dim), attempt a higher-order lift.

## Outcome: 2 NARROW, 7 BLOCK, 0 CLOSE. (judge didn't auto-run; synthesis below is mine.)

> **Correction (2026-10-28 audit, T48).** The T2 conclusions "that half is CLOSED" and "the 'all
> received words' quantifier is ELIMINATED" are withdrawn. A few generic received words with zero
> bad scalars (`μ_16`, `k = 4`, two radii) are samples. A generic-position theorem for another object
> (BGM for random evaluation points) does not show that the explicit antipodal monomial directions
> maximize the bad count over **every** received stack. That extremality statement, and the bridge
> from this incidence count to the actual MCA bad-scalar event, remain open inputs. The finite
> diagnostics are kept as evidence of where failures were observed.

### NARROWS
- **T2 genericity→graceful higher-MDS (I took this over; the most informative).** PROVEN computationally:
  in the prize WINDOW the higher-MDS failures concentrate ENTIRELY at the explicit antipodal/tower received
  words (μ_16,k=4: incidence 8 vs 0 generic at δ=.562; 88 vs 0 at δ=.625). Generic received words have ZERO
  bad scalars. So list_{μ_n}(generic u)=generic-list (provably poly, BGM applies to generic received words even
  over explicit μ_n) — that half is CLOSED. Residual = ONLY the explicit antipodal monomial-direction family =
  the I_∞ cyclotomic count (q-independent, saturating). The "all received words" quantifier is ELIMINATED.
  ⟹ the cleanest localization: prize = bound I_∞(δ) over the explicit antipodal directions at the window edge.
  (Near capacity, past the window edge, generic≈antipodal — failure zone, irrelevant.)
- **T5 constant-dim KKH26→growing dim.** Dim-uniform supply bound lifts until the ownership separation needs
  r(r−1)<2^{μ−1}, i.e. the r≲√n wall = Johnson. Narrows, stops at Johnson.

### BLOCKS (precise walls)
- **T3 intrinsic-fold (the most prize-specific borrow).** x↦x² folds μ_{2^a}→μ_{2^{a-1}}, BUT the SINGLETON
  stratum keeps UNREDUCED degree k−1 on the half-length transversal, which maps bijectively (x↦x²) onto μ_{n/2}
  — so the singleton sub-instance is RS of degree k on μ_{n/2}, the SAME problem recursively. The FRI fold
  provably does NOT reduce the problem. (Deepest structural reason the prize is hard.)
- **T1 distributional-Mahler.** Typical conjugate = √(2r)>1 (confirmed), so typical Norm = C(r)^{2^29} ≈
  2^{5e8} ≫ p. Even the typical Norm is hyper-exponential — the distributional refinement doesn't help.
- T4 tower-subspace-design: the tower cosets don't give the bounded-intersection design property.
- T6 circulant-Siegel: DFT block-diag stops at the Sudan (sub-Johnson) radius; m≥2 multiplicity re-leaks.
- T7 Mahler-Stepanov interpolation: the two techniques don't compose across γ=0.19.
- T8 semiprimitive explicit eval: √p-scale, arithmetically dead at the prize prime.
- T9 p-adic adelic local-global: the archimedean+𝔭-adic product formula leaks back to the excess count.

## Net
The strategy worked as a DIAGNOSTIC: T2 proposed a narrowed form — **bound the explicit,
q-independent, saturating cyclotomic incidence I_∞(δ) over the antipodal monomial directions** — and
observed zero bad scalars for the sampled generic received words. That narrowing is conditional on the
missing extremality and MCA-bridge inputs (see the correction above); it did not prove a
generic-received-word half. T3 gives the deepest reason it's hard (the fold recurses). It did NOT
close. Next: the I_∞ direct-attack campaign (100-approaches → essays → attack list → assault).
