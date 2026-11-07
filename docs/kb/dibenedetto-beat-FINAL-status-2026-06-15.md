# di Benedetto beat — FINAL honest status (#444): a CONDITIONAL closeness improvement, not unconditional

> **Further correction (2026-10-28 audit, T48; see R-260).** The retraction of unconditionality
> below is right, but the table still needs three repairs.
> - **Field factor.** The table drops the field factor. The conditional bound is
>   `|H|^{65/72}·p^{1/72}`, and `23/24` is its total exponent only after substituting `p = |H|^4`.
>   If the bound is written as `n^{23/24}·p^{1/72}`, as in
>   `Research/ProximityPrize/Frontier/_AvT3a_DiBenedettoBeatAssembly.lean`, it is nontrivial only for
>   `n > p^{1/3}`, not `p^{1/7}`.
> - **Hypothesis range.** The published Theorem 3.1 (arXiv:2003.06165) is stated for
>   `p^{1/4} < H < p^{1/2}`, with bound `H^{2689/2880}·p^{1/72}` up to a `p^{o(1)}` loss. The thresholds
>   in the table (`p^{0.2094}`, `p^{1/5}`, `p^{1/7}`) all lie below `p^{1/4}`, outside that range.
>   They are formal nontriviality points of the expressions, not established bounds, and "nontrivial
>   at beta=5" is not established. Any near-Sidon strengthening needs its own derivation.
> - **Characteristic transfer.** `RepTwo` / `RepThree` and the exact finite-field energies need their
>   actual transfer hypotheses. "EXACT and p-invariant" describes selected primes. Recorded thin
>   cells refute the universal equalities: `μ₃₂ ⊆ F₃₂₉₉₃` has `E_2 = 3744`, and `n = 64`,
>   `p = 17318209` has `E_2 = 13632` (T91).

CORRECTION to the earlier "will become unconditional" claim. Verified by exact F_p computation (2 agents).

## What is PROVEN (axiom-clean, in-tree)
- char-0 third-energy closed form: rEnergy G 3 <= 15*card^3 GIVEN RepThree G (= No-Excess r=3: every zero-sum
  6-tuple of G is a char-0 vanishing sum). Files: CharZeroEnergyThreeExact.lean (B6_eq_E3, kappa6_eq closed
  form 15n^3-45n^2+40n), GaussianEnergyThreeRepThree.lean (rEnergy_three_le_of_repThree). Holds for ANY
  negation-closed G in char != 2.
- The di Benedetto substitution VALIDITY (Phase 2, verified vs arXiv source): T_m = additive energy of H itself;
  modular; no coupling.
- E_2(mu_n)=3n^2-3n, E_3(mu_n)=15n^3-45n^2+40n EXACT and p-invariant, machine-verified to n<=64 incl extreme
  structured primes (v2<=25).

## What is NOT unconditional (the correction)
The all-n char-p statements RepTwo(mu_n) (No-Excess r=2) and RepThree(mu_n) (No-Excess r=3) at the PRIZE prime
do NOT follow from the Lam-Leung norm argument: the bad-prime ceiling is EXPONENTIAL (max weight-<=6 sextuple
norm ~ 6^{n/2}), and the prize prime p~n^4 << 6^{n/2}. So at the prize order the norm argument gives nothing;
RepTwo/RepThree are VERIFIED (n<=64) but reduce to the SAME good/bad-prime char-p wall, at shallow weight 4/6
(vs the deep r~89 of the full prize). E_3 IS empirically p-invariant (E_4 first fails), but that is verified,
not proven for all n at p~n^4.

## The beat (CONDITIONAL on the shallow No-Excess hypotheses, verified n<=64)
| inputs | exponent (beta=4) | threshold | condition |
|---|---|---|---|
| di Benedetto general (t2=49/20,t3=4) | 0.9892 | p^{0.2094} | UNCONDITIONAL |
| + t2=2 (Sidon floor) | 0.9861 (71/72) | p^{1/5} | No-Excess r=2 (verified n<=64) |
| + t2=2, t3=3 | 0.9583 (23/24) | p^{1/7} | No-Excess r=2,3 (verified n<=64) |

So: a CONDITIONAL closeness improvement (0.9892->0.9583, covering the prize regime where di Benedetto vanishes),
conditional on mu_n having No-Excess at r=2,3 at the prize prime. The char-0 reductions are proven; the char-p
No-Excess inputs are machine-verified to n<=64 but not proven for all n / at the prize order (shallow good/bad-
prime wall). A possible TINY unconditional gain via bootstrap (use di Benedetto's own unconditional M to bound
T_3: t3 -> 4-31/1440 ~ 3.978) is marginal and unverified-in-the-argument.

## Further push (antipodal chain-shortening)
NOT established. The Delta^72 descent collapse is energy-independent and structural (3 rounds = 6+12+54);
whether the antipodal -1 in mu_n shortens it to fewer rounds (multiplying the saving) was not resolved. Even the
absolute Sidon floor caps at Hexp=7 (saving 1/24), so this lane cannot reach exponent 1/2 regardless. Reaching
1/2 = beat the p^{1/4} trilinear prefactor = the BGK/BCHKS wall (no known subgroup improvement).

## Bottom line
A genuine, verified CONDITIONAL improvement on the SOTA char-sum exponent in the prize regime (the first thing
nontrivial at beta=5 where di Benedetto vanishes), conditional on shallow well-tested No-Excess hypotheses. NOT
unconditional, NOT a prize closure (0.9583 >> 1/2). The half-power wall stands above it. Honest correction to the
earlier unconditional framing.
