# Direct char-p sup-norm assault (10 angles + adversarial verify) — outcome

> **Correction (2026-10-28 audit, T48; cross T47/T87/T91).**
> - **Wrong regime label.** `n = 64`, `p = 65537` is not a `β = 4` in-band cell. Since
>   `65537 < 64³`, `β = log_n p ≈ 2.67 < 3`, as the same paragraph's violation row already says. The
>   "at β=4 the bound holds robustly" sentence therefore cites no `β = 4` evidence.
> - **No universal thinness separation.** "Violations only at β<3" and "a proof MUST use β≥4" are
>   finite observations. The recorded thin cell `n = 64`, `p = 17318209` (`β ≈ 4.008`) has
>   `E_2 = 13632`, so `p·E_2 − n⁴ > p·3n²` and `a_2 > 1` there (T91; G173). The `r = 2` base needs
>   the Sidon hypothesis, which fails in that cell.
> - **Not equivalences.** One supremum estimate is not equivalent to a family of moment bounds. The
>   moment bounds `a_r ≤ 1` (`r ≤ log m`) imply the supremum bound, but a supremum bound gives only
>   `∑_{b≠0} ‖η_b‖^(2r) ≤ (p − 1)·M^(2r)`, not `a_r ≤ 1`. So "⟺" and "the whole prize is the single inductive step
>   `c_r ≤ 1`" overstate a one-way sufficient condition. That condition also does not by itself
>   supply the MCA bridge. "Undecidable on reachable n" and "eliminates" are likewise statements
>   about the tested inequalities, not about all possible closed forms or methods.

Target: PROVE M(n)=max_{b≠0}|Σ_{x∈μ_n}e_p(bx)| ≤ C√(n log m) at depth r≈log m (= BCHKS 1.12 = p^{1/4}
Bourgain Problem 5). Every angle tasked to create a full/partial/conditional/almost-all bound; adversarially
verified prize-faithfully. OUTCOME: no unconditional prize bound (expected — recognized open wall), but three
genuine outputs + a sharp convergence.

## Verified verdicts (adversarial)
| angle | verify | what it gives |
|-------|--------|----------------|
| Induction on depth (recursion) | HOLDS (conditional) | **THE cleanest restatement**: M≤√(2n log m) ⟺ a_r:=A_r/Wick_r ≤ 1 ∀ r≤log m. Exact engine recursion a_{r+1}=(a_r+2r·c_r)/(1+2r) (matches in-tree CharPMomentRecursion), proven bases r=1,2 (Sidon E_2=3n²−3n), Wick growth law verified, gate+consumer hold 36 primes β∈[3,5] 0 violations. Open part = the single monotonicity/c_r≤1 step. |
| van der Corput | HOLDS (conditional) | M≤√2·√(n ln p), saddle r*=ln p; conditional on the same Wick bound. Stationary-phase = clean no-go (discrete geom. progression, no real saddle). |
| cumulant / MGF | HOLDS (conditional) | saddle y*²=2log q/n, C→√2; obstruction first bites at r=13 (n=64, log q≈11) = depth r≈log q (the wall). |
| Gauss-sum mult-independence | HOLDS (conditional) | depth-r moment = additive-mod-m index-collision energy of Gauss-sum products; reduces to (not beats) the wall. |
| Direct moment/Wick δ_eff | FAILS as prize, **but math SOLID** | δ_eff(r,n)=1−[4+r+log_n((2r−1)‼)]/(2r) → **1/2−2/r**, UNCONDITIONAL almost-all-primes at FIXED r, BEATS di Benedetto (n^{0.989}) for r≥5. NOT the prize: almost-all ≠ THE prize prime; house bound vacuous n≥16; uniformity in growing r open. Genuine partial on the almost-all Bourgain-P5. |
| almost-all-primes | FAILS as prize | density-1 at fixed r (axiom-clean counting lemmas real), vacuous at growing r≈log m. |
| refined norm bound | FAILS | |N(S)|≤t^{n/4} (halved exponent) but controls norm SIZE; real obstruction is p-DIVISIBILITY (true min |N|=2=Φ_{2^μ}(1)). Wrong object. |
| dyadic-tower descent | FAILS | τ-decomposition + contraction W_n=2^{1−r}W_{n/2}+κ_n exact, but the even-cross No-Excess (★★) leaks at +10% density for prize primes at r≈log m. |
| subspace theorem (ESS) | FAILS | conditional on cyclotomic-ideal-lattice L1-min > 2 log m; ESS count doubly-exponential in 2r (vacuous). |
| Stepanov | REFUTED | any pointwise depth-r Stepanov forced B≥n^{r/2} (no-go); the Wick target itself NOT refuted (A_r/Wick≈0.66–0.97). |

## The convergence (the real result)
SIX independent routes (induction, van der Corput, cumulant, Gauss-sum, + the moment identity, + the
crossCell) ALL reduce M≤√(2n log m) to the SAME single hypothesis: the char-p DC-subtracted Wick/deep-moment
bound A_r=E_r(μ_n,F_p)−n^{2r}/p ≤ (2r−1)‼·n^r at r≈log m (BCHKS 1.12). The SHARPEST attackable form (induction):
   **a_r := A_r/Wick_r ≤ 1 for all r ≤ log m**, with PROVEN bases r=1,2, the EXACT recursion
   a_{r+1}=(a_r+2r·c_r)/(1+2r), c_r=crossA_r/crossWick_r — the whole prize is the single inductive step c_r≤1.
THINNESS-ESSENTIAL confirmed numerically: at β=4 the bound holds robustly (n=64 Fermat p=65537 in-band ratio
0.94); violations only at β<3 (n=64 β=2.67 ratio 1.59–3.90). A proof MUST use β≥4.
GENUINE PARTIAL (new on the almost-all Bourgain-P5 at p^{1/4}): δ_eff=1/2−2/r unconditional almost-all-primes
fixed-depth, beating di Benedetto for r≥5 — but not THE prize prime.

## Next constructive step
Formalize the conditional pin: the recursion a_{r+1}=(a_r+2r c_r)/(1+2r) + bases r=1,2 + consumer
(a_r≤1 ∀r ⟹ M≤√(2n log m)) as an axiom-clean Lean brick (sharper than OpenCoreConditionalPin's
WorstCaseIncidenceBounded), reducing the prize to the SINGLE monotonicity inequality c_r≤1 at β=4 — then attack
that one inequality. The growth-class itself stays undecidable on reachable n (the structural reason the prize
needs analytic/external input), but the conditional pin is a genuine, formalizable, BGK-decoupled deliverable.
