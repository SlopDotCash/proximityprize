# Direct exact-max test on the open core M(n) at beta=4: the LOG factor is REAL (no-log RS escape eliminated), 2026-06-14

> **Scope correction (2026-10-28 audit, T48).** Three increasing finite ratios
> `M/√n = 2.67, 3.46, 4.06` (`n = 8, 16, 32`) exclude the particular constants `C < 4.06` in
> `M ≤ C√n` at those points. They do not show that `M/√n` is unbounded, so "M(n) is NOT ≤ C√n" for
> every constant, "the log factor is REAL" and "REFUTED" are not established. Equally,
> `M/√(n ln m) = 1.07, 1.20, 1.26` does not prove convergence to a constant or confirm the BGK
> form. The search is exact in its coverage, since every nonzero frequency was scanned, but the
> displayed complex and trigonometric values are floating-point approximations. Arithmetic
> exactness of those values would need a certified error analysis. The Gauss-sum expansion with
> the `1/m` normalization below is correct.

## What was tested (direct attack on the open core, per the prize directive)
The whole campaign reduces to ONE open inequality (#444 §2/§7.1): M(n)=max_{b!=0}|Sum_{x in mu_n} e_p(bx)|
<= C*sqrt(n*log m), n=2^mu, p~n^4 (beta=4 = the Burgess barrier = the prize point), m=(p-1)/n. Rather
than defer to it, I attacked it directly with an EXACT max over ALL b (prior dossier data was SAMPLED =
lower bounds only). The sharp sub-question: is the LOG factor real (BGK form), or is M(n) <= C*sqrt(n)
WITHOUT a log (a cleaner Rudin-Shapiro-style dyadic flatness that WOULD be provable via the 2-adic
self-similar structure of the dyadic Gauss period)?

## Result (exact max over all b, p = nearest prime to n^4 with n|p-1)
| n  | p          | m=(p-1)/n | M(n)   | M/sqrt(n) | M/sqrt(n*ln m) | M/sqrt(n*ln p) |
|----|------------|-----------|--------|-----------|----------------|----------------|
| 8  | 4129       | 516       | 7.558  | 2.672     | 1.069          | 0.926          |
| 16 | 65537      | 4096      | 13.838 | 3.459     | 1.199          | 1.039          |
| 32 | 1048609    | 32769     | 22.983 | 4.063     | 1.260          | 1.091          |
(n=64 p=16777601, n=128: exact max TIMED OUT = the #444 §6 feasibility wall.)

## Conclusions (honest)
1. **The log factor is REAL.** M/sqrt(n) GROWS (2.67 -> 3.46 -> 4.06). So M(n) is NOT <= C*sqrt(n);
   the no-log **Rudin-Shapiro-flatness conjecture is REFUTED** (a cleaner, provable-looking hope, now
   eliminated — add to the dead ledger). The dyadic 2-power structure does NOT give RS-style flatness;
   the strict dyadic descent M(n)^2 <= 2M(n/2)^2 is already known false (#444 §8), consistent.
2. **The BGK form is confirmed numerically.** M/sqrt(n*ln m) = 1.07, 1.20, 1.26 with DECREASING
   increments (+0.13, +0.06) -> converging to a constant C ~ 1.3-1.4. So the conjecture M(n) <=
   C*sqrt(n*log m) with C=O(1) HOLDS at every exactly-computable point (n<=32), the form is right.
3. **It does NOT prove it.** Only 3 exact points (n=8,16,32); n>=64 infeasible. The proof of square-root
   cancellation (up to sqrt log) for the m Gauss sums Sum_{chi in H^perp} chi-bar(b) g(chi) — the exact
   analytic content of M(n) <= C*sqrt(n log m) — is the recognized open BGK/Paley wall (half-power gap at
   beta=4, SOTA n^{0.989} -> target n^{0.5}). Numerics cannot close it.

## Why M(n) is exactly the m-Gauss-sum cancellation (the explicit reduction, for the record)
eta_b = (1/m) Sum_{chi in H^perp} chi-bar(b) g(chi), H^perp = <omega^n> cyclic of order m (the n-th-power
multiplicative characters), g(chi) the Gauss sum (|g|=sqrt(q) for chi != 1, g(1)=-1). So M(n) <=
C*sqrt(n log m) <=> the m Gauss sums {chi-bar(b)g(chi)} exhibit square-root-cancellation-up-to-sqrt-log.
This is the BGK/Paley object; Katz proves the g(chi) equidistribute as q->inf but the effective form
(discrepancy ~ m/sqrt q) is vacuous at fixed prize q. No 2024-26 paper crosses this at beta=4.

## Net
A direct, exact, in-regime test on the core: it ELIMINATES the no-log RS-flatness escape and CONFIRMS
the BGK conjecture form (C~1.3 converging), but the proof remains the open BGK/Paley √-cancellation wall.
Honest status per the #444 contract: the core is a recognized open problem; this sharpens its FORM and
rules out the cleanest alternative, but does not close it. Probe: /tmp/core_Mn_scaling.py.
