# #407 — Exhaustive open-avenue inventory (2026-06-14)

> **Scope correction (2026-10-28 audit, T48).** "Exhaustive" and "PROVEN DEAD" describe the routes
> and finite searches recorded in this session, not an exhaustive search over primes or over all
> possible proof methods. Each "dead" entry kills the specific inequality or construction that was
> tested. The `⟺` links in the next paragraph are proposed reductions between distinct unproved
> estimates, not established equivalences. Item `#82` is corrected inline: the HBK bound
> `E₂ ≤ n^{5/2}` *improves* the universal trivial bound `E₂ ≤ n³` for every `n > 1`; it is not
> worse than trivial, but it is still far too weak for the prize consumer.

Cross-referenced against the fleet's 100-connection mining (156 comments) + this session's campaigns.
The prize core is ONE object: a non-moment additive-combinatorial bound on the 2-power-subgroup r-fold
subset-sum **cross-surplus** at r≈ln q ⟺ `max_b|η_b| ≤ √(2n ln(q/n))` (Paley/BGK) ⟺ BCHKS Conj 1.12.
Crisp form: at n≈128 the height gate H(n)~2^192 > p~2^128 FAILS; prize = ONE explicit p-independent
inequality "char-p vanishing-2t-subset count ≤ char-0 count C(n/2,t) at |R|~n/2". n≤96 closed, n≥112 open.

## A. PROVEN DEAD (countermodels in-tree — do NOT re-attempt)
moment method (qE_r)^{1/2r}≥n; r=2+union (Fermat 1.465); energy √-lossy T²≤|G|E; Stickelberger/Hasse-Davenport
orthogonal; effective-Katz/Wasserstein (wrong limit); di Benedetto (needs n≥p^{1/4}); Weil (n<√q); per-witness;
higher-order-MDS (−1∈μ_n); #400 rigidity; sub-Gaussian/cumulant (deep cumulants inflate=W4); chirp (γ equidistribute);
free-conv/Cramér (i.i.d.-blind); lattice/Minkowski (p^{1/d}→1 vacuous); subspace-design/FRS (folding≠s=1);
Action-Orbit (3-sparse only); #82 HBK E₂≤n^{5/2} (better than the trivial E₂≤n³, but insufficient
at prize — corrected 2026-10-28; originally recorded as "worse than trivial").

## B. GENUINELY-UNEXPLORED / NAMED-BUT-NOT-ATTACKED (this session's targets, workflow wng9qwwqs)
1. **Shkredov higher additive-energy in char p** (#78/#100, NAMED BEST lever) — non-moment additive-comb bound on E_r / cross-surplus via large-spectrum/Bohr-set structure. The concrete form of "the single open lever."
2. **Kelley-Meka / Polynomial Freiman-Ruzsa** (2023, NOT in the 100) — exp-improved Roth + the now-PROVEN PFR structure theorem; do they constrain the vanishing-subset locus?
3. **Ring-LWE / ideal-SVP** (#92) — crossCell as a short-vector instance in ℤ[ζ_{2^μ}]; 2-power cyclotomic ideal-SVP has known structure (CDW/Biasse-Song).
4. **The n≥112 explicit inequality** — char-p vanishing-2t-subset count vs C(n/2,t) at the height-gate-failure scale; the crisp prize point.
5. **SubsetProductSurjectsMu** (B1 residual, char-free, PROVABLE) — (k+1)-subset sums of {0..n-1} cover ℤ/n (contiguous range length w(n-w)+1≥n). VERIFIED; closes the B1 top-direction count law unconditionally. [my main-loop verification done]
6. **Inverse Gowers / U^k-norm** (#87 NVM index>3 open) — does the multiplicative rigidity of μ_n forbid large correlation with low-degree phases (bounding max|η| via the proven inverse theorem)?
7. **Creative scan — NOT in the 100:** communication/query complexity lower bounds; Sanders quasi-poly Bogolyubov/Bohr iteration; Green-Tao-Ziegler inverse theorems; Bourgain-Gamburd spectral gap / superstrong approximation for the dilation action; Tao entropy/Shannon on subset-sums.

## C. OPEN-BUT-LOCALIZED-TO-BCHKS-1.12 (the 5 "open" of the 100: #7,15,20,92,96)
#7 (master localization), #15 (fixed-index asymptotic), #20 (sparse-cyclic-code≡incidence via BCH/syndrome),
#92 (Ring-LWE, = B3 above), #96 (R4 e₂-saturation = BGK wrong side). All are reductions TO the wall, not new levers.

## D. THE TRUE OPEN CORE (recognized open math; needs genuinely new input)
BCHKS Conjecture 1.12 (s=1) = BGK/Paley subgroup char-sum bound, best proven n^{1-o(1)} (BGK, o(1) non-effective)
and n^{1-31/2880} (di Benedetto, outside prize). The conjecture is numerically robust (B/√(2n ln)=0.76-0.89,
sub-Gaussian-leaning κ₄<0). NOT closable without a new additive-combinatorial input (Shkredov-style, char p).
