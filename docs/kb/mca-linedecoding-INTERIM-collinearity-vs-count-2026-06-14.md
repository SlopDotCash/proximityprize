# MCA line-decoding attack — INTERIM (4/6 legs; the decisive 2 failed on session limit), 2026-06-14

> **Scope note (2026-10-28 audit, T48; cross T74).** This note rightly distinguishes codeword count
> from affine structure, but its working definition of badness is not the MCA definition. It
> counts "close codewords NOT lying on the affine line". Actual MCA badness (ABF26 Def 4.3, as in
> `Errors.lean`) quantifies over a **common witness set** of size at least `(1−δ)n` and requires a
> joint codeword explanation of both rows on that set. Ordinary list collinearity alone does not
> implement that definition. The two failed legs, and any task labelled unverified here, remain
> unverified; they are not support for the proposed exact reduction.

## What returned (4 legs) + the tension
Attack fleet wf_d769b9c5 on the CORRECTED object (line-decoding / ε_mca bad-point count). Completed:
- **capacity-pin (beyond_johnson=yes, partial):** closed-form CEILING δ*_MCA ≤ (1−ρ) − H₂(ρ)/log₂(q)
  + O(1/(n log q)). Prize q=n·2^128: ρ=1/2→0.4931, ρ=1/4→0.7444, ρ=1/8→0.8712, ρ=1/16→0.9352 — all
  FAR beyond Johnson (0.293/0.5/0.646/0.75), gap-from-capacity ~0.001–0.007. BUT this is the UPPER
  bound (= known KK25/Elias-radius ceiling); the matching LOWER bound (achievability) = the open prize.
- **lit (confirmed):** 7 papers. The missing explicit-RS line-decoding lemma is NAMED = CGHLL26
  (eprint 2026/532) Conjecture 2 (line-decodability up to Elias radius r_E=capacity−Θ(1/log q)).
  GG25's capacity proof is gated on subspace-design via AHS25 PRUNE, which plain μ_n RS LACKS ⟹ cannot
  import wholesale. The Lam-Leung/Mann antipodal-rigidity lever is GENUINELY ABSENT from the
  line-decoding literature — an unused angle. IF it delivers (δ,n,n+1)-line-decodability it IS CGHLL26
  Conj 2 and closes the prize via ABF26 Thm 4.21. New eprint IDs: CGHLL26=2026/532, GG25=2025/2054,
  Hab24=2024/1571, Hab25=2025/2110, CS25=2025/2046, DG25=2025/2010, FS25=2025/2197.
- **mca-numeric (labeled "refuted"):** worst-line bad count crosses budget AT Johnson, n≤16, no
  beyond-Johnson room. BUT the leg ITSELF admits "at small n CANNOT confirm the fine structure
  (1/log n ≈ 0.5 at n=8 sits below Johnson); window too coarse." => this is the FINITE-SIZE ARTIFACT
  I already documented (n=8 bad=close because the close-fraction is a large constant at tiny n). It
  refuted the STRAWMAN "bad ≤ budget THROUGHOUT the window" (never the claim); the REAL claim (bad ≤
  budget up to capacity−Θ(1/log q)) is INVISIBLE at n≤16. So mca-numeric did NOT refute the conjecture.
- **gg25-gap (labeled "refuted"):** claims antipodal lever "collapses to BCHKS 1.12 / additive-energy
  E(μ_n) wall, √-lossy, Johnson only." BUT (a) its adversarial verify was CUT OFF by the session limit
  (unchecked), and (b) it CONFLATES collinearity (line-decoding) with list size (count). These are
  DIFFERENT objects — see below.

## The crux the failed legs leave UNRESOLVED: collinearity ≠ count
The two decisive legs FAILED on the session limit:
- **antipodal-forces-collinearity** (the structural mechanism — does antipodal rigidity force close
  codewords COLLINEAR?), and
- **refute-beyond-johnson** (the adversarial kill at large n).
gg25-gap's claim "branch B = BCHKS 1.12" assumes collinearity reduces to the list bound. It does not,
a priori:
- **List size** |Λ(C,δ)| = #close codewords (a 0-dim count). BCHKS Conj 1.12 bounds this.
- **Line-decoding bad count** = #close codewords NOT lying on the affine line u1+γu2 in C (a 2-dim/
  affine-structure object). A line can have a LARGE close-codeword list that is nonetheless almost
  entirely COLLINEAR (all on one u1+γu2 family) ⟹ small bad count ⟹ small ε_mca, EVEN above the list/
  Johnson bound. This is EXACTLY GG25's mechanism for FRS: list is large near capacity but collinear.
- So "line-decoding collapses to the list/BCHKS wall" is NOT automatic — it is true only if the close
  codewords are generically NON-collinear. Whether μ_n antipodal rigidity forces collinearity (sharing
  of agreement sets, per Def 4.3) is the open structural question — and gg25-gap did not actually settle
  it (it argued the LIST is √-lossy, which is the count, not the collinearity).

## Honest status
- Beyond-Johnson δ* is NOT refuted (the "refutation" is a finite-size artifact + a count/collinearity
  conflation). It is also NOT confirmed (only the ceiling is, which is known).
- The decisive question — does μ_n antipodal rigidity force agreement-set SHARING / collinearity of
  close codewords (bad ≤ budget) into the window — is OPEN and was not computed (the two legs failed).
- Next: re-run ONLY the two failed structural legs at LARGER n with the sharpened framing
  (collinearity/sharing, NOT count), plus an adversarial check of the count-vs-collinearity conflation.
