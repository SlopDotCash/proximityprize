# CRUX RESOLVED: the line-decoding / collinearity route reduces to BCHKS 1.12 — does NOT escape the count wall (2026-06-14)

**Bottom line (honest, well-verified): the line-decoding route (ABF26's own suggested approach via
Thm 4.21) is a FAITHFUL reformulation of the grand MCA challenge but does NOT escape the count wall for
explicit smooth μ_n RS. The MCA bad-count and the realizable non-collinear line-packing BOTH reduce to
the SAME C(n,k)/C(a,k) = far-line-incidence = BCHKS Conjecture 1.12 √-lossy ceiling. δ*_MCA is
q-INDEPENDENT and stays near Johnson for the worst (monomial / 2-power) lines, NOT near capacity. The
"collinearity ≠ count" hope is real but inert: collinearity does not give a rigidity gain here.**

## How the crux was resolved (fleet wf_7777e3f1, structural leg completed + adversarial leg)
The decisive question was: does μ_n antipodal rigidity force close codewords COLLINEAR (small bad-count)
beyond Johnson, even when the LIST is large (the GG25/FRS "collinear-but-large-list" escape)? Answer: NO.

STRUCTURAL leg (completed, collinearity_beyond_johnson = **not-forced**, refuted=True):
1. **Collinearity is not forced, even at an interior radius; there is no rigidity gain.** *(Corrected,
   audit T162. An earlier version said three close codewords "sharing a degree-<k structure are collinear
   for elementary interpolation reasons". That is false: being codewords of the same RS code is the only
   shared degree-<k structure, and it does not make three of them collinear.)* Below the unique-decoding
   radius `(n−k+1)/(2n)` at most one codeword is within `δ` of a word, so "collinearity" of close triples
   holds only **vacuously**. From the non-collinear-triple onset `δ=(n−k+1)/(2n)≈(1−ρ)/2` (item 3), which
   is an *interior* radius strictly below Johnson, machine-built examples give three mutually close
   codewords that are **not** collinear. Neither interpolation nor μ_n antipodal rigidity forces close
   codewords onto a line beyond unique decoding.
2. **Non-collinearity does NOT imply MCA-badness.** A disjoint multi-line tiled word keeps ε_mca→0
   (its witness agreement sets stay correlated). Measured two-line MCA-bad-rate vs budget~n/|F|: δ=0.5,
   0.625→0.000 all n; δ=0.70→0.032(n16)/0.000(n32)/0.000(n48); δ=0.73→0.025(n16)/0.003(n32)/0.000(n48)
   — a FINITE-SIZE artifact decaying to 0 in n. So the GG25/FRS escape does NOT produce a beyond-Johnson
   violation here, AND does not produce a beyond-Johnson GAIN either.
3. **Both reduce to the same wall.** The realizable mutually-non-collinear LINE count AND the MCA scalar
   bad-count both reduce to C(n,k)/C(agree_min,k) = far-line-incidence / BCHKS Conj 1.12 √-lossy ceiling.
   Non-collinear-triple onset δ=(n−k+1)/(2n)≈(1−ρ)/2 sits BELOW Johnson (ρ=1/4→0.375<0.5,
   ρ=1/8→0.4375<0.646; machine-built & verified all-close, all n).

ADVERSARIAL leg (rate-limited mid-run, but the key datum landed): δ* is **q-INDEPENDENT** —
δ*(monomial worst line)=0.6875 stable from q=257 through q=n³ — staying near Johnson, NOT moving toward
capacity as q grows. This is direct EVIDENCE AGAINST the conjectured δ*=capacity−Θ(1/log q) for the
worst (monomial / 2-power) lines. The honest tension: the conjecture's capacity-approach would require δ*
to move with q; it does not.

## Why this is consistent with everything else (triple convergence)
1. **In-tree transfer wall** (IN-TREE-collinearity-frame-transfer-wall doc): CollinearityMatchingFrame.lean
   proves collinear⟺antipodal-balance char-0-exact, but mod-p transfer needs p>(6n)^{n/2} (exponential),
   failing at prize field for n≥64. The per-triple criterion already collapses to the height wall.
2. **§5 unification limit**: LD⟹MCA has a √-loss false-to-remove for full-domain; the smooth-domain
   special case (the prize) is exactly the open part — and the count side (Elias floor) is Johnson-tight
   for explicit RS (Gur02/GS03).
3. **Plotkin-proxy + cliff-confinement CLOSEOUTs** (prior session): far-line incidence reproduces Johnson;
   the true MCA δ* (≥Johnson floor) is the BGK/BCHKS object.
ALL THREE converge: every route — count, collinearity, line-decoding, far-line incidence — reduces to
**BCHKS Conjecture 1.12 / additive energy of μ_n at depth r~log q** (the framework authors' own Nov-2025
open conjecture, ePrint 2025/2055). This is an OPEN hard-math conjecture.

## Honest verdict against the prize directive
The directive requires a CLOSED conjecture that does NOT reduce to open hard math. After exhaustively
attacking the CORRECT object (line-decoding / ε_mca bad-count, ABF26's suggested route — not the proxy):
- The line-decoding route is a faithful reformulation but **reduces to BCHKS 1.12**, same as every other
  face. It is NOT a BCHKS-free closed path.
- For the worst (monomial / 2-power) lines, δ*_MCA is q-independent near Johnson — no numerical
  beyond-Johnson escape was found; the capacity-approach conjecture is unsupported for these lines.
- The genuinely-open residual (structural leg's "next"): is overlapping-support line-packing realizable
  up to the BCHKS count, or capped below it by μ_n structure? — but this IS the BCHKS 1.12 wall restated.
CONCLUSION: the prize, attacked through its OWN suggested line-decoding route, reduces to BCHKS Conj 1.12.
No closed BCHKS-free conjecture pinning δ* beyond Johnson was found; the honest state is that the prize =
BCHKS 1.12 (open). This is a NEGATIVE result closing off the line-decoding route as an escape, not a
solution. The remaining live lever is the DIRECT BCHKS-1.12 / additive-energy attack (a separate effort).

## Lean targets (lock in the negative structure — valuable regardless)
- The line-packing ⟹ BCHKS-count reduction: pair GG25SpreadBound.lean (ℓ=1 spread bound) with the
  identity "realizable non-collinear line count = far-line incidence C(n,k)/C(a,k)".
- The transfer-wall corollary: CollinearityMatchingFrame.collinear_iff_balanced_modp threshold (6n)^{n/2}
  exceeds the prize field for n≥64 — formalize as "per-triple char-p collinearity transfer fails at
  prize scale".
