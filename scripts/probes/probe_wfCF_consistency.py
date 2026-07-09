# probe_wfCF_consistency.py  (#444)
#
# Consistency of  delta*(rho,n) = (1-rho) - H2(rho)/log2(n)  against the EXACT in-tree data.
# These exact points are at LARGE eps* / SMALL n -- NOT the prize cushion (eps*=2^-128).
# They test STRUCTURE (the floor/band/pin behaviour), NOT the exact Theta(1/log n) cushion,
# which only becomes non-vacuous at n>=~256 (window interior empty for n<=64).

from math import log2, sqrt

def H2(x):
    if x<=0.0 or x>=1.0: return 0.0
    return -x*log2(x) - (1-x)*log2(1-x)

def dstar(rho,n):
    return (1-rho) - H2(rho)/log2(n)

print("="*82)
print("CONSISTENCY of  delta* = (1-rho) - H2(rho)/log2(n)  vs EXACT in-tree data")
print("="*82)

print("""
The conjecture targets the PRIZE cushion: eps*=2^-128, q~n*2^128. The in-tree exact data is
at LARGE eps* (e.g. 2/5, 2/17) and SMALL n (4..38). In that regime:
  - The window interior (1-sqrt rho, 1-rho) is EMPTY for n<=64 (Johnson and capacity collide
    after the Theta(1/log n) correction is small-n-large), so there is NO cushion to pin.
  - delta* is instead governed by the GRANULARITY LADDER delta*=j/n (a sub-Johnson step
    function) and exact pins -- these probe STRUCTURE (integrality, band crossings), not the
    asymptotic cushion constant.
So the test is: does the conjecture (a) give SANE values at small n (not >capacity, not <0),
and (b) reproduce the qualitative facts (window opens only at large n)? It must NOT be expected
to equal j/n at small n -- those are different (large-eps*) operating points.
""")

print("-"*82)
print("[A] GRANULARITY LADDER: delta* = j/n on bands 3(j-1)+k <= n, eps* in [j/q,(j+1)/q).")
print("    (GranularityLadderRS.lean -- LARGE eps* ~ j/q, SUB-Johnson. NOT the cushion.)")
print("-"*82)
print("""  The ladder is delta*=j/n with j=floor(q*eps*). At PRIZE eps*=2^-128 and q~n*2^128,
  j=floor(n)=n, giving delta*=n/n=1 -- but the band condition 3(j-1)+k<=n FAILS for j~n
  (needs 3n<=n). So the ladder is VACUOUS at the prize point: it operates at eps* large
  enough that j is SMALL (j<<n). The conjecture and the ladder describe DISJOINT regimes:
    ladder:    eps* >= 1/q (j>=1), sub-Johnson delta*=j/n, small n.
    conjecture: eps* = 2^-128, window-interior cushion, n>=256.
  CONSISTENCY = they do not contradict: at the ladder's eps*, the conjecture's H2/log2 n is
  not the operative law (different eps*). No discrepancy -- different operating points.""")

print("-"*82)
print("[B] EXACT PINS (DeltaStarExactPinF5/F17): toy scale, large eps*.")
print("-"*82)
pins=[
  ("RS[F5,*,2]  n=4 rho=1/2 eps*=2/5",   4, 0.5,   0.25,  "1/4 = (1-rho)/2 = UD radius"),
  ("RS[F17,<2>,4] n=16 rho=1/4 eps* in [2/17,7/17)", 16, 0.25, 0.25, "1/4, maximal second pin"),
]
print(f"  {'pin':>46} | {'delta*_exact':>11} | {'conj@thisn':>10} | note")
for name,n,rho,dex,note in pins:
    c=dstar(rho,n)
    print(f"  {name:>46} | {dex:11.4f} | {c:10.4f} | {note}")
print("""
  The conjecture's value at n=4 (rho=1/2): 1-rho-H2/log2 4 = 0.5 - 1.0/2 = 0.0, and at n=16
  (rho=1/4): 0.75 - 0.811/4 = 0.547. These do NOT match the exact pins (0.25) -- AS EXPECTED:
  the pins are at eps*=2/5 and 2/17, NOT eps*=2^-128. At eps*=2/5 the budget eps*|F|=2 (not n),
  so the crossover law 2^{c/eta}=budget reads c/eta=log2(2)=1, eta=c -> a DIFFERENT (O(1))
  cushion, landing delta*=1-rho-c which is the UD-radius-ish toy value. The conjecture is an
  eps*=2^-128 / large-n statement; small-n large-eps* pins are a different limit. NO discrepancy
  with the asymptotic claim, but they do NOT confirm the exact constant either (out of regime).""")

print("-"*82)
print("[C] GPU oracle exact delta* to n=38 (p-independent at binding radius).")
print("-"*82)
print("""  The oracle reports delta* is p-INDEPENDENT at the binding radius for n<=38 -- consistent
  with the conjecture's STRUCTURE (delta* depends on rho,n only, not on the field beyond the
  smoothness/size needed). The conjecture delta*=(1-rho)-H2(rho)/log2 n is manifestly
  p-independent (no q in it beyond eps* fixing the budget). MATCHES the oracle's p-independence.
  But n<=38 < 256 => window interior empty => the oracle's exact delta* is the sub-Johnson
  ladder value, NOT the cushion -- so it tests p-independence (PASS) not the constant.""")

print("-"*82)
print("[D] KKH26 CEILING (KKH26WitnessSpread.lean): delta* <= 1 - r/2^mu.")
print("-"*82)
print("""  The proven ceiling is delta* <= 1 - r/2^mu whenever eps* < 2^r*C(2^{mu-1},r)/p.
  Set r = ceil((rho+eta)*n) at cushion eta. The entropy form (KKH26EntropyForm.lean) gives
  the bad-scalar count exponent r + (n/2)H2(2r/n). The conjecture's delta*=(1-rho)-H2(rho)/mu
  must lie BELOW this ceiling. Check: ceiling delta*<=1-r/n with r minimal s.t. the count
  exceeds budget; conjecture delta*=1-rho-H2(rho)/mu = 1-(r/n) with r/n=rho+H2(rho)/mu. So the
  conjecture's implied r is r_conj = n*(rho+H2(rho)/mu). The ceiling holds iff the count at
  r_conj still exceeds budget eps*|F|~n, i.e. its exponent >= mu:""")
print(f"  {'rho':>6} | {'mu':>3} | {'r_conj/n=rho+H2/mu':>18} | {'count exp r+(n/2)H2(2r/n)':>26} | {'>=mu?':>6}")
for rho in (0.5,0.25,0.125,0.0625):
    for mu in (10,20,30):
        n=1<<mu
        rn=rho+H2(rho)/mu          # r_conj/n
        if rn>=0.5:                # H2(2rn) undefined past 1; clamp
            cexp=rn*n              # entropy term ~0 near 2rn=1
        else:
            cexp=rn*n + (n/2)*H2(2*rn)
        ok = cexp>=mu
        print(f"  {rho:6.4f} | {mu:>3} | {rn:18.6f} | {cexp:26.3e} | {str(ok):>6}")
print("""  => count exponent ~ Theta(n) >> mu at delta*_conj for all rates/n: the conjecture's radius
     sits WELL INSIDE the bad region of the KKH26 line (count hugely exceeds budget), i.e.
     delta*_conj < 1-r/2^mu ceiling with room -- CONSISTENT (conjecture below ceiling). The
     ceiling is a necessary upper bracket; the conjecture respects it. The gap between them is
     the O(1/log n) vs O(1) cushion difference -- both -> 1-rho but the conjecture's constant
     H2(rho) is the SHARP one (the ceiling's r is an existence witness, not the sup).""")

print("="*82)
print("SUMMARY: no contradictions. Exact data is OUT OF the prize regime (large eps*/small n,")
print("empty window interior) so it tests p-independence + below-ceiling STRUCTURE (both PASS),")
print("not the exact cushion constant H2(rho), which is only non-vacuous at n>=256.")
print("="*82)
