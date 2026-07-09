"""
C047 refinement: the max/avg ratio over the LINE FAMILY (not per-scalar).

The connection claims:  tabulate avg vs MAX line incidence over PRIMITIVE
MONOMIAL DIRECTIONS, confirm max/avg -> infinity.

Object: a "line" is {f + gamma g : gamma in F_q} for a fixed direction g and
base f.  The incidence I(line) = total list mass over the line =
  sum_{gamma} |Lambda(gamma, a)|  =  sum_{gamma} #{c in C : agree(line(gamma), c) >= a}.
By the in-tree line_first_moment_bound this equals (Fubini) sum_{c in C} #{gamma :
agree >= a}, each term <= n/a, so  I(line) <= |C|*n/a  for EVERY line (worst case).

We measure, over a family of monomial directions g(i) = i^e (and bases f), the
DISTRIBUTION of I(line) at an interior radius, and report:
  - avg I over the family
  - max I over the family
  - max/avg
to test whether the worst line is a rare outlier (max/avg large) or typical
(max/avg ~ 1).  Exact integer arithmetic, proper-subgroup primes.

We use the constant code C = {constant words} (|C| = q) so agreement of a line
point with a codeword c=(a,...,a) = # coords i with line(gamma)(i) = a, and
|Lambda(gamma,a_thr)| = #{constants hit >= a_thr times} = #values taken >= a_thr
times by the vector (line(gamma)(i))_i.
"""
from collections import Counter
from math import sqrt, log2

CASES = [(8,1009),(16,7681),(32,12289),(64,65537)]

def is_prime(m):
    if m<2: return False
    i=2
    while i*i<=m:
        if m%i==0: return False
        i+=1
    return True

print("="*100)
print("C047: max/avg of per-line total list-incidence over the monomial line family")
print("="*100)
for (n,q) in CASES:
    assert is_prime(q) and (q-1)%n==0
    # agreement threshold a: interior radius delta -> a = n - floor(delta n).
    # use a = ceil(n * (1 - delta)) with delta = (johnson+cap)/2, rho = 1/4.
    rho = 0.25; k = max(1,int(round(rho*n)))
    delta = ((1-sqrt(rho)) + (1-rho))/2
    a_thr = max(2, n - int(delta*n))      # need a>=2 else trivial
    # family of lines: base f(i)=0, directions g(i) = i^e for e in {1,..,n-1} with
    # gcd(e, ...) primitive monomial; plus a few random affine bases.
    Is = []
    bases = [ [0]*n, [ (i) % q for i in range(n)], [ (i*i)%q for i in range(n)] ]
    for e in range(1, n):
        g = [ pow(i, e, q) for i in range(n) ]
        if any(gi==0 for gi in g[1:]):    # need nowhere-zero direction (except i=0 base ok)
            # skip degenerate (the first-moment lemma needs g i != 0)
            continue
        for f in bases:
            I = 0
            for gamma in range(q):
                vals = Counter( (f[i] + gamma*g[i]) % q for i in range(n) )
                # list mass = # distinct values hit >= a_thr times (constant code)
                I += sum(1 for v,c in vals.items() if c >= a_thr)
            Is.append(I)
    if not Is:
        print(f"n={n} q={q}: no nowhere-zero monomial directions in range"); continue
    avg = sum(Is)/len(Is); mx = max(Is); mn = min(Is)
    # theoretical per-line worst-case ceiling from line_first_moment_bound:
    ceil_fm = q * n // a_thr   # |C|=q, M <= |C| n / a
    print(f"n={n:>3} q={q:>7} a_thr={a_thr:>2} #lines={len(Is):>4}  "
          f"avg_I={avg:>10.2f} max_I={mx:>6} min_I={mn:>4}  max/avg={mx/avg:>6.2f}  "
          f"firstMoment_ceiling(|C|n/a)={ceil_fm}")
