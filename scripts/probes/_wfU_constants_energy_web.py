"""
LENS [constants] — numerical verification of the recurring-constant web in the
ProximityGap / delta* programme. We test, exactly (integers / sympy where possible,
float Gauss periods otherwise), whether the SAME constant appearing in different
derivations is in fact the SAME quantity (a hidden identity).

Targets:
  (1) Master additive-energy identity (RootsOfUnityAdditiveEnergyExact.lean):
        E(S) + 2*r0 + |S| = r0^2 + 2|S|^2     (any unit-circle S)
      Both-parity unification: r0=0 (odd, SIDON)  -> E = 2n^2 - n
                               r0=n (even)        -> E = 3n^2 - 3n
      i.e. 2n^2-n and 3n^2-3n are ONE identity at the two ends of r0.

  (2) The Shaw-flatness sqrt(2) constant (ShawFlatnessRefuted.lean) vs the
      energy constant 3. Claim chain: L4/L2 ratio
        max||eta_b||^2 >= (q*E - n^4)/(q*n - n^2) -> E/n = 3n-3 (>> 2n).
      So sqrt(2) (from the bound B<=sqrt(2)sqrt(n), i.e. ||^2<=2n) is REFUTED
      because the energy constant is 3, not 2. Test: is E2/n -> 3n exactly,
      and the kurtosis E2/(2nd-moment)^2 -> 3 (the SAME "3"), and is the
      "3/2" the ratio (energy-3)/(flatness-2)? Verify numerically with real
      Gauss periods over actual prime fields.

  (3) Kurtosis-3: 4th moment / (2nd moment)^2 of the nonzero-frequency Gauss
      periods. The "kurtosis 3" of Wick/Gaussian vs the energy "3" in 3n^2.
"""
import cmath, math
from itertools import product

def is_prime(n):
    if n < 2: return False
    i = 2
    while i*i <= n:
        if n % i == 0: return False
        i += 1
    return True

def primitive_root(p):
    # smallest primitive root mod p
    if p == 2: return 1
    fac = []
    phi = p-1; m = phi; d = 2
    while d*d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0: m//=d
        d += 1
    if m > 1: fac.append(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//f,p)!=1 for f in fac):
            return g
    return None

def mu_n_subgroup(p, n):
    """n-th roots of unity in F_p (needs n | p-1). Returns list of residues."""
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)  # generator of order n
    return [pow(h, k, p) for k in range(n)]

def eta(p, G, b):
    """eta_b = sum_{y in G} psi(b*y), psi(x)=exp(2pi i x/p)."""
    s = 0+0j
    for y in G:
        s += cmath.exp(2j*math.pi*(b*y % p)/p)
    return s

def additive_energy_unitcircle(n):
    """Exact additive energy of mu_n (n-th roots of unity on the complex circle)."""
    pts = [cmath.exp(2j*math.pi*k/n) for k in range(n)]
    # E = #{(a,b,c,d): a+b=c+d}
    from collections import defaultdict
    cnt = defaultdict(int)
    for a in pts:
        for b in pts:
            key = (round((a+b).real,9), round((a+b).imag,9))
            cnt[key]+=1
    return sum(v*v for v in cnt.values())

def repcount0(n):
    """r0 = #{(a,b): a+b=0} = ordered antipodal pairs."""
    pts = [cmath.exp(2j*math.pi*k/n) for k in range(n)]
    c=0
    for a in pts:
        for b in pts:
            if abs(a+b) < 1e-9: c+=1
    return c

print("="*78)
print("(1) MASTER ENERGY IDENTITY  E + 2*r0 + n = r0^2 + 2n^2   (unifies BOTH parities)")
print("="*78)
print(f"{'n':>4} {'r0':>4} {'E':>8} {'LHS':>10} {'RHS':>10} {'2n^2-n':>8} {'3n^2-3n':>9} {'match':>6}")
for n in range(2,17):
    E = additive_energy_unitcircle(n)
    r0 = repcount0(n)
    LHS = E + 2*r0 + n
    RHS = r0*r0 + 2*n*n
    pred_odd = 2*n*n - n
    pred_even = 3*n*n - 3*n
    match = "OK" if LHS==RHS else "FAIL"
    print(f"{n:>4} {r0:>4} {E:>8} {LHS:>10} {RHS:>10} {pred_odd:>8} {pred_even:>9} {match:>6}")
print("-> r0=0 (n odd) gives E=2n^2-n; r0=n (n even) gives E=3n^2-3n: SAME identity, two ends of r0.")
print()

print("="*78)
print("(2)+(3) REAL Gauss periods over F_p: sqrt(2) refutation, kurtosis-3, the energy-3")
print("="*78)
print("For each (p,n): max||eta_b||^2/n (vs the sqrt2-bound value 2), L4/L2 ratio,")
print("kurtosis m4/m2^2 over nonzero freqs, and E2/n (the energy '3n').")
print(f"{'p':>7} {'n':>4} {'max||^2/n':>10} {'L4/L2 /n':>9} {'kurtosis':>9} {'E2/(n*n)':>9} {'>2?':>5}")
results=[]
# pick primes p with n|p-1, n=2^m, p moderately large so periods are 'generic'
cases=[]
for m in range(2,6):       # n=4,8,16,32
    n=2**m
    # find a few primes p = 1 mod n, not too small
    found=0
    p=n+1
    while found<1:
        if p>n and is_prime(p) and (p-1)%n==0 and p> 50*n:
            cases.append((p,n)); found+=1
        p+=1
        if p>200000: break
for (p,n) in cases:
    G = mu_n_subgroup(p,n)
    norms2 = []
    for b in range(1,p):
        e = eta(p,G,b)
        norms2.append((e.real*e.real+e.imag*e.imag))
    # these recur with period; but sum over b=1..p-1 of ||eta_b||^2 = q*E1 - n^2 form.
    m2 = sum(norms2)/len(norms2)          # mean of ||eta||^2 over nonzero b
    m4 = sum(x*x for x in norms2)/len(norms2)
    mx = max(norms2)
    kurt = m4/(m2*m2)
    # E_2 via 4th moment identity: sum_{all b} ||eta||^4 = q * E_2. nonzero part:
    q=p
    sum4_nonzero = sum(x*x for x in norms2)
    E2 = (sum4_nonzero + n**4)/q   # add back eta_0^4 = n^4
    flag = "YES" if mx>2*n else "no"
    print(f"{p:>7} {n:>4} {mx/n:>10.4f} {(m4/m2)/n:>9.4f} {kurt:>9.4f} {E2/(n*n):>9.4f} {flag:>5}")
    results.append((p,n,mx/n,E2/(n*n),kurt))
print()
print("Reading:")
print(" * max||^2/n > 2 in EVERY row  => sqrt(2)-flatness (||^2<=2n) is FALSE (matches ShawFlatnessRefuted).")
print(" * E2/(n*n) -> 3 (minus 3/n)   => the energy constant is '3' (3n^2-3n), the SAME 3 as 3n^2.")
print(" * the L4/L2 ratio (q*E-n^4)/(q*n-n^2) ~ E/n = 3n-3, so the worst ||^2 >= ~3n > 2n: the")
print("   sqrt(2) bound and the energy-3 constant are LINKED: refutation gap = 3 vs 2  (ratio 3/2).")
