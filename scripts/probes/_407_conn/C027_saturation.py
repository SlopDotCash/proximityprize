"""
C027 follow-up: confirm the FIELD CAP saturates in the prize regime.

When 3^half >> q (the actual prize: half=2^{mu-1} grows doubly-exp, q~n^beta poly),
the realized distinct-subset-sum count mod q is field-capped: it should approach q
as we sample more codes (coupon-collector toward full coverage of F_q, since the
signed-cube image of a generating set is essentially equidistributed).

We pick a SMALL prize-shaped prime so q itself is enumerable as a coverage target,
and sample a # of codes >> q to estimate coverage fraction count/q. If count/q -> 1
the field cap is the binding (operative) bound, confirming C027's framing.

Also: compare the realized count to the prize BUDGET. The MCA/far-count budget that
must be exceeded to threaten the prize is ~ q*eps* with eps*=2^-128, i.e. the bad
count must exceed q*2^-128 (tiny) OR for the 'covering = univ' route the count must
reach q (full covering). We report count vs q (covering) and count vs n (domain).
"""
import random

def is_prime(n):
    if n < 2: return False
    for p in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % p == 0: return n == p
    d=n-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x==1 or x==n-1: continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True

def find_prime_1_mod_n(n, lo):
    k=(lo-1)//n+1
    if k<1: k=1
    while True:
        q=k*n+1
        if q>=lo and is_prime(q): return q
        k+=1

def primitive_nth_root(q,n):
    cof=(q-1)//n
    for h in range(2,q):
        g=pow(h,cof,q)
        if g==1: continue
        if pow(g,n,q)!=1: continue
        if pow(g,n//2,q)!=1:  # order has the full 2-part; n=2^mu so this suffices
            return g
    raise RuntimeError("no root")

def coverage(g,q,half,samples,seed=7):
    rng=random.Random(seed)
    powers=[pow(g,i,q) for i in range(half)]
    seen=set()
    for _ in range(samples):
        s=0
        for i in range(half):
            d=rng.randint(0,2)
            if d==1: s+=powers[i]
            elif d==2: s-=powers[i]
        seen.add(s%q)
    return len(seen)

print("="*78)
print("C027 SATURATION: does the signed cube cover F_q (field cap binding)?")
print("="*78)
print(f"{'n':>4} {'mu':>3} {'q':>8} {'half':>5} {'3^half':>22} {'samples':>9} "
      f"{'distinct':>9} {'cov=cnt/q':>10}")
# small prize-shaped primes so q is an enumerable coverage target
cases = [
    (32, 5, 32),     # q ~ 2^5? pick smallest q==1 mod 32 above ~ small
    (64, 6, 64),
    (128,7,128),
]
for n,mu,lo_mult in cases:
    half=n//2
    # choose a deliberately SMALL q so coverage is observable (q ~ n^2..n^3 scale here,
    # purely to test the cube->F_q surjectivity mechanism; the prize q is even larger so
    # 3^half/q is even more extreme => cap binds even harder)
    q=find_prime_1_mod_n(n, n*n*4)   # q ~ 4 n^2, well below 3^half once n>=32
    g=primitive_nth_root(q,n)
    samples=min(50*q, 5_000_000)
    cnt=coverage(g,q,half,samples)
    print(f"{n:>4} {mu:>3} {q:>8} {half:>5} {3**half:>22} {samples:>9} "
          f"{cnt:>9} {cnt/q:>10.4f}")

print()
print("If cov=cnt/q -> 1.0, the signed cube SURJECTS onto F_q, so the realized")
print("subset-sum/covering count = q EXACTLY (field cap), not 3^half. Then:")
print("  covering count = q  =>  the §7/curve-decodability 'bad count = covering'")
print("  is the FULL FIELD q.  Budget to beat for prize threat: q*eps* (eps*=2^-128)")
print("  or 'covers univ' (=q).  count=q TRIVIALLY exceeds q*2^-128 and EQUALS q-covering.")
print("  => the bad count is NOT the obstruction; the obstruction is whether those")
print("     bad scalars are ACTUALLY bad (line-explainable & far) = the BGK/Paley wall,")
print("     which the subset-sum COUNT (this connection) does not touch.")
