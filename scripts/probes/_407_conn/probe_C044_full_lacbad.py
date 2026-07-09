"""
C044 follow-up: FULL lacBad over the ENTIRE vanishing variety (not just coset-unions),
to test the two C044 cardinality assertions DIRECTLY at proper-subgroup primes:

  lacBad(mu_n, a, t) = { e_t(S) : S subset mu_n, |S|=a, e_1(S)=...=e_{t-1}(S)=0 }.

C044 claims:  #lacBad <= n/gcd(t,n) <= n.

Prize-regime window direction: (a,b)=(k+t,k), t = smallest live gap.  We enumerate ALL
a-subsets of mu_n (n=8,16 feasible) with e_1=...=e_{t-1}=0 and collect e_t values.
Exact mod q. We also check: is lacBad a union of cosets of <g^t> (coset-quantization)?
"""
import itertools

def isprime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    d = 3
    while d*d <= n:
        if n % d == 0: return False
        d += 2
    return True

def all_esymm_poly(vals, q):
    poly = [1]
    for x in vals:
        new = [0]*(len(poly)+1)
        for i,c in enumerate(poly):
            new[i]   = (new[i]   + c*(-x)) % q
            new[i+1] = (new[i+1] + c) % q
        poly = new
    return poly

def esymm(poly, t, q, N):
    return (pow(-1, t, q) * poly[N-t]) % q

def find_prime(n, beta=4):
    target = n**beta
    q = target - (target % n) + 1
    while not (isprime(q) and (q-1) % n == 0):
        q += n
    return q

def gen_unit(q):
    m=q-1; facs=set(); mm=m; d=2
    while d*d<=mm:
        while mm%d==0: facs.add(d); mm//=d
        d+=1
    if mm>1: facs.add(mm)
    for h in range(2,q):
        if all(pow(h,m//p,q)!=1 for p in facs): return h
    raise RuntimeError

def full_lacbad(n, a, t, beta=4):
    q = find_prime(n, beta)
    g = pow(gen_unit(q), (q-1)//n, q)
    mu = [pow(g, i, q) for i in range(n)]
    vals = set()
    nS = 0
    for S in itertools.combinations(mu, a):
        poly = all_esymm_poly(S, q)
        # check e_1..e_{t-1} = 0
        ok = all(esymm(poly, j, q, a) == 0 for j in range(1, t))
        if ok:
            nS += 1
            vals.add(esymm(poly, t, q, a))
    # coset quantization check: is vals closed under mult by g^t? order of g^t = n/gcd(t,n)
    from math import gcd
    ord_gt = n // gcd(t, n)
    gt = pow(g, t % n, q)
    closed = all(((v*gt) % q) in vals for v in vals)
    return dict(n=n,a=a,t=t,q=q,n_variety=nS,lacBad=len(vals),
                bound_n_over_gcd=ord_gt, n_val=n,
                coset_closed=closed,
                is_multiple_of_ord=(len(vals)%ord_gt==0) if ord_gt else None,
                exceeds_n=(len(vals)>n))

if __name__=="__main__":
    # window-interior directions: a = k+t with t = smallest live gap.
    # Test (n,a,t) where t<n (proper smallest gap), a between t and n.
    cases = [
        (8,2,2),(8,3,2),(8,4,2),(8,5,2),(8,6,2),
        (8,4,4),(8,5,4),(8,6,4),
        (16,2,2),(16,3,2),(16,4,2),(16,5,2),(16,6,2),
        (16,4,4),(16,5,4),(16,6,4),(16,8,4),
    ]
    print(f"{'n':>3}{'a':>3}{'t':>3}{'q':>10} | #variety  #lacBad  bound(n/gcd)  n  | coset_closed  mult_of_ord  exceeds_n?")
    for (n,a,t) in cases:
        r = full_lacbad(n,a,t)
        print(f"{r['n']:>3}{r['a']:>3}{r['t']:>3}{r['q']:>10} | {r['n_variety']:>7}  {r['lacBad']:>6}  {r['bound_n_over_gcd']:>10}  {r['n_val']:>3} | "
              f"{str(r['coset_closed']):>10}  {str(r['is_multiple_of_ord']):>9}  {str(r['exceeds_n'])}")
