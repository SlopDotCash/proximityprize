"""
C088 v2 (fast): two SEPARATE diagnostics.

DIAGNOSTIC 1 (decisive for the connection's CONCLUSION):
  In the prize regime mu_n is a PROPER subgroup of F_q^* of size n=2^mu.
  The covering-transfer gadget's conclusion is "distinct sumset of <-2>-image
  = all of F_q". We test directly whether the n subgroup elements have an
  r-fold distinct sumset that covers F_q. With only n elements and q ~ n^4,
  the union of ALL subset sums has size <= 2^n << q for n=64. So covering is
  impossible in-regime: it is NOT a statement about mu_n in F_q at all.

DIAGNOSTIC 2 (the actual prize core, decoupled):
  Compute the BGK house B = max_b |sum_{y in mu_n} psi(b y)| using the
  mu-coset structure: B is constant on b-cosets bmu, and there are (q-1)/n
  cosets. Also report sqrt(n), 2sqrt(n). Then check whether the reduction
  Z[zeta_n] -> F_q being "injective on the dyadic sums" (the Res condition,
  AUTOMATIC for q == 1 mod n since zeta_n is a genuine root mod q) has any
  bearing on whether B is small. It does not: B varies wildly across fully-
  split primes that ALL satisfy the injectivity/Res condition trivially.
"""
import itertools, math, cmath

def is_prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    i = 3
    while i*i <= n:
        if n % i == 0: return False
        i += 2
    return True

def primes_one_mod_n(n, lo, hi, cap):
    out=[]; start=((lo-1)//n+1)*n+1; q=start
    while q<=hi and len(out)<cap:
        if is_prime(q): out.append(q)
        q+=n
    return out

def factorize(m):
    f=set(); d=2
    while d*d<=m:
        while m%d==0: f.add(d); m//=d
        d+=1
    if m>1: f.add(m)
    return f

def subgroup_mu_n(q,n):
    qm1=q-1; fac=factorize(qm1)
    def is_gen(g):
        return all(pow(g,qm1//p,q)!=1 for p in fac)
    g=2
    while not is_gen(g): g+=1
    h=pow(g,qm1//n,q)
    return [pow(h,i,q) for i in range(n)]

def house_B(q,mu):
    """B = max over coset reps b of |sum_{y in mu} exp(2pi i b y / q)|.
    B(b) depends only on the coset b*mu, so iterate over a transversal."""
    n=len(mu); twopi=2*math.pi
    muset=set(mu)
    seen=set(); best=0.0; argbest=None
    # precompute unit roots lazily via cmath
    for b in range(1,q):
        if b in seen:  # b already covered as part of a previous coset
            continue
        # mark the whole coset b*mu as seen
        cos=[(b*y)%q for y in mu]
        for c in cos: seen.add(c)
        s=0j
        for y in mu:
            s+=cmath.exp(twopi*1j*((b*y)%q)/q)
        m=abs(s)
        if m>best:
            best=m; argbest=b
    return best, argbest

print("="*92)
print("DIAGNOSTIC 1: covering-transfer CONCLUSION in the proper-subgroup prize regime")
print("="*92)
print(f"{'n':>4} {'q':>9} {'#all-subset-sums of mu_n mod q':>32} {'q':>10} {'covers F_q?':>12}")
print("-"*92)
for mu_exp in [3,4]:        # n=8,16 (2^n subsets feasible)
    n=2**mu_exp
    q=primes_one_mod_n(n, n**4, n**4+200*n, 1)[0]
    mu=subgroup_mu_n(q,n)
    sums=set()
    for r in range(n+1):
        for S in itertools.combinations(mu,r):
            sums.add(sum(S)%q)
    print(f"{n:>4} {q:>9} {len(sums):>32} {q:>10} {('YES' if len(sums)==q else 'NO'):>12}")
print("  => with only n=2^mu elements, #subset-sums <= 2^n << q ~ n^4 always.")
print("     The covering conclusion is VACUOUS / FALSE for mu_n inside F_q.")
print()

print("="*92)
print("DIAGNOSTIC 2: BGK house B across FULLY-SPLIT prize primes (all satisfy Res/injectivity)")
print("="*92)
print(f"{'n':>4} {'q':>9} {'beta':>6} {'B':>9} {'sqrt(n)':>8} {'2sqrt(n)':>9} {'B/sqrt(n)':>10}")
print("-"*92)
for mu_exp in [3,4,5]:      # n=8,16,32; keep q moderate so coset scan is OK
    n=2**mu_exp
    # use q ~ n^3..n^3.5 so q stays < ~3e5 for n=32 (scan q-1 ints, /n cosets)
    lo = n**3
    hi = min(n**4, lo + 4000*n)
    qs=primes_one_mod_n(n, lo, hi, 4)
    for q in qs:
        mu=subgroup_mu_n(q,n)
        B,_=house_B(q,mu)
        beta=math.log(q)/math.log(n)
        print(f"{n:>4} {q:>9} {beta:>6.2f} {B:>9.3f} {math.sqrt(n):>8.3f} {2*math.sqrt(n):>9.3f} {B/math.sqrt(n):>10.3f}")
print("  => All these q are == 1 mod n (fully split): zeta_n in F_q, the Res/")
print("     injectivity condition holds TRIVIALLY for every one of them, yet B")
print("     ranges over a band (well above 2sqrt(n) for thin mu_n). Injectivity")
print("     of the reduction is DECOUPLED from the prize quantity B.")
