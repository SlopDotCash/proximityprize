"""#466 RIGHT-SIDE diagnostic: does the DYADIC subgroup structure help bound max_b|eta_b|,
or does mu_n behave like a random set of the same size?
Compare max_b |sum_{x in S} e_p(bx)| for:
  (A) dyadic subgroup mu_n
  (B) random n-subset of F_p
  (C) random SYMMETRIC (+-closed) n-subset (matches mu_n's negation closure)
  (D) a random multiplicative-subgroup-sized GEOMETRIC-progression-free set (control)
If (A) << (B),(C): structure helps -> build a dyadic tool. If (A) ~ (C): only the negation
symmetry matters, no special dyadic gain."""
import cmath, math, random
random.seed(12345)  # deterministic (no Math.random equiv issue; this is a probe)
def is_prime(n):
    if n<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n%q==0: return n==q
    d,r=n-1,0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True
def prime_ge_2adic(lo,m):
    t=max(1,(lo-1+m-1)//m)
    while True:
        p=m*t+1
        if p>=lo and is_prime(p): return p
        t+=1
def primitive_root(p):
    n=p-1; fac=set(); d=n; f=2
    while f*f<=d:
        while d%f==0: fac.add(f); d//=f
        f+=1
    if d>1: fac.add(d)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac): return g
def subgroup(p,order):
    g=primitive_root(p); h=pow(g,(p-1)//order,p)
    S=[]; x=1
    for _ in range(order): S.append(x); x=x*h%p
    return S
def maxeta(p,S):
    best=0.0
    for b in range(1,p):
        z=sum(cmath.exp(2j*math.pi*(b*x%p)/p) for x in S)
        best=max(best,abs(z))
    return best
def rand_subset(p,n):
    return random.sample(range(1,p),n)
def rand_symmetric(p,n):
    # n even: pick n/2 elements, add negatives
    half=set()
    while len(half)<n//2:
        x=random.randrange(1,p)
        if (p-x)%p not in half and x not in half: half.add(x)
    S=list(half)+[(p-x)%p for x in half]
    return S
for k in (4,5,6):
    n=1<<k; p=prime_ge_2adic(n**4,n)
    if p>2_000_000: print(f"n={n} p={p} skip"); continue
    A=maxeta(p,subgroup(p,n))
    Bs=[maxeta(p,rand_subset(p,n)) for _ in range(5)]
    Cs=[maxeta(p,rand_symmetric(p,n)) for _ in range(5)]
    tgt=math.sqrt(n*math.log(p/n))
    print(f"n={n:3d} p={p:8d} sqrt(n ln(p/n))={tgt:.2f}")
    print(f"   (A) dyadic subgroup : {A:.3f}   (A/tgt={A/tgt:.3f})")
    print(f"   (B) random subset   : mean {sum(Bs)/len(Bs):.3f} min {min(Bs):.3f} max {max(Bs):.3f}")
    print(f"   (C) random symmetric: mean {sum(Cs)/len(Cs):.3f} min {min(Cs):.3f} max {max(Cs):.3f}")
