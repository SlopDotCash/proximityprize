"""
C082 follow-up: pin the mechanism of the c>=4 variance.
Two questions:
 (1) Is the c-subset count root-of-unity-generator independent (same for every primitive g)?
     -> if yes, it's a genuine subgroup invariant (not a g-choice artifact).
 (2) For c<=3, is the count = classical full-field quadric prediction, or the FORCED
     symmetric-function vanishing (coset/F15)?  Distinguish: the classical 1-var/2-var/3-var
     quadric S^2=-Q over FREE F_q variables has a q-DEPENDENT point count ~ q^{c-1}.
     The mu_n-restricted count is O(n^?). Compare the two.
 (3) Does the c>=4 count match what a classical quadric on a (c)-dim torus would predict
     (q-independent), or the partial-character-sum / BGK quantity (q,prime-arithmetic dependent)?
"""
import itertools, math

def is_prime(x):
    if x<2: return False
    i=2
    while i*i<=x:
        if x%i==0: return False
        i+=1
    return True

def subgroup_primes(n,count):
    out=[]; lo=max(n*n*4,n+1); q=lo-(lo%n)+1
    while len(out)<count and q<lo*500:
        if is_prime(q) and q%n==1: out.append(q)
        q+=n
    return out

def all_primitive_roots(q,n):
    roots=[]
    for cand in range(2,q):
        g=pow(cand,(q-1)//n,q)
        if g==1: continue
        y=g; o=1
        while y!=1:
            y=(y*g)%q; o+=1
            if o>n: break
        if o==n and g not in roots:
            roots.append(g)
    return roots

def mu_elts(g,n,q):
    out=[]; x=1
    for _ in range(n):
        out.append(x); x=(x*g)%q
    return out

def count_c(g,n,q,c):
    elts=mu_elts(g,n,q); sq=[(e*e)%q for e in elts]
    cnt=0
    for T in itertools.combinations(range(n),c):
        S=sum(elts[i] for i in T)%q
        Q=sum(sq[i] for i in T)%q
        if (S*S)%q==(-Q)%q: cnt+=1
    return cnt

print("="*70)
print("(1) generator-independence of the c-subset count (n=32, c=4,5)")
print("="*70)
n=32
for q in subgroup_primes(n,3):
    roots=all_primitive_roots(q,n)[:6]
    for c in [4,5]:
        vals=[count_c(g,n,q,c) for g in roots]
        print(f"  q={q} c={c}: over {len(roots)} primitive roots -> {vals}  "
              f"{'generator-INDEPENDENT' if len(set(vals))==1 else 'depends on g!'}")

print()
print("="*70)
print("(2) classical FREE-VARIABLE quadric vs mu_n-restricted count")
print("    classical c-var quadric S^2=-Q over F_q^c free vars: count ~ q^{c-1}(1+O(1/sqrt q))")
print("    (q-DEPENDENT, ~q^{c-1}).  mu_n count is O(n^{c-1})-ish & we test q-dependence.")
print("="*70)
n=16
for c in [3,4,5]:
    print(f"  c={c}:")
    for q in subgroup_primes(n,4):
        g=all_primitive_roots(q,n)[0]
        cnt=count_c(g,n,q,c)
        # classical free-variable quadric point-count over F_q^c (nondegenerate) ~ q^{c-1}
        classical=q**(c-1)
        print(f"    q={q:>6}: mu_n-count={cnt:>4}   classical-free-var~q^{c-1}={classical:>12}   "
              f"ratio mu/classical={cnt/classical:.2e}")

print()
print("="*70)
print("(3) does the c>=4 count track a SUBGROUP-ARITHMETIC quantity (prime-dependent)?")
print("    report c=4,5 counts vs q mod small structure; show NON-constancy is real,")
print("    not a finite-size fluke, by scanning many primes.")
print("="*70)
for n in [32, 64]:
    print(f"  n={n}:")
    seen={}
    for q in subgroup_primes(n,8):
        g=all_primitive_roots(q,n)[0]
        c4=count_c(g,n,q,4)
        c5=count_c(g,n,q,5) if n>=32 else None
        print(f"    q={q:>7}: c=3->{count_c(g,n,q,3):>4}  c=4->{c4:>5}  c=5->{c5}")
