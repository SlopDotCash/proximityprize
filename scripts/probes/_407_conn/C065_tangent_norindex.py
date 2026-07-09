"""
C065 second leg: the tangent sum T_h has NO r-index, so "T_h crosses char-0
at (2r)^{phi(n)}=p" is not well-typed.  We pin this down:

 1) Compute max_h |T_h| EXACTLY at proper-subgroup primes and compare to the
    char-0 / Jacobi-equidistributed prediction.  The claim is that T_h's
    char-p value = char-0 value UNLESS a spurious tuple exists mod p.
    A 'spurious tuple' is an r-indexed object; T_h is not.  We test whether
    there is ANY r such that the appearance of an energy defect (r_E) lines up
    with T_h leaving char-0.

 2) The 'char-0 Jacobi value' of T_h.  Via I4 (proven in tree):
    T(phi) = (1/m) sum_{i<m} J(chi^i, phi),  m = orderOf chi.
    The char-0 (Deligne-Katz) heuristic is |J(a,b)| = sqrt(p) for generic
    nontrivial a,b,ab.  So |T(phi)| ~ (1/m) * m * sqrt(p) at worst = sqrt(p)
    if Jacobi phases ALIGNED, or ~ sqrt(p)/sqrt(m) = sqrt(p)/sqrt(m) if they
    are RANDOM (sqrt cancellation).  There is NO 'char-0 exact value' that T_h
    leaves at a finite threshold: T_h is ALWAYS a char-p object (Jacobi sums
    only exist mod p).  This is the conceptual flaw: T_h has no archimedean /
    char-0 incarnation analogous to E_r^{(0)}.

 We just report the numbers to make the conceptual point concrete.
"""
import math, cmath, sys
import sympy

def primitive_root(p):
    phi=p-1; temp=phi; fac=[]; d=2
    while d*d<=temp:
        if temp%d==0:
            fac.append(d)
            while temp%d==0: temp//=d
        d+=1
    if temp>1: fac.append(temp)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in fac):
            return g
    raise RuntimeError

def subgroup(n,p):
    g=primitive_root(p); h=pow(g,(p-1)//n,p)
    S=[]; x=1
    for _ in range(n): S.append(x); x=(x*h)%p
    return S,g

def dlogtable(p,g):
    d={}; x=1
    for e in range(p-1): d[x]=e; x=(x*g)%p
    return d

def tangent_all(n,p):
    """For ker chi = mu_n (order n subgroup), compute |T(phi)| for ALL phi=chi_j,
       return (max, argmax j, list of all)."""
    S,g=subgroup(n,p); dl=dlogtable(p,g)
    res=[]
    for j in range(p-1):
        T=0+0j
        for w in S:
            t=(1-w)%p
            if t==0: continue
            T+=cmath.exp(2j*math.pi*j*dl[t]/(p-1))
        res.append((abs(T),j))
    res.sort(reverse=True)
    return res

def jacobi(p, g, dl, a, b):
    """J(chi_a, chi_b) = sum_{x} chi_a(x) chi_b(1-x), chi_j(x)=e^{2pi i j dlog x/(p-1)}."""
    J=0+0j
    for x in range(2,p):  # x!=0,1 ; chi(0)=0
        if x==1: continue
        one_minus=(1-x)%p
        if one_minus==0: continue
        J+=cmath.exp(2j*math.pi*(a*dl[x]+b*dl[one_minus])/(p-1))
    return J

def main():
    print("=== max_h |T_h| at proper-subgroup primes (ker chi = mu_n) ===")
    print("    (T_h is a SINGLE scalar per (phi); NO r-index exists)\n")
    for n in [8,16,32]:
        # one prime ~ n^4
        lo=int(n**4); k=max(2,(lo-1)//n);
        while True:
            p=1+k*n
            if sympy.isprime(p): break
            k+=1
        res=tangent_all(n,p)
        mx,jmx=res[0]
        print(f"  n={n} p={p}: max_phi|T| = {mx:.4f}   sqrt(p)={math.sqrt(p):.2f}"
              f"   sqrt(p)/sqrt(m) where m=(p-1)/n = {math.sqrt(p)/math.sqrt((p-1)/n):.3f}"
              f"   sqrt(n)={math.sqrt(n):.3f}")
    print("\n=== Does T_h have a char-0 'exact value' it 'leaves'? ===")
    print("  T(phi)=(1/m) sum_i J(chi^i,phi). Jacobi sums |J|=sqrt(p) EXACT (Weil),")
    print("  ALWAYS, with no clean range -- there is no finite-r threshold below")
    print("  which J equals a 'char-0 integer value'.  Confirm |J|=sqrt(p):")
    n=8; lo=int(n**3); k=max(2,(lo-1)//n)
    while True:
        p=1+k*n
        if sympy.isprime(p): break
        k+=1
    S,g=subgroup(n,p); dl=dlogtable(p,g)
    for (a,b) in [(1,1),(1,2),(2,3),(1,3)]:
        J=jacobi(p,g,dl,a,b)
        print(f"    p={p}: |J(chi^{a},chi^{b})|={abs(J):.4f}  sqrt(p)={math.sqrt(p):.4f}")

if __name__=="__main__":
    main()
