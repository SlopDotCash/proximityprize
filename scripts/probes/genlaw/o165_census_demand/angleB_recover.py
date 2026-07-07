# Angle B recovery: given a bad gamma, can we CANONICALLY recover a signed r-subset of mu_{n/2}?
#
# The pinned codeword. Deep band r: agreement a0=r+1, codeword deg k=r-1, deficit 2.
# On the r+1 points of S, line (x^e, x^f) means values (z^e, z^f). A "bad" S is one where
# there is a single scalar gamma s.t. u0 + gamma*u1 = z^e + gamma z^f agrees with a deg-(k=r-1)
# polynomial Q on all r+1 = a0 points S. I.e. the (r+1) values g(z) = z^e + gamma z^f for z in S
# lie on a degree-<=(r-1) polynomial.  An (r+1)-tuple of values lies on a deg-<=(r-1) poly iff
# the (r-1+1)=r-th and (r)-th finite-difference / the top 2 interpolation coeffs vanish... but
# here only ONE relation (the bilinear V) because gamma is free. The leading-coeff condition
# is exactly: [the deg-r coeff of interpolant] = 0, giving V, and gamma pins it.
#
# CLAIM to test: a bad S with scalar gamma yields a polynomial
#     F_gamma(X) = X^e + gamma X^f   restricted ... no.
# Better: the (r+1) points z in S satisfy that the divided differences of order r of
# (z |-> z^e + gamma z^f) vanish over S. With S = {z_0..z_r}, the order-r divided difference
# of x^j over nodes = h_{j-r}(S) (complete homogeneous!). So
#   DD_r(z^e + gamma z^f) = h_{e-r}(S) + gamma h_{f-r}(S) = 0   <=> gamma = -h_{e-r}/h_{f-r}.  [exact]
# And the order-(r) one being the relevant 'deficit-1'; deficit 2 needs ALSO order r-1? No:
# agreement r+1 with deg r-1 means TWO top divided differences vanish (orders r-1 and r? no).
# Points count r+1, poly deg r-1 => need value-vector in a codim-2 space => 2 conditions:
#   DD_r = 0  AND  DD_{r-1} ... Actually a deg<=(r-1) poly through r+1 nodes: the interpolant of
#   degree <= r has top coeff DD_r; requiring deg <= r-1 is DD_r = 0 (ONE condition). deg r-1
#   through r+1 nodes is generically NO solution unless 1 condition; but we have a free gamma to
#   spend, so net 0 conditions => a variety. Wait: r+1 nodes, value = z^e+gamma z^f (1 free param
#   gamma), require interpolant deg <= r-1  => DD_r(values)=0 is ONE eqn in gamma+S. Solvable for
#   gamma generically (1 eqn, 1 unknown gamma) => so EVERY S is "bad" for SOME gamma?! No --
#   that's the deficit-1 (deg<=r) story. DEFICIT 2 = deg <= r-1 wait k=r-1, a0=r+1, so
#   deg k = r-1, nodes r+1, gap = (r+1)-(r-1) = 2. Need interpolant deg <= r-1 => BOTH
#   DD_r = 0 AND DD_{r-1}=0? No: deg<=r-1 <=> coeff of X^r = 0, that's DD_r=0 only (interp deg<=r).
#   To force deg<=r-1 from r+1 nodes you need the deg-r interpolant to actually be deg<=r-1,
#   i.e. its X^r coeff DD_r = 0. That's ONE condition. Then it's automatically deg<=r-1. With one
#   free gamma => 1 eqn 1 unknown => gamma pinned, ALWAYS solvable. Contradiction with V being a
#   nontrivial variety. RESOLUTION: the bilinear V uses h_{e-r} AND h_{e-r+1} (two consecutive),
#   i.e. TWO divided differences (orders r and r-1). So deficit 2 = DD_r=0 AND DD_{r-1}=0 with the
#   SAME gamma:  h_{e-r}+gamma h_{f-r}=0  AND  h_{e-r+1}+gamma h_{f-r+1}=0.  Eliminating gamma
#   gives V (the 2x2 determinant), and gamma=-h_{e-r}/h_{f-r}. GOOD -- now it is codim 1. CONFIRMED.
#
# So: bad S <=> the two divided differences DD_r, DD_{r-1} of (z^e + gamma z^f) over S vanish
# simultaneously => g(z)=z^e+gamma z^f agrees with a polynomial of degree <= r-2 on S?? Let's
# just verify and, crucially, identify the deg-(r-1) (or r-2) interpolant whose ROOTS or
# coefficients give a signed r-subset.

from math import comb, gcd
from itertools import combinations
from collections import Counter

p = 2013265921
def inv(x): return pow(x, p-2, p)

def mu_n(n):
    e = (p-1)//n
    for c in range(2,400):
        h = pow(c,e,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1:
            return [pow(h,i,p) for i in range(n)]
    raise RuntimeError

def h_ps(elts, mmax):
    L=len(elts); P=[L%p]+[0]*mmax; cur=[1]*L
    for i in range(1,mmax+1):
        s=0
        for j in range(L):
            cur[j]=(cur[j]*elts[j])%p; s+=cur[j]
        P[i]=s%p
    H=[1]+[0]*mmax
    for m in range(1,mmax+1):
        acc=0
        for i in range(1,m+1): acc=(acc+P[i]*H[m-i])%p
        H[m]=(acc*inv(m))%p
    return H

def interp_coeffs(pts, vals):
    m=len(pts)
    M=[[pow(pts[i],j,p) for j in range(m)]+[vals[i]%p] for i in range(m)]
    for col in range(m):
        piv=next((rr for rr in range(col,m) if M[rr][col]%p!=0),None)
        if piv is None: return None
        M[col],M[piv]=M[piv],M[col]
        iv=inv(M[col][col]); M[col]=[(v*iv)%p for v in M[col]]
        for rr in range(m):
            if rr!=col and M[rr][col]%p!=0:
                fc=M[rr][col]; M[rr]=[(M[rr][k]-fc*M[col][k])%p for k in range(m+1)]
    return [M[i][m]%p for i in range(m)]

def study(n, r, e, f):
    dom = mu_n(n)
    a = r+1
    me, mf, me1, mf1 = e-r, f-r, e-r+1, f-r+1
    mmax = max(me,mf,me1,mf1)
    fib = {}
    for S in combinations(range(n), a):
        elts=[dom[i] for i in S]
        H=h_ps(elts, mmax)
        he,hf,he1,hf1 = H[me],H[mf],H[me1],H[mf1]
        if (he*hf1-hf*he1)%p: continue
        if hf%p==0: continue
        g=(-he*inv(hf))%p
        if g==0: continue
        fib.setdefault(g, []).append(tuple(S))
    return fib, dom

if __name__ == "__main__":
    # Take r=4 n=16 where some gammas have fiber 2: inspect the deg-(r-1) interpolant Q
    # of g(z)=z^e+gamma z^f over S. Does Q (deg r-1) factor with roots related to mu_{n/2}?
    n=16; r=4; e,f = n//2+2, n//4+1   # x^10, x^5
    fib, dom = study(n,r,e,f)
    print(f"n={n} r={r} line(x^{e},x^{f}): #gamma={len(fib)}; fiberdist={dict(sorted(Counter(len(v) for v in fib.values()).items()))}")
    # for the fiber-size-2 gammas, are the two subsets antipodal images of each other (z->-z)?
    neg1 = dom[n//2]
    idx={dom[i]:i for i in range(n)}
    fib2 = {g:v for g,v in fib.items() if len(v)==2}
    print(f"#fiber-2 gammas: {len(fib2)}")
    cnt_antipodal=0; cnt_other=0
    for g,(S1,S2) in fib2.items():
        negS1 = tuple(sorted(idx[(dom[i]*neg1)%p] for i in S1))
        if negS1 == tuple(sorted(S2)): cnt_antipodal+=1
        else: cnt_other+=1
    print(f"  fiber-2 where S2 = -S1 (global negation): {cnt_antipodal}, other: {cnt_other}")
    # Examine the interpolant degree of g over S for a fiber-2 gamma
    for g,(S1,S2) in list(fib2.items())[:2]:
        for S in (S1,S2):
            pts=[dom[i] for i in S]; vals=[(pow(dom[i],e,p)+g*pow(dom[i],f,p))%p for i in S]
            c=interp_coeffs(pts,vals)
            deg = max([j for j in range(len(c)) if c[j]],default=-1)
            print(f"  gamma={g} S={S}: interpolant deg={deg} coeffs(top)={c}")
