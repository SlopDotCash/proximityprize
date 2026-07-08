# Probe: d=4 face on the QUINTIC kernel h=(x-a)(x-b)(x-c)^3 over F_q, q=13,29
# 1) fiber counts of h^e (e=(q-1)/4) are ~ q/4 per class
# 2) identity h^e = r^e * s^{(q-1)/2} pointwise (r=radical, s=L3)
# 3) brute-force DBlockIndependence F 4 q D h at tiny D,q: no nontrivial relation
#    sum_t h^{te} * A_t(X, X^q) = 0  -- checked via linear algebra over F_q on coeffs
import itertools, random
def test(q):
    e=(q-1)//4; assert (q-1)%4==0
    F=list(range(q))
    a,b,c=1,2,3
    def h(x): return ((x-a)*(x-b)*pow(x-c,3,q))%q
    def r(x): return ((x-a)*(x-b)*(x-c))%q
    # fibers
    from collections import Counter
    cnt=Counter(pow(h(x),e,q) for x in F if h(x)%q!=0)
    print(q, "fiber counts:", dict(cnt), "q/4=",q/4)
    # identity
    for x in F:
        if h(x)%q==0: continue
        assert pow(h(x),e,q)==pow(r(x),e,q)*pow(x-c,(q-1)//2,q)%q
    print(q,"identity h^e = r^e * s^{(q-1)/2}: OK")
for q in (13,29,53): test(q)

# 3) DBlockIndependence brute force at q=13, D=0, block poly A_t(X,Y)= sum_j a_{tj} Y^j, deg_Y <= J-1
# relation: sum_t h^{t e}(X) * A_t(X, X^q) = 0 in F_q[X]; with D=0 blocks are constants in X.
# unknowns a_{t,j}; each term h^{te}*X^{q j}. Build matrix of coefficients.
q=13; e=3
import numpy as np
def polymulmod(p1,p2,q):
    out=[0]*(len(p1)+len(p2)-1)
    for i,x in enumerate(p1):
        for j,y in enumerate(p2):
            out[i+j]=(out[i+j]+x*y)%q
    return out
def polypow(p,n,q):
    r=[1]
    for _ in range(n): r=polymulmod(r,p,q)
    return r
a_,b_,c_=1,2,3
hpoly=polymulmod(polymulmod([-a_%q,1],[-b_%q,1],q),polypow([-c_%q,1],3,q),q)
J=2
cols=[]
for t in range(4):
    ht=polypow(hpoly,t*e,q)
    for j in range(J):
        col=[0]*(len(ht)+q*j)
        for i,v in enumerate(ht): col[i+q*j]=v
        cols.append(col)
L=max(len(cvec) for cvec in cols)
M=[[ (cvec[i] if i<len(cvec) else 0) for cvec in cols] for i in range(L)]
# rank over F_q
def rank_mod(M,q):
    M=[row[:] for row in M]; rank=0; rows=len(M); colsn=len(M[0]); rpos=0
    for cpos in range(colsn):
        piv=None
        for rr in range(rpos,rows):
            if M[rr][cpos]%q: piv=rr;break
        if piv is None: continue
        M[rpos],M[piv]=M[piv],M[rpos]
        inv=pow(M[rpos][cpos],q-2,q)
        M[rpos]=[(x*inv)%q for x in M[rpos]]
        for rr in range(rows):
            if rr!=rpos and M[rr][cpos]%q:
                f=M[rr][cpos]; M[rr]=[(x-f*y)%q for x,y in zip(M[rr],M[rpos])]
        rpos+=1
    return rpos
rk=rank_mod(M,q)
print("q=13 D=0 J=2: unknowns",len(cols),"rank",rk,"=> DBlockIndependence(h) holds at this size:",rk==len(cols))
