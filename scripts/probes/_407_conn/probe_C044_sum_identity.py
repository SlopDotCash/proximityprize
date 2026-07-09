"""
C044 final check: confirm the EXACT structural identity at the smallest live gap.
For S = union of m cosets of mu_d (d=2^L), with c_i = x_i^d the class values:
   e_d(S) = (-1)^{d-1} * sum_i c_i        (a SUM, NOT a product)
This is read directly from loc(S)=prod_i(X^d - c_i): coeff of X^{md-d}=coeff of Y^{m-1}
in prod(Y-c_i) = -e1(c) = -sum c_i, and e_d(S)=(-1)^d * coeff(X^{md-d}).
=> e_d(S) = (-1)^d * (-(sum c_i)) = (-1)^{d-1} sum_i c_i.
Verified exactly mod q; contrast with the C044-claimed product prod_i c_i.
"""
def isprime(n):
    if n<2: return False
    if n%2==0: return n==2
    d=3
    while d*d<=n:
        if n%d==0: return False
        d+=2
    return True
def all_esymm_poly(vals,q):
    poly=[1]
    for x in vals:
        new=[0]*(len(poly)+1)
        for i,c in enumerate(poly):
            new[i]=(new[i]+c*(-x))%q; new[i+1]=(new[i+1]+c)%q
        poly=new
    return poly
def esymm(poly,t,q,N): return (pow(-1,t,q)*poly[N-t])%q
def find_prime(n,beta=4):
    q=n**beta - (n**beta % n) + 1
    while not (isprime(q) and (q-1)%n==0): q+=n
    return q
def gen_unit(q):
    m=q-1; facs=set(); mm=m; d=2
    while d*d<=mm:
        while mm%d==0: facs.add(d); mm//=d
        d+=1
    if mm>1: facs.add(mm)
    for h in range(2,q):
        if all(pow(h,m//p,q)!=1 for p in facs): return h
for (n,L,m) in [(16,1,2),(16,1,3),(16,2,2),(16,2,3),(32,2,3),(64,2,2)]:
    q=find_prime(n); g=pow(gen_unit(q),(q-1)//n,q); d=2**L
    mu_d=[pow(g,(n//d)*j % n,q) for j in range(d)]
    reps=[pow(g,i,q) for i in range(m)]; classes=[pow(r,d,q) for r in reps]
    S=set()
    for r in reps:
        for u in mu_d: S.add((r*u)%q)
    S=list(S); poly=all_esymm_poly(S,q)
    e_t=esymm(poly,d,q,len(S))
    pred_sum=(pow(-1,d-1,q)*(sum(classes)%q))%q
    prod_c=1
    for c in classes: prod_c=(prod_c*c)%q
    print(f"n={n} d={d} m={m} q={q}: e_t={e_t}  (-1)^(d-1)*SUM={pred_sum} match={e_t==pred_sum}  | PROD(claim)={prod_c} match={e_t==prod_c}")
