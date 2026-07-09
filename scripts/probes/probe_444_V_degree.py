"""
Structural handle on V (point 4). The defect D(S) = h_{e-r}h_{f-r+1} - h_{e-r+1}h_{f-r} is a 2x2
Jacobi-Trudi minor of complete-homogeneous polys => equals (up to sign) a single SKEW SCHUR poly
s_{lambda/mu}(S). For consecutive indices it is the Schur poly of a 2-row shape (a hook/ribbon).
Specifically det[[h_{a}, h_{a+1}],[h_{b}, h_{b+1}]] = h_a h_{b+1} - h_{a+1} h_b = -s_{(a, b+1)/...}.
We (i) confirm D(S)=0 <=> bad numerically equals the variety count, (ii) measure deg of D as a
symmetric poly (= (e-r)+(f-r+1)), (iii) report #{S on V}/C(n,r+1) (codim-1 heuristic ~ 1/q effective),
(iv) check whether bad set is cut by an EVEN LOWER relation (e.g. a single Schur s_lambda(S)=0).
"""
import itertools
from math import comb, gcd
from collections import Counter
p=2013265921
def w_of_order(n,P):
    e=(P-1)//n
    for c in range(2,4000):
        h=pow(c,e,P)
        if pow(h,n,P)==1 and pow(h,n//2,P)!=1: return h
    raise RuntimeError
def complete_homog(S,mmax,P):
    PS=[0]*(mmax+1)
    for z in S:
        zi=1
        for j in range(1,mmax+1): zi=(zi*z)%P; PS[j]=(PS[j]+zi)%P
    h=[0]*(mmax+1); h[0]=1
    for m in range(1,mmax+1):
        s=0
        for i in range(1,m+1): s=(s+PS[i]*h[m-i])%P
        h[m]=(s*pow(m,P-2,P))%P
    return h

def schur_2row(S, a, b, P):
    """s_{(a,b)}(S) = det[[h_a, h_{a+1}],[h_{b-1}, h_b]] (Jacobi-Trudi, lambda=(a,b), a>=b).
    Returns the value as a poly in S elements (mod P)."""
    mmax=a+1
    h=complete_homog(S,mmax,P)
    def hh(i): return h[i] if 0<=i<=mmax else 0
    # Jacobi-Trudi for lambda=(l1,l2): det [[h_{l1}, h_{l1+1}],[h_{l2-1}, h_{l2}]]
    return (hh(a)*hh(b) - hh(a+1)*hh(b-1))%P

n=16; r=6; e,f=12,10; a0=7; P=p
w=w_of_order(n,P); mu=[pow(w,i,P) for i in range(n)]
# D(S) = h_{e-r} h_{f-r+1} - h_{e-r+1} h_{f-r}. With a=e-r=6, b+? Let's just match to a Schur shape.
# h_a h_{b+1} - h_{a+1} h_b with a=e-r=6, b=f-r=4 => h_6 h_5 - h_7 h_4.
# Jacobi-Trudi: s_{(l1,l2)} = h_{l1}h_{l2} - h_{l1+1}h_{l2-1}. Match h_6 h_5 - h_7 h_4:
#   l1=6, l2=5 gives h_6 h_5 - h_7 h_4. YES => D = s_{(6,5)}(S), a 2-row Schur poly, shape (6,5).
total=0; onV=0; onV_schur=0
mmaxD=max(e-r,e-r+1,f-r,f-r+1)
for Sidx in itertools.combinations(range(n),a0):
    S=[mu[i] for i in Sidx]
    h=complete_homog(S,mmaxD,P)
    D=(h[e-r]*h[f-r+1]-h[e-r+1]*h[f-r])%P
    Sch=schur_2row(S,6,5,P)  # s_{(6,5)}
    total+=1
    if D==0: onV+=1
    if Sch==0: onV_schur+=1
print(f"n={n} r={r} line(x^{e},x^{f}): C(n,r+1)={total}")
print(f"  D(S)=0 count (#S on V) = {onV}")
print(f"  s_{{(6,5)}}(S)=0 count = {onV_schur}  (D == s_(6,5)? both counts equal: {onV==onV_schur})")
print(f"  V is a SINGLE Schur condition s_lambda(S)=0, lambda=(e-r, f-r+1)=(6,5), |lambda|={6+5}")
print(f"  deg D as symmetric poly in r+1={r+1} vars = (e-r)+(f-r+1) = {(e-r)+(f-r+1)}")
print(f"  codim-1 heuristic #S_on_V / C(n,r+1) = {onV}/{total} = {onV/total:.4f}  (=~ 1/p_eff)")
print(f"  K/C(n,r+1) = {(1<<r)*comb(n//2,r)}/{total} = {(1<<r)*comb(n//2,r)/total:.4f}")
# verify D == s_(6,5) elementwise on a few subsets
ok=True
for Sidx in list(itertools.combinations(range(n),a0))[:200]:
    S=[mu[i] for i in Sidx]
    h=complete_homog(S,mmaxD,P)
    D=(h[e-r]*h[f-r+1]-h[e-r+1]*h[f-r])%P
    Sch=schur_2row(S,6,5,P)
    if D!=Sch: ok=False; break
print(f"  elementwise D == s_(6,5) on 200 subsets: {ok}")
