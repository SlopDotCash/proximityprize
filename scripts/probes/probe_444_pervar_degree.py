"""
THE CRUX of Angle A's failure. The polynomial-method (Schwartz-Zippel / Combinatorial-
Nullstellensatz) bound on #{S : s_lambda(S)=0} is governed by the PER-VARIABLE degree of
s_lambda, NOT the total degree. We verify: as a polynomial in a single variable x_i (others
fixed), s_lambda has degree lambda_1 = e-r ~ n/2 in the prize regime.

Schwartz-Zippel/CN heuristic: a polynomial of per-variable degree d on the grid mu_n^{r+1}
vanishes on a fraction roughly <= d/n in each coordinate -> the union bound gives a vanishing
fraction that is BOUNDED BELOW by ~ (something like) the per-variable density, and CANNOT be
pushed below ~ lambda_1/n ~ 1/2 by degree alone. Since K/C(n,r+1) ~ 0.15 < 1/2, no
degree-only bound can certify #{S on V} <= K.

We verify lambda_1 = e-r is the per-variable degree by symbolic-free evaluation: fix r values,
vary the last element over distinct field points, and fit the degree of s_lambda in that slot.
"""
from math import comb
p=2013265921
def mu_n(n,P=p):
    e=(P-1)//n
    for c in range(2,4000):
        h=pow(c,e,P)
        if pow(h,n,P)==1 and pow(h,n//2,P)!=1: return [pow(h,i,P) for i in range(n)]
def h_upto(Sv,M,P=p):
    h=[0]*(M+1); h[0]=1
    for z in Sv:
        new=[0]*(M+1); prev=0
        for m in range(M+1): prev=(h[m]+z*prev)%P; new[m]=prev
        h=new
    return h
def schur_val(Sv,e,f,r,P=p):
    M=max(e-r,e-r+1,f-r,f-r+1,0); hv=h_upto(Sv,M,P)
    H=lambda m: hv[m] if 0<=m<=M else 0
    return (H(e-r)*H(f-r+1)-H(e-r+1)*H(f-r))%P
def fit_degree_in_last(base, e,f,r,P=p):
    """base = list of r fixed field elements; treat last slot as variable x. Sample s_lambda(base+[x])
       at many x, interpolate, return degree (#nonzero top coeffs)."""
    # max possible degree in x: lambda_1 = e-r. Sample e-r+5 points.
    D=(e-r)+3
    xs=[pow(7,i+1,P) for i in range(D+1)]  # distinct nonzero
    ys=[schur_val(base+[x],e,f,r,P) for x in xs]
    # Newton/Lagrange interpolation to get polynomial coeffs, then find degree
    # Use divided differences -> Newton form -> degree = highest i with nonzero leading
    n_=len(xs); coef=ys[:]
    for j in range(1,n_):
        for i in range(n_-1,j-1,-1):
            coef[i]=((coef[i]-coef[i-1])*pow((xs[i]-xs[i-j])%P,P-2,P))%P
    # Newton coeffs coef[i] correspond to product (x-x0)...(x-x_{i-1}); highest nonzero index = degree
    deg=max((i for i in range(n_) if coef[i]!=0), default=0)
    return deg
n=64
dom=mu_n(n)
for (e,f,r) in [(n//2+2,n//4+1,4),(n//2+1,n-1,5),(20//32* n,16, 6)]:
    pass
print("Per-variable degree of the Schur defect s_lambda in one slot (should = e-r = lambda_1):")
for (label,e,f,r) in [("r4 n64",34,17,4),("r5 n64",33,63,5),("r3 n32",16,15,3),("r6 n32",20,16,6)]:
    nn = 32 if 'n32' in label else 64
    dm=mu_n(nn)
    base=[dm[i] for i in range(2,2+r)]  # r fixed distinct subgroup elements
    deg=fit_degree_in_last(base,e,f,r)
    print(f"  {label}: e={e} f={f} r={r}  lambda_1=e-r={e-r}  measured per-var degree={deg}  (n/2={nn//2})")
