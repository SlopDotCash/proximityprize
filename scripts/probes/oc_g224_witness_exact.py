#!/usr/bin/env python3
"""OC G224 witness generator of record. Recomputes float-free every constant the
Lean file G224 asserts, and prints them for hard-coding + asserts self-consistency.

CORRECTION (audit finding L106).  The original revision of this probe set
    k2 = W^(chi2) * (E_r^(chi2) O_{r-1}^(chi2) + O_r^(chi2) E_{r-1}^(chi2))
with ^(chi2) the Legendre (MULTIPLICATIVE quadratic-character) transform, and called
it "the chi2-mode integrand of the PAR- packet".  That is wrong: multiplicative
transforms do not diagonalise the ADDITIVE circular correlation E_r * O_{r-1}, so
this product of separate transforms ("sepProd") is not a mode of PAR-.  The genuine
quadratic-character mode of the pairing p*<W, X>, X = E_r*O_{r-1} + O_r*E_{r-1}, is
(p/(p-1)) * W^(chi2) * X^(chi2) by multiplicative Parseval on F_p^*; its sign is the
sign of chi2Pair = W^(chi2) * X^(chi2), computed below from the actual correlation X.

Witnesses (n=16, r=5):
 W1 p=257: sepProd = +12734300160, chi2Pair = +15408783360 > 0, PAR- < 0, A < 0.
 W2 p=97 : sepProd =  -2477260800, chi2Pair =  +1278443520 > 0, PAR- < 0, A < 0.
 W3 p=113: A > 0 while PAR- < 0 (packet sign co-exists with an A sign flip).
So under the genuine chi2 pairing BOTH W1 and W2 have a strictly POSITIVE quadratic
mode inside a strictly negative packet (the multiplicative Parseval decomposition of
PAR- is not termwise sign-definite).  The sign DISAGREEMENT between W1 and W2 exists
only for sepProd and carries no packet meaning.  Nothing here certifies the sign of
any ADDITIVE-character mode; that census is the float probe oc_g224_mode_signs.py.
"""
import math,json,os,tempfile
from collections import Counter

def factor(n):
    out=[];d=2
    while d*d<=n:
        if n%d==0:
            out.append(d)
            while n%d==0:n//=d
        d+=1
    if n>1:out.append(n)
    return out
def primitive_root(p):
    fs=factor(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs):return g
    raise ValueError(p)
def subgroup(p,n):
    z=pow(primitive_root(p),(p-1)//n,p);grp=[];x=1
    for _ in range(n):grp.append(x);x=x*z%p
    assert x==1 and len(set(grp))==n
    return grp
def parts(n,hi=None):
    if n==0:yield ();return
    hi=n if hi is None or hi>n else hi
    for x in range(hi,0,-1):
        for tail in parts(n-x,x):yield (x,)+tail
def zlam(lam):
    return math.prod((j**m)*math.factorial(m) for j,m in Counter(lam).items())
def legendre(a,p):
    a%=p
    if a==0:return 0
    return 1 if pow(a,(p-1)//2,p)==1 else -1
def halves_int(p,grp,r,eta,L):
    even=[0]*p;odd=[0]*p
    for lam in parts(r):
        c=L//zlam(lam)*((-1)**(sum(lam)-len(lam)))
        acc=[0]*p;acc[0]=1
        for part in lam:
            nb=[0]*p;src=eta[part]
            nz=[(i,acc[i]) for i in range(p) if acc[i]]
            for i,ai in nz:
                for k in range(p):
                    if src[k]:nb[(i+k)%p]+=ai*src[k]
            acc=nb
        tgt=even if (r-len(lam))%2==0 else odd
        for t in range(p):
            if acc[t]:tgt[t]+=c*acc[t]
    return even,odd
def chi2_transform(arr,p):
    s=0
    for t in range(1,p):
        l=legendre(t,p)
        if l and arr[t]:s+=l*arr[t]
    return s

def cell(p,n,r):
    grp=subgroup(p,n)
    eta={j:[0]*p for j in range(1,r+1)}
    for j in range(1,r+1):
        for g in grp:eta[j][(j*g)%p]+=1
    W=[0]*p
    for y in grp:
        for z in grp:W[(2*y-z)%p]+=1
    Lr=math.lcm(*[zlam(lam) for lam in parts(r)])
    Lm=math.lcm(*[zlam(lam) for lam in parts(r-1)])
    Er,Or_=halves_int(p,grp,r,eta,Lr);Em,Om=halves_int(p,grp,r-1,eta,Lm)
    Wc=chi2_transform(W,p);Erc=chi2_transform(Er,p);Orc=chi2_transform(Or_,p)
    Emc=chi2_transform(Em,p);Omc=chi2_transform(Om,p)
    # sepProd: product of SEPARATE Legendre transforms.  Audit finding L106: the
    # Legendre symbol is a MULTIPLICATIVE character, and multiplicative transforms do
    # not turn the additive circular correlation E_r * O_{r-1} into a product of
    # transforms.  So sepProd is NOT a mode of the PAR- packet; it is recorded only
    # for provenance (it is the quantity the original G224 called "k2").
    k2=Wc*(Erc*Omc+Orc*Emc)
    # The genuine object: X(t) = sum_s E_r(s) O_{r-1}(s-t) + O_r(s) E_{r-1}(s-t), so
    # that sum_t W(t) X(t) = <W, E_r * O_{r-1} + O_r * E_{r-1}> (the PAR- pairing).
    # Multiplicative Parseval on F_p^*:
    #   sum_{t != 0} W(t) X(t) = (1/(p-1)) sum_psi conj(W^(psi)) X^(psi),
    # so the quadratic-character (psi = chi2, real) mode of p*<W,X> is
    #   (p/(p-1)) * W^(chi2) * X^(chi2),  whose sign is that of chi2Pair below.
    def xcorr(A,B):
        X=[0]*p
        for s in range(p):
            if A[s]:
                for u in range(p):
                    if B[u]:X[(s-u)%p]+=A[s]*B[u]
        return X
    X1=xcorr(Er,Om);X2=xcorr(Or_,Em)
    X=[X1[t]+X2[t] for t in range(p)]
    Xc=chi2_transform(X,p)
    chi2Pair=Wc*Xc
    # exact PAR- via physical parity split (L-scaled). correlation Corr(A,B)(t)=sum_s A(s)B(s-t)
    def corr_W(A,B):
        # sum_t W(t) * (A corr B)(t) = sum_s A(s) sum_t W(t) B(s-t)
        # Wc_b(s)=sum_t W(t) B(s-t)
        Wcb=[0]*p
        for t in range(p):
            wt=W[t]
            if wt:
                for u in range(p):
                    if B[u]:Wcb[(t+u)%p]+=wt*B[u]
        return sum(A[s]*Wcb[s] for s in range(p))
    ee=corr_W(Er,Em);eo=corr_W(Er,Om);oe=corr_W(Or_,Em);oo=corr_W(Or_,Om)
    sEe=sum(Er);sEo=sum(Or_);sMe=sum(Em);sMo=sum(Om)
    dc=lambda sa,sb:n*n*sa*sb
    PARp=p*(ee+oo)-(dc(sEe,sMe)+dc(sEo,sMo))
    PARm=p*(eo+oe)-(dc(sEe,sMo)+dc(sEo,sMe))
    mass=math.comb(n,r)*math.comb(n,r-1)
    Rr=[Er[t]+Or_[t] for t in range(p)];Rm=[Em[t]+Om[t] for t in range(p)]
    A=p*corr_W(Rr,Rm)-n*n*mass*Lr*Lm
    assert PARp+PARm==A,(p,n,r)
    # X is the right pairing object: <W,X> = eo + oe.
    assert sum(W[t]*X[t] for t in range(p))==eo+oe,(p,n,r)
    return {"p":p,"n":n,"r":r,"k2":k2,"Wc":Wc,"Xc":Xc,"chi2Pair":chi2Pair,
            "PARm":PARm,"A":A,"Lr":Lr,"Lm":Lm}

W1=cell(257,16,5)
W2=cell(97,16,5)
W3=cell(113,16,5)   # A POSITIVE, PAR- still negative (regularity across A-flip)
print("=== EXACT WITNESSES ===")
for w in (W1,W2,W3):
    print(f" n={w['n']} r={w['r']} p={w['p']}: sepProd={w['k2']} chi2Pair={w['chi2Pair']} "
          f"(Wc={w['Wc']} Xc={w['Xc']}) | PAR-={w['PARm']} | A={w['A']}")
# provenance: the separate-transform products (NOT packet modes) keep their old values
assert W1["k2"]==12734300160 and W2["k2"]==-2477260800
# genuine quadratic-character pairing: positive at both W1 and W2
assert W1["chi2Pair"]>0 and W2["chi2Pair"]>0, "genuine chi2 pairing positive at W1, W2"
assert W1["PARm"]<0 and W2["PARm"]<0 and W3["PARm"]<0, "all packets negative"
assert (W2["A"]<0) and (W3["A"]>0), "A must flip sign between W2 and W3 while PAR- stays negative"
print("\nSELF-CHECK PASS: genuine chi2 pairing > 0 inside a PAR- < 0 packet at W1 and W2;")
print("all three packets PAR- < 0; A flips sign (W2 A<0, W3 A>0) with PAR- unchanged negative.")
print("(sepProd changes sign between W1 and W2 but is NOT a mode of PAR-; audit L106.)")
print(f"\nLEAN CONSTANTS:")
print(f"  w1SepProd := {W1['k2']}  w1Chi2Pair := {W1['chi2Pair']}  (n=16,r=5,p=257)")
print(f"  w2SepProd := {W2['k2']}  w2Chi2Pair := {W2['chi2Pair']}  (n=16,r=5,p=97)")
print(f"  w1PARm := {W1['PARm']}  w1A := {W1['A']}")
print(f"  w2PARm := {W2['PARm']}  w2A := {W2['A']}")
print(f"  w3PARm := {W3['PARm']}  w3A := {W3['A']}  w3Chi2Pair := {W3['chi2Pair']}  (n=16,r=5,p=113, A>0)")
outdir="/tmp/arklib-reports" if os.path.isdir("/tmp/arklib-reports") else os.path.join(tempfile.gettempdir(),"arklib-reports")
os.makedirs(outdir,exist_ok=True)
json.dump({"W1":W1,"W2":W2,"W3":W3},open(os.path.join(outdir,"oc_g224_witnesses.json"),"w"),indent=1)
print(f"\nwrote {outdir}/oc_g224_witnesses.json")
