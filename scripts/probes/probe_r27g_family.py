import math
# Explicit Nat family mirroring d=4:  s=isqrt((q-C0)/A), m=d*s, J=s+c, D=(q-C0)/d,
# b=isqrt(A2*q), B=k*b, constant C with C^2 = k^2 * A2.
# Admissibility to prove (fold):  d*Dtot <= m*(B + q - 3),  Dtot=degG*(m+(d-1)e)+D+q*(J-1).
# We want it to hold for ALL q ≡ 1 (mod d), q >= Qmin.

def isqrt(n): return math.isqrt(n)

def check(d, C0, A, c, A2, k, Qmin, Qmax):
    degG=d+1
    badcount=0; worstC=0; firstbad=None
    q=1
    # iterate q ≡ 1 mod d
    q=Qmin
    while q%d!=1: q+=1
    while q<=Qmax:
        if q>C0:
            s=isqrt((q-C0)//A); m=d*s; J=s+c; D=(q-C0)//d
            e=(q-1)//d; b=isqrt(A2*q); B=k*b
            if s>=1 and m<q:
                # indep
                indep = d*D+(d-1)*degG < q
                # count
                count = m*(D+d*m+J) < d*J*(D+1)
                Dtot=degG*(m+(d-1)*e)+D+q*(J-1)
                fold = d*Dtot <= m*(B + q - 3)
                sqbnd = B*B <= C*C*q
                ok = indep and count and fold and sqbnd
                # actual achieved C from B
                actualC = B/math.sqrt(q)
                worstC=max(worstC, actualC)
                if not ok:
                    badcount+=1
                    if firstbad is None:
                        firstbad=(q, dict(indep=indep,count=count,fold=fold,sqbnd=sqbnd,
                                          s=s,m=m,J=J,D=D,B=B,ratio=d*Dtot/(m*(B+q-3))))
        q+=d  # next in residue class
    return badcount, firstbad, worstC

# ---- design d=8 ----
# indep: 8D+63<q. D=(q-C0)/8 -> 8D=q-C0-((q-C0)%8). want q-C0 divisible by 8 when q≡1 mod8 -> C0≡1 mod8.
# choose C0=64 (≡0)... need C0≡1 mod8 for clean; use C0=1? but need q-C0>0 headroom for 63. Try C0 s.t. 8D+63<q.
# Let's just grid-search A,c,A2,k,C0 for smallest C.
print("=== d=8 search ===")
best=None
for C0 in [1,9,17,25,33,41,49,57,65]:
    for A in range(2,120):
        for c in [7,8,9]:
            # A2,k chosen so C=k*something minimal; try to bound
            for A2 in range(2,200):
                for k in range(1,40):
                    C=math.isqrt(k*k*A2)
                    if C*C < k*k*A2: C+=1  # ceil sqrt so B^2<=C^2 q since B^2<=k^2 A2 q
                    if C>=200: continue
                    bc,fb,wc = check(8,C0,A,c,A2,k,2000,20000)
                    if bc==0 and wc<=C+0.5:
                        if best is None or C<best[0]:
                            best=(C,C0,A,c,A2,k,wc)
    # early: only test small A2/k combos to keep fast -> break after first C0 giving something
if best: print("d8 best:",best)
else: print("d8 none in coarse grid")
