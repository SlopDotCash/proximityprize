import numpy as np, math
from sympy import isprime, primitive_root

# FINAL theoretical confirmation for the effective-katz-circumvent verdict.
# 
# The sheaf G on the m-torus with trace_G(w) = S(w) = sum_{j=1}^{m-1} w^{-j} a_j is the
# "discrete Mellin/Fourier transform" of the sequence (a_j). KEY FACTS for Katz machinery:
#
# (1) RANK. S(w) is a sum of m-1 distinct characters w -> w^{-j}. As a function on the m-torus
#     it is the trace of a sheaf of rank = #{nonzero Fourier coeffs} = m-1 = O(m). So G itself
#     has poly(m) rank/conductor. SO FAR the family route LOOKS viable: a single rank-(m-1)
#     sheaf, conductor O(m), and Cond(G^{ox r}) ~ (m-1)^r. The 2r-th family moment 
#     (1/m) sum_w |S(w)|^{2r} = sum over j-tuples of a_{j1}...a_{jr} conj(a_{k1}...a_{kr}) 
#     1[ sum j = sum k mod m].   <-- this is EXACTLY the additive energy of the multiset {a_j}
#     weighted by the a-values, i.e. the r-fold autocorrelation.
#
# (2) THE CATCH. The "diagonal" (Gaussian leading term) is the tuples where {j}={k} as multisets.
#     The error = off-diagonal tuples with sum j = sum k but {j}!={k}. Katz/Weil would bound this 
#     by Cond * m^{r-1/2} IF the a_j were trace values of a SINGLE low-conductor sheaf in j 
#     (so that the off-diagonal is itself a complete sum with square-root cancellation). 
#     BUT a_j = tau(psi^j)/sqrt p, and j -> tau(psi^j) is NOT a trace function of bounded 
#     conductor in j: it is itself a Gauss sum whose dependence on j is the WILD parameter. 
#     This is the Rojas-Leon (2207.12439) "Gauss sum independence" obstruction.
#
# TEST (2): is the off-diagonal of the family moment itself square-root-cancelling, or O(1)*diagonal?
# Compute, for the a-sequence, the genuine off-diagonal energy contribution vs diagonal at r=2.

def get_a(p,n):
    g=primitive_root(p); m=(p-1)//n
    ep=np.exp(2j*np.pi/p)
    powg=[pow(g,a,p) for a in range(p-1)]
    taus=[]
    for j in range(m):
        s=sum(np.exp(2j*np.pi*j*a/m)*ep**powg[a] for a in range(p-1))
        taus.append(s/np.sqrt(p))
    return m, np.array(taus)  # a_0..a_{m-1}, |a_j|=1 for j!=0, a_0=-1/sqrt p

def r2_decompose(p,n):
    m,a = get_a(p,n)
    # family 4th moment = sum_{j1,j2,k1,k2 in [1,m-1]} a_j1 a_j2 conj(a_k1 a_k2) 1[j1+j2=k1+k2 mod m]
    # diagonal {j1,j2}={k1,k2}: gives sum 1 + cross = (m-1)^2 + (m-1) ish (since |a|=1) -> the 
    #   "Gaussian" 2*(m-1)^2-ish leading. off-diag = the rest.
    J=np.arange(1,m)
    aj=a[1:m]
    diag=0.0; off=0.0+0j
    # build by convolution: c_s = sum_{j1+j2=s} a_j1 a_j2 ; then 4th moment=sum_s |c_s|^2
    # diagonal part: pairs where {k}={j}.
    cs={}
    for j1 in J:
        for j2 in J:
            s=(j1+j2)%m
            cs[s]=cs.get(s,0)+aj[j1-1]*aj[j2-1]
    M4=sum(abs(v)**2 for v in cs.values())
    # diagonal contribution = sum over (j1,j2),(k1,k2) with {k1,k2}={j1,j2}
    # = sum_{j1,j2} |a_j1|^2|a_j2|^2 (k=j) + sum_{j1!=j2} a_j1 a_j2 conj(a_j2 a_j1) (swap) 
    #   = (m-1)^2 + (m-1)(m-2)  [since |a|=1] = 2(m-1)^2-(m-1)
    diagcontrib = (m-1)**2 + (m-1)*(m-2)
    offcontrib = M4 - diagcontrib
    return m, M4, diagcontrib, offcontrib

for (p,n,lbl) in [(7681,128,"CLEAN"),(7937,128,"DEFECT"),(1153,16,"thin-clean")]:
    if not isprime(p): continue
    m,M4,dia,off=r2_decompose(p,n)
    print(f"{lbl} p={p} n={n} m={m}: family4thMoment={M4:.1f} diagonal(Gauss)={dia:.1f} off-diagonal={off:.1f}  off/diag={off/dia:.3f}  off/sqrt(diag)*... off/m^1.5={off/m**1.5:.3f}")
