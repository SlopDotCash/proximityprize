#!/usr/bin/env python3
"""
SYZ24 probe: cross-core codeword compatibility.

Setup (single-copy; pair-doubling just multiplies by 2):
 - Field GF(p), n distinct eval points, RS[alpha,k], dual code D = dual of RS (dim n-k).
 - For a core C (subset of coords), A_C := {c in D : supp(c) subset C}
     = dual codewords supported inside C.  dim A_C = max(0, |C|-k)  (MDS).
 - SYZ23 leak: support accounting can't force the joint span up because nested cores
   look "free".  The HONEST linear-algebra question:
       is  dim( span_i A_{C_i} )  =  |U| - k    where U = union C_i ?
   If YES for real covers -> strip closes (span lower bound = |U|-k, correct accounting).
   A_U := dual codewords supported in U has dim |U|-k and CONTAINS every A_{C_i},
   so  span_i A_{C_i}  <=  A_U  always.  Question is whether equality holds.
   The GAP  d := (|U|-k) - dim(span A_i)  is the cross-core incompatibility deficiency:
   dual codewords supported on U that are NOT sums of ones each supported in a single C_i.

We measure d for:
  (a) generic / "spread" covers,
  (b) the SYZ23 nested leak profile (cores nesting inside predecessors' union).
"""
import itertools, random

def gf_setup(p):
    inv = [0]*(p)
    for a in range(1,p):
        inv[a] = pow(a,p-2,p)
    return inv

def rref(rows, ncols, p):
    """Gaussian elimination over GF(p); returns rank and reduced rows (list)."""
    M = [row[:] for row in rows]
    r = 0
    pivots = []
    for c in range(ncols):
        # find pivot
        piv = None
        for i in range(r, len(M)):
            if M[i][c] % p != 0:
                piv = i; break
        if piv is None: continue
        M[r], M[piv] = M[piv], M[r]
        invp = pow(M[r][c], p-2, p)
        M[r] = [(x*invp) % p for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] % p != 0:
                f = M[i][c]
                M[i] = [(M[i][j]-f*M[r][j]) % p for j in range(ncols)]
        pivots.append(c)
        r += 1
        if r == len(M): break
    return r, M[:r]

def dual_code_basis(alpha, k, p):
    """Basis of dual code D = {c in F^n : sum_i c_i alpha_i^d = 0, d<k}.
       That's the null space of the k x n Vandermonde V[d][i]=alpha_i^d.
       Return list of basis vectors (each length n)."""
    n = len(alpha)
    V = [[pow(alpha[i], d, p) for i in range(n)] for d in range(k)]
    # null space of V
    rank, R = rref(V, n, p)
    # pivots columns
    # recompute pivot columns
    pivcols = []
    rr = 0
    # redo to grab pivot positions
    M = [row[:] for row in V]; r=0; pivcols=[]
    for c in range(n):
        piv=None
        for i in range(r,len(M)):
            if M[i][c]%p!=0: piv=i;break
        if piv is None: continue
        M[r],M[piv]=M[piv],M[r]
        invp=pow(M[r][c],p-2,p); M[r]=[(x*invp)%p for x in M[r]]
        for i in range(len(M)):
            if i!=r and M[i][c]%p!=0:
                f=M[i][c]; M[i]=[(M[i][j]-f*M[r][j])%p for j in range(n)]
        pivcols.append(c); r+=1
        if r==len(M): break
    Rred = M[:r]
    free = [c for c in range(n) if c not in pivcols]
    basis=[]
    for fc in free:
        vec=[0]*n; vec[fc]=1
        for ri,pc in enumerate(pivcols):
            vec[pc] = (-Rred[ri][fc]) % p
        basis.append(vec)
    return basis  # dim = n-k

def A_C_basis(dualbasis, C, n, p):
    """Basis of {c in D : supp subset C}: from dual basis rows, take those with support in C
       via linear algebra: solve for combos vanishing outside C.
       Represent D-elements by coordinates in dualbasis; constraint c_j=0 for j not in C."""
    Cset=set(C)
    outside=[j for j in range(n) if j not in Cset]
    m=len(dualbasis)
    # unknown x in F^m ; vector = sum x_b * dualbasis[b]; constraints: (vector)_j=0 for j outside
    # constraint matrix rows over columns x: for each j outside: sum_b dualbasis[b][j] * x_b =0
    rows=[[dualbasis[b][j] for b in range(m)] for j in outside]
    if not rows:
        # no constraints: whole dual
        return [db[:] for db in dualbasis]
    rank,_=rref(rows,m,p)
    # null space -> combos
    M=[row[:] for row in rows]; r=0;pivcols=[]
    for c in range(m):
        piv=None
        for i in range(r,len(M)):
            if M[i][c]%p!=0: piv=i;break
        if piv is None: continue
        M[r],M[piv]=M[piv],M[r]
        invp=pow(M[r][c],p-2,p);M[r]=[(x*invp)%p for x in M[r]]
        for i in range(len(M)):
            if i!=r and M[i][c]%p!=0:
                f=M[i][c];M[i]=[(M[i][j]-f*M[r][j])%p for j in range(m)]
        pivcols.append(c);r+=1
        if r==len(M):break
    Rred=M[:r]
    freecols=[c for c in range(m) if c not in pivcols]
    Abasis=[]
    for fc in freecols:
        x=[0]*m;x[fc]=1
        for ri,pc in enumerate(pivcols):
            x[pc]=(-Rred[ri][fc])%p
        # build actual vector
        vec=[0]*n
        for b in range(m):
            if x[b]:
                for j in range(n):
                    vec[j]=(vec[j]+x[b]*dualbasis[b][j])%p
        Abasis.append(vec)
    return Abasis

def span_dim(vectors, n, p):
    if not vectors: return 0
    rank,_=rref([v[:] for v in vectors], n, p)
    return rank

def run(n,k,p,cores,label):
    alpha=list(range(n))
    D=dual_code_basis(alpha,k,p)
    assert len(D)==n-k, (len(D),n-k)
    Abases=[A_C_basis(D,C,n,p) for C in cores]
    # joint span
    allvecs=[v for Ab in Abases for v in Ab]
    joint=span_dim(allvecs,n,p)
    U=sorted(set().union(*[set(C) for C in cores])) if cores else []
    A_U=A_C_basis(D,U,n,p)
    dimAU=span_dim(A_U,n,p)
    sizes=[len(C) for C in cores]
    percore=[max(0,len(C)-k) for C in cores]
    print(f"[{label}] n={n} k={k} p={p} #cores={len(cores)} coresizes={sizes}")
    print(f"    |U|={len(U)}  |U|-k={len(U)-k}  dim(A_U)={dimAU}  dim(join span A_i)={joint}  "
          f"sum(|C_i|-k)={sum(percore)}")
    print(f"    GAP deficiency d = (|U|-k) - joint = {len(U)-k - joint}   "
          f"(strip closes iff d==0 i.e. joint == |U|-k)")
    print()
    return joint, len(U)-k, dimAU

if __name__=="__main__":
    random.seed(1)
    # Small clean case: n=15 k=7 over GF(31)
    p=31
    # (a) generic disjoint-ish cover
    run(15,7,p,[list(range(0,9)),list(range(6,15))],"generic-2core-overlap3")
    # (b) three cores each size 9, pairwise overlap small
    run(15,7,p,[[0,1,2,3,4,5,6,7,8],[4,5,6,7,8,9,10,11,12],[8,9,10,11,12,13,14,0,1]],"three-core")
    # (c) NESTED leak: seeds then a core nested in union of two seeds each overlap <= k-1=6
    #   n=15,k=7, core size 9, k-1=6
    seedA=list(range(0,9))      # 0..8
    seedB=list(range(6,15))     # 6..14, U=0..14
    nested=[0,1,2,3,4, 10,11,12,13]  # 5 from seedA(0..4), 4 from seedB(10..13): both overlaps<=6, size9 subset of U
    run(15,7,p,[seedA,seedB,nested],"nested-leak-1")
    # (d) many nested cores inside same two seeds
    cores=[seedA,seedB]
    import random as R
    pool=list(range(15))
    for t in range(8):
        C=sorted(R.sample(range(15),9))
        cores.append(C)
    run(15,7,p,cores,"many-nested-random")
    # bigger: n=32 k=16 GF(37)
    p2=37
    seedA=list(range(0,17)); seedB=list(range(15,32))
    run(32,16,p2,[seedA,seedB],"n32-two-seeds")
    cores=[seedA,seedB]
    for t in range(20):
        C=sorted(R.sample(range(32),17))
        cores.append(C)
    run(32,16,p2,cores,"n32-many-nested-random-size17")

print("=== ADVERSARIAL: many cores, try to keep joint span below |U|-k ===")
# n=32,k=16,p=37: cores all = {0..15} + one extra coord (min-weight-ish, |C|=17, A_i dim1)
p2=37
cores=[sorted(list(range(0,16))+[x]) for x in range(16,32)]
run(32,16,p2,cores,"star-cores-common15")
# cores confined to a 24-coord block: many size-17 subsets of {0..23}
import random as R
R.seed(7)
cores=[sorted(R.sample(range(24),17)) for _ in range(30)]
run(32,16,p2,cores,"confined-block24")
# ALL (k+1)=17-subsets impossible(too many); sample 40 random size17 over full n=32
cores=[sorted(R.sample(range(32),17)) for _ in range(40)]
run(32,16,p2,cores,"n32-40random-size17")
# nested leak exact SYZ23 style: 2 seeds size17 + many size17 nested, measure
seedA=list(range(0,17)); seedB=list(range(15,32))
cores=[seedA,seedB]
for _ in range(30):
    # nested: pick <=16 from seedA and rest from seedB, total 17, overlaps<=16=k
    a=R.randint(1,16); C=sorted(R.sample(seedA,a)+R.sample(seedB,17-a)); cores.append(sorted(set(C)))
cores=[c for c in cores if len(c)==17]
run(32,16,p2,cores,"nested-leak-many-size17")
