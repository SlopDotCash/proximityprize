#!/usr/bin/env python3
"""SYZ34 probe: the dim((A+B) cap C) law for post-merge band triples.

Model.  RS[n,k] over F_q (q prime, distinct eval points).  Dual code
D = null space of the k x n Vandermonde G[t,j] = x_j^t (t=0..k-1), dim n-k,
minimum distance k+1.  For a core (coordinate subset) S:
    A(S) = { v in D : supp(v) subset of S } ,  dim = max(0, |S| - k).
For pairwise cores with |S_i cap S_j| <= k-1 < dual distance k+1 the pairwise
intersections A_i cap A_j are ZERO (SYZ23).

We measure dim((A+B) cap C) exactly and compare to candidate formulas.
Generation (deficiency 0) needs  dim(A+B+C) = |union| - k, i.e.
    dim((A+B) cap C) = Sum_pair |Ci cap Cj| - |triple| - 2k        (target law)
The gate is the '<=' direction: dim((A+B) cap C) <= max(0, that).
"""
import random, itertools

def rref_dim(rows, ncol, p):
    """rank of a list of row vectors over F_p."""
    M = [r[:] for r in rows]
    rank = 0
    col = 0
    R = len(M)
    r = 0
    for col in range(ncol):
        piv = None
        for i in range(r, R):
            if M[i][col] % p != 0:
                piv = i; break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][col], p-2, p)
        M[r] = [(x*inv) % p for x in M[r]]
        for i in range(R):
            if i != r and M[i][col] % p != 0:
                f = M[i][col]
                M[i] = [(a - f*b) % p for a,b in zip(M[i], M[r])]
        r += 1
        if r == R: break
    return r

def dual_basis_on_support(x, k, S, p):
    """Basis (as full-length n-vectors) of { v in dual(RS) : supp v subset S }.
    v supported on S with sum_j v_j x_j^t = 0 (t=0..k-1). Solve null space of
    the k x |S| matrix over F_p; embed into length-n vectors."""
    n = len(x)
    Slist = sorted(S)
    m = len(Slist)
    # G_S: k x m
    G = [[pow(x[j], t, p) for j in Slist] for t in range(k)]
    # null space via rref on columns
    # Reduce G to rref, find free columns.
    M = [row[:] for row in G]
    pivots = []
    r = 0
    pivot_col = {}
    for col in range(m):
        piv = None
        for i in range(r, k):
            if M[i][col] % p != 0:
                piv = i; break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = pow(M[r][col], p-2, p)
        M[r] = [(v*inv) % p for v in M[r]]
        for i in range(k):
            if i != r and M[i][col] % p != 0:
                f = M[i][col]
                M[i] = [(a-f*b) % p for a,b in zip(M[i], M[r])]
        pivot_col[col] = r
        pivots.append(col)
        r += 1
        if r == k: break
    free = [c for c in range(m) if c not in pivot_col]
    basis = []
    for fc in free:
        vec = [0]*m
        vec[fc] = 1
        for pc in pivots:
            vec[pc] = (-M[pivot_col[pc]][fc]) % p
        full = [0]*n
        for idx, j in enumerate(Slist):
            full[j] = vec[idx]
        basis.append(full)
    return basis

def intersect_dim(basisU, basisV, n, p):
    """dim(U cap V) = dim U + dim V - dim(U+V)."""
    du = rref_dim(basisU, n, p)
    dv = rref_dim(basisV, n, p)
    duv = rref_dim(basisU + basisV, n, p)
    return du + dv - duv

def run(n, p, trials=400, seed=0):
    random.seed(seed)
    k = n//2
    pts = random.sample(range(p), n)
    fails_le = 0
    tested = 0
    mism = 0
    examples = []
    for _ in range(trials):
        # band: s in (2n/3, 3n/4)
        lo = n*2//3 + 1
        hi = (n + k - 1)//2  # top of band where pairs can coexist
        if hi < lo:
            hi = lo
        s = random.randint(lo, max(lo, min(hi, 3*n//4)))
        # build three random cores of size s
        allc = list(range(n))
        CA = set(random.sample(allc, s))
        CB = set(random.sample(allc, s))
        CC = set(random.sample(allc, s))
        # enforce post-merge pairwise overlap <= k-1
        def ov(X,Y): return len(X & Y)
        if max(ov(CA,CB), ov(CA,CC), ov(CB,CC)) > k-1:
            continue
        tested += 1
        A = dual_basis_on_support(pts, k, CA, p)
        B = dual_basis_on_support(pts, k, CB, p)
        C = dual_basis_on_support(pts, k, CC, p)
        AB = A + B
        d_int = intersect_dim(AB, C, n, p)
        pair = ov(CA,CB)+ov(CA,CC)+ov(CB,CC)
        trip = len(CA & CB & CC)
        target = pair - trip - 2*k
        formula = max(0, target)
        # deficiency
        dAB = rref_dim(AB, n, p)
        dABC = dAB + rref_dim(C,n,p) - d_int
        union = len(CA | CB | CC)
        defc = (union - k) - dABC
        if d_int > formula:
            fails_le += 1
        if d_int != formula:
            mism += 1
            if len(examples) < 6:
                examples.append((sorted([ov(CA,CB),ov(CA,CC),ov(CB,CC)]), trip, s, d_int, formula, defc))
    print(f"n={n} k={k} p={p}: tested={tested}  dim>max(0,target) fails={fails_le}  dim!=formula={mism}")
    for e in examples:
        print("   overlaps",e[0],"trip",e[1],"s",e[2],"dim((A+B)capC)",e[3],"formula",e[4],"defic",e[5])

if __name__=='__main__':
    for n in [12, 16, 20, 24, 30]:
        run(n, 101, trials=1500, seed=n)
