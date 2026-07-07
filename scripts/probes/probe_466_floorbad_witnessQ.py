"""#466 W3: inspect the witness factorization x^{3n/4}+c x^{n/2}+L = V_A * Q
for the realizable patterns at (16,17) and (32,97). Q = quotient, deg n/8·... = |3n/4|-|A|.
If Q has special algebraic structure, the n=64 directed search can be reversed."""
import sys
sys.path.insert(0, "scripts/probes")
from probe_466_floorbad_n64_directed import domain, parse_dump, canon, realizable

def polydiv(P, V, p):
    """P divided by monic V -> (Q, R)"""
    P = P[:]; dv = len(V)-1
    Q = [0]*(len(P)-dv)
    for k in range(len(P)-1, dv-1, -1):
        q = P[k] % p
        Q[k-dv] = q
        if q:
            for i in range(dv+1):
                P[k-dv+i] = (P[k-dv+i] - q*V[i]) % p
    return Q, [c % p for c in P[:dv]]

def vanpoly(A, X, p):
    V = [1]
    for j in A:
        r = X[j]
        V = [(-r*V[0]) % p] + [(V[k-1]-r*V[k]) % p for k in range(1,len(V))] + [V[-1]]
    return V

def witness(A, p, n):
    X = domain(p, n)
    half, deg34 = n//2, 3*n//4
    V = vanpoly(A, X, p)
    D = len(A)
    # r = x^{deg34} mod V  (deg <= D-1); realizable => r_k=0 for k>half.
    rr = [(-V[k]) % p for k in range(D)]
    for _ in range(deg34-D):
        top = rr[D-1]
        rr = [(-top*V[0]) % p] + [(rr[k-1]-top*V[k]) % p for k in range(1,D)]
    assert all(rr[k]==0 for k in range(half+1, D))
    c = (-rr[half]) % p          # kills the x^{half} coefficient
    # P = x^{deg34} + c x^{half} - (low part of r ... ) i.e. P = x^{deg34}+c x^{half}+L
    L = [(-rr[k]) % p for k in range(half)]
    P = L + [c] + [0]*(deg34-half-1) + [1]
    Q, R = polydiv(P, V, p)
    assert all(x==0 for x in R)
    return c, Q

def show(tag, path, p, n):
    print(f"== {tag} (n={n}, p={p}) ==")
    seen = set()
    for A in parse_dump(path):
        cn = canon(A, n)
        if cn in seen: continue
        seen.add(cn)
        c, Q = witness(list(A), p, n)
        # try to factor Q's roots inside mu_n / F_p^*
        X = domain(p, n)
        roots = [x for x in range(1, p) if sum(q*pow(x,k,p) for k,q in enumerate(Q)) % p == 0]
        rj = [X.index(r) if r in X else None for r in roots]
        print(f" orbit-rep A={list(A)}")
        print(f"   c={c}  Q={Q}  Fp-roots={roots} (mu_n idx: {rj})")

show("a=4", sys.argv[1]+"/dump16_17.txt", 17, 16)
show("a=5", sys.argv[1]+"/dump32_97.txt", 97, 32)
