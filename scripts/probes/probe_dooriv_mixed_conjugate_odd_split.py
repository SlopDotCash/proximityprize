import cmath, math
from sympy import primitive_root

def find_subgroup(p, n):
    g = primitive_root(p)
    h = pow(g, (p-1)//n, p)
    S = []
    seen = set()
    x = 1
    for _ in range(n):
        S.append(x); seen.add(x); x = (x*h) % p
    assert len(seen) == n
    return S

def eta(b, S, p):
    s = 0+0j
    for x in S:
        s += cmath.exp(2j*math.pi*((b*x) % p)/p)
    return s

cases = [(8, 809), (16, 7121), (32, 65537), (64, 602689)]
for n, p in cases:
    S = find_subgroup(p, n)
    Sset = set(S)
    negclosed = all(((-x) % p) in Sset for x in S)
    etas = [eta(c, S, p) for c in range(1, p)]
    print("n=%d p=%d negclosed=%s" % (n, p, negclosed))
    # ODD total degree D = 2r+1 in {3,5}
    for D in [3, 5]:
        vals = []
        for a in range(D+1):
            b = D - a
            tot = 0+0j
            for e in etas:
                tot += (e**a)*(e.conjugate()**b)
            vals.append(tot/p)
        ref = vals[0]  # split (0,D) = Σ conj(η)^D ; should equal Σ η^D (all splits)
        maxdev = max(abs(v-ref) for v in vals)
        maximag = max(abs(v.imag) for v in vals)
        print("  D=%d (odd): A_D=%.4f%+.2ej  maxdev_over_splits=%.3e  max|imag|=%.3e"
              % (D, ref.real, ref.imag, maxdev, maximag))
