# R21 S1 probe: Stepanov independence for f = X(X-u)(X-v) over GF(q), q=13,17.
# Checks: (1) exhaustive small / random low-deg (a,b) with 2D+3<q: a + b*f^((q-1)/2) != 0 unless a=b=0.
# (2) block version P = sum_j (a_j + b_j f^e) X^{jq} != 0 (random, J=2).
# (3) boundary overflow: with D >= 3e the relation a = -f^e, b = 1 vanishes (budget necessity).
import itertools, random
from sympy import GF, Poly, symbols
x = symbols('x')
for q in (13, 17):
    K = GF(q)
    e = (q-1)//2
    D = (q-5)//2  # 2D+3 = q-2 < q
    for (u,v) in [(1,2),(3,q-1),(2,5)]:
        f = Poly(x*(x-u)*(x-v), x, domain=K)
        fe = f**e
        # (1) exhaustive over degree<=1 pairs + random degree<=D pairs
        for a0,a1,b0,b1 in itertools.product(range(3),repeat=4):
            a = Poly(a0+a1*x, x, domain=K); b = Poly(b0+b1*x, x, domain=K)
            P = a + fe*b
            assert (P.is_zero) == (a.is_zero and b.is_zero), (q,u,v,a,b)
        for _ in range(300):
            a = Poly([random.randrange(q) for _ in range(D+1)], x, domain=K)
            b = Poly([random.randrange(q) for _ in range(D+1)], x, domain=K)
            if a.is_zero and b.is_zero: continue
            assert not (a + fe*b).is_zero
        # (2) J=2 block version
        for _ in range(100):
            blocks = [[Poly([random.randrange(q) for _ in range(D+1)], x, domain=K) for _ in range(2)] for _ in range(2)]
            if all(p.is_zero for bl in blocks for p in bl): continue
            P = Poly(0, x, domain=K)
            for j,(aj,bj) in enumerate(blocks):
                P = P + (aj + fe*bj)*Poly(x**(j*q), x, domain=K)
            assert not P.is_zero
        # (3) overflow counterexample: a=-f^e (deg 3e > D), b=1 -> P=0 nontrivially
        assert ((-fe) + fe*Poly(1,x,domain=K)).is_zero
    print(f"q={q}: OK (e={e}, D={D}, budget 2D+3={2*D+3}<q)")
print("PROBE PASS")
