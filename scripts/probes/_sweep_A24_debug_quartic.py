#!/usr/bin/env python3
"""Debug: is the m=4 HD quartic relation a consequence of quadratic HD + conjugation?
Test at n=8,16 whether quartic-combo(a) - 3*c2 is in the row space of the base system.
"""
from sympy import Matrix


def base_rows(n, cols):
    half = n // 2
    rows = []
    def row(): return [0] * cols
    seen = set()
    for a in range(1, n):
        b = (n - a) % n
        key = tuple(sorted((a, b)))
        if key in seen: continue
        seen.add(key)
        r = row(); r[a] += 1; r[b] += 1; r[n] -= 1; rows.append(r)  # -c1
    for a in range(n):
        r = row(); r[a] += 1; r[(a+half)%n] += 1; r[(2*a)%n] -= 1; r[n+1] -= 1; rows.append(r)  # -c2
    return rows


for n in (8, 16, 32):
    cols = n + 2
    base = base_rows(n, cols)
    Mbase = Matrix(base)
    rbase = Mbase.rank()
    q4 = n // 4
    # quartic relation with const_4 = 3*c2  (the algebraic consequence):
    # theta_a + theta_{a+n/4}+theta_{a+n/2}+theta_{a+3n/4} - theta_{4a} - 3 c2 = 0
    quart_coupled = []
    for a in range(n):
        r = [0]*cols
        r[a]+=1; r[(a+q4)%n]+=1; r[(a+2*q4)%n]+=1; r[(a+3*q4)%n]+=1; r[(4*a)%n]-=1
        r[n+1] -= 3   # - 3 c2
        quart_coupled.append(r)
    Mc = Matrix(base + quart_coupled)
    rc = Mc.rank()
    # quartic with FREE fresh intercept const_4:
    wcols = cols+1
    base_w = [r+[0] for r in base]
    quart_free = []
    for a in range(n):
        r=[0]*wcols
        r[a]+=1; r[(a+q4)%n]+=1; r[(a+2*q4)%n]+=1; r[(a+3*q4)%n]+=1; r[(4*a)%n]-=1
        r[cols]-=1  # fresh const_4
        quart_free.append(r)
    Mf = Matrix(base_w + quart_free)
    rf = Mf.rank()
    rbase_w = Matrix(base_w).rank()
    print(f"n={n}: base rank={rbase}; +quartic(const_4=3c2) rank={rc} (cut={rc-rbase}); "
          f"+quartic(free const_4) rank={rf} vs base_w {rbase_w} (cut={rf-rbase_w})")
