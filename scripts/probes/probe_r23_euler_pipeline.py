#!/usr/bin/env python3
"""R23 EULER lane probe: composed S2->charSum statement at q=13,17 (+37,101).
Checks:
 1. Euler set equality: NPlus(u,v) == {s : f(s)^e == 1}, f=s(s-u)(s-v), e=(q-1)/2
 2. count bridge: S = 2#N+ + 3 - q for u,v distinct nonzero
 3. for admissible (m,J,D) [hcount, hD, hme]: m*#N+ <= Dtot = 3(m+e)+D+q(J-1)
    => S <= B_min = ceil((2*Dtot+3m)/m) - q ; verify S <= B_min for ALL (u,v)
 4. scan best B over admissible params; report B/sqrt(q)
"""
import math, itertools

def chi(a, q):
    if a % q == 0: return 0
    return 1 if pow(a, (q-1)//2, q) == 1 else -1

for q in (13, 17, 37, 101):
    e = (q-1)//2
    ok_euler = ok_count = True
    worstS = -q
    for u in range(1, q):
        for v in range(1, q):
            if u == v: continue
            f = lambda s: s*((s-u)%q)*((s-v)%q) % q
            Np = [s for s in range(q) if chi(f(s), q) == 1]
            Np2 = [s for s in range(q) if pow(f(s), e, q) == 1 and f(s) % q != 0]
            # Euler: chi=1 <=> f^e=1 (f !=0 automatic since 0^e=0)
            Np3 = [s for s in range(q) if pow(f(s), e, q) == 1]
            if Np != Np3: ok_euler = False
            S = sum(chi(f(s), q) for s in range(q))
            if S != 2*len(Np) + 3 - q: ok_count = False
            worstS = max(worstS, S)
    # param scan
    best = None
    for m in range(1, e+1):
        for J in range(1, 2*m+3):
            for D in range(0, (q-4)//2 + 1):
                if 2*D + 3 >= q: continue
                if m*(D + 2*m + J) >= 2*J*(D+1): continue
                Dtot = 3*(m+e) + D + q*(J-1)
                B = -(-(2*Dtot + 3*m)//m) - q  # ceil
                if best is None or B < best[0]:
                    best = (B, m, J, D, Dtot)
    B, m, J, D, Dtot = best
    print(f"q={q}: euler_ok={ok_euler} count_ok={ok_count} worstS={worstS} "
          f"bestB={B} (m={m},J={J},D={D},Dtot={Dtot}) B/sqrt(q)={B/math.sqrt(q):.2f} "
          f"S<=B: {worstS <= B}")
