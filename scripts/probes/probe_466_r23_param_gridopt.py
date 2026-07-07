import math
isqrt=math.isqrt

def budgets(q,m,J,D):
    e=(q-1)//2
    ok = (J>0 and m>0 and m<=e and 2*D+3<q and m*(D+2*m+J) < 2*(J*(D+1)))
    Dtot = 3*(m+e)+D+q*(J-1)
    # minimal integer B: 2Dtot+3m <= m(B+q)
    Bmin = -(-(2*Dtot+3*m)//m) - q
    return ok, Dtot, Bmin

# ---- 1. grid optimization: best achievable B/sqrt(q)
for q in [101,1009,10007,65537]:
    best=None
    sq=isqrt(q)
    for m in range(2, 30*sq, 1 if q<2000 else 2):
        # J near m/2: given m,D optimal J = smallest satisfying count
        for D in set(list(range(1,(q-3)//2, max(1,q//200))) + [(q-5)//2,(q-7)//2]):
            if 2*D+3>=q: continue
            # J > m(D+2m)/(2D+2-m)
            den = 2*D+2-m
            if den<=0: continue
            J = m*(D+2*m)//den + 1
            ok,Dtot,B = budgets(q,m,J,D)
            if not ok: continue
            if best is None or B<best[0]: best=(B,m,J,D)
    B,m,J,D=best
    print(f"q={q}: best B={B} B/sqrt(q)={B/math.sqrt(q):.4f} (m={m},J={J},D={D})")
