import math

# Mirror of the d=4 fold. Kernel deg = d+1 (L1 L2 L3^(d-1)). 3 distinct linear factors.
# Budgets (PROVEN substrate shapes):
#  indep:   d*D + (d-1)*degG < q        , degG = d+1
#  count:   m*(D + d*m + J) < d*J*(D+1)
#  fiber:   Dtot = degG*(m + (d-1)*e) + D + q*(J-1) , e=(q-1)//d
#  fold:    ||S|| <= d*(Dtot/m) - q + 3 <= Cw*sqrt(q)
#  i.e. need d*Dtot - m*(q-3) <= m*Cw*sqrt(q)  -> Cw >= (d*Dtot - m*(q-3))/(m*sqrt(q))

def budgets_ok(d, q, m, J, D):
    degG = d + 1
    e = (q - 1) // d
    if not (d * D + (d - 1) * degG < q): return None
    if not (m * (D + d*m + J) < d * J * (D + 1)): return None
    if not (m < q): return None
    if not (m > 0 and J > 0): return None
    Dtot = degG * (m + (d - 1) * e) + D + q * (J - 1)
    # fold excess -> Cw
    val = d * Dtot - m * (q - 3)
    if val <= 0:
        return 0.0
    return val / (m * math.sqrt(q))

def best_Cw(d, q):
    degG = d + 1
    Dcap = (q - degG*(d-1) - 1) // d   # largest D with d*D+(d-1)degG<=q-1
    best = None; bestp=None
    # scan D near cap, m near c*sqrt(q), J = m//d + c
    sq = math.sqrt(q)
    for D in range(max(1,Dcap-2), Dcap+1):
        for m in range(1, int(6*sq)+2):
            # J minimal satisfying count: m(D+dm+J) < dJ(D+1) -> J(d(D+1)-m) > m(D+dm)
            denom = d*(D+1) - m
            if denom <= 0: continue
            Jmin = m*(D + d*m)//denom + 1
            for J in range(Jmin, Jmin+3):
                c = budgets_ok(d, q, m, J, D)
                if c is None: continue
                if best is None or c < best:
                    best = c; bestp = (m,J,D)
    return best, bestp

for d in (4, 8, 16):
    print(f"=== d={d} ===")
    for q in [1009, 10007, 100003, 1000003]:
        # only q ≡ 1 mod d
        while q % d != 1: q += 1
        b, p = best_Cw(d, q)
        print(f" q={q}: best Cw={b:.3f}  (m,J,D)={p}  -> C={math.ceil(b) if b else 0}, C^2={None if not b else math.ceil(b)**2}")
