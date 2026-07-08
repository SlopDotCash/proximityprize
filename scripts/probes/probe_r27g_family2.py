import math
def isqrt(n): return math.isqrt(n)

def family_ok(d, A, k, Qmax):
    """C0=d^2, radicand A (both s and b), J=s+d, D=(q-d^2)/d. Return (C, worst_ratio) or None."""
    C0=d*d; c=d; degG=d+1
    C=math.isqrt(k*k*A)
    if C*C<k*k*A: C+=1
    Qmin=max(C*C+1, d*d+A+d)  # below C^2 the trivial branch handles it
    q=Qmin
    while q%d!=1: q+=1
    worst=0.0
    while q<=Qmax:
        s=isqrt((q-C0)//A); m=d*s; J=s+c; D=(q-C0)//d
        e=(q-1)//d; b=isqrt(A*q); B=k*b
        if s<1 or m>=q: return None
        if not (d*D+(d-1)*degG < q): return None
        if not (m*(D+d*m+J) < d*J*(D+1)): return None
        Dtot=degG*(m+(d-1)*e)+D+q*(J-1)
        if not (d*Dtot <= m*(B+q-3)): return None
        if not (B*B <= C*C*q): return None
        worst=max(worst, B/math.sqrt(q))
        q+=d
    return (C, worst)

for d,Qmax in ((8,700000),(16,6000000)):
    print(f"=== d={d} ===")
    best=None
    for A in range(2,140):
        for k in range(1,70):
            C=math.isqrt(k*k*A)
            if C*C<k*k*A: C+=1
            if best and C>=best[0]: continue
            r=family_ok(d,A,k,Qmax)
            if r and r[1]>0:  # require nonempty test window
                if best is None or r[0]<best[0]:
                    best=(r[0],A,k,r[1])
    print("  best:",best, " (C, A, k, worstRatio)")
