import math
# Feasibility of the S2OutputSized shape: exists m,J,D,B nat/int with
#  0<J, m <= e:=(q-1)//2, 2D+3<q, m(D+2m+J) < 2J(D+1), 0<m, 0<=B,
#  B^2 <= k^2 q, 2*Dtot + 3m <= m(B+q), Dtot = 3(m+e)+D+q(J-1)
def best_B(q,m,J,D):
    e=(q-1)//2
    Dtot=3*(m+e)+D+q*(J-1)
    # minimal B: B >= ceil((2Dtot+3m)/m) - q
    B = -(-(2*Dtot+3*m)//m) - q
    return max(B,0), Dtot
def feasible(q,k):
    e=(q-1)//2
    best=None
    m0=int(math.isqrt(2*q//5))
    for m in range(max(1,m0-6), m0+7):
        if m> e: continue
        for J in range(max(1,m//2-3), m//2+6):
            for D in [ (q-5)//2, (q-4)//2, (q-6)//2, (q-7)//2 ]:
                if D<0 or 2*D+3>=q: continue
                if not (m*(D+2*m+J) < 2*J*(D+1)): continue
                B,_=best_B(q,m,J,D)
                if B*B <= k*k*q:
                    c=B/math.sqrt(q)
                    if best is None or c<best[0]: best=(c,m,J,D,B)
    return best
# find q0(k): largest odd prime power below which infeasible (scan odd q)
for k in [7,8,9,10]:
    fails=[]
    for q in range(3, 20002, 2):
        if feasible(q,k) is None: fails.append(q)
    q0 = (max(fails)+2) if fails else 3
    print(f"k={k}: #infeasible odd q in [3,20001]={len(fails)}, max infeasible={max(fails) if fails else None}, q0={q0}, k^2={k*k}, gap-free={q0<=k*k+1}")
# sample constants at large q
for q in [10007, 65537, 1000003]:
    print(q, feasible(q,8))
