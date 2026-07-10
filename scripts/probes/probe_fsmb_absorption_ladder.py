#!/usr/bin/env python3
"""_FSMB_Absorption probe: multi-threshold Plotkin ladder + integral (Jensen)
multiplicity bound for near-saturated pencil cores at the P1 rate-quarter
predecessor point.

P1 parameters:
  N = 2^30 coordinates, K = 2^28 (deg < K), T = 592794966 (agreement threshold).

Everything below is exact integer arithmetic.
"""

from math import isqrt

N = 2**30
K = 2**28
T = 592794966

print(f"N = {N}, K = {K}, T = {T}")
print(f"N - T + 1 (max line cap)         = {N - T + 1}")
print(f"2T - N (pair overlap floor)      = {2*T - N}")
print(f"ceil(T^2/N) (Plotkin ceiling)    = {(T*T + N - 1)//N}")
print()

# ---------------------------------------------------------------------------
# 1. LADDER: forced pairwise overlap among M sets of size >= T in [N]
#    (constant-weight Johnson/Plotkin, shrink-to-exactly-T argument).
#    Contradiction at pairwise cap c iff  M*T^2 > N*T + M'*N*c  with M' = M-1
#    i.e. c < (M*T^2 - N*T) / ((M-1)*N).
#    Forced overlap lambda(M) = largest contradictory c, plus 1.
# ---------------------------------------------------------------------------
print("=== Plotkin/Johnson ladder: forced overlap among M agreement sets ===")


def forced_overlap(M: int) -> int:
    # largest c such that M*(T^2 - N*c) > N*(T - c) (all integers, c < T^2/N)
    num = M * T * T - N * T
    den = (M - 1) * N
    # contradiction iff c < num/den; largest such integer c:
    cmax = (num - 1) // den  # strict inequality
    return cmax + 1


print(f"M=2 (inclusion-exclusion, stronger): 2T-N = {2*T-N}")
for M in range(2, 8):
    lam = forced_overlap(M)
    print(f"M={M}: forced overlap lambda = {lam:>12}  (K = {K}; lam >= K? {lam >= K})")
print()

# ---------------------------------------------------------------------------
# 2. Per-line forced core: L scalars on one pencil force core
#    z >= ceil((L*T - N)/(L-1))  (fresh-fibre packing L*(T-z) + z <= N).
# ---------------------------------------------------------------------------
print("=== Forced core z(L) = ceil((LT-N)/(L-1)) for balanced M-pencil covers ===")
for M in [4, 5, 6]:
    L = (N + 1 + M - 1) // M  # ceil((N+1)/M): the largest pencil in an M-cover
    znum = L * T - N
    zmin = -((-znum) // (L - 1))  # ceil
    print(f"M={M}: largest pencil L >= {L}, forced z >= {zmin} = T - {T - zmin}")
Lsat = None
# L that forces z >= T-2:  L*(T-z)+z<=N with z<=T-3 -> L <= (N-z)/(T-z); find min L forcing z>=T-2
# z <= T-3 allows L <= (N-(T-3))/3; so L > that forces z >= T-2
Lcap_Tm3 = (N - (T - 3)) // 3
print(f"L forcing saturation z>=T-2: L >= {Lcap_Tm3 + 1} (cap at z=T-3 is {Lcap_Tm3})")
print(f"line capacity at z=T-2: {(N-(T-2))//2}, at z=T-1: {N-(T-1)}")
print()

# ---------------------------------------------------------------------------
# 3. Johnson (Cauchy-Schwarz) feasibility of M cores, weight t, pairwise <= K-1
#    feasible iff M*t^2 <= N*(t + (M-1)*(K-1)).
# ---------------------------------------------------------------------------
print("=== Johnson (fractional) test: M cores weight t, pairwise <= K-1 ===")
lam = K - 1
for M in [4, 5, 6]:
    for t in [T, T - 2, T - 3]:
        lhs = M * t * t
        rhs = N * (t + (M - 1) * lam)
        print(f"M={M}, t={t}: M*t^2 = {lhs}, N*(t+(M-1)lam) = {rhs}, "
              f"feasible(Johnson)? {lhs <= rhs}")
print()

# ---------------------------------------------------------------------------
# 4. INTEGRAL multiplicity (Jensen) bound. m_x = #cores containing x, m_x <= M.
#    sum_x m_x = S = sum weights; ordered off-diag overlap = sum_x m_x(m_x-1)
#    >= min over integer m_x. Convex minorant m^2 >= 5m - 6 (tight at m=2,3).
#    For M=5: ordered offdiag <= M(M-1)*lam = 20*lam.
#    Lower bound: sum m^2 >= 5S - 6N  => offdiag = sum m^2 - S >= 4S - 6N.
# ---------------------------------------------------------------------------
print("=== Integral (Jensen) test: 5 cores weight t pairwise <= K-1 ===")


def jensen_min_offdiag(S: int, n: int, M: int) -> int:
    """Exact min of sum_x m_x(m_x-1) with sum m_x = S, 0<=m_x<=M, n points."""
    assert S <= M * n
    q, r = divmod(S, n)
    # optimal: r points at q+1, n-r at q (convexity, integer)
    return r * (q + 1) * q + (n - r) * q * (q - 1)


for t in [T, T - 2, 590558003, 590558002]:
    S = 5 * t
    mn = jensen_min_offdiag(S, N, 5)
    budget = 5 * 4 * lam  # ordered pairs
    print(f"t={t}: S=5t={S}, min ordered offdiag = {mn}, budget 20(K-1) = {budget}, "
          f"feasible? {mn <= budget}  (linear bound 4S-6N = {4*S - 6*N})")

# threshold: largest t feasible for 5 cores
lo, hi = 0, N
while lo < hi:
    mid = (lo + hi + 1) // 2
    if jensen_min_offdiag(5 * mid, N, 5) <= 20 * lam:
        lo = mid
    else:
        hi = mid - 1
print(f"LARGEST t with 5 cores pairwise <= K-1 feasible (Jensen): {lo}")
print(f"  vs T-2 = {T-2}  (T-2 - threshold = {T-2-lo})")
print(f"  => any 5 cores each of weight >= {lo+1} pairwise <= K-1: IMPOSSIBLE")
print()

# same for 4 cores (is 4 saturated feasible?)
print("=== Integral test: 4 cores ===")
for t in [T, T - 1, T - 2]:
    S = 4 * t
    mn = jensen_min_offdiag(S, N, 4)
    budget = 4 * 3 * lam
    print(f"t={t}: min ordered offdiag = {mn}, budget 12(K-1) = {budget}, "
          f"feasible? {mn <= budget}")
lo4, hi4 = 0, N
while lo4 < hi4:
    mid = (lo4 + hi4 + 1) // 2
    if jensen_min_offdiag(4 * mid, N, 4) <= 12 * lam:
        lo4 = mid
    else:
        hi4 = mid - 1
print(f"LARGEST t with 4 cores pairwise <= K-1 feasible (Jensen): {lo4} "
      f"(> T? {lo4 > T})")
print()

# ---------------------------------------------------------------------------
# 5. Verify the exact Lean-target margin: 5 cores weight >= 590558003:
#    ordered offdiag >= 4S - 6N (from m^2 >= 5m-6) vs budget 20(K-1).
# ---------------------------------------------------------------------------
print("=== Lean-target margins (linear minorant m^2 >= 5m-6) ===")
t0 = 590558003
S0 = 5 * t0
print(f"t0 = {t0}: 4*S0 - 6N = {4*S0 - 6*N}, 20(K-1) = {20*lam}, "
      f"margin = {4*S0 - 6*N - 20*lam}")
t1 = T - 2
S1 = 5 * t1
print(f"t1 = T-2 = {t1}: 4*S1 - 6N = {4*S1 - 6*N}, margin over budget = "
      f"{4*S1 - 6*N - 20*lam}")

# sanity: minorant validity for m in 0..5
for m in range(0, 6):
    assert m * m >= 5 * m - 6, m
print("minorant m^2 >= 5m - 6 checked for m = 0..5 (holds for all m: (m-2)(m-3)>=0)")
print()

# ---------------------------------------------------------------------------
# 6. High-core collapse vacuity check: 3T + 2z > 2N + 4(K-1) needs z > ?
# ---------------------------------------------------------------------------
zc = (2 * N + 4 * (K - 1) - 3 * T) // 2 + 1
print(f"high-core collapse needs z >= {zc} (T-2 = {T-2}): vacuous at P1? {zc > T-2}")
print()

# ---------------------------------------------------------------------------
# 7. BARRIER side: 4 saturated pencils capacity check + sunflower failure for 5
# ---------------------------------------------------------------------------
print("=== residual landscape after the 5-core cap ===")
cap_zTm1 = N - (T - 1)
cap_zTm2 = (N - (T - 2)) // 2
print(f"4 pencils z=T-1: capacity 4*(N-T+1) = {4*cap_zTm1} >= N+1 = {N+1}? "
      f"{4*cap_zTm1 >= N+1}")
print(f"4 pencils z=T-2: capacity 4*{cap_zTm2} = {4*cap_zTm2} >= N+1? "
      f"{4*cap_zTm2 >= N+1}")
# capacity of a non-saturated pencil (z <= five-core threshold lo)
z_small = lo
capacity_small = (N - z_small) // (T - z_small)
print(f"pencil with core z <= {z_small}: capacity <= {capacity_small}")
# 4 big + rest small: how many small pencils needed to cover the rest?
deficit = (N + 1) - 4 * cap_zTm1
print(f"4 big (z=T-1) pencils leave deficit {deficit} (negative => big pencils suffice)")
# sunflower check for 5 saturated cores
s_needed = -((-(5 * T - N)) // 4)
print(f"sunflower kernel needed for 5 cores weight T: s >= {s_needed} > K-1 = {K-1}? "
      f"{s_needed > K - 1}")
