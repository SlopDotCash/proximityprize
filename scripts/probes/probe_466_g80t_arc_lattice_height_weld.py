#!/usr/bin/env python3
"""#466 G80T probe: arc-coincidence anomalies vs lattice shortest vectors.

For d in mu_n, L_d = {(a,b): b = da mod p}. Measure:
  R(d) (dilation-coincidence count, K arcs), lambda_1(L_d) (shortest vector, sup-norm),
and test the weld: R(d) anomaly (R >> p/K) <=> lambda_1 <= K-ish.
Also verify: small (a,b) with b=da => p | Norm(b - a*zeta^k) (norm certificate).
"""
import math

def order(a, p):
    o, x = 1, a % p
    while x != 1:
        x = x * a % p; o += 1
    return o

def lambda1(d, p, bound=None):
    # shortest nonzero (a,b), b ≡ da (mod p), sup-norm; via Lagrange-Gauss on basis (1,d),(0,p)
    # simple: enumerate a in 1..A, b = da mod p reduced to (-p/2,p/2]
    best = p
    A = int(2 * math.isqrt(p)) + 2
    for a in range(1, A):
        b = (d * a) % p
        if b > p // 2:
            b -= p
        best = min(best, max(a, abs(b)))
    return best

def run(n, p, K):
    g = next(c for c in range(2, p) if order(c, p) == p - 1)
    h = pow(g, (p - 1) // n, p)
    H, x = [], 1
    for _ in range(n):
        H.append(x); x = x * h % p
    arc = lambda v: K * v // p
    rows = []
    for d in H:
        if d == 1:
            continue
        R = sum(1 for v in range(1, p) if arc(d * v % p) == arc(v))
        lam = lambda1(d, p)
        rows.append((d, R, lam))
    rows.sort(key=lambda r: -r[1])
    base = p / K
    print(f"n={n} p={p} K={K} p/K={base:.0f} sqrt(p)={math.isqrt(p)}")
    for d, R, lam in rows[:4]:
        print(f"  worst R: d={d} R={R} R/(p/K)={R/base:.2f} lambda1={lam} p/lambda1={p/lam:.0f}")
    for d, R, lam in rows[-2:]:
        print(f"  best  R: d={d} R={R} R/(p/K)={R/base:.2f} lambda1={lam}")
    # correlation: is R - p/K ~ p/lambda1?
    import statistics
    exc = [(R - base) for _, R, lam in rows]
    pred = [p / lam for _, R, lam in rows]
    if len(set(pred)) > 1:
        corr = statistics.correlation(exc, pred)
        print(f"  corr(R - p/K, p/lambda1) = {corr:.3f}")

for (n, p, K) in [(16, 769, 16), (32, 1153, 16), (32, 1153, 64), (16, 257, 16)]:
    run(n, p, K)

# --- refined predictor: L_{d-1} ---
print("\n=== refined: corr(R - p/K, p/lambda1(d-1)) ===")
import statistics
def run2(n, p, K):
    g = next(c for c in range(2, p) if order(c, p) == p - 1)
    h = pow(g, (p - 1) // n, p)
    H, x = [], 1
    for _ in range(n):
        H.append(x); x = x * h % p
    arc = lambda v: K * v // p
    exc, pred, worst = [], [], []
    for d in H:
        if d == 1:
            continue
        R = sum(1 for v in range(1, p) if arc(d * v % p) == arc(v))
        lam = lambda1((d - 1) % p, p)
        exc.append(R - p / K); pred.append(p / lam)
        worst.append((R, lam, d))
    corr = statistics.correlation(exc, pred) if len(set(pred)) > 1 else float('nan')
    worst.sort(key=lambda r: -r[0])
    print(f"n={n} p={p} K={K}: corr={corr:.3f}; top: " +
          ", ".join(f"(d={d},R={R},lam(d-1)={lam})" for R, lam, d in worst[:3]))
for (n, p, K) in [(16, 769, 16), (32, 1153, 16), (32, 1153, 64), (16, 257, 16)]:
    run2(n, p, K)
