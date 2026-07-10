#!/usr/bin/env python3
"""#466: direct census of the TERMINAL certificate object (G80Q form).

smallDiff(b) = #{(u,z) in (b*mu_n)^2 : u != z, u-z in Strip(W)},  W = p/K.
Uniform prediction: n^2 * (2W+1)/p (minus diagonal effects). Certificate needs
max_b smallDiff(b) <= n^2*(2W/p)*O(1) + n*polylog(q).
Measure max/mean/uniform over ALL cosets (coset-invariant per G80V), K near saddle.
"""
import math

def order(a, p):
    o, x = 1, a % p
    while x != 1:
        x = x * a % p; o += 1
    return o

def run(n, p):
    logq = math.log(p)
    K = max(2, round(math.sqrt(2 * math.pi * n / logq)))
    W = p // K
    g = next(c for c in range(2, p) if order(c, p) == p - 1)
    h = pow(g, (p - 1) // n, p)
    H, x = [], 1
    for _ in range(n):
        H.append(x); x = x * h % p
    m = (p - 1) // n
    uni = n * n * (2 * W + 1) / p
    vals = []
    b = 1
    for _ in range(m):  # one representative per coset
        C = [b * y % p for y in H]
        cnt = 0
        for i, u in enumerate(C):
            for j, z in enumerate(C):
                if i == j:
                    continue
                d = (u - z) % p
                if d <= W or d >= p - W:
                    cnt += 1
        vals.append(cnt)
        b = b * g % p
    mx, mean = max(vals), sum(vals) / len(vals)
    print(f"n={n} p={p} (beta={math.log(p)/math.log(n):.2f}) K={K} W={W}: "
          f"uniform={uni:.1f} mean={mean:.1f} max={mx} "
          f"max/uni={mx/uni:.2f} (max-uni)/n={((mx-uni)/n):.2f} n*log(q)={n*logq:.0f}")

for (n, p) in [(16, 257), (16, 769), (16, 65537), (32, 1153), (32, 40961), (64, 264961+2880*0)]:
    # 264961 is the canonical r369 cell (n=64)
    if (p - 1) % n == 0:
        run(n, p)
