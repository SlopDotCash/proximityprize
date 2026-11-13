"""
Sharper probe: is max_b S(b) a GENERIC concentration tail (=> controllable by union bound),
or a SUBGROUP-STRUCTURAL anomaly (=> genuine wall)?
Test at SADDLE window K ~ sqrt(2 pi n / log p), thin 2-power subgroups, larger p.
"""
import math, random

def is_prime(m):
    if m < 2: return False
    i = 2
    while i*i <= m:
        if m % i == 0: return False
        i += 1
    return True

def primitive_root(p):
    if p == 2: return 1
    phi = p-1; m = phi; fac = []; d = 2
    while d*d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fac.append(m)
    for g in range(2, p):
        if all(pow(g, phi//q, p) != 1 for q in fac): return g
    return None

def subgroup(p, n):
    g = primitive_root(p); gen = pow(g, (p-1)//n, p)
    H = []; x = 1
    for _ in range(n):
        H.append(x); x = x*gen % p
    return H

def S_of_b(H, b, K, p):
    buckets = {}
    for h in H:
        a = (K*((b*h) % p)) // p
        buckets[a] = buckets.get(a, 0) + 1
    return sum(c*c for c in buckets.values())

def cell(p, n, K, seed=0):
    H = subgroup(p, n)
    reps = []; seen = set()
    for b in range(1, p):
        if b in seen: continue
        reps.append(b)
        for h in H: seen.add((b*h) % p)
    vals = [S_of_b(H, b, K, p) for b in reps]
    ncos = len(reps)
    mean = sum(vals)/ncos
    var = sum((v-mean)**2 for v in vals)/ncos
    std = math.sqrt(var)
    mx = max(vals)
    z = (mx-mean)/std if std > 0 else 0.0
    gaus_z = math.sqrt(2*math.log(ncos)) if ncos > 1 else 0.0
    random.seed(seed)
    null_max = -1
    for _ in range(ncos):
        buckets = {}
        for _h in range(n):
            a = random.randrange(K)
            buckets[a] = buckets.get(a, 0) + 1
        Sr = sum(c*c for c in buckets.values())
        if Sr > null_max: null_max = Sr
    return dict(p=p, n=n, K=K, ncos=ncos, mean=round(mean, 2), std=round(std, 2),
                max=mx, z=round(z, 3), gaus_z=round(gaus_z, 3),
                z_over_gaus=round(z/gaus_z, 3) if gaus_z > 0 else None,
                null_max=null_max, real_le_null=(mx <= null_max),
                excess_norm=round((mx-n)/(n*n/K), 3))

tested = []
for n in [8, 16, 32, 64]:
    start = max(4*n*n, 400)
    p = None
    for cand in range(start, start+50000):
        if is_prime(cand) and (cand-1) % n == 0:
            p = cand; break
    if p is None: continue
    K = max(2, round(math.sqrt(2*math.pi*n/math.log(p))))
    tested.append(cell(p, n, K))

for r in tested:
    print(r)

print("\n=== WALL DIAGNOSTIC ===")
print("z_over_gaus ~1 bounded & real<=null True as n grows => GENERIC concentration (controllable).")
print("z_over_gaus grows or real<=null False => SUBGROUP-STRUCTURAL anomaly (true wall).\n")
for r in tested:
    print(f"n={r['n']:3d} p={r['p']:7d} K={r['K']:2d} ncos={r['ncos']:5d} mean={r['mean']:8.2f} max={r['max']:6d} z={r['z']:.2f} gaus_z={r['gaus_z']:.2f} z/gaus={r['z_over_gaus']} real<=null={r['real_le_null']} exc_norm={r['excess_norm']}")
