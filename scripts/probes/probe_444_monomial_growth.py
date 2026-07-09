#!/usr/bin/env python3
"""
probe_444_monomial_growth.py  (#444 SEAM A -- Refuter C focused growth test)

Isolates the GROWTH question for the monomial base case. For the FOUR j-roles
{N/2-1, N/2+1, 3N/4, N-3}, k'=2 ONLY (fast: C(128,2)=8128), across the SAME role
at N=16,32,64,128, at a GENUINE window radius (eta=0.125 and eta=0.1875), over >=4
primes including small-v2 (m odd), deep-v2, beta4, large.  EXCLUDES the degenerate
eta=0 / s~=k' threshold-collapse regime (there s<=k'+1 lists every interpolant; not a window).

Prints L per (N, role) and the 16->32->64->128 trajectory: does L GROW?
A growing L is a REFUTATION of monomial constancy = a WIN.
"""
import itertools
from math import comb
from sympy import isprime, primitive_root

def _v2(x):
    c = 0
    while x % 2 == 0:
        x //= 2; c += 1
    return c

def primes_for(N):
    out, seen = [], set()
    def add(p, kind):
        if p in seen or not isprime(p) or (p - 1) % N != 0:
            return False
        m = (p - 1) // N
        if m < 2:
            return False
        out.append({'p': p, 'm': m, 'v2': _v2(p - 1), 'kind': kind}); seen.add(p); return True
    # small-v2: m odd
    m = 3
    while not any(o['kind'] == 'small-v2' for o in out):
        if isprime(m * N + 1):
            add(m * N + 1, 'small-v2')
        m += 2
        if m * N + 1 > 10**9: break
    # deep-v2: maximize v2 over a window
    best = None; m = 2
    while m * N + 1 < 300000 + 10 * N:
        p = m * N + 1
        if isprime(p):
            vv = _v2(p - 1)
            if best is None or vv > best[1]: best = (p, vv)
        m += 1
    if best: add(best[0], 'deep-v2')
    # beta4
    t = int(N ** 4); p = t - (t % N) + 1
    while not add(p, 'beta4'): p += N
    # large beta5
    t = int(N ** 5); p = t - (t % N) + 1
    while not add(p, 'large'): p += N
    return out

def subgroup(N, p):
    g = primitive_root(p); zeta = pow(g, (p - 1) // N, p)
    e, x = [], 1
    for _ in range(N):
        e.append(x); x = (x * zeta) % p
    assert len(set(e)) == N
    return e

def poly_mul(a, b, p):
    r = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b): r[i + j] = (r[i + j] + ai * bj) % p
    return r

def interp_coeffs(xs, ys, p):
    k = len(xs); c = [0] * k
    for i in range(k):
        num = [1]; den = 1
        for j in range(k):
            if j == i: continue
            num = poly_mul(num, [(-xs[j]) % p, 1], p); den = (den * ((xs[i] - xs[j]) % p)) % p
        inv = pow(den, p - 2, p); sc = (ys[i] * inv) % p
        for t in range(len(num)): c[t] = (c[t] + sc * num[t]) % p
    return tuple(c)

def peval(c, x, p):
    r = 0
    for a in reversed(c): r = (r * x + a) % p
    return r

def mono_list(N, j, kp, s, p, elts):
    uv = [pow(x, j, p) for x in elts]
    seen = set()
    for T in itertools.combinations(range(N), kp):
        xs = [elts[i] for i in T]; ys = [uv[i] for i in T]
        c = interp_coeffs(xs, ys, p)
        if c in seen: continue
        ag = 0
        for i in range(N):
            if peval(c, elts[i], p) == uv[i]: ag += 1
        if ag >= s: seen.add(c)
    # report max agreement seen too
    return len(seen)

ROLES = {'N/2-1': lambda N: N // 2 - 1, 'N/2+1': lambda N: N // 2 + 1,
         '3N/4': lambda N: 3 * N // 4, 'N-3': lambda N: N - 3}

def run(Ns=(16, 32, 64, 128), kp=2, etas=(0.1875, 0.125)):
    results = {}  # (role, eta) -> list of L by N
    for N in Ns:
        ps = primes_for(N)
        sub = {d['p']: subgroup(N, d['p']) for d in ps}
        rho = kp / N
        print(f"\n== N={N} kp={kp} rho={rho:.4f}  primes "
              + ", ".join(f"{d['p']}({d['kind']},v2={d['v2']},m={d['m']})" for d in ps))
        for rname, rf in ROLES.items():
            j = rf(N)
            if not (0 < j < N) or j == N // 2: continue
            for eta in etas:
                s = round((rho + eta) * N)
                s = max(s, kp + 2)   # require window strictly above unique-decoding floor
                s = min(s, N - 1)
                vals = []
                for d in ps:
                    L = mono_list(N, j, kp, s, d['p'], sub[d['p']])
                    vals.append(L)
                maxL = max(vals)
                results.setdefault((rname, eta), {})[N] = maxL
                flag = "  >2!" if maxL > 2 else ""
                print(f"   role={rname:6s} j={j:3d} eta={eta:.4f} s={s:3d}: L={vals} max={maxL}{flag}")
    print("\n===== GROWTH TRAJECTORIES (max L over primes, by N) =====")
    grew_any = False
    for (rname, eta), byN in sorted(results.items()):
        traj = [byN.get(N) for N in Ns]
        present = [v for v in traj if v is not None]
        grows = len(present) >= 2 and present[-1] > present[0] and present[-1] > 2
        if grows: grew_any = True
        print(f"  role={rname:6s} eta={eta:.4f}: " +
              " -> ".join(f"N{N}:{byN.get(N)}" for N in Ns) +
              ("   *** GROWS ***" if grows else ""))
    print(f"\n  ANY MONOMIAL LIST GROWS WITH N (and >2)? {grew_any}")

if __name__ == "__main__":
    run()
