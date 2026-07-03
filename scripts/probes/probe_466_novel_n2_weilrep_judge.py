# Judge re-derivation probe for lane N2-weil-rep (#466 novel-math round).
# Independent implementation (fresh code, fresh parameter sets incl. odd-m cases)
# of the disputed/load-bearing numerical claims:
#   (1) M3 annihilator/Gauss decomposition  eta_b = (1/m)(-1 + sum_{1!=chi in Ann} chibar(b) tau(chi))
#   (2) dual identity  sum_{1!=chi} chibar(b) eps_chi = (m eta_b + 1)/sqrt(p)
#   (3) swap identity  sum_{chi in Ann} chibar(b) tau(chi) = m eta_b   (one-line orthogonality)
#   (4) purity |tau(chi)| = sqrt(p) exactly for chi != 1
#   (5) m-power lift  eta_b = (1/m)(S_m(b) - 1),  S_m(b) = sum_y e_p(b y^m)
#   (6) REFUTER-A DISPUTE: ||A_b|| on full L^2(F_p) — proposer wrote M(n,p); refuter says n
#       (x=0 diagonal entry is eta_0 = n).  Also M2 compressed norm = 1 (delta_0 line), not M/n.
#   (7) REFUTER-B DISPUTE: Legendre sigma|_{mu_n} = 1 iff m even (p = 1 mod n does NOT force it).
#   (8) prize-point arithmetic: overshoot 2^60.7644 (m = 2^128) and 2^42.0185 (diagonal p ~ n^4).
import cmath, math

def is_prime(x):
    if x < 2: return False
    for d in range(2, int(x**0.5) + 1):
        if x % d == 0: return False
    return True

def primitive_root(p):
    fac = []
    t = p - 1
    d = 2
    while d * d <= t:
        if t % d == 0:
            fac.append(d)
            while t % d == 0: t //= d
        d += 1
    if t > 1: fac.append(t)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fac):
            return g

def run(n, p):
    assert is_prime(p) and (p - 1) % n == 0
    m = (p - 1) // n
    g = primitive_root(p)
    # index table: dlog[g^k mod p] = k
    dlog = {}
    x = 1
    for k in range(p - 1):
        dlog[x] = k
        x = x * g % p
    psi = lambda a: cmath.exp(2j * math.pi * (a % p) / p)
    w = cmath.exp(2j * math.pi / (p - 1))   # character root of unity
    mu = sorted(pow(g, m * t, p) for t in range(n))          # mu_n = <g^m>
    eta = [sum(psi(b * u) for u in mu) for b in range(p)]     # eta_b for all b
    M = max(abs(eta[b]) for b in range(1, p))
    C = M / math.sqrt(n * math.log(p / n))

    # characters chi_j(g^k) = w^{jk}; Ann(mu_n) = {chi_j : n | j}, |Ann| = m
    def chi(j, a): return w ** ((j * dlog[a]) % (p - 1))
    ann = [j for j in range(0, p - 1, n)]                     # j = 0, n, 2n, ...
    tau = {j: sum(chi(j, a) * psi(a) for a in range(1, p)) for j in ann}

    # (4) purity
    purity_err = max(abs(abs(tau[j]) - math.sqrt(p)) for j in ann if j != 0)
    # tau(chi_0) should be -1
    tau0_err = abs(tau[0] - (-1))

    # (1)(2)(3)(5) over every b (small p) or a deterministic sample (large p);
    # dual_max (for C_dual) always needs all b, so compute it from the exact dual
    # identity ONLY after the identity itself is verified on the b-sample.
    sp = math.sqrt(p)
    m3_err = dual_err = swap_err = lift_err = 0.0
    dual_max = 0.0
    if p <= 4000:
        bs = list(range(1, p))
    else:
        import random
        rng = random.Random(466)
        bs = sorted(rng.sample(range(1, p), 96))
    for b in bs:
        binv_conj = {j: chi(j, b).conjugate() for j in ann}
        s_nontriv = sum(binv_conj[j] * tau[j] for j in ann if j != 0)
        m3_err = max(m3_err, abs(eta[b] - (-1 + s_nontriv) / m))
        dual = sum(binv_conj[j] * (tau[j] / sp) for j in ann if j != 0)
        dual_err = max(dual_err, abs(dual - (m * eta[b] + 1) / sp))
        dual_max = max(dual_max, abs(dual))
        swap = sum(binv_conj[j] * tau[j] for j in ann)         # includes chi_0
        swap_err = max(swap_err, abs(swap - m * eta[b]))
        Sm = sum(psi(b * pow(y, m, p)) for y in range(p))
        lift_err = max(lift_err, abs(eta[b] - (Sm - 1) / m))
    if p > 4000:
        # identity verified on the sample above; use it to get the true max over all b
        dual_max = max(abs((m * eta[b] + 1) / sp) for b in range(1, p))
    C_dual = dual_max / math.sqrt(m * math.log(m)) if m > 1 else float('nan')

    # (6) A_b diagonal on FULL L^2(F_p): entries {eta_{(b*x) mod p} : x in F_p}
    b = 1
    diag = [abs(eta[(b * x) % p]) for x in range(p)]
    norm_full = max(diag)                 # refuter-A: = n (x = 0 gives eta_0 = n)
    norm_punct = max(diag[1:])            # restricted to L^2(F_p^x): = M
    # M2 compressed norm on V_0 = coset lines (+ delta_0 line): entries eta_c/n and 1
    comp_norm_with_delta0 = max(1.0, M / n)
    comp_norm_cosets_only = M / n

    # (7) Legendre on mu_n
    leg_on_mu = {u: pow(u, (p - 1) // 2, p) for u in mu}
    leg_trivial = all(v == 1 for v in leg_on_mu.values())

    print(f"n={n:4d} p={p:6d} m={m:5d} (m {'EVEN' if m % 2 == 0 else 'ODD '}) | "
          f"M={M:9.4f} C={C:6.3f} C_dual={C_dual:6.3f} | "
          f"m3={m3_err:.2e} dual={dual_err:.2e} swap={swap_err:.2e} "
          f"lift={lift_err:.2e} pur={purity_err:.2e} tau0={tau0_err:.2e}")
    print(f"      ||A_b||_(L2 F_p) = {norm_full:.4f} (claim n = {n}) ; "
          f"restricted to L2(F_p^x) = {norm_punct:.4f} (claim M = {M:.4f}) ; "
          f"M2 comp-norm with delta0 = {comp_norm_with_delta0:.4f}, cosets-only = {comp_norm_cosets_only:.4f}")
    print(f"      Legendre|_mu_n trivial: {leg_trivial} (predicted by m even: {m % 2 == 0})")
    return dict(m3=m3_err, dual=dual_err, swap=swap_err, lift=lift_err, pur=purity_err,
                norm_full=norm_full, norm_punct=norm_punct, M=M,
                leg_ok=(leg_trivial == (m % 2 == 0)))

print("== JUDGE probe: independent re-derivation, fresh parameter sets ==")
results = []
for (n, p) in [(8, 41), (8, 137), (16, 113), (16, 1889), (32, 6529), (16, 65537)]:
    results.append(run(n, p))

ok = all(max(r['m3'], r['dual'], r['swap'], r['lift'], r['pur']) < 1e-8 for r in results)
normA = all(abs(r['norm_full'] - n) < 1e-9 or True for r in results)  # printed above per-row
leg = all(r['leg_ok'] for r in results)
print(f"\nidentity families (1)-(5) all verified < 1e-8: {ok}")
print(f"Legendre-parity law verified on all rows (incl. odd m): {leg}")

print("\n== prize-point arithmetic (judge re-derivation) ==")
ln2 = math.log(2)
# convention A: index m = 2^128, p ~ n*m = 2^158
tgt_log2 = 15 + 0.5 * math.log2(128 * ln2)      # sqrt(2^30 * ln 2^128)
print(f"m=2^128 convention: sqrt(p)=2^79, target=2^{tgt_log2:.4f}, overshoot=2^{79 - tgt_log2:.4f}")
# convention B: analytic diagonal p ~ n^4 = 2^120
tgt_log2_d = 15 + 0.5 * math.log2(90 * ln2)     # sqrt(2^30 * ln 2^90)
print(f"diagonal p~n^4:     sqrt(p)=2^60, target=2^{tgt_log2_d:.4f}, overshoot=2^{60 - tgt_log2_d:.4f}")
# weight-0 floor: rank n = 2^30 vs target
print(f"weight-0 floor:     rank n = 2^30 vs target 2^{tgt_log2:.4f} -> overshoot 2^{30 - tgt_log2:.4f}")
