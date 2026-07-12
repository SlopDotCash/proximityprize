#!/usr/bin/env python3
# G217 witness generator of record: emits and CROSS-CHECKS the exact integer constants
# recorded in Frontier/_G217PhaseCoherenceNoGo.lean.
#
# The Lean file records, per witness (n, p, r):
#   A       = p * sum_t W_G(t) R_r(t) - n^2 * M_r            (exact signed covariance, ∈ ℤ)
#   zcNum   = (p*W_G(0) - n^2) * (p*R_r(0) - M_r)            (zero-cell numerator, = zero_cell*(p-1))
#   s2      = What(chi2) * Rhat(chi2)                        (unique real/quadratic Mellin mode, ∈ ℤ)
#   proxy   = zcNum + p * s2                                 ((p-1) * the real-mode+DC contribution)
# and the no-go theorems assert sign(proxy) != sign(A) for the flip witnesses and
# sign(proxy) = sign(A) for the concordant control.
#
# THIS probe recomputes all four constants FLOAT-FREE from exact integer arithmetic over F_p:
#   - W_G(t) = #{y in G : 2y - t in G}                       (exact integer histogram)
#   - R_r(t) = #{(A,B): |A|=r,|B|=r-1, sumA - sumB = t}      (exact subset-sum convolution)
#   - the unique quadratic character chi2 (a = (p-1)/2, a multiple of n): chi2(t) = (-1)^dlog(t),
#     so What(chi2), Rhat(chi2) are exact integers and s2 = What*Rhat is an exact integer.
# It then asserts the emitted constants EXACTLY match those hard-coded in the Lean file, and
# recomputes proxy and its sign relation to A. No floats anywhere: the quadratic-character
# contribution is the ONLY nontrivial Mellin mode that is integer-valued, which is precisely
# why the certificate is float-free (all other characters are complex-conjugate pairs).
#
# Addresses codex review [P2] (2026-07-12): the committed probes must reproduce and check the
# exact p=1153 / p=97 witness arithmetic used by the Lean certificate.

import itertools, math, sys
from collections import Counter
from sympy import primitive_root as pr

# --- exact F_p machinery ---------------------------------------------------------------

def build_group(p, n):
    assert (p - 1) % n == 0, (p, n)
    g = pr(p)
    m = (p - 1) // n
    G = sorted({pow(g, (m * k) % (p - 1), p) for k in range(n)})
    assert len(G) == n
    return G, g, m

def W_G(p, G):
    Gs = set(G)
    return [sum(1 for y in G if (2 * y - t) % p in Gs) for t in range(p)]

def R_r(p, G, r):
    Gl = sorted(G)
    sA = Counter(sum(A) % p for A in itertools.combinations(Gl, r))
    sB = Counter(sum(B) % p for B in itertools.combinations(Gl, r - 1))
    R = [0] * p
    for sa, ca in sA.items():
        for sb, cb in sB.items():
            R[(sa - sb) % p] += ca * cb
    return R

def dlog_table(p, g):
    d = [0] * p
    v = 1
    for e in range(p - 1):
        d[v] = e
        v = (v * g) % p
    return d

def constants(n, p, r):
    G, g, m = build_group(p, n)
    W = W_G(p, G)
    R = R_r(p, G, r)
    p1 = p - 1
    dl = dlog_table(p, g)
    Mr = math.comb(n, r) * math.comb(n, r - 1)

    # exact signed covariance A
    C12 = sum(W[t] * R[t] for t in range(p))
    A = p * C12 - n * n * Mr

    # zero-cell numerator (= zero_cell * (p-1))
    zcNum = (p * W[0] - n * n) * (p * R[0] - Mr)

    # unique quadratic (order-2) quotient character: a = (p-1)/2, which must be a multiple of n
    a = p1 // 2
    assert a % n == 0 and (2 * a) % p1 == 0, f"no integer quadratic quotient char for (n={n},p={p})"
    # chi2(t) = exp(pi i * dlog(t)) = (-1)^dlog(t), integer-valued; conj(chi2)=chi2
    What = sum(W[t] * ((-1) ** (dl[t] % 2)) for t in range(1, p))
    Rhat = sum(R[t] * ((-1) ** (dl[t] % 2)) for t in range(1, p))
    s2 = What * Rhat  # real character => product is exact integer

    proxy = zcNum + p * s2
    return dict(n=n, p=p, r=r, A=A, zcNum=zcNum, s2=s2, proxy=proxy)

# --- the four Lean-recorded witnesses (must match _G217PhaseCoherenceNoGo.lean exactly) --

LEAN = {
    "wFlip1153": dict(n=16, p=1153, r=5, A=1133232,   zcNum=127172608, s2=-4189184, proxy=-4702956544),
    "wFlip97r5": dict(n=16, p=97,   r=5, A=-6285008,  zcNum=101818368, s2=1292288,  proxy=227170304),
    "wFlip97r6": dict(n=16, p=97,   r=6, A=-14107248, zcNum=237981696, s2=3020288,  proxy=530949632),
    "wCtrl257":  dict(n=16, p=257,  r=5, A=-1051408,  zcNum=-1035505664, s2=-647680, proxy=None),  # proxy check below
}

def sign(x):
    return 1 if x > 0 else -1 if x < 0 else 0

def main():
    ok = True
    for name, rec in LEAN.items():
        c = constants(rec["n"], rec["p"], rec["r"])
        for k in ("A", "zcNum", "s2"):
            match = (c[k] == rec[k])
            ok &= match
            flag = "OK" if match else "*** MISMATCH ***"
            print(f"{name} {k}: computed={c[k]}  lean={rec[k]}  {flag}")
        # proxy = zcNum + p*s2, recomputed
        computed_proxy = c["proxy"]
        if rec["proxy"] is not None:
            pm = (computed_proxy == rec["proxy"])
            ok &= pm
            print(f"{name} proxy: computed={computed_proxy}  lean={rec['proxy']}  {'OK' if pm else '*** MISMATCH ***'}")
        else:
            print(f"{name} proxy: computed={computed_proxy}  (control, no hard-coded value)")
        # the actual no-go relation
        rel = "FLIP (sign(proxy)!=sign(A))" if sign(c["A"]) != sign(computed_proxy) else "AGREE (sign match)"
        print(f"{name}: A={c['A']}({'+' if c['A']>0 else '-'})  proxy={computed_proxy}"
              f"({'+' if computed_proxy>0 else '-'})  => {rel}")
        print()
    # assert the intended no-go structure: three flips + one agree
    flips = all(sign(constants(**{k: LEAN[w][k] for k in ('n','p','r')})["A"]) !=
                sign(constants(**{k: LEAN[w][k] for k in ('n','p','r')})["proxy"])
                for w in ("wFlip1153", "wFlip97r5", "wFlip97r6"))
    ctrl_agree = (sign(constants(16,257,5)["A"]) == sign(constants(16,257,5)["proxy"]))
    print(f"THREE FLIP WITNESSES sign(proxy)!=sign(A): {flips}")
    print(f"CONTROL wCtrl257 sign(proxy)==sign(A):     {ctrl_agree}")
    print(f"ALL LEAN CONSTANTS REPRODUCED EXACTLY:     {ok}")
    if not (ok and flips and ctrl_agree):
        print("FAIL: certificate constants or no-go structure did not reproduce.")
        sys.exit(1)
    print("PASS: every recorded Lean constant reproduced float-free; no-go structure confirmed.")

if __name__ == "__main__":
    main()
