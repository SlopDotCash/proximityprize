#!/usr/bin/env python3
"""
#466 ROUND 13 — World I vs World II: does M=max_b||eta_b|| control the SIGNED
hyperplane incidence sum I(s0,s1) = sum_{b : b*s1=0} conj(eta_b) psi(b*s0)?  (FFT)

  eta_b = sum_{y in mu_n} e_p(b*y).  M = max_{b!=0}||eta_b||  (the prize object).
  For a NONTRIVIAL frequency subgroup H (a "hyperplane" of size |H|~q/deg) the
  question is whether

      sup_{s0 in F} | sum_{b in H} conj(eta_b) e_p(b*s0) |

  is (a) ~ sqrt(|H|)*M  [WORLD I: derivable from M by orthogonality/2nd moment], or
         (b) ~ |H|*M    [WORLD II: distinct input, NOT implied by M].

  KEY: s0 |-> sum_{b in H} c_b e_p(b*s0) is the length-p inverse DFT of the
  spectrum {c_b} supported on H; so sup_{s0}|I| = ||IDFT(c)||_inf * p, one FFT.
  We compute worst-case over ALL s0 exactly.
"""
import cmath, math, sys
import numpy as np

def is_prime(n):
    if n < 2: return False
    if n % 2 == 0: return n == 2
    i = 3
    while i*i <= n:
        if n % i == 0: return False
        i += 2
    return True

def primitive_root(p):
    if p == 2: return 1
    phi = p-1; factors = []; m = phi; d = 2
    while d*d <= m:
        if m % d == 0:
            factors.append(d)
            while m % d == 0: m//=d
        d += 1
    if m > 1: factors.append(m)
    for g in range(2, p):
        if all(pow(g, phi//f, p) != 1 for f in factors):
            return g
    return None

def find_primes(n, count=2, pmin=None):
    if pmin is None: pmin = n**4
    out = []; seen_v2 = set()
    p = pmin - (pmin % n) + 1
    if p < pmin: p += n
    while len(out) < count and p < pmin*60:
        if is_prime(p) and (p-1) % n == 0:
            t = p-1; v2 = 0
            while t % 2 == 0: t//=2; v2+=1
            if v2 not in seen_v2:
                out.append(p); seen_v2.add(v2)
        p += n
    return out

def subgroup(p, n, g):
    h = pow(g, (p-1)//n, p)
    S = []; x = 1
    for _ in range(n): S.append(x); x = (x*h) % p
    assert len(set(S)) == n
    return S

def all_etas(p, n, mu):
    # eta_b for b=0..p-1 via one length-p FFT of the indicator of mu.
    ind = np.zeros(p, dtype=np.float64)
    for y in mu: ind[y % p] = 1.0
    # eta_b = sum_y e_p(b*y) = sum_y exp(2pi i b y /p) = FFT(ind)[b] with sign convention
    # np.fft.fft(ind)[k] = sum_y ind[y] exp(-2pi i k y/p); we want +, so conjugate index.
    F = np.fft.fft(ind)          # F[b] = sum_y exp(-2pi i b y/p)
    eta = np.conjugate(F)        # eta[b] = sum_y exp(+2pi i b y/p)
    return eta

def worst_over_s0(eta, H_mask, p):
    # c_b = conj(eta_b) on H, 0 elsewhere.  I(s0) = sum_b c_b exp(+2pi i b s0/p)
    #     = sum_b c_b exp(-2pi i b (-s0)/p) = FFT(c)[-s0].  worst over s0 = ||FFT(c)||_inf
    c = np.where(H_mask, np.conjugate(eta), 0.0+0.0j)
    I = np.fft.fft(np.conjugate(c))   # gives sum_b c_b exp(+2pi i b s0/p) up to index sign
    # Actually: FFT(x)[k]=sum_b x[b] exp(-2pi i b k/p). Want sum_b c_b exp(+..). Use conj(c) then take that FFT?
    # simplest: |I(s0)| = |sum_b c_b exp(+2pi i b s0/p)|. Let X=fft(c): X[k]=sum c_b exp(-2pi i b k/p).
    # so sum_b c_b exp(+2pi i b s0/p) = X[-s0 mod p]. |.| identical set over all s0. Use |fft(c)|.
    X = np.fft.fft(c)
    return np.max(np.abs(X))

def main():
    out = []
    def P(s): out.append(s); print(s); sys.stdout.flush()
    for n in [8, 16]:
        primes = find_primes(n, count=2)
        P(f"\n{'='*74}\nn = {n}   primes (p==1 mod n, p>=n^4, distinct v2): {primes}")
        for p in primes:
            g = primitive_root(p)
            mu = subgroup(p, n, g)
            eta = all_etas(p, n, mu)
            nz = np.abs(eta[1:])            # b != 0
            M = float(np.max(nz))
            l2_full = float(math.sqrt(np.sum(np.abs(eta[1:])**2)))
            P(f"\n  p = {p}  q = {p}  g = {g}")
            P(f"    M = max_(b!=0)||eta_b|| = {M:.4f}   M/sqrt(n) = {M/math.sqrt(n):.4f}"
              f"   (2*sqrt(n)={2*math.sqrt(n):.3f})")
            P(f"    ||eta||_2 over b!=0 = {l2_full:.2f}   ~ sqrt((q-1)*n) = {math.sqrt((p-1)*n):.2f}")
            # CONTROL: H = F^* (whole nonzero spectrum) = the s1=0 degenerate line=point
            maskA = np.ones(p, dtype=bool); maskA[0] = False
            wA = worst_over_s0(eta, maskA, p)
            P(f"    CONTROL H=F* (s1=0, line=point): worst_s0|I| = {wA:.2f}"
              f"   vs q-n = {p-n}   [reaches q-scale: naive q*B NOT beatable on full spectrum]")
            # MODE B: proper subgroups H = <g^deg> of index deg
            for deg in [2, 4, 8]:
                if (p-1) % deg != 0: continue
                gh = pow(g, deg, p)
                H = set(); x = 1
                while x not in H: H.add(x); x = (x*gh) % p
                absH = len(H)
                if absH < 4: continue
                mask = np.zeros(p, dtype=bool)
                for b in H: mask[b] = True
                mask[0] = False   # exclude DC if present
                MH = float(np.max(np.abs(eta[np.array(sorted(H))]))) if H else 0
                # restrict M_H to nonzero b in H
                Hnz = [b for b in H if b != 0]
                MH = float(np.max(np.abs(eta[np.array(Hnz)])))
                l2H = float(math.sqrt(np.sum(np.abs(eta[np.array(Hnz)])**2)))
                worst = worst_over_s0(eta, mask, p)
                absHnz = len(Hnz)
                sqrtHM = math.sqrt(absHnz)*MH
                naive = absHnz*MH
                P(f"    -- MODE B  H=<g^{deg}> index {deg}  |H\\0|={absHnz}  M_H={MH:.3f}")
                P(f"        worst_s0 |I|        = {worst:.4f}")
                P(f"        L2 avg sqrt(S||^2)  = {l2H:.4f}")
                P(f"        sqrt|H|*M_H  [WORLD I] = {sqrtHM:.4f}")
                P(f"        naive |H|*M_H [WORLD II] = {naive:.4f}")
                P(f"        RATIOS  worst/(sqrt|H|*M_H)={worst/sqrtHM:.3f}   "
                  f"worst/(|H|*M_H)={worst/naive:.4f}   worst/L2avg={worst/l2H:.3f}")

    with open("scripts/probes/_out_466r13_incidence.txt", "w") as f:
        f.write("\n".join(out))

if __name__ == "__main__":
    main()
